# -*- coding: utf-8 -*-
"""
QGIS Processing Toolbox Script
Name: Traffica UE Analytics
Author: Maya Safira, Firman Afrianto
License: GPL-2.0-or-later

Adds new outputs
1) OUT_ZONES: polygon zones with O, D, gen, att, snapped node, snap_dist, poi_n, pop_sum
2) OUT_OD_LINES: desire lines between zone centroids with flow and distance (and optional skim cost)

Core fixes kept
- Correct processAlgorithm order (boundary geometry built before using area)
- Node dedup for speed
- Clean AutoSplit with registry check
- Stability clamps DEMAND_SCALE, MIN_CAP, MIN_T0
- UE gap denominator uses x_new

Notes
- CRS must be meter based (UTM). Geographic CRS is rejected.
- OD Lines are straight centroid to centroid. Not the assigned path geometry.
"""

from qgis.PyQt.QtCore import QCoreApplication, QVariant
from qgis.core import (
    QgsApplication,
    QgsProcessing,
    QgsProcessingException,
    QgsProcessingAlgorithm,
    QgsProcessingParameterFeatureSource,
    QgsProcessingParameterRasterLayer,
    QgsProcessingParameterFeatureSink,
    QgsProcessingParameterFileDestination,
    QgsProcessingParameterEnum,
    QgsProcessingParameterNumber,
    QgsProcessingParameterBoolean,
    QgsProcessingParameterField,
    QgsFeature,
    QgsFields,
    QgsField,
    QgsGeometry,
    QgsPointXY,
    QgsWkbTypes,
    QgsFeatureSink,
    QgsSpatialIndex,
    QgsRectangle,
    QgsVectorLayer,
)
from qgis import processing

import math
import os
import csv

try:
    import networkx as nx
    HAS_NX = True
except Exception:
    HAS_NX = False


# =========================================================
# Helpers
# =========================================================
def _safe_float(x, default=None):
    try:
        return float(x)
    except Exception:
        return default


def _safe_int(x, default=None):
    try:
        return int(float(x))
    except Exception:
        return default


def _node_key(p: QgsPointXY, prec: int):
    return f"{round(p.x(), prec)}|{round(p.y(), prec)}"


def _get_endpoints(g: QgsGeometry):
    if g is None or g.isEmpty():
        return None
    if g.isMultipart():
        parts = g.asMultiPolyline()
        if not parts or not parts[0] or len(parts[0]) < 2:
            return None
        pts = parts[0]
    else:
        pts = g.asPolyline()
        if not pts or len(pts) < 2:
            return None
        pts = pts
    return QgsPointXY(pts[0]), QgsPointXY(pts[-1])


def _parse_lanes(val):
    if val is None:
        return 1
    s = str(val).strip()
    if not s:
        return 1
    for sep in [";", "|", ","]:
        if sep in s:
            parts = [p.strip() for p in s.split(sep) if p.strip()]
            nums = [_safe_int(p, None) for p in parts]
            nums = [n for n in nums if n is not None and n > 0]
            return max(nums) if nums else 1
    n = _safe_int(s, None)
    return n if n and n > 0 else 1


# =========================================================
# OSM mapping + filters
# =========================================================
_FCLASS_NORMALIZE = {
    "living street": "living_street",
    "track grade1": "track_grade1",
    "track grade2": "track_grade2",
    "track grade3": "track_grade3",
    "track grade4": "track_grade4",
    "track grade5": "track_grade5",
}


def _norm_fclass(fclass: str) -> str:
    if not fclass:
        return ""
    k = str(fclass).strip().lower()
    return _FCLASS_NORMALIZE.get(k, k)


EXCLUDE_ALWAYS = {"pedestrian", "steps", "path", "footway"}

EXCLUDE_VEHICLE_DEFAULT = {
    "service", "living_street",
    "track", "road",
    "track_grade1", "track_grade2", "track_grade3", "track_grade4", "track_grade5",
    "residential",
}

SPEED_KMH_BY_FCLASS = {
    "trunk": 70.0,
    "trunk_link": 50.0,
    "primary": 50.0,
    "primary_link": 40.0,
    "secondary": 40.0,
    "secondary_link": 35.0,
    "tertiary": 30.0,
    "unclassified": 25.0,
}

CAP_PER_LANE_BY_FCLASS = {
    "trunk": 1800.0,
    "trunk_link": 1200.0,
    "primary": 1200.0,
    "primary_link": 900.0,
    "secondary": 900.0,
    "secondary_link": 800.0,
    "tertiary": 700.0,
    "unclassified": 600.0,
}


def _speed_from_fclass(fclass: str, default_speed: float):
    k = _norm_fclass(fclass)
    if not k:
        return default_speed
    return float(SPEED_KMH_BY_FCLASS.get(k, default_speed))


def _cap_from_fclass(fclass: str, default_cap_per_lane: float, lanes: int):
    k = _norm_fclass(fclass)
    if not k:
        return float(default_cap_per_lane * max(1, lanes))
    base = float(CAP_PER_LANE_BY_FCLASS.get(k, default_cap_per_lane))
    return float(base * max(1, lanes))


# =========================================================
# AutoSplit helpers
# =========================================================
def _alg_exists(alg_id: str) -> bool:
    try:
        return QgsApplication.processingRegistry().algorithmById(alg_id) is not None
    except Exception:
        return False


def _run_first_available(feedback, context, candidates):
    for alg_id, params, out_key in candidates:
        if not _alg_exists(alg_id):
            continue
        res = processing.run(alg_id, params, context=context, feedback=feedback)
        if out_key in res:
            return res[out_key], alg_id
        if "OUTPUT" in res:
            return res["OUTPUT"], alg_id
    raise QgsProcessingException("Auto split gagal: tidak ada algoritma split yang tersedia pada instalasi ini.")


def _auto_split_network(net_input, feedback, context):
    candidates = [
        ("native:splitwithlines", {"INPUT": net_input, "LINES": net_input, "OUTPUT": "memory:"}, "OUTPUT"),
        ("qgis:splitwithlines", {"INPUT": net_input, "LINES": net_input, "OUTPUT": "memory:"}, "OUTPUT"),
        ("native:splitlinesbylines", {"INPUT": net_input, "LINES": net_input, "OUTPUT": "memory:"}, "OUTPUT"),
        ("qgis:splitlinesbylines", {"INPUT": net_input, "LINES": net_input, "OUTPUT": "memory:"}, "OUTPUT"),
    ]
    out, used = _run_first_available(feedback, context, candidates)
    feedback.pushInfo(f"Auto split sukses memakai: {used}")
    return out


# =========================================================
# Main Algorithm
# =========================================================
class TrafficaUEAnalytics(QgsProcessingAlgorithm):

    BOUNDARY = "BOUNDARY"
    NETWORK = "NETWORK"
    POI = "POI"
    POP_RASTER = "POP_RASTER"

    AUTO_SPLIT = "AUTO_SPLIT"
    HIGHWAY_FIELD = "HIGHWAY_FIELD"
    SPEED_FIELD = "SPEED_FIELD"
    CAP_FIELD = "CAP_FIELD"
    LANES_FIELD = "LANES_FIELD"

    DEFAULT_SPEED = "DEFAULT_SPEED"
    DEFAULT_CAP = "DEFAULT_CAP"

    GRID_SIZE = "GRID_SIZE"
    NODE_PREC = "NODE_PREC"
    SNAP_TOL = "SNAP_TOL"

    LAMBDA = "LAMBDA"
    TOPK = "TOPK"
    CAND_MULT = "CAND_MULT"

    ASSIGN_METHOD = "ASSIGN_METHOD"
    K_PATHS = "K_PATHS"
    DETOUR_MAX = "DETOUR_MAX"
    BETA = "BETA"

    ENABLE_UE = "ENABLE_UE"
    BPR_A = "BPR_A"
    BPR_B = "BPR_B"
    MAX_ITERS = "MAX_ITERS"
    EPS_GAP = "EPS_GAP"
    USE_MSA = "USE_MSA"

    DEMAND_SCALE = "DEMAND_SCALE"
    MIN_CAP = "MIN_CAP"
    MIN_T0 = "MIN_T0"

    EXCL_CYCLEWAY = "EXCL_CYCLEWAY"
    EXCL_VEH_DEFAULT = "EXCL_VEH_DEFAULT"

    AUTO_PROFILE = "AUTO_PROFILE"
    PROFILE_APPLY = "PROFILE_APPLY"

    OD_CSV_OUT = "OD_CSV_OUT"
    LOG_CSV = "LOG_CSV"

    OUT_EDGES = "OUT_EDGES"
    OUT_ZONES = "OUT_ZONES"
    OUT_OD_LINES = "OUT_OD_LINES"

    def tr(self, s):
        return QCoreApplication.translate("Processing", s)

    def createInstance(self):
        return TrafficaUEAnalytics()

    def name(self):
        return "traffica_ue_analytics"

    def displayName(self):
        return self.tr("Traffica UE Analytics")

    def shortHelpString(self):
        return self.tr(
            "<p><b>Created by Maya Safira, Firman Afrianto</b></p>"
            "<p><i>Indicative traffic assignment without OD survey data</i>. This tool builds a grid-based zoning system "
            "inside a study boundary, generates <b>synthetic OD demand</b> using a gravity formulation (Population and or POI as mass), "
            "and assigns flows to a road network using <b>All-or-Nothing (AoN)</b> or <b>Probabilistic/Path-Size Logit (PSL)</b>. "
            "Optional <b>User Equilibrium (UE)</b> iterations are available via the <b>BPR congestion function</b> and <b>MSA</b> flow averaging.</p>"

            "<p><b>What is new in the latest version</b></p>"
            "<ul>"
            "<li><b>OSM road filtering</b>: excludes pedestrian, steps, path, footway (optionally cycleway etc.) so non-vehicular links are not counted.</li>"
            "<li><b>Clean Auto-Split</b>: splits lines at intersections using available algorithms (registry check, minimal 'not found' noise).</li>"
            "<li><b>Stability controls</b>: <b>DEMAND_SCALE</b> (flow scaling for big cities), <b>MIN_CAP</b>, and <b>MIN_T0</b> clamps to prevent exploding v/c and UE metrics.</li>"
            "<li><b>Auto profile</b> (optional): presets for <b>Small / Medium / Large</b> areas to keep runtime manageable.</li>"
            "</ul>"

            "<p><b>Use cases</b></p>"
            "<ul>"
            "<li><b>Corridor screening</b>: identify which links are most loaded by synthetic demand.</li>"
            "<li><b>Congestion hotspot proxy</b>: map v/c and delay patterns using BPR-derived travel times.</li>"
            "<li><b>Scenario testing (indicative)</b>: compare network changes such as link closures, access restrictions, speed/capacity adjustments, or new connections.</li>"
            "</ul>"

            "<p><b>Quick workflow</b></p>"
            "<ol>"
            "<li><b>Auto-split</b> the road network at intersections (default ON).</li>"
            "<li>Create <b>grid zones</b> inside the boundary (GRID_SIZE).</li>"
            "<li>Compute <b>Origin mass (O)</b>: prioritizes <b>Population raster zonal sum</b>; fallback uses zone area.</li>"
            "<li>Compute <b>Destination mass (D)</b>: prioritizes <b>POI count per zone</b>; fallback uses O.</li>"
            "<li>Generate <b>synthetic OD</b>: flow ∝ O × D × exp(-LAMBDA × distance), keep <b>TOPK</b> destinations per origin.</li>"
            "<li>Assign flows: <b>AoN</b> (fast baseline) or <b>PSL</b> (multi-path, more realistic dispersion).</li>"
            "<li>If UE is enabled: update link costs with <b>BPR</b>, update flows with <b>MSA</b>, repeat until EPS_GAP or MAX_ITERS.</li>"
            "<li>Export <b>edge results</b> with flow, travel time, v/c, and delay fields.</li>"
            "</ol>"

            "<p><b>Inputs</b></p>"
            "<ul>"
            "<li><b>Boundary</b>: polygon study area.</li>"
            "<li><b>Network</b>: road centerlines. Use a <b>meter-based CRS (e.g., UTM)</b> for meaningful distances and speeds.</li>"
            "<li><b>POP_RASTER</b> (optional): improves origin mass realism compared to zone area.</li>"
            "<li><b>POI</b> (optional): improves destination attractiveness representation.</li>"
            "</ul>"

            "<p><b>Key parameters</b></p>"
            "<ul>"
            "<li><b>GRID_SIZE</b>: zone resolution. Smaller means more detail but heavier runtime.</li>"
            "<li><b>LAMBDA</b>: distance decay. Larger means more local trips dominate.</li>"
            "<li><b>TOPK</b> and <b>CAND_MULT</b>: control OD candidate size (main driver of runtime).</li>"
            "<li><b>ASSIGN_METHOD</b>: AoN for speed, PSL for multi-route dispersion.</li>"
            "<li><b>K_PATHS</b>, <b>DETOUR_MAX</b>, <b>BETA</b> (PSL): route set size, detour limit, and path-size weighting.</li>"
            "<li><b>ENABLE_UE</b>, <b>BPR_A</b>, <b>BPR_B</b>, <b>MAX_ITERS</b>, <b>EPS_GAP</b>, <b>USE_MSA</b>: congestion and convergence controls.</li>"
            "<li><b>SNAP_TOL</b>: zone-to-network snapping tolerance. Increase if many zones fail to snap.</li>"
            "<li><b>DEMAND_SCALE</b> (recommended for big cities): scales synthetic flows down to keep UE stable.</li>"
            "</ul>"

            "<p><b>Outputs</b></p>"
            "<ul>"
            "<li><b>OUT_EDGES</b>: line layer with fields: "
            "<ul>"
            "<li><b>edge_id</b>: representative edge identifier used by the graph.</li>"
            "<li><b>fclass</b>: road class (from OSM field, after normalization).</li>"
            "<li><b>t0</b>: free-flow travel time (seconds), derived from length and speed (or class defaults).</li>"
            "<li><b>cap</b>: capacity (veh/hour), from field or class default per-lane × lanes, with minimum clamp.</li>"
            "<li><b>flow</b>: assigned synthetic flow (scaled), aggregated from all OD pairs.</li>"
            "<li><b>cost</b>: final travel time (seconds). Equals t0 if UE disabled, or BPR(t0, flow, cap) if UE enabled.</li>"
            "<li><b>vc</b>: volume-to-capacity ratio (flow/cap).</li>"
            "<li><b>delay</b>: delay proxy, (cost - t0) × flow (non-negative) when UE is enabled.</li>"
            "<li><b>length</b>: link length in layer units (meters recommended).</li>"
            "</ul>"
            "</li>"
            "<li><b>OD_CSV_OUT</b> (optional): synthetic OD pairs (origin_zone, dest_zone, flow, dist).</li>"
            "<li><b>LOG_CSV</b> (optional): UE iteration log (iter, gap, total_demand, total_delay).</li>"
            "</ul>"

            "<p><b>Interpretation notes</b></p>"
            "<ul>"
            "<li>Results are <b>indicative</b> because OD, free-flow speed, and capacity may be proxies.</li>"
            "<li>For reliable geometry-distance logic, use a <b>meter-based CRS</b> and ensure the network is connected within the boundary.</li>"
            "<li>If many flows are zero, common causes are: zone snapping failure, geographic CRS (degrees), disconnected network components, or overly strict road filtering.</li>"
            "<li>For large cities, reduce runtime by increasing GRID_SIZE, reducing TOPK/CAND_MULT/K_PATHS, and using DEMAND_SCALE.</li>"
            "</ul>"
        )

    def initAlgorithm(self, config=None):

        self.addParameter(QgsProcessingParameterFeatureSource(
            self.BOUNDARY, self.tr("Boundary (polygon)"), [QgsProcessing.TypeVectorPolygon]
        ))
        self.addParameter(QgsProcessingParameterFeatureSource(
            self.NETWORK, self.tr("Network (lines)"), [QgsProcessing.TypeVectorLine]
        ))
        self.addParameter(QgsProcessingParameterFeatureSource(
            self.POI, self.tr("POI (optional)"), [QgsProcessing.TypeVectorPoint], optional=True
        ))
        self.addParameter(QgsProcessingParameterRasterLayer(
            self.POP_RASTER, self.tr("Population raster (optional)"), optional=True
        ))

        self.addParameter(QgsProcessingParameterBoolean(
            self.AUTO_SPLIT, self.tr("Auto split network at intersections"), defaultValue=True
        ))

        self.addParameter(QgsProcessingParameterField(
            self.HIGHWAY_FIELD, self.tr("Road class field (e.g. fclass/highway)"),
            parentLayerParameterName=self.NETWORK, optional=True, defaultValue="fclass"
        ))
        self.addParameter(QgsProcessingParameterField(
            self.SPEED_FIELD, self.tr("Speed field (km/h, optional)"),
            parentLayerParameterName=self.NETWORK, optional=True
        ))
        self.addParameter(QgsProcessingParameterField(
            self.CAP_FIELD, self.tr("Capacity field (veh/h, optional)"),
            parentLayerParameterName=self.NETWORK, optional=True
        ))
        self.addParameter(QgsProcessingParameterField(
            self.LANES_FIELD, self.tr("Lanes field (optional)"),
            parentLayerParameterName=self.NETWORK, optional=True
        ))

        self.addParameter(QgsProcessingParameterNumber(
            self.DEFAULT_SPEED, self.tr("Default speed (km/h)"),
            QgsProcessingParameterNumber.Double, 30.0, False, 1.0, 200.0
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.DEFAULT_CAP, self.tr("Default capacity per lane (veh/h)"),
            QgsProcessingParameterNumber.Double, 800.0, False, 10.0, 20000.0
        ))

        self.addParameter(QgsProcessingParameterNumber(
            self.GRID_SIZE, self.tr("Grid size (meters)"),
            QgsProcessingParameterNumber.Double, 400.0, False, 50.0, 50000.0
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.NODE_PREC, self.tr("Node rounding precision (digits)"),
            QgsProcessingParameterNumber.Integer, 3, False, 0, 8
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.SNAP_TOL, self.tr("Snap tolerance zone centroid to network node (m)"),
            QgsProcessingParameterNumber.Double, 300.0, False, 0.0, 1e12
        ))

        self.addParameter(QgsProcessingParameterNumber(
            self.LAMBDA, self.tr("Gravity lambda"),
            QgsProcessingParameterNumber.Double, 0.001, False, 1e-9, 1000.0
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.TOPK, self.tr("Top K destinations per origin"),
            QgsProcessingParameterNumber.Integer, 10, False, 1, 500
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.CAND_MULT, self.tr("Candidate multiplier (TopK × this)"),
            QgsProcessingParameterNumber.Integer, 5, False, 1, 50
        ))

        self.addParameter(QgsProcessingParameterEnum(
            self.ASSIGN_METHOD, self.tr("Assignment method"),
            options=["AoN", "PSL"], defaultValue=1
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.K_PATHS, self.tr("K paths per OD (PSL)"),
            QgsProcessingParameterNumber.Integer, 3, False, 1, 100
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.DETOUR_MAX, self.tr("Detour max ratio to shortest"),
            QgsProcessingParameterNumber.Double, 1.3, False, 1.0, 50.0
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.BETA, self.tr("PSL beta overlap weight"),
            QgsProcessingParameterNumber.Double, 1.0, False, 0.0, 50.0
        ))

        self.addParameter(QgsProcessingParameterBoolean(
            self.ENABLE_UE, self.tr("Enable UE (BPR + MSA)"), defaultValue=True
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.BPR_A, self.tr("BPR a"),
            QgsProcessingParameterNumber.Double, 0.15, False, 0.0, 10.0
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.BPR_B, self.tr("BPR b"),
            QgsProcessingParameterNumber.Double, 4.0, False, 1.0, 20.0
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.MAX_ITERS, self.tr("Max iterations"),
            QgsProcessingParameterNumber.Integer, 15, False, 1, 200
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.EPS_GAP, self.tr("Convergence epsilon gap"),
            QgsProcessingParameterNumber.Double, 0.003, False, 1e-9, 1.0
        ))
        self.addParameter(QgsProcessingParameterBoolean(
            self.USE_MSA, self.tr("Use MSA smoothing"), defaultValue=True
        ))

        self.addParameter(QgsProcessingParameterBoolean(
            self.EXCL_CYCLEWAY, self.tr("Exclude cycleway"), defaultValue=True
        ))
        self.addParameter(QgsProcessingParameterBoolean(
            self.EXCL_VEH_DEFAULT, self.tr("Exclude service/residential/track/living_street (veh screening)"),
            defaultValue=True
        ))

        self.addParameter(QgsProcessingParameterEnum(
            self.AUTO_PROFILE,
            self.tr("Auto setting profile"),
            options=[
                "Manual (no auto)",
                "Auto by boundary area",
                "Small area",
                "Medium area",
                "Large area"
            ],
            defaultValue=1
        ))
        self.addParameter(QgsProcessingParameterBoolean(
            self.PROFILE_APPLY,
            self.tr("Apply profile to speed up (override heavy parameters)"),
            defaultValue=True
        ))

        self.addParameter(QgsProcessingParameterNumber(
            self.DEMAND_SCALE, self.tr("Demand scale (multiply synthetic flows)"),
            QgsProcessingParameterNumber.Double, 1e-6, False, 0.0, 1e6
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.MIN_CAP, self.tr("Minimum capacity clamp (veh/h)"),
            QgsProcessingParameterNumber.Double, 200.0, False, 0.0, 1e12
        ))
        self.addParameter(QgsProcessingParameterNumber(
            self.MIN_T0, self.tr("Minimum free flow time t0 clamp (sec)"),
            QgsProcessingParameterNumber.Double, 1.0, False, 0.0, 1e12
        ))

        self.addParameter(QgsProcessingParameterFileDestination(
            self.OD_CSV_OUT, self.tr("Synthetic OD CSV output (optional)"),
            fileFilter="CSV (*.csv)", optional=True
        ))
        self.addParameter(QgsProcessingParameterFileDestination(
            self.LOG_CSV, self.tr("Iteration log CSV (optional)"),
            fileFilter="CSV (*.csv)", optional=True
        ))

        self.addParameter(QgsProcessingParameterFeatureSink(
            self.OUT_EDGES, self.tr("Edges output (flows)"),
            QgsProcessing.TypeVectorLine
        ))
        self.addParameter(QgsProcessingParameterFeatureSink(
            self.OUT_ZONES, self.tr("Zones output (polygons)"),
            QgsProcessing.TypeVectorPolygon
        ))
        self.addParameter(QgsProcessingParameterFeatureSink(
            self.OUT_OD_LINES, self.tr("OD desire lines output (lines)"),
            QgsProcessing.TypeVectorLine
        ))

    def _pick_profile(self, area_m2: float, mode: int) -> str:
        if mode == 2:
            return "small"
        if mode == 3:
            return "medium"
        if mode == 4:
            return "large"
        if area_m2 <= 50_000_000:
            return "small"
        if area_m2 <= 250_000_000:
            return "medium"
        return "large"

    def processAlgorithm(self, parameters, context, feedback):

        if not HAS_NX:
            raise QgsProcessingException("NetworkX is not available. Install NetworkX in the QGIS environment.")

        boundary_src = self.parameterAsSource(parameters, self.BOUNDARY, context)
        net_src_in = self.parameterAsSource(parameters, self.NETWORK, context)
        poi_src = self.parameterAsSource(parameters, self.POI, context)
        pop_ras = self.parameterAsRasterLayer(parameters, self.POP_RASTER, context)

        if boundary_src is None or net_src_in is None:
            raise QgsProcessingException("Boundary and Network are required.")

        bgeom = None
        for f in boundary_src.getFeatures():
            g = f.geometry()
            if g is None or g.isEmpty():
                continue
            bgeom = g if bgeom is None else bgeom.combine(g)
        if bgeom is None or bgeom.isEmpty():
            raise QgsProcessingException("Boundary geometry is empty.")

        crs = boundary_src.sourceCrs()
        if crs.isGeographic():
            raise QgsProcessingException("Geographic CRS (degrees) is not supported. Reproject to a metric CRS (UTM).")

        area_m2 = float(bgeom.area())

        auto_split = self.parameterAsBool(parameters, self.AUTO_SPLIT, context)

        grid_size = self.parameterAsDouble(parameters, self.GRID_SIZE, context)

        highway_field = self.parameterAsString(parameters, self.HIGHWAY_FIELD, context).strip()
        speed_field = self.parameterAsString(parameters, self.SPEED_FIELD, context).strip()
        cap_field = self.parameterAsString(parameters, self.CAP_FIELD, context).strip()
        lanes_field = self.parameterAsString(parameters, self.LANES_FIELD, context).strip()

        default_speed = self.parameterAsDouble(parameters, self.DEFAULT_SPEED, context)
        default_cap = self.parameterAsDouble(parameters, self.DEFAULT_CAP, context)

        node_prec = self.parameterAsInt(parameters, self.NODE_PREC, context)
        snap_tol = self.parameterAsDouble(parameters, self.SNAP_TOL, context)

        lamb = self.parameterAsDouble(parameters, self.LAMBDA, context)
        topk = self.parameterAsInt(parameters, self.TOPK, context)
        cand_mult = self.parameterAsInt(parameters, self.CAND_MULT, context)

        assign_method = self.parameterAsEnum(parameters, self.ASSIGN_METHOD, context)
        k_paths = self.parameterAsInt(parameters, self.K_PATHS, context)
        detour_max = self.parameterAsDouble(parameters, self.DETOUR_MAX, context)
        beta = self.parameterAsDouble(parameters, self.BETA, context)

        enable_ue = self.parameterAsBool(parameters, self.ENABLE_UE, context)
        bpr_a = self.parameterAsDouble(parameters, self.BPR_A, context)
        bpr_b = self.parameterAsDouble(parameters, self.BPR_B, context)
        max_iters = self.parameterAsInt(parameters, self.MAX_ITERS, context)
        eps_gap = self.parameterAsDouble(parameters, self.EPS_GAP, context)
        use_msa = self.parameterAsBool(parameters, self.USE_MSA, context)

        demand_scale = self.parameterAsDouble(parameters, self.DEMAND_SCALE, context)
        min_cap = self.parameterAsDouble(parameters, self.MIN_CAP, context)
        min_t0 = self.parameterAsDouble(parameters, self.MIN_T0, context)

        excl_cycleway = self.parameterAsBool(parameters, self.EXCL_CYCLEWAY, context)
        excl_veh_default = self.parameterAsBool(parameters, self.EXCL_VEH_DEFAULT, context)

        auto_mode = self.parameterAsEnum(parameters, self.AUTO_PROFILE, context)
        apply_profile = self.parameterAsBool(parameters, self.PROFILE_APPLY, context)

        od_csv_out = self.parameterAsFile(parameters, self.OD_CSV_OUT, context)
        od_csv_out = str(od_csv_out).strip() if od_csv_out else ""
        if not od_csv_out:
            od_csv_out = None

        log_csv = self.parameterAsFile(parameters, self.LOG_CSV, context)
        log_csv = str(log_csv).strip() if log_csv else ""
        if not log_csv:
            log_csv = None

        profile = self._pick_profile(area_m2, auto_mode)
        feedback.pushInfo(f"Boundary area={area_m2:.2f} m2 | auto_mode={auto_mode} | profile={profile}")

        if apply_profile and auto_mode != 0:
            if profile == "small":
                grid_size = max(grid_size, 300.0)
                topk = min(topk, 10)
                cand_mult = min(cand_mult, 4)
                k_paths = min(k_paths, 3)
                max_iters = min(max_iters, 10)
                eps_gap = max(eps_gap, 0.003)
                detour_max = min(detour_max, 1.3)
                snap_tol = max(snap_tol, 250.0)
                demand_scale = max(demand_scale, 1e-5)
            elif profile == "medium":
                grid_size = max(grid_size, 600.0)
                topk = min(topk, 8)
                cand_mult = min(cand_mult, 3)
                k_paths = min(k_paths, 2)
                max_iters = min(max_iters, 6)
                eps_gap = max(eps_gap, 0.004)
                detour_max = min(detour_max, 1.2)
                snap_tol = max(snap_tol, 300.0)
                demand_scale = max(demand_scale, 1e-6)
            else:
                grid_size = max(grid_size, 1000.0)
                topk = min(topk, 6)
                cand_mult = min(cand_mult, 2)
                k_paths = min(k_paths, 2)
                max_iters = min(max_iters, 3)
                eps_gap = max(eps_gap, 0.01)
                detour_max = min(detour_max, 1.2)
                snap_tol = max(snap_tol, 400.0)
                demand_scale = max(demand_scale, 1e-6)

        feedback.pushInfo(
            f"Applied params -> GRID_SIZE={grid_size}, TOPK={topk}, CAND_MULT={cand_mult}, K_PATHS={k_paths}, "
            f"MAX_ITERS={max_iters}, EPS_GAP={eps_gap}, DETOUR_MAX={detour_max}, SNAP_TOL={snap_tol}, DEMAND_SCALE={demand_scale}"
        )

        if auto_split:
            feedback.pushInfo("Auto split is enabled.")
            net_layer = _auto_split_network(parameters[self.NETWORK], feedback, context)
        else:
            net_layer = QgsVectorLayer(f"LineString?crs={net_src_in.sourceCrs().authid()}", "net_tmp", "memory")
            prn = net_layer.dataProvider()
            prn.addAttributes(net_src_in.fields().toList())
            net_layer.updateFields()
            feats = [f for f in net_src_in.getFeatures()]
            prn.addFeatures(feats)
            net_layer.updateExtents()

        # Zones grid inside boundary
        zones_vl = QgsVectorLayer(f"Polygon?crs={crs.authid()}", "zones_tmp", "memory")
        prz = zones_vl.dataProvider()
        prz.addAttributes([QgsField("zone_id", QVariant.Int), QgsField("poi_n", QVariant.Int)])
        zones_vl.updateFields()

        ext = bgeom.boundingBox()
        xmin, xmax = ext.xMinimum(), ext.xMaximum()
        ymin, ymax = ext.yMinimum(), ext.yMaximum()

        feats_z = []
        zid = 0
        x = xmin
        while x < xmax:
            y = ymin
            while y < ymax:
                rect = QgsRectangle(x, y, x + grid_size, y + grid_size)
                poly = QgsGeometry.fromRect(rect)
                inter = poly.intersection(bgeom)
                if inter is not None and not inter.isEmpty() and inter.area() > 0:
                    zid += 1
                    ft = QgsFeature(zones_vl.fields())
                    ft["zone_id"] = zid
                    ft["poi_n"] = 0
                    ft.setGeometry(inter)
                    feats_z.append(ft)
                y += grid_size
            x += grid_size

        if not feats_z:
            raise QgsProcessingException("No zones were created. Check the GRID_SIZE and boundary.")

        prz.addFeatures(feats_z)
        zones_vl.updateExtents()

        # POI count per zone
        if poi_src is not None:
            try:
                res = processing.run(
                    "qgis:countpointsinpolygon",
                    {
                        "POLYGONS": zones_vl,
                        "POINTS": parameters[self.POI],
                        "WEIGHT": None,
                        "CLASSFIELD": None,
                        "FIELD": "poi_n",
                        "OUTPUT": "memory:"
                    },
                    context=context,
                    feedback=feedback
                )
                zones_vl = res["OUTPUT"]
            except Exception as e:
                feedback.pushInfo(f"Gagal hitung POI per zona. Detail: {e}")

        # Population zonal sum for O
        pop_sum_field = None
        if pop_ras is not None:
            try:
                res = processing.run(
                    "qgis:zonalstatisticsfb",
                    {
                        "INPUT": zones_vl,
                        "INPUT_RASTER": pop_ras,
                        "RASTER_BAND": 1,
                        "COLUMN_PREFIX": "pop_",
                        "STATISTICS": [1],
                        "OUTPUT": "memory:"
                    },
                    context=context,
                    feedback=feedback
                )
                zones_vl = res["OUTPUT"]
            except Exception:
                try:
                    processing.run(
                        "qgis:zonalstatistics",
                        {
                            "INPUT": zones_vl,
                            "RASTER": pop_ras,
                            "BAND": 1,
                            "COLUMN_PREFIX": "pop_",
                            "STATISTICS": [1]
                        },
                        context=context,
                        feedback=feedback
                    )
                except Exception as e:
                    feedback.pushInfo(f"Gagal zonal pop. Detail: {e}")

            for nm in zones_vl.fields().names():
                if nm.lower().endswith("sum") and nm.lower().startswith("pop_"):
                    pop_sum_field = nm
                    break
            if pop_sum_field is None:
                for nm in zones_vl.fields().names():
                    if nm.lower() == "pop_sum":
                        pop_sum_field = nm
                        break

        # Build zones data list with geometry
        zones = []
        for f in zones_vl.getFeatures():
            g = f.geometry()
            if g is None or g.isEmpty():
                continue
            zid = int(f["zone_id"])
            cent = QgsPointXY(g.centroid().asPoint())
            area = max(1e-9, g.area())
            poi_n = _safe_int(f["poi_n"], 0) if "poi_n" in f.fields().names() else 0

            pop_sum = None
            if pop_sum_field and pop_sum_field in f.fields().names():
                pop_sum = _safe_float(f[pop_sum_field], None)

            O = float(pop_sum) if (pop_sum is not None and pop_sum > 0) else float(area)
            D = float(poi_n) if (poi_n and poi_n > 0) else float(O)

            zones.append({
                "zone_id": zid,
                "geom": g,
                "cent": cent,
                "poi_n": int(poi_n),
                "pop_sum": float(pop_sum) if (pop_sum is not None) else None,
                "O": max(1e-9, float(O)),
                "D": max(1e-9, float(D))
            })

        if len(zones) < 2:
            raise QgsProcessingException("Too few zones to form an OD matrix.")
        feedback.pushInfo(f"Zones built: {len(zones)}")

        # Build graph with node dedup
        G = nx.Graph()

        node_index = QgsSpatialIndex()
        node_feat_by_id = {}
        node_key_by_fid = {}
        node_fid_by_key = {}
        next_fid = 1

        def ensure_node(pxy: QgsPointXY, nkey: str):
            nonlocal next_fid
            fid = node_fid_by_key.get(nkey, None)
            if fid is not None:
                return fid
            ft = QgsFeature()
            ft.setId(next_fid)
            next_fid += 1
            ft.setGeometry(QgsGeometry.fromPointXY(pxy))
            node_fid_by_key[nkey] = ft.id()
            node_feat_by_id[ft.id()] = ft
            node_key_by_fid[ft.id()] = nkey
            node_index.addFeature(ft)
            return ft.id()

        edge_geom_by_eid = {}
        edge_t0_by_eid = {}
        edge_cap_by_eid = {}
        edge_len_by_eid = {}
        edge_cls_by_eid = {}
        pair_to_eid = {}

        net_fields = net_layer.fields().names()
        has_cls = bool(highway_field) and (highway_field in net_fields)
        has_speed = bool(speed_field) and (speed_field in net_fields)
        has_cap = bool(cap_field) and (cap_field in net_fields)
        has_lanes = bool(lanes_field) and (lanes_field in net_fields)

        exclude_set = set(EXCLUDE_ALWAYS)
        if excl_cycleway:
            exclude_set.add("cycleway")
        if excl_veh_default:
            exclude_set |= set(EXCLUDE_VEHICLE_DEFAULT)

        excluded = 0
        used = 0

        for f in net_layer.getFeatures():
            geom = f.geometry()
            ep = _get_endpoints(geom)
            if ep is None:
                continue

            cls_raw = str(f[highway_field]).strip().lower() if has_cls else ""
            cls = _norm_fclass(cls_raw)
            if cls in exclude_set:
                excluded += 1
                continue

            a, b = ep
            ukey = _node_key(a, node_prec)
            vkey = _node_key(b, node_prec)

            length = float(geom.length())
            if length <= 0:
                continue

            lanes = _parse_lanes(f[lanes_field]) if has_lanes else 1

            sp = _safe_float(f[speed_field], None) if has_speed else None
            if sp is None or sp <= 0:
                sp = _speed_from_fclass(cls, default_speed)

            capv = _safe_float(f[cap_field], None) if has_cap else None
            if capv is None or capv <= 0:
                capv = _cap_from_fclass(cls, default_cap, lanes)

            capv = max(float(capv), float(min_cap))
            t0 = (length * 3.6) / max(1e-9, float(sp))
            t0 = max(float(t0), float(min_t0))

            eid = int(f.id())
            used += 1

            ensure_node(QgsPointXY(a.x(), a.y()), ukey)
            ensure_node(QgsPointXY(b.x(), b.y()), vkey)

            G.add_node(ukey)
            G.add_node(vkey)

            pair = tuple(sorted([ukey, vkey]))
            prev_eid = pair_to_eid.get(pair, None)
            if prev_eid is None:
                pair_to_eid[pair] = eid
                G.add_edge(ukey, vkey, weight=float(t0))
            else:
                prev_t0 = edge_t0_by_eid.get(prev_eid, None)
                if prev_t0 is None or t0 < prev_t0:
                    pair_to_eid[pair] = eid
                    if G.has_edge(ukey, vkey):
                        G[ukey][vkey]["weight"] = float(t0)

            edge_geom_by_eid[eid] = geom
            edge_t0_by_eid[eid] = float(t0)
            edge_cap_by_eid[eid] = float(capv)
            edge_len_by_eid[eid] = float(length)
            edge_cls_by_eid[eid] = cls

        feedback.pushInfo(f"Network edges used: {used} | excluded: {excluded}")
        if G.number_of_edges() == 0:
            raise QgsProcessingException("The graph is empty after filtering. Check the HIGHWAY_FIELD and the fclass/highway values.")

        # Snap zones to nearest node
        def snap_to_node(pt: QgsPointXY):
            geom_pt = QgsGeometry.fromPointXY(pt)
            nn = node_index.nearestNeighbor(geom_pt.asPoint(), 1)
            if not nn:
                return None, None
            fid = nn[0]
            feat = node_feat_by_id.get(fid)
            dist = feat.geometry().distance(geom_pt) if feat else None
            if snap_tol > 0 and dist is not None and dist > snap_tol:
                return None, dist
            return node_key_by_fid.get(fid), dist

        zone_to_node = {}
        zone_snap_dist = {}
        fail = 0
        for z in zones:
            nk, dist = snap_to_node(z["cent"])
            if nk is None:
                fail += 1
                continue
            zone_to_node[z["zone_id"]] = nk
            zone_snap_dist[z["zone_id"]] = float(dist) if dist is not None else None

        if fail:
            feedback.pushInfo(f"Zones gagal snap: {fail}. Jika banyak: naikkan SNAP_TOL atau pastikan CRS meter.")
        if len(zone_to_node) < 2:
            raise QgsProcessingException("Too few valid zones on the network (check snapping and network connectivity).")

        # Candidate OD by nearest zones
        z_index = QgsSpatialIndex()
        zone_by_id = {z["zone_id"]: z for z in zones if z["zone_id"] in zone_to_node}
        zone_ids = list(zone_by_id.keys())
        for zid2 in zone_ids:
            ft = QgsFeature()
            ft.setId(int(zid2))
            ft.setGeometry(QgsGeometry.fromPointXY(zone_by_id[zid2]["cent"]))
            z_index.addFeature(ft)

        cand_k = max(topk * max(1, cand_mult), topk)

        OD = []
        for ozid in zone_ids:
            o = zone_by_id[ozid]
            ocent = o["cent"]
            nn = z_index.nearestNeighbor(QgsGeometry.fromPointXY(ocent).asPoint(), cand_k + 1)

            candidates = []
            for fid in nn:
                dzid = int(fid)
                if dzid == ozid:
                    continue
                if dzid not in zone_by_id:
                    continue
                dzone = zone_by_id[dzid]
                dist = ocent.distance(dzone["cent"])
                if dist <= 0:
                    continue
                score = o["O"] * dzone["D"] * math.exp(-lamb * dist)
                candidates.append((dzid, dist, score))

            if not candidates:
                continue

            candidates.sort(key=lambda x: -x[2])
            for dzid, dist, score in candidates[:topk]:
                fl = float(score)
                if demand_scale is not None and demand_scale > 0:
                    fl *= float(demand_scale)
                OD.append((ozid, dzid, fl, float(dist)))

        if not OD:
            raise QgsProcessingException("Synthetic OD is empty. Check lambda, grid, population, and POI.")

        if od_csv_out:
            try:
                out_dir = os.path.dirname(od_csv_out)
                if out_dir:
                    os.makedirs(out_dir, exist_ok=True)
                with open(od_csv_out, "w", encoding="utf-8", newline="") as fh:
                    w = csv.writer(fh)
                    w.writerow(["origin_zone", "dest_zone", "flow", "dist"])
                    for row in OD:
                        w.writerow([row[0], row[1], row[2], row[3]])
            except Exception as e:
                feedback.pushInfo(f"Gagal menulis OD CSV: {e}")

        total_demand = sum(r[2] for r in OD)
        feedback.pushInfo(f"OD pairs: {len(OD)} | Total synthetic demand: {total_demand}")

        # Precompute gen and att for zone polygons
        gen_sum = {zid2: 0.0 for zid2 in zone_ids}
        att_sum = {zid2: 0.0 for zid2 in zone_ids}
        for oz, dz, fl, _dist in OD:
            if oz in gen_sum:
                gen_sum[oz] += float(fl)
            if dz in att_sum:
                att_sum[dz] += float(fl)

        # UE helpers
        rep_eids = set(pair_to_eid.values())
        x_old = {eid: 0.0 for eid in rep_eids}
        iter_log = []

        def bpr_cost(t0, v, capv):
            capv = max(float(capv), float(min_cap))
            x = max(0.0, float(v) / capv)
            return float(t0) * (1.0 + float(bpr_a) * (x ** float(bpr_b)))

        def path_cost(nodes):
            csum = 0.0
            for a, b in zip(nodes[:-1], nodes[1:]):
                csum += float(G[a][b]["weight"])
            return csum

        def gen_paths(s, t):
            sp = nx.shortest_path(G, s, t, weight="weight")
            c0 = path_cost(sp)
            if assign_method == 0:
                return [(sp, c0)]
            out = []
            try:
                gen = nx.shortest_simple_paths(G, s, t, weight="weight")
                for p in gen:
                    cp = path_cost(p)
                    if cp > c0 * detour_max:
                        break
                    out.append((p, cp))
                    if len(out) >= k_paths:
                        break
                if not out:
                    out = [(sp, c0)]
            except Exception:
                out = [(sp, c0)]
            return out

        def assignment_once():
            x_hat = {eid: 0.0 for eid in rep_eids}
            nOD = len(OD)
            stride = max(1, int(nOD / 25))
            for idx, (oz, dz, fl, _dist) in enumerate(OD):
                if feedback.isCanceled():
                    break
                if idx % stride == 0:
                    feedback.setProgress(int(100.0 * idx / max(1, nOD)))

                s = zone_to_node.get(oz)
                t = zone_to_node.get(dz)
                if not s or not t or s not in G or t not in G:
                    continue

                try:
                    paths = gen_paths(s, t)
                except Exception:
                    continue
                if not paths:
                    continue

                if assign_method == 0:
                    p, _cp = paths[0]
                    for a, b in zip(p[:-1], p[1:]):
                        pair = tuple(sorted([a, b]))
                        eid = pair_to_eid.get(pair, None)
                        if eid in x_hat:
                            x_hat[eid] += float(fl)
                else:
                    edge_count = {}
                    for p, _cp in paths:
                        for a, b in zip(p[:-1], p[1:]):
                            pair = tuple(sorted([a, b]))
                            eid = pair_to_eid.get(pair, None)
                            if eid is None:
                                continue
                            edge_count[eid] = edge_count.get(eid, 0) + 1

                    Vk = []
                    for p, cp in paths:
                        Lk = cp if cp > 0 else 1.0
                        ps = 0.0
                        for a, b in zip(p[:-1], p[1:]):
                            pair = tuple(sorted([a, b]))
                            eid = pair_to_eid.get(pair, None)
                            if eid is None:
                                continue
                            le = float(edge_t0_by_eid.get(eid, 0.0))
                            ce = max(1, edge_count.get(eid, 1))
                            ps += (le / Lk) * (1.0 / ce)
                        ps = max(ps, 1e-12)
                        Vk.append((-cp) + beta * math.log(ps))

                    vmax = max(Vk)
                    wv = [math.exp(v - vmax) for v in Vk]
                    sw = sum(wv) if wv else 1.0
                    probs = [wi / sw for wi in wv]

                    for (p, _cp), pr in zip(paths, probs):
                        fpr = float(fl) * float(pr)
                        for a, b in zip(p[:-1], p[1:]):
                            pair = tuple(sorted([a, b]))
                            eid = pair_to_eid.get(pair, None)
                            if eid in x_hat:
                                x_hat[eid] += fpr

            return x_hat

        # Run assignment or UE
        if not enable_ue:
            x_old = assignment_once()
            iter_log = [(1, 0.0, total_demand, 0.0)]
        else:
            for it in range(1, max_iters + 1):
                if feedback.isCanceled():
                    break

                x_hat = assignment_once()
                step = (1.0 / float(it)) if use_msa else 1.0
                x_new = {}

                num = 0.0
                for eid in rep_eids:
                    xo = x_old.get(eid, 0.0)
                    xn = xo + step * (x_hat.get(eid, 0.0) - xo)
                    x_new[eid] = xn
                    num += abs(xn - xo)

                den = sum(abs(x_new[eid]) for eid in rep_eids)
                gap = num / max(1e-9, den)

                for (u, v) in G.edges():
                    pair = tuple(sorted([u, v]))
                    eid = pair_to_eid.get(pair, None)
                    if eid is None:
                        continue
                    t0 = edge_t0_by_eid.get(eid, None)
                    capv = edge_cap_by_eid.get(eid, None)
                    if t0 is None or capv is None:
                        continue
                    G[u][v]["weight"] = float(bpr_cost(t0, x_new.get(eid, 0.0), capv))

                total_delay = 0.0
                for eid in rep_eids:
                    t0 = edge_t0_by_eid[eid]
                    capv = edge_cap_by_eid[eid]
                    vflow = x_new.get(eid, 0.0)
                    t = bpr_cost(t0, vflow, capv)
                    total_delay += max(0.0, (t - t0) * vflow)

                iter_log.append((it, gap, total_demand, total_delay))
                feedback.pushInfo(f"Iter {it}: gap={gap:.6f}, total_delay={total_delay:.3f}")

                x_old = x_new
                if gap < eps_gap:
                    feedback.pushInfo(f"Konvergen pada iterasi {it}")
                    break

        if log_csv:
            try:
                out_dir = os.path.dirname(log_csv)
                if out_dir:
                    os.makedirs(out_dir, exist_ok=True)
                with open(log_csv, "w", encoding="utf-8", newline="") as fh:
                    w = csv.writer(fh)
                    w.writerow(["iter", "gap", "total_demand", "total_delay"])
                    for row in iter_log:
                        w.writerow(list(row))
            except Exception as e:
                feedback.pushInfo(f"Gagal menulis LOG CSV: {e}")

        # =========================================================
        # Outputs: edges
        # =========================================================
        edges_fields = QgsFields()
        edges_fields.append(QgsField("edge_id", QVariant.Int))
        edges_fields.append(QgsField("fclass", QVariant.String))
        edges_fields.append(QgsField("t0", QVariant.Double))
        edges_fields.append(QgsField("cap", QVariant.Double))
        edges_fields.append(QgsField("flow", QVariant.Double))
        edges_fields.append(QgsField("cost", QVariant.Double))
        edges_fields.append(QgsField("vc", QVariant.Double))
        edges_fields.append(QgsField("delay", QVariant.Double))
        edges_fields.append(QgsField("length", QVariant.Double))

        edges_sink, edges_sink_id = self.parameterAsSink(
            parameters, self.OUT_EDGES, context, edges_fields, QgsWkbTypes.LineString, net_layer.crs()
        )

        def final_cost(t0, v, capv):
            return bpr_cost(t0, v, capv) if enable_ue else float(t0)

        for eid in rep_eids:
            geom = edge_geom_by_eid.get(eid, None)
            if geom is None or geom.isEmpty():
                continue
            vflow = x_old.get(eid, 0.0)
            t0 = edge_t0_by_eid[eid]
            capv = edge_cap_by_eid[eid]
            cost = final_cost(t0, vflow, capv)
            vc = (vflow / capv) if capv > 0 else 0.0
            delay = max(0.0, (cost - t0) * vflow) if enable_ue else 0.0
            length = edge_len_by_eid.get(eid, 0.0)
            cls = edge_cls_by_eid.get(eid, "")

            ft = QgsFeature(edges_fields)
            ft["edge_id"] = int(eid)
            ft["fclass"] = cls
            ft["t0"] = float(t0)
            ft["cap"] = float(capv)
            ft["flow"] = float(vflow)
            ft["cost"] = float(cost)
            ft["vc"] = float(vc)
            ft["delay"] = float(delay)
            ft["length"] = float(length)
            ft.setGeometry(geom)
            edges_sink.addFeature(ft, QgsFeatureSink.FastInsert)

        # =========================================================
        # Outputs: zones polygons
        # =========================================================
        zones_fields = QgsFields()
        zones_fields.append(QgsField("zone_id", QVariant.Int))
        zones_fields.append(QgsField("poi_n", QVariant.Int))
        zones_fields.append(QgsField("pop_sum", QVariant.Double))
        zones_fields.append(QgsField("O_mass", QVariant.Double))
        zones_fields.append(QgsField("D_mass", QVariant.Double))
        zones_fields.append(QgsField("gen", QVariant.Double))
        zones_fields.append(QgsField("att", QVariant.Double))
        zones_fields.append(QgsField("node_key", QVariant.String))
        zones_fields.append(QgsField("snap_dist", QVariant.Double))
        zones_fields.append(QgsField("cx", QVariant.Double))
        zones_fields.append(QgsField("cy", QVariant.Double))

        zones_sink, zones_sink_id = self.parameterAsSink(
            parameters, self.OUT_ZONES, context, zones_fields, QgsWkbTypes.Polygon, crs
        )

        for zid2 in zone_ids:
            z = zone_by_id[zid2]
            g = z["geom"]
            if g is None or g.isEmpty():
                continue
            nk = zone_to_node.get(zid2, "")
            sd = zone_snap_dist.get(zid2, None)
            pop_sum_val = z["pop_sum"] if z["pop_sum"] is not None else None

            ft = QgsFeature(zones_fields)
            ft["zone_id"] = int(zid2)
            ft["poi_n"] = int(z.get("poi_n", 0))
            ft["pop_sum"] = float(pop_sum_val) if pop_sum_val is not None else None
            ft["O_mass"] = float(z["O"])
            ft["D_mass"] = float(z["D"])
            ft["gen"] = float(gen_sum.get(zid2, 0.0))
            ft["att"] = float(att_sum.get(zid2, 0.0))
            ft["node_key"] = str(nk)
            ft["snap_dist"] = float(sd) if sd is not None else None
            ft["cx"] = float(z["cent"].x())
            ft["cy"] = float(z["cent"].y())
            ft.setGeometry(g)
            zones_sink.addFeature(ft, QgsFeatureSink.FastInsert)

        # =========================================================
        # Outputs: OD desire lines
        # =========================================================
        od_fields = QgsFields()
        od_fields.append(QgsField("od_id", QVariant.Int))
        od_fields.append(QgsField("origin", QVariant.Int))
        od_fields.append(QgsField("dest", QVariant.Int))
        od_fields.append(QgsField("flow", QVariant.Double))
        od_fields.append(QgsField("dist", QVariant.Double))
        od_fields.append(QgsField("skim_t0", QVariant.Double))
        od_fields.append(QgsField("method", QVariant.String))

        od_sink, od_sink_id = self.parameterAsSink(
            parameters, self.OUT_OD_LINES, context, od_fields, QgsWkbTypes.LineString, crs
        )

        # Optional skim of shortest time using current graph weights (after UE)
        # If UE enabled, weights are last updated. If UE disabled, weights are t0.
        def _skim_time(s_node, t_node):
            try:
                return float(nx.shortest_path_length(G, s_node, t_node, weight="weight"))
            except Exception:
                return None

        method_label = "AoN" if assign_method == 0 else "PSL"

        od_id = 0
        for oz, dz, fl, dist in OD:
            if oz not in zone_by_id or dz not in zone_by_id:
                continue
            op = zone_by_id[oz]["cent"]
            dp = zone_by_id[dz]["cent"]
            line = QgsGeometry.fromPolylineXY([op, dp])

            s_node = zone_to_node.get(oz)
            t_node = zone_to_node.get(dz)
            skim = _skim_time(s_node, t_node) if (s_node and t_node) else None

            od_id += 1
            ft = QgsFeature(od_fields)
            ft["od_id"] = int(od_id)
            ft["origin"] = int(oz)
            ft["dest"] = int(dz)
            ft["flow"] = float(fl)
            ft["dist"] = float(dist)
            ft["skim_t0"] = float(skim) if skim is not None else None
            ft["method"] = method_label
            ft.setGeometry(line)
            od_sink.addFeature(ft, QgsFeatureSink.FastInsert)

        results = {
            self.OUT_EDGES: edges_sink_id,
            self.OUT_ZONES: zones_sink_id,
            self.OUT_OD_LINES: od_sink_id
        }
        if od_csv_out:
            results[self.OD_CSV_OUT] = od_csv_out
        if log_csv:
            results[self.LOG_CSV] = log_csv
        return results
