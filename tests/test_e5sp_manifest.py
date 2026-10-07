"""Static validator for the LOCKED E5-SP shadow-price/obstruction manifest (data/manifests/e5sp_shadowprice_inputs.json).

Per the external reviewer ruling + freeze patch preserved in
results/provenance/decommissioned_plan_agent_sources.json: the E5-SP inputs/observable/shells/
Omega/gates must be locked before build so the builder cannot improvise after seeing the residual price. Asserts the design is FAITHFUL
to the ruling and the non-degeneracy guarantees (no cumulative-row lambda_max; disjoint shells; row-count-null normalization
N=Xi/q_row_0.95 [NOT fixed/effective-rank]; row-count + proxy controls).
"""
import json
import os

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(HERE, "data", "manifests", "e5sp_shadowprice_inputs.json")


def _load():
    with open(MANIFEST) as fh:
        return json.load(fh)


def test_required_blocks():
    m = _load()
    for k in ("decisive_observable", "heterogeneity_proxy", "stage_shells_DISJOINT", "L_geom",
              "audit_metric_C_and_covariance_floors", "Omega_budget", "models", "power_rule", "slack", "gates",
              "outcome_statuses", "phases", "inputs_trust", "inputs_discard", "naming_discipline"):
        assert k in m, f"missing block: {k}"
    assert m["design_version"] == "E5-SP-v1"


def test_observable_is_disjoint_budgeted_not_cumulative():
    obs = _load()["decisive_observable"]
    f = obs["formula"]
    assert "lambda_max" in f and "Omega" in f and "]_+" in f, "pi must be [lambda_max(N(Xi)-Omega)]_+"
    # explicitly NOT the discarded degenerate observable
    notlist = " ".join(obs["NOT"]).lower()
    assert "cumulative" in notlist, "must explicitly exclude the cumulative-row lambda_max observable"
    g = " ".join(obs["non_degeneracy_guarantees"]).lower()
    assert "disjoint" in g and ("row-count" in g or "row count" in g), \
        "non-degeneracy guarantees must include disjoint shells and row-count control"
    assert "N_normalization" in obs
    # reviewer freeze 2.1 — the row-count-null normalizer N=Xi/q_row_0.95 (NOT fixed-rank projection)
    assert "q_row_0.95" in f, "observable must use the row-count-null normalizer q_row_0.95"
    assert "fixed-rank" in obs["N_normalization"].lower(), "N_normalization must rule OUT fixed-rank projection"
    rcn = obs["row_count_null"]
    assert rcn["seed_and_generator_committed_before_pi"] is True, "row-null seed+generator must be committed before pi"
    assert "2000" in rcn["draws_B"], "row-null draws B>=2000 (1000 acceptable)"
    matches = " ".join(rcn["rownull_matches"]).lower()
    assert "no physical w_{f,s}/h alignment" in matches or "no physical" in matches, \
        "row-null surrogates must NOT carry the physical W/H alignment"


def test_shells_are_disjoint_and_enough():
    s = _load()["stage_shells_DISJOINT"]
    assert "DISJOINT" in s["rule"] and "NOT cumulative" in s["rule"]
    kids = s["KiDS-Legacy"]["shells"]
    hsc = s["HSC-Y3"]["shells"]
    assert len(kids) >= 2 and len(hsc) >= 2, "each within-family-slope family needs >=2 disjoint shells (Gate 0)"
    # pin the exact frozen edges (m15 — guard against drift)
    assert kids == [[1, 2], [3, 4], [5, 6]], "KiDS COSEBIs mode bands must be the frozen disjoint set"
    assert hsc == [[300, 600], [600, 1000], [1000, 1500], [1500, 1800]], "HSC ell bands must be the frozen disjoint set"
    # KiDS mode bands disjoint
    flat = [x for band in kids for x in band]
    assert len(flat) == len(set(flat)), "KiDS mode bands must be disjoint"
    # HSC ell bands disjoint and ordered
    for a, b in zip(hsc, hsc[1:]):
        assert a[1] <= b[0], "HSC ell bands must be disjoint/ordered"
    # CMB-lensing is held-out (edges declared-at-freeze) — must carry an explicit lofo_role
    assert "lofo_role" in s["CMB-lensing"] and "held-out" in s["CMB-lensing"]["lofo_role"].lower()


def test_heterogeneity_proxy_and_ablation():
    h = _load()["heterogeneity_proxy"]
    # primary H must be the POSITIVE PART of log(P_nl/P_lin) — the load-bearing nonlinearity (ruling critique #5)
    assert "log( P_nl" in h["primary_H"] and "]_+" in h["primary_H"], \
        "primary H must be the positive part [.]_+ of log(P_nl/P_lin), not a bare/signed average"
    # secondary H' must be the SQUARED positive part
    assert "P_nl/P_lin" in h["secondary_Hprime"] and "_+^2" in h["secondary_Hprime"], \
        "secondary H' must be the squared positive part (P_nl/P_lin-1)_+^2"
    assert h["proxy_is_candidate_not_currency"] is True
    abl = " ".join(h["proxy_ablation_required"]).lower()
    assert "permuted" in abl and ("scale" in abl and "noise" in abl), "proxy ablation must include permuted + scale-matched-noise"
    assert "BEFORE" in h["blinding"], "H must be frozen BEFORE any pi (blinding)"


def test_omega_has_all_six_floors_incl_rowcount():
    ob = _load()["Omega_budget"]
    for floor in ("Omega_same_family", "Omega_linear_synthetic", "Omega_nuisance_systematics",
                  "Omega_theory", "Omega_row_count", "Omega_proxy"):
        assert floor in ob and ob[floor], f"Omega budget missing floor {floor}"
    assert "equal-row-count" in ob["Omega_row_count"].lower(), "Omega_row_count must be the equal-row-count null"
    # reviewer 2.1 — in normalized units the row-count floor is q_row_0.95-absorbed to a unit threshold
    assert "q_row_0.95" in ob["Omega_row_count"] and "normalized" in ob["Omega_row_count"].lower(), \
        "Omega_row_count must reference the q_row_0.95 normalization (=1 in normalized units)"
    # reviewer 2.4 — Delta_margin pinned to 0.10 normalized units + the {0.05,0.10,0.20} sensitivity triple
    assert "0.10" in ob["Delta_margin"], "Delta_margin must be pinned to 0.10 (reviewer 2.4)"
    assert "0.05" in ob["Delta_margin"] and "0.20" in ob["Delta_margin"], \
        "Delta_margin must declare the {0.05,0.10,0.20} sensitivity set"
    assert "DECLARATION split" in ob["frozen"] and "BEFORE witness" in ob["frozen"]


def test_covariance_C_has_all_eight_floors():
    # mirror the six-Omega-floor guard: lock the 8 covariance-C floors against silent drift (reviewer 'must include' list)
    cf = _load()["audit_metric_C_and_covariance_floors"]
    floors = " ".join(cf["must_include_floors"]).lower()
    for need in ("ia/tatt", "photo-z", "shear", "baryon", "backend", "conditioning", "pipeline", "shared-wl"):
        assert need in floors, f"covariance C must include the {need} floor"
    swr = cf["shared_WL_rule"].lower()
    assert "diagonal-only" in swr and "may not pass" in swr, \
        "shared-WL rule must forbid passing under diagonal-only cross-family covariance"


def test_four_models_plus_row_and_lofo():
    mods = _load()["models"]
    for k in ("M_Lambda", "M_U", "M_F4_SP", "M_sys", "M_row"):
        assert k in mods, f"missing model {k}"
    assert "A>0" in mods["M_F4_SP"] and "H_slack" in mods["M_F4_SP"]
    # M_U must carry the no-H qualifier AND the reducibility precondition (m8/m16)
    assert ("NO H dependence" in mods["M_U"] or "no h dependence" in mods["M_U"].lower())
    assert "reduce" in mods["M_U"].lower() and ("row count" in mods["M_U"].lower() or "row-count" in mods["M_U"].lower())
    assert "LOFO" in mods["comparison"]
    # reviewer 2.2 — slack-anchored excess price dependent variable (no per-family intercept carries it)
    dv = mods["dependent_variable"].lower()
    assert "pi_bar" in dv and "median" in dv and "slack-anchored" in dv, \
        "models must be fit on the slack-anchored excess price y=pi-pi_bar_{f,slack}"
    # reviewer 2.5 — pre-registered M_sys regressor list; H/H'/k_eff/L_eff excluded; M_row on log r_eff
    Z = mods["M_sys_regressors"]["Z"]
    for tok in ("I_WL", "kappa(Sigma", "r_eff", "U_{f,s}", "P_{f,s}"):
        assert tok in Z, f"M_sys regressor Z must include {tok}"
    assert "[ 1," in Z or "[1," in Z.replace(" ", ""), "Z must lead with the intercept 1"
    assert "log10 kappa" in Z and "log r_eff" in Z, "Z must use log10 kappa(Sigma) and log r_eff transforms"
    fit = mods["M_sys_regressors"]["fit"].lower()
    assert "k_eff" in fit and "l_eff" in fit and "not primary" in fit, "primary M_sys must EXCLUDE H/H'/k_eff/L_eff"
    assert "Omega_total" in mods["M_sys_regressors"]["U"], "U = (Omega_nuisance/sys + Omega_theory)/Omega_total"
    assert "systematics-proxy" in mods["M_sys"], "M_sys must carry the 'beats M_F4/SP => systematics-proxy' consequence"
    assert "r_eff" in mods["M_row"] and "log" in mods["M_row"].lower(), "M_row must be beta0+beta1*log r_eff"
    assert "NEVER added" in mods["H_prime_not_extra_points"], "H' must never be added as extra observations"


def test_gates_0_through_6():
    g = _load()["gates"]
    keys = list(g)
    for i in range(7):
        assert any(f"G-E5SP-{i}" in k for k in keys), f"missing gate G-E5SP-{i}"
    # slack threshold + decisive-vs-characterization + per-family slack/binding requirement (reviewer 2.3)
    g2 = g["G-E5SP-2_slack_regime"]
    assert "0.05" in g2 and "characterization" in g2
    assert "slack shell" in g2.lower() and "binding shell" in g2.lower(), \
        "Gate-2 must require >=1 slack AND >=1 binding shell per family"
    # binding margins + slack-anchored excess price + power rule (reviewer 2.2)
    g3 = g["G-E5SP-3_binding_heterogeneity"]
    assert ("2*SE" in g3 or "2 SE" in g3) and "BIC>=6" in g3.replace(" ", "")
    assert "slack-anchored" in g3.lower() and "power_rule" in g3.lower() and "m_sys" in g3.lower(), \
        "Gate-3 must fit the slack-anchored y, beat M_sys too, and be power-rule-gated"
    # proxy-failure includes cumulative-row + survey-label
    g4 = g["G-E5SP-4_proxy_failure_no_manufacture"].lower()
    assert "cumulative-row" in g4 and "survey-label" in g4 and "row-count" in g4
    # zero controls include P_nl=P_lin and held-out-removed and rotation
    g5 = g["G-E5SP-5_zero_controls"]
    assert "P_nl=P_lin" in g5 and "removed from BOTH L and D" in g5 and "rotation" in g5
    # M5 — control (6) must keep the operative 'destroys the window/heterogeneity alignment' qualifier
    assert "DESTROY" in g5.upper() and "alignment" in g5.lower(), \
        "Gate-5 rotation control must DESTROY the window/heterogeneity alignment (not just preserve covariance)"


def test_slack_and_lgeom_resolution():
    m = _load()
    sl = m["slack"]
    assert abs(sl["H_slack_primary"] - 0.05) < 1e-12
    assert sl["choose_before_running"] is True
    assert m["L_geom"]["N_posterior_min"] >= 256, "L_geom must resolve geometry dof (old N=4 -> rank 3 was the bug)"
    assert m["L_geom"]["single_whitening"] is True
    # reviewer 2.3 — per-family slack anchor + Phase-B stop; bottom-quartile is robustness only
    pfa = sl["per_family_anchor"].lower()
    assert "slack shell" in pfa and "binding shell" in pfa, "slack block must require >=1 slack + >=1 binding shell per family"
    assert "STOP" in sl["phase_B_stop"].upper(), "Phase B must STOP if the per-family slack rule fails"
    assert "robustness" in sl["robustness"].lower() and "only" in sl["robustness"].lower(), \
        "bottom-quartile-of-H must be robustness-only, not the decisive threshold"


def test_power_rule():
    pr = _load()["power_rule"]
    joined = " ".join(pr["decisive_requires_all"]).lower()
    assert "3 families" in joined and "binding" in joined and "slack" in joined and "9" in joined, \
        "power rule must require >=3 families x >=2 shells, >=1 slack & >=1 binding per family, >=9 rows"
    assert "underpowered" in pr["else_status"].lower()


def test_cmb_tertiles_and_sigma_estimation():
    m = _load()
    cmb = m["stage_shells_DISJOINT"]["CMB-lensing"]
    # reviewer 2.4 — three equal-count L_eff-ordered tertile shells (not hand-picked, not post-hoc)
    assert "L_eff" in cmb["ordering"], "CMB shells must be ordered by bandpower effective multipole L_eff"
    assert "floor(n_L/3)" in cmb["shells"], "CMB shells must be equal-count L_eff tertiles floor(n_L/3)"
    # reviewer 2.4 — membership frozen before H + (L_min,L_max,L_eff) recorded in the H table (provenance)
    assert "FROZEN before H" in cmb["shells"], "CMB shell membership must be frozen before H"
    assert "L_min" in cmb["shells"] and "L_eff" in cmb["shells"], "CMB block must record (L_min,L_max,L_eff)"
    assert "L_eff" in m["phases"]["B"], "Phase B H-table column schema must record L_eff (the CMB provenance)"
    # per-floor Sigma recipe present + PD/condition gate
    sig = m["audit_metric_C_and_covariance_floors"]["Sigma_estimation"]
    assert "J_nu" in sig and "PD" in sig, "per-floor Sigma recipe must specify J_nu Pi_nu J_nu^T and the PD/condition gate"


def test_freeze_status_resolved():
    m = _load()
    assert "DESIGN-FROZEN" in m["status"] and "Phase B" in m["status"], "status must be DESIGN-FROZEN pending Phase B"
    assert "resolved_freeze_patch" in m, "the resolved freeze patch block must be present"
    assert "provisional_pending_rereview" not in m, "no item may remain provisional after the freeze patch"
    items = m["resolved_freeze_patch"]["items"]
    for k in ("N_normalization", "statistical_power", "slack_existence", "CMB_and_floors", "M_sys"):
        assert k in items, f"resolved_freeze_patch missing {k}"


def test_discards_and_naming_discipline():
    m = _load()
    disc = " ".join(m["inputs_discard"]).lower()
    assert "e5_v3a" in disc and "e5_shadowprice" in disc, "must discard the v3a + shadowprice artifacts"
    nd = " ".join(m["naming_discipline"]).lower()
    assert "candidate" in nd, "pi is a CANDIDATE obstruction price until it passes the gates"
    assert "f4-compatible" in nd or "f4-inspired" in nd, "F4 must be called compatible/inspired, NOT proven (reviewer critique 2.3)"
    assert "w0wa" in nd and "geometry" in nd, "must state the test does not reduce to beating w0wa on geometry"


def test_outcome_statuses():
    st = _load()["outcome_statuses"]
    assert len(st) == 5
    j = " ".join(st).lower()
    for need in ("shadow-price", "universal-layer", "plain-geometry", "systematics", "underpowered"):
        assert need in j, f"missing outcome status containing {need}"
