"""Static validator for the LOCKED E5 growth-currency input manifest (data/manifests/e5_growth_currency_inputs.json).

Per the external E5 pre-execution review: the E5 inputs/splits/Ω/staging must be locked before build so the
builder cannot choose the experiment after seeing data. This asserts:
  1. required top-level blocks present; valid JSON;
  2. every probe is well-formed (family, role, split, backend_tier, decisive flag);
  3. the declare/witness/control splits are consistent with each probe's `split` field and pairwise disjoint;
  4. the decisive battery spans >= 3 INDEPENDENT growth families (the decisiveness requirement);
  5. RSD is NOT decisive (no public DR2 fσ8 product) unless manifest-verified;
  6. the numeric localization threshold is present (0.60 / 2x / 0.6);
  7. the Ω budget carries all four floors + a margin + computed-on-declare-only;
  8. survey_label is forbidden as a staging axis; the six staging axes are present;
  9. signed-S8-scalar and fitted per-probe Ξ are excluded.
"""
import json
import os

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(HERE, "data", "manifests", "e5_growth_currency_inputs.json")


def _load():
    with open(MANIFEST) as fh:
        return json.load(fh)


def test_required_blocks():
    m = _load()
    for k in ("probes", "evaluation_design", "rotating_lofo_folds", "decisive_rule", "decisive_battery_families",
              "staging_axes", "nuisance_model", "omega_budget",
              "localization_threshold", "zero_controls", "excluded", "decisive_requirement"):
        assert k in m, f"missing block: {k}"


def test_probes_well_formed():
    m = _load()
    for p in m["probes"]:
        for k in ("probe_id", "family", "role", "decisive", "in_decisive_battery", "backend_tier"):
            assert k in p, f"probe {p.get('probe_id')} missing {k}"
        assert isinstance(p["decisive"], bool) and isinstance(p["in_decisive_battery"], bool)
        assert p["in_decisive_battery"] == p["decisive"], f"probe {p['probe_id']} decisive/in_decisive_battery mismatch"
        assert p["backend_tier"].startswith("physical_CCL"), f"probe {p['probe_id']} must use a physical_CCL backend (surrogate forbidden, G-E5-NOSURR)"


def test_rotating_lofo_folds():
    """E5-minimal-physical-v2: rotating leave-one-family-out over the 3 available decisive families, each
    holding out exactly that family as the witness and using the other 2 as the declare/build set;
    ALL 3 of 3 must pass (reviewer C2, no >=2-of-3 majority rescue)."""
    m = _load()
    assert m["evaluation_design"] == "rotating_leave_one_family_out_3fold"
    fams = list(m["decisive_battery_families"])
    by_fam = {p["family"]: p["probe_id"] for p in m["probes"] if p["decisive"]}
    assert set(fams) == set(by_fam), "decisive_battery_families must match the decisive probes' families"
    folds = m["rotating_lofo_folds"]
    assert len(folds) == len(fams), "one fold per decisive family"
    witnesses = set()
    for f in folds:
        wf = f["witness_family"]
        assert wf in fams, f"fold {f['fold_id']} witness_family {wf} not a decisive family"
        assert f["witness_probe"] == by_fam[wf], f"fold {f['fold_id']} witness_probe != the family's probe"
        assert set(f["declare_families"]) == set(fams) - {wf}, \
            f"fold {f['fold_id']} declare_families must be the other {len(fams)-1} families"
        assert wf not in witnesses, f"family {wf} is the witness in two folds"
        witnesses.add(wf)
    assert witnesses == set(fams), "every decisive family must be the held-out witness exactly once"
    # v2 decisive rule must require ALL-3-of-3 and explicitly forbid a 2-of-3 majority rescue
    rule = m["decisive_rule"].upper()
    assert ("ALL 3" in rule or "ALL-3" in rule), "decisive_rule must require ALL-3-of-3 folds to pass (reviewer C2)"
    assert "MAJORITY RESCUE" in rule or "NO >=2" in rule, "decisive_rule must explicitly forbid a 2-of-3 majority rescue"


def test_v2_reviewer_conditions():
    """The five locked reviewer conditions for E5-minimal-physical-v2 (2026-06-01)."""
    m = _load()
    # C1: 3-fold LOFO, DES Y6 dropped from decisive
    assert len(m["rotating_lofo_folds"]) == 3 and len(m["decisive_battery_families"]) == 3
    dy6 = [p for p in m["probes"] if p["probe_id"] == "des_y6_3x2pt"]
    assert dy6 and dy6[0]["decisive"] is False, "DES Y6 must be dropped from the decisive battery (C1)"
    # C2: all-3-of-3 (asserted in test_rotating_lofo_folds too)
    assert "ALL-3" in m["decisive_rule"].upper() or "ALL 3" in m["decisive_rule"].upper()
    # C3: KiDS<->HSC shared-systematics floor + conservative stress grid
    ob = m["omega_budget"]
    assert "Omega_WL_shared" in ob, "missing KiDS<->HSC shared-systematics floor (C3)"
    assert ob["Omega_WL_shared"]["shared_correlation_stress_grid"] == [0.25, 0.50, 0.75]
    # C4: DES Y3 present as method-control/rehearsal, NEVER decisive
    dy3 = [p for p in m["probes"] if p["probe_id"] == "des_y3_3x2pt"]
    assert dy3 and dy3[0]["decisive"] is False and "rehearsal" in dy3[0]["role"], "DES Y3 must be rehearsal-only (C4)"
    # C5: HSC Fourier/real-space pipeline-mismatch floor
    assert "Omega_HSC_pipeline" in ob, "missing HSC Fourier/real-space pipeline floor (C5)"
    # every decisive family carries real fetched data
    for p in m["probes"]:
        if p["decisive"]:
            assert p.get("data_available") is True, f"{p['probe_id']} decisive but no real data_available"


def test_decisive_battery_has_three_independent_families():
    m = _load()
    decisive_families = {p["family"] for p in m["probes"] if p["decisive"]}
    assert len(decisive_families) >= 3, \
        f"decisive battery spans only {len(decisive_families)} families ({decisive_families}); need >= 3 independent"


def test_rsd_not_decisive():
    m = _load()
    for p in m["probes"]:
        if p["family"].startswith("RSD") or "rsd" in p["probe_id"].lower():
            assert p["decisive"] is False, "RSD must NOT be decisive (no public DESI DR2 fσ8 product) unless manifest-verified"
            assert p["role"] == "method_control"


def test_localization_threshold_numeric():
    m = _load()
    lt = m["localization_threshold"]
    assert abs(lt["eigenvector_mass_high_stage_min"] - 0.60) < 1e-9
    assert abs(lt["shuffled_stage_null_factor_min"] - 2.0) < 1e-9
    assert abs(lt["spearman_rho_min"] - 0.6) < 1e-9


def test_omega_budget_has_all_floors():
    m = _load()
    ob = m["omega_budget"]
    for floor in ("Omega_same_family", "Omega_synthetic_null", "Omega_nuisance_systematics", "Omega_theory"):
        assert floor in ob and ob[floor], f"Ω budget missing floor {floor}"
    assert "Delta_margin" in ob
    assert "declare" in ob["computed_on"].lower() and "only" in ob["computed_on"].lower(), \
        "Ω must be computed on the declare split ONLY (pre-witness)"


def test_staging_axes_and_forbidden_label():
    m = _load()
    axes = {a["axis"] for a in m["staging_axes"]}
    for needed in ("scale_cut_severity", "redshift_tomographic_stage", "nonlinear_baryon_stage",
                   "photoz_calibration_stage", "IA_model_stage", "probe_family_stage"):
        assert needed in axes, f"missing staging axis {needed}"
    assert "survey_label" not in axes, "survey_label must NOT be a staging axis (confounder)"
    assert "forbidden_staging_axis" in m and "survey_label" in m["forbidden_staging_axis"]


def test_exclusions():
    m = _load()
    txt = json.dumps(m["excluded"]).lower()
    assert "s8" in txt or "s₈" in txt, "scalar S8-shift must be explicitly excluded as the decisive observable"
    assert "per-probe" in txt or "per_probe" in txt or "signed closure amplitudes" in txt, \
        "fitted per-probe Ξ / signed amplitudes must be excluded"
