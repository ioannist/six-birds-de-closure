from fractions import Fraction
import importlib.util
from pathlib import Path
import sys

import numpy as np
import pytest

MODULE_PATH = Path(__file__).resolve().parents[1] / "scripts/de_original_claim_checks.py"
sys.path.insert(0, str(MODULE_PATH.parent))
SPEC = importlib.util.spec_from_file_location("de_original_claim_checks", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)


def test_original_history_bridge_and_tag_counterexample():
    receipt = checks.recompute()
    assert 0.4388 < receipt["cpl"]["crossing_float"] < 0.4389
    assert [r["RS"] for r in receipt["tag_counterexample"]] == [False, True, False]
    threshold = Fraction(receipt["window_threshold"]["aggregate_threshold_exact"])
    assert Fraction(3, 2) < threshold < 20000
    assert receipt["window_threshold"]["required_seeds"] == 10
    assert receipt["window_threshold"]["original_carrier_threshold_checks"] == 60


def test_iid_law_matches_disjoint_enumeration_and_population_ordering():
    p, q = Fraction(3, 7), Fraction(2, 5)
    probabilities = [checks.iid_record_probability(n, p, q) for n in range(7)]
    assert probabilities[:2] == [0, 0]
    for n, probability in enumerate(probabilities):
        assert probability == checks.enumerate_record_probability(n, p, q)
    assert all(x < y for x, y in zip(probabilities[1:], probabilities[2:]))


def test_tag_dependence_also_occurs_with_full_support():
    assert checks.iid_record_probability(2, Fraction(1), Fraction(1, 2)) == Fraction(1, 2)
    assert checks.iid_record_probability(2, Fraction(1), Fraction(1, 4)) == Fraction(3, 8)


@pytest.mark.parametrize("n,p,q", [(-1, Fraction(1), Fraction(1, 2)),
                                   (2, Fraction(-1), Fraction(1, 2)),
                                   (2, Fraction(1, 2), Fraction(2))])
def test_population_law_rejects_invalid_parameters(n, p, q):
    with pytest.raises(ValueError, match="probabilities"):
        checks.iid_record_probability(n, p, q)


def test_fluid_is_derivative_of_same_expansion_history():
    # An independent finite-difference check exercises the existing expansion
    # implementation rather than differentiating the new symbolic formula.
    w0, wa = -0.7946824224094571, -0.6731772288179667
    matter, radiation, amplitude = 0.316, 0.0001, 0.6839
    z = np.array([0.0, 0.2, 0.6, 1.5])
    step = 1e-5

    def additive(t):
        return checks.bg._e_z(t, omega_m=matter, omega_r=radiation,
                              omega_de=amplitude, w0_fld=w0, wa_fld=wa)**2 - matter*(1+t)**3 - radiation*(1+t)**4

    slope = (additive(z + step) - additive(z - step)) / (2*step)
    inferred = -1 + (1+z)*slope/(3*additive(z))
    np.testing.assert_allclose(inferred, w0 + wa*z/(1+z), rtol=0, atol=1e-8)
