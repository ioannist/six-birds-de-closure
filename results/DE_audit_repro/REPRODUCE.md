# DE Audit Third-Party Reproduction

This recipe verifies the compressed DE audit without `classy` or Planck `clik`.
The audit path uses the scipy/analytic compressed backend. `classy` is optional
only for explicit `backend="classy"` oracle validation outside this audit.

## Minimal Environment

- Python: `>=3.11,<3.12`
- Install: `pip install -r results/DE_audit_repro/requirements-de-audit.txt`
- The repository data symlinks must resolve to the already fetched E1 data.

## No-Classy Proof Method

The proof run used an import blocker:

```bash
mkdir -p /tmp/de_audit_no_classy
printf 'raise ImportError("blocked for DE audit recomputability proof")\n' > /tmp/de_audit_no_classy/classy.py
printf 'raise ImportError("blocked for DE audit recomputability proof")\n' > /tmp/de_audit_no_classy/clik.py
export PYTHONPATH=/tmp/de_audit_no_classy:$PWD
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
```

## Acceptance Commands

```bash
pytest -q tests/test_de_audit.py
python scripts/de_audit_validate.py --results-dir results/DE_audit
python scripts/de_audit_repro_smoke.py --tolerance-chi2 5.0
```

Expected outputs:

- `tests/test_de_audit.py`: `4 passed`
- `de_audit_validate.py`: `{"mismatch_count": 0, "verdict_match": true}`
- `de_audit_repro_smoke.py`: `passes=true`

Smoke-refit tolerance: absolute `chi2` difference <= `5.0` relative to the
frozen `results/DE_audit/B1_model_table.csv` rows. The recorded proof run gave:

- `lcdm`: frozen `1455.8036842117926`, smoke `1455.79602807367`, delta `-0.007656138122683842`
- `rewrite_power`: frozen `1453.656518313084`, smoke `1453.0257884792682`, delta `-0.6307298338158489`

These are reduced optimizer smoke refits, not a regenerated dynesty campaign.
