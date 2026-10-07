#!/usr/bin/env python3
"""Exact first-ANY-patch threshold evidence for the original N32/N128 inputs.

Read the immutable reified populations; do not resample or integrate an ODE.
Default: verify byte replay. --write: write this packet's exact report.
"""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'results/patch_ratio_2026-10-03/thresholds.json'


def construct():
    data = json.loads((ROOT / 'results/patch_count_2026-10-03/populations.json').read_text())
    delta = F(data['model_scalars_decimal']['delta_c'])
    variants = []
    for group in data['variants']:
        n = group['n_patches']
        assert n in (32, 128)
        rows = group['populations']
        thresholds = []
        first = []
        for row in rows:
            a = list(map(F, row['amplitudes_exact']))
            tags = row['tags']
            assert len(a) == len(tags) == n and all(x >= 0 for x in a)
            maxima = [max(x for x, tag in zip(a, tags) if tag == b) for b in (False, True)]
            assert all(m > 0 for m in maxima)
            assert list(map(F, row['tag_maxima_exact'])) == maxima
            thresholds.append(max(delta/m for m in maxima))
            assert thresholds[-1] == F(row['threshold_exact'])
            first.append(delta/max(maxima))
            assert first[-1] == min(delta/m for m in maxima)
        assert len(rows) == 12
        aggregate = sorted(thresholds)[9]
        assert aggregate == F(group['aggregate_threshold_exact'])
        assert sum(t < aggregate for t in thresholds) == 9
        assert sum(t <= aggregate for t in thresholds) == 10
        c = aggregate/965
        assert F(1, 5) < c < 4
        low, high = (F(129, 100), F(131, 100)) if n == 32 else (F(83, 100), F(84, 100))
        assert low < c < high
        assert all(1 < t < 2000 and 450*c < t < 897*c for t in first)
        # A real false-target control: the original N64 lower bound does not
        # survive to all N32 seeds. A changed readout is also detectable.
        failures_500 = [row['seed'] for row, t in zip(rows, first) if not 500*c < t]
        wrong_readout = [row['seed'] for row, t, f in zip(rows, thresholds, first) if t != f]
        assert wrong_readout
        if n == 32:
            assert failures_500
        variants.append({
            'n_patches': n, 'lean_variant': group['lean_variant'],
            'aggregate_threshold_exact': str(aggregate), 'normalization_scale_exact': str(c),
            'normalization_reference': '965, only a variable change; original growth and data fixed',
            'first_ANY_patch_thresholds_exact': [str(t) for t in first],
            'normalized_first_thresholds_exact': [str(t/c) for t in first],
            'bounds': {'first': '(1,2000)', 'normalized_first': '(450,897)', 'scale': f'({low},{high})'},
            'false_500_lower_bound_failing_seeds': failures_500,
            'changed_two_tag_readout_detected_seeds': wrong_readout,
        })
    assert [g['n_patches'] for g in variants] == [32, 128]
    return json.dumps({'arithmetic': 'Python Fraction only; no float, RNG or ODE',
                       'input': 'results/patch_count_2026-10-03/populations.json',
                       'variants': variants}, indent=2) + '\n'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    report = construct()
    if args.write:
        REPORT.parent.mkdir(parents=True, exist_ok=True)
        REPORT.write_text(report)
    else:
        assert REPORT.read_text() == report
    print('Exact N32/N128 first-threshold bounds and false-target controls passed; byte replay matched.'
          if not args.write else 'Exact N32/N128 threshold report written.')


if __name__ == '__main__':
    main()
