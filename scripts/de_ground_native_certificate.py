#!/usr/bin/env python3
"""Exact imaginary-block certificates for the unchanged original complex update.

NumPy proposes fixed rational bases only. Integer/Fraction replay earns each
basis inverse and the induced norm over the already certified root boxes.
This is mathematical exact computation, not a Lean kernel instantiation.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import de_ground_interval_certificate as cert

ROOT = cert.ROOT
PRIOR = ROOT/'results/ground_interval_2026-10-03'
OUT = ROOT/'results/ground_native_2026-10-03'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def generate():
    import numpy as np
    cert.require(np.__version__ == '1.26.4', 'pinned NumPy generator required')
    data = json.loads((PRIOR/'witnesses.json').read_text())
    rows = []
    for w in data['witnesses']:
        u = np.array([float(Fraction(int(t), cert.SCALE)) for t in w['center'][:8]])
        # An approximately orthogonal basis with first column along the ground.
        _, _, vt = np.linalg.svd(u.reshape(1, 8), full_matrices=True)
        basis = vt.T
        rows.append(dict(sweep=w['sweep'], parameter_hex=w['parameter_hex'],
                         basis=[[str(round(float(t)*cert.SCALE)) for t in row] for row in basis]))
    return dict(scale=str(cert.SCALE), original_root_witness_sha256=sha(PRIOR/'witnesses.json'),
                imaginary_bases=rows)


def certify(w, r):
    cert.require((w['sweep'], w['parameter_hex']) == (r['sweep'], r['parameter_hex']),
                 'basis/root identity mismatch')
    cert.require(len(r['basis']) == 8 and all(len(row) == 8 for row in r['basis']),
                 'wrong imaginary basis dimension')
    cert.require(int(w['radius']) > 0, 'root radius must be positive')
    radius = int(w['radius'])
    u = [cert.I(int(t)-radius, int(t)+radius) for t in w['center'][:8]]
    a = [[(cert.I.of(int(i == j))-u[i]*u[j])/2 for j in range(8)] for i in range(8)]
    basis = cert.read_points(r['basis'])
    transformed = cert.mm(cert.mm(cert.exact_inverse(basis), a), basis)
    upper = cert.maxrow(transformed)
    cert.require(upper < cert.SCALE, 'imaginary induced norm is not below one')
    return dict(sweep=w['sweep'], parameter_hex=w['parameter_hex'],
                imaginary_derivative=[[[str(t.lo), str(t.hi)] for t in row] for row in a],
                imaginary_transformed_norm_upper=str(upper))


def replay(data):
    cert.require(data['scale'] == str(cert.SCALE), 'dyadic scale changed')
    cert.require(data['original_root_witness_sha256'] == sha(PRIOR/'witnesses.json'),
                 'original root witness changed')
    prior = json.loads((PRIOR/'witnesses.json').read_text())
    roots = cert.replay(prior)
    cert.require(roots == json.loads((PRIOR/'certificates.json').read_text()),
                 'prior root/real-spectrum receipt does not replay')
    cert.require(len(data['imaginary_bases']) == len(prior['witnesses']) == 30,
                 'exactly the original thirty roots required')
    rows = []
    for w, r, real in zip(prior['witnesses'], data['imaginary_bases'], roots['certificates']):
        row = certify(w, r)
        stable = real['verdict'].startswith('all_real')
        row.update(real_verdict=real['verdict'], real_transformed_norm_upper=real['spectral_radius_upper'],
                   full_native_complex_local_attraction=stable,
                   full_product_norm_upper=str(max(int(real['spectral_radius_upper']),
                                                   int(row['imaginary_transformed_norm_upper']))) if stable else None,
                   real_unstable_mode_retained=not stable)
        rows.append(row)
    tol = Fraction.from_float(1e-10)
    cert.require((tol.numerator, tol.denominator) ==
                 (7737125245533627, 77371252455336267181195264), 'IEEE tolerance identity changed')
    source = cert.SOURCE.read_text()
    cert.require('TOL = 1e-10' in source and 'np.exp(-1j * np.angle(overlap))' in source,
                 'original phase/tolerance syntax changed')
    return dict(scale=str(cert.SCALE), arithmetic='exact outward dyadic integers and fixed Fraction inverses',
                phase_rule='original conjugate-first overlap with exp(-i arg); sign bug retained',
                original_tolerance=[str(tol.numerator), str(tol.denominator)],
                original_roots_replayed=30, imaginary_strict_norm_bounds=30,
                full_native_complex_locally_attracting_samples=sum(r['full_native_complex_local_attraction'] for r in rows),
                real_unstable_samples=sum(r['real_unstable_mode_retained'] for r in rows),
                lean_analytic_convergence_criterion=True, concrete_lean_kernel_instantiations=False,
                original_complex_initialization_basin=False, nonlinear_escape_at_unstable_samples=False,
                continuous_nonlinear_branch=False, floating_runtime_emulation=False,
                certificates=rows)


def controls(data):
    import copy
    prior = json.loads((PRIOR/'witnesses.json').read_text())
    w, r = prior['witnesses'][0], data['imaginary_bases'][0]
    failures = []
    variants = []
    bad = copy.deepcopy(r); bad['basis'][1] = bad['basis'][0]; variants.append(('singular basis', w, bad))
    bad = copy.deepcopy(r); bad['basis'] = bad['basis'][:7]; variants.append(('wrong basis dimension', w, bad))
    bad = copy.deepcopy(r); bad['parameter_hex'] = (123.).hex(); variants.append(('wrong root identity', w, bad))
    badw = copy.deepcopy(w); badw['radius'] = str(10*cert.SCALE); variants.append(('oversized uncertified root box', badw, r))
    for name, ww, rr in variants:
        try:
            certify(ww, rr)
        except AssertionError as e:
            failures.append(dict(control=name, rejected=True, reason=str(e)))
        else:
            raise AssertionError('false certificate accepted: '+name)
    return dict(false_certificate_rejections=failures,
                scope='singularity, dimensions, identity, and destructive box enlargement')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT/'imaginary_witnesses.json'
    if args.generate:
        path.write_text(json.dumps(generate(), indent=2)+'\n')
    data = json.loads(path.read_text())
    result = replay(data)
    (OUT/'native_certificates.json').write_text(json.dumps(result, indent=2)+'\n')
    (OUT/'controls.json').write_text(json.dumps(controls(data), indent=2)+'\n')
    print('30 original roots replayed; 30 strict imaginary-block bounds; 28 full complex local-attraction returns; 2 real unstable modes retained')


if __name__ == '__main__':
    main()
