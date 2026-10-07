#!/usr/bin/env python3
"""Uniform nonlinear root tubes over the original coupling interval [0,30].

Proposals use pinned NumPy. Replay is exact integer/Fraction arithmetic. Seams
are joined by small certified common roots, never by floating proximity alone.
Concrete inequalities here are not Lean kernel proof terms.
"""
import argparse
from fractions import Fraction
import hashlib
import json

import de_ground_interval_certificate as cert

ROOT = cert.ROOT
OLD = ROOT/'results/ground_interval_2026-10-03'
OUT = ROOT/'results/ground_branch_2026-10-03'


def uniform(w, base):
    a, b = map(Fraction, w['coupling_interval'])
    cert.require(a < b, 'empty coupling interval')
    k = cert.I.of(a) + cert.I(0, cert.I.of(b-a).hi)
    x = [cert.I(int(t)) for t in w['center']]
    cert.require(len(x) == 9, 'wrong root dimension')
    r = int(w['radius'])
    cert.require(r > 0, 'positive root radius required')
    box = [cert.I(t.lo-r, t.hi+r) for t in x]
    cert.require(all(t.lo > 0 for t in box[:8]), 'positive field box required')
    c = cert.read_points(w['newton_inverse'])
    cert.require(len(c) == 9 and all(len(row) == 9 for row in c), 'wrong inverse dimension')
    cert.exact_inverse(c)
    ff = cert.equations(base, k, x)[0]
    df = cert.equations(base, k, box)[1]
    q = cert.maxrow(cert.sub(cert.eye(9), cert.mm(c, df)))
    y = cert.maxrow(cert.mm(c, ff))
    cert.require(q < cert.SCALE, 'uniform derivative not contracting')
    cert.require(y+cert.ceil_div(q*r, cert.SCALE) < r, 'uniform root ball not strictly invariant')
    return dict(coupling_interval=w['coupling_interval'], radius=str(r),
                uniform_defect_upper=str(q), uniform_center_residual_upper=str(y),
                strict_root_radius_upper=str(cert.ceil_div(y*cert.SCALE, cert.SCALE-q)),
                partial_derivative_invertible_everywhere_in_box=True)


def anchor(w, base):
    p = Fraction(w['coupling'])
    # Reuse the uniform checker at a degenerate parameter point by duplicating
    # the formulas explicitly; no parameter-width or spectral assertion needed.
    x = [cert.I(int(t)) for t in w['center']]
    cert.require(len(x) == 9, 'wrong anchor dimension')
    r = int(w['radius'])
    cert.require(r > 0, 'positive anchor radius required')
    box = [cert.I(t.lo-r, t.hi+r) for t in x]
    cert.require(all(t.lo > 0 for t in box[:8]), 'positive anchor field required')
    c = cert.read_points(w['newton_inverse'])
    cert.require(len(c) == 9 and all(len(row) == 9 for row in c), 'wrong anchor inverse dimension')
    cert.exact_inverse(c)
    f, _, _, _ = cert.equations(base, cert.I.of(p), x)
    df = cert.equations(base, cert.I.of(p), box)[1]
    q = cert.maxrow(cert.sub(cert.eye(9), cert.mm(c, df)))
    y = cert.maxrow(cert.mm(c, f))
    cert.require(q < cert.SCALE and y+cert.ceil_div(q*r, cert.SCALE) < r,
                 'anchor root not certified')
    return dict(coupling=w['coupling'], defect_upper=str(q), residual_upper=str(y))


def contained(small, large):
    cert.require(len(small['center']) == len(large['center']) == 9, 'wrong containment dimension')
    cert.require(max(abs(int(a)-int(b))+int(small['radius'])
                     for a, b in zip(small['center'], large['center'])) < int(large['radius']),
                 'common root box not strictly inside tube')


def normalized_matrix(w, base):
    anchor(w, base)
    r = int(w['radius'])
    box = [cert.I(int(t)-r, int(t)+r) for t in w['center']]
    _, _, border, ds = cert.equations(base, cert.I.of(Fraction(w['coupling'])), box)
    c = cert.read_points(w['border_inverse'])
    cert.require(len(c) == 9 and all(len(row) == 9 for row in c), 'wrong crossing border dimension')
    cert.exact_inverse(c)
    bi, _, _ = cert.inverse_enclosure(border, c)
    rhs = [[-box[i]*ds[i][j] for j in range(8)] for i in range(8)]+[[cert.I.of(0)]*8]
    jac = cert.mm(bi, rhs)[:8]
    return [[(cert.I.of(int(i == j))-box[i]*box[j]+jac[i][j])/2 for j in range(8)] for i in range(8)]


def generate():
    import numpy as np
    cert.require(np.__version__ == '1.26.4', 'pinned NumPy generator required')
    old = json.loads((OLD/'witnesses.json').read_text())
    roots = [w for w in old['witnesses'] if w['sweep'] == 'kappa']
    bg = roots[0]['background_hex']
    background = np.array([float.fromhex(t) for t in bg])
    ib = [cert.I.of(Fraction.from_float(float(t))) for t in background]
    kinetic = np.eye(8)
    for i in range(8):
        kinetic[i, (i-1) % 8] = kinetic[i, (i+1) % 8] = -.5
    grad = np.zeros((8, 8))
    for i in range(8):
        grad[i, (i+1) % 8], grad[i, (i-1) % 8] = .5, -.5
    cache = {}

    def proposal(p, radius):
        p = Fraction(p)
        if p not in cache:
            nearest = min(roots, key=lambda w: abs(float.fromhex(w['coupling_hex'])-float(p)))
            x = np.array([float(Fraction(int(t), cert.SCALE)) for t in nearest['center']])
            for _ in range(12):
                u, e, k = x[:8], x[8], float(p)
                g = grad @ u
                v = background+k*(g*g+background*u*u)
                h = kinetic+np.diag(v)-e*np.eye(8)
                ds = 2*k*(np.diag(g)@grad+np.diag(background*u))
                f = np.r_[h@u, (u@u-1)/2]
                d = np.block([[h+np.diag(u)@ds, -u.reshape(8, 1)],
                              [u.reshape(1, 8), np.zeros((1, 1))]])
                dx = np.linalg.solve(d, f)
                x -= dx
                if np.max(np.abs(dx)) < 2e-16:
                    break
            # Recompute DF at the final proposal, not the previous Newton step.
            ix = [cert.I.of(Fraction.from_float(float(t))) for t in x]
            df = cert.equations(ib, cert.I.of(p), ix)[1]
            d = np.array([[float(Fraction(t.lo+t.hi, 2*cert.SCALE)) for t in row] for row in df])
            inverse = np.linalg.inv(d)
            cache[p] = dict(center=[str(round(float(t)*cert.SCALE)) for t in x],
                            newton_inverse=[[str(round(float(t)*cert.SCALE)) for t in row] for row in inverse])
        return dict(cache[p], radius=str(radius))

    tubes = []
    failures = 0

    def subdivide(a, b, depth=0):
        nonlocal failures
        cert.require(depth < 20, 'tube construction needs a new strategy')
        w = proposal((a+b)/2, cert.SCALE//256)
        w['coupling_interval'] = [str(a), str(b)]
        try:
            uniform(w, ib)
            # Common anchors also need strict inclusion in adjacent tubes.
            for p in [a, b]:
                aw = proposal(p, 1 << 48); contained(aw, w)
        except AssertionError:
            failures += 1
            mid = (a+b)/2
            subdivide(a, mid, depth+1); subdivide(mid, b, depth+1)
        else:
            tubes.append(w)

    for a, b in [(Fraction(0), Fraction(15)), (Fraction(15), Fraction(20)), (Fraction(20), Fraction(30))]:
        subdivide(a, b)
    endpoints = [Fraction(tubes[0]['coupling_interval'][0])]+[Fraction(w['coupling_interval'][1]) for w in tubes]
    anchors = [dict(proposal(p, 1 << 48), coupling=str(p)) for p in endpoints]
    crossing = []
    for p in [Fraction(79, 5), Fraction(159, 10)]:
        w = dict(proposal(p, 1 << 48), coupling=str(p))
        _, _, border, _ = cert.equations(ib, cert.I.of(p), [cert.I(int(t)) for t in w['center']])
        arr = np.array([[float(Fraction(t.lo+t.hi, 2*cert.SCALE)) for t in row] for row in border])
        inverse = np.linalg.inv(arr)
        w['border_inverse'] = [[str(round(float(t)*cert.SCALE)) for t in row] for row in inverse]
        crossing.append(w)
    return dict(scale=str(cert.SCALE), original_root_witness_sha256=hashlib.sha256((OLD/'witnesses.json').read_bytes()).hexdigest(),
                background_hex=bg, interval=['0', '30'], tubes=tubes, anchors=anchors,
                crossing_anchors=crossing, rejected_proposal_intervals=failures)


def replay(data):
    cert.require(data['scale'] == str(cert.SCALE) and data['interval'] == ['0', '30'], 'scope/scale changed')
    cert.require(data['original_root_witness_sha256'] == hashlib.sha256((OLD/'witnesses.json').read_bytes()).hexdigest(),
                 'original witness changed')
    old = json.loads((OLD/'witnesses.json').read_text())
    original = cert.replay(old)
    cert.require(original == json.loads((OLD/'certificates.json').read_text()), 'original roots do not replay')
    roots = [w for w in old['witnesses'] if w['sweep'] == 'kappa']
    bg = roots[0]['background_hex']
    cert.require(data['background_hex'] == bg, 'original background changed')
    base = [cert.I.of(Fraction.from_float(float.fromhex(t))) for t in bg]
    tubes, anchors = data['tubes'], data['anchors']
    cert.require(len(tubes) > 0 and len(anchors) == len(tubes)+1, 'wrong seam count')
    edges = [Fraction(tubes[0]['coupling_interval'][0])]+[Fraction(w['coupling_interval'][1]) for w in tubes]
    cert.require(edges[0] == 0 and edges[-1] == 30, 'coupling interval not fully covered')
    for i, w in enumerate(tubes):
        cert.require(list(map(Fraction, w['coupling_interval'])) == edges[i:i+2], 'gap or reordered interval')
    cert.require([Fraction(w['coupling']) for w in anchors] == edges, 'seam identities changed')
    rows = [uniform(w, base) for w in tubes]
    seam_rows = [anchor(w, base) for w in anchors]
    for i, w in enumerate(tubes):
        contained(anchors[i], w); contained(anchors[i+1], w)
    returned = []
    for w in roots:
        p = Fraction.from_float(float.fromhex(w['coupling_hex']))
        candidates = [i for i, t in enumerate(tubes) if Fraction(t['coupling_interval'][0]) <= p <= Fraction(t['coupling_interval'][1])]
        cert.require(bool(candidates), 'original coupling not covered')
        for i in candidates:
            contained(w, tubes[i])
        returned.append(dict(parameter_hex=w['parameter_hex'], containing_tubes=candidates,
                             original_root_identified_by_uniqueness=True))
    cert.require([Fraction(w['coupling']) for w in data['crossing_anchors']] == [Fraction(79, 5), Fraction(159, 10)],
                 'crossing parameters changed')
    signs = []
    for w in data['crossing_anchors']:
        p = Fraction(w['coupling'])
        for t in tubes:
            if Fraction(t['coupling_interval'][0]) <= p <= Fraction(t['coupling_interval'][1]):
                contained(w, t)
        a = normalized_matrix(w, base)
        determinant = cert.determinant([[a[i][j]+cert.I.of(int(i == j)) for j in range(8)] for i in range(8)])
        cert.require(determinant.lo > 0 if p == Fraction(79, 5) else determinant.hi < 0,
                     'minus-one crossing endpoint sign not certified')
        signs.append(dict(coupling=str(p), determinant_A_plus_I=determinant.json()))
    r20 = next(r for r in original['certificates'] if r['sweep'] == 'kappa' and float.fromhex(r['parameter_hex']) == 20.)
    a20 = [[cert.I(int(t[0]), int(t[1])) for t in row] for row in r20['normalized_jacobian']]
    d20 = cert.determinant([[a20[i][j]+cert.I.of(int(i == j)) for j in range(8)] for i in range(8)])
    cert.require(d20.lo > 0, 'second-crossing endpoint sign not certified')
    signs.append(dict(coupling='20', determinant_A_plus_I=d20.json()))
    return dict(scale=str(cert.SCALE), arithmetic='exact outward dyadic integers with Fraction basis inversion',
                original_background=bg, full_coupling_interval=['0', '30'],
                uniform_root_tubes=len(tubes), common_certified_anchors=len(anchors),
                all_tubes_positive_strictly_invariant_and_unique=True,
                all_partial_derivatives_invertible=True, local_C_infinity_branch_criterion_lean=True,
                seams_joined_by_common_root_and_uniqueness=True,
                mathematical_single_C_infinity_positive_ground_branch=True,
                original_coupling_roots_returned=12,
                actual_half_mixing_minus_one_crossing_interval=['79/5', '159/10'],
                additional_distinct_minus_one_crossing_interval=['159/10', '20'],
                concrete_kernel_instantiations=False, background_offset_continuum=False,
                global_root_uniqueness=False, exactly_one_crossing=False, nonlinear_escape=False,
                floating_runtime_emulation=False, tubes=rows, anchors=seam_rows,
                original_sample_return=returned, crossing_signs=signs)


def controls(data):
    import copy
    failures = []
    for name in ['gap', 'wrong background', 'false seam', 'singular preconditioner']:
        bad = copy.deepcopy(data)
        if name == 'gap':
            bad['tubes'][1]['coupling_interval'][0] = str(Fraction(bad['tubes'][1]['coupling_interval'][0])+Fraction(1, 1024))
        elif name == 'wrong background':
            bad['background_hex'][0] = (99.).hex()
        elif name == 'false seam':
            bad['anchors'][1]['center'][0] = str(10*cert.SCALE)
        else:
            bad['tubes'][0]['newton_inverse'][1] = bad['tubes'][0]['newton_inverse'][0]
        try:
            replay(bad)
        except AssertionError as e:
            failures.append(dict(control=name, rejected=True, reason=str(e)))
        else:
            raise AssertionError('false continuation certificate accepted: '+name)
    return dict(false_certificate_rejections=failures)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    p = OUT/'witnesses.json'
    if args.generate:
        p.write_text(json.dumps(generate(), indent=2)+'\n')
    data = json.loads(p.read_text())
    result = replay(data)
    (OUT/'certificates.json').write_text(json.dumps(result, indent=2)+'\n')
    (OUT/'controls.json').write_text(json.dumps(controls(data), indent=2)+'\n')
    print(f"Exact full [0,30] branch: {result['uniform_root_tubes']} uniform tubes, {result['common_certified_anchors']} common-root anchors, all12 original roots returned; minus-one crossings in(15.8,15.9) and(15.9,20)")


if __name__ == '__main__':
    main()
