#!/usr/bin/env python3
"""Generate/replay exact dyadic certificates for original Step26 sample points.

Generation uses NumPy only to propose witnesses. Replay uses Python integers
and Fraction only. This computational certificate is not a Lean kernel proof.
It concerns the positive real representative and half mixing, not a frozen run.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/ground_interval_2026-10-03"
SOURCE = ROOT / "external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py"
DATA = SOURCE.parent.parent / "step24_derived_physical_audits_artifacts/toy_field_samples_step24.json"
PIN = "391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd"
SCALE = 1 << 80


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def ceil_div(a, b):
    require(b > 0, "positive divisor required")
    return -((-a) // b)


class I:
    """[lo/2^80,hi/2^80], with exact outward rounding at every operation."""
    def __init__(self, lo, hi=None):
        self.lo, self.hi = int(lo), int(lo if hi is None else hi)
        require(self.lo <= self.hi, "invalid interval")

    @staticmethod
    def of(x):
        if isinstance(x, I):
            return x
        x = Fraction(x)
        return I(x.numerator*SCALE // x.denominator,
                 ceil_div(x.numerator*SCALE, x.denominator))

    def __add__(self, other):
        other = I.of(other)
        return I(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I.of(other)

    def __rsub__(self, other):
        return I.of(other) + -self

    def __mul__(self, other):
        other = I.of(other)
        ends = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(ends)//SCALE, ceil_div(max(ends), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = I.of(other)
        require(other.hi < 0 or other.lo > 0, "division interval contains zero")
        ends = [Fraction(a*SCALE, b) for a in (self.lo, self.hi)
                for b in (other.lo, other.hi)]
        low, high = min(ends), max(ends)
        return I(low.numerator//low.denominator,
                 ceil_div(high.numerator, high.denominator))

    def bound(self):
        return max(abs(self.lo), abs(self.hi))

    def json(self):
        return [str(self.lo), str(self.hi)]


def eye(n):
    return [[I.of(int(i == j)) for j in range(n)] for i in range(n)]


def mm(a, b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))), I.of(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def sub(a, b):
    return [[x-y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def maxrow(a):
    return max(sum(x.bound() for x in row) for row in a)


def exact_inverse(a):
    """Fraction Gauss-Jordan, used only on fixed rational witness matrices."""
    n = len(a)
    q = [[Fraction(x.lo, SCALE) for x in row] +
         [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(a)]
    require(all(x.lo == x.hi for row in a for x in row), "inverse needs points")
    for i in range(n):
        p = next((k for k in range(i, n) if q[k][i]), None)
        require(p is not None, "singular proposed basis")
        q[i], q[p] = q[p], q[i]
        d = q[i][i]
        q[i] = [x/d for x in q[i]]
        for k in range(n):
            if k != i:
                d = q[k][i]
                q[k] = [x-d*y for x, y in zip(q[k], q[i])]
    return [[I.of(x) for x in row[n:]] for row in q]


def source(b, k, u):
    g = [(u[(i+1) % 8]-u[(i-1) % 8])/2 for i in range(8)]
    v = [b[i]+k*(g[i]*g[i]+b[i]*u[i]*u[i]) for i in range(8)]
    ds = [[2*k*(g[i]*(Fraction(1, 2) if j == (i+1) % 8 else
                         Fraction(-1, 2) if j == (i-1) % 8 else 0) +
                (b[i]*u[i] if i == j else 0)) for j in range(8)] for i in range(8)]
    return v, ds


def equations(b, k, x):
    u, e = x[:8], x[8]
    v, ds = source(b, k, u)
    h = [[(1+v[i]-e if i == j else
           I.of(Fraction(-1, 2)) if j in ((i-1) % 8, (i+1) % 8) else I.of(0))
          for j in range(8)] for i in range(8)]
    f = mm(h, [[y] for y in u]) + [[(sum((y*y for y in u), I.of(0))-1)/2]]
    df = [[h[i][j]+u[i]*ds[i][j] for j in range(8)]+[-u[i]] for i in range(8)]
    df += [u+[I.of(0)]]
    border = [row+[-u[i]] for i, row in enumerate(h)] + [u+[I.of(0)]]
    return f, df, border, ds


def inverse_enclosure(a, c):
    """B^-1=(I-E)^-1 C, E=I-CB; infinity-norm Neumann bound."""
    q = maxrow(sub(eye(len(a)), mm(c, a)))
    require(q < SCALE, "border inverse not earned")
    err = ceil_div(q*maxrow(c), SCALE-q)
    return [[I(x.lo-err, x.hi+err) for x in row] for row in c], q, err


def determinant(a):
    """Interval elimination; every chosen pivot is separated from zero."""
    a = [row[:] for row in a]
    result = I.of(1)
    for j in range(len(a)):
        candidates = [i for i in range(j, len(a)) if a[i][j].lo > 0 or a[i][j].hi < 0]
        require(bool(candidates), "determinant pivot inconclusive")
        p = max(candidates, key=lambda i: min(abs(a[i][j].lo), abs(a[i][j].hi)))
        if p != j:
            a[j], a[p] = a[p], a[j]
            result = -result
        pivot = a[j][j]
        result = result*pivot
        for i in range(j+1, len(a)):
            ratio = a[i][j]/pivot
            for k in range(j+1, len(a)):
                a[i][k] = a[i][k]-ratio*a[j][k]
            a[i][j] = I.of(0)
    return result


def read_points(rows):
    return [[I(int(x)) for x in row] for row in rows]


def certify(w):
    require(len(w['background_hex']) == 8 and len(w['center']) == 9, "wrong field/root dimension")
    for name, n in [('newton_inverse', 9), ('border_inverse', 9), ('spectral_basis', 8)]:
        require(len(w[name]) == n and all(len(row) == n for row in w[name]),
                f"wrong {name} dimension")
    b = [I.of(Fraction.from_float(float.fromhex(x))) for x in w['background_hex']]
    k = I.of(Fraction.from_float(float.fromhex(w['coupling_hex'])))
    x = [I(int(t)) for t in w['center']]
    r = int(w['radius'])
    require(r > 0, "positive root radius required")
    box = [I(y.lo-r, y.hi+r) for y in x]
    require(all(y.lo > 0 for y in box[:8]), "positive representative not certified")
    c = read_points(w['newton_inverse'])
    exact_inverse(c)  # Cf=0 must imply f=0, independently of numerical inversion.
    f = equations(b, k, x)[0]
    _, df, border, ds = equations(b, k, box)
    q = maxrow(sub(eye(9), mm(c, df)))
    y = maxrow(mm(c, f))
    require(q < SCALE, "Newton correction not contracting")
    require(y+ceil_div(q*r, SCALE) < r, "root ball not invariant")
    bi, bq, berr = inverse_enclosure(border, read_points(w['border_inverse']))
    rhs = [[-box[i]*ds[i][j] for j in range(8)] for i in range(8)] + [[I.of(0)]*8]
    jac = mm(bi, rhs)[:8]
    a = [[(I.of(int(i == j))-box[i]*box[j]+jac[i][j])/2
          for j in range(8)] for i in range(8)]
    s = read_points(w['spectral_basis'])
    transform = mm(mm(exact_inverse(s), a), s)
    spectral_upper = maxrow(transform)
    report = {
        'sweep': w['sweep'], 'parameter_hex': w['parameter_hex'],
        'root_radius': str(r), 'root_center': w['center'],
        'root_correction_upper': str(y),
        'root_contraction_upper': str(q), 'border_defect_upper': str(bq),
        'border_inverse_error_upper': str(berr),
        'spectral_radius_upper': str(spectral_upper),
        'normalized_jacobian': [[t.json() for t in row] for row in a],
    }
    if w['verdict'] == 'stable':
        require(spectral_upper < SCALE, "all-mode spectral stability inconclusive")
        report['verdict'] = 'all_real_tangent_modes_spectral_stable'
    else:
        left, right = map(Fraction, w['unstable_bracket'])
        require(left < right < -1, "unstable eigenvalue bracket must be below -1")
        dets = [determinant(sub(a, [[t*z for z in row] for row in eye(8)]))
                for t in (left, right)]
        require((dets[0].hi < 0 and dets[1].lo > 0) or
                (dets[1].hi < 0 and dets[0].lo > 0), "real eigenvalue sign change not certified")
        report.update(verdict='real_tangent_eigenvalue_below_minus_one',
                      unstable_bracket=w['unstable_bracket'],
                      determinant_endpoints=[z.json() for z in dets])
    return report


def generate():
    import numpy as np
    require(np.__version__ == '1.26.4', "use pinned generator NumPy")
    historical = json.loads((ROOT/'results/ground_state_2026-10-02/receipt.json').read_text())
    base = np.asarray(json.loads(DATA.read_text())['potential'], dtype=float)
    witnesses = []
    point = lambda a: [[str(round(float(x)*SCALE)) for x in row] for row in a]
    # A center can be historical and inaccurate: exact replay must earn its return.
    for row in historical['continuation']:
        sweep, p = row['sweep'], float(row['parameter'])
        b = base+p if sweep == 'background' else base.copy()
        k = .3 if sweep == 'background' else p
        u = np.asarray(row['psi'])
        g = (np.roll(u, -1)-np.roll(u, 1))/2
        v = b+k*(g*g+b*u*u)
        h = np.eye(8)+np.diag(v)
        for i in range(8):
            h[i, (i-1) % 8] = h[i, (i+1) % 8] = -.5
        x = np.r_[u, u @ h @ u]
        # Propose a tighter center using a polynomial Newton solve.
        for _ in range(3):
            ix = [I.of(Fraction.from_float(float(t))) for t in x]
            ib = [I.of(Fraction.from_float(float(t))) for t in b]
            ik = I.of(Fraction.from_float(k))
            ff, dd, bb, ss = equations(ib, ik, ix)
            arr = lambda z: np.array([[float(Fraction(t.lo+t.hi, 2*SCALE)) for t in rr] for rr in z])
            x -= np.linalg.solve(arr(dd), arr(ff)[:, 0])
        ff, dd, bb, ss = equations(ib, ik, [I.of(Fraction.from_float(float(t))) for t in x])
        cinv, binv = np.linalg.inv(arr(dd)), np.linalg.inv(arr(bb))
        j = binv @ np.vstack((-np.diag(x[:8]) @ arr(ss), np.zeros((1, 8))))
        a = (np.eye(8)-np.outer(x[:8], x[:8])+j[:8])/2
        ev, basis = np.linalg.eig(a)
        columns = []
        for z, vector in zip(ev, basis.T):
            if z.imag > 1e-10:
                columns.extend([vector.real, vector.imag])
            elif abs(z.imag) <= 1e-10:
                columns.append(vector.real)
        require(len(columns) == 8, f"real invariant candidate basis failed at {sweep}={p}: {ev}")
        basis = np.array(columns).T
        stable = np.max(np.abs(ev)) < 1
        leading = float(ev.real.min())
        w = dict(sweep=sweep, parameter_hex=p.hex(), background_hex=[float(t).hex() for t in b],
                 coupling_hex=k.hex(), center=[r[0] for r in point(x.reshape(-1, 1))],
                 radius=str(1 << 48), newton_inverse=point(cinv), border_inverse=point(binv),
                 spectral_basis=point(basis), verdict='stable' if stable else 'unstable')
        if not stable:
            require(leading < -1.01, "unstable candidate not a separated negative mode")
            w['unstable_bracket'] = [str(Fraction(round(leading*100)-1, 100)),
                                     str(Fraction(round(leading*100)+1, 100))]
        try:
            certify(w)
        except AssertionError as error:
            raise AssertionError(f"{sweep}={p}: {error}; approximate eigenvalues={ev}") from error
        witnesses.append(w)
    return dict(scale=str(SCALE), step26_sha256=PIN,
                source_fields_sha256=hashlib.sha256(DATA.read_bytes()).hexdigest(),
                witnesses=witnesses)


def replay(data):
    require(data['scale'] == str(SCALE), "dyadic scale changed")
    require(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == data['step26_sha256'] == PIN, "Step26 source changed")
    require(hashlib.sha256(DATA.read_bytes()).hexdigest() == data['source_fields_sha256'], "original field data changed")
    base = [float(t) for t in json.loads(DATA.read_text())['potential']]
    offsets = [-8., -5., -3., -2., -1., -.5, -.2, -.1, 0., .1, .2, .5, 1., 2., 3., 5., 8., 10.]
    couplings = [0., .1, .3, .5, 1., 2., 3., 5., 10., 15., 20., 30.]
    expected = [('background', p) for p in offsets]+[('kappa', p) for p in couplings]
    require([(w['sweep'], float.fromhex(w['parameter_hex'])) for w in data['witnesses']] == expected,
            "ordered original 30 sample parameters changed")
    reports = []
    for w, (sweep, p) in zip(data['witnesses'], expected):
        b = [t+p for t in base] if sweep == 'background' else base
        require(w['background_hex'] == [t.hex() for t in b], "IEEE background return failed")
        require(w['coupling_hex'] == (.3 if sweep == 'background' else p).hex(), "coupling return failed")
        reports.append(certify(w))
    return dict(scale=str(SCALE), arithmetic='exact integers with outward dyadic rounding',
                scope='30 isolated positive real self-consistent roots; normalized half-mixing tangent spectrum',
                lean_kernel_checked=False, branch_continuation_certified=False,
                frozen_complex_run_certified=False, nonlinear_orbit_convergence_certified=False,
                certificates=reports,
                stable_samples=sum(r['verdict'].startswith('all_real') for r in reports),
                unstable_samples=sum(r['verdict'].startswith('real_tangent') for r in reports))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--outdir', type=Path, default=OUT)
    args = parser.parse_args()
    path = args.outdir/'witnesses.json'
    if args.generate:
        data = generate()
        args.outdir.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data, indent=2)+'\n')
    data = json.loads(path.read_text())
    result = replay(data)
    args.outdir.mkdir(parents=True, exist_ok=True)
    (args.outdir/'certificates.json').write_text(json.dumps(result, indent=2)+'\n')
    print(f"Exact replay: {len(result['certificates'])} isolated positive roots; "
          f"{result['stable_samples']} spectrally stable and {result['unstable_samples']} unstable at half mixing")


if __name__ == '__main__':
    main()
