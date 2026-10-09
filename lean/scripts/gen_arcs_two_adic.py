"""Generate the arc data that justifies the class types of the certificate (II, Cor. 5.4).

For every cell [a, b] of certificates/cert_uniform_M96_delta0.4286.json, the circle R/uZ
(positions x = r/n of the residues r mod l, u = l/n) is cut at the critical points
  -3/2, 3/2 (node range), u/2 (hs threshold |y| = u/2), -1/2 + u/2, 1/2 + u/2 (zero range, shifted),
  and 0,
reduced mod u.  On the cell they are affine functions of u, and their order does not change.
For every arc between consecutive breakpoints we record its right end (affine in u) and the index
of the certificate type of its classes (None if the class has no kept node).

The Lean checker `TwoAdicWin.Arc.cellArcsOK` recomputes, for every arc and every shift j in
[-J, J], whether the shifted arc lies inside / outside the node range, the hs region and the zero
range (by affine inequalities at u = a and u = b), hence the class data (N, #hs, z) and the kept
runs, and compares them with the certificate type; it also checks the measures.  This script
mirrors that checker exactly, so that the generated data passes it.

Output: RequestProject/TwoAdic/ArcData/A<k>.lean (one module per cell) and
RequestProject/TwoAdic/ArcAll.lean.
"""
import json, sys, os, math
from fractions import Fraction as F

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CERT = os.path.join(ROOT, 'certificates', 'cert_uniform_M96_delta0.4286.json')
OUTD = os.path.join(ROOT, 'RequestProject', 'TwoAdic', 'ArcData')


def runs_of(alphas):
    runs = []
    for a, hs in alphas:
        if runs and runs[-1][0] == a and runs[-1][1] == hs:
            runs[-1][2] += 1
        else:
            runs.append([a, hs, 1])
    return runs


def val(f, u):
    return f[0] + f[1] * u


def geAB(a, b, f, c):
    return c <= val(f, a) and c <= val(f, b)


def leAB(a, b, f, c):
    return val(f, a) <= c and val(f, b) <= c


def node_status(a, b, lo, hi, j):
    L = (lo[0], lo[1] + j)
    H = (hi[0], hi[1] + j)
    if geAB(a, b, L, F(-3, 2)) and leAB(a, b, H, F(3, 2)):
        if geAB(a, b, (L[0], L[1] - F(1, 2)), 0) or leAB(a, b, (H[0], H[1] + F(1, 2)), 0):
            return (True, True)
        if geAB(a, b, (L[0], L[1] + F(1, 2)), 0) and leAB(a, b, (H[0], H[1] - F(1, 2)), 0):
            return (True, False)
        return None
    if leAB(a, b, H, F(-3, 2)) or geAB(a, b, L, F(3, 2)):
        return (False, False)
    return None


def zero_status(a, b, lo, hi, j):
    ZL = (2 * lo[0], 2 * lo[1] + 2 * j - 1)
    ZH = (2 * hi[0], 2 * hi[1] + 2 * j - 1)
    if geAB(a, b, ZL, -1) and leAB(a, b, ZH, 1):
        return True
    if leAB(a, b, ZH, -1) or geAB(a, b, ZL, 1):
        return False
    return None


def arc_info(a, b, lo, hi, J):
    N = nh = z = 0
    for j in range(-J, J + 1):
        s = node_status(a, b, lo, hi, j)
        if s is None:
            return None
        if s[0]:
            N += 1
            if s[1]:
                nh += 1
        t = zero_status(a, b, lo, hi, j)
        if t is None:
            return None
        if t:
            z += 1
    return (N, nh, z)


def runs_from_info(info):
    N, nh, z = info
    v = N - z
    mu = (N >= 2) or (z >= 1)
    mk = (N - nh) if (mu and v >= 1) else 0
    if nh == 0 and mk == 0:
        return []
    return [(v, True, nh), (v, False, mk)]


def q(x):
    x = F(x)
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def main():
    d = json.load(open(CERT))
    delta = F(3, 7)
    cells = d['cells']
    os.makedirs(OUTD, exist_ok=True)
    names = []
    for k, c in enumerate(cells):
        a, b = F(c['a']), F(c['b'])
        types = []
        for t in c['types']:
            al = [(F(x), int(h)) for x, h in t['alphas']]
            rr = []
            for al_, hs, cnt in runs_of(al):
                base = al_ - (1 + delta) * hs
                assert base.denominator == 1
                rr.append((int(base), bool(hs), cnt))
            types.append((F(t['m0']), F(t['m1']), rr))
        um = (a + b) / 2
        crits = [(F(-3, 2), F(0)), (F(3, 2), F(0)), (F(0), F(1, 2)), (F(-1, 2), F(1, 2)),
                 (F(1, 2), F(1, 2)), (F(0), F(0))]
        red = []
        for al_, be in crits:
            w = math.floor(val((al_, be), um) / um)
            red.append((al_, be - w))
        red = sorted(set(red), key=lambda f: (val(f, um), f))
        assert red[0] == (F(0), F(0)), (k, red)
        bps = red + [(F(0), F(1))]
        # monotone at both ends
        for e1, e2 in zip(bps, bps[1:]):
            assert val(e1, a) <= val(e2, a) and val(e1, b) <= val(e2, b), (k, e1, e2)
        J = math.floor(F(3, 2) / a) + 1
        assert J * a > F(3, 2)
        arcs = []
        meas = [[F(0), F(0)] for _ in types]
        for lo, hi in zip(bps, bps[1:]):
            info = arc_info(a, b, lo, hi, J)
            assert info is not None, (k, lo, hi)
            rs = runs_from_info(info)
            if rs == []:
                idx = None
            else:
                cand = [i for i, t in enumerate(types) if t[2] == rs]
                assert len(cand) == 1, (k, lo, hi, rs, [t[2] for t in types])
                idx = cand[0]
                meas[idx][0] += hi[0] - lo[0]
                meas[idx][1] += hi[1] - lo[1]
            arcs.append((hi, idx))
        for i, t in enumerate(types):
            for u in (a, b):
                assert meas[i][0] + meas[i][1] * u <= t[0] + t[1] * u, (k, i, meas[i], t)
                assert 0 <= t[0] + t[1] * u
        # distinct runs
        pass
        name = f"arcs{k}"
        names.append(name)
        lines = []
        lines.append("import RequestProject.TwoAdic.AsmArcs")
        lines.append("import RequestProject.TwoAdic.CertData.C%d" % k)
        lines.append("")
        lines.append("/-! Generated by `scripts/gen_arcs_two_adic.py`: the arcs of cell %d, `[%s, %s]`, and their" % (k, q(a), q(b)))
        lines.append("check against the class types of the certificate (`decide +kernel`). -/")
        lines.append("")
        lines.append("namespace TwoAdicWin.Arc.ArcData")
        lines.append("")
        lines.append("/-- The arcs of cell %d: right ends `(c0, c1)` (`c0 + c1 u`) and type indices. -/" % k)
        items = []
        for hi, idx in arcs:
            si = "none" if idx is None else f"some {idx}"
            items.append(f"(({q(hi[0])}, {q(hi[1])}), {si})")
        lines.append("def %s : ArcsD where" % name)
        lines.append("  J := %d" % J)
        lines.append("  arcs := [" + ", ".join(items) + "]")
        lines.append("")
        lines.append("set_option maxRecDepth 100000 in")
        lines.append("theorem %s_ok : cellArcsOK Cert.CertData.c%d %s = true := by decide +kernel" % (name, k, name))
        lines.append("")
        lines.append("end TwoAdicWin.Arc.ArcData")
        open(os.path.join(OUTD, "A%d.lean" % k), "w").write("\n".join(lines) + "\n")
    print("cells", len(cells))


if __name__ == '__main__':
    main()
