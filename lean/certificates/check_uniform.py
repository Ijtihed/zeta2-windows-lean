"""Independent checker for cert_uniform_*.json. It shares no code with the generator.

Recomputes from scratch, in exact rational arithmetic:
  * the breakpoint set of the circle model for nodes [-a,a], zeros [-1/2,1/2), hs iff |y| >= u/2;
  * at three interior points of every cell, the class types (multiset of per-node (alpha, hs)) and their
    measures, and checks they agree with the (affine) data in the file;
  * every height h_i >= max over the two subcell endpoints of  lt*kappa~ + sum_t meas_t(u) psi_t(lt);
  * the final constant Ct;
  * the structure: the paper's parameters, an ordered tiling of [eps, 7/2] by cells and of every cell by subcells
    of positive width, nonnegative multipliers, heights and measures, sorted alpha lists (see structure_issues).
Usage: python check_uniform.py cert.json"""
import sys, json, math
from fractions import Fraction as F
sys.set_int_max_str_digits(0)


def classes(u, a, delta):
    """exact dict: tuple(sorted alphas desc with hs flag) -> measure, for positions x in [0,u)."""
    # critical points mod u: node-range ends, hs threshold (u/2), zero-range ends shifted by u/2, and 0
    pts = sorted(set(p % u for p in (-a, a, u / 2, F(-1, 2) + u / 2, F(1, 2) + u / 2, F(0))))
    pts.append(pts[0] + u)
    res = {}
    for lo, hi in zip(pts, pts[1:]):
        if hi == lo:
            continue
        x = (lo + hi) / 2
        # nodes y = x + j u in [-a, a]
        ys = []
        j = math.floor((-a - x) / u)
        while x + j * u <= a:
            if x + j * u >= -a:
                ys.append(x + j * u)
            j += 1
        if not ys:
            continue
        # zeros y' in [-1/2, 1/2) with y' + u/2 = x (mod u)
        z = 0
        j = math.floor((F(-1, 2) - (x - u / 2)) / u)
        while x - u / 2 + j * u < F(1, 2):
            if x - u / 2 + j * u >= F(-1, 2):
                z += 1
            j += 1
        N = len(ys)
        kept = []
        for y in ys:
            hs = 1 if abs(y) >= u / 2 else 0
            if N == 1 and z == 0 and hs == 0:
                continue                      # mu = 0 singleton: f+ = 0
            if hs == 0 and N - z <= 0:
                continue                      # E = q(N-z) <= 0 < q
            kept.append((N - z + (1 + delta) * hs, hs))
        key = tuple(sorted(kept, reverse=True))
        res[key] = res.get(key, F(0)) + (hi - lo)
    return res


def psi(alphas, lt):
    best = F(0); acc = F(0)
    for m, (al, _) in enumerate(alphas):
        sl = al - lt
        s = min(max(sl / 2, F(m)), F(m + 1))
        v = acc + (s - m) * sl - s * s
        if v > best:
            best = v
        acc += sl
    return best


def structure_issues(d):
    """Structural validation: the paper's parameters, an ordered tiling of [eps, 2a + 1/2] by cells, an ordered tiling
    of every cell by subcells of positive width, nonnegative multipliers, heights and measures, and alpha lists sorted
    in non-increasing order (psi() relies on this). Returns a list of messages; empty means valid."""
    msg = []
    try:
        a = F(d.get('half', '3/2')); eps = F(d['eps']); delta = F(d['delta'])
    except Exception as e:
        return [f'bad parameters: {e}']
    if a != F(3, 2): msg.append(f'half = {a}, expected 3/2')
    if eps != F(1, 20): msg.append(f'eps = {eps}, expected 1/20')
    if delta != F(3, 7): msg.append(f'delta = {delta}, expected 3/7')
    cells = d.get('cells') or []
    if not cells:
        return msg + ['no cells']
    top = 2 * a + F(1, 2)
    if F(cells[0]['a']) != eps: msg.append(f'first cell starts at {cells[0]["a"]}, expected eps')
    if F(cells[-1]['b']) != top: msg.append(f'last cell ends at {cells[-1]["b"]}, expected {top}')
    for i, c in enumerate(cells):
        lo, hi = F(c['a']), F(c['b'])
        if not lo < hi: msg.append(f'cell {i}: non-positive width')
        if i and F(cells[i - 1]['b']) != lo: msg.append(f'cell {i}: not contiguous with cell {i - 1}')
        subs = c.get('subcells') or []
        if not subs:
            msg.append(f'cell {i}: no subcells'); continue
        if F(subs[0]['a']) != lo or F(subs[-1]['b']) != hi: msg.append(f'cell {i}: subcells do not cover the cell')
        for j, sc in enumerate(subs):
            sa, sb = F(sc['a']), F(sc['b'])
            if not sa < sb: msg.append(f'cell {i} subcell {j}: non-positive width')
            if j and F(subs[j - 1]['b']) != sa: msg.append(f'cell {i} subcell {j}: not contiguous')
            if F(sc['lt']) < 0: msg.append(f'cell {i} subcell {j}: negative multiplier')
            if F(sc['h']) < 0: msg.append(f'cell {i} subcell {j}: negative height')
        for t in c['types']:
            al = [F(x) for x, _ in t['alphas']]
            if any(al[k] < al[k + 1] for k in range(len(al) - 1)): msg.append(f'cell {i}: alphas not sorted')
            for u in (lo, hi):
                if F(t['m0']) + F(t['m1']) * u < 0: msg.append(f'cell {i}: negative measure at u = {u}')
    return msg


def main(fn, d=None):
    d = json.load(open(fn)) if d is None else d
    struct = structure_issues(d)
    for m in struct[:10]:
        print('structure:', m)
    if struct:
        print(fn, 'INVALID STRUCTURE', len(struct), 'problems')
        return len(struct)
    a = F(d.get('half', '3/2')); delta = F(d['delta']) if d['delta'] != 'None' else F(0)
    eps = F(d['eps']); kt = a - F(1, 2)
    cells = d['cells']
    # breakpoints: differences of critical points in uZ or (uZ + u/2); recompute set independently
    B = {eps, 2 * a + F(1, 2)}
    lo_, hi_ = eps, 2 * a + F(1, 2)
    plain = [2 * a, F(1), F(1, 2)]        # -a vs a; zero ends vs each other; hs point u/2 vs zero ends u/2 -+ 1/2
    half = [a, a - F(1, 2), a + F(1, 2)]  # u/2 (hs) vs +-a; u/2 -+ 1/2 (zero ends) vs +-a
    for D in plain:
        for j in range(1, 400):
            if lo_ < D / j < hi_: B.add(D / j)
    for D in half:
        for j in range(1, 400):
            u = 2 * D / (2 * j - 1)
            if lo_ < u < hi_: B.add(u)
    B = sorted(B)
    ends = [F(cells[0]['a'])] + [F(c['b']) for c in cells]
    missing = sorted(set(B) - set(ends))
    issues = 0
    if missing:
        print('breakpoints missing from certificate:', [str(x) for x in missing[:5]]); issues += len(missing)
    step = F(0)
    for c in cells:
        lo, hi = F(c['a']), F(c['b'])
        data = []
        for t in c['types']:
            key = tuple((F(x), int(h)) for x, h in t['alphas'])
            data.append((key, F(t['m0']), F(t['m1'])))
        # compare measures at interior points (types with identical kept-alpha lists are merged)
        for fr in (F(1, 5), F(1, 2), F(4, 5)):
            u = lo + fr * (hi - lo)
            ex = classes(u, a, delta)
            got = {}
            for key, m0, m1 in data:
                if key:
                    got[key] = got.get(key, F(0)) + m0 + m1 * u
            ex = {k: v for k, v in ex.items() if k}
            if ex != got:
                issues += 1
        for sc in c['subcells']:
            sa, sb, lt, h = F(sc['a']), F(sc['b']), F(sc['lt']), F(sc['h'])
            if lt < 0: issues += 1
            ps = [psi(key, lt) for key, _, _ in data]
            g = max(lt * kt + sum((m0 + m1 * u) * p for (key, m0, m1), p in zip(data, ps)) for u in (sa, sb))
            if h < g: issues += 1
            step += (sb - sa) * h
    E_hi, ln20_lo, ln2_lo, ln2_hi = F(-12701758, 10**7), F(29957322, 10**7), F(6931471, 10**7), F(6931472, 10**7)
    num = kt * kt * (E_hi - ln20_lo) + step + (1 + delta) * kt * eps + eps * eps / 2
    Ct = num / ln2_lo if num >= 0 else num / ln2_hi
    print(fn, 'issues', issues, 'step equal', step == F(d['step']), 'Ct <=', float(Ct), 'file Ct', d['Ct_float'])
    return issues + (step != F(d['step']))


if __name__ == '__main__':
    sys.exit(1 if sum(main(fn) for fn in sys.argv[1:]) else 0)
