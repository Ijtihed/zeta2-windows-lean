"""Check that the weak-duality bound D(mu) = sum_k (c_k - mu)^+ + mu^2/4 (c_k = alpha_k - tau), at a
well-chosen mu, reproduces psi() of check_uniform.py exactly, and that every height inequality of the
certificate holds with D in place of psi.  Exact rational arithmetic."""
import json, sys
from fractions import Fraction as F
sys.set_int_max_str_digits(0)


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


def runs_of(alphas):
    runs = []
    for a, hs in alphas:
        if runs and runs[-1][0] == a and runs[-1][1] == hs:
            runs[-1][2] += 1
        else:
            runs.append([a, hs, 1])
    return runs


def D(runs, lt, mu):
    return sum(cnt * max(F(0), a - lt - mu) for a, hs, cnt in runs) + mu * mu / 4


def best_mu(runs, lt):
    cands = [F(2 * j) for j in range(0, 62)] + [a - lt for a, _, _ in runs]
    cands = [c for c in cands if c >= 0] + [F(0)]
    return min(cands, key=lambda m: D(runs, lt, m))


def main():
    d = json.load(open('certificates/cert_uniform_M96_delta0.4286.json'))
    delta = F(3, 7)
    bad = 0; badh = 0; negm = 0; nsub = 0
    for c in d['cells']:
        types = []
        for t in c['types']:
            al = [(F(x), int(h)) for x, h in t['alphas']]
            types.append((al, runs_of(al), F(t['m0']), F(t['m1'])))
        for sc in c['subcells']:
            nsub += 1
            sa, sb, lt, h = F(sc['a']), F(sc['b']), F(sc['lt']), F(sc['h'])
            vals = []
            for al, runs, m0, m1 in types:
                p = psi(al, lt)
                mu = best_mu(runs, lt)
                dv = D(runs, lt, mu)
                if dv != p:
                    bad += 1
                vals.append((dv, m0, m1))
                for u in (sa, sb):
                    if m0 + m1 * u < 0:
                        negm += 1
            for u in (sa, sb):
                g = lt + sum((m0 + m1 * u) * dv for dv, m0, m1 in vals)
                if h < g:
                    badh += 1
    print('subcells', nsub, 'D != psi', bad, 'height failures', badh, 'negative measures', negm)
    return bad + badh + negm


sys.exit(1 if main() else 0)
