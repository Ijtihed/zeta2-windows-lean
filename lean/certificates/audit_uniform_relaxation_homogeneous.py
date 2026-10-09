"""Audit of the homogeneous relaxation (Paper II, Lemma 5.3), against exact leaf values: 60 random class types for each
q = 4, 6, 8, 10, 12 and the seven multipliers tau = 0, 1/2, 1, 3/2, 2, 3, 5, that is 2100 inequalities (a corroboration).
Checks V_t(S) - lambda*S <= q^2 psi~(lambda/q) for these class types t, all S and lambda = q*tau, where V_t is
computed exactly (brute-force vbar -> f+ -> dynamic programme over nodes, with the definitions of [P, sec 8],
A = q). This corroborates the lemma, which is proved in the paper. Self-contained."""
import itertools, random, sys
from functools import lru_cache
from fractions import Fraction as F
rng = random.Random(7); worst = None; bad = 0; cnt = 0
for q, delta in ((4, F(1, 2)), (6, F(1, 3)), (8, F(1, 4)), (10, F(2, 5)), (12, F(1, 4))):
    print(f'start q={q}', flush=True)
    d2 = (1 + delta) * q                        # d + 2 (need not be an odd-d integer for the inequality)
    A = q
    def vbar(D, mu, hs, a):
        c = [-D - (q - i - a) * mu - (i - 2 + d2 + 1) * hs for i in range(1, q - a + 1)]   # (i+d+1) = i-2+d2+1
        return min(c)
    @lru_cache(maxsize=None)
    def fplus(D, o, mu, hs, s):
        if s == 0: return F(0)
        # vbar affine in a whenever (mu,hs) != (0,0); brute force over R with reversed pi (value pi-independent then)
        best = None
        for R in itertools.combinations(range(q), s):
            pi = tuple(reversed(range(s)))
            if any(R[t] + pi[t] > q - 1 for t in range(s)): continue
            ell = sum(R) - s * (s - 1) // 2
            v = sum(-vbar(D, mu, hs, R[t] + pi[t]) for t in range(s)) + ell * (1 if o > 0 else 0)
            best = v if best is None else max(best, v)
        return max(best, F(0))
    for trial in range(60):
        N = rng.randint(1, 5); z = rng.randint(0, 2); o = N - 1
        mu = 1 if (o + z) > 0 else 0
        hs_flags = [rng.randint(0, 1) for _ in range(N)]
        D = q * o - A * z
        # exact V(S) by DP
        W = {0: F(0)}
        for hs in hs_flags:
            nw = {}
            for S0, w0 in W.items():
                for s in range(q + 1):
                    val = w0 + fplus(D, o, mu, hs, s) + s * s
                    if S0 + s not in nw or val > nw[S0 + s]: nw[S0 + s] = val
            W = nw
        V = {S: W[S] - S * S for S in W}
        # relaxation data
        alphas = []
        for hs in hs_flags:
            if mu == 0 and hs == 0: continue
            a = N - z + (1 + delta) * hs
            if hs == 0 and N - z <= 0: continue
            alphas.append(a)
        alphas.sort(reverse=True); h = sum(1 for x in hs_flags if x and not (mu == 0 and x == 0))
        def psi(lt):
            best = F(0); acc = F(0)
            for m, a in enumerate(alphas):
                slope = a - lt; s_star = min(max(slope / 2, F(m)), F(m + 1))
                best = max(best, acc + (s_star - m) * slope - s_star * s_star)
                acc += slope; best = max(best, acc - F(m + 1) ** 2) if False else best
                acc = acc  # acc = sum_{j<=m} (a_j - lt)
            # exact: max over sigma in [0, len] of sum_{j} a_j*min(1,max(0,sigma-j)) - lt*sigma - sigma^2, piecewise
            res = F(0); pre = F(0)
            for m, a in enumerate(alphas):
                slope = a - lt
                for sig in (F(m), F(m + 1), min(max((slope - 2 * m + 2 * m) / 2, F(m)), F(m + 1))):
                    val = pre + (sig - m) * slope - sig * sig
                    res = max(res, val)
                s_c = min(max(slope / 2, F(m)), F(m + 1))
                res = max(res, pre + (s_c - m) * slope - s_c * s_c)
                pre += slope
            return res
        if trial == 59: print(f'q={q} done, checks so far {cnt}, violations {bad}', flush=True)
        for lt in (F(0), F(1, 2), F(1), F(3, 2), F(2), F(3), F(5)):
            lam = q * lt; rhs = q * q * psi(lt)          # homogeneous: no q*h_t term (paper II, Lemma 5.3)
            lhs = max(V[S] - lam * S for S in V)
            cnt += 1
            if lhs > rhs:
                bad += 1
                if bad <= 5: print('VIOLATION', q, delta, N, z, hs_flags, lt, float(lhs), float(rhs))
            gap = rhs - lhs
            worst = gap if worst is None or gap < worst else worst
print(f'relaxation checks: {cnt}, violations: {bad}, min slack {float(worst):.4f}')
sys.exit(1 if bad else 0)
