"""Exact non-vanishing check for general shapes (no (2t+n) factor):
   W(t) = prod_{j in Zs} (t+1/2+j)^A / prod_{k in Ks} (t+k)^q ,  L(P) = int (PW)^{(d)}(t+1/2) dt,
aux prime p; conditions: all q jets at every node k with |k| >= (p+1)/2 ("HS nodes").
Prediction: v_p(det B) = sum over HS nodes of q*(v_p(h_k) - (d+2))  (anti-triangular blocks),
and adding multiples of the zeta-parts does not change it."""
import sys, random
from fractions import Fraction as Fr
from math import comb
import flint
from exact import series_linear, mul, HS, rising, hankel, vp


def local_H(Ks, Zs, A, q, k):
    s = [Fr(1)] + [Fr(0)] * (q - 1)
    for j in Zs:
        s = mul(s, series_linear(Fr(1, 2) + j - k, A, q), q)
    for m in Ks:
        if m != k:
            s = mul(s, series_linear(Fr(m - k), -q, q), q)
    return s


def run(Ks, Zs, A, q, d, p, trials=2):
    surv = [i for i in range(2, q + 1) if (i + d + 1) % 2 == 1]
    hs = [k for k in Ks if abs(k) >= (p + 1) // 2]
    K = q * len(hs)
    J = 2 * K - 1
    # purity: deg(x^{2K-2} W) <= -2
    assert 2 * K - 2 + A * len(Zs) - q * len(Ks) <= -2, 'purity fails'
    muB = [Fr(0)] * J
    muZ = {i: [Fr(0)] * J for i in surv}
    sg = (-1) ** d
    pred = 0
    xs = {}
    for k in Ks:
        H = local_H(Ks, Zs, A, q, k)
        if k in hs:
            pred += q * (vp(H[0], p) - (d + 2))
        xk = -Fr(k)
        cB = [Fr(0)] * q
        cZ = {i: [Fr(0)] * q for i in surv}
        for a in range(q):
            for i in range(1, q - a + 1):
                r = H[q - i - a]
                cB[a] += -sg * rising(i, d + 1) * HS(k, i + d + 1) * r
                if i in surv:
                    cZ[i][a] += sg * rising(i, d + 1) * 2 ** (i + d + 1) * r
        pw = [xk ** j for j in range(J)]
        for j in range(J):
            for a in range(min(q, j + 1)):
                t = comb(j, a) * pw[j - a]
                muB[j] += cB[a] * t
                for i in surv:
                    muZ[i][j] += cZ[i][a] * t
    B = hankel(muB, K)
    Zm = [hankel(muZ[i], K) for i in surv]
    out = [vp(B.det(), p)]
    for _ in range(trials):
        M = B
        for Z in Zm:
            M = M + random.randint(-50, 50) * Z
        out.append(vp(M.det(), p))
    return K, [i + d + 1 for i in surv], pred, out


if __name__ == '__main__':
    # symmetric shape: nodes [-3n/2, 3n/2], zeros j in [-n/2, n/2), p = 2n+1
    q, d, A = map(int, sys.argv[1:4])
    bad = 0
    for n in map(int, sys.argv[4:]):
        p = 2 * n + 1
        Ks = list(range(-(3 * n) // 2, (3 * n) // 2 + 1))
        Zs = list(range(-(n // 2), n - n // 2))
        K, vals, pred, out = run(Ks, Zs, A, q, d, p)
        print('sym q,d,A', (q, d, A), 'n', n, 'p', p, 'K', K, 'values', vals, 'pred', pred, 'got', out, 'OK' if out == [pred] * len(out) else 'MISMATCH')
        bad += out != [pred] * len(out)
    sys.exit(1 if bad else 0)
