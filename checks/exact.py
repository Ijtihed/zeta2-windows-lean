"""Exact helpers (series, Hankel matrices, harmonic sums, valuations) used by exact2.py."""
from fractions import Fraction as Fr
from math import comb
import flint


def series_linear(alpha, e, N):
    """(alpha + u)^e truncated to N terms (e may be negative)."""
    out = []
    coef = Fr(1)
    for j in range(N):
        # binom(e, j) alpha^(e-j)
        out.append(coef * Fr(alpha) ** (e - j))
        coef = coef * (e - j) / (j + 1)
    return out


def mul(a, b, N):
    return [sum(a[i] * b[j - i] for i in range(j + 1)) for j in range(N)]


def local_H(n, A, q, k, lin=True):
    N = q
    s = [Fr(1)] + [Fr(0)] * (N - 1)
    if lin:                                   # factor 2t+n at t=-k+u:  (n-2k) + 2u
        s = ([Fr(n - 2 * k), Fr(2)] + [Fr(0)] * N)[:N]
    for j in range(n):
        s = mul(s, series_linear(Fr(1, 2) + j - k, A, N), N)
    for m in range(-n, 2 * n + 1):
        if m != k:
            s = mul(s, series_linear(Fr(m - k), -q, N), N)
    return s


def HS(k, M):
    if k >= 0:
        return sum(Fr(2 ** M, (2 * l - 1) ** M) for l in range(1, k + 1))
    return -sum(Fr(2 ** M, (2 * l - 1) ** M) for l in range(k + 1, 1))


def rising(i, d):
    r = 1
    for t in range(d):
        r *= i + t
    return r


def moments(n, A, q, d, J, lin=True):
    surv = [i for i in range(2, q + 1) if (i + d + 1) % 2 == 1]
    muB = [Fr(0)] * J
    muZ = {i: [Fr(0)] * J for i in surv}
    sg = (-1) ** d
    for k in range(-n, 2 * n + 1):
        H = local_H(n, A, q, k, lin)
        xk = Fr(n, 2) - k
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
    return muB, muZ, surv


def hankel(mu, K):
    return flint.fmpq_mat(K, K, [flint.fmpq(mu[i + j].numerator, mu[i + j].denominator) for i in range(K) for j in range(K)])


def vp(x, p):
    x = Fr(int(x.p), int(x.q)) if not isinstance(x, Fr) else x
    if x == 0:
        return None
    v = 0
    a, b = x.numerator, x.denominator
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v


if __name__ == '__main__':
    import sys, random
    q, d, A = map(int, sys.argv[1:4])
    for n in [int(x) for x in sys.argv[4:]]:
        p = 2 * n + 1
        K = q * n
        muB, muZ, surv = moments(n, A, q, d, 2 * K - 1)
        B = hankel(muB, K)
        Zs = [hankel(muZ[i], K) for i in surv]
        pred = -((n - 1) * q * (q + d + 2 - A) + q * (q + d + 1 - A))
        out = [vp(B.det(), p)]
        for trial in range(2):
            M = B
            for Z in Zs:
                M = M + random.randint(-50, 50) * Z
            out.append(vp(M.det(), p))
        print('q,d,A', (q, d, A), 'n', n, 'p', p, 'K', K, 'values', [i + d + 1 for i in surv], 'v_p(const)', out[0], 'pred', pred, 'random', out[1:], 'OK' if out == [pred] * 3 else 'MISMATCH')
