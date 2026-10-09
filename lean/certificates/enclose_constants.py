"""Rigorous enclosure of the constants in the budget of Paper II, in exact rational arithmetic.

log 2, log 3, log 5: artanh series with explicit tail bounds. Euler's gamma: Euler-Maclaurin with N = 1024 and
remainder 0 <= gamma - A_N <= 1/(132 N^10). It first runs the structural validation of check_uniform.py; run check_uniform.py itself for
the cell types and height inequalities. This script recomputes the step sum from the subcells and proves
  C~(3/7) <= 4.388838,  F-dagger/q^2 < 0.5978770,  5 - F-dagger/q^2 - C~(3/7) >= 0.013285.
usage: python enclose_constants.py cert_uniform_M96_delta0.4286.json
"""
from fractions import Fraction as Q
import json, sys
sys.set_int_max_str_digits(0)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a, b):
    return add(a, neg(b))


def scale(c, a):
    v = (c * a[0], c * a[1])
    return min(v), max(v)


def div(a, b):
    assert b[0] > 0
    v = [x / y for x in a for y in b]
    return min(v), max(v)


def point(x):
    return Q(x), Q(x)


def log_interval(x, terms=200):
    t = Q(x - 1, x + 1)
    s = 2 * sum(t ** (2 * j + 1) / Q(2 * j + 1) for j in range(terms))
    return s, s + 2 * t ** (2 * terms + 1) / ((2 * terms + 1) * (1 - t * t))


def gamma_interval(N=1024):
    l2 = log_interval(2)
    H = sum(Q(1, k) for k in range(1, N + 1))
    corr = -Q(1, 2 * N) + Q(1, 12 * N ** 2) - Q(1, 120 * N ** 4) + Q(1, 252 * N ** 6) - Q(1, 240 * N ** 8)
    A = sub(point(H + corr), scale(10, l2))          # log 1024 = 10 log 2
    return A[0], A[1] + Q(1, 132 * N ** 10)


def show(name, a, digits=12):
    print(f'{name:28s} [{float(a[0]):.{digits}f}, {float(a[1]):.{digits}f}]')


def main(fn):
    C = json.load(open(fn))
    from check_uniform import structure_issues
    problems = structure_issues(C)
    if problems:
        print('INVALID STRUCTURE:', problems[:5])
        sys.exit(1)
    delta, eps = Q(C['delta']), Q(C['eps'])
    assert delta == Q(3, 7) and eps == Q(1, 20)
    subs = [s for c in C['cells'] for s in c['subcells']]
    assert all(Q(s['lt']) >= 0 for s in subs)
    step = sum((Q(s['b']) - Q(s['a'])) * Q(s['h']) for s in subs)
    assert step == Q(C['step']), 'step sum differs from the file'
    l2, l3, l5 = (log_interval(x) for x in (2, 3, 5))
    g = gamma_interval()
    l20 = add(scale(2, l2), l5)
    # C~(delta) = [ -gamma - ln2 - ln20 + step + (1+delta) eps + eps^2/2 ] / ln2   (kappa~ = 1)
    num = add(neg(add(add(g, l2), l20)), point(step + (1 + delta) * eps + eps * eps / 2))
    Ct = div(num, l2)
    # F-dagger / q^2 = (6 + 8 ln2 - 9 ln3) / (4 ln2)
    Fd = div(sub(add(point(6), scale(8, l2)), scale(9, l3)), scale(4, l2))
    margin = sub(sub(point(5), Fd), Ct)
    show('gamma', g)
    show('C~(3/7)', Ct)
    show('F-dagger / q^2', Fd)
    show('margin / q^2', margin)
    ok = Ct[1] <= Q('4.388838') and Fd[1] < Q('0.5978770') and margin[0] >= Q('0.013285')
    print('PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main(sys.argv[1])
