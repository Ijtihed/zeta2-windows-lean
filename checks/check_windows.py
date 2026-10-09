"""Exact check of the window corollaries (Paper II, Corollary 1.2).
Uses only integer/rational arithmetic. usage: python check_windows.py [SMAX]"""
import sys
from fractions import Fraction as F
SMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200001

def ceil_div(a, b): return -((-a) // b)

# Paper II: d = s-4, q = 2*ceil(7(s-2)/20); need q>=4 even, d odd, q<=d+1, 7(d+2)<=10q, 10(d+q) < 17 s
bad = 0
for s in range(7, SMAX, 2):
    d = s - 4; q = 2 * ceil_div(7 * (s - 2), 20)
    ok = q >= 4 and d % 2 == 1 and q <= d + 1 and 7 * (d + 2) <= 10 * q and 10 * (d + q) < 17 * s and d + 4 == s
    if not ok: bad += 1; print('II fail', s, d, q)
print('Paper II corollary: s in [7,%d) odd, failures %d' % (SMAX, bad))
for s in (7, 9, 11, 13):
    d = s - 4; q = 2 * ceil_div(7 * (s - 2), 20); print('  s=%d (q,d)=(%d,%d) set %s' % (s, q, d, list(range(d + 4, d + q + 1, 2))))
sys.exit(1 if bad else 0)
