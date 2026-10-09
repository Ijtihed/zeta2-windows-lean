"""Negative controls for check_uniform.py and enclose_constants.py.

Each broken copy of the certificate must be rejected; the original must pass. usage: python test_check_uniform.py
"""
import copy, json, subprocess, sys, tempfile, os
from fractions import Fraction as F
sys.set_int_max_str_digits(0)
from check_uniform import main as check

CERT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cert_uniform_M96_delta0.4286.json')
d0 = json.load(open(CERT))


def broken(kind):
    d = copy.deepcopy(d0)
    if kind == 'empty_subcells':            # the referee's example: no integration domain, step 0
        for c in d['cells']:
            c['subcells'] = []
        d['step'] = '0'
    elif kind == 'gap_between_cells':
        del d['cells'][60]
    elif kind == 'subcell_gap':
        del d['cells'][10]['subcells'][5]
    elif kind == 'wrong_eps':
        d['eps'] = '1/10'
    elif kind == 'lowered_height':
        s = d['cells'][40]['subcells'][7]; s['h'] = str(F(s['h']) - F(1, 10))
    elif kind == 'unsorted_alphas':
        for c in d['cells']:
            for t in c['types']:
                if len(t['alphas']) > 1 and t['alphas'][0][0] != t['alphas'][-1][0]:
                    t['alphas'] = t['alphas'][::-1]; return d
    return d


fails = 0
print('original:'); ok = check(CERT, d0) == 0
if not ok: print('  ORIGINAL REJECTED'); fails += 1
for kind in ['empty_subcells', 'gap_between_cells', 'subcell_gap', 'wrong_eps', 'lowered_height', 'unsorted_alphas']:
    print(f'{kind}:'); bad = check(kind, broken(kind))
    if not bad: print(f'  NOT REJECTED: {kind}'); fails += 1
# enclose_constants.py must also refuse the empty-subcell certificate
with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as f:
    json.dump(broken('empty_subcells'), f); tmp = f.name
r = subprocess.run([sys.executable, os.path.join(os.path.dirname(CERT), 'enclose_constants.py'), tmp], capture_output=True, text=True)
os.unlink(tmp)
print('enclose_constants on empty_subcells: exit', r.returncode)
if r.returncode == 0: print('  NOT REJECTED by enclose_constants.py'); fails += 1
print('PASS' if not fails else f'FAIL ({fails})')
sys.exit(1 if fails else 0)
