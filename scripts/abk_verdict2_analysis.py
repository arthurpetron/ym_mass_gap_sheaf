"""Exact-arithmetic analysis of the completed abk_verdict2 (beta = 4*kappa,
correlation mode) run.

Input : abk_verdict2_ckpt.json  (mirror of
        ym_mass_gap_sheaf/computations/abk_verdict2_ckpt.json, run complete
        at i=300)
Output: abk_verdict2_analysis.json + stdout report.

Match convention (from computations/abk_verdict2.py):
    direct : beta == (4 if kappa else 0)          i.e. beta ≡ 4*kappa (mod 8)
    mirror : (8 - beta) % 8 == (4 if kappa else 0)
Baseline: random beta mod 8 -> P(match) = 1/8 per completed sample.
Binomial tail P(X >= k | n, p) computed exactly with Fractions.
"""
import json
import os
from collections import Counter
from fractions import Fraction
from math import comb

_REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CKPT = os.path.join(_REPO, 'computations', 'abk_verdict2_ckpt.json')
OUT = os.path.join(_REPO, 'computations', 'abk_verdict2_analysis.json')


def binom_tail(n, k, p):
    """Exact P(X >= k) for X ~ Bin(n, p), p a Fraction."""
    return sum(Fraction(comb(n, j)) * p**j * (1 - p)**(n - j)
               for j in range(k, n + 1))


state = json.load(open(CKPT))
rows = state['rows']
assert state['i'] == len(rows), "checkpoint index != row count"
n_total = len(rows)

# sanity: sampler drew 150 kappa=1 and 150 kappa=0 configs
ksplit = Counter(r['kappa'] for r in rows)
assert ksplit == Counter({0: 150, 1: 150}), f"kappa split {ksplit}"

done = [r for r in rows if 'beta' in r]
fails = Counter(r['fail'] for r in rows if 'fail' in r)
n_done = len(done)

target = lambda k: 4 if k else 0
direct = [r for r in done if r['beta'] == target(r['kappa'])]
mirror = [r for r in done if (8 - r['beta']) % 8 == target(r['kappa'])]

# circular distance mod 8 between beta and 4*kappa
def circ(a, b):
    d = (a - b) % 8
    return min(d, 8 - d)

miss_dist = Counter(circ(r['beta'], target(r['kappa']))
                    for r in done if r['beta'] != target(r['kappa']))
dist_all = Counter(circ(r['beta'], target(r['kappa'])) for r in done)

# beta x kappa histogram (mirrors the script's FINAL print)
hist = Counter((r['beta'], r['kappa']) for r in done)

# strata by kappa and by b1
by_kappa = {}
for kv in (0, 1):
    sub = [r for r in done if r['kappa'] == kv]
    m = sum(1 for r in sub if r['beta'] == target(kv))
    by_kappa[kv] = {'done': len(sub), 'match': m}

by_b1 = {}
for r in done:
    d = by_b1.setdefault(r['b1'], {'done': 0, 'match': 0})
    d['done'] += 1
    d['match'] += r['beta'] == target(r['kappa'])

p = Fraction(1, 8)
k = len(direct)
tail = binom_tail(n_done, k, p)
tail_mirror = binom_tail(n_done, len(mirror), p)
rate = Fraction(k, n_done)

# honesty cuts:
# (a) b1 = 0 rows have beta = 0 by construction -> match iff kappa = 0,
#     no information about the Brown invariant at all.  Exclude them.
nt = [r for r in done if r['b1'] > 0]
nt_match = sum(1 for r in nt if r['beta'] == target(r['kappa']))
tail_nt = binom_tail(len(nt), nt_match, p)
# (b) per-kappa tails on the nontrivial set
per_k = {}
for kv in (0, 1):
    sub = [r for r in nt if r['kappa'] == kv]
    m = sum(1 for r in sub if r['beta'] == target(kv))
    per_k[kv] = {'done': len(sub), 'match': m,
                 'tail': binom_tail(len(sub), m, p)}

# beta parity: q_ii even for even sublattice remark; check evenness of beta
even_beta = sum(1 for r in done if r['beta'] % 2 == 0)

report = {
    'n_total': n_total,
    'run_complete': state['i'] == 300,
    'n_completed_beta': n_done,
    'failures': dict(fails),
    'match_direct': k,
    'match_mirror': len(mirror),
    'match_rate': {'fraction': f'{rate.numerator}/{rate.denominator}',
                   'decimal': float(rate)},
    'baseline_p': '1/8',
    'binom_tail_direct': {
        'fraction': f'{tail.numerator}/{tail.denominator}',
        'decimal': float(tail)},
    'binom_tail_mirror': {
        'fraction': f'{tail_mirror.numerator}/{tail_mirror.denominator}',
        'decimal': float(tail_mirror)},
    'miss_circular_distance_hist': {str(a): b for a, b in
                                    sorted(miss_dist.items())},
    'all_circular_distance_hist': {str(a): b for a, b in
                                   sorted(dist_all.items())},
    'beta_kappa_hist': {f'beta={b},kappa={kv}': c for (b, kv), c in
                        sorted(hist.items())},
    'even_beta_count': even_beta,
    'by_kappa': by_kappa,
    'by_b1': {str(b): v for b, v in sorted(by_b1.items())},
    'nontrivial_b1_gt_0': {
        'done': len(nt), 'match': nt_match,
        'rate': f'{Fraction(nt_match, len(nt))}',
        'tail_fraction': f'{tail_nt.numerator}/{tail_nt.denominator}',
        'tail_decimal': float(tail_nt)},
    'nontrivial_by_kappa': {
        str(kv): {'done': v['done'], 'match': v['match'],
                  'tail_decimal': float(v['tail'])}
        for kv, v in per_k.items()},
}
json.dump(report, open(OUT, 'w'), indent=1)

print(f"rows={n_total} (complete: {state['i']}/300)  "
      f"beta computed on {n_done}")
print(f"failures: {dict(fails)}")
print(f"direct beta=4k: {k}/{n_done} = {rate} = {float(rate):.4f}")
print(f"mirror        : {len(mirror)}/{n_done}")
print(f"P(X>={k} | n={n_done}, p=1/8) = {float(tail):.6g}")
print(f"  exact = {tail.numerator}/{tail.denominator}")
print(f"P_mirror(X>={len(mirror)}) = {float(tail_mirror):.6g}")
print(f"miss circular distances (mod 8): {dict(sorted(miss_dist.items()))}")
print(f"beta x kappa hist: {dict(sorted(hist.items()))}")
print(f"even beta: {even_beta}/{n_done}")
print(f"by kappa: {by_kappa}")
print(f"by b1: {dict(sorted(by_b1.items()))}")
print(f"nontrivial (b1>0): {nt_match}/{len(nt)} = "
      f"{Fraction(nt_match, len(nt))}  "
      f"P(X>={nt_match}|n={len(nt)},1/8) = {float(tail_nt):.6g}")
print(f"  exact = {tail_nt.numerator}/{tail_nt.denominator}")
for kv, v in per_k.items():
    print(f"nontrivial kappa={kv}: {v['match']}/{v['done']}  "
          f"tail = {float(v['tail']):.6g}")
