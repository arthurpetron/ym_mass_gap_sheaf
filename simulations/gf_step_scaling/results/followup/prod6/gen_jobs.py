#!/usr/bin/env python3
# Generates prod6 production job lines (Python list -> ' '.join, no shell word-splitting involved).
RATE = {6: 0.0168, 8: 0.0609, 12: 0.507, 16: 1.973, 24: 18.09}   # s per (meas + therm/sep) unit; L12 from today's probe (worse than prod5 0.4375)
COMMON = ['--twist', '1', '--sep', '10', '--nor', '4', '--eps', '0.1', '--alt-eps', '0', '--start', 'cold', '--ckpt-every', '50', '--c', '0.3,0.4']
jobs = []; seed = 96100
def add(name, L, beta, nmeas, therm):
    global seed; seed += 1
    est = (nmeas + therm / 10) * RATE[L]; cap = max(300, int(1.25 * est))
    args = ['su2gf_capped', str(cap), '--L', str(L), '--beta', beta, '--therm', str(therm), '--nmeas', str(nmeas)] + COMMON + ['--seed', str(seed)]
    jobs.append((est, name, ' '.join(args), cap))
# B: 4th u ~ 2.0 (c=0.3), betas from ana_prepro.py (linear in 1/g2), design as prod5
B6, B8, B12 = '3.658', '3.785', '3.929'
add(f'su2_L24_b{B12}_twd', 24, B12, 600, 300); add(f'su2_L24_b{B12}_twe', 24, B12, 600, 300)
add(f'su2_L12_b{B12}_twd', 12, B12, 1200, 300)
add(f'su2_L16_b{B8}_twd', 16, B8, 1200, 300); add(f'su2_L8_b{B8}_twd', 8, B8, 2000, 300)
add(f'su2_L12_b{B6}_twd', 12, B6, 1200, 300); add(f'su2_L6_b{B6}_twd', 6, B6, 2000, 300)
# A2: weak-coupling Nhat_T check, beta 20 and 40, therm 500 (cold start), N40:N20 = 2:1 (optimal for delta = 2 R40 - R20 - 1)
for b, n24, n16, n12, n8 in (('20', 200, 800, 1000, 1500), ('40', 400, 1600, 2000, 3000)):
    for ch in 'abc': add(f'su2_L24_b{b}_wc{ch}', 24, b, n24, 500)
    add(f'su2_L16_b{b}_wca', 16, b, n16, 500); add(f'su2_L12_b{b}_wca', 12, b, n12, 500); add(f'su2_L8_b{b}_wca', 8, b, n8, 500)
jobs.sort(key=lambda j: -j[0])
with open('/Users/darthur/ym_numerics_runs/prod6/jobs6_prod.txt', 'w') as f:
    for est, name, cmd, cap in jobs: f.write(f'{name}|{cmd}\n')
tot = sum(j[0] for j in jobs) / 3600; caps = sum(j[3] for j in jobs) / 3600
# LPT simulation for wall time (3 slots, FIFO in file order)
sl = [0.0] * 3
for est, *_ in jobs: i = sl.index(min(sl)); sl[i] += est
for est, name, cmd, cap in jobs: print(f'{est/3600:6.3f} h  cap {cap/3600:5.2f} h  {name}')
print(f'jobs={len(jobs)} est total {tot:.2f} CPU-h; sum of caps {caps:.2f} CPU-h; wall (3 slots, unthrottled) {max(sl)/3600:.2f} h')
