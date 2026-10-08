# Scope: certified theta-ceiling at named nomes (R1 commit 37, 2026-10-07 PT)

## PROVED
- For w ∈ {1/2, 4/5} and every rational x with −1 ≤ x ≤ 1: `CReal.leRat (productRadialCostCReal …) (2w/(1−w²))`, i.e. 4/3 and 40/9.
- Onsets: N = 2 at w = 1/2 (c_2 = 1/32 ≤ 1/8), and N = 5 at w = 4/5 (c_5 = (4/5)^11 ≈ 0.0859; N = 4 gives c_4 ≈ 0.134 > 1/8).
- Tail: 4c_N/(1−w²), from the existing signed-tail theorems. The starting N is explicit data.
- Grid: 14 dyadic cells at w = 1/2, and 66 at w = 4/5 (finest 1/256, refined near x = −1). Each cell uses a monotone interval enclosure, so no Lipschitz constant is needed.

## NOT CLAIMED / OPEN
- Rational x only, which is where `productRadialCostCReal` is defined. Extending to real x needs a continuity or density argument.
- Only the two named nomes, w = 1/2 and w = 4/5. Nothing uniform in w.
- The theorem is stated at the cap 2w/(1−w²) by a per-nome certificate. It is not the general-w addition-square route, and does not use the 3/[2(1−w)] claim, which fails below the c_N ≤ 1/8 onset.
- Any angular, Haar, OS or physical-scaling consequence.
