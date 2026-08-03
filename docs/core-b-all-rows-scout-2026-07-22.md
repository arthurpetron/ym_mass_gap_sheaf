# Core-B all-row scout — tail survives, diagonal prefix remains

**Date:** 2026-07-22  
**Status:** exact-arithmetic scouting result; not a proof of Core B

## Verdict

The proposed pure-boundary anchor is not a row-one accident.  For every fixed
row `s = 1,...,8` tested, the elementary-family expansion has even exponent
deltas, eventually fixed signs, a coordinatewise-dominating `E*E` versus
`E^2` anchor, and an exact discounted adverse payment throughout the checked
tail.

The right formal target is therefore a **single tail theorem symbolic in both
`s` and `r`**, not a theorem specialized to `s = 1`.

That tail theorem will not by itself close Core B.  The sign-stabilization
threshold grows as

```text
r0(s) = floor((s+2)^2 / 2),
```

on every row tested.  Hence the complementary region `r < r0(s)` is infinite
over all rows; it cannot be discharged by an ever-growing list of generated
finite cells.  The next proof must combine the generic tail with a symbolic
low-region or diagonal-cumulative payment.

## Correction to the row-one checkpoint

The original row-one scout tested the invalid claim that every adverse family
had total-degree gap at least `6r+4`.  Four families already contradicted that
claim in the scout output, but the ledger nevertheless quoted the resulting
over-optimistic `~10^16` slack.

The true minimum gap is `2r`.  After correcting the bound:

- exact per-family discounted payment still passes for every `r = 4,...,200`;
- the valid crude payment
  `sum(C_a L_a) * 4^(-2r) <= C_f` also passes exactly;
- its ratio to the anchor at `r = 4` is below `8.90e-4`, then decreases rapidly.

Thus the row-one route survives, but with honest slack of roughly three orders
of magnitude for the crude bound, not sixteen.

## Fixed-row exact structure

For a fixed row `s`, collect equal monomials inside the four numerator
components `A_i` and three midpoint components `M_j`.  The scout finds the
following closed forms on all tested rows:

```text
|A_0| = (s+2)(s+3)/2 - 2,   |A_1| = |A_2| = s+1,   |A_3| = 1,
|M_0| = (s+1)(s+2)/2,       |M_1| = s+1,           |M_2| = 1,

families = (s+1)(s+2)(3s+11)/2.
```

Every family is indexed by `(i,j,a_term,m_term)` with `(i,j) != (0,0)`.
Every exponent delta is even, so every elementary determinant is individually
divisible by `w^2-h^2`.

The pure-boundary family `(i,j)=(3,2)` has exponent delta `2` and the anchor

```text
C_f(s,r) = (s+2)^4 (r+1)(r+2)^2(r+3),
m_f(s,r) = 2r^2 + 8r + 2s^2 + 8s + 12,
T_f(s,r) = 2 m_f(s,r).
```

For every eventual adverse family in the tested rows, every quotient-chain
monomial is coordinatewise above `(wh)^m_f`.  The symbolic minimum
total-degree gap is

```text
g_min(s,r) = 2r - 2(s-1).
```

The fixed-row sign threshold and this gap formula were checked symbolically as
affine integer expressions, not inferred from floating-point samples.  The
discounted payment itself was checked with exact rational arithmetic over the
reported finite `r` ranges; its all-`r`, all-`s` proof remains to be written.

## Results

| `s` | families | favorable / adverse / zero | `r0(s)` | minimum gap | exact payment/anchor at `r0` |
|---:|---:|---:|---:|---:|---:|
| 1 | 42 | 22 / 19 / 1 | 4 | `2r` | `7.121e-5` |
| 2 | 102 | 50 / 51 / 1 | 8 | `2r-2` | `3.688e-8` |
| 3 | 200 | 95 / 104 / 1 | 12 | `2r-4` | `1.403e-11` |
| 4 | 345 | 159 / 185 / 1 | 18 | `2r-6` | `2.125e-17` |
| 5 | 546 | 247 / 298 / 1 | 24 | `2r-8` | `2.798e-23` |
| 6 | 812 | 361 / 450 / 1 | 32 | `2r-10` | `1.443e-31` |
| 7 | 1152 | 506 / 645 / 1 | 40 | `2r-12` | `6.895e-40` |
| 8 | 1575 | 684 / 890 / 1 | 50 | `2r-14` | `1.287e-50` |

Rows `1,...,7` were checked through `r=60` in the combined regression and row
8 through `r=60`; separate runs extended rows `1,...,7` to `r=120`, and the
corrected row-one check extends to `r=200`.  These are exact finite checks, not
an asymptotic proof.

## Low-region findings

The constant-reserve tactic succeeds for every prefix cell in rows `s=1,2,3`
after allowing per-monomial degree discounts.  At `(s,r)=(4,0)`, the quotient
has 260 terms, 79 negative coefficients, and **zero constant reserve**.  The
cell therefore requires positive nonconstant groups; this is a proof-tactic
obstruction, not a sign counterexample.  An exact 64-point simplex sweep of its
quotient found no negative value.

A direct exact-rational falsification pass over every cell
`0 <= r < r0(s)` for `s=1,...,8`, at 15 physical-simplex points per cell,
tested 2,820 values and found no negative residual.  This supports—but does not
prove—termwise residual positivity in the low region.

The growth of `r0(s)` is the strategic point: serial per-row cell generation is
not a closure strategy.  The low region needs one symbolic grouping, or the
proof should target the weaker diagonal cumulative directly.

## Cumulative interface banked in Lean

`CoreBStructuralRecurrence.cumulativeResidual_two` now proves, for arbitrary
starting row and offset,

```text
C(s,r,2) ≈ R(s,r+1) + R(s+1,r).
```

The targeted module build is green and its axiom gate is `[propext]`.  This is
the exact all-row interface for a diagonal proof; the older theorem recorded
only the specialization `s=0`.

## Reproduction

```sh
python3 computations/CoreBResidualRowOne_anchor_scout.py

python3 computations/CoreBResidualAllRows_scout.py \
  --rows 1 2 3 4 5 6 7 8 --max-r 60 --skip-prefix --sweep-prefix

python3 computations/CoreBResidualAllRows_scout.py \
  --rows 1 2 3 4 --max-r 120

cd lean
python3 scripts/safe_lean_build.py -- YMGap.Continuum.CoreBStructuralRecurrence
```

Use `--show-groups` to print every exact total-gap group and its collected
coefficient mass.

## Next attack

1. Prove the all-`s,r` monomial normal form without enumerating the
   `(s+1)(s+2)(3s+11)/2` families as separate Lean declarations.
2. Prove the parity, anchor, threshold, coordinate-domination, and minimum-gap
   formulas with bounded summand indices.
3. Bound the total adverse coefficient mass by
   `4^(2r-2(s-1)) C_f` under `r >= floor((s+2)^2/2)`.
4. In parallel, scout the exact diagonal cumulative
   `sum_{t<n} R(t,r+n-1-t)` for a symbolic low-region reserve.  Do not open an
   infinite ladder of per-row finite-cell modules.

Nothing here inhabits `CoreBBridge`, `CrossRatioMonotone`, or any Clay-facing
frontier bundle.  Core B remains open.
