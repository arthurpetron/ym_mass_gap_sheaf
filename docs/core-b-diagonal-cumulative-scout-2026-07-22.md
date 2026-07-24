# Core-B diagonal-cumulative scout — linear-length reserve recovery

**Date:** 2026-07-22  
**Status:** exact-arithmetic design result; not a proof of Core B

## Result

The first all-row scout found that the one-cell constant-reserve tactic fails
at `(s,r)=(4,0)` and increasingly many later-row cells.  The exact cumulative
recurrence provides a better target:

```text
C(s,r,n) = sum_{t<n} R(s+t, r+n-1-t).
```

Sparse exact expansion through rows `s=1,...,8` finds the tested-minimal
constant-reserve payment length

```text
n_pay(s,r) = max(1, s-r-2).
```

For example, at `r=0` the minimal tested lengths for rows `4,...,8` are
`2,3,4,5,6`.  At row 8 and offsets `r=0,...,4`, they are `6,5,4,3,2`.
Thus the obstruction is not an infinite ladder of isolated cells: moving one
step right in offset removes one required diagonal term.

For `s>=3` and `0<=r<=s-3`, every checked predicted-length cumulative has
the same leading content and constant reserve:

```text
content(s) = 4s^2 + 4s - 2,
reserve(s) = 4 s^5 (s+1)^2 (s+2).
```

The reserve formula was checked by exact expansion through row 12; the full
payment/minimal-length regression was checked through row 8.  These formulas
give the symbolic proof an explicit positive source term.

The payment is rigorous for each computed polynomial.  After factoring the
common `(wh)^m`, it discards positive nonconstant monomials, bounds every
adverse `c w^a h^b` by `c 4^-(a+b)` on `0 <= h <= w <= 1/4`, and checks with
exact rational arithmetic that the remaining constant reserve pays the sum.

## Implication

The new Lean target should be a symbolic diagonal theorem, not termwise
positivity throughout the quadratic low region.  A promising split is:

1. use the all-row anchor theorem in the sign-stable tail;
2. use a direct residual payment where `r >= s-2`;
3. for `r < s-2`, use the cumulative of length `s-r-2` and prove its common
   reserve `4 s^5 (s+1)^2 (s+2)` pays the discounted adverse mass.

This turns the observed low-region depth from the quadratic threshold
`floor((s+2)^2/2)` into a linear diagonal length.  Proving the displayed
formula for all indices still requires the bounded-index monomial normal form
and a symbolic coefficient-mass bound.  Nothing here inhabits `CoreBBridge`
or `CrossRatioMonotone`.

## Consumer and parity correction

The determinant telescope consumes arbitrary root-start lengths, whereas the
formula above describes the tested-minimal odd low diagonal.  The exact split

```text
C(0,r,n+1) = R(0,r+n) + C(1,r,n)
```

reduces the necessary certificate to row-zero residuals plus all row-one
cumulatives, but it also makes the missing parity visible.  The predicted
low-diagonal blocks above all satisfy `row+offset=2s-3`.  On the adjacent even
prefix family, exact sparse expansion through row 8 instead finds

```text
content_even(s) = 4s^2 - 4,
constant_reserve_even(s) = 0.
```

Thus the constant-reserve tactic fails there.  Exact physical-simplex sweeps
found no negative value, so the next symbolic target is a positive
nonconstant grouping, not a claim of failure.  A complete proof must treat
both parity-uniform prefix families before invoking the root consumer.

## Consumer-origin correction and the true endpoint

The preceding paragraph still overstates what the downstream theorem needs.
`CrossRatioMonotone.cross s` consumes only

```text
offsetDelta(wH, w, s, 0),
```

so the diagonal telescope needs only `C(wH,w,0,0,s)`.  After the exact root
split, the sole all-length analytic family is

```text
C(wH,w,1,0,n),
```

not every `C(1,r,n)`.  On this complete consumer diagonal, the direct head and
the odd/even low suffix must be collected *before* extracting a reserve.  This
collection restores a positive constant reserve in both parities; the zero
reserve of the isolated even suffix is therefore not the final obstruction.

There is also a load-bearing domain correction.  The older residual payments
assume the larger determinant endpoint satisfies `4w <= 1`, whereas the
cross-ratio determinant is oriented from `wH = 1/2`.  Those positivity theorem
signatures cannot be instantiated at the consumer.  The correct monomial cap
at the fixed endpoint is

```text
wH^a h^b <= 2^-(a+b),       0 <= h <= wH,
```

not `4^-(a+b)`.  Re-running the exact ledger with that weaker, correct discount
still succeeds through every checked consumer length.  Exact expansion through
`n=15` (18,049 collected quotient monomials in the last cell) gives ratios
between `0.037393` and `0.160381`; in particular the stronger candidate bound
`6 * discounted_adverse <= reserve` survives every checked length.  The first
seven ratios are

```text
0.037393, 0.140368, 0.105057, 0.141235,
0.114952, 0.149297, 0.119422.
```

A second, deliberately coarser ledger now discards all cancellations between
distinct residual cells (while retaining collection inside each cell).  This
cellwise adverse mass is still paid with fourfold slack through `n=13`; the
largest checked ratio is `0.206074 < 1/4`.  This is a more promising symbolic
target than the sixfold collected bound because every residual block can be
estimated independently.  The intended proof is an exact central-band check
plus a quadratic-Casimir-gap geometric bound on the off-center blocks.

The triangle estimate can be pushed one step further: split every adverse
determinant family before *any* equal-monomial collection.  This fully atomwise
debt still satisfies `2 * debt <= reserve` through `n=11`, with ratios

```text
0.1954, 0.21883, 0.35520, 0.27962, 0.37852, 0.29838,
0.38928, 0.30873, 0.39541, 0.31503, 0.39924.
```

For `n=2k`, a cell `d` places left of center gains content discount
`2^(-8d^2)`; for `n=2k+1` it gains `2^(-8d(d+1))`.  On the right, the minimum
quotient gaps grow quadratically after the first two central cells.  The exact
even gap-4 and gap-8 contributions are bounded by `reserve/4` and
`3*reserve/64`; the odd gap-4 contribution is
`reserve * (1/8 - 1/(4(k+2)(k+3)))`.  These formulas make the atomwise
factor-two inequality the preferred closure target: unlike the sixfold bound,
it needs no canonical cross-family cancellation theorem.

The checked common-content formulas are, with `n=2k` or `n=2k+1`,

```text
content(2k)   = 4k^2 + 16k + 12,
content(2k+1) = 4k^2 + 20k + 22.
```

The collected constant reserves are

```text
reserve(1)  = 11232,
reserve(2k) = 4 (k+1) (k+2)^6 (k+3),

reserve(2k+1) =
  8 (k+2)^2 (k+3)^2 [2 (k+2)^3 (k+4) - (2k+5)]     (k >= 1).
```

The formulas were also checked through `n=18`.  These are exact-arithmetic
design formulas, not yet Lean theorems.  Their main
implication is strategic: the shortest proof should establish one parity-
uniform coefficient-mass bound for the complete `C(1,0,n)` family at the fixed
endpoint.  Proving every low prefix or the row-one residual tail separately is
strictly stronger and reintroduces a parity obstruction that the consumer does
not have.

## Reproduction

```sh
python3 computations/core_b_diagonal_cumulative_scout.py \
  --rows 1 2 3 4 5 6 7 8 --max-offset 4 --check-even-prefixes \
  --check-canonical-consumer 15
```
