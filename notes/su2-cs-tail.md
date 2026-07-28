# The OS/Cauchy-Schwarz sharpened tail — reflection positivity as a quantitative |N| bound

2026-07-28, third stage of the session.  Code
`computations/su2_cs_tail.py`; ledgers `su2_cs_diagonals.json*`,
`su2_cs_tail_results.json`; pins in `tests/test_cs_tail.py`.
Executes the §16g "interim sharpening" — upgraded from an exact-N
hybrid to a REFLECTION-POSITIVITY bound, the config-level shadow of
DP.R1's OS Gram.

## 1. The lemma

The DP.3 OS pairing (link reflection theta: z -> 1-z through the
plane z = 1/2, dp3_rp_check conventions) restricts to each fixed
transverse sector: the perimeter-class labels q and interior-wall
labels w sit on theta-invariant vertical faces carrying SINGLE
characters (positive spectral weight — the Osterwalder-Seiler
condition), the top data (loop n, tiles a) lives strictly above the
plane, the bottom data (m, b) strictly below.  OS link-reflection
positivity therefore holds SECTOR-WISE, and Cauchy-Schwarz in the
OS inner product gives, for every admissible fixed-tile labelling,

    N(n, m, q, w, a, b)^2 <= N(n, n, q, w, a, a)
                             * N(m, m, q, w, b, b),

with both right-hand values >= 0 (OS norms).  This is the
fixed-tile-granular form of the DP.R1 Gram statement.

## 2. Machine gates (all green)

- **CS gate.**  Verified on the banked EXACT negative network
  values of dp3_m2_entries (their diagonal partners computed here):
  e.g. N = -1/1492992 with sqrt(D_a D_b) ~ 8.9e-7 >= |N| — a
  nontrivial check because the left side is strictly negative
  (signed 6j interference) while the bound is a product of norms.
- **D4 gate.**  The canonicalization used to dedup diagonal keys
  (simultaneous rotation/reflection of (q, w, tiles) in the
  dp3_fixed_tile corner conventions) is verified against computed
  values: rotation, reflection, and wall-shift images agree exactly
  (1/331776 and 1/62208 test cases).
- **Positivity.**  Every computed diagonal value is >= 0, as the
  lemma requires (asserted at computation time).

## 3. The quantitative gain

Crude domination bounds |N| <= d_n d_m prod_f d ~ 10^3..10^5 per
config; the computed diagonals give sqrt(D_a D_b) ~ 10^-7..10^-6:
NINE TO TWELVE orders of magnitude recovered per covered config.
Coverage strategy: level-3 configs ranked by the crude tail mass
they carry (steep profile — the top ~100 diagonal keys own
essentially all of it); diagonal values computed exactly
(network_value_fixed) under wall-clock budgets, one-sided CS
(sqrt(D_a) x crude half) where only one side is available, crude
fallback otherwise — every path certified, unreached values only
LOOSEN the bound.  Levels >= 4 keep the §16g domination-transfer
bound.  Windows: see the results ledger; the certified X_11 > 0
domain extends beyond the §16g s = 1/2 point toward the series
domain.

## 4. What this is a shadow of

The corner-transfer program proper (replace domination weights by
true recoupling amplitudes) subsumes this: the diagonal values
N(n,n,q,w,a,a) are exactly the DIAGONAL entries of the corner
Gram, and the full amplitude factorization would make every |N|
available at once instead of config-by-config.  The lemma and its
gates stand independently of that program's completion.

## 5. Honesty

The lemma's proof is the standard OS-Seiler link-reflection
argument applied sector-wise; it is machine-VERIFIED on the banked
exact values but the written proof lives at the standard-literature
level of rigor (a Lean-grade formalization is not claimed).  The
diagonal computations inherit the Haar engine's exactness; budget
timeouts are recorded as unreached (never consumed as values).
Cloud-side only; the usual Mac session-lock and push obligations
apply to the banking commit.
