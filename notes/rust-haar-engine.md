# The Rust contraction engine — the evaluation-technology item, executed

2026-07-28, fourth stage of the session.  Code
`rust/haar_contract/` (crate) + `computations/su2_rust_eval.py`
(driver/gates); pins `tests/test_rust_eval.py`.  Executes the §16i
"single critical-path item" in its pragmatic form: not yet the
recoupling (6j) evaluator, but a faithful port of the
exact_haar_network hot core that removes the representation
overhead §16i identified as the wall.

## 1. What is ported

`p_mul` (sparse multivariate multiply with monomial merge + size
cap), `integrate_link` (the exact S^3 moment formula), 
`p_reduce_units` (z^2 -> 1 - w^2 - x^2 - y^2 canonicalization),
and the `_eliminate_all` greedy elimination with the
pair-premerge fallback of `contract`.  Arithmetic: num-bigint
rationals — exact, no floats.  Monomials: packed (var, exp) byte
vectors (the Python dict/Fraction representation costs ~20-50x
more memory per monomial).  Factors are still CONSTRUCTED by the
gated Python path (chi/holonomy of the gauge-fixed complex); only
the contraction crosses the FFI boundary (JSON, big-int strings).

## 2. Gates (all green)

The full banked-value battery: the D4-gate values (1/331776,
1/62208), the SIGNED negative configs of dp3_m2_entries for the
(1,1), (0,1), (1,2) entries (sign and magnitude exact — 6j
interference is the hard case), and Python-computed diagonals from
the CS ledger.  Plus the standing lemma pin: every landed direct
M=2 value satisfies the OS/CS bound against its diagonal partners.

## 3. The wall, before and after

- reference diagonal (Python greedy 556 s):  Rust 61 s;
- gate-battery cases (Python 24-40 s):       Rust 0.4-11 s;
- the all-walls-active M=2-unreached configs (Python: NEVER landed,
  300 s original budget, 600-900 s retries):  Rust 78-203 s — the
  class that §16i named as the blocker now completes;
- a residual hard sub-class remains (BUDGET at 300 s / 10M
  monomials, e.g. q=(0,0,2,2) w=(0,2,2,2) patterns and the 908 s
  diagonal): larger budgets/caps land some; the recoupling
  evaluator remains the structural fix for the rest.

## 4. Consumption

The sweep driver (/tmp-tier, results in the banked ledgers
`su2_cs_diagonals.json*` and `su2_m2_finality.json*`) walks the
ENTIRE blocked tier — M=2-unreached direct values (each kills its
U_2 contribution outright, tightening T_2 on both sides) and the
need-ranked level-3 diagonal keys (each collapses its crude tail
mass by the OS/CS lemma) — in (1,1)-first priority order, since
(1,1) is the binding entry of every closed window.  The certified
window assembly (`su2_m2_finality.combined_x11_window`) consumes
new values with no code change.

## 5. Honesty

The Rust engine is gated against every banked exact value but is
NOT itself formally verified; it is scaffolding in exactly the
sense of the §16d convention (its outputs enter certified windows
only as exact rationals cross-checked where Python values exist,
and the OS/CS-lemma pin runs over all landed values).  Budget
misses are recorded as unreached, never consumed.  The recoupling
(6j/corner-basis) evaluator — microsecond evaluation and the TRUE
corner transfer weights — remains the structural open item; this
port turns it from a blocker into an optimization.
