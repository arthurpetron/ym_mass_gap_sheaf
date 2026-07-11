/-
`IntAmpAnchors` — Milestone 14.2, second half OPENED with an ADJUDICATION:
the interacting-amplitude ledger as kernel facts, and the NAIVE ratio
normalization machine-REFUTED at `w = 1` before a session is spent
constructing it.

# The interacting ledger (kernel `decide`, axiom-FREE)

At the pilot truncation `N = 3` (spins `1..3` in the interacting block):

  * `intAmp 3 0 = 29` (diagonal pairs `(a,a)`, `a ≥ 1`: `4 + 9 + 16`);
  * `intAmp 3 1 = 36` (neighbour pairs `{1,2}, {2,3}`: `2·6 + 2·12`).

These are the DERIVED amplitudes the `w⁶`-decaying deviation carries
(`FusedFreeSplit.intBlock_le`) — the exact inputs to whatever budget check
the correct normalization produces.

# THE ADJUDICATION: the naive ratio is the WRONG defect object

The tempting second-half plan — "normalize the blocked channel by the
blocked vacuum and compare against the free ratio `dimQ s·w^{C₄(s)}`" — is
REFUTED at the fully decidable point `w = 1`:

    fusedAmp 3 1 = 40   but   2 · fusedAmp 3 0 = 60,

i.e. the naive blocked ratio tends to `40/30 = 4/3 ≠ 2 = dimQ 1` — the
channel/vacuum ratio does NOT approach the free ratio as `w → 1`
(`naive_ratio_mismatch`, kernel-checked).  A defect defined as
naive-ratio-minus-free would be `O(1)` at the continuum end and could
NEVER satisfy the `6(1−w)²` budget.  Consequence (banked per the Lakatos
discipline): the correct 14.2 defect object must carry the interaction-
induced VACUUM renormalization — the transfer-operator ratio of the
properly normalized blocked map (the transverse-MK normalization of
`docs/blockspin_defect_crux.md` / the Peter–Weyl `δ/dim` layer that
already corrected `reconTransfer`'s character-vs-eigenvalue
misidentification once) — NOT the raw fusion-coefficient ratio.  The
free/interacting split (`boxSum_free_split`) and this ledger survive
unchanged as the correct object's inputs.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; kernel `decide` on exact rationals only.  Gated with
`#print axioms`.
-/

import YMGap.Continuum.FusedFreeSplit

namespace YMGap.Continuum.IntAmpAnchors

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedChannelAll
open YMGap.Continuum.FusedFreeSplit

/-- The interacting channel-0 amplitude at `N = 3`: `4 + 9 + 16 = 29`. -/
theorem intAmp_N3_ch0 : (intAmp 3 0).eqv (Q'.ofNat 29) := by decide

/-- The interacting channel-1 amplitude at `N = 3`:
`2·(2·3) + 2·(3·4) = 36`. -/
theorem intAmp_N3_ch1 : (intAmp 3 1).eqv (Q'.ofNat 36) := by decide

/-- **`naive_ratio_mismatch` (kernel-checked REFUTATION).**  At `w = 1` the
blocked channel-1 amplitude is NOT the free multiple of the blocked
vacuum: `fusedAmp 3 1 = 40 ≠ 60 = dimQ 1 · fusedAmp 3 0`.  The naive
channel/vacuum ratio tends to `4/3`, not the free `2`: a defect defined
from the raw fusion-coefficient ratio is `O(1)` at the continuum end and
can never meet the `6(1−w)²` budget — the correct defect object must
carry the vacuum renormalization of the properly normalized blocked
transfer map. -/
theorem naive_ratio_mismatch :
    ¬ (fusedAmp 3 1).eqv (Q'.ofNat 2 * fusedAmp 3 0) := by decide

end YMGap.Continuum.IntAmpAnchors

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.IntAmpAnchors.intAmp_N3_ch0
#print axioms YMGap.Continuum.IntAmpAnchors.intAmp_N3_ch1
#print axioms YMGap.Continuum.IntAmpAnchors.naive_ratio_mismatch
