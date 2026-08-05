/-
Track 11.7-fusion / R2b — **the exact bare-reference statement fence and the
re-based bulk-to-gap-edge localization bridge.**

# Why this module exists

`FusionKernelStatement.SaddleLocalCLT.bulkShiftBound` compares the physical
`p`-fold fusion eigenvalue with the *bare* `p = 1` heat rate `eigA w s`.  The
companion module `RebasedBulkShift` explains why this is the wrong reference for
`p >= 2` and replaces it by `rateP w_eff s`.

This module makes both sides of that correction kernel-visible.

1. At the small, exact near-continuum point

       N = 3,  w = 11/12,  p = 2,  s = 2,

   the literal bare shift is strictly larger than `1/12`.  Thus the physical
   fusion spectrum cannot inhabit either the old `SaddleLocalCLT` field or a
   `SpectralLocalization` whose `eig'` is pinned to that spectrum.  This is a
   theorem, not a numerical pilot and not an informal warning.

2. For the corrected `RebasedLocalCLT`, the downstream bulk localization step
   is closed: if `w_eff` is a genuine weight and the mode is bulk at `w_eff`,
   then the physical fusion eigenvalue is at most the original gap edge
   `eigA w 1`.  The proof spends `2/3 + 1/12 = 3/4` and uses the original
   near-continuum lower bound `3/4 <= eigA w 1`.

The remaining physical input is exactly `RebasedBulkShift.ExpShiftBridge`; this
file neither inhabits nor weakens that named-open analytic carrier.

# Axiom gate

All load-bearing declarations are checked below with `#print axioms`.  The
counterexample is exact kernel `decide` over finite rational fusion sums.  There
is no `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
definition.
-/

import YMGap.Continuum.RebasedBulkShift
import YMGap.Continuum.EigenvalueShiftBridge

namespace YMGap.Continuum.RebasedBulkLocalizationBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkShift

/-! ## 1. Exact statement fence for the old bare-reference carrier -/

/-- The exact near-continuum fence weight `11/12`. -/
def fenceW : Q' := Q'.mkPos 11 12 (by decide)

/-- `fenceW` is a physical nonnegative heat weight. -/
theorem fenceW_nonneg : (0 : Q') <= fenceW := by decide

/-- `fenceW` is at most one. -/
theorem fenceW_le_one : fenceW <= (1 : Q') := by decide

/-- The fence lies exactly on the canonical near-continuum boundary. -/
theorem fenceW_near_continuum : (1 : Q') - fenceW <= q112 := by decide

/-- Vacuum positivity for the concrete `N = 3`, `p = 2` fusion kernel. -/
theorem fenceBmcZero_pos : (0 : Q') < bondMovedCoeff 3 fenceW 2 0 :=
  S1Dominance.bmc_zero_pos 3 fenceW_nonneg fenceW_le_one 2 (by decide)

/-- Positive eigenvalue denominator for every mode at the fence point. -/
def fenceDenomPos (s : Nat) :
    (0 : Q') < dimQ s * bondMovedCoeff 3 fenceW 2 0 :=
  fusionEigDenom_pos s fenceBmcZero_pos

/-- **Exact obstruction.**  At `N=3`, `w=11/12`, `p=2`, `s=2`, the physical
fusion eigenvalue's shift above the bare `p=1` heat rate is *not* at most
`1/12`.  This finite rational statement is discharged by kernel reduction. -/
theorem bareFusionShift_two_not_le :
    ¬ (fusionEig 3 fenceW 2 2 (fenceDenomPos 2) - eigA fenceW 2 <= q112) := by
  decide

/-- Consequently the old bare-reference `SaddleLocalCLT` has no physical
inhabitant at this exact near-continuum `p=2` point. -/
theorem noBareSaddleLocalCLT :
    SaddleLocalCLT 3 fenceW 2 fenceDenomPos -> False := by
  intro S
  exact bareFusionShift_two_not_le (S.bulkShiftBound 2)

/-- A `SpectralLocalization` pinned to the actual physical fusion eigenvalues at
the fence point.  This is a diagnostic carrier only: the next theorem proves it
has no inhabitant because the old shift reference is too small. -/
structure BareFusionLocalizationAtFence : Type where
  localization : SpectralLocalization fenceW
  pinsFusionEig : forall s,
    localization.eig' s = fusionEig 3 fenceW 2 s (fenceDenomPos s)

/-- The old canonical localization shape cannot be pinned to the actual
`p=2` fusion spectrum at the fence point.  Its `pert` and `bulk_shift` fields
would imply the exact inequality refuted by `bareFusionShift_two_not_le`. -/
theorem noBareFusionLocalizationAtFence :
    BareFusionLocalizationAtFence -> False := by
  intro B
  have hpert := B.localization.pert 2
  rw [B.pinsFusionEig 2] at hpert
  have hsub :
      fusionEig 3 fenceW 2 2 (fenceDenomPos 2) - eigA fenceW 2
        <= B.localization.shift 2 :=
    Q'.sub_le_of_le_add hpert
  have hle :
      fusionEig 3 fenceW 2 2 (fenceDenomPos 2) - eigA fenceW 2 <= q112 :=
    Q'.le_trans' _ _ _ hsub (B.localization.bulk_shift 2)
  exact bareFusionShift_two_not_le hle

/-! ## 2. Corrected re-based bulk localization -/

/-- **The corrected physical bulk-to-gap-edge bridge.**  A re-based local-CLT
bound controls the fusion eigenvalue relative to `rateP R.weff`.  If `R.weff`
is in `[0,1]` and `s` is bulk at that effective weight, then `rateP <= 2/3`.
Spending the `1/12` re-based shift gives `fusionEig <= 3/4`; near the continuum
the original gap edge satisfies `3/4 <= eigA w 1`.

This is precisely the downstream step that the original `RebasedBulkShift`
module left separate.  It is uniform in `N`, `p`, and `s`; no bare-reference
shift hypothesis is used. -/
theorem rebasedFusion_bulk_below_gapEdge {N : Nat} {w : Q'} {p : Nat}
    {h0' : forall s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (R : RebasedLocalCLT N w p h0')
    (hweff0 : (0 : Q') <= R.weff) (hweff1 : R.weff <= (1 : Q'))
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hnc : (1 : Q') - w <= q112) (s : Nat)
    (hbulk : q12 <= Q'.ofNat (c4 s) * ((1 : Q') - R.weff)) :
    fusionEig N w p s (h0' s) <= eigA w 1 := by
  have hrate : rateP R.weff s <= q23 :=
    bulk_eigA_le hweff0 hweff1 s hbulk
  have hfusion :
      fusionEig N w p s (h0' s) <= q112 + rateP R.weff s :=
    EigenvalueShiftBridge.le_add_of_sub_le (R.rebasedBulkShift s)
  have hsum : q112 + rateP R.weff s <= q112 + q23 :=
    qadd_le_add (Q'.le_refl' q112) hrate
  have hedge : q112 + q23 <= eigA w 1 :=
    Q'.le_trans' _ _ _ (by decide : q112 + q23 <= q34)
      (gapEdge_ge hw0 hw1 hnc)
  exact Q'.le_trans' _ _ _ hfusion (Q'.le_trans' _ _ _ hsum hedge)

end YMGap.Continuum.RebasedBulkLocalizationBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.fenceW_nonneg
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.fenceW_le_one
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.fenceW_near_continuum
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.fenceBmcZero_pos
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.fenceDenomPos
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.bareFusionShift_two_not_le
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.noBareSaddleLocalCLT
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.noBareFusionLocalizationAtFence
#print axioms YMGap.Continuum.RebasedBulkLocalizationBridge.rebasedFusion_bulk_below_gapEdge
