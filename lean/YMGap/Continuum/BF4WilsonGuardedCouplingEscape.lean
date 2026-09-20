/-
# Positive physical-time response forces escape from every guarded nome ceiling

Monotonicity of the ACTUAL certified Wilson rate removes the previously
supplied common-rate hypothesis. A family with nomes bounded above by one
fixed guarded W has a common strict rate, even when its completed carriers
and centered vectors vary. Its bounded positive-time responses vanish at
the explicit spacing threshold already constructed for those SAME pairings.

Conversely, a positive response floor at that threshold forces w_j > W.
This excludes survival inside any fixed guarded subinterval, not the entire
open guard region: approaching its entropy boundary is not excluded here.
It does not identify that boundary with a physical critical point, prove
w_j -> 1, exclude renormalizations with diverging lattice norms, construct
a scaling family, or establish continuum Yang--Mills.
PhysicalSpacing is supplied as the duration of TWO original lattice steps;
the tested physical time is a positive integer, not a newly calibrated time.
-/
import YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity
import YMGap.Continuum.BF4WilsonUniformLatticeRateScalingObstruction

namespace YMGap.Continuum.BF4WilsonGuardedCouplingEscape

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity (twoStepRate_mono)
open YMGap.Continuum.BF4WilsonUniformLatticeRateScalingObstruction
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- No new modulus is postulated: this computes with the certified rate at W. -/
def escapeThreshold {A : PhysicalSpacing} (Z : SpacingToZero A)
    (W : Q') (hdW : heatRemainderBound W < 1)
    (C floor : Q') (t : Nat) : Nat :=
  physicalDecayModulus Z (twoStepRate W hdW) C t (HalfPow.half * floor)

variable {w : Nat → Q'} (hw0 : ∀ j, (0 : Q') < w j) (hw1 : ∀ j, w j < (1 : Q'))
  (hsmall : ∀ j, heatRatio (w j) ≤ HalfPow.half)
  (hd : ∀ j, heatRemainderBound (w j) < 1)
  (hs : ∀ j, entropyRate 625 (adjustedCoreRate (w j) (hd j)) < 1)

variable (x : (j : Nat) → UnionCompletion (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j))

local notation:max "B" j:arg => completedInner (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)
local notation:max "U" j:arg => completedUnit (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)

/-- A lower response on the original completed carrier forces an actual nome
inequality, not merely escape of an unconstrained scalar surrogate. -/
theorem nome_gt_of_sampled_response
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t) (j : Nat)
    (hj : escapeThreshold Z W hdW C floor t ≤ j)
    (hx : B j (x j) (U j) = RCzero)
    (hcap : RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)) : W < w j := by
  apply Int.lt_of_not_ge
  intro hwW
  have hrate := rate_gt_of_response_floor hw0 hw1 hsmall hd hs x A Z t ht
    (twoStepRate W hdW) C floor (Q'.le_of_lt (twoStepRate_positive hW0 hdW))
    (twoStepRate_lt_one hW0 hdW hsW) hC hf j hj hx hcap hresponse
  exact Int.not_lt.mpr (twoStepRate_mono (Q'.le_of_lt (hw0 j)) hwW (hd j) hdW) hrate

/-- No common rate is an input; the coupling ceiling produces it. -/
theorem sampled_small_of_nome_le
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1)
    (hwW : ∀ j, w j ≤ W)
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (C : Q') (hC : (0 : Q') ≤ C)
    (hcap : ∀ j, RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (epsilon : Q') (he : (0 : Q') < epsilon) (j : Nat)
    (hj : physicalDecayModulus Z (twoStepRate W hdW) C t epsilon ≤ j) :
    RCle (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  sampledAutocorrelation_small hw0 hw1 hsmall hd hs x hx (twoStepRate W hdW) C
    (Q'.le_of_lt (twoStepRate_positive hW0 hdW)) (twoStepRate_lt_one hW0 hdW hsW) hC
    (fun j => twoStepRate_mono (Q'.le_of_lt (hw0 j)) (hwW j) (hd j) hdW) hcap
    A Z t ht epsilon he j hj

/-- The limit, when represented and supplied, is pinned to the SAME response.
The positive physical time and bounded norm are essential hypotheses. -/
theorem sampledLimit_zero_of_nome_le
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1)
    (hwW : ∀ j, w j ≤ W)
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (C : Q') (hC : (0 : Q') ≤ C)
    (hcap : ∀ j, RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (f : Nat → CReal)
    (hpin : ∀ j, Quotient.mk crealSetoid (f j) =
      sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
    (l : CReal) (hl : ConvergesTo f l) : Equiv l czero :=
  sampledLimit_zero hw0 hw1 hsmall hd hs x hx (twoStepRate W hdW) C
    (Q'.le_of_lt (twoStepRate_positive hW0 hdW)) (twoStepRate_lt_one hW0 hdW hsW) hC
    (fun j => twoStepRate_mono (Q'.le_of_lt (hw0 j)) (hwW j) (hd j) hdW) hcap
    A Z t ht f hpin l hl

/-- An explicit violating scale at or beyond ANY requested start. This
refutes a persistent response floor without using choice or a subsequence. -/
theorem no_persistent_response_below_ceiling
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1)
    (hwW : ∀ j, w j ≤ W)
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : ∀ j, RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t) (start : Nat) :
    ¬ RCle (Quotient.mk crealSetoid (ofQ' floor))
      (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t
        (max start (escapeThreshold Z W hdW C floor t))) := by
  intro hresponse
  have h := nome_gt_of_sampled_response hw0 hw1 hsmall hd hs x W hW0 hdW hsW
    C floor hC hf A Z t ht _ (Nat.le_max_right _ _) (hx _) (hcap _) hresponse
  exact Int.not_lt.mpr (hwW _) h

section CheckedPilot

open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

/-- At W=1/1024 the ceiling guards are already proved, not supplied. -/
def pilotEscapeThreshold {A : PhysicalSpacing} (Z : SpacingToZero A)
    (C floor : Q') (t : Nat) : Nat :=
  escapeThreshold Z nome existingNome_guards.2 C floor t

theorem pilot_nome_gt_of_sampled_response
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t) (j : Nat)
    (hj : pilotEscapeThreshold Z C floor t ≤ j)
    (hx : B j (x j) (U j) = RCzero)
    (hcap : RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' C)))
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)) : nome < w j :=
  nome_gt_of_sampled_response hw0 hw1 hsmall hd hs x nome nome_pos
    existingNome_guards.2 existingNome_entropyRate.2 C floor hC hf A Z t ht j hj hx hcap hresponse

end CheckedPilot

end YMGap.Continuum.BF4WilsonGuardedCouplingEscape

#print axioms YMGap.Continuum.BF4WilsonGuardedCouplingEscape.escapeThreshold
#print axioms YMGap.Continuum.BF4WilsonGuardedCouplingEscape.nome_gt_of_sampled_response
#print axioms YMGap.Continuum.BF4WilsonGuardedCouplingEscape.sampled_small_of_nome_le
#print axioms YMGap.Continuum.BF4WilsonGuardedCouplingEscape.sampledLimit_zero_of_nome_le
#print axioms YMGap.Continuum.BF4WilsonGuardedCouplingEscape.no_persistent_response_below_ceiling
#print axioms YMGap.Continuum.BF4WilsonGuardedCouplingEscape.pilotEscapeThreshold
#print axioms YMGap.Continuum.BF4WilsonGuardedCouplingEscape.pilot_nome_gt_of_sampled_response
