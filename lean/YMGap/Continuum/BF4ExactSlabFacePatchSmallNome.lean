/-
# Signed local generator-square bound on an original physical face patch

The actual original-action conditional residuals on one four-link face
obey the existing two-link signed estimate. Three off-diagonal neighbors
per row cost six pair coefficients. No local spectral input is assumed,
and positivity of this coefficient is not asserted for every nome.
-/

import YMGap.Continuum.BF4ExactSlabFacePatchSize
import YMGap.Continuum.BF4ExactSlabConditionalGeneratorLowerBound

namespace YMGap.Continuum.BF4ExactSlabFacePatchSmallNome

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabTwoLinkResidualLowerBound
open YMGap.Continuum.BF4ExactSlabFacePatchSize
open YMGap.Continuum.RingNormaliser

private instance (extent : Nat) : DecidableEq (PhysicalLink extent) :=
  inferInstanceAs (DecidableEq {i // i ∈
    YMGap.Continuum.Z4HalfTimeReflectionGeometry.boundaryCompleteSlabLinks extent})

/-- The face-patch coefficient retains all signed pair terms. -/
def faceCoefficient {w : Q'} (hd : heatRemainderBound w < 1) : Q' :=
  1 + -(6 * pairCoefficient hd)

theorem faceCoefficient_le_one {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) : faceCoefficient hd ≤ (1 : Q') := by
  have he : (0 : Q') ≤ pairCoefficient hd := pairCoefficient_nonnegative hw0 hd
  have h6 : (0 : Q') ≤ 6 * pairCoefficient hd :=
    Q'.mul_nonneg _ _ (by decide) he
  unfold faceCoefficient
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h6)) (by decide)

private theorem margin_scale (e : Q') (a : RC) :
    RCadd a (RCneg (RCscale (6 * e) a)) =
      RCscale (1 + -(6 * e)) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.mul (.const 6) (.var 1)) (.var 0))))
      (.mul (.add (.const 1) (.neg (.mul (.const 6) (.var 1)))) (.var 0))
      (by decide) (fun | 0 => A.approx n | _ => e)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

include hsmall in
/-- Actual all-completed-vector local square lower bound for the four-link
patch on one ORIGINAL physical face. It retains the original full action,
including its exterior, and all signed pair terms. -/
theorem actual_face_lower (id : Nat) (x : GNSCompletionSpace F) :
    RCle
      (RCscale (faceCoefficient hd)
        ((P).finalEnergy (facePatch extent id) x))
      (normSq ((P).residualSum (facePatch extent id) x)) := by
  let patch := facePatch extent id
  let e := pairCoefficient hd
  let E := (P).finalEnergy patch x
  have hcross := (P).neighboringCross_lower (fun _ _ => true) patch x 3 e
    (pairCoefficient_nonnegative hw0 hd)
    (fun i hi => facePatch_other_length_le_three extent id i hi)
    (fun j hj => by
      have h := facePatch_other_length_le_three extent id j hj
      have heq : patch.filter (fun i => if i = j then false else true) =
          patch.filter (fun i => if j = i then false else true) := by
        apply List.filter_congr
        intro i _
        by_cases hij : i = j
        · subst i
          simp only [if_pos rfl]
        · simp only [if_neg hij, if_neg (Ne.symm hij)]
      change (patch.filter (fun i => if i = j then false else true)).length ≤ 3
      rw [heq]
      exact h)
    (fun i j _ _ _ _ => conditional_residual_pair_lower hw0 hw1 hsmall hd
      K extent hK i.val j.val i.property j.property x)
  have hcoeff : Q'.eqv ((2 : Q') * Q'.ofNat 3 * e) (6 * e) :=
    Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv ((2 : Q') * Q'.ofNat 3) 6)
  rw [RCSignedPairBudget.scale_congr hcoeff] at hcross
  have hdiag := RCadd_le_add (RCle_refl E) hcross
  rw [margin_scale] at hdiag
  have hgram := (P).neighborhoodGram_le_residualSum_square
    (fun _ _ => true) (fun _ _ h _ => False.elim (by cases h)) patch x
  rw [(P).neighborhoodGram_diagonal (fun _ _ => true)
    (fun _ => rfl) patch (facePatch_nodup extent id)] at hgram
  exact RCle_trans hdiag hgram

#print axioms faceCoefficient
#print axioms faceCoefficient_le_one
#print axioms actual_face_lower

end YMGap.Continuum.BF4ExactSlabFacePatchSmallNome
