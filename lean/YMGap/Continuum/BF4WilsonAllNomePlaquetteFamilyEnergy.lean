/-
# The whole signed family's temporal energy on its existing completion

The original joint squared increment is twice the temporal defect form of
the SAME already constructed centered Wilson family. All signed cross terms
and the original partition survive the finite-to-completed join.

The transferred coefficient floor is a LOWER energy estimate at fixed nome.
It is not an upper estimate relative to variance, a positive-time survival
theorem, or a scaling/continuum statement.
-/

import YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
open YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement (family_increment_floor)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector centeredVector_loss_pin)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "e" => familyExpression width qs c hqs
local notation "he" => family_within width qs c hqs
local notation "x" => familyState width qs c hqs
local notation "v" => Subtype.val (familyExcitation hw0 hw1 width qs c hqs)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- The entire signed increment is exactly twice the SAME completed
temporal defect, not the squared norm of `v - T n v`. -/
theorem family_increment_completed_pin (n : Nat) :
    Quotient.mk crealSetoid (increment hw0 hw1 e he n) =
      RCscale 2 (RCsub (B v v) (B v (T n v))) := by
  change Quotient.mk crealSetoid (increment hw0 hw1 e he n) =
    RCscale 2 (RCsub
      (B (centeredVector hw0 hw1 x) (centeredVector hw0 hw1 x))
      (B (centeredVector hw0 hw1 x) (T n (centeredVector hw0 hw1 x))))
  rw [centeredVector_loss_pin, RCsub_mk, RCscale_mk]
  exact Quotient.sound (increment_reflected_pin hw0 hw1 e he n)

/-- The previously proved original family-energy floor now applies to this
actual completed operator and vector. Nome dependence is unchanged. -/
theorem family_temporalEnergy_floor (hn : qs.Nodup) :
    RCle (Rq (varianceFloor w hw0 * listQSum (fun face => c face*c face) qs))
      (RCsub (B v v) (B v (T 1 v))) := by
  let b := varianceFloor w hw0 * listQSum (fun face => c face*c face) qs
  have h : RCle (Rq ((2 : Q')*b))
      (Quotient.mk crealSetoid (increment hw0 hw1 e he 1)) :=
    family_increment_floor hw0 hw1 width qs c hqs hn
  rw [family_increment_completed_pin] at h
  have hs := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) h
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (by decide : Q'.eqv (HalfPow.half*2) 1),
    RCscale_one] at hs
  have hl : RCscale HalfPow.half (Rq ((2 : Q')*b)) = Rq b := by
    rw [RCscale_mk]
    apply Quotient.sound
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half 2 b))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ b (by decide : Q'.eqv (HalfPow.half*2) 1))
          (Q'.one_mul_eqv b)))
  rw [hl] at hs
  exact hs

#print axioms family_increment_completed_pin
#print axioms family_temporalEnergy_floor

end YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyEnergy
