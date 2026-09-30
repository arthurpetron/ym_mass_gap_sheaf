/-
# Signed-family coercivity on the literal all-nome Wilson completion

The old spatial plaquette-family scalar and the literal Wilson expression
have identical finite source polynomials in one original window ratio.
Uniqueness of their existing diagonal limits identifies their means and
diagonal moments. This transfers the already proved signed-family floor to
an actual centered vector in the Wilson completion, not to a replacement
carrier. No new finite dual construction or whole-carrier isometry is used.

The constant is uniform in width and family size at each FIXED strict nome.
Its deterioration as the nome tends to one is unchanged. No positive-time
survival, spatial/spacing comparison, or continuum mass gap is asserted.
-/

import YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance
import YMGap.Continuum.BF4WilsonAllNomeCenteredVector

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (mixedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit physicalTime_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamily (familySpan familySpan_radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar chartScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (jointPairing_symm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm (jointCenteredMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance (family_joint_variance_floor)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor varianceFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (commonForm intrinsicForm intrinsicForm_chart intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
open YMGap.Continuum.BF4WilsonAllNomeFormLaws (intrinsicForm_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime VacuumComplement)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

attribute [local irreducible] chartScalar chartJointLimit jointPairing
  originalJointLimit originalWindowScalar intrinsicForm

/-- A scalar chart comparison only: both convergent sequences use the same
finite original ratio after the supplied coefficient identity. -/
private theorem zero_radius_pairing_pin {width : Nat}
    (p q : PhysicalSpan width) (x y : IntrinsicExpression width)
    (hp : radius p.val ≤ 0) (hq : radius q.val ≤ 0)
    (hx : x.radius = 0) (hy : y.radius = 0)
    (hsource : RatPolyCoeffEqv
      (mixedProduct width 0 (encodeChart 0 p.val) (encodeChart 0 q.val))
      (sourcePolynomial (.mul (mirror 0 x.expression) y.expression))) :
    Equiv (jointPairing hw0 hw1 width p q) (intrinsicForm hw0 hw1 x y) := by
  have hye : Within 0 y.expression := hy ▸ y.within
  have he : Within 0 (.mul (mirror 0 x.expression) y.expression) :=
    ⟨mirror_within 0 x.expression, hye⟩
  have hlimits : Equiv (chartJointLimit hw0 hw1 width 0 p q hp hq)
      (originalJointLimit hw0 hw1 0 (.mul (mirror 0 x.expression) y.expression) he) := by
    apply Equiv_of_limit_of_equal ?_
      (chartJoint_diagonal_converges hw0 hw1 width 0 p q hp hq)
      (originalJoint_diagonal_converges hw0 hw1 0
        (.mul (mirror 0 x.expression) y.expression) he)
    intro stage
    apply SumOfSquares.Equiv_of_approx_eqv
    intro k
    exact Q'.eqv_trans _ _ _
      (chartScalar_pin hw0 hw1 width stage 0 p q hp hq stage)
      (Q'.eqv_trans _ _ _
        (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) stage 0 stage hsource)
        (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 0
          (.mul (mirror 0 x.expression) y.expression) he stage stage stage)))
  have hnew := intrinsicForm_chart hw0 hw1 x y 0
    (by rw [hx]; exact Nat.le_refl 0) (by rw [hy]; exact Nat.le_refl 0)
  have hnew' : Equiv (intrinsicForm hw0 hw1 x y)
      (originalJointLimit hw0 hw1 0 (.mul (mirror 0 x.expression) y.expression) he) := by
    simpa only [commonForm, chart, hx, hy, Nat.sub_self, shift_zero,
      Nat.mul_zero] using hnew
  exact (jointPairing_chart hw0 hw1 width 0 p q hp hq).trans
    (hlimits.trans hnew'.symm)

variable (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "p" => familySpan width qs c hqs
local notation "x" => familyState width qs c hqs
local notation "u" => BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit width
local notation "J" => jointPairing hw0 hw1 width
local notation "F" => intrinsicForm hw0 hw1
local notation "B" => completedInner hw0 hw1

/-- The actual signed family's original mean, with no carrier identification. -/
theorem family_mean_pin : Equiv (J p (unit width)) (F x u) := by
  exact zero_radius_pairing_pin hw0 hw1 p (unit width) x u
    (by rw [familySpan_radius]; exact Nat.le_refl 0) (Nat.le_refl 0)
    rfl rfl (mixedProduct_mean width qs c hqs)

/-- The complete square is compared before limits; every signed cross term
and the common partition remain present. -/
theorem family_square_pin : Equiv (J p p) (F x x) := by
  exact zero_radius_pairing_pin hw0 hw1 p p x x
    (by rw [familySpan_radius]; exact Nat.le_refl 0)
    (by rw [familySpan_radius]; exact Nat.le_refl 0)
    rfl rfl (mixedProduct_square width qs c hqs)

/-- Equal connected scalars do not assert equal completed carriers. -/
theorem centered_norm_pin :
    Equiv (jointCenteredMoment hw0 hw1 width 0 p p)
      (centeredTimeMoment hw0 hw1 0 x x) := by
  have hm := family_mean_pin hw0 hw1 width qs c hqs
  have hm' : Equiv (J (unit width) p) (F u x) :=
    (jointPairing_symm hw0 hw1 width (unit width) p).trans
      (hm.trans (intrinsicForm_symm hw0 hw1 x u))
  unfold jointCenteredMoment centeredTimeMoment
  rw [physicalTime_zero, advance_zero]
  exact Equiv_add (family_square_pin hw0 hw1 width qs c hqs)
    (neg_congr ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm')))

/-- The existing fixed-nome, width-independent signed coefficient floor now
holds on the literal Wilson intrinsic form. -/
theorem centered_norm_floor (hn : qs.Nodup) :
    leEv (ofQ' (varianceFloor w hw0 * listQSum (fun face => c face*c face) qs))
      (centeredTimeMoment hw0 hw1 0 x x) :=
  leEv_trans (family_joint_variance_floor hw0 hw1 width qs c hqs hn)
    (leEv_of_equiv (centered_norm_pin hw0 hw1 width qs c hqs))

/-- A constructed vector in the EXISTING literal Wilson vacuum complement. -/
def familyExcitation : VacuumComplement hw0 hw1 (width := width) :=
  centeredExcitation hw0 hw1 x

/-- Signed-family coercivity on this actual completed vector. -/
theorem familyExcitation_norm_floor (hn : qs.Nodup) :
    RCle (Quotient.mk crealSetoid
      (ofQ' (varianceFloor w hw0 * listQSum (fun face => c face*c face) qs)))
      (B (familyExcitation hw0 hw1 width qs c hqs).val
        (familyExcitation hw0 hw1 width qs c hqs).val) := by
  change RCle _ (B (centeredVector hw0 hw1 x) (centeredVector hw0 hw1 x))
  rw [centeredVector_diagonal]
  exact centered_norm_floor hw0 hw1 width qs c hqs hn

/-- A positive coefficient budget gives positive norm, not just a formal
vacuum-complement expression. The floor still depends on nome. -/
theorem familyExcitation_norm_ne_zero (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs) :
    B (familyExcitation hw0 hw1 width qs c hqs).val
      (familyExcitation hw0 hw1 width qs c hqs).val ≠ RCzero := by
  intro hz
  have h := familyExcitation_norm_floor hw0 hw1 width qs c hqs hn
  rw [hz] at h
  have hle : varianceFloor w hw0 * listQSum (fun face => c face*c face) qs ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (Q'.mul_pos (varianceFloor_positive hw0 hw1) hc) hle)

theorem familyExcitation_ne_zero (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs) :
    (familyExcitation hw0 hw1 width qs c hqs).val ≠ embed hw0 hw1 (zero width) := by
  intro hz
  apply familyExcitation_norm_ne_zero hw0 hw1 width qs c hqs hn hc
  rw [hz, completedInner_embed]
  exact Quotient.sound (intrinsicForm_zero_left hw0 hw1 (zero width))

/-- Its correlations are those of the same existing completed time operator.
This is an exact pin, not a positive-time lower bound. -/
theorem familyExcitation_correlator_pin (n : Nat) :
    B (familyExcitation hw0 hw1 width qs c hqs).val
      (completedTime hw0 hw1 n (familyExcitation hw0 hw1 width qs c hqs).val) =
      Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 n x x) :=
  centeredVector_time_pairing hw0 hw1 n x

#print axioms family_mean_pin
#print axioms family_square_pin
#print axioms centered_norm_pin
#print axioms centered_norm_floor
#print axioms familyExcitation
#print axioms familyExcitation_norm_floor
#print axioms familyExcitation_norm_ne_zero
#print axioms familyExcitation_ne_zero
#print axioms familyExcitation_correlator_pin

end YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
