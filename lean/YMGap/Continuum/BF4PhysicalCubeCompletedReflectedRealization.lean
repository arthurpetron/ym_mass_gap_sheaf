/-
# The actual completed one-step form realizes the all-spin cube kernel

The explicit cube-cylinder map lands in the existing completed marginal
carrier. Its pairing for E(x,y)=B(x,Py), with the actual cutoff-removed P,
is exactly the constructed normalized raw cube form. The finite admission
cutoff and the existing source-tail and pairing moduli justify passage to
the same completed objects. At the fixed anchor this yields the two-sided
64/65-to-1 comparison with the raw reflected squared norm on every finite
signed span, not a marginal-norm comparison or a strict spectral gap.

The image's E completion and its inverse raw comparison are subsequently
constructed at the fixed anchor in `BF4PhysicalCubeReflectedCompletion`.
Descending/intertwining the actual transfer on that completion, geometric
time, uniform strict gap and continuum remain open.
-/

import YMGap.Continuum.BF4PhysicalCubeObservableRealization
import YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
import YMGap.Continuum.RCDistBridge

namespace YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Concrete finite-span map into the actual completed physical carrier. -/
def cubeToCompleted (terms : CubeSpan) : CentralPhysicalCutoffLinearCompletion hw0 hw1 0 :=
  embedCentralPhysicalLinearObservable hw0 hw1 0 (cubeObservable terms)

/-- Explicit representative of the actual completed cross pairing. -/
def cubeTransferPairingLimit (left right : CubeSpan) : CReal :=
  physicalCauchyPairingLimit hw0 hw1 0
    (centralPhysicalLinearMarkovCutoffCauchy
      ((centralPhysicalDenseMarkovCauchyData hw0 hw1 0).modulus (cubeObservable left)))
    ((centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 0).constant (cubeObservable right))

/-- Same physical limit on both sides; the reindex only pays explicit admission. -/
theorem cubeTransferPairingLimit_eq_normalized (left right : CubeSpan) :
    CReal.Equiv (cubeTransferPairingLimit hw0 hw1 left right)
      (normalizedFormLimit hw0 hw1 left right) := by
  let index := fun K => max (realizationCutoff left right) K
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := fun K => CReal.ofQ'
      (centralPhysicalWeightedInner w (Q'.le_of_lt hw0) (index K) 0
        (centralPhysicalMarkovApply w (Q'.le_of_lt hw0) (index K) 0 (cubeObservable left).value)
        (cubeObservable right).value))
    (bSeq := fun K => CReal.ofQ' ((normalizedFormLimit hw0 hw1 left right).approx (index K)))
  · intro K
    apply CReal.ofQ'_equiv_of_eqv
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm
      (centralPhysicalMarkovApply_self_adjoint w (Q'.le_of_lt hw0) (index K) 0 _ _))
      (cubeObservable_form_eq_normalized_approx hw0 hw1 left right (index K) (Nat.le_max_left _ _))
  · exact convergesTo_cofinalReindex
      (centralPhysicalDenseMarkovCrossForm_converges hw0 hw1 0 (cubeObservable left) (cubeObservable right))
      index (fun n => n) (fun n K hK => Nat.le_trans hK (Nat.le_max_right _ _))
  · exact convergesTo_cofinalReindex
      (CReal.convergesTo_self (normalizedFormLimit hw0 hw1 left right))
      index (fun n => n) (fun n K hK => Nat.le_trans hK (Nat.le_max_right _ _))

/-- The all-spin cube form is the SAME completed reflected pairing on its
literal observable image, for arbitrary finite signed lists on both sides. -/
theorem cubeToCompleted_reflected_pairing (left right : CubeSpan) :
    completedReflectedForm hw0 hw1 0
        (cubeToCompleted hw0 hw1 left) (cubeToCompleted hw0 hw1 right) =
      Quotient.mk CReal.crealSetoid (normalizedFormLimit hw0 hw1 left right) := by
  unfold completedReflectedForm
  rw [← concrete_selfAdjoint]
  unfold cubeToCompleted
  rw [centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_embed]
  exact Quotient.sound (cubeTransferPairingLimit_eq_normalized hw0 hw1 left right)

/-- Explicit two-sided norm comparison on the realized image, at w=1/400 and
extent one only. Both norms here are REFLECTED norms. -/
theorem cubeToCompleted_anchor_reflected_norm_bounds (terms : CubeSpan) :
    CReal.RCle
        (Quotient.mk CReal.crealSetoid
          (CReal.ofQ' (Q'.mkPos 64 65 (by decide) * form (kernel anchorCoupling) terms terms)))
        (completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0
          (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) terms)
          (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) terms)) ∧
      CReal.RCle
        (completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0
          (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) terms)
          (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) terms))
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' (form (kernel anchorCoupling) terms terms))) := by
  rw [cubeToCompleted_reflected_pairing]
  constructor
  · apply CReal.leEv_of_le
    apply CReal.ofQ'_le_of_approx_ge
    exact fun K => (normalizedFormLimit_anchor_norm_bounds terms K).1
  · apply CReal.leEv_of_le
    intro K
    exact Q'.le_trans' _ _ _ (normalizedFormLimit_anchor_norm_bounds terms K).2
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos K)))

/-- The dense realization neither creates nor removes zero-norm vectors at
the fixed anchor. This concerns the E radical, not equality in the marginal
completion and not a completed-space equivalence. -/
theorem cubeToCompleted_anchor_reflected_null_iff (terms : CubeSpan) :
    completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0
        (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) terms)
        (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) terms) = CReal.RCzero ↔
      form (kernel anchorCoupling) terms terms ≈ 0 := by
  constructor
  · intro hzero
    have hl := (cubeToCompleted_anchor_reflected_norm_bounds terms).1
    rw [hzero] at hl
    have hf : Q'.mkPos 64 65 (by decide) * form (kernel anchorCoupling) terms terms ≤ 0 :=
      GNSData.RCofQ'_le_reflect hl
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 65 64 (by decide)) hf (by decide)
    have hcancel : Q'.mkPos 65 64 (by decide) *
        (Q'.mkPos 64 65 (by decide) * form (kernel anchorCoupling) terms terms) ≈
        form (kernel anchorCoupling) terms terms :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (by decide : Q'.mkPos 65 64 (by decide) * Q'.mkPos 64 65 (by decide) ≈ 1))
          (Q'.one_mul_eqv _))
    have hle := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.mul_zero_eqv _)))
    exact Int.le_antisymm hle (form_nonnegative (w := anchorCoupling) (by decide) terms)
  · intro hzero
    rw [cubeToCompleted_reflected_pairing]
    apply Quotient.sound
    apply SumOfSquares.Equiv_of_approx_eqv
    intro K
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hzero) (Q'.zero_mul_eqv _)

end YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization

#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization.cubeToCompleted
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization.cubeTransferPairingLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization.cubeTransferPairingLimit_eq_normalized
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization.cubeToCompleted_reflected_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization.cubeToCompleted_anchor_reflected_norm_bounds
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization.cubeToCompleted_anchor_reflected_null_iff
