/-
# A common dense form bound extends over the entire reflected complement

The centered physical presentations already approximate every represented
vacuum-orthogonal vector. Their explicit error rates, the actual nonexpansive
transfer, and joint pairing continuity now pass any ONE rational form bound
to every point of the completed reflected vacuum complement, with NO rate
loss and NO choice of quotient representatives.

The dense bound is an explicit input, not supplied here. In particular this
does not construct q<1, a uniform gap, geometric time, or continuum QFT.
Scope of the physical objects is fixed w=1/400, extent one.
-/

import YMGap.Continuum.BF4PhysicalCubeDissipation
import YMGap.Continuum.GNSRepresentedApproximation

namespace YMGap.Continuum.BF4PhysicalCubeDenseFormClosure

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeCenteredDensity
open YMGap.Continuum.BF4PhysicalCubeDissipation
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local notation "lambda" => Quotient.mk CReal.crealSetoid anchorNormalization.value
local notation "floor" => anchorNormalization.floor
local notation "rawClass" => GNSRepresentedApproximation.classOf D
local notation "rawError" => GNSRepresentedApproximation.errorSq D

private theorem normalization_cancel (a b : RC)
    (h : RCle (RCmul a lambda) (RCmul b lambda)) : RCle a b := by
  refine Quotient.inductionOn₂ a b ?_ h
  intro A B hab
  exact RCBilinearDifference.cancel_positive_factor floor anchorNormalization.floor_pos
    anchorNormalization.lower hab

/-- The actual normalization floor converts a reflected error budget to a
raw error budget. This is not an unproved equivalence of completions. -/
theorem raw_error_bound (x y : CubeReflectedCompletion) (epsilon : Q')
    (h : RCle (BF4PhysicalCubeCenteredDensity.errorSq x y) (Rq (floor * epsilon))) :
    RCle ((D).cinnerCompl ((D).cSub (reflectedToRaw x) (reflectedToRaw y))
      ((D).cSub (reflectedToRaw x) (reflectedToRaw y))) (Rq epsilon) := by
  let a := (D).cinnerCompl ((D).cSub (reflectedToRaw x) (reflectedToRaw y))
    ((D).cSub (reflectedToRaw x) (reflectedToRaw y))
  have hf : RCle (Rq floor) lambda := CReal.leEv_ofQ'_of_approx_ge anchorNormalization.lower
  have hlow := mul_mono_left ((D).cinner_self_nonneg ((D).cSub (reflectedToRaw x) (reflectedToRaw y))) hf
  unfold BF4PhysicalCubeCenteredDensity.errorSq cubeReflectedSub at h
  rw [cubeReflectedInner_comparison] at h
  have hscaled : RCle (RCmul a (Rq floor)) (Rq (floor * epsilon)) := RCle_trans hlow h
  apply cancel_q floor anchorNormalization.floor_pos
  rw [rq_mul, rq_eqv (Q'.mul_comm_eqv epsilon floor)]
  exact hscaled

def rawApproximant (X : CauchyGNS D) (n : Nat) : CauchyGNS D :=
  toRawCauchy D anchorNormalization (approximationRepresentative X n)

theorem rawApproximant_reflected (X : CauchyGNS D) (n : Nat) :
    rawToReflected (rawClass (rawApproximant X n)) = (approximationVector X n).val := by
  change rawToReflected (reflectedToRaw
    (Quotient.mk cubeReflectedSeminorm.completionSetoid (approximationRepresentative X n))) = _
  rw [reflected_raw_inverse, approximationRepresentative_realizes]

/-- Explicit raw approximation rate, including the exact normalization cost. -/
def rawApproximationRate (X : CauchyGNS D) (epsilon : Q') : Nat :=
  approximationRate X (floor * epsilon)

theorem raw_approximation_bound (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (rawClass X) = x.val)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : rawApproximationRate X epsilon ≤ n) :
    RCle (rawError (rawApproximant X n) X) (Rq epsilon) := by
  have h := raw_error_bound (approximationVector X n).val x.val epsilon
    (approximation_bound x X hX (floor * epsilon)
      (Q'.mul_pos anchorNormalization.floor_pos hepsilon) n hn)
  rw [← rawApproximant_reflected, ← hX, raw_reflected_inverse, raw_reflected_inverse] at h
  exact h

theorem raw_action_approximation_bound (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (rawClass X) = x.val)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : rawApproximationRate X epsilon ≤ n) :
    RCle (rawError (denseTransferData.mapRep (rawApproximant X n)) (denseTransferData.mapRep X))
      (Rq epsilon) :=
  RCle_trans (cubeRawTransfer_nonexpansive (rawClass (rawApproximant X n)) (rawClass X))
    (raw_approximation_bound x X hX epsilon hepsilon n hn)

theorem raw_norm_converges (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (rawClass X) = x.val) :
    CReal.ConvergesTo (fun n => (D).cinnerRep (rawApproximant X n) (rawApproximant X n))
      ((D).cinnerRep X X) :=
  GNSRepresentedApproximation.pairing_converges_to D X (rawApproximant X) (rawApproximationRate X)
    (raw_approximation_bound x X hX) X (rawApproximant X) (rawApproximationRate X)
    (raw_approximation_bound x X hX)

theorem raw_transfer_pairing_converges (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (rawClass X) = x.val) :
    CReal.ConvergesTo
      (fun n => (D).cinnerRep (denseTransferData.mapRep (rawApproximant X n)) (rawApproximant X n))
      ((D).cinnerRep (denseTransferData.mapRep X) X) :=
  GNSRepresentedApproximation.pairing_converges_to D (denseTransferData.mapRep X)
    (fun n => denseTransferData.mapRep (rawApproximant X n)) (rawApproximationRate X)
    (raw_action_approximation_bound x X hX) X (rawApproximant X) (rawApproximationRate X)
    (raw_approximation_bound x X hX)

private theorem raw_form_bound (q : Q') (x : GNSCompletionSpace D)
    (h : RCle (B (T (rawToReflected x)) (rawToReflected x))
      (RCmul (Rq q) (B (rawToReflected x) (rawToReflected x)))) :
    RCle ((D).cinnerCompl (cubeRawTransfer x) x) (RCmul (Rq q) ((D).cinnerCompl x x)) := by
  rw [cubeTransfer_rawComparison, cubeReflectedInner_comparison, cubeReflectedInner_comparison,
    ← BF4PhysicalCubeDissipation.mul_assoc] at h
  exact normalization_cancel _ _ h

/-- The ONLY analytic premise is the common bound on the original centered
physical presentations. The target may be anywhere in the reflected complement. -/
theorem represented_form_bound (q : Q')
    (dense_bound : ∀ p : SectorPresentation,
      let y := (centeredCubeVector p.base p.coefficient).val
      RCle (B (T y) y) (RCmul (Rq q) (B y y)))
    (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (rawClass X) = x.val) :
    RCle (B (T x.val) x.val) (RCmul (Rq q) (B x.val x.val)) := by
  have hstage (n : Nat) :
      CReal.leEv ((D).cinnerRep (denseTransferData.mapRep (rawApproximant X n)) (rawApproximant X n))
        (CReal.mul (CReal.ofQ' q) ((D).cinnerRep (rawApproximant X n) (rawApproximant X n))) := by
    apply raw_form_bound q (rawClass (rawApproximant X n))
    rw [rawApproximant_reflected]
    exact dense_bound (approximationPresentation X n)
  have hraw := CReal.leEv_of_convergesTo_le (raw_transfer_pairing_converges x X hX)
    (CReal.convergesTo_const_mul (CReal.ofQ' q) (raw_norm_converges x X hX)) hstage
  change RCle ((D).cinnerCompl (cubeRawTransfer (rawClass X)) (rawClass X))
    (RCmul (Rq q) ((D).cinnerCompl (rawClass X) (rawClass X))) at hraw
  have hscaled := mul_mono_right (normalization_nonnegative anchorNormalization) hraw
  rw [← hX, cubeTransfer_rawComparison, cubeReflectedInner_comparison, cubeReflectedInner_comparison]
  exact Eq.mp (congrArg (fun z => RCle _ z)
    (BF4PhysicalCubeDissipation.mul_assoc (Rq q) ((D).cinnerCompl (rawClass X) (rawClass X)) lambda)) hscaled

/-- No supplied-representative restriction in the RESULT: quotient induction
is used only to prove this proposition, never to choose representative data. -/
theorem completed_form_bound_of_dense (q : Q')
    (dense_bound : ∀ p : SectorPresentation,
      let y := (centeredCubeVector p.base p.coefficient).val
      RCle (B (T y) y) (RCmul (Rq q) (B y y)))
    (x : CubeSectorVacuumComplement) :
    RCle (B (T x.val) x.val) (RCmul (Rq q) (B x.val x.val)) := by
  rcases x with ⟨x, hx⟩
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  exact represented_form_bound q dense_bound ⟨Quotient.mk _ X, hx⟩
    (toRawCauchy D anchorNormalization X) (reflected_raw_inverse (Quotient.mk _ X))

/-- Exact equivalence, at the SAME rate, not a new gap certificate. -/
theorem dense_form_bound_iff_completed (q : Q') :
    (∀ p : SectorPresentation,
      let y := (centeredCubeVector p.base p.coefficient).val
      RCle (B (T y) y) (RCmul (Rq q) (B y y))) ↔
    (∀ x : CubeSectorVacuumComplement, RCle (B (T x.val) x.val) (RCmul (Rq q) (B x.val x.val))) :=
  ⟨fun h x => completed_form_bound_of_dense q h x,
    fun h p => h (centeredCubeVector p.base p.coefficient)⟩

end YMGap.Continuum.BF4PhysicalCubeDenseFormClosure

#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.raw_error_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.rawApproximant
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.rawApproximant_reflected
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.rawApproximationRate
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.raw_approximation_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.raw_action_approximation_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.raw_norm_converges
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.raw_transfer_pairing_converges
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.represented_form_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.completed_form_bound_of_dense
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseFormClosure.dense_form_bound_iff_completed
