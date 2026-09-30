/-
# Conjugation commutes with every distinct block integration

Quaternion conjugation in the multiplier coordinates is an involution on
the existing polynomial carrier. It preserves arbitrary-insertion Haar
equality, and commutes coefficientwise with integration in another block.
These identities supply the inverse-orientation conditional gauge steps;
no smallness or completed invariant-sector assertion is made.
-/

import YMGap.Continuum.SU2QuaternionSelectedConditionalTranslation

namespace YMGap.Continuum.SU2QuaternionConjugationProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation "C" => conjugateQuaternionBlockPolynomial

private theorem conjugate_twice_terms (blocks block : Nat) :
    ∀ p : RatPoly, RatPolyTermwiseEqv (C blocks block (C blocks block p)) p
  | [] => True.intro
  | t :: p => by
      refine ⟨rfl, ?_, conjugate_twice_terms blocks block p⟩
      change (if selectedExponentParity (4*blocks)
          (quaternionConjugateCoordinateSelector block) t.1 then
          -(if selectedExponentParity (4*blocks)
            (quaternionConjugateCoordinateSelector block) t.1 then -t.2 else t.2)
          else (if selectedExponentParity (4*blocks)
            (quaternionConjugateCoordinateSelector block) t.1 then -t.2 else t.2)) ≈ t.2
      cases selectedExponentParity (4*blocks) (quaternionConjugateCoordinateSelector block) t.1
      · exact Q'.eqv_refl _
      · exact Q'.neg_neg_eqv _

theorem conjugate_involutive (blocks block : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (C blocks block (C blocks block p)) p :=
  fun weight => ratWeightedSum_termwise_eqv weight (conjugate_twice_terms blocks block p)

/-- Move conjugation to the test; no independence or support is dropped. -/
theorem conjugate_pairing (blocks block : Nat) (r p : RatPoly) :
    quaternionHaar blocks (polyMul r (C blocks block p)) ≈
      quaternionHaar blocks (polyMul (C blocks block r) p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (quaternionHaar_conjugateQuaternionBlock blocks block (polyMul r (C blocks block p))))
    (haar_of_coeff ((conjugateQuaternionBlockPolynomial_mul blocks block r
      (C blocks block p)).trans ((conjugate_involutive blocks block p).mul_left _)))

theorem conjugate_carrier {blocks block : Nat} {p q : RatPoly}
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (C blocks block p) (C blocks block q) := by
  intro r
  exact Q'.eqv_trans _ _ _ (conjugate_pairing blocks block r p)
    (Q'.eqv_trans _ _ _ (h (C blocks block r))
      (Q'.eqv_symm (conjugate_pairing blocks block r q)))

private theorem parity_clear (blocks selected block : Nat) (hne : selected ≠ block)
    (m : List Nat) :
    selectedExponentParity (4*blocks) (quaternionConjugateCoordinateSelector selected)
      (clearQuaternionBlock block m) =
    selectedExponentParity (4*blocks) (quaternionConjugateCoordinateSelector selected) m := by
  unfold selectedExponentParity
  congr 1
  funext parity coordinate
  by_cases hs : quaternionConjugateCoordinateSelector selected coordinate = true
  · simp only [hs, if_true]
    have hc : coordinate = 4*selected+1 ∨ coordinate = 4*selected+2 ∨
        coordinate = 4*selected+3 := of_decide_eq_true hs
    rcases hc with hc | hc | hc
    · rw [hc, exponentAt_clearQuaternionBlock_of_ne m hne (by decide : 1 < 4)]
    · rw [hc, exponentAt_clearQuaternionBlock_of_ne m hne (by decide : 2 < 4)]
    · rw [hc, exponentAt_clearQuaternionBlock_of_ne m hne (by decide : 3 < 4)]
  · simp [hs]

private theorem project_conjugate_terms (blocks selected block : Nat)
    (hne : selected ≠ block) : ∀ p : RatPoly,
    RatPolyTermwiseEqv (project block (C blocks selected p))
      (C blocks selected (project block p))
  | [] => True.intro
  | t :: p => by
      refine ⟨rfl, ?_, project_conjugate_terms blocks selected block hne p⟩
      change ((if selectedExponentParity (4*blocks)
        (quaternionConjugateCoordinateSelector selected) t.1 then -t.2 else t.2) *
          quaternionBlockMoment t.1 block) ≈
        (if selectedExponentParity (4*blocks) (quaternionConjugateCoordinateSelector selected)
          (clearQuaternionBlock block t.1) then -(t.2 * quaternionBlockMoment t.1 block)
          else t.2 * quaternionBlockMoment t.1 block)
      rw [parity_clear blocks selected block hne t.1]
      cases selectedExponentParity (4*blocks) (quaternionConjugateCoordinateSelector selected) t.1
      · exact Q'.eqv_refl _
      · exact Q'.neg_mul_eqv _ _

/-- Integration in a distinct coordinate block commutes coefficientwise. -/
theorem project_conjugate (blocks selected block : Nat) (hne : selected ≠ block)
    (p : RatPoly) : RatPolyCoeffEqv (project block (C blocks selected p))
      (C blocks selected (project block p)) :=
  fun weight => ratWeightedSum_termwise_eqv weight
    (project_conjugate_terms blocks selected block hne p)

#print axioms conjugate_involutive
#print axioms conjugate_pairing
#print axioms conjugate_carrier
#print axioms project_conjugate

end YMGap.Continuum.SU2QuaternionConjugationProjection
