/-
# Adjacent fundamental plaquettes: conditional shared-link elimination

Only head-coordinate moments are computed. The outer path polynomials remain
symbolic. This is not a full-action comparison or a proof that the output has
an original plaquette-expression/transfer preimage.
-/

import YMGap.Continuum.SU2QuaternionHeadLinearHaar
import YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

namespace YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

local infix:50 " ≈ " => Q'.eqv

private theorem lift_neg (p : RatPoly) : liftHead (polyNeg p) = polyNeg (liftHead p) := by
  simp only [liftHead, polyNeg, List.map_map]
  rfl

private theorem lift_add (p q : RatPoly) :
    liftHead (polyAdd p q) = polyAdd (liftHead p) (liftHead q) := List.map_append

def liftQuaternion (q : PolyQuaternion) : PolyQuaternion :=
  ⟨liftHead q.scalar, liftHead q.iPart, liftHead q.jPart, liftHead q.kPart⟩

theorem lift_mul (p q : PolyQuaternion) :
    liftQuaternion (PolyQuaternion.mul p q) =
      PolyQuaternion.mul (liftQuaternion p) (liftQuaternion q) := by
  simp only [liftQuaternion, PolyQuaternion.mul, lift_add, lift_neg, liftHead_mul]

theorem lift_conj (q : PolyQuaternion) :
    liftQuaternion (PolyQuaternion.conj q) = PolyQuaternion.conj (liftQuaternion q) := by
  simp only [liftQuaternion, PolyQuaternion.conj, lift_neg]

private def components (q : PolyQuaternion) (i : Fin 4) : RatPoly :=
  match i.val with | 0 => q.scalar | 1 => q.iPart | 2 => q.jPart | _ => q.kPart

private def signedComponents (q : PolyQuaternion) (i : Fin 4) : RatPoly :=
  if i.val = 0 then q.scalar else polyNeg (components q i)

private theorem linear_slim (p : Fin 4 → RatPoly) :
    RatPolyCoeffEqv (linear (four p)) (polyAdd (atom 0 (p 0))
      (polyAdd (atom 1 (p 1)) (polyAdd (atom 2 (p 2)) (atom 3 (p 3))))) :=
  (RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)))

private def environment (q : PolyQuaternion) (i : Nat) : RatPoly :=
  match i with
  | 0 => liftHead q.scalar | 1 => liftHead q.iPart
  | 2 => liftHead q.jPart | 3 => liftHead q.kPart
  | 4 => polyVar 0 | 5 => polyVar 1 | 6 => polyVar 2 | _ => polyVar 3

private theorem left_linear (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (PolyQuaternion.mul (liftQuaternion q) (PolyQuaternion.coordinateVariable 0)).scalar
      (linear (four (signedComponents q))) := by
  refine RatPolyCoeffEqv.trans ?_ (linear_slim (signedComponents q)).symm
  simpa only [atom, signedComponents, components, Fin.reduceFinMk,
    Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceEqDiff, ↓reduceIte,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
    PolyQuaternion.mul, PolyQuaternion.coordinateVariable, liftQuaternion,
    lift_neg, environment, coeffEvalExpr] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 4)) (.neg (.add (.mul (.var 1) (.var 5))
        (.add (.mul (.var 2) (.var 6)) (.mul (.var 3) (.var 7))))))
      (.add (.mul (.var 4) (.var 0)) (.add (.mul (.var 5) (.neg (.var 1)))
        (.add (.mul (.var 6) (.neg (.var 2))) (.mul (.var 7) (.neg (.var 3))))))
      (by decide) (environment q))

private theorem right_linear (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (PolyQuaternion.mul (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0))
        (liftQuaternion q)).scalar
      (linear (four (components q))) := by
  refine RatPolyCoeffEqv.trans ?_ (linear_slim (components q)).symm
  simpa only [atom, components, Fin.reduceFinMk,
    PolyQuaternion.mul, PolyQuaternion.conj, PolyQuaternion.coordinateVariable,
    liftQuaternion, environment, coeffEvalExpr] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 4) (.var 0)) (.neg (.add (.mul (.neg (.var 5)) (.var 1))
        (.add (.mul (.neg (.var 6)) (.var 2)) (.mul (.neg (.var 7)) (.var 3))))))
      (.add (.mul (.var 4) (.var 0)) (.add (.mul (.var 5) (.var 1))
        (.add (.mul (.var 6) (.var 2)) (.mul (.var 7) (.var 3)))))
      (by decide) (environment q))

theorem scalar_schur (p q : PolyQuaternion) :
    RatPolyCoeffEqv (partialHaarHead (polyMul
      (PolyQuaternion.mul (liftQuaternion p) (PolyQuaternion.coordinateVariable 0)).scalar
      (PolyQuaternion.mul (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0))
        (liftQuaternion q)).scalar))
      (polySmul quarter (PolyQuaternion.mul p q).scalar) := by
  refine (partialHaarHead_congr ((left_linear p).mul (right_linear q))).trans
    ((four_pair (signedComponents p) (components q)).trans ?_)
  apply RatPolyCoeffEqv.smul
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 4)) (.add (.mul (.neg (.var 1)) (.var 5))
      (.add (.mul (.neg (.var 2)) (.var 6)) (.mul (.neg (.var 3)) (.var 7)))))
    (.add (.mul (.var 0) (.var 4)) (.neg (.add (.mul (.var 1) (.var 5))
      (.add (.mul (.var 2) (.var 6)) (.mul (.var 3) (.var 7))))))
    (by decide) (fun i => match i with
      | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
      | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart)

theorem partial_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polySmul c p)) (polySmul c (partialHaarHead p)) := by
  have h : RatPolyTermwiseEqv (partialHaarHead (polySmul c p))
      (polySmul c (partialHaarHead p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl, Q'.mul_assoc_eqv _ _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight h

def schurFactor : Q' := Q'.mkPos 1 2 (by decide)

/-- Conditional fundamental Schur identity with arbitrary retained path
polynomials. They need not use disjoint outer variables or be unit quaternions. -/
theorem path_schur (p q : PolyQuaternion) :
    RatPolyCoeffEqv (partialHaarHead (polyMul
      (characterPolynomial (PolyQuaternion.mul (liftQuaternion p)
        (PolyQuaternion.coordinateVariable 0)).scalar 1)
      (characterPolynomial (PolyQuaternion.mul
        (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0)) (liftQuaternion q)).scalar 1)))
      (polySmul schurFactor (characterPolynomial (PolyQuaternion.mul p q).scalar 1)) := by
  have hscale (a b : RatPoly) : RatPolyCoeffEqv
      (polyMul (polySmul 2 a) (polySmul 2 b)) (polySmul 4 (polyMul a b)) :=
    (RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul 2).trans (twice_twice_smul _))
  refine (partialHaarHead_congr (hscale _ _)).trans
    ((partial_smul _ _).trans (((scalar_schur p q).smul 4).trans ?_))
  exact (RatPolyCoeffEqv.smul_assoc _ _ _).trans
    ((RatPolyCoeffEqv.smul_coefficient (by decide : 4*quarter ≈ schurFactor*2) _).trans
      (RatPolyCoeffEqv.smul_assoc _ _ _).symm)

local infixl:70 " ⋄ " => PolyQuaternion.mul

private theorem first_cycle (a s c d : PolyQuaternion) :
    RatPolyCoeffEqv (((a ⋄ s) ⋄ c) ⋄ d).scalar (((c ⋄ d) ⋄ a) ⋄ s).scalar :=
  (PolyQuaternionCoeffEqv.mul_assoc (a ⋄ s) c d).scalar.trans
    ((polyQuaternion_mul_scalar_cyclic (a ⋄ s) (c ⋄ d)).trans
      (PolyQuaternionCoeffEqv.mul_assoc (c ⋄ d) a s).scalar.symm)

private theorem outer_cycle (a b e f c d : PolyQuaternion) :
    RatPolyCoeffEqv (((c ⋄ d) ⋄ a) ⋄ ((b ⋄ e) ⋄ f)).scalar
      (((((a ⋄ b) ⋄ e) ⋄ f) ⋄ c) ⋄ d).scalar := by
  have h := (PolyQuaternionCoeffEqv.mul_assoc a (b ⋄ e) f).symm.trans
    ((PolyQuaternionCoeffEqv.mul_assoc a b e).symm.mul (PolyQuaternionCoeffEqv.refl f))
  exact (PolyQuaternionCoeffEqv.mul_assoc (c ⋄ d) a ((b ⋄ e) ⋄ f)).scalar.trans
    ((polyQuaternion_mul_scalar_cyclic (c ⋄ d) (a ⋄ ((b ⋄ e) ⋄ f))).trans
      ((h.mul (PolyQuaternionCoeffEqv.refl (c ⋄ d))).scalar.trans
        (PolyQuaternionCoeffEqv.mul_assoc (((a ⋄ b) ⋄ e) ⋄ f) c d).scalar.symm))

private def leftPath : PolyQuaternion :=
  (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4) ⋄
    PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5)) ⋄
    PolyQuaternion.coordinateVariable 0

private def rightPath : PolyQuaternion :=
  (PolyQuaternion.coordinateVariable 1 ⋄ PolyQuaternion.coordinateVariable 2) ⋄
    PolyQuaternion.conj (PolyQuaternion.coordinateVariable 3)

/-- Block zero is the SAME shared link with opposite incidences. -/
def adjacentProduct : RatPoly := polyMul (plaquette 1 0 5 6) (plaquette 2 3 4 0)

/-- Six outer links are numbered 0..5 AFTER eliminating the shared block. -/
def rectangle : RatPoly := characterPolynomial
  (((((PolyQuaternion.coordinateVariable 0 ⋄ PolyQuaternion.coordinateVariable 1) ⋄
    PolyQuaternion.coordinateVariable 2) ⋄ PolyQuaternion.conj (PolyQuaternion.coordinateVariable 3)) ⋄
      PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4)) ⋄
        PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5)).scalar 1

/-- Coefficient-sensitive equality before any outer variable is integrated:
integral_s chi(a s c^-1 d^-1) chi(b e f^-1 s^-1)
= (1/2) chi(a b e f^-1 c^-1 d^-1). -/
theorem shared_link_contraction :
    RatPolyCoeffEqv (partialHaarHead adjacentProduct) (polySmul schurFactor rectangle) := by
  have hl : liftQuaternion leftPath =
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5) ⋄
        PolyQuaternion.conj (PolyQuaternion.coordinateVariable 6)) ⋄
          PolyQuaternion.coordinateVariable 1 := by
    unfold leftPath
    rw [lift_mul, lift_mul, lift_conj, lift_conj]
    rfl
  have hr : liftQuaternion rightPath =
      (PolyQuaternion.coordinateVariable 2 ⋄ PolyQuaternion.coordinateVariable 3) ⋄
        PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4) := by
    unfold rightPath
    rw [lift_mul, lift_mul, lift_conj]
    rfl
  have hs := path_schur leftPath rightPath
  rw [hl,hr] at hs
  have hfirst := (first_cycle (PolyQuaternion.coordinateVariable 1)
    (PolyQuaternion.coordinateVariable 0) (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 6))).smul 2
  have hsecond := (polyQuaternion_mul_scalar_cyclic
    ((PolyQuaternion.coordinateVariable 2 ⋄ PolyQuaternion.coordinateVariable 3) ⋄
      PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4))
        (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 0))).smul 2
  have hout := ((outer_cycle (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.coordinateVariable 1) (PolyQuaternion.coordinateVariable 2)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 3))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 4))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 5))).smul 2).smul schurFactor
  exact (partialHaarHead_congr (hfirst.mul hsecond)).trans (hs.trans hout)

private theorem haar_coeff {p q : RatPoly} (h : RatPolyCoeffEqv p q) (blocks : Nat) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  have pin : ∀ r : RatPoly, quaternionHaar blocks r = ratWeightedSum (quaternionHaarMono blocks) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih => simp only [quaternionHaar, ratWeightedSum, ih]
  rw [pin,pin]
  exact h _

/-- All outer/spectator coordinates and their polynomial dependence are
retained. The boundary factor must not depend on the eliminated shared link. -/
theorem adjacent_boundary_haar (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks+1) (polyMul adjacentProduct (liftHead boundary)) ≈
      schurFactor * quaternionHaar blocks (polyMul rectangle boundary) := by
  have hf := quaternionHaar_polyMul_headIndependent blocks adjacentProduct (liftHead boundary)
    (headIndependentCheck_sound (liftHead_independent boundary))
  rw [drop_liftHead] at hf
  exact Q'.eqv_trans _ _ _ hf (Q'.eqv_trans _ _ _
    (haar_coeff ((shared_link_contraction.mul_right boundary).trans
      (RatPolyCoeffEqv.polyMul_smul_left _ _ _)) blocks) (quaternionHaar_polySmul _ _ _))

/-- Product of the two original fundamental heat coefficients and the Haar
factor. This is one selected term, not the whole heat-weight product. -/
def selectedHeatFactor (w : Q') : Q' :=
  BondMovingStep.coeffW w 1 * BondMovingStep.coeffW w 1 * schurFactor

theorem selectedHeatFactor_pin (w : Q') : selectedHeatFactor w ≈ 2*qpow w 6 := by
  have h : selectedHeatFactor w ≈ (4*schurFactor)*qpow w 6 := poly_identity_of_normal_eq
    (.mul (.mul (.mul (.const 2) (.pow (.var 0) 3))
      (.mul (.const 2) (.pow (.var 0) 3))) (.var 1))
    (.mul (.mul (.const 4) (.var 1)) (.pow (.var 0) 6))
    (by decide) (fun i => if i = 0 then w else schurFactor)
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ _
    (by decide : 4*schurFactor ≈ (2 : Q')))

end YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing

#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.liftQuaternion
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.lift_mul
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.lift_conj
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.scalar_schur
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.partial_smul
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.schurFactor
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.path_schur
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.adjacentProduct
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.rectangle
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.shared_link_contraction
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.adjacent_boundary_haar
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.selectedHeatFactor
#print axioms YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing.selectedHeatFactor_pin
