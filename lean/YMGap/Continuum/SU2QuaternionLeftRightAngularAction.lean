/-
# Actual left/right angular action on original quaternion coordinates

The existing pairedDerivativeAt is LEFT multiplication by an imaginary
quaternion. The complementary signed pairs below give RIGHT multiplication,
with no factor one-half. Common-padded coefficient equality retains the
literal formal derivatives and their zero exponent padding. No sphere or
unit-quaternion equation is used. Reverse orientation follows actual
componentwise conjugation, not an assumed endpoint tangent rule.

The next consumer is the finite original physical-link vertex-Gauss sum.
This file does not construct that sum, its closed-word telescope, a
continuum generator/domain, or a signed-response/physical-gap estimate.
-/

import YMGap.Continuum.SU2QuaternionAngularCoordinatePadded
import YMGap.Continuum.SU2QuaternionPairedFrameAt

namespace YMGap.Continuum.SU2QuaternionLeftRightAngularAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularCoordinatePadded
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.QuaternionHaarAngularCarrier

/-- Opposite complementary-plane signs give actual right multiplication. -/
def rightDerivativeAt (block : Nat) (i : Fin 3) (p : RatPoly) : RatPoly :=
  match i.val with
  | 0 => polyAdd (blockAngularDerivative block 0 1 p)
      (polyNeg (blockAngularDerivative block 2 3 p))
  | 1 => polyAdd (blockAngularDerivative block 0 2 p) (blockAngularDerivative block 1 3 p)
  | _ => polyAdd (blockAngularDerivative block 0 3 p)
      (polyNeg (blockAngularDerivative block 1 2 p))

/-- False is the EXISTING left frame; true is the literal right frame. -/
def frameDerivativeAt (right : Bool) (block : Nat) (i : Fin 3) (p : RatPoly) : RatPoly :=
  if right then rightDerivativeAt block i p else pairedDerivativeAt block i p

/-- Apply the actual scalar derivation to all four original components. -/
def quaternionAction (right : Bool) (block : Nat) (i : Fin 3) (q : PolyQuaternion) : PolyQuaternion :=
  ⟨frameDerivativeAt right block i q.scalar, frameDerivativeAt right block i q.iPart,
    frameDerivativeAt right block i q.jPart, frameDerivativeAt right block i q.kPart⟩

def negQuaternion (q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyNeg q.scalar, polyNeg q.iPart, polyNeg q.jPart, polyNeg q.kPart⟩

def zeroQuaternion : PolyQuaternion := ⟨polyZero,polyZero,polyZero,polyZero⟩

private def basisExpr (i : Fin 3) : PolyQuaternionExpr :=
  ⟨.const 0, .const (if i.val=0 then 1 else 0),
    .const (if i.val=1 then 1 else 0), .const (if i.val=2 then 1 else 0)⟩

private def evalQuaternion (env : Nat → RatPoly) (e : PolyQuaternionExpr) : PolyQuaternion :=
  ⟨coeffEvalExpr env e.scalar, coeffEvalExpr env e.iPart,
    coeffEvalExpr env e.jPart, coeffEvalExpr env e.kPart⟩

/-- The three literal constant imaginary basis quaternions, with exact
rational zero/one coefficients; no auxiliary coordinate or unit hypothesis. -/
def imaginaryBasis (i : Fin 3) : PolyQuaternion :=
  evalQuaternion (fun _ => polyZero) (basisExpr i)

private def coordinateEnv (b : Nat) (k : Nat) : RatPoly := polyVar (4*b+k)
private def componentExpr (q : PolyQuaternionExpr) (c : Fin 4) : PolyExpr :=
  match c.val with
  | 0 => q.scalar
  | 1 => q.iPart
  | 2 => q.jPart
  | _ => q.kPart

private def planeExpr (a d c : Nat) : PolyExpr :=
  .add (if c=d then .var a else .const 0) (.neg (if c=a then .var d else .const 0))

private def frameExpr (right : Bool) (i : Fin 3) (c : Fin 4) : PolyExpr :=
  match i.val with
  | 0 => .add (planeExpr 0 1 c.val)
      (if right then .neg (planeExpr 2 3 c.val) else planeExpr 2 3 c.val)
  | 1 => .add (planeExpr 0 2 c.val)
      (if right then planeExpr 1 3 c.val else .neg (planeExpr 1 3 c.val))
  | _ => .add (planeExpr 0 3 c.val)
      (if right then .neg (planeExpr 1 2 c.val) else planeExpr 1 2 c.val)

private def productExpr (right : Bool) (i : Fin 3) : PolyQuaternionExpr :=
  if right then PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (basisExpr i)
  else PolyQuaternionExpr.mul (basisExpr i) (PolyQuaternionExpr.coordinate 0)

private theorem directions (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem components (c : Fin 4) : c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by
  simp only [Fin.ext_iff]
  omega

private theorem padded_neg {B : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv B p q) :
    PaddedPolynomialCoeffEqv B (polyNeg p) (polyNeg q) :=
  (PaddedPolynomialCoeffEqv.of_coeff (neg_smul p)).trans
    ((h.smul (-1)).trans (PaddedPolynomialCoeffEqv.of_coeff (neg_smul q).symm))

private theorem zero_constant (B : Nat) (env : Nat → RatPoly) :
    PaddedPolynomialCoeffEqv B polyZero (coeffEvalExpr env (.const 0)) := by
  change PaddedPolynomialCoeffEqv B polyZero (polySmul (Q'.ofInt 0) polyOne)
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.zero_smul polyOne).symm

private theorem branch_pin (B b a c d : Nat) :
    PaddedPolynomialCoeffEqv B (if c=d then coordinateEnv b a else polyZero)
      (coeffEvalExpr (coordinateEnv b) (if c=d then .var a else .const 0)) := by
  by_cases h : c=d
  · simp only [h, if_pos, coeffEvalExpr]; exact .refl _ _
  · simp only [h]; exact zero_constant _ _

private theorem plane_pin {B b : Nat} (hb : b<B) (a d c : Fin 4) :
    PaddedPolynomialCoeffEqv B (blockAngularDerivative b a.val d.val (coordinateEnv b c.val))
      (coeffEvalExpr (coordinateEnv b) (planeExpr a.val d.val c.val)) := by
  have h := angularDerivative_polyVar_padded (B := B)
    (a := 4*b+a.val) (b := 4*b+d.val) (c := 4*b+c.val)
    (by have := a.isLt; omega) (by have := d.isLt; omega) (by have := c.isLt; omega)
  have hcd : (4*b+c.val=4*b+d.val) ↔ c.val=d.val := by
    constructor <;> intro he <;> omega
  have hca : (4*b+c.val=4*b+a.val) ↔ c.val=a.val := by
    constructor <;> intro he <;> omega
  simp only [hcd, hca] at h
  exact h.trans ((branch_pin B b a.val c.val d.val).add
    (padded_neg (branch_pin B b d.val c.val a.val)))

private theorem frame_pin {B b : Nat} (right : Bool) (hb : b<B) (i : Fin 3) (c : Fin 4) :
    PaddedPolynomialCoeffEqv B (frameDerivativeAt right b i (coordinateEnv b c.val))
      (coeffEvalExpr (coordinateEnv b) (frameExpr right i c)) := by
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact (plane_pin hb 0 1 c).add (plane_pin hb 2 3 c)
    · exact (plane_pin hb 0 1 c).add (padded_neg (plane_pin hb 2 3 c))
  · cases right
    · exact (plane_pin hb 0 2 c).add (padded_neg (plane_pin hb 1 3 c))
    · exact (plane_pin hb 0 2 c).add (plane_pin hb 1 3 c)
  · cases right
    · exact (plane_pin hb 0 3 c).add (plane_pin hb 1 2 c)
    · exact (plane_pin hb 0 3 c).add (padded_neg (plane_pin hb 1 2 c))

private theorem matrix_pin (right : Bool) (i : Fin 3) (c : Fin 4) :
    normalize (frameExpr right i c) = normalize (componentExpr (productExpr right i) c) := by
  rcases directions i with rfl | rfl | rfl <;>
    rcases components c with rfl | rfl | rfl | rfl <;> cases right <;> decide

private theorem component_pin {B b : Nat} (right : Bool) (hb : b<B) (i : Fin 3) (c : Fin 4) :
    PaddedPolynomialCoeffEqv B (frameDerivativeAt right b i (coordinateEnv b c.val))
      (coeffEvalExpr (coordinateEnv b) (componentExpr (productExpr right i) c)) :=
  (frame_pin right hb i c).trans (PaddedPolynomialCoeffEqv.of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq _ _ (matrix_pin right i c) (coordinateEnv b)))

/-- Actual LEFT e_i*q and RIGHT q*e_i action on the declared original block. -/
theorem coordinate_action {B b : Nat} (right : Bool) (hb : b<B) (i : Fin 3) :
    PaddedQuaternionCoeffEqv B (quaternionAction right b i (PolyQuaternion.coordinateVariable b))
      (if right then PolyQuaternion.mul (PolyQuaternion.coordinateVariable b) (imaginaryBasis i)
       else PolyQuaternion.mul (imaginaryBasis i) (PolyQuaternion.coordinateVariable b)) := by
  cases right
  · exact ⟨component_pin false hb i 0, component_pin false hb i 1,
      component_pin false hb i 2, component_pin false hb i 3⟩
  · exact ⟨component_pin true hb i 0, component_pin true hb i 1,
      component_pin true hb i 2, component_pin true hb i 3⟩

private theorem plus_neg (p q : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyNeg p) (polyNeg q)) (polyNeg (polyAdd p q)) :=
  coeffEvalExpr_eqv_of_normalize_eq (.add (.neg (.var 0)) (.neg (.var 1)))
    (.neg (.add (.var 0) (.var 1))) (by decide) (fun | 0 => p | _ => q)

private theorem minus_neg (p q : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyNeg p) (polyNeg (polyNeg q)))
      (polyNeg (polyAdd p (polyNeg q))) :=
  coeffEvalExpr_eqv_of_normalize_eq (.add (.neg (.var 0)) (.neg (.neg (.var 1))))
    (.neg (.add (.var 0) (.neg (.var 1)))) (by decide) (fun | 0 => p | _ => q)

private def signedPair (minus : Bool) (p q : RatPoly) : RatPoly :=
  polyAdd p (if minus then polyNeg q else q)

private def signedExpr (minus : Bool) (p q : PolyExpr) : PolyExpr :=
  .add p (if minus then .neg q else q)

private theorem signedPair_congr (minus : Bool) {p p' q q' : RatPoly}
    (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q q') :
    RatPolyCoeffEqv (signedPair minus p q) (signedPair minus p' q') := by
  cases minus
  · exact hp.add hq
  · exact hp.add (RatPolyCoeffEqv.neg hq)

private theorem signedPair_zero (minus : Bool) :
    RatPolyCoeffEqv (signedPair minus polyZero polyZero) polyZero := by
  cases minus <;> exact .refl _

private theorem signedPair_add (minus : Bool) (a b c d : RatPoly) :
    RatPolyCoeffEqv (signedPair minus (polyAdd a b) (polyAdd c d))
      (polyAdd (signedPair minus a c) (signedPair minus b d)) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (signedExpr minus (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (signedExpr minus (.var 0) (.var 2)) (signedExpr minus (.var 1) (.var 3)))
    (by cases minus <;> decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  cases minus <;> exact h

private theorem signedPair_mul (minus : Bool) (p q a b c d : RatPoly) :
    RatPolyCoeffEqv
      (signedPair minus (polyAdd (polyMul a q) (polyMul p b))
        (polyAdd (polyMul c q) (polyMul p d)))
      (polyAdd (polyMul (signedPair minus a c) q) (polyMul p (signedPair minus b d))) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (signedExpr minus (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3)))
      (.add (.mul (.var 4) (.var 1)) (.mul (.var 0) (.var 5))))
    (.add (.mul (signedExpr minus (.var 2) (.var 4)) (.var 1))
      (.mul (.var 0) (signedExpr minus (.var 3) (.var 5))))
    (by cases minus <;> decide)
    (fun | 0 => p | 1 => q | 2 => a | 3 => b | 4 => c | _ => d)
  cases minus <;> exact h

private theorem neg_smul_comm (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c p)) (polySmul c (polyNeg p)) := by
  have hleft := (neg_smul (polySmul c p)).trans (RatPolyCoeffEqv.smul_assoc (-1) c p)
  have hright := ((neg_smul p).smul c).trans (RatPolyCoeffEqv.smul_assoc c (-1) p)
  exact hleft.trans ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) c) p).trans
    hright.symm)

private theorem signedPair_smul (minus : Bool) (c : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (signedPair minus (polySmul c p) (polySmul c q))
      (polySmul c (signedPair minus p q)) := by
  cases minus
  · exact (RatPolyCoeffEqv.smul_add c p q).symm
  · exact ((RatPolyCoeffEqv.refl _).add (neg_smul_comm c q)).trans
      (RatPolyCoeffEqv.smul_add c p (polyNeg q)).symm

/-- Raw additivity of the actual original-coordinate frame. -/
theorem frameDerivativeAt_add (right : Bool) (b : Nat) (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (frameDerivativeAt right b i (polyAdd p q))
      (polyAdd (frameDerivativeAt right b i p) (frameDerivativeAt right b i q)) := by
  have h (minus : Bool) (a d e f : Nat) :=
    (signedPair_congr minus (angularDerivative_add (4*b+a) (4*b+d) p q)
      (angularDerivative_add (4*b+e) (4*b+f) p q)).trans (signedPair_add minus _ _ _ _)
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact h false 0 1 2 3
    · exact h true 0 1 2 3
  · cases right
    · exact h true 0 2 1 3
    · exact h false 0 2 1 3
  · cases right
    · exact h false 0 3 1 2
    · exact h true 0 3 1 2

/-- Raw rational linearity; no padded representative is differentiated. -/
theorem frameDerivativeAt_smul (right : Bool) (b : Nat) (i : Fin 3) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (frameDerivativeAt right b i (polySmul c p))
      (polySmul c (frameDerivativeAt right b i p)) := by
  have h (minus : Bool) (a d e f : Nat) :=
    (signedPair_congr minus (angularDerivative_smul (4*b+a) (4*b+d) c p)
      (angularDerivative_smul (4*b+e) (4*b+f) c p)).trans (signedPair_smul minus c _ _)
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact h false 0 1 2 3
    · exact h true 0 1 2 3
  · cases right
    · exact h true 0 2 1 3
    · exact h false 0 2 1 3
  · cases right
    · exact h false 0 3 1 2
    · exact h true 0 3 1 2

/-- Raw Leibniz rule for the literal frame polynomial operator. -/
theorem frameDerivativeAt_mul (right : Bool) (b : Nat) (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (frameDerivativeAt right b i (polyMul p q))
      (polyAdd (polyMul (frameDerivativeAt right b i p) q)
        (polyMul p (frameDerivativeAt right b i q))) := by
  have h (minus : Bool) (a d e f : Nat) :=
    (signedPair_congr minus (angularDerivative_mul (4*b+a) (4*b+d) p q)
      (angularDerivative_mul (4*b+e) (4*b+f) p q)).trans (signedPair_mul minus p q _ _ _ _)
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact h false 0 1 2 3
    · exact h true 0 1 2 3
  · cases right
    · exact h true 0 2 1 3
    · exact h false 0 2 1 3
  · cases right
    · exact h false 0 3 1 2
    · exact h true 0 3 1 2

theorem frameDerivativeAt_zero (right : Bool) (b : Nat) (i : Fin 3) :
    RatPolyCoeffEqv (frameDerivativeAt right b i polyZero) polyZero := by
  rcases directions i with rfl | rfl | rfl <;> cases right <;> exact .refl _

theorem frameDerivativeAt_one (right : Bool) (b : Nat) (i : Fin 3) :
    RatPolyCoeffEqv (frameDerivativeAt right b i polyOne) polyZero := by
  have h (minus : Bool) (a d e f : Nat) :=
    (signedPair_congr minus (angularDerivative_one (4*b+a) (4*b+d))
      (angularDerivative_one (4*b+e) (4*b+f))).trans (signedPair_zero minus)
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact h false 0 1 2 3
    · exact h true 0 1 2 3
  · cases right
    · exact h true 0 2 1 3
    · exact h false 0 2 1 3
  · cases right
    · exact h false 0 3 1 2
    · exact h true 0 3 1 2

/-- Raw negation law acts on the actual polynomial, before any padding. -/
theorem frameDerivativeAt_neg (right : Bool) (b : Nat) (i : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (frameDerivativeAt right b i (polyNeg p))
      (polyNeg (frameDerivativeAt right b i p)) := by
  have hp (a d e f : Nat) :=
    ((angularDerivative_neg (4*b+a) (4*b+d) p).add
      (angularDerivative_neg (4*b+e) (4*b+f) p)).trans (plus_neg _ _)
  have hm (a d e f : Nat) :=
    ((angularDerivative_neg (4*b+a) (4*b+d) p).add
      (RatPolyCoeffEqv.neg (angularDerivative_neg (4*b+e) (4*b+f) p))).trans (minus_neg _ _)
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact hp 0 1 2 3
    · exact hm 0 1 2 3
  · cases right
    · exact hm 0 2 1 3
    · exact hp 0 2 1 3
  · cases right
    · exact hp 0 3 1 2
    · exact hm 0 3 1 2

/-- Raw conjugation rule, before the coordinate pins or carrier padding. -/
theorem quaternionAction_conj (right : Bool) (b : Nat) (i : Fin 3) (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (quaternionAction right b i (PolyQuaternion.conj q))
      (PolyQuaternion.conj (quaternionAction right b i q)) :=
  ⟨.refl _, frameDerivativeAt_neg right b i q.iPart,
    frameDerivativeAt_neg right b i q.jPart, frameDerivativeAt_neg right b i q.kPart⟩

private def reverseExpr (right : Bool) (i : Fin 3) : PolyQuaternionExpr :=
  let q := PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0)
  let p := if right then PolyQuaternionExpr.mul (basisExpr i) q
    else PolyQuaternionExpr.mul q (basisExpr i)
  ⟨.neg p.scalar, .neg p.iPart, .neg p.jPart, .neg p.kPart⟩

private theorem reverse_matrix (right : Bool) (i : Fin 3) (c : Fin 4) :
    normalize (componentExpr (PolyQuaternionExpr.conj (productExpr right i)) c) =
      normalize (componentExpr (reverseExpr right i) c) := by
  rcases directions i with rfl | rfl | rfl <;>
    rcases components c with rfl | rfl | rfl | rfl <;> cases right <;> decide

private theorem reverse_component (right : Bool) (b : Nat) (i : Fin 3) (c : Fin 4) :
    RatPolyCoeffEqv
      (coeffEvalExpr (coordinateEnv b) (componentExpr (PolyQuaternionExpr.conj (productExpr right i)) c))
      (coeffEvalExpr (coordinateEnv b) (componentExpr (reverseExpr right i) c)) :=
  coeffEvalExpr_eqv_of_normalize_eq _ _ (reverse_matrix right i c) (coordinateEnv b)

/-- Reverse orientation swaps multiplication side and inserts the actual
imaginary-basis minus sign, at the SAME block and without unit assumptions. -/
theorem conjugate_coordinate_action {B b : Nat} (right : Bool) (hb : b<B) (i : Fin 3) :
    PaddedQuaternionCoeffEqv B
      (quaternionAction right b i (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b)))
      (negQuaternion (if right then PolyQuaternion.mul (imaginaryBasis i)
          (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
        else PolyQuaternion.mul (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
          (imaginaryBasis i))) := by
  have h := (PaddedQuaternionCoeffEqv.of_coeff (quaternionAction_conj right b i _)).trans
    (PaddedQuaternionCoeffEqv.conj (coordinate_action right hb i))
  apply h.trans
  apply PaddedQuaternionCoeffEqv.of_coeff
  cases right
  · exact ⟨reverse_component false b i 0, reverse_component false b i 1,
      reverse_component false b i 2, reverse_component false b i 3⟩
  · exact ⟨reverse_component true b i 0, reverse_component true b i 1,
      reverse_component true b i 2, reverse_component true b i 3⟩

private theorem plane_other {B b d : Nat} (hb : b<B) (hd : d<B) (hne : b≠d)
    (a e c : Fin 4) :
    PaddedPolynomialCoeffEqv B (blockAngularDerivative b a.val e.val (coordinateEnv d c.val)) polyZero := by
  have h := angularDerivative_polyVar_padded (B := B)
    (a := 4*b+a.val) (b := 4*b+e.val) (c := 4*d+c.val)
    (by have := a.isLt; omega) (by have := e.isLt; omega) (by have := c.isLt; omega)
  have he : 4*d+c.val ≠ 4*b+e.val := by have := c.isLt; have := e.isLt; omega
  have ha : 4*d+c.val ≠ 4*b+a.val := by have := c.isLt; have := a.isLt; omega
  simp only [if_neg he, if_neg ha] at h
  exact h.trans (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.zero_add polyZero))

private theorem frame_other {B b d : Nat} (right : Bool) (hb : b<B) (hd : d<B)
    (hne : b≠d) (i : Fin 3) (c : Fin 4) :
    PaddedPolynomialCoeffEqv B (frameDerivativeAt right b i (coordinateEnv d c.val)) polyZero := by
  have hp (a e f g : Fin 4) :=
    ((plane_other hb hd hne a e c).add (plane_other hb hd hne f g c)).trans
      (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.zero_add polyZero))
  have hm (a e f g : Fin 4) :=
    ((plane_other hb hd hne a e c).add (padded_neg (plane_other hb hd hne f g c))).trans
      (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.zero_add polyZero))
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact hp 0 1 2 3
    · exact hm 0 1 2 3
  · cases right
    · exact hm 0 2 1 3
    · exact hp 0 2 1 3
  · cases right
    · exact hp 0 3 1 2
    · exact hm 0 3 1 2

/-- The actual frame acts trivially on every distinct retained coordinate block. -/
theorem other_coordinate_action {B b d : Nat} (right : Bool) (hb : b<B) (hd : d<B)
    (hne : b≠d) (i : Fin 3) :
    PaddedQuaternionCoeffEqv B (quaternionAction right b i (PolyQuaternion.coordinateVariable d))
      zeroQuaternion :=
  ⟨frame_other right hb hd hne i 0, frame_other right hb hd hne i 1,
    frame_other right hb hd hne i 2, frame_other right hb hd hne i 3⟩

/-- Reverse occurrences in a distinct block are annihilated as well. -/
theorem other_conjugate_coordinate_action {B b d : Nat} (right : Bool) (hb : b<B)
    (hd : d<B) (hne : b≠d) (i : Fin 3) :
    PaddedQuaternionCoeffEqv B
      (quaternionAction right b i (PolyQuaternion.conj (PolyQuaternion.coordinateVariable d)))
      zeroQuaternion :=
  (PaddedQuaternionCoeffEqv.of_coeff (quaternionAction_conj right b i _)).trans
    (PaddedQuaternionCoeffEqv.conj (other_coordinate_action right hb hd hne i))

end YMGap.Continuum.SU2QuaternionLeftRightAngularAction

#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.rightDerivativeAt
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.frameDerivativeAt
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.quaternionAction
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.negQuaternion
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.zeroQuaternion
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.imaginaryBasis
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.coordinate_action
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.frameDerivativeAt_neg
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.frameDerivativeAt_add
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.frameDerivativeAt_smul
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.frameDerivativeAt_mul
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.frameDerivativeAt_zero
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.frameDerivativeAt_one
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.quaternionAction_conj
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.conjugate_coordinate_action
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.other_coordinate_action
#print axioms YMGap.Continuum.SU2QuaternionLeftRightAngularAction.other_conjugate_coordinate_action
