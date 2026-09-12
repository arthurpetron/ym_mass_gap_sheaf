/-
# Solid-zonal identification and Haar descent of the actual polynomial trace

The actual polynomial matrix trace is identified coefficientwise with the
solid-zonal recurrence using the literal polynomial quaternion norm. The
existing sphere-ideal theorem then supplies ordinary-character equality
under every Haar insertion whenever that norm is a proved Haar unit.
Pointwise unit-norm assumptions are never used under the integral.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈c " => ComplexCoeffEqv
local infixl:65 " ⊞ " => complexRatPolyAdd
local infixl:70 " ⊠ " => complexRatPolyMul
local notation "𝟘" => complexRatPolyZero
local notation "𝟙" => complexRatPolyOne
private abbrev A := fundamentalMatrixCoefficient

/-- The literal sum of the four squared polynomial quaternion components. -/
def radiusPolynomial (q : RatPolyQuaternion) : RatPoly :=
  polyQuaternionNorm ⟨q.r, q.i, q.j, q.k⟩

/-- Real polynomials embedded without discarding their coefficient data. -/
def realPolynomial (p : RatPoly) : ComplexRatPoly := (p, polyZero)

private theorem real_mul (p q : RatPoly) :
    (realPolynomial p ⊠ realPolynomial q) ≈c realPolynomial (polyMul p q) :=
  ⟨((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left _))).trans
      (RatPolyCoeffEqv.add_zero _),
    ((RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.mul_zero_left _)).trans
      (RatPolyCoeffEqv.zero_add _)⟩

private def qenv (q : RatPolyQuaternion) : Nat → RatPoly
  | 0 => q.r | 1 => q.i | 2 => q.j | 3 => q.k | _ => polyZero

private def r : PolyExpr := .var 0
private def i : PolyExpr := .var 1
private def j : PolyExpr := .var 2
private def k : PolyExpr := .var 3
private def sq (x : PolyExpr) : PolyExpr := .mul x x
private def radiusExpr : PolyExpr := .add (sq r) (.add (sq i) (.add (sq j) (sq k)))

private theorem zero_certificate (e : PolyExpr) (h : normalize e = normalize (.const 0))
    (environment : Nat → RatPoly) : RatPolyCoeffEqv (coeffEvalExpr environment e) polyZero :=
  (coeffEvalExpr_eqv_of_normalize_eq e (.const 0) h environment).trans (RatPolyCoeffEqv.zero_smul _)

private theorem diagonal_product (q : RatPolyQuaternion) :
    (A q false false ⊠ A q true true) ≈c realPolynomial (polyAdd (polyMul q.r q.r) (polyMul q.i q.i)) := by
  constructor
  · exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (sq r) (.neg (.mul i (.neg i)))) (.add (sq r) (sq i)) (by decide) (qenv q)
  · exact zero_certificate (.add (.mul r (.neg i)) (.mul i r)) (by decide) (qenv q)

private theorem offdiagonal_product (q : RatPolyQuaternion) :
    (A q false true ⊠ A q true false) ≈c realPolynomial (polyNeg (polyAdd (polyMul q.j q.j) (polyMul q.k q.k))) := by
  constructor
  · exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul j (.neg j)) (.neg (sq k))) (.neg (.add (sq j) (sq k))) (by decide) (qenv q)
  · exact zero_certificate (.add (.mul j k) (.mul k (.neg j))) (by decide) (qenv q)

/-- Determinant/norm identity at coefficient-probe strength, with no
unit-norm premise on an evaluation environment. -/
theorem diagonal_product_radius (q : RatPolyQuaternion) :
    (A q false false ⊠ A q true true) ≈c
      (realPolynomial (radiusPolynomial q) ⊞ (A q false true ⊠ A q true false)) := by
  refine (diagonal_product q).trans (?_ : ComplexCoeffEqv _ _)
  refine (show realPolynomial (polyAdd (polyMul q.r q.r) (polyMul q.i q.i)) ≈c
    (realPolynomial (radiusPolynomial q) ⊞
      realPolynomial (polyNeg (polyAdd (polyMul q.j q.j) (polyMul q.k q.k)))) from ?_).trans ?_
  · exact ⟨coeffEvalExpr_eqv_of_normalize_eq (.add (sq r) (sq i))
      (.add radiusExpr (.neg (.add (sq j) (sq k)))) (by decide) (qenv q), RatPolyCoeffEqv.refl _⟩
  · exact (ComplexCoeffEqv.refl _).add (offdiagonal_product q).symm

private theorem double_polynomial (p : RatPoly) : RatPolyCoeffEqv (polyAdd p p) (polySmul 2 p) :=
  ((RatPolyCoeffEqv.one_smul p).symm.add (RatPolyCoeffEqv.one_smul p).symm).trans
    ((RatPolyCoeffEqv.add_smul_same 1 1 p).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide) p))

theorem fundamental_trace (q : RatPolyQuaternion) :
    (A q false false ⊞ A q true true) ≈c realPolynomial (polySmul 2 q.r) :=
  ⟨double_polynomial q.r, zero_certificate (.add i (.neg i)) (by decide) (qenv q)⟩

private theorem q_remove (a b : Q') : ((a + b) + -b).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (-b))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv b)) (QPoly.q_add_zero_eqv a))

private theorem q_cancel {a b z : Q'} (h : (a + z).eqv (b + z)) : a.eqv b :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (q_remove a z))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-z) h) (q_remove b z))

private theorem coeff_cancel {a b z : RatPoly}
    (h : RatPolyCoeffEqv (polyAdd a z) (polyAdd b z)) : RatPolyCoeffEqv a b := by
  intro weight
  exact q_cancel (Q'.eqv_trans _ _ _ (Q'.eqv_symm (ratWeightedSum_add weight _ _))
    (Q'.eqv_trans _ _ _ (h weight) (ratWeightedSum_add weight _ _)))

private theorem complex_cancel {a b z : ComplexRatPoly} (h : (a ⊞ z) ≈c (b ⊞ z)) : a ≈c b :=
  ⟨coeff_cancel h.1, coeff_cancel h.2⟩

/-- The trace recurrence with the actual polynomial radius, still before
sphere-ideal descent and valid under all coefficient probes. -/
theorem polynomialTrace_radial_recurrence (q : RatPolyQuaternion) (n : Nat) :
    (polynomialTrace q (n + 2) ⊞ (realPolynomial (radiusPolynomial q) ⊠ polynomialTrace q n)) ≈c
      (realPolynomial (polySmul 2 q.r) ⊠ polynomialTrace q (n + 1)) := by
  let t := polynomialTrace q n
  let bc := A q false true ⊠ A q true false
  let norm := realPolynomial (radiusPolynomial q)
  have hleft : ((polynomialTrace q (n + 2) ⊞ (norm ⊠ t)) ⊞ (bc ⊠ t)) ≈c
      (polynomialTrace q (n + 2) ⊞ ((A q false false ⊠ A q true true) ⊠ t)) :=
    (add_assoc _ _ _).trans ((ComplexCoeffEqv.refl _).add
      ((add_mul norm bc t).symm.trans ((diagonal_product_radius q).symm.mul (ComplexCoeffEqv.refl t))))
  have hright := ((fundamental_trace q).mul (ComplexCoeffEqv.refl (polynomialTrace q (n + 1)))).add
    (ComplexCoeffEqv.refl (bc ⊠ t))
  exact complex_cancel ((hleft.trans (polynomialTrace_recurrence q n)).trans hright)

private theorem cancel_negative_smul (a b : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyAdd a (polySmul (-1) b)) b) a :=
  (RatPolyCoeffEqv.add_assoc _ _ _).trans
    (((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.add_comm _ _).trans (RatPolyCoeffEqv.add_neg_smul _))).trans
      (RatPolyCoeffEqv.add_zero _))

private theorem solid_balance (q : RatPolyQuaternion) (n : Nat) :
    (realPolynomial (solidZonalCharacterPolynomial q.r (radiusPolynomial q) (n + 2)) ⊞
      (realPolynomial (radiusPolynomial q) ⊠ realPolynomial (solidZonalCharacterPolynomial q.r (radiusPolynomial q) n))) ≈c
      (realPolynomial (polySmul 2 q.r) ⊠
        realPolynomial (solidZonalCharacterPolynomial q.r (radiusPolynomial q) (n + 1))) := by
  let z := solidZonalCharacterPolynomial q.r (radiusPolynomial q)
  have hc : RatPolyCoeffEqv (polyAdd (z (n + 2)) (polyMul (radiusPolynomial q) (z n)))
      (polyMul (polySmul 2 q.r) (z (n + 1))) := cancel_negative_smul _ _
  have hreal : (realPolynomial (z (n + 2)) ⊞ realPolynomial (polyMul (radiusPolynomial q) (z n))) ≈c
      realPolynomial (polyMul (polySmul 2 q.r) (z (n + 1))) := ⟨hc, RatPolyCoeffEqv.refl _⟩
  exact (((ComplexCoeffEqv.refl (realPolynomial (z (n + 2)))).add
    (real_mul (radiusPolynomial q) (z n))).trans hreal).trans (real_mul _ _).symm

/-- The ORIGINAL matrix trace equals the solid-zonal polynomial at EVERY
degree, with every spectator coefficient retained. No unit-norm hypothesis. -/
theorem polynomialTrace_eq_solid (q : RatPolyQuaternion) : ∀ n,
    polynomialTrace q n ≈c realPolynomial (solidZonalCharacterPolynomial q.r (radiusPolynomial q) n)
  | 0 => polynomialTrace_zero q
  | 1 => (polynomialTrace_one q).trans (fundamental_trace q)
  | n + 2 => by
    apply complex_cancel (z := realPolynomial (radiusPolynomial q) ⊠ polynomialTrace q n)
    refine (polynomialTrace_radial_recurrence q n).trans ?_
    refine ((ComplexCoeffEqv.refl _).mul (polynomialTrace_eq_solid q (n + 1))).trans ?_
    exact (solid_balance q n).symm.trans
      ((ComplexCoeffEqv.refl _).add ((ComplexCoeffEqv.refl _).mul (polynomialTrace_eq_solid q n).symm))

/-- Haar descent consumes a proved arbitrary-insertion radius relation,
never an isolated pointwise unit-norm fact. -/
theorem polynomialTrace_haar_character {blocks : Nat} (q : RatPolyQuaternion)
    (hradius : QuaternionHaarCarrierEqv blocks (radiusPolynomial q) polyOne) (n : Nat) :
    QuaternionHaarCarrierEqv blocks (polynomialTrace q n).1 (characterPolynomial q.r n) ∧
      QuaternionHaarCarrierEqv blocks (polynomialTrace q n).2 polyZero :=
  ⟨QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polynomialTrace_eq_solid q n).1)
      (solidZonalCharacterPolynomial_eq_character_of_radius_eq_one q.r (radiusPolynomial q) hradius n),
    RatPolyCoeffEqv.haarCarrier (polynomialTrace_eq_solid q n).2⟩

end YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace.radiusPolynomial
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace.realPolynomial
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace.diagonal_product_radius
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace.fundamental_trace
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace.polynomialTrace_radial_recurrence
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace.polynomialTrace_eq_solid
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace.polynomialTrace_haar_character
