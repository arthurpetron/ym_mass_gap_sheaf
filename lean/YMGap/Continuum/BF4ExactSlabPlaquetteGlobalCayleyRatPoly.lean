/-
# Global Cayley identity as literal ORIGINAL RatPoly probes

The global division-free Cayley formula is reified here in the finite-support
`RatPoly` carrier accepted by the ORIGINAL slab functional.  Sixteen atoms are
the four coordinates of the four literally oriented plaquette-link
polynomials; atom 16 is the existing corrected-slab plaquette scalar.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyPolynomialClear

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly

set_option autoImplicit false
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator
open YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyPolynomialClear
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a + c ≈ b + d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b :=
  Q'.neg_eqv_congr _ _ h

/-! ## 1. Substitution into the full finite RatPoly carrier -/

private def ratPolyPow (polynomial : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | exponent + 1 => polyMul (ratPolyPow polynomial exponent) polynomial

private def instantiate
    (atoms : Nat → RatPoly) : PolyExpr → RatPoly
  | .const coefficient => polyConst (Q'.ofInt coefficient)
  | .var index => atoms index
  | .add left right => polyAdd (instantiate atoms left) (instantiate atoms right)
  | .mul left right => polyMul (instantiate atoms left) (instantiate atoms right)
  | .neg value => polyNeg (instantiate atoms value)
  | .pow value power => ratPolyPow (instantiate atoms value) power

private theorem eval_polyConst (rho : Nat → Q') (value : Q') :
    evalRatPoly rho (polyConst value) ≈ value := by
  change value * 1 + 0 ≈ value
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (Q'.add_zero' (value * 1)))
    (Q'.mul_one_eqv value)

private theorem eval_ratPolyPow (rho : Nat → Q') (polynomial : RatPoly) :
    ∀ exponent,
      evalRatPoly rho (ratPolyPow polynomial exponent) ≈
        qpow (evalRatPoly rho polynomial) exponent
  | 0 => evalRatPoly_one rho
  | exponent + 1 =>
      Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho (ratPolyPow polynomial exponent) polynomial)
        (mc (eval_ratPolyPow rho polynomial exponent) (Q'.eqv_refl _))

private theorem eval_instantiate (rho : Nat → Q') (atoms : Nat → RatPoly) :
    ∀ expression,
      evalRatPoly rho (instantiate atoms expression) ≈
        RingNormaliser.eval (fun index => evalRatPoly rho (atoms index)) expression
  | .const coefficient => eval_polyConst rho (Q'.ofInt coefficient)
  | .var _ => Q'.eqv_refl _
  | .add left right =>
      Q'.eqv_trans _ _ _
        (evalRatPoly_add rho (instantiate atoms left) (instantiate atoms right))
        (ac (eval_instantiate rho atoms left) (eval_instantiate rho atoms right))
  | .mul left right =>
      Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho (instantiate atoms left) (instantiate atoms right))
        (mc (eval_instantiate rho atoms left) (eval_instantiate rho atoms right))
  | .neg value =>
      Q'.eqv_trans _ _ _
        (evalRatPoly_neg rho (instantiate atoms value))
        (nc (eval_instantiate rho atoms value))
  | .pow value power =>
      Q'.eqv_trans _ _ _
        (eval_ratPolyPow rho (instantiate atoms value) power)
        (qpow_eqv_congr (eval_instantiate rho atoms value) power)

private theorem polyConst_coeffEvalConst (coefficient : Q') :
    RatPolyCoeffEqv (polyConst coefficient)
      (polySmul coefficient polyOne) := by
  intro weight
  change coefficient * weight [] + 0 ≈
    (coefficient * 1) * weight [] + 0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv coefficient)))
    (Q'.eqv_refl 0)

private theorem ratPolyPow_coeffPolyPow
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) : ∀ power,
    RatPolyCoeffEqv (ratPolyPow left power) (coeffPolyPow right power)
  | 0 => RatPolyCoeffEqv.refl polyOne
  | power + 1 =>
      RatPolyCoeffEqv.mul (ratPolyPow_coeffPolyPow h power) h

/-- The local substitution compiler and the shared coefficient compiler agree
coefficientwise for every expression and polynomial atom environment. -/
theorem instantiate_coeffEvalExpr
    (atoms : Nat → RatPoly) : ∀ expression,
    RatPolyCoeffEqv (instantiate atoms expression)
      (coeffEvalExpr atoms expression)
  | .const coefficient => polyConst_coeffEvalConst (Q'.ofInt coefficient)
  | .var index => RatPolyCoeffEqv.refl (atoms index)
  | .add left right =>
      RatPolyCoeffEqv.add
        (instantiate_coeffEvalExpr atoms left)
        (instantiate_coeffEvalExpr atoms right)
  | .mul left right =>
      RatPolyCoeffEqv.mul
        (instantiate_coeffEvalExpr atoms left)
        (instantiate_coeffEvalExpr atoms right)
  | .neg value =>
      RatPolyCoeffEqv.neg (instantiate_coeffEvalExpr atoms value)
  | .pow value power =>
      ratPolyPow_coeffPolyPow (instantiate_coeffEvalExpr atoms value) power

private def substituteExpr
    (substitution : Nat → PolyExpr) : PolyExpr → PolyExpr
  | .const coefficient => .const coefficient
  | .var index => substitution index
  | .add left right =>
      .add (substituteExpr substitution left)
        (substituteExpr substitution right)
  | .mul left right =>
      .mul (substituteExpr substitution left)
        (substituteExpr substitution right)
  | .neg value => .neg (substituteExpr substitution value)
  | .pow value power => .pow (substituteExpr substitution value) power

private theorem coeffEvalExpr_substitute
    (atoms : Nat → RatPoly) (substitution : Nat → PolyExpr) : ∀ expression,
    RatPolyCoeffEqv
      (coeffEvalExpr atoms (substituteExpr substitution expression))
      (coeffEvalExpr
        (fun index => coeffEvalExpr atoms (substitution index)) expression)
  | .const _ => RatPolyCoeffEqv.refl _
  | .var _ => RatPolyCoeffEqv.refl _
  | .add left right =>
      RatPolyCoeffEqv.add
        (coeffEvalExpr_substitute atoms substitution left)
        (coeffEvalExpr_substitute atoms substitution right)
  | .mul left right =>
      RatPolyCoeffEqv.mul
        (coeffEvalExpr_substitute atoms substitution left)
        (coeffEvalExpr_substitute atoms substitution right)
  | .neg value =>
      RatPolyCoeffEqv.neg (coeffEvalExpr_substitute atoms substitution value)
  | .pow value power =>
      coeffPolyPow_congr
        (coeffEvalExpr_substitute atoms substitution value) power

private theorem eval_expression_congr {rho sigma : Nat → Q'}
    (h : ∀ index, rho index ≈ sigma index) :
    ∀ expression,
      RingNormaliser.eval rho expression ≈ RingNormaliser.eval sigma expression
  | .const _ => Q'.eqv_refl _
  | .var index => h index
  | .add left right =>
      ac (eval_expression_congr h left) (eval_expression_congr h right)
  | .mul left right =>
      mc (eval_expression_congr h left) (eval_expression_congr h right)
  | .neg value => nc (eval_expression_congr h value)
  | .pow value power =>
      qpow_eqv_congr (eval_expression_congr h value) power

/-! ## 2. The exact global Cayley expressions -/

private abbrev PE := PolyExpr

local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private structure ETriple where
  x : PE
  y : PE
  z : PE

private structure EQuaternion where
  r : PE
  i : PE
  j : PE
  k : PE

private structure ECayleyData where
  D : PE
  p : ETriple
  q : ETriple
  r : ETriple
  s : ETriple

private def eQuaternion (offset : Nat) : EQuaternion :=
  ⟨.var offset, .var (offset + 1), .var (offset + 2), .var (offset + 3)⟩

private def eImaginary (q : EQuaternion) : ETriple := ⟨q.i, q.j, q.k⟩

private def eScale3 (scale : PE) (a : ETriple) : ETriple :=
  ⟨scale * a.x, scale * a.y, scale * a.z⟩

private def eAdd3 (a b : ETriple) : ETriple :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

private def eDot3 (a b : ETriple) : PE :=
  (a.x * b.x + a.y * b.y) + a.z * b.z

private def eNorm3 (a : ETriple) : PE := eDot3 a a

private def eCross3 (a b : ETriple) : ETriple :=
  ⟨a.y * b.z + -(a.z * b.y),
    a.z * b.x + -(a.x * b.z),
    a.x * b.y + -(a.y * b.x)⟩

private def eDet3 (a b c : ETriple) : PE := eDot3 (eCross3 a b) c

private def ePow2 (x : PE) : PE := x * x
private def ePow3 (x : PE) : PE := (x * x) * x
private def ePow4 (x : PE) : PE := (x * x) * (x * x)
private def ePow5 (x : PE) : PE := ((x * x) * (x * x)) * x
private def ePow6 (x : PE) : PE := ((x * x) * (x * x)) * (x * x)

private def eH2 (a b c d : ETriple) : PE :=
  4 * eNorm3 (eAdd3 (eAdd3 (eAdd3 a b) c) d)

private def eH3 (a b c d : ETriple) : PE :=
  16 * ((eDet3 a b c + eDet3 a b d) + (eDet3 a c d + eDet3 b c d))

private def eH4 (a b c d : ETriple) : PE :=
  -(8 * ((eDot3 a b * (eNorm3 c + eNorm3 d) +
      eDot3 a c * (eNorm3 b + eNorm3 d)) +
    eDot3 a d * (eNorm3 b + eNorm3 c) +
    ((eDot3 b c * (eNorm3 a + eNorm3 d) +
      eDot3 b d * (eNorm3 a + eNorm3 c)) +
      eDot3 c d * (eNorm3 a + eNorm3 b)))) +
  -(32 * (eDot3 a b * eDot3 c d +
    -(eDot3 (eCross3 a b) (eCross3 c d))))

private def eH5 (a b c d : ETriple) : PE :=
  -(16 * ((eDet3 a b c * eNorm3 d + eDet3 a b d * eNorm3 c) +
    (eDet3 a c d * eNorm3 b + eDet3 b c d * eNorm3 a)))

private def eH6 (a b c d : ETriple) : PE :=
  4 * ((eNorm3 a * eNorm3 b * eNorm3 c +
      eNorm3 a * eNorm3 b * eNorm3 d) +
    (eNorm3 a * eNorm3 c * eNorm3 d +
      eNorm3 b * eNorm3 c * eNorm3 d)) +
  8 * ((eDot3 a b * (eNorm3 c * eNorm3 d) +
      eDot3 a c * (eNorm3 b * eNorm3 d)) +
    eDot3 a d * (eNorm3 b * eNorm3 c) +
    ((eDot3 b c * (eNorm3 a * eNorm3 d) +
      eDot3 b d * (eNorm3 a * eNorm3 c)) +
      eDot3 c d * (eNorm3 a * eNorm3 b)))

private def eClearedFactor (D : PE) (a : ETriple) : PE :=
  ePow2 D + eNorm3 a

private def eClearedDenominator (D : PE) (a b c d : ETriple) : PE :=
  ((eClearedFactor D a * eClearedFactor D b) * eClearedFactor D c) *
    eClearedFactor D d

private def eClearedDeficit (D : PE) (a b c d : ETriple) : PE :=
  ((((ePow6 D * eH2 a b c d + ePow5 D * eH3 a b c d) +
      ePow4 D * eH4 a b c d) +
      ePow3 D * eH5 a b c d) +
      ePow2 D * eH6 a b c d)

private def eCayleyData : ECayleyData :=
  let u0 := eQuaternion 0
  let u1 := eQuaternion 4
  let u2 := eQuaternion 8
  let u3 := eQuaternion 12
  let d0 := 1 + u0.r
  let d1 := 1 + u1.r
  let d2 := 1 + u2.r
  let d3 := 1 + u3.r
  let D := ((d0 * d1) * d2) * d3
  ⟨D,
    eScale3 ((d1 * d2) * d3) (eImaginary u0),
    eScale3 ((d0 * d2) * d3) (eImaginary u1),
    eScale3 ((d0 * d1) * d3) (eImaginary u2),
    eScale3 ((d0 * d1) * d2) (eImaginary u3)⟩

private def eCayleyNormSum : PE :=
  (eNorm3 eCayleyData.p + eNorm3 eCayleyData.q) +
    (eNorm3 eCayleyData.r + eNorm3 eCayleyData.s)

private def eCayleyNormalizedH4 : PE :=
  eH4 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s +
    -(eCayleyNormSum *
      eH2 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

private def globalDenominatorExpression : PE :=
  eClearedDenominator eCayleyData.D eCayleyData.p eCayleyData.q
    eCayleyData.r eCayleyData.s

private def globalLeftExpression : PE :=
  globalDenominatorExpression * (2 + -(2 * .var 16))

private def globalDeficitExpression : PE :=
  eClearedDeficit eCayleyData.D eCayleyData.p eCayleyData.q
    eCayleyData.r eCayleyData.s

private def evalETriple (rho : Nat → Q') (a : ETriple) : Triple :=
  ⟨RingNormaliser.eval rho a.x,
    RingNormaliser.eval rho a.y,
    RingNormaliser.eval rho a.z⟩

private theorem eval_eH2 (rho : Nat → Q') (a b c d : ETriple) :
    RingNormaliser.eval rho (eH2 a b c d) =
      H2 (evalETriple rho a) (evalETriple rho b)
        (evalETriple rho c) (evalETriple rho d) := rfl

private theorem eval_eH3 (rho : Nat → Q') (a b c d : ETriple) :
    RingNormaliser.eval rho (eH3 a b c d) =
      H3 (evalETriple rho a) (evalETriple rho b)
        (evalETriple rho c) (evalETriple rho d) := rfl

private theorem eval_eH4 (rho : Nat → Q') (a b c d : ETriple) :
    RingNormaliser.eval rho (eH4 a b c d) =
      H4 (evalETriple rho a) (evalETriple rho b)
        (evalETriple rho c) (evalETriple rho d) := rfl

private theorem eval_eH5 (rho : Nat → Q') (a b c d : ETriple) :
    RingNormaliser.eval rho (eH5 a b c d) =
      H5 (evalETriple rho a) (evalETriple rho b)
        (evalETriple rho c) (evalETriple rho d) := rfl

private theorem eval_eH6 (rho : Nat → Q') (a b c d : ETriple) :
    RingNormaliser.eval rho (eH6 a b c d) =
      H6 (evalETriple rho a) (evalETriple rho b)
        (evalETriple rho c) (evalETriple rho d) := rfl

private theorem eval_eClearedDenominator
    (rho : Nat → Q') (D : PE) (a b c d : ETriple) :
    RingNormaliser.eval rho (eClearedDenominator D a b c d) =
      clearedCayleyDenominator (RingNormaliser.eval rho D)
        (evalETriple rho a) (evalETriple rho b)
        (evalETriple rho c) (evalETriple rho d) := rfl

private theorem eval_eClearedDeficit
    (rho : Nat → Q') (D : PE) (a b c d : ETriple) :
    RingNormaliser.eval rho (eClearedDeficit D a b c d) =
      clearedCayleyDeficit (RingNormaliser.eval rho D)
        (evalETriple rho a) (evalETriple rho b)
        (evalETriple rho c) (evalETriple rho d) := rfl

private theorem eval_globalDenominatorExpression (rho : Nat → Q') :
    RingNormaliser.eval rho globalDenominatorExpression =
      clearedCayleyDenominator (RingNormaliser.eval rho eCayleyData.D)
        (evalETriple rho eCayleyData.p) (evalETriple rho eCayleyData.q)
        (evalETriple rho eCayleyData.r) (evalETriple rho eCayleyData.s) :=
  eval_eClearedDenominator rho eCayleyData.D eCayleyData.p
    eCayleyData.q eCayleyData.r eCayleyData.s

private theorem eval_globalLeftExpression (rho : Nat → Q') :
    RingNormaliser.eval rho globalLeftExpression =
      clearedCayleyDenominator (RingNormaliser.eval rho eCayleyData.D)
          (evalETriple rho eCayleyData.p) (evalETriple rho eCayleyData.q)
          (evalETriple rho eCayleyData.r) (evalETriple rho eCayleyData.s) *
        (2 + -(2 * rho 16)) :=
  congrArg (fun value => value * (2 + -(2 * rho 16)))
    (eval_globalDenominatorExpression rho)

private theorem eval_globalDeficitExpression (rho : Nat → Q') :
    RingNormaliser.eval rho globalDeficitExpression =
      clearedCayleyDeficit (RingNormaliser.eval rho eCayleyData.D)
        (evalETriple rho eCayleyData.p) (evalETriple rho eCayleyData.q)
        (evalETriple rho eCayleyData.r) (evalETriple rho eCayleyData.s) :=
  eval_eClearedDeficit rho eCayleyData.D eCayleyData.p
    eCayleyData.q eCayleyData.r eCayleyData.s

/-! ## 3. ORIGINAL oriented face atoms -/

private def faceEntry0 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(face.1, (dirsOf face.2).1), false⟩

private def faceEntry1 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(addE face.1 (dirsOf face.2).1, (dirsOf face.2).2), false⟩

private def faceEntry2 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(addE face.1 (dirsOf face.2).2, (dirsOf face.2).1), true⟩

private def faceEntry3 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(face.1, (dirsOf face.2).2), true⟩

private def facePolynomialAtoms
    (extent : Nat) (face : Z4Plaq) : Nat → RatPoly
  | 0 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry0 face)).scalar
  | 1 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry0 face)).iPart
  | 2 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry0 face)).jPart
  | 3 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry0 face)).kPart
  | 4 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry1 face)).scalar
  | 5 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry1 face)).iPart
  | 6 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry1 face)).jPart
  | 7 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry1 face)).kPart
  | 8 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry2 face)).scalar
  | 9 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry2 face)).iPart
  | 10 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry2 face)).jPart
  | 11 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry2 face)).kPart
  | 12 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry3 face)).scalar
  | 13 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry3 face)).iPart
  | 14 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry3 face)).jPart
  | 15 => (orientedCorrectedSlabLinkPolynomial extent (faceEntry3 face)).kPart
  | 16 => (correctedSlabPlaquettePolynomial extent face).scalar
  | _ => polyZero

private theorem face_entry0_eval
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment qs)
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry0 face)))
      (unitValue (orientedLinkValue extent qs (faceEntry0 face))) :=
  oriented_link_eval extent qs (faceEntry0 face)

private theorem face_entry1_eval
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment qs)
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry1 face)))
      (unitValue (orientedLinkValue extent qs (faceEntry1 face))) :=
  oriented_link_eval extent qs (faceEntry1 face)

private theorem face_entry2_eval
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment qs)
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry2 face)))
      (unitValue (orientedLinkValue extent qs (faceEntry2 face))) :=
  oriented_link_eval extent qs (faceEntry2 face)

private theorem face_entry3_eval
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment qs)
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry3 face)))
      (unitValue (orientedLinkValue extent qs (faceEntry3 face))) :=
  oriented_link_eval extent qs (faceEntry3 face)

private def faceStage1Atoms
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) : Nat → Q'
  | 0 => (orientedLinkValue extent qs (faceEntry0 face)).val.r
  | 1 => (orientedLinkValue extent qs (faceEntry0 face)).val.i
  | 2 => (orientedLinkValue extent qs (faceEntry0 face)).val.j
  | 3 => (orientedLinkValue extent qs (faceEntry0 face)).val.k
  | index => evalRatPoly (environment qs) (facePolynomialAtoms extent face index)

private def faceStage2Atoms
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) : Nat → Q'
  | 4 => (orientedLinkValue extent qs (faceEntry1 face)).val.r
  | 5 => (orientedLinkValue extent qs (faceEntry1 face)).val.i
  | 6 => (orientedLinkValue extent qs (faceEntry1 face)).val.j
  | 7 => (orientedLinkValue extent qs (faceEntry1 face)).val.k
  | index => faceStage1Atoms extent qs face index

private def faceStage3Atoms
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) : Nat → Q'
  | 8 => (orientedLinkValue extent qs (faceEntry2 face)).val.r
  | 9 => (orientedLinkValue extent qs (faceEntry2 face)).val.i
  | 10 => (orientedLinkValue extent qs (faceEntry2 face)).val.j
  | 11 => (orientedLinkValue extent qs (faceEntry2 face)).val.k
  | index => faceStage2Atoms extent qs face index

private def faceActualAtoms
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) : Nat → Q'
  | 12 => (orientedLinkValue extent qs (faceEntry3 face)).val.r
  | 13 => (orientedLinkValue extent qs (faceEntry3 face)).val.i
  | 14 => (orientedLinkValue extent qs (faceEntry3 face)).val.j
  | 15 => (orientedLinkValue extent qs (faceEntry3 face)).val.k
  | index => faceStage3Atoms extent qs face index

private theorem face_stage1_pin
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    ∀ index,
      evalRatPoly (environment qs) (facePolynomialAtoms extent face index) ≈
        faceStage1Atoms extent qs face index
  | 0 => (face_entry0_eval extent qs face).scalar
  | 1 => (face_entry0_eval extent qs face).iPart
  | 2 => (face_entry0_eval extent qs face).jPart
  | 3 => (face_entry0_eval extent qs face).kPart
  | _ + 4 => Q'.eqv_refl _

private theorem face_stage2_pin
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    ∀ index,
      faceStage1Atoms extent qs face index ≈
        faceStage2Atoms extent qs face index
  | 0 => Q'.eqv_refl _
  | 1 => Q'.eqv_refl _
  | 2 => Q'.eqv_refl _
  | 3 => Q'.eqv_refl _
  | 4 => (face_entry1_eval extent qs face).scalar
  | 5 => (face_entry1_eval extent qs face).iPart
  | 6 => (face_entry1_eval extent qs face).jPart
  | 7 => (face_entry1_eval extent qs face).kPart
  | _ + 8 => Q'.eqv_refl _

private theorem face_stage3_pin
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    ∀ index,
      faceStage2Atoms extent qs face index ≈
        faceStage3Atoms extent qs face index
  | 0 => Q'.eqv_refl _
  | 1 => Q'.eqv_refl _
  | 2 => Q'.eqv_refl _
  | 3 => Q'.eqv_refl _
  | 4 => Q'.eqv_refl _
  | 5 => Q'.eqv_refl _
  | 6 => Q'.eqv_refl _
  | 7 => Q'.eqv_refl _
  | 8 => (face_entry2_eval extent qs face).scalar
  | 9 => (face_entry2_eval extent qs face).iPart
  | 10 => (face_entry2_eval extent qs face).jPart
  | 11 => (face_entry2_eval extent qs face).kPart
  | _ + 12 => Q'.eqv_refl _

private theorem face_stage4_pin
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    ∀ index,
      faceStage3Atoms extent qs face index ≈
        faceActualAtoms extent qs face index
  | 0 => Q'.eqv_refl _
  | 1 => Q'.eqv_refl _
  | 2 => Q'.eqv_refl _
  | 3 => Q'.eqv_refl _
  | 4 => Q'.eqv_refl _
  | 5 => Q'.eqv_refl _
  | 6 => Q'.eqv_refl _
  | 7 => Q'.eqv_refl _
  | 8 => Q'.eqv_refl _
  | 9 => Q'.eqv_refl _
  | 10 => Q'.eqv_refl _
  | 11 => Q'.eqv_refl _
  | 12 => (face_entry3_eval extent qs face).scalar
  | 13 => (face_entry3_eval extent qs face).iPart
  | 14 => (face_entry3_eval extent qs face).jPart
  | 15 => (face_entry3_eval extent qs face).kPart
  | _ + 16 => Q'.eqv_refl _

private theorem face_expression_pin
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq)
    (expression : PolyExpr) :
    RingNormaliser.eval
        (fun index => evalRatPoly (environment qs)
          (facePolynomialAtoms extent face index)) expression ≈
      RingNormaliser.eval (faceActualAtoms extent qs face) expression :=
  Q'.eqv_trans _ _ _
    (eval_expression_congr (face_stage1_pin extent qs face) expression)
    (Q'.eqv_trans _ _ _
      (eval_expression_congr (face_stage2_pin extent qs face) expression)
      (Q'.eqv_trans _ _ _
        (eval_expression_congr (face_stage3_pin extent qs face) expression)
        (eval_expression_congr (face_stage4_pin extent qs face) expression)))

/-- Literal finite-support ORIGINAL probe for the cleared Cayley left side. -/
def globalCayleyDenominatorPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face) globalDenominatorExpression

/-- Literal finite-support ORIGINAL probe for the cleared Cayley left side. -/
def globalCayleyLeftPolynomial (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face) globalLeftExpression

/-- Literal finite-support ORIGINAL probe for the global cleared deficit. -/
def globalCayleyDeficitPolynomial (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face) globalDeficitExpression

/-- Degree-two homogeneous Cayley term, including its shared-denominator
power, on the ORIGINAL face carrier. -/
def globalCayleyDegreeTwoPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face)
    (ePow6 eCayleyData.D *
      eH2 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Degree-three homogeneous Cayley term on the ORIGINAL face carrier. -/
def globalCayleyDegreeThreePolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face)
    (ePow5 eCayleyData.D *
      eH3 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Degree-four homogeneous Cayley term on the ORIGINAL face carrier. -/
def globalCayleyDegreeFourPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face)
    (ePow4 eCayleyData.D *
      eH4 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Degree-four probe in the normalized Cayley convention
`F4 = H4 - normSum*H2`, still multiplied by the global clearing weight. -/
def globalCayleyNormalizedDegreeFourPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face)
    (ePow4 eCayleyData.D * eCayleyNormalizedH4)

/-- Exact quartic correction contributed by the Cayley denominator when the
raw `H4` coefficient is converted to the normalized `F4` convention. -/
def globalCayleyQuarticNormalizationCorrectionPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face)
    (ePow4 eCayleyData.D *
      (eCayleyNormSum *
        eH2 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s))

/-- The raw cleared quartic term is the weighted normalized quartic plus its
explicit denominator correction. -/
theorem globalCayleyDegreeFourPolynomial_coeff_normalized
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (globalCayleyDegreeFourPolynomial extent face)
      (polyAdd
        (globalCayleyNormalizedDegreeFourPolynomial extent face)
        (globalCayleyQuarticNormalizationCorrectionPolynomial extent face)) := by
  let environment : Nat → RatPoly
    | 0 => instantiate (facePolynomialAtoms extent face) (ePow4 eCayleyData.D)
    | 1 => instantiate (facePolynomialAtoms extent face)
        (eH4 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)
    | 2 => instantiate (facePolynomialAtoms extent face) eCayleyNormSum
    | 3 => instantiate (facePolynomialAtoms extent face)
        (eH2 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)
    | _ => polyZero
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.var 1))
    (.add
      (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 2) (.var 3)))))
      (.mul (.var 0) (.mul (.var 2) (.var 3))))
    (by decide) environment
  simpa [globalCayleyDegreeFourPolynomial,
    globalCayleyNormalizedDegreeFourPolynomial,
    globalCayleyQuarticNormalizationCorrectionPolynomial,
    eCayleyNormalizedH4, environment, coeffEvalExpr, instantiate] using h

/-- Degree-five homogeneous Cayley term on the ORIGINAL face carrier. -/
def globalCayleyDegreeFivePolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face)
    (ePow3 eCayleyData.D *
      eH5 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Degree-six homogeneous Cayley term on the ORIGINAL face carrier. -/
def globalCayleyDegreeSixPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face)
    (ePow2 eCayleyData.D *
      eH6 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- The global cleared deficit is exactly its five homogeneous Cayley terms,
coefficientwise. -/
theorem globalCayleyDeficitPolynomial_coeff_degrees
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (globalCayleyDeficitPolynomial extent face)
      (polyAdd
        (polyAdd
          (polyAdd
            (polyAdd
              (globalCayleyDegreeTwoPolynomial extent face)
              (globalCayleyDegreeThreePolynomial extent face))
            (globalCayleyDegreeFourPolynomial extent face))
          (globalCayleyDegreeFivePolynomial extent face))
        (globalCayleyDegreeSixPolynomial extent face)) := by
  exact RatPolyCoeffEqv.refl _

private theorem actual_expression_identity
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    RingNormaliser.eval (faceActualAtoms extent qs face) globalLeftExpression ≈
      RingNormaliser.eval (faceActualAtoms extent qs face)
        globalDeficitExpression := by
  let atoms := faceActualAtoms extent qs face
  have hleft :
      RingNormaliser.eval atoms globalLeftExpression ≈
        clearedCayleyDenominator (RingNormaliser.eval atoms eCayleyData.D)
            (evalETriple atoms eCayleyData.p) (evalETriple atoms eCayleyData.q)
            (evalETriple atoms eCayleyData.r) (evalETriple atoms eCayleyData.s) *
          (2 + -(2 * atoms 16)) := by
    exact Q'.eqv_of_eq (eval_globalLeftExpression atoms)
  have hright :
      RingNormaliser.eval atoms globalDeficitExpression ≈
        clearedCayleyDeficit (RingNormaliser.eval atoms eCayleyData.D)
          (evalETriple atoms eCayleyData.p) (evalETriple atoms eCayleyData.q)
          (evalETriple atoms eCayleyData.r) (evalETriple atoms eCayleyData.s) := by
    exact Q'.eqv_of_eq (eval_globalDeficitExpression atoms)
  have hpoint :
      clearedCayleyDenominator (RingNormaliser.eval atoms eCayleyData.D)
            (evalETriple atoms eCayleyData.p) (evalETriple atoms eCayleyData.q)
            (evalETriple atoms eCayleyData.r) (evalETriple atoms eCayleyData.s) *
          (2 + -(2 * atoms 16)) ≈
        clearedCayleyDeficit (RingNormaliser.eval atoms eCayleyData.D)
          (evalETriple atoms eCayleyData.p) (evalETriple atoms eCayleyData.q)
          (evalETriple atoms eCayleyData.r) (evalETriple atoms eCayleyData.s) := by
    simpa only [atoms, eCayleyData, eQuaternion, eImaginary, eScale3,
      evalETriple, RingNormaliser.eval, faceActualAtoms, faceStage3Atoms,
      faceStage2Atoms, faceStage1Atoms, facePolynomialAtoms,
      faceEntry0, faceEntry1, faceEntry2, faceEntry3,
      commonChartDenominator, chartDenominator,
      firstClearedTriple, secondClearedTriple, thirdClearedTriple,
      fourthClearedTriple, firstComplement, secondComplement, thirdComplement,
      fourthComplement, chartNumerator, scale3, orientedLinkValue] using
        (original_plaquette_global_cayley_polynomial_cleared extent qs face)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hpoint (Q'.eqv_symm hright))

/-- The two explicit finite-support `RatPoly` probes evaluate equally at every
ORIGINAL unit-link assignment.  This is the direct functional input missing
after the pointwise global identity. -/
theorem global_cayley_ratPoly_eval
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    evalRatPoly (environment qs) (globalCayleyLeftPolynomial extent face) ≈
      evalRatPoly (environment qs)
        (globalCayleyDeficitPolynomial extent face) := by
  exact Q'.eqv_trans _ _ _
    (eval_instantiate (environment qs) (facePolynomialAtoms extent face)
      globalLeftExpression)
    (Q'.eqv_trans _ _ _
      (face_expression_pin extent qs face globalLeftExpression)
      (Q'.eqv_trans _ _ _
        (actual_expression_identity extent qs face)
        (Q'.eqv_symm
          (Q'.eqv_trans _ _ _
            (eval_instantiate (environment qs)
              (facePolynomialAtoms extent face) globalDeficitExpression)
            (face_expression_pin extent qs face globalDeficitExpression)))))

/-! ## 4. Arbitrary-insertion carrier clearing for one raw factor -/

private def factorEnvironment
    (q : PolyQuaternion) (complement : RatPoly) : Nat → RatPoly
  | 0 => q.scalar
  | 1 => q.iPart
  | 2 => q.jPart
  | 3 => q.kPart
  | 4 => complement
  | _ => polyZero

private def factorPolynomial
    (q : PolyQuaternion) (complement : RatPoly) (expression : PE) : RatPoly :=
  coeffEvalExpr (factorEnvironment q complement) expression

private def eQuaternionNorm : PE :=
  .var 0 * .var 0 +
    (.var 1 * .var 1 + (.var 2 * .var 2 + .var 3 * .var 3))

private def eUnitResidual : PE := 1 + -eQuaternionNorm

private def eLocalDenominator : PE := (1 + .var 0) * .var 4

private def eLocalImaginaryNorm : PE :=
  ((.var 4 * .var 1) * (.var 4 * .var 1) +
    (.var 4 * .var 2) * (.var 4 * .var 2)) +
    (.var 4 * .var 3) * (.var 4 * .var 3)

private def eLocalClearedFactor : PE :=
  eLocalDenominator * eLocalDenominator + eLocalImaginaryNorm

private def eLocalNorthClearedFactor : PE :=
  2 * (1 + .var 0) * (.var 4 * .var 4)

private def eLocalNorthCorrection : PE :=
  -(.var 4 * .var 4)

private def eLocalRawScalar : PE :=
  eLocalDenominator * eLocalDenominator + -eLocalImaginaryNorm

private def eLocalRawComponent (coordinate : Nat) : PE :=
  2 * eLocalDenominator * (.var 4 * .var coordinate)

private def eLocalScaledComponent (coordinate : Nat) : PE :=
  eLocalClearedFactor * .var coordinate

private def eLocalScalarCorrection : PE :=
  (.var 4 * .var 4) * (1 + .var 0)

private def eLocalVectorCorrection (coordinate : Nat) : PE :=
  (.var 4 * .var 4) * .var coordinate

/-- The raw common-denominator Cayley factor as a polynomial quaternion. -/
def rawCayleyFactor
    (q : PolyQuaternion) (complement : RatPoly) : PolyQuaternion :=
  ⟨factorPolynomial q complement eLocalRawScalar,
    factorPolynomial q complement (eLocalRawComponent 1),
    factorPolynomial q complement (eLocalRawComponent 2),
    factorPolynomial q complement (eLocalRawComponent 3)⟩

/-- Polynomial scalar multiplying the supplied unit quaternion after one
raw Cayley factor is cleared. -/
def clearedCayleyFactorPolynomial
    (q : PolyQuaternion) (complement : RatPoly) : RatPoly :=
  factorPolynomial q complement eLocalClearedFactor

/-- North-chart form of the cleared scalar factor.  On the unit-quaternion
carrier the cleared factor equals
`2 * (1 + scalar(q)) * complement^2`. -/
def northCayleyFactorPolynomial
    (q : PolyQuaternion) (complement : RatPoly) : RatPoly :=
  factorPolynomial q complement eLocalNorthClearedFactor

private def cayleyQuaternionAtoms
    (q0 q1 q2 q3 : PolyQuaternion) : Nat → RatPoly
  | 0 => q0.scalar
  | 1 => q0.iPart
  | 2 => q0.jPart
  | 3 => q0.kPart
  | 4 => q1.scalar
  | 5 => q1.iPart
  | 6 => q1.jPart
  | 7 => q1.kPart
  | 8 => q2.scalar
  | 9 => q2.iPart
  | 10 => q2.jPart
  | 11 => q2.kPart
  | 12 => q3.scalar
  | 13 => q3.iPart
  | 14 => q3.jPart
  | 15 => q3.kPart
  | _ => polyZero

def cayleyChartDenominatorPolynomial (q : PolyQuaternion) : RatPoly :=
  polyAdd (polySmul 1 polyOne) q.scalar

/-- Coefficientwise expansion of the north-chart factor.  Unlike the
carrier theorem below, this identity uses no unit-quaternion relation. -/
theorem northCayleyFactorPolynomial_coeff_formula
    (q : PolyQuaternion) (complement : RatPoly) :
    RatPolyCoeffEqv
      (northCayleyFactorPolynomial q complement)
      (polyMul
        (polyMul (polySmul 2 polyOne)
          (cayleyChartDenominatorPolynomial q))
        (polyMul complement complement)) :=
  RatPolyCoeffEqv.refl _

def cayleyComplement0Polynomial
    (_q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  polyMul
    (polyMul (cayleyChartDenominatorPolynomial q1)
      (cayleyChartDenominatorPolynomial q2))
    (cayleyChartDenominatorPolynomial q3)

def cayleyComplement1Polynomial
    (q0 _q1 q2 q3 : PolyQuaternion) : RatPoly :=
  polyMul
    (polyMul (cayleyChartDenominatorPolynomial q0)
      (cayleyChartDenominatorPolynomial q2))
    (cayleyChartDenominatorPolynomial q3)

def cayleyComplement2Polynomial
    (q0 q1 _q2 q3 : PolyQuaternion) : RatPoly :=
  polyMul
    (polyMul (cayleyChartDenominatorPolynomial q0)
      (cayleyChartDenominatorPolynomial q1))
    (cayleyChartDenominatorPolynomial q3)

def cayleyComplement3Polynomial
    (q0 q1 q2 _q3 : PolyQuaternion) : RatPoly :=
  polyMul
    (polyMul (cayleyChartDenominatorPolynomial q0)
      (cayleyChartDenominatorPolynomial q1))
    (cayleyChartDenominatorPolynomial q2)

def clearedCayleyScaleProduct
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  polyMul
    (polyMul
      (polyMul
        (clearedCayleyFactorPolynomial q0
          (cayleyComplement0Polynomial q0 q1 q2 q3))
        (clearedCayleyFactorPolynomial q1
          (cayleyComplement1Polynomial q0 q1 q2 q3)))
      (clearedCayleyFactorPolynomial q2
        (cayleyComplement2Polynomial q0 q1 q2 q3)))
    (clearedCayleyFactorPolynomial q3
      (cayleyComplement3Polynomial q0 q1 q2 q3))

def compiledCayleyDenominatorPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    globalDenominatorExpression

private def eCayleyComplement0 : PE :=
  let q1 := eQuaternion 4
  let q2 := eQuaternion 8
  let q3 := eQuaternion 12
  (((1 + q1.r) * (1 + q2.r)) * (1 + q3.r))

private def eCayleyComplement1 : PE :=
  let q0 := eQuaternion 0
  let q2 := eQuaternion 8
  let q3 := eQuaternion 12
  (((1 + q0.r) * (1 + q2.r)) * (1 + q3.r))

private def eCayleyComplement2 : PE :=
  let q0 := eQuaternion 0
  let q1 := eQuaternion 4
  let q3 := eQuaternion 12
  (((1 + q0.r) * (1 + q1.r)) * (1 + q3.r))

private def eCayleyComplement3 : PE :=
  let q0 := eQuaternion 0
  let q1 := eQuaternion 4
  let q2 := eQuaternion 8
  (((1 + q0.r) * (1 + q1.r)) * (1 + q2.r))

private def eLocalClearedFactorOf
    (q : EQuaternion) (complement : PE) : PE :=
  eClearedFactor ((1 + q.r) * complement)
    (eScale3 complement (eImaginary q))

private def eLocalRawFactorOf
    (q : EQuaternion) (complement : PE) : PolyQuaternionExpr :=
  let D := (1 + q.r) * complement
  let a := eScale3 complement (eImaginary q)
  ⟨ePow2 D + -eNorm3 a,
    2 * D * a.x,
    2 * D * a.y,
    2 * D * a.z⟩

private def eHamiltonMul
    (left right : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨(left.scalar * right.scalar + -(left.iPart * right.iPart)) +
      (-(left.jPart * right.jPart) + -(left.kPart * right.kPart)),
    (left.scalar * right.iPart + left.iPart * right.scalar) +
      (left.jPart * right.kPart + -(left.kPart * right.jPart)),
    (left.scalar * right.jPart + -(left.iPart * right.kPart)) +
      (left.jPart * right.scalar + left.kPart * right.iPart),
    (left.scalar * right.kPart + left.iPart * right.jPart) +
      (-(left.jPart * right.iPart) + left.kPart * right.scalar)⟩

private def eCayleyRawWord : PolyQuaternionExpr :=
  eHamiltonMul
    (eHamiltonMul
      (eHamiltonMul
        (eLocalRawFactorOf (eQuaternion 0) eCayleyComplement0)
        (eLocalRawFactorOf (eQuaternion 4) eCayleyComplement1))
      (eLocalRawFactorOf (eQuaternion 8) eCayleyComplement2))
    (eLocalRawFactorOf (eQuaternion 12) eCayleyComplement3)

private def coeffEvalPolyQuaternionExpr
    (atoms : Nat → RatPoly) (q : PolyQuaternionExpr) : PolyQuaternion :=
  ⟨coeffEvalExpr atoms q.scalar,
    coeffEvalExpr atoms q.iPart,
    coeffEvalExpr atoms q.jPart,
    coeffEvalExpr atoms q.kPart⟩

private theorem coeffEvalPolyQuaternionExpr_mul
    (atoms : Nat → RatPoly) (left right : PolyQuaternionExpr) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul
        (coeffEvalPolyQuaternionExpr atoms left)
        (coeffEvalPolyQuaternionExpr atoms right))
      (coeffEvalPolyQuaternionExpr atoms
        (PolyQuaternionExpr.mul left right)) :=
  PolyQuaternionCoeffEqv.refl _

private theorem coeffEvalPolyQuaternionExpr_hamiltonMul
    (atoms : Nat → RatPoly) (left right : PolyQuaternionExpr) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul
        (coeffEvalPolyQuaternionExpr atoms left)
        (coeffEvalPolyQuaternionExpr atoms right))
      (coeffEvalPolyQuaternionExpr atoms (eHamiltonMul left right)) := by
  let environment : Nat → RatPoly
    | 0 => coeffEvalExpr atoms left.scalar
    | 1 => coeffEvalExpr atoms left.iPart
    | 2 => coeffEvalExpr atoms left.jPart
    | 3 => coeffEvalExpr atoms left.kPart
    | 4 => coeffEvalExpr atoms right.scalar
    | 5 => coeffEvalExpr atoms right.iPart
    | 6 => coeffEvalExpr atoms right.jPart
    | 7 => coeffEvalExpr atoms right.kPart
    | _ => polyZero
  let ordinary := PolyQuaternionExpr.mul
    (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)
  let hamilton := eHamiltonMul
    (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)
  have h : PolyQuaternionCoeffEqv
      (coeffEvalPolyQuaternionExpr environment ordinary)
      (coeffEvalPolyQuaternionExpr environment hamilton) :=
    ⟨coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) environment,
      coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) environment,
      coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) environment,
      coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) environment⟩
  simpa [environment, ordinary, hamilton, eHamiltonMul,
    coeffEvalPolyQuaternionExpr, PolyQuaternionExpr.mul,
    PolyQuaternionExpr.coordinate, coeffEvalExpr] using h

private theorem coeffEvalPolyQuaternionExpr_eqv_of_normalize_eq
    (atoms : Nat → RatPoly) (left right : PolyQuaternionExpr)
    (hscalar : normalize left.scalar = normalize right.scalar)
    (hiPart : normalize left.iPart = normalize right.iPart)
    (hjPart : normalize left.jPart = normalize right.jPart)
    (hkPart : normalize left.kPart = normalize right.kPart) :
    PolyQuaternionCoeffEqv
      (coeffEvalPolyQuaternionExpr atoms left)
      (coeffEvalPolyQuaternionExpr atoms right) :=
  ⟨coeffEvalExpr_eqv_of_normalize_eq _ _ hscalar atoms,
    coeffEvalExpr_eqv_of_normalize_eq _ _ hiPart atoms,
    coeffEvalExpr_eqv_of_normalize_eq _ _ hjPart atoms,
    coeffEvalExpr_eqv_of_normalize_eq _ _ hkPart atoms⟩

private theorem coeffEvalPolyQuaternionExpr_hamiltonMul_congr
    (atoms : Nat → RatPoly)
    {left left' right right' : PolyQuaternionExpr}
    (hleft : PolyQuaternionCoeffEqv
      (coeffEvalPolyQuaternionExpr atoms left)
      (coeffEvalPolyQuaternionExpr atoms left'))
    (hright : PolyQuaternionCoeffEqv
      (coeffEvalPolyQuaternionExpr atoms right)
      (coeffEvalPolyQuaternionExpr atoms right')) :
    PolyQuaternionCoeffEqv
      (coeffEvalPolyQuaternionExpr atoms (eHamiltonMul left right))
      (coeffEvalPolyQuaternionExpr atoms (eHamiltonMul left' right')) :=
  (coeffEvalPolyQuaternionExpr_hamiltonMul atoms left right).symm.trans
    ((hleft.mul hright).trans
      (coeffEvalPolyQuaternionExpr_hamiltonMul atoms left' right'))

def rawCayleyWordPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (rawCayleyFactor q0
          (cayleyComplement0Polynomial q0 q1 q2 q3))
        (rawCayleyFactor q1
          (cayleyComplement1Polynomial q0 q1 q2 q3)))
      (rawCayleyFactor q2
        (cayleyComplement2Polynomial q0 q1 q2 q3)))
    (rawCayleyFactor q3
      (cayleyComplement3Polynomial q0 q1 q2 q3))

def compiledCayleyRawScalarPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    eCayleyRawWord.scalar

/-- The generic raw four-factor word scalar is its direct expression
compilation, coefficientwise. -/
theorem rawCayleyWordPolynomial_scalar_coeff_compiled
    (q0 q1 q2 q3 : PolyQuaternion) :
    RatPolyCoeffEqv (rawCayleyWordPolynomial q0 q1 q2 q3).scalar
      (compiledCayleyRawScalarPolynomial q0 q1 q2 q3) := by
  let atoms := cayleyQuaternionAtoms q0 q1 q2 q3
  let expression0 := eLocalRawFactorOf (eQuaternion 0) eCayleyComplement0
  let expression1 := eLocalRawFactorOf (eQuaternion 4) eCayleyComplement1
  let expression2 := eLocalRawFactorOf (eQuaternion 8) eCayleyComplement2
  let expression3 := eLocalRawFactorOf (eQuaternion 12) eCayleyComplement3
  have h0 : PolyQuaternionCoeffEqv
      (rawCayleyFactor q0
        (cayleyComplement0Polynomial q0 q1 q2 q3))
      (coeffEvalPolyQuaternionExpr atoms expression0) :=
    PolyQuaternionCoeffEqv.refl _
  have h1 : PolyQuaternionCoeffEqv
      (rawCayleyFactor q1
        (cayleyComplement1Polynomial q0 q1 q2 q3))
      (coeffEvalPolyQuaternionExpr atoms expression1) :=
    PolyQuaternionCoeffEqv.refl _
  have h2 : PolyQuaternionCoeffEqv
      (rawCayleyFactor q2
        (cayleyComplement2Polynomial q0 q1 q2 q3))
      (coeffEvalPolyQuaternionExpr atoms expression2) :=
    PolyQuaternionCoeffEqv.refl _
  have h3 : PolyQuaternionCoeffEqv
      (rawCayleyFactor q3
        (cayleyComplement3Polynomial q0 q1 q2 q3))
      (coeffEvalPolyQuaternionExpr atoms expression3) :=
    PolyQuaternionCoeffEqv.refl _
  have hword := PolyQuaternionCoeffEqv.mul
    (PolyQuaternionCoeffEqv.mul
      (PolyQuaternionCoeffEqv.mul h0 h1) h2) h3
  have h01 := coeffEvalPolyQuaternionExpr_hamiltonMul atoms expression0 expression1
  have h012 := (PolyQuaternionCoeffEqv.mul h01
    (PolyQuaternionCoeffEqv.refl
      (coeffEvalPolyQuaternionExpr atoms expression2))).trans
    (coeffEvalPolyQuaternionExpr_hamiltonMul atoms
      (eHamiltonMul expression0 expression1) expression2)
  have h0123 := (PolyQuaternionCoeffEqv.mul h012
    (PolyQuaternionCoeffEqv.refl
      (coeffEvalPolyQuaternionExpr atoms expression3))).trans
    (coeffEvalPolyQuaternionExpr_hamiltonMul atoms
      (eHamiltonMul
        (eHamiltonMul expression0 expression1) expression2)
      expression3)
  change RatPolyCoeffEqv
    (rawCayleyWordPolynomial q0 q1 q2 q3).scalar
    (coeffEvalPolyQuaternionExpr atoms eCayleyRawWord).scalar
  simpa [expression0, expression1, expression2, expression3,
    eCayleyRawWord] using (hword.trans h0123).scalar

/-- Generic four-polynomial-quaternion compilation of the complete cleared
Cayley deficit. -/
def compiledCayleyDeficitPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    globalDeficitExpression

/-- Generic homogeneous degree-two Cayley piece. -/
def compiledCayleyDegreeTwoPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    (ePow6 eCayleyData.D *
      eH2 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Generic homogeneous degree-three Cayley piece. -/
def compiledCayleyDegreeThreePolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    (ePow5 eCayleyData.D *
      eH3 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Generic homogeneous degree-four Cayley piece. -/
def compiledCayleyDegreeFourPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    (ePow4 eCayleyData.D *
      eH4 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Generic homogeneous degree-five Cayley piece. -/
def compiledCayleyDegreeFivePolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    (ePow3 eCayleyData.D *
      eH5 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Generic homogeneous degree-six Cayley piece. -/
def compiledCayleyDegreeSixPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (cayleyQuaternionAtoms q0 q1 q2 q3)
    (ePow2 eCayleyData.D *
      eH6 eCayleyData.p eCayleyData.q eCayleyData.r eCayleyData.s)

/-- Generic degree-three-through-six Cayley remainder. -/
def compiledCayleyHigherPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  polyAdd
    (polyAdd
      (compiledCayleyDegreeThreePolynomial q0 q1 q2 q3)
      (compiledCayleyDegreeFourPolynomial q0 q1 q2 q3))
    (polyAdd
      (compiledCayleyDegreeFivePolynomial q0 q1 q2 q3)
      (compiledCayleyDegreeSixPolynomial q0 q1 q2 q3))

/-- The generic compiled deficit is exactly the sum of its five homogeneous
pieces. -/
theorem compiledCayleyDeficitPolynomial_coeff_degrees
    (q0 q1 q2 q3 : PolyQuaternion) :
    RatPolyCoeffEqv (compiledCayleyDeficitPolynomial q0 q1 q2 q3)
      (polyAdd
        (polyAdd
          (polyAdd
            (polyAdd
              (compiledCayleyDegreeTwoPolynomial q0 q1 q2 q3)
              (compiledCayleyDegreeThreePolynomial q0 q1 q2 q3))
            (compiledCayleyDegreeFourPolynomial q0 q1 q2 q3))
          (compiledCayleyDegreeFivePolynomial q0 q1 q2 q3))
        (compiledCayleyDegreeSixPolynomial q0 q1 q2 q3)) :=
  RatPolyCoeffEqv.refl _

def globalCayleyRawScalarPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  instantiate (facePolynomialAtoms extent face) eCayleyRawWord.scalar

/-- The ORIGINAL face raw-scalar probe is the generic four-quaternion raw
word scalar compilation. -/
theorem globalCayleyRawScalarPolynomial_coeff_compiled
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (globalCayleyRawScalarPolynomial extent face)
      (compiledCayleyRawScalarPolynomial
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry0 face))
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry1 face))
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry2 face))
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry3 face))) := by
  simpa [globalCayleyRawScalarPolynomial,
    compiledCayleyRawScalarPolynomial, cayleyQuaternionAtoms,
    facePolynomialAtoms] using
      (instantiate_coeffEvalExpr (facePolynomialAtoms extent face)
        eCayleyRawWord.scalar)

private def eFourVector (a b c d : ETriple) : PE :=
  eDot3 a b * eDot3 c d +
    -(eDot3 (eCross3 a b) (eCross3 c d))

private def eFourScalarSubstitution : Nat → PE
  | 0 => ePow2 eCayleyData.D + -eNorm3 eCayleyData.p
  | 1 => ePow2 eCayleyData.D + -eNorm3 eCayleyData.q
  | 2 => ePow2 eCayleyData.D + -eNorm3 eCayleyData.r
  | 3 => ePow2 eCayleyData.D + -eNorm3 eCayleyData.s
  | 4 => 2 * eCayleyData.D * eCayleyData.p.x
  | 5 => 2 * eCayleyData.D * eCayleyData.p.y
  | 6 => 2 * eCayleyData.D * eCayleyData.p.z
  | 7 => 2 * eCayleyData.D * eCayleyData.q.x
  | 8 => 2 * eCayleyData.D * eCayleyData.q.y
  | 9 => 2 * eCayleyData.D * eCayleyData.q.z
  | 10 => 2 * eCayleyData.D * eCayleyData.r.x
  | 11 => 2 * eCayleyData.D * eCayleyData.r.y
  | 12 => 2 * eCayleyData.D * eCayleyData.r.z
  | 13 => 2 * eCayleyData.D * eCayleyData.s.x
  | 14 => 2 * eCayleyData.D * eCayleyData.s.y
  | _ => 2 * eCayleyData.D * eCayleyData.s.z

private def eRawScalarFormulaExpanded : PE :=
  substituteExpr eFourScalarSubstitution fourScalarRightExpression

private def eInvariantDenominatorForData : PE :=
  eInvariantDenominator eCayleyData.D
    (eNorm3 eCayleyData.p) (eNorm3 eCayleyData.q)
    (eNorm3 eCayleyData.r) (eNorm3 eCayleyData.s)

private def eInvariantRawScalarForData : PE :=
  eInvariantRawScalar eCayleyData.D
    (eNorm3 eCayleyData.p) (eNorm3 eCayleyData.q)
    (eNorm3 eCayleyData.r) (eNorm3 eCayleyData.s)
    (eDot3 eCayleyData.p eCayleyData.q)
    (eDot3 eCayleyData.p eCayleyData.r)
    (eDot3 eCayleyData.p eCayleyData.s)
    (eDot3 eCayleyData.q eCayleyData.r)
    (eDot3 eCayleyData.q eCayleyData.s)
    (eDot3 eCayleyData.r eCayleyData.s)
    (eDet3 eCayleyData.p eCayleyData.q eCayleyData.r)
    (eDet3 eCayleyData.p eCayleyData.q eCayleyData.s)
    (eDet3 eCayleyData.p eCayleyData.r eCayleyData.s)
    (eDet3 eCayleyData.q eCayleyData.r eCayleyData.s)
    (eFourVector eCayleyData.p eCayleyData.q
      eCayleyData.r eCayleyData.s)

private def eInvariantDeficitForData : PE :=
  eInvariantDeficit eCayleyData.D
    (eNorm3 eCayleyData.p) (eNorm3 eCayleyData.q)
    (eNorm3 eCayleyData.r) (eNorm3 eCayleyData.s)
    (eDot3 eCayleyData.p eCayleyData.q)
    (eDot3 eCayleyData.p eCayleyData.r)
    (eDot3 eCayleyData.p eCayleyData.s)
    (eDot3 eCayleyData.q eCayleyData.r)
    (eDot3 eCayleyData.q eCayleyData.s)
    (eDot3 eCayleyData.r eCayleyData.s)
    (eDet3 eCayleyData.p eCayleyData.q eCayleyData.r)
    (eDet3 eCayleyData.p eCayleyData.q eCayleyData.s)
    (eDet3 eCayleyData.p eCayleyData.r eCayleyData.s)
    (eDet3 eCayleyData.q eCayleyData.r eCayleyData.s)
    (eFourVector eCayleyData.p eCayleyData.q
      eCayleyData.r eCayleyData.s)

private def eInvariantData : Nat → PE
  | 0 => eCayleyData.D
  | 1 => eNorm3 eCayleyData.p
  | 2 => eNorm3 eCayleyData.q
  | 3 => eNorm3 eCayleyData.r
  | 4 => eNorm3 eCayleyData.s
  | 5 => eDot3 eCayleyData.p eCayleyData.q
  | 6 => eDot3 eCayleyData.p eCayleyData.r
  | 7 => eDot3 eCayleyData.p eCayleyData.s
  | 8 => eDot3 eCayleyData.q eCayleyData.r
  | 9 => eDot3 eCayleyData.q eCayleyData.s
  | 10 => eDot3 eCayleyData.r eCayleyData.s
  | 11 => eDet3 eCayleyData.p eCayleyData.q eCayleyData.r
  | 12 => eDet3 eCayleyData.p eCayleyData.q eCayleyData.s
  | 13 => eDet3 eCayleyData.p eCayleyData.r eCayleyData.s
  | 14 => eDet3 eCayleyData.q eCayleyData.r eCayleyData.s
  | _ => eFourVector eCayleyData.p eCayleyData.q
      eCayleyData.r eCayleyData.s

private def eCoordinateTriple (offset : Nat) : ETriple :=
  ⟨.var offset, .var (offset + 1), .var (offset + 2)⟩

private def eCommonRawFactor (D : PE) (a : ETriple) : PolyQuaternionExpr :=
  ⟨ePow2 D + -eNorm3 a,
    2 * D * a.x,
    2 * D * a.y,
    2 * D * a.z⟩

private def eCoordinateCommonRawWord : PolyQuaternionExpr :=
  let D : PE := .var 0
  let a := eCoordinateTriple 1
  let b := eCoordinateTriple 4
  let c := eCoordinateTriple 7
  let d := eCoordinateTriple 10
  eHamiltonMul
    (eHamiltonMul
      (eHamiltonMul (eCommonRawFactor D a) (eCommonRawFactor D b))
      (eCommonRawFactor D c))
    (eCommonRawFactor D d)

private def eCoordinateInvariantRawScalar : PE :=
  let D : PE := .var 0
  let a := eCoordinateTriple 1
  let b := eCoordinateTriple 4
  let c := eCoordinateTriple 7
  let d := eCoordinateTriple 10
  eInvariantRawScalar D
    (eNorm3 a) (eNorm3 b) (eNorm3 c) (eNorm3 d)
    (eDot3 a b) (eDot3 a c) (eDot3 a d)
    (eDot3 b c) (eDot3 b d) (eDot3 c d)
    (eDet3 a b c) (eDet3 a b d) (eDet3 a c d) (eDet3 b c d)
    (eFourVector a b c d)

private def eCoordinateGlobalDenominator : PE :=
  let D : PE := .var 0
  let a := eCoordinateTriple 1
  let b := eCoordinateTriple 4
  let c := eCoordinateTriple 7
  let d := eCoordinateTriple 10
  eClearedDenominator D a b c d

private def eCoordinateInvariantDenominator : PE :=
  let D : PE := .var 0
  let a := eCoordinateTriple 1
  let b := eCoordinateTriple 4
  let c := eCoordinateTriple 7
  let d := eCoordinateTriple 10
  eInvariantDenominator D
    (eNorm3 a) (eNorm3 b) (eNorm3 c) (eNorm3 d)

private def eCoordinateGlobalDeficit : PE :=
  let D : PE := .var 0
  let a := eCoordinateTriple 1
  let b := eCoordinateTriple 4
  let c := eCoordinateTriple 7
  let d := eCoordinateTriple 10
  eClearedDeficit D a b c d

private def eCoordinateInvariantDeficit : PE :=
  let D : PE := .var 0
  let a := eCoordinateTriple 1
  let b := eCoordinateTriple 4
  let c := eCoordinateTriple 7
  let d := eCoordinateTriple 10
  eInvariantDeficit D
    (eNorm3 a) (eNorm3 b) (eNorm3 c) (eNorm3 d)
    (eDot3 a b) (eDot3 a c) (eDot3 a d)
    (eDot3 b c) (eDot3 b d) (eDot3 c d)
    (eDet3 a b c) (eDet3 a b d) (eDet3 a c d) (eDet3 b c d)
    (eFourVector a b c d)

set_option maxHeartbeats 2000000 in
private theorem eCoordinateCommonRawWord_invariant_normal :
    normalize eCoordinateCommonRawWord.scalar =
      normalize eCoordinateInvariantRawScalar := by
  decide

private theorem eCoordinateDenominator_invariant_normal :
    normalize eCoordinateGlobalDenominator =
      normalize eCoordinateInvariantDenominator := by
  decide

set_option maxHeartbeats 2000000 in
private theorem eCoordinateDeficit_invariant_normal :
    normalize eCoordinateGlobalDeficit =
      normalize eCoordinateInvariantDeficit := by
  decide

private def eCoordinateData : Nat → PE
  | 0 => eCayleyData.D
  | 1 => eCayleyData.p.x
  | 2 => eCayleyData.p.y
  | 3 => eCayleyData.p.z
  | 4 => eCayleyData.q.x
  | 5 => eCayleyData.q.y
  | 6 => eCayleyData.q.z
  | 7 => eCayleyData.r.x
  | 8 => eCayleyData.r.y
  | 9 => eCayleyData.r.z
  | 10 => eCayleyData.s.x
  | 11 => eCayleyData.s.y
  | _ => eCayleyData.s.z

private def eCommonRawWordForData : PolyQuaternionExpr :=
  eHamiltonMul
    (eHamiltonMul
      (eHamiltonMul
        (eCommonRawFactor eCayleyData.D eCayleyData.p)
        (eCommonRawFactor eCayleyData.D eCayleyData.q))
      (eCommonRawFactor eCayleyData.D eCayleyData.r))
    (eCommonRawFactor eCayleyData.D eCayleyData.s)

private theorem eCoordinateCommonRawWord_scalar_substitute :
    substituteExpr eCoordinateData eCoordinateCommonRawWord.scalar =
      eCommonRawWordForData.scalar := rfl

private theorem eCoordinateDenominator_substitute :
    substituteExpr eCoordinateData eCoordinateGlobalDenominator =
      globalDenominatorExpression := rfl

private theorem eCoordinateInvariantDenominator_substitute :
    substituteExpr eCoordinateData eCoordinateInvariantDenominator =
      eInvariantDenominatorForData := rfl

private theorem eCoordinateDeficit_substitute :
    substituteExpr eCoordinateData eCoordinateGlobalDeficit =
      globalDeficitExpression := rfl

private theorem eCoordinateInvariantDeficit_substitute :
    substituteExpr eCoordinateData eCoordinateInvariantDeficit =
      eInvariantDeficitForData := rfl

private theorem eCoordinateInvariantRawScalar_substitute :
    substituteExpr eCoordinateData eCoordinateInvariantRawScalar =
      eInvariantRawScalarForData := rfl

private theorem eInvariantLeft_substitute :
    substituteExpr eInvariantData invariantLeftExpression =
      (2 * eInvariantDenominatorForData +
        -(2 * eInvariantRawScalarForData)) := rfl

private theorem eInvariantDeficit_substitute :
    substituteExpr eInvariantData invariantDeficitExpression =
      eInvariantDeficitForData := rfl

private def eCayleyRawDeficitRepresentation : PE :=
  2 * globalDenominatorExpression + -(2 * eCayleyRawWord.scalar)

private def eCayleyOriginalLeftAbstract : PE :=
  .var 0 * (2 + -(2 * .var 1))

private def eCayleyOriginalDeficitAbstract : PE :=
  2 * .var 0 + -(2 * (.var 0 * .var 1))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
private theorem compiledGlobalDeficit_coeff_raw
    (atoms : Nat → RatPoly) :
    RatPolyCoeffEqv (coeffEvalExpr atoms globalDeficitExpression)
      (coeffEvalExpr atoms eCayleyRawDeficitRepresentation) := by
  let local0 := eLocalRawFactorOf (eQuaternion 0) eCayleyComplement0
  let local1 := eLocalRawFactorOf (eQuaternion 4) eCayleyComplement1
  let local2 := eLocalRawFactorOf (eQuaternion 8) eCayleyComplement2
  let local3 := eLocalRawFactorOf (eQuaternion 12) eCayleyComplement3
  let common0 := eCommonRawFactor eCayleyData.D eCayleyData.p
  let common1 := eCommonRawFactor eCayleyData.D eCayleyData.q
  let common2 := eCommonRawFactor eCayleyData.D eCayleyData.r
  let common3 := eCommonRawFactor eCayleyData.D eCayleyData.s
  have h0 := coeffEvalPolyQuaternionExpr_eqv_of_normalize_eq
    atoms local0 common0 (by decide) (by decide) (by decide) (by decide)
  have h1 := coeffEvalPolyQuaternionExpr_eqv_of_normalize_eq
    atoms local1 common1 (by decide) (by decide) (by decide) (by decide)
  have h2 := coeffEvalPolyQuaternionExpr_eqv_of_normalize_eq
    atoms local2 common2 (by decide) (by decide) (by decide) (by decide)
  have h3 := coeffEvalPolyQuaternionExpr_eqv_of_normalize_eq
    atoms local3 common3 (by decide) (by decide) (by decide) (by decide)
  have h01 := coeffEvalPolyQuaternionExpr_hamiltonMul_congr atoms h0 h1
  have h012 := coeffEvalPolyQuaternionExpr_hamiltonMul_congr atoms h01 h2
  have h0123 := coeffEvalPolyQuaternionExpr_hamiltonMul_congr atoms h012 h3
  have hlocal : PolyQuaternionCoeffEqv
      (coeffEvalPolyQuaternionExpr atoms eCayleyRawWord)
      (coeffEvalPolyQuaternionExpr atoms eCommonRawWordForData) := by
    simpa [local0, local1, local2, local3, common0, common1, common2,
      common3, eCayleyRawWord, eCommonRawWordForData] using h0123
  have hcoordinateBase := coeffEvalExpr_eqv_of_normalize_eq _ _
    eCoordinateCommonRawWord_invariant_normal
    (fun index => coeffEvalExpr atoms (eCoordinateData index))
  have hcoordinate : RatPolyCoeffEqv
      (coeffEvalExpr atoms eCommonRawWordForData.scalar)
      (coeffEvalExpr atoms eInvariantRawScalarForData) := by
    have hsub := (coeffEvalExpr_substitute atoms eCoordinateData
      eCoordinateCommonRawWord.scalar).trans
      (hcoordinateBase.trans
        (coeffEvalExpr_substitute atoms eCoordinateData
          eCoordinateInvariantRawScalar).symm)
    rw [eCoordinateCommonRawWord_scalar_substitute,
      eCoordinateInvariantRawScalar_substitute] at hsub
    exact hsub
  have hraw := hlocal.scalar.trans hcoordinate
  have hden : RatPolyCoeffEqv
      (coeffEvalExpr atoms globalDenominatorExpression)
      (coeffEvalExpr atoms eInvariantDenominatorForData) := by
    have hbase := coeffEvalExpr_eqv_of_normalize_eq _ _
      eCoordinateDenominator_invariant_normal
      (fun index => coeffEvalExpr atoms (eCoordinateData index))
    have hsub := (coeffEvalExpr_substitute atoms eCoordinateData
      eCoordinateGlobalDenominator).trans
      (hbase.trans
        (coeffEvalExpr_substitute atoms eCoordinateData
          eCoordinateInvariantDenominator).symm)
    rw [eCoordinateDenominator_substitute,
      eCoordinateInvariantDenominator_substitute] at hsub
    exact hsub
  have hdeficit : RatPolyCoeffEqv
      (coeffEvalExpr atoms globalDeficitExpression)
      (coeffEvalExpr atoms eInvariantDeficitForData) := by
    have hbase := coeffEvalExpr_eqv_of_normalize_eq _ _
      eCoordinateDeficit_invariant_normal
      (fun index => coeffEvalExpr atoms (eCoordinateData index))
    have hsub := (coeffEvalExpr_substitute atoms eCoordinateData
      eCoordinateGlobalDeficit).trans
      (hbase.trans
        (coeffEvalExpr_substitute atoms eCoordinateData
          eCoordinateInvariantDeficit).symm)
    rw [eCoordinateDeficit_substitute,
      eCoordinateInvariantDeficit_substitute] at hsub
    exact hsub
  have hinvariantBase := coeffEvalExpr_eqv_of_normalize_eq _ _
    invariant_normal (fun index => coeffEvalExpr atoms (eInvariantData index))
  have hinvariant : RatPolyCoeffEqv
      (coeffEvalExpr atoms
        (2 * eInvariantDenominatorForData +
          -(2 * eInvariantRawScalarForData)))
      (coeffEvalExpr atoms eInvariantDeficitForData) := by
    have hsub := (coeffEvalExpr_substitute atoms eInvariantData
      invariantLeftExpression).trans
      (hinvariantBase.trans
        (coeffEvalExpr_substitute atoms eInvariantData
          invariantDeficitExpression).symm)
    rw [eInvariantLeft_substitute, eInvariantDeficit_substitute] at hsub
    exact hsub
  have hrepresentation : RatPolyCoeffEqv
      (coeffEvalExpr atoms eCayleyRawDeficitRepresentation)
      (coeffEvalExpr atoms
        (2 * eInvariantDenominatorForData +
          -(2 * eInvariantRawScalarForData))) :=
    RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul
        (RatPolyCoeffEqv.refl (coeffEvalExpr atoms 2)) hden)
      (RatPolyCoeffEqv.neg
        (RatPolyCoeffEqv.mul
          (RatPolyCoeffEqv.refl (coeffEvalExpr atoms 2)) hraw))
  exact hdeficit.trans (hinvariant.symm.trans hrepresentation.symm)

/-- The generic compiled Cayley deficit is coefficientwise twice the compiled
denominator minus twice the compiled raw-word scalar. -/
theorem compiledCayleyDeficitPolynomial_coeff_raw
    (q0 q1 q2 q3 : PolyQuaternion) :
    RatPolyCoeffEqv (compiledCayleyDeficitPolynomial q0 q1 q2 q3)
      (polyAdd
        (polyMul (polySmul (Q'.ofInt 2) polyOne)
          (compiledCayleyDenominatorPolynomial q0 q1 q2 q3))
        (polyNeg
          (polyMul (polySmul (Q'.ofInt 2) polyOne)
            (compiledCayleyRawScalarPolynomial q0 q1 q2 q3)))) := by
  let atoms := cayleyQuaternionAtoms q0 q1 q2 q3
  simpa [compiledCayleyDeficitPolynomial,
    compiledCayleyDenominatorPolynomial,
    compiledCayleyRawScalarPolynomial,
    eCayleyRawDeficitRepresentation, atoms, coeffEvalExpr] using
      (compiledGlobalDeficit_coeff_raw atoms)

/-- The global cleared deficit is coefficientwise twice the cleared
denominator minus twice the raw common-denominator word scalar. -/
theorem globalCayleyDeficitPolynomial_coeff_raw
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (globalCayleyDeficitPolynomial extent face)
      (polyAdd
        (polyMul (polyConst 2)
          (globalCayleyDenominatorPolynomial extent face))
        (polyNeg
          (polyMul (polyConst 2)
            (globalCayleyRawScalarPolynomial extent face)))) := by
  let atoms := facePolynomialAtoms extent face
  have hleft := instantiate_coeffEvalExpr atoms globalDeficitExpression
  have hidentity := compiledGlobalDeficit_coeff_raw atoms
  have hright := instantiate_coeffEvalExpr atoms eCayleyRawDeficitRepresentation
  have h := hleft.trans (hidentity.trans hright.symm)
  simpa [globalCayleyDeficitPolynomial, globalCayleyDenominatorPolynomial,
    globalCayleyRawScalarPolynomial, eCayleyRawDeficitRepresentation,
    instantiate, atoms] using h

/-- The cleared left side is coefficientwise twice the shared denominator
minus twice that denominator times the ORIGINAL plaquette scalar. -/
theorem globalCayleyLeftPolynomial_coeff_original
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (globalCayleyLeftPolynomial extent face)
      (polyAdd
        (polyMul (polyConst 2)
          (globalCayleyDenominatorPolynomial extent face))
        (polyNeg
          (polyMul (polyConst 2)
            (polyMul (globalCayleyDenominatorPolynomial extent face)
              (correctedSlabPlaquettePolynomial extent face).scalar)))) := by
  let denominator := globalCayleyDenominatorPolynomial extent face
  let plaquette := (correctedSlabPlaquettePolynomial extent face).scalar
  let environment : Nat → RatPoly
    | 0 => denominator
    | 1 => plaquette
    | _ => polyZero
  have hshape : RatPolyCoeffEqv (globalCayleyLeftPolynomial extent face)
      (polyMul denominator
        (polyAdd (polyConst 2)
          (polyNeg (polyMul (polyConst 2) plaquette)))) := by
    exact RatPolyCoeffEqv.refl _
  have hleft := instantiate_coeffEvalExpr environment
    eCayleyOriginalLeftAbstract
  have hidentity := coeffEvalExpr_eqv_of_normalize_eq
    eCayleyOriginalLeftAbstract eCayleyOriginalDeficitAbstract
    (by decide) environment
  have hright := instantiate_coeffEvalExpr environment
    eCayleyOriginalDeficitAbstract
  have habstract := hleft.trans (hidentity.trans hright.symm)
  have hexpanded : RatPolyCoeffEqv
      (polyMul denominator
        (polyAdd (polyConst 2)
          (polyNeg (polyMul (polyConst 2) plaquette))))
      (polyAdd (polyMul (polyConst 2) denominator)
        (polyNeg
          (polyMul (polyConst 2) (polyMul denominator plaquette)))) := by
    simpa [eCayleyOriginalLeftAbstract, eCayleyOriginalDeficitAbstract,
      environment, instantiate] using habstract
  exact hshape.trans hexpanded

set_option maxHeartbeats 2000000 in
/-- The product of the four local cleared factors is exactly the shared
global cleared denominator, coefficientwise. -/
theorem clearedCayleyScaleProduct_coeff_compiled
    (q0 q1 q2 q3 : PolyQuaternion) :
    RatPolyCoeffEqv (clearedCayleyScaleProduct q0 q1 q2 q3)
      (compiledCayleyDenominatorPolynomial q0 q1 q2 q3) := by
  let atoms := cayleyQuaternionAtoms q0 q1 q2 q3
  have h0 : RatPolyCoeffEqv
      (clearedCayleyFactorPolynomial q0
        (cayleyComplement0Polynomial q0 q1 q2 q3))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.p)) := by
    change RatPolyCoeffEqv
      (coeffEvalExpr atoms
        (eLocalClearedFactorOf (eQuaternion 0) eCayleyComplement0))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.p))
    exact coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) atoms
  have h1 : RatPolyCoeffEqv
      (clearedCayleyFactorPolynomial q1
        (cayleyComplement1Polynomial q0 q1 q2 q3))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.q)) := by
    change RatPolyCoeffEqv
      (coeffEvalExpr atoms
        (eLocalClearedFactorOf (eQuaternion 4) eCayleyComplement1))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.q))
    exact coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) atoms
  have h2 : RatPolyCoeffEqv
      (clearedCayleyFactorPolynomial q2
        (cayleyComplement2Polynomial q0 q1 q2 q3))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.r)) := by
    change RatPolyCoeffEqv
      (coeffEvalExpr atoms
        (eLocalClearedFactorOf (eQuaternion 8) eCayleyComplement2))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.r))
    exact coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) atoms
  have h3 : RatPolyCoeffEqv
      (clearedCayleyFactorPolynomial q3
        (cayleyComplement3Polynomial q0 q1 q2 q3))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.s)) := by
    change RatPolyCoeffEqv
      (coeffEvalExpr atoms
        (eLocalClearedFactorOf (eQuaternion 12) eCayleyComplement3))
      (coeffEvalExpr atoms
        (eClearedFactor eCayleyData.D eCayleyData.s))
    exact coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) atoms
  simpa [clearedCayleyScaleProduct, compiledCayleyDenominatorPolynomial,
    globalDenominatorExpression, atoms, coeffEvalExpr] using
      (RatPolyCoeffEqv.mul
        (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.mul h0 h1) h2) h3)

/-- The ORIGINAL face denominator probe is coefficientwise the generic
four-quaternion compiled denominator. -/
theorem globalCayleyDenominatorPolynomial_coeff_compiled
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (globalCayleyDenominatorPolynomial extent face)
      (compiledCayleyDenominatorPolynomial
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry0 face))
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry1 face))
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry2 face))
        (orientedCorrectedSlabLinkPolynomial extent (faceEntry3 face))) := by
  simpa [globalCayleyDenominatorPolynomial,
    compiledCayleyDenominatorPolynomial, cayleyQuaternionAtoms,
    facePolynomialAtoms] using
      (instantiate_coeffEvalExpr (facePolynomialAtoms extent face)
        globalDenominatorExpression)

/-- The corresponding cleared scalar multiple of the supplied polynomial
quaternion. -/
def clearedUnitFactor
    (q : PolyQuaternion) (complement : RatPoly) : PolyQuaternion :=
  ⟨factorPolynomial q complement (eLocalScaledComponent 0),
    factorPolynomial q complement (eLocalScaledComponent 1),
    factorPolynomial q complement (eLocalScaledComponent 2),
    factorPolynomial q complement (eLocalScaledComponent 3)⟩

/-- The cleared factor is coefficientwise its explicit scalar polynomial
times the original polynomial quaternion. -/
theorem clearedUnitFactor_coeff_scale
    (q : PolyQuaternion) (complement : RatPoly) :
    PolyQuaternionCoeffEqv
      (clearedUnitFactor q complement)
      ⟨polyMul (clearedCayleyFactorPolynomial q complement) q.scalar,
        polyMul (clearedCayleyFactorPolynomial q complement) q.iPart,
        polyMul (clearedCayleyFactorPolynomial q complement) q.jPart,
        polyMul (clearedCayleyFactorPolynomial q complement) q.kPart⟩ :=
  ⟨RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _,
    RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _⟩

private theorem carrier_of_normal
    {blocks : Nat} (q : PolyQuaternion) (complement : RatPoly)
    (left right : PE) (h : normalize left = normalize right) :
    HaarCarrierEqv blocks
      (factorPolynomial q complement left)
      (factorPolynomial q complement right) :=
  RatPolyCoeffEqv.haarCarrier
    (coeffEvalExpr_eqv_of_normalize_eq left right h
      (factorEnvironment q complement))

private theorem factor_residual_carrier_zero
    {blocks : Nat} (q : PolyQuaternion) (complement : RatPoly)
    (hunit : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    HaarCarrierEqv blocks
      (factorPolynomial q complement eUnitResidual)
      (factorPolynomial q complement 0) := by
  have hone : HaarCarrierEqv blocks
      (factorPolynomial q complement 1) polyOne := by
    change HaarCarrierEqv blocks (polySmul 1 polyOne) polyOne
    exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_smul polyOne)
  have hnorm : HaarCarrierEqv blocks
      (factorPolynomial q complement eQuaternionNorm)
      (factorPolynomial q complement 1) := by
    change HaarCarrierEqv blocks (polyQuaternionNorm q) (polySmul 1 polyOne)
    exact HaarCarrierEqv.trans hunit (HaarCarrierEqv.symm hone)
  have hres : HaarCarrierEqv blocks
      (factorPolynomial q complement eUnitResidual)
      (factorPolynomial q complement (1 + -1)) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.refl blocks (factorPolynomial q complement 1))
      (HaarCarrierEqv.neg hnorm)
  exact HaarCarrierEqv.trans hres
    (carrier_of_normal (blocks := blocks) q complement (1 + -1) 0 (by decide))

private theorem factor_coordinate_clear
    {blocks : Nat} (q : PolyQuaternion) (complement : RatPoly)
    (hres : HaarCarrierEqv blocks
      (factorPolynomial q complement eUnitResidual)
      (factorPolynomial q complement 0))
    (raw scaled correction : PE)
    (hidentity : normalize raw =
      normalize (scaled + correction * eUnitResidual)) :
    HaarCarrierEqv blocks
      (factorPolynomial q complement raw)
      (factorPolynomial q complement scaled) := by
  have hraw := carrier_of_normal (blocks := blocks) q complement raw
    (scaled + correction * eUnitResidual) hidentity
  have hcorrectionCore : HaarCarrierEqv blocks
      (factorPolynomial q complement (correction * eUnitResidual))
      (factorPolynomial q complement (correction * 0)) :=
    HaarCarrierEqv.mul
      (HaarCarrierEqv.refl blocks (factorPolynomial q complement correction)) hres
  have hcorrection : HaarCarrierEqv blocks
      (factorPolynomial q complement (correction * eUnitResidual))
      (factorPolynomial q complement 0) :=
    HaarCarrierEqv.trans hcorrectionCore
      (RatPolyCoeffEqv.haarCarrier
        (((RatPolyCoeffEqv.refl
            (factorPolynomial q complement correction)).mul
          (RatPolyCoeffEqv.zero_smul polyOne)).trans
        ((RatPolyCoeffEqv.mul_zero_right
            (factorPolynomial q complement correction)).trans
          (RatPolyCoeffEqv.zero_smul polyOne).symm)))
  have hsum : HaarCarrierEqv blocks
      (factorPolynomial q complement
        (scaled + correction * eUnitResidual))
      (factorPolynomial q complement (scaled + 0)) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.refl blocks (factorPolynomial q complement scaled))
      hcorrection
  exact HaarCarrierEqv.trans hraw
    (HaarCarrierEqv.trans hsum
      (RatPolyCoeffEqv.haarCarrier
        (((RatPolyCoeffEqv.refl
            (factorPolynomial q complement scaled)).add
          (RatPolyCoeffEqv.zero_smul polyOne)).trans
        (RatPolyCoeffEqv.add_zero
          (factorPolynomial q complement scaled)))))

/-- The local cleared factor is exactly its north-chart scalar weight on the
unit-quaternion Haar carrier. -/
theorem clearedCayleyFactorPolynomial_carrier_north
    {blocks : Nat} (q : PolyQuaternion) (complement : RatPoly)
    (hunit : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    HaarCarrierEqv blocks
      (clearedCayleyFactorPolynomial q complement)
      (northCayleyFactorPolynomial q complement) := by
  have hres := factor_residual_carrier_zero q complement hunit
  have hidentity : normalize eLocalClearedFactor =
      normalize
        (eLocalNorthClearedFactor + eLocalNorthCorrection * eUnitResidual) := by
    decide
  exact factor_coordinate_clear q complement hres eLocalClearedFactor
    eLocalNorthClearedFactor eLocalNorthCorrection hidentity

/-- One raw Cayley factor clears in the arbitrary-insertion Haar carrier using
only the supplied polynomial quaternion's unit-radius carrier identity. -/
theorem rawCayleyFactor_carrier_clear
    {blocks : Nat} (q : PolyQuaternion) (complement : RatPoly)
    (hunit : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    PolyQuaternionHaarCarrierEqv blocks
      (rawCayleyFactor q complement)
      (clearedUnitFactor q complement) := by
  have hres := factor_residual_carrier_zero q complement hunit
  exact ⟨
    factor_coordinate_clear q complement hres
      eLocalRawScalar (eLocalScaledComponent 0) eLocalScalarCorrection
      (by decide),
    factor_coordinate_clear q complement hres
      (eLocalRawComponent 1) (eLocalScaledComponent 1)
      (eLocalVectorCorrection 1) (by decide),
    factor_coordinate_clear q complement hres
      (eLocalRawComponent 2) (eLocalScaledComponent 2)
      (eLocalVectorCorrection 2) (by decide),
    factor_coordinate_clear q complement hres
      (eLocalRawComponent 3) (eLocalScaledComponent 3)
      (eLocalVectorCorrection 3) (by decide)⟩

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyLeftPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyDeficitPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyDeficitPolynomial_coeff_degrees
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyDegreeFourPolynomial_coeff_normalized
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.global_cayley_ratPoly_eval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.instantiate_coeffEvalExpr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.rawCayleyWordPolynomial_scalar_coeff_compiled
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.compiledCayleyDeficitPolynomial_coeff_degrees
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.compiledCayleyDeficitPolynomial_coeff_raw
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyRawScalarPolynomial_coeff_compiled
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyDeficitPolynomial_coeff_raw
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyLeftPolynomial_coeff_original
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.clearedCayleyScaleProduct_coeff_compiled
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.globalCayleyDenominatorPolynomial_coeff_compiled
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.clearedUnitFactor_coeff_scale
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.northCayleyFactorPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.northCayleyFactorPolynomial_coeff_formula
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.clearedCayleyFactorPolynomial_carrier_north
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly.rawCayleyFactor_carrier_clear
