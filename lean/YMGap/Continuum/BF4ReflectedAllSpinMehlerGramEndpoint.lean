/-
# Positive finite BF4 Feynman--Kac/Mehler feature Gram

The global Taylor polynomial of `exp (-A(x,y))` is not, at finite order, a
positive kernel.  The BF4 action has a more useful exact factorization:

  exp (-A(x,y)) = exp (-D(x)) exp (-D(y))
    exp ((1 / 48) xᵀ K24 y).

The last exponential is positive definite because the exact LDL
factorization of `K24` has five positive squares.  For three Lie colours this
gives fifteen positive features.  Truncating the *cross exponential* by
ordered feature words preserves this Gram structure at every finite order;
the one-sided Feynman--Kac factor stays inside each half-amplitude.

This file constructs that finite endpoint explicitly.  It proves:

* all fifteen BF4 feature weights are nonnegative;
* every factorial word weight is nonnegative;
* the raw all-spin endpoint is symmetric;
* every positive shifted diagonal order has an explicit positive vacuum
  half-amplitude and hence a strictly positive partition;
* partition normalization preserves the complete finite PSD quadratic form.

The physical-mean-zero Rayleigh rate and the AF-uniform physical comparison
remain separate analytic data.  They are not hidden in this algebraic
constructor.

## Axiom gate

Finite lists, exact `Q'` arithmetic, polynomial Haar integration, and the
already-proved finite weighted-Gram SOS theorem only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
import YMGap.Continuum.BF4CompactActionCPOrder
import YMGap.Continuum.BF4CompactActionMomentPositivity
import YMGap.Continuum.BF4CompactActionSphereShift
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
open YMGap.Continuum.BF4CompactActionDiagonalSOS
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The fifteen exact BF4 kinetic features -/

/-- Three Lie colours times the five positive LDL modes of `K24`. -/
abbrev BF4KineticFeature := Fin 15

/-- Literal enumeration of all fifteen kinetic features. -/
def bf4KineticFeatureAlphabet : List BF4KineticFeature :=
  List.finRange 15

def bf4FeatureColor (feature : BF4KineticFeature) : Fin 3 :=
  ⟨feature.val / 5, by omega⟩

def bf4FeatureSlot (feature : BF4KineticFeature) : Fin 5 :=
  ⟨feature.val % 5, Nat.mod_lt _ (by decide)⟩

/-- The five integer coefficients in the exact cleared LDL identity
`108900 xᵀ K24 x = Σ_i weight_i z_i(x)^2`. -/
def kineticLDLIntegerWeight (slot : Fin 5) : Q' :=
  match slot.val with
  | 0 => 10890
  | 1 => 990
  | 2 => 7920
  | 3 => 87120
  | _ => 435600

/-- The five cleared LDL linear forms, in the coordinate order used by
`kineticK24`. -/
def kineticLDLLinearTemplate
    (slot : Fin 5) : RingNormaliser.PolyExpr :=
  match slot.val with
  | 0 =>
      RingNormaliser.PolyExpr.add
        (RingNormaliser.PolyExpr.add
          (RingNormaliser.PolyExpr.add
            (RingNormaliser.PolyExpr.add
              (RingNormaliser.PolyExpr.mul
                (RingNormaliser.PolyExpr.const 10)
                (RingNormaliser.PolyExpr.var 0))
              (RingNormaliser.PolyExpr.var 1))
            (RingNormaliser.PolyExpr.mul
              (RingNormaliser.PolyExpr.const (-2))
              (RingNormaliser.PolyExpr.var 2)))
          (RingNormaliser.PolyExpr.neg
            (RingNormaliser.PolyExpr.var 3)))
        (RingNormaliser.PolyExpr.mul
          (RingNormaliser.PolyExpr.const (-4))
          (RingNormaliser.PolyExpr.var 4))
  | 1 =>
      RingNormaliser.PolyExpr.add
        (RingNormaliser.PolyExpr.add
          (RingNormaliser.PolyExpr.add
            (RingNormaliser.PolyExpr.mul
              (RingNormaliser.PolyExpr.const 33)
              (RingNormaliser.PolyExpr.var 1))
            (RingNormaliser.PolyExpr.mul
              (RingNormaliser.PolyExpr.const (-16))
              (RingNormaliser.PolyExpr.var 2)))
          (RingNormaliser.PolyExpr.mul
            (RingNormaliser.PolyExpr.const (-13))
            (RingNormaliser.PolyExpr.var 3)))
        (RingNormaliser.PolyExpr.mul
          (RingNormaliser.PolyExpr.const 18)
          (RingNormaliser.PolyExpr.var 4))
  | 2 =>
      RingNormaliser.PolyExpr.add
        (RingNormaliser.PolyExpr.add
          (RingNormaliser.PolyExpr.mul
            (RingNormaliser.PolyExpr.const 10)
            (RingNormaliser.PolyExpr.var 2))
          (RingNormaliser.PolyExpr.mul
            (RingNormaliser.PolyExpr.const 4)
            (RingNormaliser.PolyExpr.var 3)))
        (RingNormaliser.PolyExpr.mul
          (RingNormaliser.PolyExpr.const (-3))
          (RingNormaliser.PolyExpr.var 4))
  | 3 =>
      RingNormaliser.PolyExpr.add
        (RingNormaliser.PolyExpr.mul
          (RingNormaliser.PolyExpr.const 3)
          (RingNormaliser.PolyExpr.var 3))
        (RingNormaliser.PolyExpr.neg
          (RingNormaliser.PolyExpr.var 4))
  | _ => RingNormaliser.PolyExpr.var 4

/-- One source-side BF4 kinetic feature as a polynomial in the first five
quaternion holonomies. -/
def sourceKineticFeaturePolynomial
    (feature : BF4KineticFeature) : RatPoly :=
  exprToRatPoly
    (substituteVariables
      (sourceReplacement (bf4FeatureColor feature))
      (kineticLDLLinearTemplate (bf4FeatureSlot feature)))

/-- The reflected target copy of one BF4 kinetic feature. -/
def targetKineticFeaturePolynomial
    (feature : BF4KineticFeature) : RatPoly :=
  exprToRatPoly
    (substituteVariables
      (targetReplacement (bf4FeatureColor feature))
      (kineticLDLLinearTemplate (bf4FeatureSlot feature)))

/-- Coefficient of `z_i(x) z_i(y)` in
`(1/48) xᵀ K24 y`, including the cleared LDL denominator. -/
def bf4KineticFeatureWeight
    (feature : BF4KineticFeature) : Q' :=
  kineticLDLIntegerWeight (bf4FeatureSlot feature) *
    Q'.mkPos 1 (48 * 108900) (by decide)

theorem kineticLDLIntegerWeight_nonnegative
    (slot : Fin 5) :
    (0 : Q') ≤ kineticLDLIntegerWeight slot := by
  unfold kineticLDLIntegerWeight
  split <;> decide

theorem bf4KineticFeatureWeight_nonnegative
    (feature : BF4KineticFeature) :
    (0 : Q') ≤ bf4KineticFeatureWeight feature := by
  unfold bf4KineticFeatureWeight
  exact Q'.mul_nonneg _ _
    (kineticLDLIntegerWeight_nonnegative
      (bf4FeatureSlot feature))
    (Q'.le_of_lt (by decide))

/-! ## 2. Positive factorial words for the cross exponential -/

/-- Ordered feature words of one exact length.  Ordered words reproduce the
multinomial expansion without choosing multiplicities. -/
def bf4FeatureWordsExact : Nat → List (List BF4KineticFeature)
  | 0 => [[]]
  | length + 1 =>
      bf4KineticFeatureAlphabet.flatMap fun feature =>
        (bf4FeatureWordsExact length).map fun word =>
          feature :: word

/-- All words of length at most `order`.  The empty channel is present at
every order. -/
def bf4FeatureWordsAtMost : Nat → List (List BF4KineticFeature)
  | 0 => [[]]
  | order + 1 =>
      bf4FeatureWordsAtMost order ++
        bf4FeatureWordsExact (order + 1)

theorem empty_mem_bf4FeatureWordsAtMost :
    ∀ order, [] ∈ bf4FeatureWordsAtMost order
  | 0 => List.mem_cons_self
  | order + 1 =>
      List.mem_append_left _
        (empty_mem_bf4FeatureWordsAtMost order)

/-- The ordered-word coefficient
`(Π featureWeight) / word.length!`, defined recursively without a separate
factorial division. -/
def bf4FeatureWordWeight :
    List BF4KineticFeature → Q'
  | [] => 1
  | feature :: rest =>
      (bf4KineticFeatureWeight feature *
        Q'.invSucc rest.length) *
      bf4FeatureWordWeight rest

theorem bf4FeatureWordWeight_nonnegative :
    ∀ word : List BF4KineticFeature,
      (0 : Q') ≤ bf4FeatureWordWeight word
  | [] => Q'.zero_le_one
  | feature :: rest =>
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (bf4KineticFeatureWeight_nonnegative feature)
          (Q'.invSucc_nonneg rest.length))
        (bf4FeatureWordWeight_nonnegative rest)

/-- Product of all source-side feature polynomials in an ordered channel. -/
def sourceFeatureWordPolynomial :
    List BF4KineticFeature → RatPoly
  | [] => polyOne
  | feature :: rest =>
      polyMul
        (sourceKineticFeaturePolynomial feature)
        (sourceFeatureWordPolynomial rest)

/-- Product of the reflected target-side feature polynomials in the same
ordered channel. -/
def targetFeatureWordPolynomial :
    List BF4KineticFeature → RatPoly
  | [] => polyOne
  | feature :: rest =>
      polyMul
        (targetKineticFeaturePolynomial feature)
        (targetFeatureWordPolynomial rest)

/-! ## 3. The one-sided interior Feynman--Kac polynomial -/

/-- Cleared LDL reconstruction of the one-colour source kinetic quadratic. -/
def sourceKineticLDLClearedPolynomial (color : Fin 3) : RatPoly :=
  (List.finRange 5).foldr
    (fun slot total =>
      let feature : BF4KineticFeature :=
        ⟨5 * color.val + slot.val, by omega⟩
      polyAdd
        (polySmul (kineticLDLIntegerWeight slot)
          (polyMul
            (sourceKineticFeaturePolynomial feature)
            (sourceKineticFeaturePolynomial feature)))
        total)
    polyZero

/-! ### A five-Haar shifted complement

The alternating Taylor partial of `exp (-D)` has no finite-order positivity
property.  We instead clear the exact one-sided quadratic and write

`D = B - E`

in the five-sphere quotient, with `E` a literal sum of squares.  The common
scalar `exp (-B)` occurs in every half-amplitude and cancels from the
partition-normalized endpoint.  Truncating `exp E` therefore preserves both
the physical limit and finite-order positivity.
-/

private def sourceSpatialLDLEntries :
    List (Int × RingNormaliser.PolyExpr) :=
  let z0 :=
    RingNormaliser.PolyExpr.add
      (RingNormaliser.PolyExpr.mul
        (RingNormaliser.PolyExpr.const 2)
        (RingNormaliser.PolyExpr.var 0))
      (RingNormaliser.PolyExpr.neg
        (RingNormaliser.PolyExpr.var 4))
  let z1 :=
    RingNormaliser.PolyExpr.add
      (RingNormaliser.PolyExpr.add
        (RingNormaliser.PolyExpr.add
          (RingNormaliser.PolyExpr.mul
            (RingNormaliser.PolyExpr.const 2)
            (RingNormaliser.PolyExpr.var 1))
          (RingNormaliser.PolyExpr.neg
            (RingNormaliser.PolyExpr.var 2)))
        (RingNormaliser.PolyExpr.neg
          (RingNormaliser.PolyExpr.var 3)))
      (RingNormaliser.PolyExpr.var 4)
  let z2 :=
    RingNormaliser.PolyExpr.add
      (RingNormaliser.PolyExpr.add
        (RingNormaliser.PolyExpr.mul
          (RingNormaliser.PolyExpr.const 3)
          (RingNormaliser.PolyExpr.var 2))
        (RingNormaliser.PolyExpr.var 3))
      (RingNormaliser.PolyExpr.neg
        (RingNormaliser.PolyExpr.var 4))
  let z3 :=
    RingNormaliser.PolyExpr.add
      (RingNormaliser.PolyExpr.mul
        (RingNormaliser.PolyExpr.const 4)
        (RingNormaliser.PolyExpr.var 3))
      (RingNormaliser.PolyExpr.neg
        (RingNormaliser.PolyExpr.var 4))
  [(24, z0), (24, z1), (8, z2), (4, z3),
   (36, RingNormaliser.PolyExpr.var 4)]

private def kineticLDLIntegerWeightInt
    (slot : Fin 5) : Int :=
  match slot.val with
  | 0 => 10890
  | 1 => 990
  | 2 => 7920
  | 3 => 87120
  | _ => 435600

private def weightedSquareExpression
    (weight : Int)
    (linear : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.mul
    (RingNormaliser.PolyExpr.const weight)
    (RingNormaliser.PolyExpr.mul linear linear)

private def sumExpressions :
    List RingNormaliser.PolyExpr →
      RingNormaliser.PolyExpr
  | [] => RingNormaliser.PolyExpr.const 0
  | expression :: rest =>
      RingNormaliser.PolyExpr.add expression
        (sumExpressions rest)

/-- Common denominator clearing the exact three-colour one-sided action. -/
def sourceDiagonalClearing : Nat := 96 * 108900

private def sourceColorClearedDiagonalActionExpression
    (color : Fin 3) : RingNormaliser.PolyExpr :=
  let kinetic :=
    (List.finRange 5).map fun slot =>
      weightedSquareExpression
        (kineticLDLIntegerWeightInt slot)
        (substituteVariables
          (sourceReplacement color)
          (kineticLDLLinearTemplate slot))
  let spatial :=
    sourceSpatialLDLEntries.map fun entry =>
      weightedSquareExpression
        (27225 * entry.1)
        (substituteVariables
          (sourceReplacement color) entry.2)
  sumExpressions (kinetic ++ spatial)

/-- Literal integer expression for
`(96*108900) D(source)` on all three Lie colours. -/
def sourceClearedDiagonalActionExpression :
    RingNormaliser.PolyExpr :=
  lieColorIndices.foldr
    (fun color total =>
      RingNormaliser.PolyExpr.add
        (sourceColorClearedDiagonalActionExpression color)
        total)
    (RingNormaliser.PolyExpr.const 0)

/-- Target-reflected copy of one cleared colour-diagonal action. -/
private def targetColorClearedDiagonalActionExpression
    (color : Fin 3) : RingNormaliser.PolyExpr :=
  let kinetic :=
    (List.finRange 5).map fun slot =>
      weightedSquareExpression
        (kineticLDLIntegerWeightInt slot)
        (substituteVariables
          (targetReplacement color)
          (kineticLDLLinearTemplate slot))
  let spatial :=
    sourceSpatialLDLEntries.map fun entry =>
      weightedSquareExpression
        (27225 * entry.1)
        (substituteVariables
          (targetReplacement color) entry.2)
  sumExpressions (kinetic ++ spatial)

/-- Literal integer expression for
`(96*108900) D(target)` on all three Lie colours. -/
def targetClearedDiagonalActionExpression :
    RingNormaliser.PolyExpr :=
  lieColorIndices.foldr
    (fun color total =>
      RingNormaliser.PolyExpr.add
        (targetColorClearedDiagonalActionExpression color)
        total)
    (RingNormaliser.PolyExpr.const 0)

/-- The cleared positive source/target kinetic pairing.  Its normalization
is `(96*108900) * (1/48) xᵀK24y`; the factor two comes from clearing
`1/48` rather than the one-sided `1/96`. -/
def sourceTargetKineticCrossExpression :
    RingNormaliser.PolyExpr :=
  sumExpressions
    (bf4KineticFeatureAlphabet.map fun feature =>
      RingNormaliser.PolyExpr.mul
        (RingNormaliser.PolyExpr.const
          (2 *
            kineticLDLIntegerWeightInt
              (bf4FeatureSlot feature)))
        (RingNormaliser.PolyExpr.mul
          (substituteVariables
            (sourceReplacement
              (bf4FeatureColor feature))
            (kineticLDLLinearTemplate
              (bf4FeatureSlot feature)))
          (substituteVariables
            (targetReplacement
              (bf4FeatureColor feature))
            (kineticLDLLinearTemplate
              (bf4FeatureSlot feature)))))

/-- Exact cleared reflected Mehler factorization
`(96*108900) * (D(source)+D(target)-cross)`. -/
def factorizedClearedCoupledActionExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.add
    sourceClearedDiagonalActionExpression
    (RingNormaliser.PolyExpr.add
      targetClearedDiagonalActionExpression
      (RingNormaliser.PolyExpr.neg
        sourceTargetKineticCrossExpression))

/-- The old `480 A` physical compiler rescaled to the common LDL
denominator.  Since `(96*108900)/480 = 21780`, this is the same cleared
action in the original source file. -/
def rescaledPhysicalClearedCoupledActionExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.mul
    (RingNormaliser.PolyExpr.const 21780)
    clearedCompactActionExpr

/-- Kernel-checked exact identification of the reflected diagonal/cross
factorization with the genuine compact BF4 action. -/
theorem factorizedClearedCoupledAction_normal :
    RingNormaliser.normalize
        factorizedClearedCoupledActionExpression =
      RingNormaliser.normalize
        rescaledPhysicalClearedCoupledActionExpression := by
  decide

theorem rescaledPhysicalClearedCoupledActionPolynomial_eq :
    exprToRatPoly
        rescaledPhysicalClearedCoupledActionExpression =
      polySmul (Q'.ofInt 21780)
        (exprToRatPoly clearedCompactActionExpr) := by
  decide

/-- Exact reciprocal of the one-sided action clearing. -/
def oneOverSourceDiagonalClearing : Q' :=
  Q'.mkPos 1 sourceDiagonalClearing (by decide)

/-- Three-colour one-sided BF4 diagonal action, compiled directly from its
exact LDL reconstruction. -/
def sourceDiagonalActionPolynomial : RatPoly :=
  polySmul oneOverSourceDiagonalClearing
    (exprToRatPoly
      sourceClearedDiagonalActionExpression)

/-- Reflected target one-sided BF4 diagonal action. -/
def targetDiagonalActionPolynomial : RatPoly :=
  polySmul oneOverSourceDiagonalClearing
    (exprToRatPoly
      targetClearedDiagonalActionExpression)

/-- Positive kinetic pairing in the Mehler factorization. -/
def sourceTargetKineticCrossPolynomial : RatPoly :=
  polySmul oneOverSourceDiagonalClearing
    (exprToRatPoly
      sourceTargetKineticCrossExpression)

/-- Polynomial compiled directly from the exact reflected
`D(source)+D(target)-cross` factorization. -/
def factorizedCoupledBF4ActionPolynomial : RatPoly :=
  polySmul oneOverSourceDiagonalClearing
    (exprToRatPoly
      factorizedClearedCoupledActionExpression)

theorem sourceClearing_rescale_to_oneOver480 :
    oneOverSourceDiagonalClearing *
        Q'.ofInt 21780 ≈
      oneOver480 := by
  decide

/-- Under every ten-Haar insertion, the LDL-factorized action is exactly the
original compact physical BF4 action.  This is the load-bearing bridge from
the positive feature Gram back to `geometricMehlerTaylorPartial`. -/
theorem factorizedCoupledBF4Action_haar_eq_physical
    (polynomial : RatPoly) :
    tenfoldHaar
        (polyMul polynomial
          factorizedCoupledBF4ActionPolynomial) ≈
      tenfoldHaar
        (polyMul polynomial
          compactCoupledBF4ActionPolynomial) := by
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      tenfoldHaar
        (polyMul polynomial
          (exprToRatPoly
            factorizedClearedCoupledActionExpression))) _
    (quaternionHaar_polyMul_smul_right
      10 oneOverSourceDiagonalClearing polynomial
      (exprToRatPoly
        factorizedClearedCoupledActionExpression)) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      tenfoldHaar
        (polyMul polynomial
          (exprToRatPoly
            rescaledPhysicalClearedCoupledActionExpression))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (quaternionHaar_mul_expr_congr_of_normal_eq
        10
        factorizedClearedCoupledActionExpression
        rescaledPhysicalClearedCoupledActionExpression
        factorizedClearedCoupledAction_normal
        polynomial)) ?_
  rw [rescaledPhysicalClearedCoupledActionPolynomial_eq]
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (Q'.ofInt 21780 *
        tenfoldHaar
          (polyMul polynomial
            (exprToRatPoly clearedCompactActionExpr)))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (quaternionHaar_polyMul_smul_right
        10 (Q'.ofInt 21780) polynomial
        (exprToRatPoly clearedCompactActionExpr))) ?_
  refine Q'.eqv_trans _
    ((oneOverSourceDiagonalClearing *
        Q'.ofInt 21780) *
      tenfoldHaar
        (polyMul polynomial
          (exprToRatPoly clearedCompactActionExpr))) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        oneOverSourceDiagonalClearing
        (Q'.ofInt 21780)
        (tenfoldHaar
          (polyMul polynomial
            (exprToRatPoly
              clearedCompactActionExpr))))) ?_
  refine Q'.eqv_trans _
    (oneOver480 *
      tenfoldHaar
        (polyMul polynomial
          (exprToRatPoly clearedCompactActionExpr))) _
    (Q'.mul_eqv_congr_right _ _ _
      sourceClearing_rescale_to_oneOver480) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul polynomial
        compactActionPolynomialFromCleared)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_smul_right
        10 oneOver480 polynomial
        (exprToRatPoly clearedCompactActionExpr))) ?_
  exact
    compactActionPolynomialFromCleared_haar_eq_physical
      polynomial

/-- Five source quaternion radius squares. -/
def sourceFiveRadiusSumExpression :
    RingNormaliser.PolyExpr :=
  sumExpressions
    ((List.range 20).map fun coordinate =>
      RingNormaliser.PolyExpr.mul
        (RingNormaliser.PolyExpr.var coordinate)
        (RingNormaliser.PolyExpr.var coordinate))

/-- A deliberately explicit diagonal-dominance clearance.  It gives the
one-sided shift `B = 5*100000000/(96*108900)`. -/
def sourceDiagonalSphereCoefficient : Int := 100000000

/-- Cleared five-sphere complement
`sourceDiagonalSphereCoefficient * Σ|q_i|² -
 (96*108900) D`. -/
def sourceClearedDiagonalComplementExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.add
    (RingNormaliser.PolyExpr.mul
      (RingNormaliser.PolyExpr.const
        sourceDiagonalSphereCoefficient)
      sourceFiveRadiusSumExpression)
    (RingNormaliser.PolyExpr.neg
      sourceClearedDiagonalActionExpression)

private def sourceActionCoefficient
    (left right : Nat) : Int :=
  let monomial :=
    monoMul (varMono left) (varMono right)
  let normalized :=
    RingNormaliser.normalize
      sourceClearedDiagonalActionExpression
  normalized.foldr
    (fun term total =>
      (if term.1 = monomial then term.2 else 0) + total)
    0

private def sourceComplementCrossCoefficient
    (left right : Nat) : Int :=
  -(sourceActionCoefficient left right)

private def sourceComplementEdgeWeight
    (left right : Nat) : Int :=
  Int.ofNat
    ((sourceComplementCrossCoefficient left right).natAbs / 2)

private def sourceCoordinatePairs : List (Nat × Nat) :=
  (List.range 20).flatMap fun left =>
    (List.range (20 - (left + 1))).map fun offset =>
      (left, left + 1 + offset)

private def sourceActiveCoordinatePairs :
    List (Nat × Nat) :=
  sourceCoordinatePairs.filter fun pair =>
    sourceComplementEdgeWeight pair.1 pair.2 != 0

private def sourceSignedEdgeLinearExpression
    (left right : Nat) : RingNormaliser.PolyExpr :=
  if sourceComplementCrossCoefficient left right < 0 then
    RingNormaliser.PolyExpr.add
      (RingNormaliser.PolyExpr.var left)
      (RingNormaliser.PolyExpr.neg
        (RingNormaliser.PolyExpr.var right))
  else
    RingNormaliser.PolyExpr.add
      (RingNormaliser.PolyExpr.var left)
      (RingNormaliser.PolyExpr.var right)

private def sourceIncidentWeight
    (coordinate : Nat) : Int :=
  sourceActiveCoordinatePairs.foldl
    (fun total pair =>
      if pair.1 = coordinate ∨ pair.2 = coordinate then
        total + sourceComplementEdgeWeight pair.1 pair.2
      else total)
    0

private def sourceDiagonalReserve
    (coordinate : Nat) : Int :=
  sourceDiagonalSphereCoefficient -
    sourceActionCoefficient coordinate coordinate -
    sourceIncidentWeight coordinate

/-- Literal five-source-sphere SOS carrier for the shifted complement. -/
def sourceDiagonalComplementSOSEntries :
    List (Int × RingNormaliser.PolyExpr) :=
  (sourceActiveCoordinatePairs.map fun pair =>
    (sourceComplementEdgeWeight pair.1 pair.2,
      sourceSignedEdgeLinearExpression pair.1 pair.2)) ++
  ((List.range 20).map fun coordinate =>
    (sourceDiagonalReserve coordinate,
      RingNormaliser.PolyExpr.var coordinate))

/-- Expanded literal SOS expression for the one-sided complement. -/
def sourceDiagonalComplementSOSExpression :
    RingNormaliser.PolyExpr :=
  sumExpressions
    (sourceDiagonalComplementSOSEntries.map fun entry =>
      weightedSquareExpression entry.1 entry.2)

theorem sourceDiagonalComplement_sos_normal :
    RingNormaliser.normalize
        sourceClearedDiagonalComplementExpression =
      RingNormaliser.normalize
        sourceDiagonalComplementSOSExpression := by
  decide

theorem sourceDiagonalComplementSOSEntries_nonnegative :
    ∀ entry,
      entry ∈ sourceDiagonalComplementSOSEntries →
        (0 : Int) ≤ entry.1 := by
  decide

theorem sourceDiagonalComplementSOSEntries_supported :
    ∀ entry,
      entry ∈ sourceDiagonalComplementSOSEntries →
        SupportedQuaternionBlocks 5
          (exprToRatPoly entry.2) := by
  have hall :
      sourceDiagonalComplementSOSEntries.all
        (fun entry =>
          polynomialSupportedBool 5
            (exprToRatPoly entry.2)) = true := by
    decide
  intro entry hentry
  exact supported_of_bool 5
    (exprToRatPoly entry.2)
    (List.all_eq_true.mp hall entry hentry)

/-- Normalized five-sphere complement `E = B-D`. -/
def sourceDiagonalComplementPolynomial : RatPoly :=
  polySmul oneOverSourceDiagonalClearing
    (exprToRatPoly
      sourceClearedDiagonalComplementExpression)

theorem sourceDiagonalComplement_supported :
    SupportedQuaternionBlocks 5
      sourceDiagonalComplementPolynomial := by
  apply supported_of_bool 5
  decide

/-- Complete positivity of the five-Haar one-sided complement. -/
theorem sourceDiagonalComplement_cp
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 5 polynomial) :
    (0 : Q') ≤
      quaternionHaar 5
        (polyMul (polyMul polynomial polynomial)
          sourceDiagonalComplementPolynomial) := by
  have hsos :
      (0 : Q') ≤
        quaternionHaar 5
          (polyMul (polyMul polynomial polynomial)
            (sourceDiagonalComplementSOSEntries.foldr
              (fun entry total =>
                polyAdd
                  (polynomialSOSEntry entry) total)
              (exprToRatPoly
                (RingNormaliser.PolyExpr.const 0)))) :=
    sos_entries_nonnegative
      5 polynomial hsupport
      sourceDiagonalComplementSOSEntries
      sourceDiagonalComplementSOSEntries_nonnegative
      sourceDiagonalComplementSOSEntries_supported
  have hfold :
      sourceDiagonalComplementSOSEntries.foldr
          (fun entry total =>
            polyAdd
              (polynomialSOSEntry entry) total)
          (exprToRatPoly
            (RingNormaliser.PolyExpr.const 0)) =
        exprToRatPoly
          sourceDiagonalComplementSOSExpression := by
    decide
  rw [hfold] at hsos
  have hnormal :
      quaternionHaar 5
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              sourceClearedDiagonalComplementExpression)) ≈
        quaternionHaar 5
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              sourceDiagonalComplementSOSExpression)) :=
    quaternionHaar_mul_expr_congr_of_normal_eq
      5 sourceClearedDiagonalComplementExpression
      sourceDiagonalComplementSOSExpression
      sourceDiagonalComplement_sos_normal
      (polyMul polynomial polynomial)
  have hcleared :
      (0 : Q') ≤
        quaternionHaar 5
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              sourceClearedDiagonalComplementExpression)) :=
    Q'.le_trans' _ _ _ hsos
      (Q'.le_of_eqv (Q'.eqv_symm hnormal))
  have hscale :
      quaternionHaar 5
          (polyMul (polyMul polynomial polynomial)
            sourceDiagonalComplementPolynomial) ≈
        oneOverSourceDiagonalClearing *
          quaternionHaar 5
            (polyMul (polyMul polynomial polynomial)
              (exprToRatPoly
                sourceClearedDiagonalComplementExpression)) :=
    quaternionHaar_polyMul_smul_right
      5 oneOverSourceDiagonalClearing
      (polyMul polynomial polynomial)
      (exprToRatPoly
        sourceClearedDiagonalComplementExpression)
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt (by decide)) hcleared)
    (Q'.le_of_eqv (Q'.eqv_symm hscale))

/-- Parity-arranged representative of `E^n`. -/
def sourceDiagonalComplementMomentPolynomial
    (exponent : Nat) : RatPoly :=
  let half :=
    polynomialPower sourceDiagonalComplementPolynomial
      (exponent / 2)
  if exponent % 2 = 0 then
    polyMul half half
  else
    polyMul (polyMul half half)
      sourceDiagonalComplementPolynomial

theorem sourceDiagonalComplementMoment_nonnegative
    (exponent : Nat) :
    (0 : Q') ≤
      quaternionHaar 5
        (sourceDiagonalComplementMomentPolynomial
          exponent) := by
  let half :=
    polynomialPower sourceDiagonalComplementPolynomial
      (exponent / 2)
  have hhalf :
      SupportedQuaternionBlocks 5 half :=
    polynomialPower_supported
      sourceDiagonalComplement_supported
      (exponent / 2)
  unfold sourceDiagonalComplementMomentPolynomial
  split
  · exact quaternionHaar_square_nonnegative
      5 half hhalf
  · exact sourceDiagonalComplement_cp half hhalf

/-! ### Exact five-sphere shift for the one-sided action -/

/-- The common one-sided scalar shift
`B = 5*100000000/(96*108900)`. -/
def sourceDiagonalSphereShift : Q' :=
  oneOverSourceDiagonalClearing *
    (Q'.ofInt sourceDiagonalSphereCoefficient *
      Q'.ofNat 5)

/-- The complement plus the one-sided action is exactly the declared
multiple of the five quaternion radius sum. -/
def sourceComplementPlusActionExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.add
    sourceClearedDiagonalComplementExpression
    sourceClearedDiagonalActionExpression

def sourceDiagonalRadiusShiftExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.mul
    (RingNormaliser.PolyExpr.const
      sourceDiagonalSphereCoefficient)
    sourceFiveRadiusSumExpression

theorem sourceComplementPlusAction_normal :
    RingNormaliser.normalize
        sourceComplementPlusActionExpression =
      RingNormaliser.normalize
        sourceDiagonalRadiusShiftExpression := by
  decide

theorem sourceDiagonalRadiusShiftPolynomial_eq :
    exprToRatPoly sourceDiagonalRadiusShiftExpression =
      polyAdd
        (polySmul
          (Q'.ofInt sourceDiagonalSphereCoefficient)
          (quaternionRadiusPrefixSum 5))
        (exprToRatPoly
          (RingNormaliser.PolyExpr.const 0)) := by
  decide

private theorem quaternionHaar_polyMul_compiledZero_right :
    ∀ polynomial : RatPoly,
      quaternionHaar 5
          (polyMul polynomial
            (exprToRatPoly
              (RingNormaliser.PolyExpr.const 0))) ≈
        0
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (term.2 * 0) *
              quaternionHaarMono 5
                (monoMul term.1 []) +
            quaternionHaar 5
              (polyMul rest
                (exprToRatPoly
                  (RingNormaliser.PolyExpr.const 0))) ≈
          0
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_zero_eqv term.2))
            (Q'.zero_mul_eqv _))
          (quaternionHaar_polyMul_compiledZero_right
            rest)
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- Exact arbitrary-insertion five-sphere identity

`H₅(P E) + H₅(P D) = B H₅(P)`.

It proves that replacing `exp(-D)` by the positive series
`exp(E)` changes every half-amplitude only by the same scalar `exp(-B)`. -/
theorem sourceDiagonal_sphere_shift
    (polynomial : RatPoly) :
    quaternionHaar 5
          (polyMul polynomial
            sourceDiagonalComplementPolynomial) +
        quaternionHaar 5
          (polyMul polynomial
            sourceDiagonalActionPolynomial) ≈
      sourceDiagonalSphereShift *
        quaternionHaar 5 polynomial := by
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (quaternionHaar 5
          (polyMul polynomial
            (exprToRatPoly
              sourceClearedDiagonalComplementExpression)) +
        quaternionHaar 5
          (polyMul polynomial
            (exprToRatPoly
              sourceClearedDiagonalActionExpression)))) _
    ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (quaternionHaar_polyMul_smul_right
          5 oneOverSourceDiagonalClearing polynomial
          (exprToRatPoly
            sourceClearedDiagonalComplementExpression))
        (quaternionHaar_polyMul_smul_right
          5 oneOverSourceDiagonalClearing polynomial
          (exprToRatPoly
            sourceClearedDiagonalActionExpression)))
      (Q'.eqv_symm
        (Q'.mul_add_eqv
          oneOverSourceDiagonalClearing _ _))
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      quaternionHaar 5
        (polyMul polynomial
          (exprToRatPoly
            sourceComplementPlusActionExpression))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_add_right
          5 polynomial
          (exprToRatPoly
            sourceClearedDiagonalComplementExpression)
          (exprToRatPoly
            sourceClearedDiagonalActionExpression)))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      quaternionHaar 5
        (polyMul polynomial
          (exprToRatPoly
            sourceDiagonalRadiusShiftExpression))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (quaternionHaar_mul_expr_congr_of_normal_eq
        5 sourceComplementPlusActionExpression
        sourceDiagonalRadiusShiftExpression
        sourceComplementPlusAction_normal polynomial)) ?_
  rw [sourceDiagonalRadiusShiftPolynomial_eq]
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (quaternionHaar 5
          (polyMul polynomial
            (polySmul
              (Q'.ofInt
                sourceDiagonalSphereCoefficient)
              (quaternionRadiusPrefixSum 5))) +
        quaternionHaar 5
          (polyMul polynomial
            (exprToRatPoly
              (RingNormaliser.PolyExpr.const 0))))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (quaternionHaar_polyMul_add_right
        5 polynomial
        (polySmul
          (Q'.ofInt sourceDiagonalSphereCoefficient)
          (quaternionRadiusPrefixSum 5))
        (exprToRatPoly
          (RingNormaliser.PolyExpr.const 0)))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (quaternionHaar 5
          (polyMul polynomial
            (polySmul
              (Q'.ofInt
                sourceDiagonalSphereCoefficient)
              (quaternionRadiusPrefixSum 5))) +
        0)) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.add_eqv_congr_left _ _ _
        (quaternionHaar_polyMul_compiledZero_right
          polynomial))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      quaternionHaar 5
        (polyMul polynomial
          (polySmul
            (Q'.ofInt sourceDiagonalSphereCoefficient)
            (quaternionRadiusPrefixSum 5)))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.eqv_of_eq
        (Q'.add_zero'
          (quaternionHaar 5
            (polyMul polynomial
              (polySmul
                (Q'.ofInt
                  sourceDiagonalSphereCoefficient)
                (quaternionRadiusPrefixSum 5))))))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (Q'.ofInt sourceDiagonalSphereCoefficient *
        quaternionHaar 5
          (polyMul polynomial
            (quaternionRadiusPrefixSum 5)))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (quaternionHaar_polyMul_smul_right
        5 (Q'.ofInt sourceDiagonalSphereCoefficient)
        polynomial (quaternionRadiusPrefixSum 5))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (Q'.ofInt sourceDiagonalSphereCoefficient *
        (Q'.ofNat 5 *
          quaternionHaar 5 polynomial))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.mul_eqv_congr_left
        (Q'.ofInt sourceDiagonalSphereCoefficient) _ _
        (quaternionHaar_mul_radiusPrefixSum
          5 polynomial))) ?_
  unfold sourceDiagonalSphereShift
  refine Q'.eqv_trans _
    ((oneOverSourceDiagonalClearing *
        Q'.ofInt sourceDiagonalSphereCoefficient) *
      (Q'.ofNat 5 *
        quaternionHaar 5 polynomial)) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        oneOverSourceDiagonalClearing
        (Q'.ofInt sourceDiagonalSphereCoefficient)
        (Q'.ofNat 5 *
          quaternionHaar 5 polynomial))) ?_
  refine Q'.eqv_trans _
    (((oneOverSourceDiagonalClearing *
        Q'.ofInt sourceDiagonalSphereCoefficient) *
      Q'.ofNat 5) *
        quaternionHaar 5 polynomial) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (oneOverSourceDiagonalClearing *
          Q'.ofInt sourceDiagonalSphereCoefficient)
        (Q'.ofNat 5)
        (quaternionHaar 5 polynomial))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_assoc_eqv
      oneOverSourceDiagonalClearing
      (Q'.ofInt sourceDiagonalSphereCoefficient)
      (Q'.ofNat 5))

/-- One positive coefficient of the shifted one-sided exponential. -/
def sourceDiagonalShiftedTerm
    (exponent : Nat) : RatPoly :=
  polySmul (ExpNeg.termAbs 1 exponent)
    (sourceDiagonalComplementMomentPolynomial exponent)

theorem sourceDiagonalShiftedTerm_nonnegative
    (exponent : Nat) :
    (0 : Q') ≤
      quaternionHaar 5
        (sourceDiagonalShiftedTerm exponent) := by
  have hscale :=
    quaternionHaar_polySmul
      5 (ExpNeg.termAbs 1 exponent)
      (sourceDiagonalComplementMomentPolynomial exponent)
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _
      (ExpNeg.termAbs_nonneg 1 (by decide) exponent)
      (sourceDiagonalComplementMoment_nonnegative
        exponent))
    (Q'.le_of_eqv (Q'.eqv_symm hscale))

/-- Positivity-preserving finite approximation of `exp (B-D)`.
The omitted scalar `exp (-B)` cancels after partition normalization. -/
def sourceDiagonalFeynmanKacPartial : Nat → RatPoly
  | 0 => polyZero
  | order + 1 =>
      polyAdd
        (sourceDiagonalFeynmanKacPartial order)
        (sourceDiagonalShiftedTerm order)

theorem sourceDiagonalFeynmanKacPartial_haar_ge_one :
    ∀ order : Nat,
      (1 : Q') ≤
        quaternionHaar 5
          (sourceDiagonalFeynmanKacPartial
            (order + 1))
  | 0 => by
      unfold sourceDiagonalFeynmanKacPartial
        sourceDiagonalShiftedTerm
        sourceDiagonalComplementMomentPolynomial
        polynomialPower polySmul
      decide
  | order + 1 => by
      have hprevious :=
        sourceDiagonalFeynmanKacPartial_haar_ge_one
          order
      have hterm :=
        sourceDiagonalShiftedTerm_nonnegative
          (order + 1)
      have hadd :=
        quaternionHaar_append 5
          (sourceDiagonalFeynmanKacPartial
            (order + 1))
          (sourceDiagonalShiftedTerm
            (order + 1))
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _
          hprevious
          (Q'.add_le_self_of_nonneg _ _ hterm))
        (Q'.le_of_eqv (Q'.eqv_symm hadd))

/-! ## 4. All-spin half-amplitudes and the finite Gram endpoint -/

/-- Canonical polynomial representative of the geometric source
wavefunction.  When all twenty-four geometric BF4 face labels vanish, the
eighteen-chord contraction is exactly the constant wavefunction; we select
the literal polynomial unit so subsequent Haar algebra does not retain a
spurious length-twenty all-zero monomial. -/
def sourceMehlerWavefunction
    (state : EdgeLabelling) : RatPoly :=
  if bf4SourceSpatialFaces.all (fun face =>
      state
        ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 0)
  then polyOne
  else sourceGeometricWavefunction state

/-- One all-spin BF4 half-amplitude.  The geometric spin-network
wavefunction is multiplied by the one-sided interior action and one ordered
cross-exponential feature word before exact normalized Haar integration over
the five transmitted holonomies. -/
def bf4MehlerHalfAmplitude
    (diagonalOrder : Nat)
    (state : EdgeLabelling)
    (word : List BF4KineticFeature) : Q' :=
  quaternionHaar 5
    (polyMul
      (polyMul
        (sourceMehlerWavefunction state)
        (sourceDiagonalFeynmanKacPartial diagonalOrder))
      (sourceFeatureWordPolynomial word))

/-- The geometric vacuum and empty feature channel reduce exactly to the
five-Haar shifted diagonal partial. -/
theorem bf4MehlerVacuumEmptyHalf_eq_haar
    (diagonalOrder : Nat) :
    bf4MehlerHalfAmplitude
        diagonalOrder (fun _ => 0) [] ≈
      quaternionHaar 5
        (sourceDiagonalFeynmanKacPartial
          diagonalOrder) := by
  let diagonalPolynomial :=
    sourceDiagonalFeynmanKacPartial diagonalOrder
  have honeLeft :
      quaternionHaar 5
          (polyMul polyOne diagonalPolynomial) ≈
        quaternionHaar 5 diagonalPolynomial := by
    exact Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_comm
        5 polyOne diagonalPolynomial)
      (quaternionHaar_polyMul_one_right
        5 diagonalPolynomial)
  have hvacuumCanonical :
      sourceMehlerWavefunction (fun _ => 0) =
        polyOne := by
    unfold sourceMehlerWavefunction
    rw [if_pos (by decide)]
  unfold bf4MehlerHalfAmplitude
    sourceFeatureWordPolynomial
  rw [hvacuumCanonical]
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_one_right
      5
      (polyMul
        polyOne
        (sourceDiagonalFeynmanKacPartial
          diagonalOrder)))
    honeLeft

/-- Raw positivity-preserving finite BF4 endpoint numerator. -/
def bf4MehlerGramNumerator
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : Q' :=
  weightedGram
    (bf4FeatureWordsAtMost crossOrder)
    bf4FeatureWordWeight
    (bf4MehlerHalfAmplitude diagonalOrder)
    left right

/-- Vacuum coefficient of the raw feature-Gram endpoint. -/
def bf4MehlerGramVacuumPartition
    (diagonalOrder crossOrder : Nat) : Q' :=
  bf4MehlerGramNumerator
    diagonalOrder crossOrder
    (fun _ => 0) (fun _ => 0)

theorem bf4MehlerGramNumerator_symmetric
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    bf4MehlerGramNumerator
        diagonalOrder crossOrder left right ≈
      bf4MehlerGramNumerator
        diagonalOrder crossOrder right left := by
  unfold bf4MehlerGramNumerator weightedGram
  apply listQSum_congr
  intro word
  exact Q'.mul_eqv_congr_left
    (bf4FeatureWordWeight word) _ _
    (Q'.mul_comm_eqv
      (bf4MehlerHalfAmplitude diagonalOrder left word)
      (bf4MehlerHalfAmplitude diagonalOrder right word))

/-- The only strict input needed to normalize a displayed diagonal
truncation: its empty-channel vacuum half-amplitude is positive.  This datum
is constructive and scale-free; no spectral or AF estimate is included. -/
structure BF4MehlerVacuumCertificate
    (diagonalOrder : Nat) : Type where
  empty_half_pos :
    (0 : Q') <
      bf4MehlerHalfAmplitude
        diagonalOrder (fun _ => 0) []

/-- At diagonal order one the one-sided Taylor polynomial is exactly one,
so the empty-channel geometric vacuum half-amplitude is exactly one.  This
is a useful normalization anchor, not the final interior-weight
approximation. -/
def zerothDiagonalVacuumCertificate :
    BF4MehlerVacuumCertificate 1 where
  empty_half_pos := by
    have hhaar :
        (0 : Q') <
          quaternionHaar 5
            (sourceDiagonalFeynmanKacPartial 1) :=
      Q'.pos_of_lt_of_le
        (by decide)
        (sourceDiagonalFeynmanKacPartial_haar_ge_one 0)
    exact Q'.pos_of_lt_of_le hhaar
      (Q'.ge_of_eqv
        (bf4MehlerVacuumEmptyHalf_eq_haar 1))

/-- Every positive shifted order has a strict, explicit vacuum witness.
This removes the previous moving-order normalization hypothesis. -/
def shiftedDiagonalVacuumCertificate
    (order : Nat) :
    BF4MehlerVacuumCertificate (order + 1) where
  empty_half_pos := by
    have hhaar :
        (0 : Q') <
          quaternionHaar 5
            (sourceDiagonalFeynmanKacPartial
              (order + 1)) :=
      Q'.pos_of_lt_of_le
        (by decide)
        (sourceDiagonalFeynmanKacPartial_haar_ge_one
          order)
    exact Q'.pos_of_lt_of_le hhaar
      (Q'.ge_of_eqv
        (bf4MehlerVacuumEmptyHalf_eq_haar
          (order + 1)))

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items →
        value item ≤ listQSum value items
  | [], _, hmem =>
      False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head)
              (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

theorem bf4MehlerGramVacuumPartition_pos
    {diagonalOrder : Nat}
    (vacuum : BF4MehlerVacuumCertificate diagonalOrder)
    (crossOrder : Nat) :
    (0 : Q') <
      bf4MehlerGramVacuumPartition
        diagonalOrder crossOrder := by
  let amplitude :=
    bf4MehlerHalfAmplitude
      diagonalOrder (fun _ => 0)
  let term :=
    fun word : List BF4KineticFeature =>
      bf4FeatureWordWeight word *
        (amplitude word * amplitude word)
  have htermNonnegative :
      ∀ word, (0 : Q') ≤ term word := by
    intro word
    exact Q'.mul_nonneg _ _
      (bf4FeatureWordWeight_nonnegative word)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        (amplitude word))
  have hemptyPositive :
      (0 : Q') < term [] := by
    unfold term amplitude bf4FeatureWordWeight
    exact Q'.pos_of_lt_of_le
      (Q'.mul_pos vacuum.empty_half_pos
        vacuum.empty_half_pos)
      (Q'.ge_of_eqv
        (Q'.one_mul_eqv
          (bf4MehlerHalfAmplitude
              diagonalOrder (fun _ => 0) [] *
            bf4MehlerHalfAmplitude
              diagonalOrder (fun _ => 0) [])))
  have hemptyLe :
      term [] ≤
        listQSum term
          (bf4FeatureWordsAtMost crossOrder) :=
    listQSum_member_le_nonnegative
      term htermNonnegative
      (bf4FeatureWordsAtMost crossOrder)
      (empty_mem_bf4FeatureWordsAtMost crossOrder)
  exact Q'.pos_of_lt_of_le hemptyPositive hemptyLe

/-! ## 5. Normalization preserves positive semidefiniteness -/

def normalizedBF4FeatureWordWeight
    {diagonalOrder : Nat}
    (vacuum : BF4MehlerVacuumCertificate diagonalOrder)
    (crossOrder : Nat)
    (word : List BF4KineticFeature) : Q' :=
  bf4FeatureWordWeight word *
    Q'.recipPos
      (bf4MehlerGramVacuumPartition
        diagonalOrder crossOrder)
      (bf4MehlerGramVacuumPartition_pos
        vacuum crossOrder)

theorem normalizedBF4FeatureWordWeight_nonnegative
    {diagonalOrder : Nat}
    (vacuum : BF4MehlerVacuumCertificate diagonalOrder)
    (crossOrder : Nat)
    (word : List BF4KineticFeature) :
    (0 : Q') ≤
      normalizedBF4FeatureWordWeight
        vacuum crossOrder word := by
  exact Q'.mul_nonneg _ _
    (bf4FeatureWordWeight_nonnegative word)
    (Q'.le_of_lt
      (Q'.recipPos_pos _ _))

theorem normalized_bf4MehlerGram_entry_eqv
    {diagonalOrder : Nat}
    (vacuum : BF4MehlerVacuumCertificate diagonalOrder)
    (crossOrder : Nat)
    (left right : EdgeLabelling) :
    Q'.divPos
        (bf4MehlerGramNumerator
          diagonalOrder crossOrder left right)
        (bf4MehlerGramVacuumPartition
          diagonalOrder crossOrder)
        (bf4MehlerGramVacuumPartition_pos
          vacuum crossOrder) ≈
      weightedGram
        (bf4FeatureWordsAtMost crossOrder)
        (normalizedBF4FeatureWordWeight
          vacuum crossOrder)
        (bf4MehlerHalfAmplitude diagonalOrder)
        left right := by
  unfold Q'.divPos bf4MehlerGramNumerator
    normalizedBF4FeatureWordWeight weightedGram
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_mul_right
        (fun word =>
          bf4FeatureWordWeight word *
            (bf4MehlerHalfAmplitude diagonalOrder left word *
              bf4MehlerHalfAmplitude diagonalOrder right word))
        (Q'.recipPos
          (bf4MehlerGramVacuumPartition
            diagonalOrder crossOrder)
          (bf4MehlerGramVacuumPartition_pos
            vacuum crossOrder))
        (bf4FeatureWordsAtMost crossOrder))) ?_
  apply listQSum_congr
  intro word
  let reciprocal :=
    Q'.recipPos
      (bf4MehlerGramVacuumPartition
        diagonalOrder crossOrder)
      (bf4MehlerGramVacuumPartition_pos
        vacuum crossOrder)
  let product :=
    bf4MehlerHalfAmplitude diagonalOrder left word *
      bf4MehlerHalfAmplitude diagonalOrder right word
  change
    (bf4FeatureWordWeight word * product) * reciprocal ≈
      (bf4FeatureWordWeight word * reciprocal) * product
  exact Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      (bf4FeatureWordWeight word) product reciprocal)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (bf4FeatureWordWeight word) _ _
        (Q'.mul_comm_eqv product reciprocal))
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (bf4FeatureWordWeight word) reciprocal product)))

theorem normalized_bf4MehlerGram_quadratic_nonnegative
    {diagonalOrder : Nat}
    (vacuum : BF4MehlerVacuumCertificate diagonalOrder)
    (crossOrder : Nat)
    (states : List EdgeLabelling)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤
      finiteJointQuadratic states observable
        (fun left right =>
          Q'.divPos
            (bf4MehlerGramNumerator
              diagonalOrder crossOrder left right)
            (bf4MehlerGramVacuumPartition
              diagonalOrder crossOrder)
            (bf4MehlerGramVacuumPartition_pos
              vacuum crossOrder)) := by
  have hgram :
      (0 : Q') ≤
        weightedGramQuadratic
          states
          (bf4FeatureWordsAtMost crossOrder)
          (normalizedBF4FeatureWordWeight
            vacuum crossOrder)
          (bf4MehlerHalfAmplitude diagonalOrder)
          observable :=
    weightedGramQuadratic_nonnegative
      states
      (bf4FeatureWordsAtMost crossOrder)
      (normalizedBF4FeatureWordWeight
        vacuum crossOrder)
      (bf4MehlerHalfAmplitude diagonalOrder)
      observable
      (fun word _ =>
        normalizedBF4FeatureWordWeight_nonnegative
          vacuum crossOrder word)
  exact Q'.le_trans' _ _ _ hgram
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (by
          unfold finiteJointQuadratic
            weightedGramQuadratic
          apply listQSum_congr
          intro left
          apply listQSum_congr
          intro right
          exact Q'.mul_eqv_congr_left
            (observable left * observable right) _ _
            (normalized_bf4MehlerGram_entry_eqv
              vacuum crossOrder left right))))

#print axioms kineticLDLIntegerWeight_nonnegative
#print axioms bf4KineticFeatureWeight_nonnegative
#print axioms bf4FeatureWordWeight_nonnegative
#print axioms factorizedClearedCoupledAction_normal
#print axioms factorizedCoupledBF4Action_haar_eq_physical
#print axioms sourceDiagonalComplement_sos_normal
#print axioms sourceDiagonalComplement_cp
#print axioms sourceDiagonalComplementMoment_nonnegative
#print axioms sourceComplementPlusAction_normal
#print axioms sourceDiagonal_sphere_shift
#print axioms sourceDiagonalFeynmanKacPartial_haar_ge_one
#print axioms bf4MehlerVacuumEmptyHalf_eq_haar
#print axioms bf4MehlerGramNumerator_symmetric
#print axioms zerothDiagonalVacuumCertificate
#print axioms shiftedDiagonalVacuumCertificate
#print axioms bf4MehlerGramVacuumPartition_pos
#print axioms normalized_bf4MehlerGram_entry_eqv
#print axioms normalized_bf4MehlerGram_quadratic_nonnegative

end YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
