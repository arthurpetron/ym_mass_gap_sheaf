/-
# Completely-positive order for the genuine compact BF4 action

The complement certificate proves `133/4 - A >= 0` in polynomial-square
Haar order.  To bound its powers uniformly one also needs the opposite
endpoint, namely `A >= 0` in that same order—not merely pointwise
nonnegativity of the quadratic form.

This file turns the exact LDL certificates for the physical kinetic and
spatial matrices into one finite forty-coordinate SOS.  Multiplying
`480 A` by `87120` clears both LDL denominators:

* the kinetic LDL sum receives factor `4`;
* each spatial LDL sum receives factor `108900`.

The resulting 45 squares are checked reflectively against the literal
three-colour coupled BF4 action.  The final theorem transports the
certificate through the already-proved coefficientwise compiler bridge, so
its action is definitionally the one used by `geometricMehlerTaylorTerm`.

## Axiom gate

Finite exact polynomial algebra only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompactActionSphereShift

namespace YMGap.Continuum.BF4CompactActionPhysicalCPOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.BF4CompactActionDiagonalSOS
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal LDL square carriers -/

private def spatialLDLSquareEntries : List (Int × PolyExpr) :=
  let z0 :=
    .add (.mul (.const 2) (.var 0)) (.neg (.var 4))
  let z1 :=
    .add
      (.add
        (.add (.mul (.const 2) (.var 1))
          (.neg (.var 2)))
        (.neg (.var 3)))
      (.var 4)
  let z2 :=
    .add
      (.add (.mul (.const 3) (.var 2))
        (.var 3))
      (.neg (.var 4))
  let z3 :=
    .add (.mul (.const 4) (.var 3))
      (.neg (.var 4))
  [(24, z0), (24, z1), (8, z2), (4, z3),
   (36, .var 4)]

private def kineticLDLSquareEntries : List (Int × PolyExpr) :=
  let z0 :=
    .add
      (.add
        (.add
          (.add (.mul (.const 10) (.var 0))
            (.var 1))
          (.mul (.const (-2)) (.var 2)))
        (.neg (.var 3)))
      (.mul (.const (-4)) (.var 4))
  let z1 :=
    .add
      (.add
        (.add (.mul (.const 33) (.var 1))
          (.mul (.const (-16)) (.var 2)))
        (.mul (.const (-13)) (.var 3)))
      (.mul (.const 18) (.var 4))
  let z2 :=
    .add
      (.add (.mul (.const 10) (.var 2))
        (.mul (.const 4) (.var 3)))
      (.mul (.const (-3)) (.var 4))
  let z3 :=
    .add (.mul (.const 3) (.var 3))
      (.neg (.var 4))
  [(10890, z0), (990, z1), (7920, z2),
   (87120, z3), (435600, .var 4)]

private def scaleSOSEntry
    (scale : Int) (entry : Int × PolyExpr) :
    Int × PolyExpr :=
  (scale * entry.1, entry.2)

private def substituteSOSEntry
    (replacement : Nat → PolyExpr)
    (entry : Int × PolyExpr) : Int × PolyExpr :=
  (entry.1, substituteVariables replacement entry.2)

private def compactActionColorSOSEntries
    (color : Fin 3) : List (Int × PolyExpr) :=
  (kineticLDLSquareEntries.map fun entry =>
    substituteSOSEntry (differenceReplacement color)
      (scaleSOSEntry 4 entry)) ++
  (spatialLDLSquareEntries.map fun entry =>
    substituteSOSEntry (sourceReplacement color)
      (scaleSOSEntry 108900 entry)) ++
  (spatialLDLSquareEntries.map fun entry =>
    substituteSOSEntry (targetReplacement color)
      (scaleSOSEntry 108900 entry))

/-- Forty-coordinate 45-square carrier: fifteen LDL squares for each of the
three Lie colours. -/
def compactPhysicalActionSOSEntries :
    List (Int × PolyExpr) :=
  lieColorIndices.flatMap compactActionColorSOSEntries

private def sumExprLocal : List PolyExpr → PolyExpr
  | [] => .const 0
  | expression :: rest =>
      .add expression (sumExprLocal rest)

private def weightedSquareExprLocal
    (entry : Int × PolyExpr) : PolyExpr :=
  .mul (.const entry.1)
    (.mul entry.2 entry.2)

/-- Literal SOS expression for `87120 * (480 A)`. -/
def compactPhysicalActionSOSExpr : PolyExpr :=
  sumExprLocal
    (compactPhysicalActionSOSEntries.map
      weightedSquareExprLocal)

/-- The denominator-cleared physical action used on the other side of the
reflective identity. -/
def scaledClearedCompactActionExpr : PolyExpr :=
  .mul (.const 87120) clearedCompactActionExpr

/-- Exact reflective LDL reconstruction of the genuine coupled action. -/
theorem scaledClearedCompactAction_sos_normal :
    normalize scaledClearedCompactActionExpr =
      normalize compactPhysicalActionSOSExpr := by
  decide

theorem compactPhysicalActionSOSEntries_nonnegative :
    ∀ entry, entry ∈ compactPhysicalActionSOSEntries →
      (0 : Int) ≤ entry.1 := by
  decide

private theorem compactPhysicalActionSOSEntries_supported :
    ∀ entry, entry ∈ compactPhysicalActionSOSEntries →
      SupportedQuaternionBlocks 10
        (exprToRatPoly entry.2) := by
  have hall :
      List.all compactPhysicalActionSOSEntries
        (fun entry =>
          polynomialSupportedBool 10
            (exprToRatPoly entry.2)) = true := by
    decide
  intro entry hentry
  exact supported_of_bool 10
    (exprToRatPoly entry.2)
    (List.all_eq_true.mp hall entry hentry)

def compactPhysicalActionSOSPolynomial : RatPoly :=
  compactPhysicalActionSOSEntries.foldr
    (fun entry total =>
      polyAdd (polynomialSOSEntry entry) total)
    (exprToRatPoly (.const 0))

theorem compactPhysicalActionSOSPolynomial_eq :
    compactPhysicalActionSOSPolynomial =
      exprToRatPoly compactPhysicalActionSOSExpr := by
  decide

/-! ## 2. CP order before and after denominator cancellation -/

theorem scaledClearedCompactAction_cp
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    (0 : Q') ≤
      tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          (exprToRatPoly
            scaledClearedCompactActionExpr)) := by
  have hnormal :
      tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              scaledClearedCompactActionExpr)) ≈
        tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              compactPhysicalActionSOSExpr)) :=
    quaternionHaar_mul_expr_congr_of_normal_eq
      10 scaledClearedCompactActionExpr
      compactPhysicalActionSOSExpr
      scaledClearedCompactAction_sos_normal
      (polyMul polynomial polynomial)
  have hsos :
      (0 : Q') ≤
        tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            (exprToRatPoly
              compactPhysicalActionSOSExpr)) := by
    rw [← compactPhysicalActionSOSPolynomial_eq]
    exact sos_entries_nonnegative
      10 polynomial hsupport
      compactPhysicalActionSOSEntries
      compactPhysicalActionSOSEntries_nonnegative
      compactPhysicalActionSOSEntries_supported
  exact Q'.le_trans' _ _ _ hsos
    (Q'.le_of_eqv
      (Q'.eqv_symm hnormal))

theorem scaledClearedCompactActionPolynomial_eq :
    exprToRatPoly scaledClearedCompactActionExpr =
      polySmul (Q'.ofInt 87120)
        (exprToRatPoly clearedCompactActionExpr) := by
  decide

/-- The integer-denominator-cleared action itself is CP-positive. -/
theorem clearedCompactAction_cp
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    (0 : Q') ≤
      tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          (exprToRatPoly
            clearedCompactActionExpr)) := by
  have hscaled :=
    scaledClearedCompactAction_cp polynomial hsupport
  rw [scaledClearedCompactActionPolynomial_eq] at hscaled
  have hscale :=
    quaternionHaar_polyMul_smul_right
      10 (Q'.ofInt 87120)
      (polyMul polynomial polynomial)
      (exprToRatPoly clearedCompactActionExpr)
  have hproduct :
      (0 : Q') ≤
        Q'.ofInt 87120 *
          tenfoldHaar
            (polyMul (polyMul polynomial polynomial)
              (exprToRatPoly
                clearedCompactActionExpr)) :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv hscale)
  apply Q'.le_of_mul_le_mul_left
    (c := Q'.ofInt 87120)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.zero_mul_eqv
          (Q'.ofInt 87120)))
      hproduct
  · decide

/-- **Genuine physical action CP order.**

For every supported boundary polynomial `P`,

  `0 <= H_10(P² A)`,

where `A` is definitionally the coupled `(K,S)` polynomial in the physical
Feynman--Kac Taylor kernel.
-/
theorem compactPhysicalAction_cp
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    (0 : Q') ≤
      tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          compactCoupledBF4ActionPolynomial) := by
  have hcleared :=
    clearedCompactAction_cp polynomial hsupport
  have hnormalized :
      (0 : Q') ≤
        tenfoldHaar
          (polyMul (polyMul polynomial polynomial)
            compactActionPolynomialFromCleared) := by
    have hscale :=
      quaternionHaar_polyMul_smul_right
        10 oneOver480
        (polyMul polynomial polynomial)
        (exprToRatPoly clearedCompactActionExpr)
    have hproduct :
        (0 : Q') ≤
          oneOver480 *
            tenfoldHaar
              (polyMul (polyMul polynomial polynomial)
                (exprToRatPoly
                  clearedCompactActionExpr)) :=
      Q'.mul_nonneg _ _ (by decide) hcleared
    exact Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (Q'.eqv_symm hscale))
  have hbridge :=
    compactActionPolynomialFromCleared_haar_eq_physical
      (polyMul polynomial polynomial)
  exact Q'.le_trans' _ _ _ hnormalized
    (Q'.le_of_eqv hbridge)

/-! ## 3. The exact two-sided CP window -/

/-- The genuine physical action is bounded above by `133/4` in the same
polynomial-square Haar order. -/
theorem compactPhysicalAction_square_le_ceiling
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          compactCoupledBF4ActionPolynomial) ≤
      compactCoupledBF4ActionCeiling *
        tenfoldHaar
          (polyMul polynomial polynomial) := by
  let square := polyMul polynomial polynomial
  let actionValue :=
    tenfoldHaar
      (polyMul square
        compactCoupledBF4ActionPolynomial)
  let complementValue :=
    tenfoldHaar
      (polyMul square
        compactActionComplementPolynomial)
  have haction : (0 : Q') ≤ actionValue :=
    compactPhysicalAction_cp polynomial hsupport
  have hcomplement : (0 : Q') ≤ complementValue :=
    compactActionComplement_cp polynomial hsupport
  have hsum :
      complementValue + actionValue ≈
        compactCoupledBF4ActionCeiling *
          tenfoldHaar square :=
    by
      simpa [square, actionValue, complementValue] using
        (compactPhysicalAction_sphere_shift square)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg
      actionValue complementValue hcomplement)
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv
          actionValue complementValue)
        hsum))

/-- The compact complement is likewise bounded above by `133/4` in
polynomial-square Haar order. -/
theorem compactActionComplement_square_le_ceiling
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    tenfoldHaar
        (polyMul (polyMul polynomial polynomial)
          compactActionComplementPolynomial) ≤
      compactCoupledBF4ActionCeiling *
        tenfoldHaar
          (polyMul polynomial polynomial) := by
  let square := polyMul polynomial polynomial
  let actionValue :=
    tenfoldHaar
      (polyMul square
        compactCoupledBF4ActionPolynomial)
  let complementValue :=
    tenfoldHaar
      (polyMul square
        compactActionComplementPolynomial)
  have haction : (0 : Q') ≤ actionValue :=
    compactPhysicalAction_cp polynomial hsupport
  have hsum :
      complementValue + actionValue ≈
        compactCoupledBF4ActionCeiling *
          tenfoldHaar square :=
    by
      simpa [square, actionValue, complementValue] using
        (compactPhysicalAction_sphere_shift square)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg
      complementValue actionValue haction)
    (Q'.le_of_eqv hsum)

end YMGap.Continuum.BF4CompactActionPhysicalCPOrder

#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.scaledClearedCompactAction_sos_normal
#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.compactPhysicalActionSOSEntries_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.compactPhysicalActionSOSPolynomial_eq
#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.scaledClearedCompactAction_cp
#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.clearedCompactAction_cp
#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.compactPhysicalAction_cp
#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.compactPhysicalAction_square_le_ceiling
#print axioms YMGap.Continuum.BF4CompactActionPhysicalCPOrder.compactActionComplement_square_le_ceiling
