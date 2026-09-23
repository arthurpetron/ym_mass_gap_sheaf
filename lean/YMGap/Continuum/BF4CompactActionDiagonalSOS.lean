/-
# A sphere-relative SOS certificate for the compact BF4 action complement

The forty-coordinate BF4 action is quadratic.  On the ten quaternion
spheres, the constant ceiling `133/4` can be written as

  (133/40) * sum_{block < 10} |q_block|^2.

After multiplication by `480`, the complement is therefore the integral
quadratic form

  1596 * sum_{coordinate < 40} x_coordinate^2 - 480 A.

This file constructs its signed-edge diagonal-dominance decomposition
directly from the normalized coefficients of the genuine `(K,S)` action.
Every cross coefficient `b_ij x_i x_j` contributes

  (|b_ij|/2) (x_i + sign(b_ij) x_j)^2,

and the residual diagonal coefficients are nonnegative.  The smallest
reserve is positive; all claims are checked by the kernel evaluator on the
literal finite expression.
-/

import YMGap.Continuum.BF4CompactCoupledActionBounds
import YMGap.Continuum.SU2QuaternionHaarRingNormalizer
import YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity

namespace YMGap.Continuum.BF4CompactActionDiagonalSOS

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity

local infix:50 " ≈ " => Q'.eqv

private def spatialTemplate : PolyExpr :=
  .add
    (.mul (.const 2) (.mul (.var 0) (.var 0)))
    (.add
      (.mul (.const 2) (.mul (.var 1) (.var 1)))
      (.add
        (.mul (.const 2) (.mul (.var 2) (.var 2)))
        (.add
          (.mul (.const 2) (.mul (.var 3) (.var 3)))
          (.add
            (.mul (.const 2) (.mul (.var 4) (.var 4)))
            (.add
              (.mul (.const (-2)) (.mul (.var 0) (.var 4)))
              (.add
                (.mul (.const (-2)) (.mul (.var 1) (.var 2)))
                (.add
                  (.mul (.const (-2)) (.mul (.var 1) (.var 3)))
                  (.add
                    (.mul (.const 2) (.mul (.var 1) (.var 4)))
                    (.add
                      (.mul (.const 2) (.mul (.var 2) (.var 3)))
                      (.add
                        (.mul (.const (-2)) (.mul (.var 2) (.var 4)))
                        (.mul (.const (-2))
                          (.mul (.var 3) (.var 4)))))))))))))

private def kineticTemplate : PolyExpr :=
  let x0 := .var 0; let x1 := .var 1; let x2 := .var 2
  let x3 := .var 3; let x4 := .var 4
  .add (.mul (.const 10) (.mul x0 x0))
    (.add (.mul (.const 10) (.mul x1 x1))
      (.add (.mul (.const 10) (.mul x2 x2))
        (.add (.mul (.const 10) (.mul x3 x3))
          (.add (.mul (.const 10) (.mul x4 x4))
            (.add (.mul (.const 2) (.mul x0 x1))
              (.add (.mul (.const (-4)) (.mul x0 x2))
                (.add (.mul (.const (-2)) (.mul x0 x3))
                  (.add (.mul (.const (-8)) (.mul x0 x4))
                    (.add (.mul (.const (-10)) (.mul x1 x2))
                      (.add (.mul (.const (-8)) (.mul x1 x3))
                        (.add (.mul (.const 10) (.mul x1 x4))
                          (.add (.mul (.const 10) (.mul x2 x3))
                            (.add (.mul (.const (-8)) (.mul x2 x4))
                              (.mul (.const (-10))
                                (.mul x3 x4)))))))))))))))

private def clearedColorActionExpr
    (color : Fin 3) : PolyExpr :=
  .add
    (.mul (.const 5)
      (substituteVariables
        (differenceReplacement color) kineticTemplate))
    (.add
      (.mul (.const 60)
        (substituteVariables
          (sourceReplacement color) spatialTemplate))
      (.mul (.const 60)
        (substituteVariables
          (targetReplacement color) spatialTemplate)))

/-- The exact integer expression `480 A` for the genuine three-colour
compact BF4 action. -/
def clearedCompactActionExpr : PolyExpr :=
  lieColorIndices.foldr
    (fun color total =>
      .add (clearedColorActionExpr color) total)
    (.const 0)

private def coordinateSquareExpr (coordinate : Nat) : PolyExpr :=
  .mul (.var coordinate) (.var coordinate)

private def sumExpr : List PolyExpr → PolyExpr
  | [] => .const 0
  | head :: rest => .add head (sumExpr rest)

/-- Sum of the ten quaternion radius squares in forty coordinates. -/
def tenRadiusSumExpr : PolyExpr :=
  sumExpr ((List.range 40).map coordinateSquareExpr)

/-- The cleared sphere-relative complement `480 * (133/4 - A)`. -/
def clearedSphereComplementExpr : PolyExpr :=
  .add
    (.mul (.const 1596) tenRadiusSumExpr)
    (.neg clearedCompactActionExpr)

/-! The action coefficient lookup used to normalize the complete forty-variable
quadratic once for every queried pair.  In particular, constructing each
diagonal reserve rebuilt that normal form while filtering all `choose(40, 2)`
pairs.  The two small tables below are the coefficients already displayed in
`spatialTemplate` and `kineticTemplate`; the unchanged final normal-form check
at the end of the file independently checks their use in the assembled SOS. -/

private def spatialTemplateCoefficient
    (left right : Nat) : Int :=
  match min left right, max left right with
  | 0, 0 => 2
  | 1, 1 => 2
  | 2, 2 => 2
  | 3, 3 => 2
  | 4, 4 => 2
  | 0, 4 => -2
  | 1, 2 => -2
  | 1, 3 => -2
  | 1, 4 => 2
  | 2, 3 => 2
  | 2, 4 => -2
  | 3, 4 => -2
  | _, _ => 0

private def kineticTemplateCoefficient
    (left right : Nat) : Int :=
  match min left right, max left right with
  | 0, 0 => 10
  | 1, 1 => 10
  | 2, 2 => 10
  | 3, 3 => 10
  | 4, 4 => 10
  | 0, 1 => 2
  | 0, 2 => -4
  | 0, 3 => -2
  | 0, 4 => -8
  | 1, 2 => -10
  | 1, 3 => -8
  | 1, 4 => 10
  | 2, 3 => 10
  | 2, 4 => -8
  | 3, 4 => -10
  | _, _ => 0

/-- Decode a used imaginary quaternion coordinate as
`(isTarget, holonomy, colour)`.  Scalar coordinates and coordinates outside
the forty-coordinate carrier do not occur in the action. -/
private def actionCoordinateData
    (coordinate : Nat) : Option (Bool × Nat × Nat) :=
  if coordinate < 20 then
    let component := coordinate % 4
    if component = 0 then none
    else some (false, coordinate / 4, component - 1)
  else if coordinate < 40 then
    let offset := coordinate - 20
    let component := offset % 4
    if component = 0 then none
    else some (true, offset / 4, component - 1)
  else none

private def actionCoefficient
    (left right : Nat) : Int :=
  match actionCoordinateData left, actionCoordinateData right with
  | some (leftTarget, leftHolonomy, leftColour),
      some (rightTarget, rightHolonomy, rightColour) =>
      if leftColour != rightColour then 0
      else
        let kinetic :=
          kineticTemplateCoefficient leftHolonomy rightHolonomy
        if leftTarget = rightTarget then
          5 * kinetic +
            60 * spatialTemplateCoefficient leftHolonomy rightHolonomy
        else if leftHolonomy = rightHolonomy then
          -10 * kinetic
        else
          -5 * kinetic
  | _, _ => 0

private def complementCrossCoefficient
    (left right : Nat) : Int :=
  -(actionCoefficient left right)

def edgeWeight
    (left right : Nat) : Int :=
  Int.ofNat
    ((complementCrossCoefficient left right).natAbs / 2)

private def allCoordinatePairs : List (Nat × Nat) :=
  (List.range 40).flatMap fun left =>
    ((List.range (40 - (left + 1))).map fun offset =>
      (left, left + 1 + offset))

/-- Exactly the nonzero off-diagonal edges of the cleared complement. -/
def activeCoordinatePairs : List (Nat × Nat) :=
  allCoordinatePairs.filter fun pair =>
    edgeWeight pair.1 pair.2 != 0

def signedEdgeLinearExpr
    (left right : Nat) : PolyExpr :=
  if complementCrossCoefficient left right < 0 then
    .add (.var left) (.neg (.var right))
  else
    .add (.var left) (.var right)

private def edgeSquareExpr
    (pair : Nat × Nat) : PolyExpr :=
  let linear :=
    signedEdgeLinearExpr pair.1 pair.2
  .mul (.const (edgeWeight pair.1 pair.2))
    (.mul linear linear)

private def incidentWeight
    (coordinate : Nat) : Int :=
  activeCoordinatePairs.foldl
    (fun total pair =>
      if pair.1 = coordinate ∨ pair.2 = coordinate then
        total + edgeWeight pair.1 pair.2
      else total)
    0

/-- Residual diagonal coefficient after all signed edge squares have been
removed. -/
def diagonalReserve (coordinate : Nat) : Int :=
  1596 - actionCoefficient coordinate coordinate -
    incidentWeight coordinate

private def diagonalSquareExpr
    (coordinate : Nat) : PolyExpr :=
  .mul (.const (diagonalReserve coordinate))
    (coordinateSquareExpr coordinate)

/-- The finite SOS carrier: first the signed off-diagonal edge forms, then
the forty residual coordinate forms. -/
def compactActionComplementSOSEntries :
    List (Int × PolyExpr) :=
  (activeCoordinatePairs.map fun pair =>
      (edgeWeight pair.1 pair.2,
        signedEdgeLinearExpr pair.1 pair.2)) ++
    ((List.range 40).map fun coordinate =>
      (diagonalReserve coordinate, .var coordinate))

private def weightedSquareExpr
    (entry : Int × PolyExpr) : PolyExpr :=
  .mul (.const entry.1)
    (.mul entry.2 entry.2)

/-- The literal signed-edge plus diagonal-square certificate. -/
def compactActionComplementSOSExpr : PolyExpr :=
  sumExpr
    (compactActionComplementSOSEntries.map
      weightedSquareExpr)

/-- The coefficient-generated SOS expands exactly to the cleared complement. -/
theorem compactActionComplementSOS_normal :
    normalize clearedSphereComplementExpr =
      normalize compactActionComplementSOSExpr := by
  decide

/-- Every one of the forty residual diagonal coefficients is nonnegative. -/
theorem diagonalReserve_nonnegative
    (coordinate : Fin 40) :
    (0 : Int) ≤ diagonalReserve coordinate.val := by
  revert coordinate
  decide

/-- In fact the certificate is strict in every coordinate. -/
theorem diagonalReserve_positive
    (coordinate : Fin 40) :
    (0 : Int) < diagonalReserve coordinate.val := by
  revert coordinate
  decide

/-- All weights in the exposed finite SOS carrier are nonnegative. -/
theorem compactActionComplementSOSEntries_nonnegative :
    ∀ entry,
      entry ∈ compactActionComplementSOSEntries →
        (0 : Int) ≤ entry.1 := by
  decide

/-- Exact smallest diagonal reserve, after the `480` denominator clearing. -/
theorem diagonalReserve_minimum :
    (List.range 40).foldl
        (fun current coordinate =>
          min current (diagonalReserve coordinate))
        1596 =
      956 := by
  decide

end YMGap.Continuum.BF4CompactActionDiagonalSOS

#print axioms YMGap.Continuum.BF4CompactActionDiagonalSOS.compactActionComplementSOS_normal
#print axioms YMGap.Continuum.BF4CompactActionDiagonalSOS.diagonalReserve_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionDiagonalSOS.diagonalReserve_positive
#print axioms YMGap.Continuum.BF4CompactActionDiagonalSOS.compactActionComplementSOSEntries_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionDiagonalSOS.diagonalReserve_minimum
