/-
Finite G₂ root-coordinate certificate.

This is explicit rank-two integer data in the convention that α is short,
β is long, and the Cartan matrix is [[2,-1],[-3,2]].  Coordinates are
relative to (α,β).  The file checks the six positive roots, their twelve
signed roots, the two simple reflections, pairings, and squared lengths by
kernel computation / integer arithmetic.

Scope boundary: this certificate is not a realization of a compact group,
Lie algebra, root/weight lattice theorem, representation, Haar functional,
heat operator, or Yang--Mills/OS object.  The existing G₂ center entry is a
global-form CODE only; determinant one below is not used to infer a center
or a compact-group property.
-/

import YMGap.RepTheory.CartanType
import YMGap.RepTheory.CompactSimpleGlobalForm

namespace YMGap.RepTheory.G2RootCoordinates

abbrev Root := Int × Int

/-- The six positive roots in `(α, β)` coordinates, with α short. -/
def positiveRoots : List Root :=
  [(1, 0), (0, 1), (1, 1), (2, 1), (3, 1), (3, 2)]

/-- Negation of a root coordinate pair. -/
def rootNeg (r : Root) : Root := (-r.1, -r.2)

/-- All roots, with the positive list followed by its negatives. -/
def signedRoots : List Root := positiveRoots ++ positiveRoots.map rootNeg

/-- Pairing with the short simple coroot α∨. -/
def shortCorootPairing (r : Root) : Int := 2 * r.1 - 3 * r.2

/-- Pairing with the long simple coroot β∨. -/
def longCorootPairing (r : Root) : Int := -r.1 + 2 * r.2

/-- Squared length with `(α,α)=2`, `(α,β)=-3`, `(β,β)=6`. -/
def squaredLength (r : Root) : Int :=
  2 * r.1 * r.1 - 6 * r.1 * r.2 + 6 * r.2 * r.2

/-- Reflection in the short simple root α. -/
def shortReflection (r : Root) : Root := (-r.1 + 3 * r.2, r.2)

/-- Reflection in the long simple root β. -/
def longReflection (r : Root) : Root := (r.1, r.1 - r.2)

/-- G₂'s Cartan code from the existing finite classification. -/
def cartanCode : YMGap.RG.CartanType := .G2

/-- The positive-root list has the count already recorded by the Cartan code. -/
theorem positiveRootCount_matches_code :
    positiveRoots.length = YMGap.RG.CartanType.numPosRoots cartanCode := by
  decide

/-- The six listed positive roots are distinct. -/
theorem positiveRoots_nodup : positiveRoots.Nodup := by decide

/-- The explicit twelve signed roots are distinct. -/
theorem signedRoots_nodup : signedRoots.Nodup := by decide

/-- Pairings of the positive roots with `(α∨, β∨)`, in list order. -/
theorem positiveRoot_pairings :
    positiveRoots.map (fun r => (shortCorootPairing r, longCorootPairing r)) =
      [(2, -1), (-3, 2), (-1, 1), (1, 0), (3, -1), (0, 1)] := by
  decide

/-- Squared lengths of the positive roots: short roots have length² 2 and
long roots have length² 6, in the chosen normalization. -/
theorem positiveRoot_squaredLengths :
    positiveRoots.map squaredLength = [2, 6, 2, 2, 6, 6] := by
  decide

/-- Explicit reflection action on the finite signed-root list. -/
def reflectionCloses (reflect : Root → Root) : Bool :=
  signedRoots.all (fun r => signedRoots.contains (reflect r))

/-- The short simple reflection preserves the signed root set. -/
theorem shortReflection_closes_signedRoots :
    reflectionCloses shortReflection = true := by decide

/-- The long simple reflection preserves the signed root set. -/
theorem longReflection_closes_signedRoots :
    reflectionCloses longReflection = true := by decide

/-- The short reflection is an involution on all coordinate pairs. -/
theorem shortReflection_involutive (r : Root) :
    shortReflection (shortReflection r) = r := by
  cases r with
  | mk a b =>
      apply Prod.ext <;> simp [shortReflection] <;> omega

/-- The long reflection is an involution on all coordinate pairs. -/
theorem longReflection_involutive (r : Root) :
    longReflection (longReflection r) = r := by
  cases r with
  | mk a b =>
      apply Prod.ext <;> simp [longReflection] <;> omega

/-- The finite reflection checks also preserve the chosen length function. -/
def reflectionPreservesLength (reflect : Root → Root) : Bool :=
  signedRoots.all (fun r => squaredLength (reflect r) == squaredLength r)

theorem shortReflection_preservesLength :
    reflectionPreservesLength shortReflection = true := by decide

theorem longReflection_preservesLength :
    reflectionPreservesLength longReflection = true := by decide

/-- The determinant of the displayed Cartan matrix is one, as integer data. -/
theorem cartanDeterminant_one : (2 : Int) * 2 - (-1) * (-3) = 1 := by decide

/-- The repository's G₂ center classification is the trivial CENTER CODE.
This theorem is only a pin to that existing finite code, not a group
realization or a deduction from `cartanDeterminant_one`. -/
theorem g2_centerCode_is_trivial :
    YMGap.RepTheory.simplyConnectedCenter cartanCode =
      YMGap.RepTheory.CenterShape.trivial := rfl

#print axioms positiveRootCount_matches_code
#print axioms positiveRoots_nodup
#print axioms signedRoots_nodup
#print axioms positiveRoot_pairings
#print axioms positiveRoot_squaredLengths
#print axioms shortReflection_closes_signedRoots
#print axioms longReflection_closes_signedRoots
#print axioms shortReflection_involutive
#print axioms longReflection_involutive
#print axioms shortReflection_preservesLength
#print axioms longReflection_preservesLength
#print axioms cartanDeterminant_one
#print axioms g2_centerCode_is_trivial

end YMGap.RepTheory.G2RootCoordinates
