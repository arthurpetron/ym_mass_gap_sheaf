/-
# Common-budget rooted animal descent codes

The exact binary descent code is padded independently in its shape and
descent coordinates.  Zero shape bits decode to inert backtracks, so the
resulting word is proved equal to the existing padded tour code; the extra
descent entries are never consumed.
-/

import YMGap.Continuum.FiniteRootedAnimalDescentCode

namespace YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FiniteRootedAnimalDescentCode
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode

def zeroBit : Fin 2 := ⟨0, by decide⟩

def zeroBits (n : Nat) : List (Fin 2) := List.replicate n zeroBit

def paddedCode {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (filler : Fin BL.D) (massBudget : Nat) : Code BL.D :=
  (shape (rootedAnimalTourCode animal) ++
      zeroBits (2 * massBudget - (shape (rootedAnimalTourCode animal)).length),
    descents (rootedAnimalTourCode animal) ++
      List.replicate (massBudget - (descents (rootedAnimalTourCode animal)).length) filler)

def carrier (D massBudget : Nat) : List (Code D) :=
  cartesian (choiceSeqs 2 (2 * massBudget)) (choiceSeqs D massBudget)

theorem inflate_zeroBits {BL : BddLattice} : ∀ (n : Nat) (ds : List (Fin BL.D)),
    inflate (zeroBits n) ds =
      List.replicate n (backtrackSymbol BL)
  | 0, _ => rfl
  | n+1, ds => congrArg (List.cons (backtrackSymbol BL)) (inflate_zeroBits n ds)

theorem paddedCode_length {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (filler : Fin BL.D) (massBudget : Nat)
    (hsupport : animal.support.length ≤ massBudget) :
    (paddedCode animal filler massBudget).1.length = 2 * massBudget ∧
      (paddedCode animal filler massBudget).2.length = massBudget := by
  have hshape := (code_lengths animal).1
  have hdesc := (code_lengths animal).2
  change (shape (rootedAnimalTourCode animal)).length = _ at hshape
  change (descents (rootedAnimalTourCode animal)).length = _ at hdesc
  simp only [paddedCode, zeroBits, List.length_append, List.length_replicate, hshape, hdesc]
  constructor <;> omega

theorem paddedCode_mem {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (filler : Fin BL.D) (massBudget : Nat)
    (hsupport : animal.support.length ≤ massBudget) :
    paddedCode animal filler massBudget ∈ carrier BL.D massBudget := by
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨mem_choiceSeqs_of_length _ _ _ (paddedCode_length animal filler massBudget hsupport).1,
    mem_choiceSeqs_of_length _ _ _ (paddedCode_length animal filler massBudget hsupport).2⟩

theorem carrier_length (D massBudget : Nat) :
    (carrier D massBudget).length = (4 * D)^massBudget := by
  rw [carrier, cartesian_length, choiceSeqs_length, choiceSeqs_length,
    Nat.pow_mul, ← Nat.mul_pow]

theorem inflate_paddedCode {BL : BddLattice} (animal : RootedConnectedAnimal BL)
    (filler : Fin BL.D) (massBudget : Nat) :
    inflate (paddedCode animal filler massBudget).1
      (paddedCode animal filler massBudget).2 =
      rootedAnimalPaddedTourCode animal massBudget := by
  unfold paddedCode
  rw [inflate_shape_append, inflate_zeroBits, shape_length]
  rfl

theorem paddedCode_decode_sameSupport {BL : BddLattice}
    (animal : RootedConnectedAnimal BL) (filler : Fin BL.D) (massBudget : Nat) :
    sameSupport animal.support
      (decode BL animal.root
        (inflate (paddedCode animal filler massBudget).1
          (paddedCode animal filler massBudget).2)) := by
  rw [inflate_paddedCode]
  exact rootedAnimalPaddedTourCode_decode_sameSupport animal massBudget

end YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode

#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.zeroBit
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.zeroBits
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.paddedCode
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.carrier
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.inflate_zeroBits
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.paddedCode_length
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.paddedCode_mem
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.carrier_length
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.inflate_paddedCode
#print axioms YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode.paddedCode_decode_sameSupport
