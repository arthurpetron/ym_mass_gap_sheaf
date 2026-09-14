/-
# Rooted animal tours pay for neighbor choices only on descent

A tour is exactly reconstructed from its binary descend/return shape and
the ordered list of descent indices. A k-node tree has k-1 descent indices,
not 2*(k-1). Thus canonical rooted animals of size k at a fixed root have
support-recovering codes in a carrier of size (4*D)^(k-1), instead of the
older (D+1)^(2*(k-1)). This is a reversible recoding of the existing genuine
BFS tree, not an assumed injection or a replacement lattice model.

Forest assembly and counting the full original spatial-pair family remain
separate obligations. No weight or continuum assertion is made here.
-/

import YMGap.Continuum.FiniteRootedAnimalTourCode
import YMGap.Continuum.BF4ExactSlabTwoCapLocalCode

namespace YMGap.Continuum.FiniteRootedAnimalDescentCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode

def shape {D : Nat} : List (Fin (D+1)) → List (Fin 2)
  | [] => []
  | x::xs => (if x.val < D then ⟨1,by decide⟩ else ⟨0,by decide⟩) :: shape xs

def descents {D : Nat} : List (Fin (D+1)) → List (Fin D)
  | [] => []
  | x::xs => if h : x.val < D then ⟨x.val,h⟩ :: descents xs else descents xs

def inflate {D : Nat} : List (Fin 2) → List (Fin D) → List (Fin (D+1))
  | [], _ => []
  | b::bs, ds => if b.val = 0 then ⟨D,Nat.lt_succ_self D⟩ :: inflate bs ds else
      match ds with
      | [] => []
      | d::rest => ⟨d.val,Nat.lt_succ_of_lt d.isLt⟩ :: inflate bs rest

theorem inflate_shape_append {D : Nat} : ∀ (word : List (Fin (D+1)))
    (bits : List (Fin 2)) (ds : List (Fin D)),
    inflate (shape word ++ bits) (descents word ++ ds) = word ++ inflate bits ds
  | [], _, _ => rfl
  | x::xs, bits, ds => by
    by_cases h : x.val < D
    · simp only [shape,descents,h,↓reduceIte,↓reduceDIte,List.cons_append,inflate,
        Nat.one_ne_zero,inflate_shape_append xs bits ds]
    · have hx : (⟨D,Nat.lt_succ_self D⟩ : Fin (D+1))=x := Fin.ext (by
        change D=x.val
        have hxlt := x.isLt
        omega)
      simp only [shape,descents,h,↓reduceIte,↓reduceDIte,List.cons_append,inflate,hx,
        inflate_shape_append xs bits ds]

theorem inflate_shape {D : Nat} (word : List (Fin (D+1))) :
    inflate (shape word) (descents word)=word := by
  simpa only [List.append_nil,inflate] using inflate_shape_append word [] []

theorem shape_length {D : Nat} : ∀ word : List (Fin (D+1)), (shape word).length=word.length
  | [] => rfl
  | _::xs => congrArg Nat.succ (shape_length xs)

theorem descents_append {D : Nat} : ∀ (left right : List (Fin (D+1))),
    descents (left++right)=descents left++descents right
  | [], _ => rfl
  | x::xs, right => by
    by_cases h : x.val < D <;>
      simp only [List.cons_append,descents,h,↓reduceDIte,descents_append xs right]

mutual
  theorem tree_descents_length {BL : BddLattice} : ∀ tree : RTree BL,
      (descents (RTree.tour tree)).length+1=(RTree.nodes tree).length
    | .node _ children => by
      change (descents (RTree.tourList children)).length+1=(RTree.nodesList children).length+1
      rw [children_descents_length children]
  theorem children_descents_length {BL : BddLattice} :
      ∀ children : List (Fin BL.D × RTree BL),
      (descents (RTree.tourList children)).length=(RTree.nodesList children).length
    | [] => rfl
    | (i,tree)::rest => by
      simp only [RTree.tourList,descents,i.isLt,↓reduceDIte,descents_append,
        Nat.lt_irrefl,List.length_cons,List.length_append,RTree.nodesList]
      have ht := tree_descents_length tree
      have hr := children_descents_length rest
      omega
end

abbrev Code (D : Nat) := List (Fin 2) × List (Fin D)

def code {BL : BddLattice} (animal : RootedConnectedAnimal BL) : Code BL.D :=
  (shape (rootedAnimalTourCode animal),descents (rootedAnimalTourCode animal))

theorem code_lengths {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    (code animal).1.length=2*(animal.support.length-1) ∧
      (code animal).2.length=animal.support.length-1 := by
  constructor
  · exact (shape_length _).trans (rootedAnimalTourCode_length animal)
  · have ht := tree_descents_length (rootedAnimalTree animal)
    rw [rootedAnimalTree_nodes_length] at ht
    change (descents (RTree.tour (rootedAnimalTree animal))).length=animal.support.length-1
    omega

def carrier (D size : Nat) : List (Code D) :=
  cartesian (choiceSeqs 2 (2*(size-1))) (choiceSeqs D (size-1))

theorem code_mem {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    code animal ∈ carrier BL.D animal.support.length :=
  (mem_cartesian_iff _ _ _).mpr ⟨mem_choiceSeqs_of_length _ _ _ (code_lengths animal).1,
    mem_choiceSeqs_of_length _ _ _ (code_lengths animal).2⟩

theorem carrier_length (D size : Nat) : (carrier D size).length=(4*D)^(size-1) := by
  rw [carrier,cartesian_length,choiceSeqs_length,choiceSeqs_length,Nat.pow_mul,← Nat.mul_pow]

theorem code_decode {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    sameSupport animal.support (decode BL animal.root (inflate (code animal).1 (code animal).2)) := by
  rw [code,inflate_shape]
  exact rootedAnimalTourCode_decode_sameSupport animal

theorem code_eq_sameSupport {BL : BddLattice} (left right : RootedConnectedAnimal BL)
    (hroot : left.root=right.root) (hcode : code left=code right) :
    sameSupport left.support right.support := by
  have hl := code_decode left
  rw [hroot,hcode] at hl
  exact sameSupport_trans hl (sameSupport_symm (code_decode right))

end YMGap.Continuum.FiniteRootedAnimalDescentCode

#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.shape
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.descents
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.inflate
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.inflate_shape_append
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.inflate_shape
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.shape_length
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.descents_append
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.tree_descents_length
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.children_descents_length
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.code
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.code_lengths
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.carrier
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.code_mem
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.carrier_length
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.code_decode
#print axioms YMGap.Continuum.FiniteRootedAnimalDescentCode.code_eq_sameSupport
