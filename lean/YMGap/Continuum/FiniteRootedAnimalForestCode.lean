/-
# Whole-forest decoding recovers the supports of the genuine BFS animals

The binary forest parser reconstructs root/tour records. Here those records
are evaluated by the actual lattice decoder. One appended return is inert,
so equality of forest codes implies equality of the original union supports.
The construction uses the existing faithful BFS trees, not supplied spanning
or decoding hypotheses.
-/

import YMGap.Continuum.FiniteRootedForestCount

namespace YMGap.Continuum.FiniteRootedAnimalForestCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FiniteRootedForestCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode

def trees {BL : BddLattice} (animals : List (RootedConnectedAnimal BL)) : List (RTree BL) :=
  animals.map rootedAnimalTree

def forestCode {BL : BddLattice} (animals : List (RootedConnectedAnimal BL)) :
    Code BL.toLattice.Plaquette BL.D := encode (trees animals)

def support {BL : BddLattice} (animals : List (RootedConnectedAnimal BL)) : List BL.toLattice.Plaquette :=
  animals.flatMap (fun a => a.support)

def decodedSupport (BL : BddLattice) (code : Code BL.toLattice.Plaquette BL.D) :
    List BL.toLattice.Plaquette := (decodeRecords code).flatMap (fun record => decode BL record.1 record.2)

theorem record_support {BL : BddLattice} (animal : RootedConnectedAnimal BL) :
    sameSupport animal.support (decode BL (RTree.root (rootedAnimalTree animal))
      (RTree.tour (rootedAnimalTree animal)++[⟨BL.D,Nat.lt_succ_self BL.D⟩])) := by
  rw [rootedAnimalTree_root]
  change sameSupport animal.support (decode BL animal.root
    (rootedAnimalTourCode animal ++ List.replicate 1 (backtrackSymbol BL)))
  rw [decode_append_replicate_backtrack]
  exact rootedAnimalTourCode_decode_sameSupport animal

theorem decodedSupport_forestCode {BL : BddLattice} (animals : List (RootedConnectedAnimal BL)) :
    decodedSupport BL (forestCode animals)=animals.flatMap (fun animal =>
      decode BL (RTree.root (rootedAnimalTree animal))
        (RTree.tour (rootedAnimalTree animal)++[⟨BL.D,Nat.lt_succ_self BL.D⟩])) := by
  rw [decodedSupport,forestCode,decode_encode]
  simp only [originalRecords,trees,List.flatMap_map]

theorem forestCode_support {BL : BddLattice} (animals : List (RootedConnectedAnimal BL)) :
    sameSupport (support animals) (decodedSupport BL (forestCode animals)) := by
  rw [decodedSupport_forestCode]
  constructor
  · intro x hx
    obtain ⟨animal,ha,hm⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨animal,ha,(record_support animal).1 x hm⟩
  · intro x hx
    obtain ⟨animal,ha,hm⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨animal,ha,(record_support animal).2 x hm⟩

theorem forestCode_eq_sameSupport {BL : BddLattice} (left right : List (RootedConnectedAnimal BL))
    (he : forestCode left=forestCode right) : sameSupport (support left) (support right) := by
  have hl := forestCode_support left
  rw [he] at hl
  exact sameSupport_trans hl (sameSupport_symm (forestCode_support right))

theorem trees_mass {BL : BddLattice} : ∀ animals : List (RootedConnectedAnimal BL),
    mass (trees animals)=(animals.map (fun a => a.support.length)).sum
  | [] => rfl
  | a::rest => by
    change (RTree.nodes (rootedAnimalTree a)).length+mass (trees rest)=
      a.support.length+(rest.map (fun b => b.support.length)).sum
    rw [rootedAnimalTree_nodes_length,trees_mass rest]

theorem trees_length {BL : BddLattice} (animals : List (RootedConnectedAnimal BL)) :
    (trees animals).length=animals.length := List.length_map _

end YMGap.Continuum.FiniteRootedAnimalForestCode

#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.trees
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.forestCode
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.support
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.decodedSupport
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.record_support
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.decodedSupport_forestCode
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.forestCode_support
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.forestCode_eq_sameSupport
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.trees_mass
#print axioms YMGap.Continuum.FiniteRootedAnimalForestCode.trees_length
