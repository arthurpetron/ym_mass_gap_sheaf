/-
# A reversible binary-shape code for an entire rooted forest

One outer opening/closing pair surrounds each tree tour. At depth zero an
opening reads a root; at positive depth it reads a neighbor index. Thus no
extra alphabet symbol or independent list of component sizes is needed.
The code has 2*S bits, c roots, and S-c descent indices. The decoder returns
the original root/tour records, including one harmless terminal backtrack.

This is a concrete algorithm and reconstruction proof, not a forest-count
hypothesis. Its application to original spatial components and the resulting
weighted family bound are separate steps.
-/

import YMGap.Continuum.FiniteRootedAnimalDescentCode

namespace YMGap.Continuum.FiniteRootedForestCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteRootedAnimalDescentCode

inductive Op (A : Type) (D : Nat) : Type
  | root (value : A)
  | symbol (value : Fin (D+1))

def expand {A : Type} {D : Nat} :
    Nat → List (Fin 2) → List A → List (Fin D) → List (Op A D)
  | _, [], _, _ => []
  | depth, bit::bits, roots, ds =>
    if bit.val=0 then .symbol ⟨D,Nat.lt_succ_self D⟩ :: expand (depth-1) bits roots ds
    else if depth=0 then
      match roots with
      | [] => []
      | r::rest => .root r :: expand 1 bits rest ds
    else
      match ds with
      | [] => []
      | d::rest => .symbol ⟨d.val,Nat.lt_succ_of_lt d.isLt⟩ :: expand (depth+1) bits roots rest

theorem shape_append {D : Nat} : ∀ (xs ys : List (Fin (D+1))),
    shape (xs++ys)=shape xs++shape ys
  | [], _ => rfl
  | _::xs, ys => congrArg (List.cons _) (shape_append xs ys)

mutual
  theorem tree_expand {BL : BddLattice} : ∀ (tree : RTree BL) (depth : Nat)
      (bits : List (Fin 2)) (roots : List BL.toLattice.Plaquette) (ds : List (Fin BL.D)),
      expand (depth+1) (shape (RTree.tour tree)++bits) roots
        (descents (RTree.tour tree)++ds) =
      (RTree.tour tree).map Op.symbol ++ expand (depth+1) bits roots ds
    | .node _ children, depth, bits, roots, ds =>
      children_expand children depth bits roots ds
  theorem children_expand {BL : BddLattice} :
      ∀ (children : List (Fin BL.D × RTree BL)) (depth : Nat)
      (bits : List (Fin 2)) (roots : List BL.toLattice.Plaquette) (ds : List (Fin BL.D)),
      expand (depth+1) (shape (RTree.tourList children)++bits) roots
        (descents (RTree.tourList children)++ds) =
      (RTree.tourList children).map Op.symbol ++ expand (depth+1) bits roots ds
    | [], _, _, _, _ => rfl
    | (i,tree)::rest, depth, bits, roots, ds => by
      simp only [RTree.tourList,shape,shape_append,descents,descents_append,i.isLt,
        Nat.lt_irrefl,↓reduceIte,↓reduceDIte,List.cons_append,List.append_assoc,
        List.map_cons,List.map_append,expand,Nat.succ_ne_zero]
      rw [tree_expand tree (depth+1)]
      simp only [expand,↓reduceIte,Nat.add_sub_cancel]
      rw [children_expand rest depth bits roots ds]
end

def bits {BL : BddLattice} : List (RTree BL) → List (Fin 2)
  | [] => []
  | tree::rest => ⟨1,by decide⟩ :: (shape (RTree.tour tree) ++ ⟨0,by decide⟩ :: bits rest)

def roots {BL : BddLattice} (forest : List (RTree BL)) : List BL.toLattice.Plaquette :=
  forest.map RTree.root

def choices {BL : BddLattice} : List (RTree BL) → List (Fin BL.D)
  | [] => []
  | tree::rest => descents (RTree.tour tree) ++ choices rest

def tape {BL : BddLattice} : List (RTree BL) → List (Op BL.toLattice.Plaquette BL.D)
  | [] => []
  | tree::rest => .root (RTree.root tree) ::
      ((RTree.tour tree ++ [(⟨BL.D,Nat.lt_succ_self BL.D⟩ : Fin (BL.D+1))]).map Op.symbol ++ tape rest)

theorem expand_forest {BL : BddLattice} : ∀ forest : List (RTree BL),
    expand 0 (bits forest) (roots forest) (choices forest)=tape forest
  | [] => rfl
  | tree::rest => by
    simp only [bits,roots,List.map_cons,choices,expand,Nat.one_ne_zero,↓reduceIte,tape]
    rw [tree_expand tree 0]
    simp only [expand,↓reduceIte,Nat.zero_add,Nat.sub_self,List.map_append,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,List.append_assoc]
    rw [show expand 0 (bits rest) (rest.map RTree.root) (choices rest)=tape rest from expand_forest rest]

def readPrefix {A : Type} {D : Nat} : List (Op A D) → List (Fin (D+1)) × List (Op A D)
  | [] => ([],[])
  | .root r::rest => ([],.root r::rest)
  | .symbol s::rest => let next := readPrefix rest; (s::next.1,next.2)

theorem prefix_symbols {A : Type} {D : Nat} :
    ∀ (word : List (Fin (D+1))) (rest : List (Op A D)),
    readPrefix (word.map Op.symbol++rest)=(word++(readPrefix rest).1,(readPrefix rest).2)
  | [], _ => rfl
  | s::word, rest => by
    simp only [List.map_cons,List.cons_append,readPrefix,prefix_symbols word rest]

theorem prefix_tape {BL : BddLattice} (forest : List (RTree BL)) :
    readPrefix (tape forest)=([],tape forest) := by cases forest <;> rfl

def records {A : Type} {D : Nat} : Nat → List (Op A D) → List (A × List (Fin (D+1)))
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, .root r::rest =>
    let next := readPrefix rest
    (r,next.1)::records fuel next.2
  | _+1, .symbol _::_ => []

def originalRecords {BL : BddLattice} (forest : List (RTree BL)) :
    List (BL.toLattice.Plaquette × List (Fin (BL.D+1))) :=
  forest.map (fun tree => (RTree.root tree,RTree.tour tree++[⟨BL.D,Nat.lt_succ_self BL.D⟩]))

theorem records_tape {BL : BddLattice} : ∀ forest : List (RTree BL),
    records forest.length (tape forest)=originalRecords forest
  | [] => rfl
  | tree::rest => by
    simp only [List.length_cons,tape,records,prefix_symbols,prefix_tape,List.append_nil,
      originalRecords,List.map_cons]
    rw [records_tape rest]
    rfl

abbrev Code (A : Type) (D : Nat) := List (Fin 2) × List A × List (Fin D)

def encode {BL : BddLattice} (forest : List (RTree BL)) : Code BL.toLattice.Plaquette BL.D :=
  (bits forest,roots forest,choices forest)

def decodeRecords {A : Type} {D : Nat} (code : Code A D) : List (A × List (Fin (D+1))) :=
  records code.2.1.length (expand 0 code.1 code.2.1 code.2.2)

theorem decode_encode {BL : BddLattice} (forest : List (RTree BL)) :
    decodeRecords (encode forest)=originalRecords forest := by
  unfold decodeRecords encode
  rw [expand_forest,roots,List.length_map,records_tape]

def mass {BL : BddLattice} : List (RTree BL) → Nat
  | [] => 0
  | tree::rest => (RTree.nodes tree).length+mass rest

theorem bits_length {BL : BddLattice} : ∀ forest : List (RTree BL),
    (bits forest).length=2*mass forest
  | [] => rfl
  | tree::rest => by
    simp only [bits,List.length_cons,List.length_append,shape_length,mass,bits_length rest]
    have ht := RTree.tour_length_aux tree
    omega

theorem choices_length {BL : BddLattice} : ∀ forest : List (RTree BL),
    (choices forest).length+forest.length=mass forest
  | [] => rfl
  | tree::rest => by
    simp only [choices,List.length_append,List.length_cons,mass]
    have ht := tree_descents_length tree
    have hr := choices_length rest
    omega

end YMGap.Continuum.FiniteRootedForestCode

#print axioms YMGap.Continuum.FiniteRootedForestCode.expand
#print axioms YMGap.Continuum.FiniteRootedForestCode.shape_append
#print axioms YMGap.Continuum.FiniteRootedForestCode.tree_expand
#print axioms YMGap.Continuum.FiniteRootedForestCode.children_expand
#print axioms YMGap.Continuum.FiniteRootedForestCode.bits
#print axioms YMGap.Continuum.FiniteRootedForestCode.roots
#print axioms YMGap.Continuum.FiniteRootedForestCode.choices
#print axioms YMGap.Continuum.FiniteRootedForestCode.tape
#print axioms YMGap.Continuum.FiniteRootedForestCode.expand_forest
#print axioms YMGap.Continuum.FiniteRootedForestCode.readPrefix
#print axioms YMGap.Continuum.FiniteRootedForestCode.prefix_symbols
#print axioms YMGap.Continuum.FiniteRootedForestCode.prefix_tape
#print axioms YMGap.Continuum.FiniteRootedForestCode.records
#print axioms YMGap.Continuum.FiniteRootedForestCode.originalRecords
#print axioms YMGap.Continuum.FiniteRootedForestCode.records_tape
#print axioms YMGap.Continuum.FiniteRootedForestCode.encode
#print axioms YMGap.Continuum.FiniteRootedForestCode.decodeRecords
#print axioms YMGap.Continuum.FiniteRootedForestCode.decode_encode
#print axioms YMGap.Continuum.FiniteRootedForestCode.mass
#print axioms YMGap.Continuum.FiniteRootedForestCode.bits_length
#print axioms YMGap.Continuum.FiniteRootedForestCode.choices_length
