/-
# The full recoupling pentagon from constructive coordinate bases

Multiplicity-free trivalent vertices do not make a four-factor recoupling
space one-dimensional: different intermediate labels give several channels.
Consequently a scalar attached only to a pair of trees cannot represent the
physical associator in general.  The correct coherence carrier is a family of
coordinate systems on one common semantic space, one coordinate type for each
fusion tree.

This module proves the full (multi-channel) pentagon constructively.  Each tree
has a synthesis map and a coordinate map.  If synthesis followed by coordinates
and coordinates followed by synthesis are inverse up to the supplied semantic
relations, then every basis change is `coords B ∘ synth A`.  Composition of
basis changes collapses by one round trip, so the long and short pentagon routes
are pointwise `Q'`-equivalent.  No factorial identity and no scalar-collapse
assumption is used.

The theorem is the structural target for the all-label transvectant route: its
remaining physical work is to prove that every admissible fusion-tree family
is a constructive coordinate basis of the common four-form intertwiner space.

Mathlib-free; no classical choice, native decision procedure, proof hole, or
new axiom.
-/

import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.PentagonFromCoordinateBases

open YMGap.Constructive

/-- A constructive family of coordinate bases for one semantic space `V`.

The channel type may depend on the tree.  Equality in `V` is an explicit
constructive relation, while coefficient equality is `Q'.eqv`.  The two
round-trip laws are exactly the basis existence and uniqueness obligations. -/
structure CoordinateBases (Tree V : Type) where
  /-- Admissible channel coordinates for each fusion tree. -/
  Index : Tree → Type
  /-- Semantic equality in the common intertwiner space. -/
  Rel : V → V → Prop
  rel_refl : ∀ v, Rel v v
  rel_symm : ∀ {v w}, Rel v w → Rel w v
  rel_trans : ∀ {u v w}, Rel u v → Rel v w → Rel u w
  /-- Synthesize a semantic vector from tree coordinates. -/
  synth : ∀ T, (Index T → Q') → V
  /-- Read the coordinates of a semantic vector in a tree basis. -/
  coords : ∀ T, V → Index T → Q'
  /-- Coordinates respect semantic equality. -/
  coords_congr : ∀ T {v w}, Rel v w → ∀ i, (coords T v i).eqv (coords T w i)
  /-- Semantic reconstruction from coordinates. -/
  synth_coords : ∀ T v, Rel (synth T (coords T v)) v
  /-- Coordinate uniqueness after synthesis. -/
  coords_synth : ∀ T c i, (coords T (synth T c) i).eqv (c i)

variable {Tree V : Type}

/-- Pointwise semantic equality of two coordinate vectors in the same tree. -/
def CoordEqv (B : CoordinateBases Tree V) (T : Tree)
    (c d : B.Index T → Q') : Prop :=
  ∀ i, (c i).eqv (d i)

/-- Change coordinates from tree `A` to tree `B` through the common semantic
space. -/
def basisChange (B : CoordinateBases Tree V) (A C : Tree)
    (c : B.Index A → Q') : B.Index C → Q' :=
  B.coords C (B.synth A c)

/-- A basis change from a tree to itself is the identity, pointwise up to the
project's rational equivalence. -/
theorem basisChange_refl (B : CoordinateBases Tree V) (A : Tree)
    (c : B.Index A → Q') :
    CoordEqv B A (basisChange B A A c) c :=
  B.coords_synth A c

/-- **Composition of full basis changes.**  Passing through any intermediate
tree gives the same coordinates as changing directly.  This is the correct
matrix-valued replacement for a scalar recoupling composition law. -/
theorem basisChange_comp (B : CoordinateBases Tree V) (A M C : Tree)
    (c : B.Index A → Q') :
    CoordEqv B C
      (basisChange B M C (basisChange B A M c))
      (basisChange B A C c) := by
  intro i
  exact B.coords_congr C (B.synth_coords M (B.synth A c)) i

/-- **THE FULL PENTAGON FROM COORDINATE BASES.**  For five bracketings, the
three-edge and two-edge routes agree on every input vector and every output
channel.  Channel types may vary from vertex to vertex, so this covers genuine
rectangular intermediate transforms as well as square F-matrices. -/
theorem pentagon_from_coordinate_bases
    (B : CoordinateBases Tree V) (P0 P1 P2 P3 P4 : Tree)
    (c : B.Index P0 → Q') :
    CoordEqv B P3
      (basisChange B P2 P3
        (basisChange B P1 P2 (basisChange B P0 P1 c)))
      (basisChange B P4 P3 (basisChange B P0 P4 c)) := by
  intro i
  have h12 := basisChange_comp B P1 P2 P3 (basisChange B P0 P1 c) i
  have h01 := basisChange_comp B P0 P1 P3 c i
  have hlong :
      (basisChange B P2 P3
        (basisChange B P1 P2 (basisChange B P0 P1 c)) i).eqv
      (basisChange B P0 P3 c i) :=
    Q'.eqv_trans _ _ _ h12 h01
  have hshort := basisChange_comp B P0 P4 P3 c i
  exact Q'.eqv_trans _ _ _ hlong (Q'.eqv_symm hshort)

/-! ## A genuinely two-channel witness

The abstract carrier is not restricted to scalar channels.  Two coordinate
systems below differ by a swap of two channels; the resulting basis change is
nontrivial, and the full pentagon theorem still applies. -/

inductive SwapTree where
  | straight
  | swapped
deriving DecidableEq

inductive SwapChannel where
  | first
  | second
deriving DecidableEq

def swapVector (c : SwapChannel → Q') : SwapChannel → Q'
  | .first => c .second
  | .second => c .first

def swapByTree : SwapTree → (SwapChannel → Q') → SwapChannel → Q'
  | .straight, c => c
  | .swapped, c => swapVector c

/-- A non-scalar two-channel coordinate family.  The common semantic space is
the pair of rational coefficients; the second tree uses the swapped basis. -/
def twoChannelBases : CoordinateBases SwapTree (SwapChannel → Q') where
  Index := fun _ => SwapChannel
  Rel := fun v w => ∀ i, (v i).eqv (w i)
  rel_refl := fun v i => Q'.eqv_refl (v i)
  rel_symm := fun h i => Q'.eqv_symm (h i)
  rel_trans := fun h₁ h₂ i => Q'.eqv_trans _ _ _ (h₁ i) (h₂ i)
  synth := swapByTree
  coords := swapByTree
  coords_congr := by
    intro T v w h i
    cases T <;> cases i
    · exact h .first
    · exact h .second
    · exact h .second
    · exact h .first
  synth_coords := by
    intro T v i
    cases T <;> cases i <;> exact Q'.eqv_refl _
  coords_synth := by
    intro T c i
    cases T <;> cases i <;> exact Q'.eqv_refl _

def witnessCoords : SwapChannel → Q'
  | .first => 1
  | .second => 2

/-- The witness basis change really mixes channel placement: its first output
coordinate is the source's second coordinate, namely `2`. -/
theorem twoChannel_change_is_nontrivial :
    (basisChange twoChannelBases .straight .swapped witnessCoords .first).eqv 2 := by
  decide

/-- The multi-channel pentagon fires on the two-channel witness. -/
theorem twoChannel_pentagon
    (P0 P1 P2 P3 P4 : SwapTree) :
    CoordEqv twoChannelBases P3
      (basisChange twoChannelBases P2 P3
        (basisChange twoChannelBases P1 P2
          (basisChange twoChannelBases P0 P1 witnessCoords)))
      (basisChange twoChannelBases P4 P3
        (basisChange twoChannelBases P0 P4 witnessCoords)) :=
  pentagon_from_coordinate_bases twoChannelBases P0 P1 P2 P3 P4 witnessCoords

end YMGap.Continuum.PentagonFromCoordinateBases

#print axioms YMGap.Continuum.PentagonFromCoordinateBases.basisChange_refl
#print axioms YMGap.Continuum.PentagonFromCoordinateBases.basisChange_comp
#print axioms YMGap.Continuum.PentagonFromCoordinateBases.pentagon_from_coordinate_bases
#print axioms YMGap.Continuum.PentagonFromCoordinateBases.twoChannelBases
#print axioms YMGap.Continuum.PentagonFromCoordinateBases.twoChannel_change_is_nontrivial
#print axioms YMGap.Continuum.PentagonFromCoordinateBases.twoChannel_pentagon
