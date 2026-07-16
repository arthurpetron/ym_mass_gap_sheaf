/-
# Uniform pinned bounds for the canonical cutoff-one Z4 polymer gas

The canonical polymer gas is a finite list of numerical face supports.  This
module turns the geometric-animal representation into the cardinality bound
actually needed by Kotecký--Preiss: at a fixed numerical face and fixed size,
the canonical polymers inject into the unconditional degree-625 DFS animal
enumeration.  It then combines that count with the exact anchor activity
envelope and sums the resulting geometric majorant uniformly in the box,
the pinned face, and the truncation length.
-/

import YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
import YMGap.Continuum.PinnedCluster

namespace YMGap.Continuum.Z4CanonicalPinnedPolymerBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The finite list of canonical polymers pinned at a face and size -/

def canonicalPinnedSizePolymers (n rootId size : Nat) : List (List Nat) :=
  (canonicalSurfacePolymers n).filter
    (fun polymer => decide (rootId ∈ polymer ∧ polymer.length = size))

theorem mem_canonicalPinnedSizePolymers_iff
    {n rootId size : Nat} {polymer : List Nat} :
    polymer ∈ canonicalPinnedSizePolymers n rootId size ↔
      polymer ∈ canonicalSurfacePolymers n ∧
        rootId ∈ polymer ∧ polymer.length = size := by
  unfold canonicalPinnedSizePolymers
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem canonicalPinnedSizePolymers_nodup (n rootId size : Nat) :
    (canonicalPinnedSizePolymers n rootId size).Nodup := by
  unfold canonicalPinnedSizePolymers
  exact List.filter_sublist.nodup (canonicalSurfacePolymers_nodup n)

/-! ## 2. A constructive finite-cardinality injection lemma -/

/-- If every member of a duplicate-free source list is represented in a
target list, and no target value represents two source members, then the
source has at most the target's length.  The proof removes one concrete target
occurrence at each induction step; it uses neither choice nor a finite-set
cardinality library. -/
theorem length_le_of_unique_representation {A B : Type}
    (rel : A → B → Prop) :
    ∀ (source : List A) (target : List B),
      source.Nodup →
      (∀ x, x ∈ source → ∃ y, y ∈ target ∧ rel x y) →
      (∀ x, x ∈ source → ∀ y, y ∈ source → ∀ z,
        rel x z → rel y z → x = y) →
      source.length ≤ target.length
  | [], target, _, _, _ => Nat.zero_le _
  | head :: tail, target, hnodup, hrepresented, hunique => by
      have hheadMem : head ∈ head :: tail := List.mem_cons_self
      obtain ⟨representative, hrepresentative, hheadRel⟩ :=
        hrepresented head hheadMem
      obtain ⟨before, after, hsplit⟩ :=
        List.append_of_mem hrepresentative
      subst target
      have hparts := List.nodup_cons.mp hnodup
      have htailRepresented :
          ∀ x, x ∈ tail →
            ∃ y, y ∈ before ++ after ∧ rel x y := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ :=
          hrepresented x (List.mem_cons_of_mem head hx)
        have hyne : y ≠ representative := by
          intro heq
          subst y
          have hxeq : x = head :=
            hunique x (List.mem_cons_of_mem head hx)
              head hheadMem representative hxy hheadRel
          subst x
          exact hparts.1 hx
        rcases List.mem_append.mp hy with hyBefore | hyRest
        · exact ⟨y, List.mem_append_left after hyBefore, hxy⟩
        · have hyAfter : y ∈ after :=
            (List.mem_cons.mp hyRest).resolve_left hyne
          exact ⟨y, List.mem_append_right before hyAfter, hxy⟩
      have htailUnique :
          ∀ x, x ∈ tail → ∀ y, y ∈ tail → ∀ z,
            rel x z → rel y z → x = y := by
        intro x hx y hy z hxz hyz
        exact hunique x (List.mem_cons_of_mem head hx)
          y (List.mem_cons_of_mem head hy) z hxz hyz
      have ih : tail.length ≤ (before ++ after).length :=
        length_le_of_unique_representation rel tail (before ++ after)
          hparts.2 htailRepresented htailUnique
      rw [List.length_append] at ih
      simp only [List.length_cons, List.length_append]
      omega

/-! ## 3. Canonical pinned polymers inject into the Z4 DFS enumeration -/

theorem canonicalPinnedSize_length_le_enum
    (n rootId size : Nat) :
    (canonicalPinnedSizePolymers n rootId size).length ≤
      (enumPolys z4Chain (boxPlaquetteAt n rootId) size).length := by
  apply length_le_of_unique_representation
    (fun polymer animal => sameSupport (geometricPolymer n polymer) animal)
    (canonicalPinnedSizePolymers n rootId size)
    (enumPolys z4Chain (boxPlaquetteAt n rootId) size)
    (canonicalPinnedSizePolymers_nodup n rootId size)
  · intro polymer hpolymer
    have hfacts := mem_canonicalPinnedSizePolymers_iff.mp hpolymer
    obtain ⟨animal, hanimal, hsupport⟩ :=
      canonicalSurfacePolymer_overcountedAt hfacts.1 hfacts.2.1
    rw [hfacts.2.2] at hanimal
    exact ⟨animal, hanimal, hsupport⟩
  · intro left hleft right hright animal hleftSupport hrightSupport
    have hleftAmbient :=
      (mem_canonicalPinnedSizePolymers_iff.mp hleft).1
    have hrightAmbient :=
      (mem_canonicalPinnedSizePolymers_iff.mp hright).1
    apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
      hleftAmbient hrightAmbient
    exact sameSupport_trans hleftSupport (sameSupport_symm hrightSupport)

theorem canonicalPinnedSize_count_le_animalCount
    (n rootId size : Nat) :
    Q'.ofNat (canonicalPinnedSizePolymers n rootId size).length ≤
      (z4ClusterCountBound (boxPlaquetteAt n rootId)).animalCount size := by
  change Q'.ofNat (canonicalPinnedSizePolymers n rootId size).length ≤
    Q'.ofNat (enumPolys z4Chain (boxPlaquetteAt n rootId) size).length
  exact Q'.ofNat_le_ofNat
    (canonicalPinnedSize_length_le_enum n rootId size)

/-! ## 4. Exact activity sums at fixed pinned size -/

def canonicalPinnedSizeActivitySum (n rootId size : Nat) : Q' :=
  listQSum (canonicalSurfaceActivity anchorCoupling n)
    (canonicalPinnedSizePolymers n rootId size)

theorem listQSum_nonnegative {A : Type} (f : A → Q')
    (hf : ∀ x, (0 : Q') ≤ f x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum f xs
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hf head) (listQSum_nonnegative f hf tail)

/-- A finite list sum of terms bounded by `bound` is at most its length
times `bound`.  This is the list-indexed counterpart of the repository's
finite-sequence count bound. -/
theorem listQSum_le_length_mul {A : Type} (f : A → Q')
    {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → f x ≤ bound) →
      listQSum f xs ≤ Q'.ofNat xs.length * bound
  | [], _ => by
      show (0 : Q') ≤ Q'.ofNat 0 * bound
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead : f head ≤ bound := hbound head List.mem_cons_self
      have htailMembers : ∀ x, x ∈ tail → f x ≤ bound :=
        fun x hx => hbound x (List.mem_cons_of_mem head hx)
      have htail : listQSum f tail ≤ Q'.ofNat tail.length * bound :=
        listQSum_le_length_mul f hbound0 tail htailMembers
      have hsum : f head + listQSum f tail ≤
          bound + Q'.ofNat tail.length * bound :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ (listQSum f tail) hhead)
          (Q'.add_le_add_left bound _ _ htail)
      have htarget :
          (Q'.ofNat (tail.length + 1) * bound).eqv
            (bound + Q'.ofNat tail.length * bound) := by
        have hstep :
            (Q'.ofNat (tail.length + 1) * bound).eqv
              ((Q'.ofNat tail.length + (1 : Q')) * bound) :=
          Q'.mul_eqv_congr_right _ _ bound
            (Q'.ofNat_add_eqv tail.length 1)
        refine Q'.eqv_trans _ _ _ hstep ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_mul_eqv (Q'.ofNat tail.length) (1 : Q') bound) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (Q'.ofNat tail.length * bound)
            ((1 : Q') * bound) bound (Q'.one_mul_eqv bound)) ?_
        exact Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound
      exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv htarget)

theorem canonicalPinnedSizeActivitySum_nonnegative
    (n rootId size : Nat) :
    (0 : Q') ≤ canonicalPinnedSizeActivitySum n rootId size := by
  unfold canonicalPinnedSizeActivitySum
  exact listQSum_nonnegative _
    (canonicalSurfacePolymer_activity_nonnegative n)
    (canonicalPinnedSizePolymers n rootId size)

theorem canonicalPinnedSizeActivitySum_le_lengthEnvelope
    (n rootId size : Nat) :
    canonicalPinnedSizeActivitySum n rootId size ≤
      Q'.ofNat (canonicalPinnedSizePolymers n rootId size).length *
        anchorPerFaceEnvelope ^ size := by
  unfold canonicalPinnedSizeActivitySum
  apply listQSum_le_length_mul
    (canonicalSurfaceActivity anchorCoupling n)
    (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size)
  intro polymer hpolymer
  have hfacts := mem_canonicalPinnedSizePolymers_iff.mp hpolymer
  have hactivity := canonicalSurfacePolymer_activity_le hfacts.1
  rw [hfacts.2.2] at hactivity
  exact hactivity

theorem canonicalPinnedSizeActivitySum_le_animalEnvelope
    (n rootId size : Nat) :
    canonicalPinnedSizeActivitySum n rootId size ≤
      (z4ClusterCountBound (boxPlaquetteAt n rootId)).animalCount size *
        anchorPerFaceEnvelope ^ size := by
  exact Q'.le_trans' _ _ _
    (canonicalPinnedSizeActivitySum_le_lengthEnvelope n rootId size)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalPinnedSize_count_le_animalCount n rootId size)
      (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size))

/-! ## 5. The genuine uniform KP majorant and its geometric tail -/

def canonicalPinnedSizeWeightedActivity (n rootId size : Nat) : Q' :=
  canonicalPinnedSizeActivitySum n rootId size * eSurrogate ^ size

theorem canonicalPinnedSizeWeightedActivity_nonnegative
    (n rootId size : Nat) :
    (0 : Q') ≤ canonicalPinnedSizeWeightedActivity n rootId size := by
  unfold canonicalPinnedSizeWeightedActivity
  exact Q'.mul_nonneg _ _
    (canonicalPinnedSizeActivitySum_nonnegative n rootId size)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

theorem canonicalPinnedSizeWeightedActivity_le_geom
    (n rootId size : Nat) :
    canonicalPinnedSizeWeightedActivity n rootId size ≤
      anchorEffectiveRatio ^ size := by
  unfold canonicalPinnedSizeWeightedActivity anchorEffectiveRatio
  have henvelopePow0 : (0 : Q') ≤ anchorPerFaceEnvelope ^ size :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size
  have hePow0 : (0 : Q') ≤ eSurrogate ^ size :=
    Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
  have hactivity :
      canonicalPinnedSizeActivitySum n rootId size * eSurrogate ^ size ≤
        ((z4ClusterCountBound (boxPlaquetteAt n rootId)).animalCount size *
            anchorPerFaceEnvelope ^ size) * eSurrogate ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalPinnedSizeActivitySum_le_animalEnvelope n rootId size)
      hePow0
  have hcount :
      (z4ClusterCountBound (boxPlaquetteAt n rootId)).animalCount size *
            anchorPerFaceEnvelope ^ size ≤
        animalK z4Chain ^ size * anchorPerFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      ((z4ClusterCountBound (boxPlaquetteAt n rootId)).count_le size)
      henvelopePow0
  have hscaled :
      ((z4ClusterCountBound (boxPlaquetteAt n rootId)).animalCount size *
            anchorPerFaceEnvelope ^ size) * eSurrogate ^ size ≤
        (animalK z4Chain ^ size * anchorPerFaceEnvelope ^ size) *
          eSurrogate ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcount hePow0
  have hpow :
      ((animalK z4Chain * anchorPerFaceEnvelope * eSurrogate) ^ size).eqv
        (animalK z4Chain ^ size * anchorPerFaceEnvelope ^ size *
          eSurrogate ^ size) :=
    pow_mul3_eqv (animalK z4Chain) anchorPerFaceEnvelope eSurrogate size
  exact Q'.le_trans' _ _ _ hactivity
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hpow))

def canonicalPinnedTruncatedKPSum (n rootId : Nat) (N : Nat) : Q' :=
  finSum (fun size => canonicalPinnedSizeWeightedActivity n rootId size) N

theorem anchorEffectiveRatio_nonnegative :
    (0 : Q') ≤ anchorEffectiveRatio := by
  unfold anchorEffectiveRatio
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (animalK_nonneg z4Chain) (by decide))
    eSurrogate_nonneg

/-- The actual canonical finite-box polymer activities satisfy a uniform
pinned KP bound.  The constant is independent of the box size, pinned face,
and size truncation. -/
theorem canonicalPinnedTruncatedKPSum_le_two
    (n rootId N : Nat) :
    canonicalPinnedTruncatedKPSum n rootId N ≤ Q'.ofNat 2 := by
  unfold canonicalPinnedTruncatedKPSum
  exact Q'.le_trans' _ _ _
    (YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (canonicalPinnedSizeWeightedActivity_le_geom n rootId) N)
    (geom_partial_le_two anchorEffectiveRatio_nonnegative
      anchorEffectiveRatio_le_half N)

def canonicalPinnedShiftedKPSum
    (n rootId sizeFloor depth : Nat) : Q' :=
  finSum (fun offset =>
    canonicalPinnedSizeWeightedActivity n rootId (sizeFloor + offset)) depth

/-- The same actual polymer sum has a geometrically decaying size tail,
uniformly in the finite box and the pinned face. -/
theorem canonicalPinnedShiftedKPSum_le_tail
    (n rootId sizeFloor depth : Nat) :
    canonicalPinnedShiftedKPSum n rootId sizeFloor depth ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ sizeFloor := by
  unfold canonicalPinnedShiftedKPSum
  have hsum1 :
      finSum (fun offset =>
          canonicalPinnedSizeWeightedActivity n rootId (sizeFloor + offset)) depth ≤
        finSum (fun offset =>
          anchorEffectiveRatio ^ (sizeFloor + offset)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        canonicalPinnedSizeWeightedActivity_le_geom
          n rootId (sizeFloor + offset)) depth
  have hsum2 :
      (finSum (fun offset =>
          anchorEffectiveRatio ^ (sizeFloor + offset)) depth).eqv
        (finSum (fun offset =>
          anchorEffectiveRatio ^ sizeFloor *
            anchorEffectiveRatio ^ offset) depth) :=
    RationalTail.finSum_eqv_congr _ _
      (fun offset =>
        Q'.pow_add_eqv anchorEffectiveRatio sizeFloor offset) depth
  have hsum3 :
      (finSum (fun offset =>
          anchorEffectiveRatio ^ sizeFloor *
            anchorEffectiveRatio ^ offset) depth).eqv
        (anchorEffectiveRatio ^ sizeFloor *
          finSum (fun offset => anchorEffectiveRatio ^ offset) depth) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun offset => anchorEffectiveRatio ^ offset)
      (anchorEffectiveRatio ^ sizeFloor) depth)
  have hgeo :
      finSum (fun offset => anchorEffectiveRatio ^ offset) depth ≤
        Q'.ofNat 2 :=
    geom_partial_le_two anchorEffectiveRatio_nonnegative
      anchorEffectiveRatio_le_half depth
  have hscaled :
      anchorEffectiveRatio ^ sizeFloor *
          finSum (fun offset => anchorEffectiveRatio ^ offset) depth ≤
        anchorEffectiveRatio ^ sizeFloor * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative sizeFloor)
  have hcomm :
      (anchorEffectiveRatio ^ sizeFloor * Q'.ofNat 2).eqv
        (Q'.ofNat 2 * anchorEffectiveRatio ^ sizeFloor) :=
    Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _ hsum1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum2)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum3)
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcomm))))

end YMGap.Continuum.Z4CanonicalPinnedPolymerBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.length_le_of_unique_representation
#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.canonicalPinnedSize_length_le_enum
#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.canonicalPinnedSize_count_le_animalCount
#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.listQSum_le_length_mul
#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.canonicalPinnedSizeActivitySum_le_animalEnvelope
#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.canonicalPinnedSizeWeightedActivity_le_geom
#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.canonicalPinnedTruncatedKPSum_le_two
#print axioms YMGap.Continuum.Z4CanonicalPinnedPolymerBound.canonicalPinnedShiftedKPSum_le_tail
