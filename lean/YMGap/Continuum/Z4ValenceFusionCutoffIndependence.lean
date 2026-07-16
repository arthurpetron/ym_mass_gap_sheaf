/-
# Cutoff independence of the explicit local fusion multiplicities

The explicit valence formulas enumerate internal channels in finite ranges.
Their fusion constraints give sharper prefix bounds than the production
window `6*K`.  This file turns those support inequalities into exact
cardinality stability: enlarging the auxiliary cutoff contributes no new
admissible paths.
-/

import YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity

namespace YMGap.Continuum.Z4ValenceFusionCutoffIndependence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4LinkIdentifierFreshness

/-! ## 1. One-dimensional finite support -/

def filterRangeCount (cutoff : Nat) (allowed : Nat → Bool) : Nat :=
  ((List.range (cutoff + 1)).filter allowed).length

theorem filterRangeCount_zero
    (cutoff : Nat) (allowed : Nat → Bool)
    (hzero : ∀ x, allowed x = false) :
    filterRangeCount cutoff allowed = 0 := by
  unfold filterRangeCount
  induction List.range (cutoff + 1) with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filter_cons, hzero, Bool.false_eq_true, if_false]
      exact ih

theorem filterRangeCount_stable_add
    (bound : Nat) (allowed : Nat → Bool)
    (hsupport : ∀ x, allowed x = true → x ≤ bound) :
    ∀ extra,
      filterRangeCount (bound + extra) allowed =
        filterRangeCount bound allowed
  | 0 => by simp
  | extra + 1 => by
      have hnew : allowed (bound + extra + 1) = false := by
        cases h : allowed (bound + extra + 1) with
        | false => rfl
        | true =>
            have hle := hsupport _ h
            omega
      unfold filterRangeCount
      rw [show bound + (extra + 1) + 1 =
          (bound + extra + 1) + 1 by omega,
        List.range_succ, List.filter_append, List.length_append]
      simp only [List.filter_cons, List.filter_nil, hnew,
        Bool.false_eq_true, if_false, List.length_nil, Nat.add_zero]
      exact filterRangeCount_stable_add bound allowed hsupport extra

theorem filterRangeCount_stable_of_le
    {bound cutoff : Nat} (allowed : Nat → Bool)
    (hbound : bound ≤ cutoff)
    (hsupport : ∀ x, allowed x = true → x ≤ bound) :
    filterRangeCount cutoff allowed = filterRangeCount bound allowed := by
  have hdecomp : bound + (cutoff - bound) = cutoff := by omega
  rw [← hdecomp]
  exact filterRangeCount_stable_add bound allowed hsupport (cutoff - bound)

/-! ## 2. The one-channel path count -/

theorem oneChannelMultiplicity_cutoff_independent
    {K cutoff a b c d : Nat}
    (hcutoff : linkAuxiliaryCutoff K ≤ cutoff)
    (ha : a ≤ K) (hb : b ≤ K) :
    oneChannelMultiplicity cutoff a b c d =
      oneChannelMultiplicity (linkAuxiliaryCutoff K) a b c d := by
  unfold oneChannelMultiplicity
  apply filterRangeCount_stable_of_le
  · exact hcutoff
  · intro x hallowed
    exact oneChannel_support_within_linkCutoff ha hb hallowed

theorem oneValentMultiplicity_cutoff_independent
    {bound cutoff a : Nat} (hcutoff : bound ≤ cutoff) :
    oneValentMultiplicity cutoff a = oneValentMultiplicity bound a := by
  unfold oneValentMultiplicity
  apply filterRangeCount_stable_of_le
  · exact hcutoff
  · intro vacuum hallowed
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hallowed
    omega

theorem twoValentMultiplicity_cutoff_independent
    {bound cutoff a b : Nat} (hcutoff : bound ≤ cutoff) :
    twoValentMultiplicity cutoff a b = twoValentMultiplicity bound a b := by
  unfold twoValentMultiplicity
  apply filterRangeCount_stable_of_le
  · exact hcutoff
  · intro vacuum hallowed
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hallowed
    omega

/-! ## 3. Finite-sum bookkeeping for Cartesian path sets -/

def natListSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + natListSum xs

theorem natListSum_append : ∀ left right : List Nat,
    natListSum (left ++ right) = natListSum left + natListSum right
  | [], right => by simp [natListSum]
  | x :: xs, right => by
      simp only [List.cons_append, natListSum]
      rw [natListSum_append xs right]
      omega

theorem natListSum_map_congr {A : Type} (left right : A → Nat) :
    ∀ xs : List A, (∀ x, x ∈ xs → left x = right x) →
      natListSum (xs.map left) = natListSum (xs.map right)
  | [], _ => rfl
  | x :: xs, hagree => by
      simp only [List.map_cons, natListSum]
      rw [hagree x List.mem_cons_self,
        natListSum_map_congr left right xs
          (fun y hy => hagree y (List.mem_cons_of_mem x hy))]

theorem natListSum_range_stable_add
    (bound : Nat) (term : Nat → Nat)
    (hsupport : ∀ x, bound < x → term x = 0) :
    ∀ extra,
      natListSum ((List.range (bound + extra + 1)).map term) =
        natListSum ((List.range (bound + 1)).map term)
  | 0 => by simp
  | extra + 1 => by
      rw [show bound + (extra + 1) + 1 =
          (bound + extra + 1) + 1 by omega,
        List.range_succ, List.map_append, natListSum_append]
      simp only [List.map_singleton, natListSum, Nat.add_zero,
        hsupport (bound + extra + 1) (by omega), Nat.add_zero]
      exact natListSum_range_stable_add bound term hsupport extra

theorem natListSum_range_stable_of_le
    {bound cutoff : Nat} (term : Nat → Nat)
    (hbound : bound ≤ cutoff)
    (hsupport : ∀ x, bound < x → term x = 0) :
    natListSum ((List.range (cutoff + 1)).map term) =
      natListSum ((List.range (bound + 1)).map term) := by
  have hdecomp : bound + (cutoff - bound) = cutoff := by omega
  rw [← hdecomp]
  exact natListSum_range_stable_add bound term hsupport (cutoff - bound)

theorem filter_flatMap_length {A B : Type}
    (block : A → List B) (allowed : B → Bool) :
    ∀ xs : List A,
      ((xs.flatMap block).filter allowed).length =
        natListSum (xs.map fun x => ((block x).filter allowed).length)
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.map_cons, natListSum]
      rw [filter_flatMap_length block allowed xs]

theorem filter_map_length {A B : Type}
    (f : A → B) (allowed : B → Bool) : ∀ xs : List A,
    (((xs.map f).filter allowed).length) =
      ((xs.filter fun x => allowed (f x)).length)
  | [] => rfl
  | x :: xs => by
      cases h : allowed (f x) <;>
        simp [List.map_cons, h,
          filter_map_length f allowed xs]

/-! ## 4. Two-channel cutoff independence -/

def pairPathCount (outerCutoff innerCutoff : Nat)
    (allowed : Nat × Nat → Bool) : Nat :=
  natListSum ((List.range (outerCutoff + 1)).map fun x =>
    filterRangeCount innerCutoff (fun y => allowed (x, y)))

theorem twoChannelMultiplicity_eq_pairPathCount
    (cutoff a b c d e : Nat) :
    twoChannelMultiplicity cutoff a b c d e =
      pairPathCount cutoff cutoff (fun xy =>
        fusionOK a b xy.1 &&
          (fusionOK xy.1 c xy.2 && fusionOK xy.2 d e)) := by
  unfold twoChannelMultiplicity pairPathCount filterRangeCount
  rw [filter_flatMap_length]
  apply natListSum_map_congr
  intro x _
  exact filter_map_length (fun y => (x, y)) _ _

theorem pairPathCount_inner_stable
    {bound cutoff : Nat} (outerCutoff : Nat)
    (allowed : Nat × Nat → Bool) (hbound : bound ≤ cutoff)
    (hsupport : ∀ x y, allowed (x, y) = true → y ≤ bound) :
    pairPathCount outerCutoff cutoff allowed =
      pairPathCount outerCutoff bound allowed := by
  unfold pairPathCount
  apply natListSum_map_congr
  intro x _
  exact filterRangeCount_stable_of_le _ hbound
    (fun y hy => hsupport x y hy)

theorem pairPathCount_outer_stable
    {bound cutoff innerCutoff : Nat}
    (allowed : Nat × Nat → Bool) (hbound : bound ≤ cutoff)
    (hsupport : ∀ x y, allowed (x, y) = true → x ≤ bound) :
    pairPathCount cutoff innerCutoff allowed =
      pairPathCount bound innerCutoff allowed := by
  unfold pairPathCount
  apply natListSum_range_stable_of_le _ hbound
  intro x hx
  apply filterRangeCount_zero
  intro y
  cases h : allowed (x, y) with
  | false => rfl
  | true =>
      have hle := hsupport x y h
      omega

theorem twoChannelMultiplicity_cutoff_independent
    {K cutoff a b c d e : Nat}
    (hcutoff : linkAuxiliaryCutoff K ≤ cutoff)
    (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K) :
    twoChannelMultiplicity cutoff a b c d e =
      twoChannelMultiplicity (linkAuxiliaryCutoff K) a b c d e := by
  let allowed : Nat × Nat → Bool := fun xy =>
    fusionOK a b xy.1 &&
      (fusionOK xy.1 c xy.2 && fusionOK xy.2 d e)
  rw [twoChannelMultiplicity_eq_pairPathCount,
    twoChannelMultiplicity_eq_pairPathCount]
  refine Eq.trans
    (pairPathCount_inner_stable cutoff allowed hcutoff ?_) ?_
  · intro x y hxy
    exact (twoChannel_support_within_linkCutoff ha hb hc hxy).2
  · exact pairPathCount_outer_stable allowed hcutoff
      (fun x y hxy =>
        (twoChannel_support_within_linkCutoff ha hb hc hxy).1)

/-! ## 5. Three-channel cutoff independence -/

theorem pairEnumeration_filter_length
    (outerCutoff innerCutoff : Nat)
    (allowed : Nat × Nat → Bool) :
    (((List.range (outerCutoff + 1)).flatMap fun x =>
        (List.range (innerCutoff + 1)).map fun y => (x, y)).filter
      allowed).length = pairPathCount outerCutoff innerCutoff allowed := by
  unfold pairPathCount filterRangeCount
  rw [filter_flatMap_length]
  apply natListSum_map_congr
  intro x _
  exact filter_map_length (fun y => (x, y)) _ _

theorem pairEnumeration_mapped_filter_length {A : Type}
    (outerCutoff innerCutoff : Nat) (f : Nat × Nat → A)
    (allowed : A → Bool) :
    (((List.range (outerCutoff + 1)).flatMap fun x =>
        (List.range (innerCutoff + 1)).map fun y => f (x, y)).filter
      allowed).length = pairPathCount outerCutoff innerCutoff
        (fun xy => allowed (f xy)) := by
  unfold pairPathCount filterRangeCount
  rw [filter_flatMap_length]
  apply natListSum_map_congr
  intro x _
  exact filter_map_length (fun y => f (x, y)) allowed _

theorem pairPathCount_zero
    (outerCutoff innerCutoff : Nat) (allowed : Nat × Nat → Bool)
    (hzero : ∀ x y, allowed (x, y) = false) :
    pairPathCount outerCutoff innerCutoff allowed = 0 := by
  unfold pairPathCount
  induction List.range (outerCutoff + 1) with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, natListSum]
      rw [filterRangeCount_zero innerCutoff _ (hzero x), ih,
        Nat.zero_add]

def triplePathCount (outerCutoff middleCutoff innerCutoff : Nat)
    (allowed : Nat × Nat × Nat → Bool) : Nat :=
  natListSum ((List.range (outerCutoff + 1)).map fun x =>
    pairPathCount middleCutoff innerCutoff
      (fun yz => allowed (x, yz.1, yz.2)))

theorem threeChannelMultiplicity_eq_triplePathCount
    (cutoff a b c d e f : Nat) :
    threeChannelMultiplicity cutoff a b c d e f =
      triplePathCount cutoff cutoff cutoff (fun xyz =>
        fusionOK a b xyz.1 &&
          (fusionOK xyz.1 c xyz.2.1 &&
            (fusionOK xyz.2.1 d xyz.2.2 &&
              fusionOK xyz.2.2 e f))) := by
  unfold threeChannelMultiplicity triplePathCount
  rw [filter_flatMap_length]
  apply natListSum_map_congr
  intro x _
  exact pairEnumeration_mapped_filter_length cutoff cutoff
    (fun yz => (x, yz.1, yz.2))
    (fun xyz =>
      fusionOK a b xyz.1 &&
        (fusionOK xyz.1 c xyz.2.1 &&
          (fusionOK xyz.2.1 d xyz.2.2 && fusionOK xyz.2.2 e f)))

theorem triplePathCount_inner_stable
    {bound cutoff : Nat} (outerCutoff middleCutoff : Nat)
    (allowed : Nat × Nat × Nat → Bool) (hbound : bound ≤ cutoff)
    (hsupport : ∀ x y z, allowed (x, y, z) = true → z ≤ bound) :
    triplePathCount outerCutoff middleCutoff cutoff allowed =
      triplePathCount outerCutoff middleCutoff bound allowed := by
  unfold triplePathCount
  apply natListSum_map_congr
  intro x _
  exact pairPathCount_inner_stable middleCutoff
    (fun yz => allowed (x, yz.1, yz.2)) hbound
    (fun y z hyz => hsupport x y z hyz)

theorem triplePathCount_middle_stable
    {bound cutoff : Nat} (outerCutoff innerCutoff : Nat)
    (allowed : Nat × Nat × Nat → Bool) (hbound : bound ≤ cutoff)
    (hsupport : ∀ x y z, allowed (x, y, z) = true → y ≤ bound) :
    triplePathCount outerCutoff cutoff innerCutoff allowed =
      triplePathCount outerCutoff bound innerCutoff allowed := by
  unfold triplePathCount
  apply natListSum_map_congr
  intro x _
  exact pairPathCount_outer_stable
    (fun yz => allowed (x, yz.1, yz.2)) hbound
    (fun y z hyz => hsupport x y z hyz)

theorem triplePathCount_outer_stable
    {bound cutoff middleCutoff innerCutoff : Nat}
    (allowed : Nat × Nat × Nat → Bool) (hbound : bound ≤ cutoff)
    (hsupport : ∀ x y z, allowed (x, y, z) = true → x ≤ bound) :
    triplePathCount cutoff middleCutoff innerCutoff allowed =
      triplePathCount bound middleCutoff innerCutoff allowed := by
  unfold triplePathCount
  apply natListSum_range_stable_of_le _ hbound
  intro x hx
  apply pairPathCount_zero
  intro y z
  cases h : allowed (x, y, z) with
  | false => rfl
  | true =>
      have hle := hsupport x y z h
      omega

theorem threeChannelMultiplicity_cutoff_independent
    {K cutoff a b c d e f : Nat}
    (hcutoff : linkAuxiliaryCutoff K ≤ cutoff)
    (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K) (hd : d ≤ K) :
    threeChannelMultiplicity cutoff a b c d e f =
      threeChannelMultiplicity (linkAuxiliaryCutoff K) a b c d e f := by
  let allowed : Nat × Nat × Nat → Bool := fun xyz =>
    fusionOK a b xyz.1 &&
      (fusionOK xyz.1 c xyz.2.1 &&
        (fusionOK xyz.2.1 d xyz.2.2 && fusionOK xyz.2.2 e f))
  rw [threeChannelMultiplicity_eq_triplePathCount,
    threeChannelMultiplicity_eq_triplePathCount]
  refine Eq.trans
    (triplePathCount_inner_stable cutoff cutoff allowed hcutoff ?_)
    (Eq.trans
      (triplePathCount_middle_stable cutoff
        (linkAuxiliaryCutoff K) allowed hcutoff ?_)
      (triplePathCount_outer_stable allowed hcutoff ?_))
  · intro x y z hxyz
    exact (threeChannel_support_within_linkCutoff ha hb hc hd hxyz).2.2
  · intro x y z hxyz
    exact (threeChannel_support_within_linkCutoff ha hb hc hd hxyz).2.1
  · intro x y z hxyz
    exact (threeChannel_support_within_linkCutoff ha hb hc hd hxyz).1

/-! ## 6. Uniform valence and actual-box corollaries -/

def ExternalSpinsBounded (K degree : Nat)
    (external : EdgeLabelling) : Prop :=
  ∀ position, position < degree → external position ≤ K

theorem explicitValenceMultiplicity_cutoff_independent
    {K cutoff degree : Nat} (external : EdgeLabelling)
    (hcutoff : linkAuxiliaryCutoff K ≤ cutoff)
    (hdegree : degree ≤ linkIncidenceBound)
    (hexternal : ExternalSpinsBounded K degree external) :
    explicitValenceMultiplicity cutoff degree external =
      explicitValenceMultiplicity (linkAuxiliaryCutoff K) degree external := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact oneValentMultiplicity_cutoff_independent hcutoff
  · exact twoValentMultiplicity_cutoff_independent hcutoff
  · rfl
  · apply oneChannelMultiplicity_cutoff_independent hcutoff
    · exact hexternal 0 (by omega)
    · exact hexternal 1 (by omega)
  · apply twoChannelMultiplicity_cutoff_independent hcutoff
    · exact hexternal 0 (by omega)
    · exact hexternal 1 (by omega)
    · exact hexternal 2 (by omega)
  · apply threeChannelMultiplicity_cutoff_independent hcutoff
    · exact hexternal 0 (by omega)
    · exact hexternal 1 (by omega)
    · exact hexternal 2 (by omega)
    · exact hexternal 3 (by omega)

/-- A physical labelling drawn from the cutoff-`K` box Cartesian product
induces external spins bounded by `K` on every canonical position of every
link resolver. -/
theorem actualExternalSpinsBounded
    {K n i : Nat} {ell :
      YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    ExternalSpinsBounded K (incidentPlaqIds n ell).length
      (fun position => physical
        (localIdentifierRename (incidentPlaqIds n ell)
          (linkBlockBase n i) position)) := by
  let labels := incidentPlaqIds n ell
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  intro position hposition
  have hpositionMem : position ∈ List.range labels.length :=
    List.mem_range.mpr hposition
  have hmapped : rename position ∈ labels := by
    rw [← map_localIdentifierRename_range labels base]
    exact List.mem_map.mpr ⟨position, hpositionMem, rfl⟩
  have hmappedRange : rename position ∈
      List.range (plaquetteEdgeCount n) :=
    List.mem_range.mpr (incidentPlaqId_lt_count hmapped)
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) physical hphysical
  have hlt := hsound.1 (rename position) hmappedRange
  change physical (rename position) ≤ K
  omega

/-- **Exact local cutoff independence for an actual box link.**  Once the
external plaquette labelling is cutoff-`K`, every larger auxiliary Cartesian
window has exactly the same fixed-external invariant multiplicity as the
production `6*K` window. -/
theorem enlargedCanonicalMultiplicity_eq_actualCount
    {K cutoff n i : Nat} {ell :
      YMGap.Continuum.ClusterCount4DProgress.Z4Link}
    {physical : EdgeLabelling}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (hcutoff : linkAuxiliaryCutoff K ≤ cutoff)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    canonicalLinkInvariantMultiplicityCount cutoff
        (incidentPlaqIds n ell).length
        (fun position => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) position)) =
      linkInvariantMultiplicityCount K n physical (i, ell) := by
  let external : EdgeLabelling := fun position => physical
    (localIdentifierRename (incidentPlaqIds n ell)
      (linkBlockBase n i) position)
  have hdegree := incidentPlaqIds_length_le_six n ell
  rw [canonicalMultiplicity_eq_explicit external hdegree]
  rw [explicitValenceMultiplicity_cutoff_independent external
    hcutoff hdegree (actualExternalSpinsBounded hphysical)]
  rw [← canonicalMultiplicity_eq_explicit external hdegree]
  exact (linkInvariantMultiplicityCount_eq_canonical
    hindexed physical).symm

end YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ValenceFusionCutoffIndependence.filterRangeCount_stable_of_le
#print axioms YMGap.Continuum.Z4ValenceFusionCutoffIndependence.oneChannelMultiplicity_cutoff_independent
#print axioms YMGap.Continuum.Z4ValenceFusionCutoffIndependence.twoChannelMultiplicity_cutoff_independent
#print axioms YMGap.Continuum.Z4ValenceFusionCutoffIndependence.threeChannelMultiplicity_cutoff_independent
#print axioms YMGap.Continuum.Z4ValenceFusionCutoffIndependence.explicitValenceMultiplicity_cutoff_independent
#print axioms YMGap.Continuum.Z4ValenceFusionCutoffIndependence.actualExternalSpinsBounded
#print axioms YMGap.Continuum.Z4ValenceFusionCutoffIndependence.enlargedCanonicalMultiplicity_eq_actualCount
