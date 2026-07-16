/-
# Spatial boundary tails for the canonical cutoff-one Z4 polymer gas

The pinned KP theorem controls polymers by their number of plaquettes.  A
thermodynamic-limit estimate needs spatial control: a polymer which reaches a
remote box shell must be large.  This module proves that bridge for the actual
canonical polymers using the non-collapsing per-coordinate L-infinity metric.
It then restricts the exact pinned activity sum to polymers reaching distance
`d` and obtains the uniform geometric boundary tail.
-/

import YMGap.Continuum.Z4CanonicalPinnedPolymerBound
import YMGap.Continuum.DecoderReachFloor
import YMGap.Continuum.SepLatticeZ4Linf
import YMGap.Constructive.CornerBound

namespace YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecoderReachFloor
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

/-! ## 1. Decoder supports are duplicate-free -/

theorem step_visited_nodup (BL : BddLattice) (s : DState BL)
    (c : Fin (BL.D + 1)) (h : s.visited.Nodup) :
    (step BL s c).visited.Nodup := by
  unfold step
  split
  · split
    · exact h
    · split
      · exact h
      · exact List.nodup_cons.mpr ⟨by assumption, h⟩
  · split <;> exact h

theorem foldl_step_visited_nodup (BL : BddLattice) :
    ∀ (code : List (Fin (BL.D + 1))) (s : DState BL),
      s.visited.Nodup →
        (code.foldl (step BL) s).visited.Nodup
  | [], _, h => h
  | c :: rest, s, h => by
      simp only [List.foldl_cons]
      exact foldl_step_visited_nodup BL rest (step BL s c)
        (step_visited_nodup BL s c h)

theorem decode_nodup (BL : BddLattice)
    (p : BL.toLattice.Plaquette)
    (code : List (Fin (BL.D + 1))) :
    (decode BL p code).Nodup := by
  unfold decode
  apply foldl_step_visited_nodup
  exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem enumPoly_nodup (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (size : Nat)
    {polymer : Polymer BL.toLattice}
    (hpolymer : polymer ∈ enumPolys BL p size) : polymer.Nodup := by
  obtain ⟨code, _, rfl⟩ := List.mem_map.mp hpolymer
  exact decode_nodup BL p code

theorem sameSupport_length_eq_of_nodup
    {L : Lattice} [DecidableEq L.Plaquette]
    {left right : Polymer L}
    (hsupport : sameSupport left right)
    (hleft : left.Nodup) (hright : right.Nodup) :
    left.length = right.length := by
  exact (Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
    left right hleft hright
    (fun item => ⟨hsupport.1 item, hsupport.2 item⟩)).length_eq

/-! ## 2. Every decoded neighbour step moves L-infinity distance at most one -/

theorem edgePlaqs_comp_window (q : Z4Plaq) (u : Z4Vertex)
    (d m : Dir4) (h : q ∈ edgePlaqs u d) :
    vComp q.1 m ≤ vComp u m ∧
      vComp u m ≤ vComp q.1 m + 1 := by
  obtain ⟨a, b, c, e⟩ := u
  cases d <;> cases m <;>
    simp only [edgePlaqs, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [vComp, subE] <;> omega

theorem z4Nbrs_natDist_comp_le (p q : Z4Plaq)
    (h : q ∈ z4Nbrs p) (m : Dir4) :
    natDist (cPlaq p m) (cPlaq q m) ≤ 1 := by
  unfold z4Nbrs at h
  rcases List.mem_append.mp h with h' | h4
  · rcases List.mem_append.mp h' with h'' | h3
    · rcases List.mem_append.mp h'' with h1 | h2
      · have hw := edgePlaqs_comp_window q p.1 (dirsOf p.2).1 m h1
        simp only [natDist, cPlaq]
        omega
      · have hw := edgePlaqs_comp_window q p.1 (dirsOf p.2).2 m h2
        simp only [natDist, cPlaq]
        omega
    · have hw := edgePlaqs_comp_window q
          (addE p.1 (dirsOf p.2).2) (dirsOf p.2).1 m h3
      have ha := vComp_addE_cases p.1 (dirsOf p.2).2 m
      simp only [natDist, cPlaq]
      omega
  · have hw := edgePlaqs_comp_window q
        (addE p.1 (dirsOf p.2).1) (dirsOf p.2).2 m h4
    have ha := vComp_addE_cases p.1 (dirsOf p.2).1 m
    simp only [natDist, cPlaq]
    omega

theorem z4_nbrs_linfDist_le (p q : Z4Plaq)
    (h : q ∈ z4Nbrs p) : linfDist p q ≤ 1 := by
  exact linfDist_le p q 1
    (z4Nbrs_natDist_comp_le p q h x0)
    (z4Nbrs_natDist_comp_le p q h x1)
    (z4Nbrs_natDist_comp_le p q h x2)
    (z4Nbrs_natDist_comp_le p q h x3)

theorem z4_linf_decode_dist_floor
    (p : Z4Plaq) (code : List (Fin (z4Chain.D + 1))) :
    ∀ q, q ∈ decode z4Chain p code →
      linfDist p q + 1 ≤ (decode z4Chain p code).length :=
  decode_dist_floor z4Chain linfDist p
    (z4SepLinf.dist_self p)
    (fun a b c => z4SepLinf.dist_triangle a b c)
    z4_nbrs_linfDist_le code

theorem enum_linf_reach_floor (p : Z4Plaq) (size : Nat)
    (polymer : Polymer z4Chain.toLattice)
    (hpolymer : polymer ∈ enumPolys z4Chain p size)
    (q : Z4Plaq) (hq : q ∈ polymer)
    (distance : Nat) (hsep : distance ≤ linfDist p q) :
    distance + 1 ≤ polymer.length := by
  obtain ⟨code, _, rfl⟩ := List.mem_map.mp hpolymer
  exact Nat.le_trans (Nat.succ_le_succ hsep)
    (z4_linf_decode_dist_floor p code q hq)

/-! ## 3. Spatial size floor for the actual canonical polymers -/

theorem canonicalSurfacePolymer_linf_size_floor
    {n rootId distance : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hroot : rootId ∈ polymer)
    {q : Z4Plaq} (hq : q ∈ geometricPolymer n polymer)
    (hsep : distance ≤ linfDist (boxPlaquetteAt n rootId) q) :
    distance + 1 ≤ polymer.length := by
  obtain ⟨animal, hanimal, hsupport⟩ :=
    canonicalSurfacePolymer_overcountedAt hpolymer hroot
  have hqAnimal : q ∈ animal := hsupport.1 q hq
  have hfloor := enum_linf_reach_floor
    (boxPlaquetteAt n rootId) polymer.length animal hanimal
    q hqAnimal distance hsep
  have hgeomNodup : (geometricPolymer n polymer).Nodup :=
    geometricPolymer_nodup
      (canonicalSurfacePolymer_mem_faceSupports hpolymer)
  have hanimalNodup : animal.Nodup :=
    enumPoly_nodup z4Chain (boxPlaquetteAt n rootId)
      polymer.length hanimal
  have hlength : animal.length = polymer.length := by
    have hsameLength := sameSupport_length_eq_of_nodup
      hsupport hgeomNodup hanimalNodup
    simpa only [geometricPolymer, List.length_map] using hsameLength.symm
  rw [hlength] at hfloor
  exact hfloor

/-! ## 4. Corner-box shells imply genuine L-infinity separation -/

/-- A decidable geometric test that a plaquette base lies outside the
corner-anchored box of side `outer`. -/
def outsideBoxB (outer : Nat) (q : Z4Plaq) : Bool :=
  decide (outer ≤ cPlaq q x0 ∨ outer ≤ cPlaq q x1 ∨
    outer ≤ cPlaq q x2 ∨ outer ≤ cPlaq q x3)

theorem outsideBoxB_true_iff_not_mem
    (outer : Nat) (q : Z4Plaq) :
    outsideBoxB outer q = true ↔ q ∉ boxPlaquettes outer := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := q
  unfold outsideBoxB
  rw [decide_eq_true_eq, mem_boxPlaquettes]
  simp only [cPlaq, vComp]
  constructor
  · rintro (h0 | h1 | h2 | h3) hall
    · omega
    · omega
    · omega
    · omega
  · intro hout
    by_cases h0 : a < outer
    · by_cases h1 : b < outer
      · by_cases h2 : c < outer
        · by_cases h3 : d < outer
          · exfalso
            apply hout
            exact ⟨h0, h1, h2, h3⟩
          · exact Or.inr (Or.inr (Or.inr (Nat.le_of_not_gt h3)))
        · exact Or.inr (Or.inr (Or.inl (Nat.le_of_not_gt h2)))
      · exact Or.inr (Or.inl (Nat.le_of_not_gt h1))
    · exact Or.inl (Nat.le_of_not_gt h0)

/-- If the root is in an inner corner box and `q` lies outside the box
expanded by `distance`, then the plaquettes are separated by at least
`distance + 1` in the non-collapsing L-infinity metric. -/
theorem outside_expanded_box_linf_floor
    {root q : Z4Plaq} {inner distance : Nat}
    (hroot : root ∈ boxPlaquettes inner)
    (hout : outsideBoxB (inner + distance) q = true) :
    distance + 1 ≤ linfDist root q := by
  obtain ⟨⟨a, b, c, d⟩, rootPlane⟩ := root
  obtain ⟨⟨e, f, g, h⟩, qPlane⟩ := q
  have hr := (mem_boxPlaquettes
    (((a, b, c, d), rootPlane) : Z4Plaq) inner).1 hroot
  unfold outsideBoxB at hout
  simp only [cPlaq, vComp] at hout hr
  have houtside : inner + distance ≤ e ∨
      inner + distance ≤ f ∨
      inner + distance ≤ g ∨
      inner + distance ≤ h :=
    of_decide_eq_true hout
  rcases houtside with h0 | h1 | h2 | h3
  · have hmetric := le_linfDist_comp
      (((a, b, c, d), rootPlane) : Z4Plaq)
      (((e, f, g, h), qPlane) : Z4Plaq) x0
    simp only [natDist, cPlaq, vComp] at hmetric
    omega
  · have hmetric := le_linfDist_comp
      (((a, b, c, d), rootPlane) : Z4Plaq)
      (((e, f, g, h), qPlane) : Z4Plaq) x1
    simp only [natDist, cPlaq, vComp] at hmetric
    omega
  · have hmetric := le_linfDist_comp
      (((a, b, c, d), rootPlane) : Z4Plaq)
      (((e, f, g, h), qPlane) : Z4Plaq) x2
    simp only [natDist, cPlaq, vComp] at hmetric
    omega
  · have hmetric := le_linfDist_comp
      (((a, b, c, d), rootPlane) : Z4Plaq)
      (((e, f, g, h), qPlane) : Z4Plaq) x3
    simp only [natDist, cPlaq, vComp] at hmetric
    omega

theorem canonicalSurfacePolymer_outside_box_size_floor
    {n rootId inner distance : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hroot : rootId ∈ polymer)
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner)
    {q : Z4Plaq} (hq : q ∈ geometricPolymer n polymer)
    (hout : outsideBoxB (inner + distance) q = true) :
    distance + 2 ≤ polymer.length := by
  have hsep := outside_expanded_box_linf_floor hrootInner hout
  have hfloor := canonicalSurfacePolymer_linf_size_floor
    hpolymer hroot hq hsep
  omega

/-! ## 5. Canonical polymers which reach a remote L-infinity shell -/

/-- Boolean reach test on the actual geometric plaquette support of a
canonical numerical polymer. -/
def canonicalPolymerReachesB (n rootId distance : Nat)
    (polymer : List Nat) : Bool :=
  (geometricPolymer n polymer).any (fun q =>
    decide (distance ≤ linfDist (boxPlaquetteAt n rootId) q))

/-- Does the actual geometric support leave the corner box obtained by
expanding `inner` by `distance`? -/
def canonicalPolymerExitsExpandedBoxB
    (n inner distance : Nat) (polymer : List Nat) : Bool :=
  (geometricPolymer n polymer).any
    (outsideBoxB (inner + distance))

theorem canonicalPolymerExitsExpandedBoxB_implies_reaches
    {n rootId inner distance : Nat} {polymer : List Nat}
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner)
    (hexit : canonicalPolymerExitsExpandedBoxB
      n inner distance polymer = true) :
    canonicalPolymerReachesB n rootId (distance + 1) polymer = true := by
  unfold canonicalPolymerExitsExpandedBoxB at hexit
  obtain ⟨q, hq, hout⟩ := List.any_eq_true.mp hexit
  unfold canonicalPolymerReachesB
  exact List.any_eq_true.mpr ⟨q, hq,
    decide_eq_true (outside_expanded_box_linf_floor hrootInner hout)⟩

/-- The exact-size canonical polymers pinned at `rootId` whose geometric
support reaches L-infinity distance at least `distance`. -/
def canonicalPinnedReachSizePolymers
    (n rootId distance size : Nat) : List (List Nat) :=
  (canonicalPinnedSizePolymers n rootId size).filter
    (canonicalPolymerReachesB n rootId distance)

theorem mem_canonicalPinnedReachSizePolymers_iff
    {n rootId distance size : Nat} {polymer : List Nat} :
    polymer ∈ canonicalPinnedReachSizePolymers n rootId distance size ↔
      polymer ∈ canonicalSurfacePolymers n ∧
        rootId ∈ polymer ∧ polymer.length = size ∧
        ∃ q, q ∈ geometricPolymer n polymer ∧
          distance ≤ linfDist (boxPlaquetteAt n rootId) q := by
  unfold canonicalPinnedReachSizePolymers canonicalPolymerReachesB
  rw [List.mem_filter]
  constructor
  · intro h
    have hpinned := mem_canonicalPinnedSizePolymers_iff.mp h.1
    obtain ⟨q, hq, hsep⟩ := List.any_eq_true.mp h.2
    exact ⟨hpinned.1, hpinned.2.1, hpinned.2.2,
      q, hq, of_decide_eq_true hsep⟩
  · rintro ⟨hpolymer, hroot, hsize, q, hq, hsep⟩
    exact ⟨mem_canonicalPinnedSizePolymers_iff.mpr
        ⟨hpolymer, hroot, hsize⟩,
      List.any_eq_true.mpr ⟨q, hq, decide_eq_true hsep⟩⟩

/-- Low size grades of the spatially reaching list are definitionally empty:
reaching distance `distance` costs at least `distance + 1` plaquettes. -/
theorem canonicalPinnedReachSizePolymers_eq_nil_of_le
    (n rootId distance size : Nat) (hsize : size ≤ distance) :
    canonicalPinnedReachSizePolymers n rootId distance size = [] := by
  cases hreach : canonicalPinnedReachSizePolymers n rootId distance size with
  | nil => rfl
  | cons polymer tail =>
      exfalso
      have hmem : polymer ∈
          canonicalPinnedReachSizePolymers n rootId distance size := by
        rw [hreach]
        exact List.mem_cons_self
      obtain ⟨hpolymer, hroot, hlength, q, hq, hsep⟩ :=
        mem_canonicalPinnedReachSizePolymers_iff.mp hmem
      have hfloor := canonicalSurfacePolymer_linf_size_floor
        hpolymer hroot hq hsep
      rw [hlength] at hfloor
      omega

/-! ## 6. Exact rational activity sums and the boundary tail -/

/-- Removing terms from a list cannot increase a sum of nonnegative exact
rational weights. -/
theorem listQSum_filter_le {A : Type} (f : A → Q')
    (p : A → Bool) (hf : ∀ x, (0 : Q') ≤ f x) :
    ∀ xs : List A,
      listQSum f (xs.filter p) ≤ listQSum f xs
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le f p hf tail
      cases hp : p head with
      | false =>
          simp only [List.filter, hp, listQSum]
          have hhead : listQSum f tail ≤
              f head + listQSum f tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (f head) (listQSum f tail) (hf head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih
            hhead
      | true =>
          simp only [List.filter, hp, listQSum]
          exact Q'.add_le_add_left (f head) _ _ ih

/-- Pointwise implication between two Boolean filters gives domination of
their nonnegative weighted sums, retaining list occurrences exactly. -/
theorem listQSum_filter_le_filter {A : Type} (f : A → Q')
    (p q : A → Bool) (hf : ∀ x, (0 : Q') ≤ f x)
    (hpq : ∀ x, p x = true → q x = true) :
    ∀ xs : List A,
      listQSum f (xs.filter p) ≤ listQSum f (xs.filter q)
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_filter f p q hf hpq tail
      cases hp : p head with
      | false =>
          cases hq : q head with
          | false =>
              simpa only [List.filter, hp, hq, listQSum] using ih
          | true =>
              simp only [List.filter, hp, hq, listQSum]
              have hhead : listQSum f (tail.filter q) ≤
                  f head + listQSum f (tail.filter q) := by
                have hscaled := Q'.add_le_add_right
                  (0 : Q') (f head) (listQSum f (tail.filter q)) (hf head)
                rwa [Q'.zero_add'] at hscaled
              exact Q'.le_trans' _ _ _ ih hhead
      | true =>
          have hq : q head = true := hpq head hp
          simp only [List.filter, hp, hq, listQSum]
          exact Q'.add_le_add_left (f head) _ _ ih

def canonicalPinnedReachSizeActivitySum
    (n rootId distance size : Nat) : Q' :=
  listQSum (canonicalSurfaceActivity anchorCoupling n)
    (canonicalPinnedReachSizePolymers n rootId distance size)

theorem canonicalPinnedReachSizeActivitySum_nonnegative
    (n rootId distance size : Nat) :
    (0 : Q') ≤
      canonicalPinnedReachSizeActivitySum n rootId distance size := by
  unfold canonicalPinnedReachSizeActivitySum
  exact listQSum_nonnegative _
    (canonicalSurfacePolymer_activity_nonnegative n)
    (canonicalPinnedReachSizePolymers n rootId distance size)

theorem canonicalPinnedReachSizeActivitySum_le_pinned
    (n rootId distance size : Nat) :
    canonicalPinnedReachSizeActivitySum n rootId distance size ≤
      canonicalPinnedSizeActivitySum n rootId size := by
  unfold canonicalPinnedReachSizeActivitySum
    canonicalPinnedReachSizePolymers canonicalPinnedSizeActivitySum
  exact listQSum_filter_le _ _
    (canonicalSurfacePolymer_activity_nonnegative n)
    (canonicalPinnedSizePolymers n rootId size)

def canonicalPinnedReachSizeWeightedActivity
    (n rootId distance size : Nat) : Q' :=
  canonicalPinnedReachSizeActivitySum n rootId distance size *
    eSurrogate ^ size

theorem canonicalPinnedReachSizeWeightedActivity_nonnegative
    (n rootId distance size : Nat) :
    (0 : Q') ≤
      canonicalPinnedReachSizeWeightedActivity n rootId distance size := by
  unfold canonicalPinnedReachSizeWeightedActivity
  exact Q'.mul_nonneg _ _
    (canonicalPinnedReachSizeActivitySum_nonnegative
      n rootId distance size)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

theorem canonicalPinnedReachSizeWeightedActivity_le_pinned
    (n rootId distance size : Nat) :
    canonicalPinnedReachSizeWeightedActivity n rootId distance size ≤
      canonicalPinnedSizeWeightedActivity n rootId size := by
  unfold canonicalPinnedReachSizeWeightedActivity
    canonicalPinnedSizeWeightedActivity
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (canonicalPinnedReachSizeActivitySum_le_pinned
      n rootId distance size)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

theorem canonicalPinnedReachSizeWeightedActivity_eqv_zero_of_le
    (n rootId distance size : Nat) (hsize : size ≤ distance) :
    (canonicalPinnedReachSizeWeightedActivity
      n rootId distance size).eqv 0 := by
  unfold canonicalPinnedReachSizeWeightedActivity
    canonicalPinnedReachSizeActivitySum
  rw [canonicalPinnedReachSizePolymers_eq_nil_of_le
    n rootId distance size hsize]
  exact Q'.zero_mul_eqv _

/-- Every prefix ending before the first geometrically permitted size is
exactly zero. -/
theorem canonicalPinnedReachKPPrefix_eqv_zero
    (n rootId distance : Nat) :
    ∀ M, M ≤ distance + 1 →
      (finSum (fun size =>
        canonicalPinnedReachSizeWeightedActivity
          n rootId distance size) M).eqv 0
  | 0, _ => Q'.eqv_refl 0
  | k + 1, hk => by
      show (finSum (fun size =>
          canonicalPinnedReachSizeWeightedActivity
            n rootId distance size) k +
        canonicalPinnedReachSizeWeightedActivity
          n rootId distance k).eqv 0
      have hhead := canonicalPinnedReachKPPrefix_eqv_zero
        n rootId distance k (by omega)
      have hlast :=
        canonicalPinnedReachSizeWeightedActivity_eqv_zero_of_le
          n rootId distance k (by omega)
      refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr' hhead hlast
      · exact Q'.eqv_of_eq rfl

/-- The spatial tail begins at the first permitted grade, `distance + 1`.
`depth` is arbitrary and the estimate is uniform in it, the box, and the
pinned numerical face. -/
def canonicalPinnedReachShiftedKPSum
    (n rootId distance depth : Nat) : Q' :=
  finSum (fun offset =>
    canonicalPinnedReachSizeWeightedActivity n rootId distance
      (distance + 1 + offset)) depth

/-- Uniform exponential spatial boundary tail for the actual canonical
cutoff-one finite-box activities.  The base is the exact rational `6/25`. -/
theorem canonicalPinnedReachShiftedKPSum_le_boundaryTail
    (n rootId distance depth : Nat) :
    canonicalPinnedReachShiftedKPSum n rootId distance depth ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ (distance + 1) := by
  unfold canonicalPinnedReachShiftedKPSum
  have hsub :
      finSum (fun offset =>
          canonicalPinnedReachSizeWeightedActivity n rootId distance
            (distance + 1 + offset)) depth ≤
        finSum (fun offset =>
          canonicalPinnedSizeWeightedActivity n rootId
            (distance + 1 + offset)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        canonicalPinnedReachSizeWeightedActivity_le_pinned
          n rootId distance (distance + 1 + offset)) depth
  exact Q'.le_trans' _ _ _ hsub
    (canonicalPinnedShiftedKPSum_le_tail
      n rootId (distance + 1) depth)

/-- The complete reach-filtered KP sum over every size below `sizeCutoff`. -/
def canonicalPinnedReachTruncatedKPSum
    (n rootId distance sizeCutoff : Nat) : Q' :=
  finSum (fun size =>
    canonicalPinnedReachSizeWeightedActivity
      n rootId distance size) sizeCutoff

/-- Uniform spatial boundary estimate for an arbitrary size cutoff.  This is
the form needed to dominate finite-volume boundary corrections: no alignment
between the cutoff and the distance floor is assumed. -/
theorem canonicalPinnedReachTruncatedKPSum_le_boundaryTail
    (n rootId distance sizeCutoff : Nat) :
    canonicalPinnedReachTruncatedKPSum
        n rootId distance sizeCutoff ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ (distance + 1) := by
  let f : Nat → Q' := fun size =>
    canonicalPinnedReachSizeWeightedActivity
      n rootId distance size
  by_cases hcut : distance + 1 ≤ sizeCutoff
  · obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le hcut
    have hsplit := YMGap.Constructive.finSum_split
      f (distance + 1) depth
    have hprefix : (finSum f (distance + 1)).eqv 0 :=
      canonicalPinnedReachKPPrefix_eqv_zero
        n rootId distance (distance + 1) (Nat.le_refl _)
    have hcollapse :
        (finSum f (distance + 1) +
          finSum (fun offset => f (distance + 1 + offset)) depth).eqv
            (finSum (fun offset => f (distance + 1 + offset)) depth) := by
      refine Q'.eqv_trans _ ((0 : Q') +
          finSum (fun offset => f (distance + 1 + offset)) depth) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ hprefix
      · exact Q'.eqv_of_eq (Q'.zero_add' _)
    have hwhole :
        (finSum f (distance + 1 + depth)).eqv
          (finSum (fun offset => f (distance + 1 + offset)) depth) :=
      Q'.eqv_trans _ _ _ hsplit hcollapse
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hwhole)
      (canonicalPinnedReachShiftedKPSum_le_boundaryTail
        n rootId distance depth)
  · have hprefix :
        (finSum f sizeCutoff).eqv 0 :=
      canonicalPinnedReachKPPrefix_eqv_zero
        n rootId distance sizeCutoff (by omega)
    have htail0 : (0 : Q') ≤
        Q'.ofNat 2 * anchorEffectiveRatio ^ (distance + 1) :=
      Q'.mul_nonneg _ _ (by decide)
        (Q'.pow_nonneg anchorEffectiveRatio
          anchorEffectiveRatio_nonnegative (distance + 1))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hprefix) htail0

/-! ## 7. Boundary exit sums in the cofinal corner-box exhaustion -/

def canonicalPinnedExitSizeActivitySum
    (n rootId inner distance size : Nat) : Q' :=
  listQSum (canonicalSurfaceActivity anchorCoupling n)
    ((canonicalPinnedSizePolymers n rootId size).filter
      (canonicalPolymerExitsExpandedBoxB n inner distance))

theorem canonicalPinnedExitSizeActivitySum_le_reach
    {n rootId inner distance size : Nat}
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner) :
    canonicalPinnedExitSizeActivitySum
        n rootId inner distance size ≤
      canonicalPinnedReachSizeActivitySum
        n rootId (distance + 1) size := by
  unfold canonicalPinnedExitSizeActivitySum
    canonicalPinnedReachSizeActivitySum
    canonicalPinnedReachSizePolymers
  exact listQSum_filter_le_filter _ _ _
    (canonicalSurfacePolymer_activity_nonnegative n)
    (fun polymer hexit =>
      canonicalPolymerExitsExpandedBoxB_implies_reaches
        hrootInner hexit)
    (canonicalPinnedSizePolymers n rootId size)

def canonicalPinnedExitSizeWeightedActivity
    (n rootId inner distance size : Nat) : Q' :=
  canonicalPinnedExitSizeActivitySum n rootId inner distance size *
    eSurrogate ^ size

theorem canonicalPinnedExitSizeWeightedActivity_le_reach
    {n rootId inner distance size : Nat}
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner) :
    canonicalPinnedExitSizeWeightedActivity
        n rootId inner distance size ≤
      canonicalPinnedReachSizeWeightedActivity
        n rootId (distance + 1) size := by
  unfold canonicalPinnedExitSizeWeightedActivity
    canonicalPinnedReachSizeWeightedActivity
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (canonicalPinnedExitSizeActivitySum_le_reach hrootInner)
    (Q'.pow_nonneg eSurrogate eSurrogate_nonneg size)

def canonicalPinnedExitTruncatedKPSum
    (n rootId inner distance sizeCutoff : Nat) : Q' :=
  finSum (fun size =>
    canonicalPinnedExitSizeWeightedActivity
      n rootId inner distance size) sizeCutoff

/-- A fixed root in the inner box sees only an exponentially small total
activity from polymers which leave the box expanded by `distance`. -/
theorem canonicalPinnedExitTruncatedKPSum_le_boundaryTail
    {n rootId inner distance sizeCutoff : Nat}
    (hrootInner : boxPlaquetteAt n rootId ∈ boxPlaquettes inner) :
    canonicalPinnedExitTruncatedKPSum
        n rootId inner distance sizeCutoff ≤
      Q'.ofNat 2 * anchorEffectiveRatio ^ (distance + 2) := by
  unfold canonicalPinnedExitTruncatedKPSum
  have hsum :
      finSum (fun size =>
          canonicalPinnedExitSizeWeightedActivity
            n rootId inner distance size) sizeCutoff ≤
        canonicalPinnedReachTruncatedKPSum
          n rootId (distance + 1) sizeCutoff :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun size =>
        canonicalPinnedExitSizeWeightedActivity_le_reach hrootInner)
      sizeCutoff
  have htail := canonicalPinnedReachTruncatedKPSum_le_boundaryTail
    n rootId (distance + 1) sizeCutoff
  have hindex : distance + 1 + 1 = distance + 2 := by omega
  rw [hindex] at htail
  exact Q'.le_trans' _ _ _ hsum htail

end YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.decode_nodup
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.z4_nbrs_linfDist_le
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.enum_linf_reach_floor
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.canonicalSurfacePolymer_linf_size_floor
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.outside_expanded_box_linf_floor
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.canonicalSurfacePolymer_outside_box_size_floor
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.canonicalPinnedReachSizePolymers_eq_nil_of_le
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.listQSum_filter_le
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.listQSum_filter_le_filter
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.canonicalPinnedReachSizeActivitySum_le_pinned
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.canonicalPinnedReachShiftedKPSum_le_boundaryTail
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.canonicalPinnedReachTruncatedKPSum_le_boundaryTail
#print axioms YMGap.Continuum.Z4CanonicalPolymerBoundaryTail.canonicalPinnedExitTruncatedKPSum_le_boundaryTail
