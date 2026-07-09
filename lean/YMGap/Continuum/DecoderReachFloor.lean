/-
`DecoderReachFloor` — the DFS-decoder DISTANCE INVARIANT: every plaquette the
depth-first decoder visits lies within `|visited| − 1` metric steps of the
root.  This is the missing bridge between the (D2) separation metric and the
(D1) loopy cluster geometry (Milestone 13.1): it converts "a decoded polymer
REACHES separation `d`" into the SIZE FLOOR "the polymer has `≥ d + 1`
plaquettes" — for the REAL decoded enumeration `enumPolys`, not for an
abstract `AdjPath` datum.

# Why this is needed (Milestone 13.1, the D1-loopy wall)

`PinnedCluster.connected_spanning_size_ge` already gives a size floor, but it
CONSUMES an in-polymer `AdjPath` — data that nothing constructs for the real
decoded animals of `BddLatticeAnimal.enumPolys`.  The under-constrained (D1)
inhabitant (`MayerUrsellZ4PhysicalClose`) bypassed the geometry entirely (the
head-term route, single-line model).  To pin the LOOPY multi-plaquette
connecting-cluster sum, the size floor must be derived for every decoded
polymer directly.  This module does that by a fold invariant on the decoder
state — the (D2) metric (`SepLatticeZ4Close.z4dist`) becomes LOAD-BEARING for
the first time on the (D1) chain.

# What is delivered (all PROVED, axiom-clean)

  * `Inv` — the decoder-state invariant: the current plaquette and the whole
    backtrack stack are visited, and every visited plaquette `q` satisfies
    `dist root q + 1 ≤ |visited|`.
  * `inv_init` / `inv_step` / `inv_foldl` — the invariant holds initially and
    is preserved by every decoder step (descend AND backtrack), for ANY
    `Nat`-valued `dist` with the triangle inequality and the ONE lattice
    compatibility fact `hnb : b ∈ nbrs a → dist a b ≤ 1`.
  * `decode_dist_floor` — the generic conclusion: every plaquette of a decoded
    polymer is within `|X| − 1` steps of the root.
  * `sVertex_subE_le` / `sVertex_le_subE_succ` / `edgePlaqs_window` /
    `z4_nbrs_dist_le` — the z4 instance of `hnb`: every
    enumerated neighbour is within `z4dist ≤ 1` (each of the 24 candidates
    moves the base potential by at most one).
  * `z4_decode_dist_floor` / `enum_reach_floor` — the 4D payload: every
    decoded polymer `X ∈ enumPolys z4Chain p n` containing a plaquette `q`
    with `d ≤ z4dist p q` has `d + 1 ≤ |X|`.  THE size floor for the pinned
    loopy connecting-cluster sum (consumed by `LoopyPinnedPenroseUrsell`).

# Honest scope (AGENTS.md Rule 6)

This is a finite combinatorial invariant about the REAL decoder over the
GENUINE z4 geometry — fixed spacing, no Haar integral, no Ursell signs, no
cluster-expansion identity.  It does NOT discharge (D1)'s physical expansion
identity, does NOT touch the continuum modulus, and does NOT close any
Clay-frontier type.  The Clay Yang–Mills mass gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.  Every
load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.BddLatticeAnimal
import YMGap.Continuum.SepLatticeZ4Close

namespace YMGap.Continuum.DecoderReachFloor

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Close

/-! ## 1. The generic decoder invariant

Everything in this section is generic over a bounded-degree lattice `BL` and
an ABSTRACT `Nat`-valued plaquette distance `dist`.  Only three facts about
`dist` are consumed — `dist p p = 0` (at the root), the triangle inequality,
and the single lattice-compatibility bound `b ∈ nbrs a → dist a b ≤ 1`.  The
z4 instance is discharged in §2. -/

variable (BL : BddLattice)
variable (dist : BL.toLattice.Plaquette → BL.toLattice.Plaquette → Nat)

/-- **The decoder-state invariant.**  Relative to the root `p`:
  (i) the current plaquette is visited;
  (ii) every stack entry is visited;
  (iii) every visited plaquette `q` has `dist p q + 1 ≤ |visited|` —
        the DISTANCE FLOOR (a plaquette `d` steps out needs `≥ d + 1`
        visited plaquettes, since each decoder descent adds one plaquette
        and moves the current plaquette by `≤ 1`). -/
def Inv (p : BL.toLattice.Plaquette) (s : DState BL) : Prop :=
  s.current ∈ s.visited ∧ (∀ t, t ∈ s.stack → t ∈ s.visited) ∧
    (∀ q, q ∈ s.visited → dist p q + 1 ≤ s.visited.length)

/-- The invariant holds at the initial state (visited `= [p]`, so the floor
is `dist p p + 1 ≤ 1`, i.e. `dist p p = 0`). -/
theorem inv_init (p : BL.toLattice.Plaquette) (hself : dist p p = 0) :
    Inv BL dist p (initState BL p) := by
  refine ⟨List.mem_cons_self, ?_, ?_⟩
  · intro t ht
    exact absurd ht List.not_mem_nil
  · intro q hq
    have h : q = p := by
      rcases List.mem_cons.mp hq with h | h
      · exact h
      · exact absurd h List.not_mem_nil
    rw [h]
    show dist p p + 1 ≤ 1
    omega

/-- **The invariant is preserved by one decoder step** (both the descend and
the backtrack branch).  The descend branch is where the metric works: the
fresh plaquette `q` is an enumerated neighbour of `current`
(`List.mem_of_getElem?` on the indexed lookup), so `dist current q ≤ 1`
(`hnb`), and the triangle inequality through `current` (whose floor is the
inductive hypothesis) gives the extended floor for the grown visited list. -/
theorem inv_step (p : BL.toLattice.Plaquette)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (hnb : ∀ a b, b ∈ BL.nbrs a → dist a b ≤ 1)
    (s : DState BL) (c : Fin (BL.D + 1)) (h : Inv BL dist p s) :
    Inv BL dist p (step BL s c) := by
  obtain ⟨hcur, hstk, hd⟩ := h
  unfold step
  split
  · -- descend instruction `c.val < BL.D`
    split
    · -- lookup `none`: state unchanged
      exact ⟨hcur, hstk, hd⟩
    · -- lookup `some q`
      rename_i q hq
      split
      · -- `q` already visited: state unchanged
        exact ⟨hcur, hstk, hd⟩
      · -- fresh `q`: current := q, push current, visit q
        have hqnbr : q ∈ BL.nbrs s.current := List.mem_of_getElem? hq
        refine ⟨List.mem_cons_self, ?_, ?_⟩
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | h'
          · exact List.mem_cons_of_mem _ hcur
          · exact List.mem_cons_of_mem _ (hstk t h')
        · intro q' hq'
          show dist p q' + 1 ≤ (q :: s.visited).length
          rw [List.length_cons]
          rcases List.mem_cons.mp hq' with rfl | h'
          · -- the fresh plaquette: triangle through `current`
            have h1 : dist p q' ≤ dist p s.current + dist s.current q' :=
              htri p s.current q'
            have h2 : dist p s.current + 1 ≤ s.visited.length :=
              hd s.current hcur
            have h3 : dist s.current q' ≤ 1 := hnb s.current q' hqnbr
            omega
          · -- an old plaquette: the old floor, list one longer
            have := hd q' h'
            omega
  · -- backtrack instruction
    split
    · -- empty stack: state unchanged
      exact ⟨hcur, hstk, hd⟩
    · -- pop `t :: rest`
      rename_i t rest hstack
      refine ⟨?_, ?_, hd⟩
      · exact hstk t (by rw [hstack]; exact List.mem_cons_self)
      · intro x hx
        exact hstk x (by rw [hstack]; exact List.mem_cons_of_mem _ hx)

/-- The invariant is preserved by the whole fold over a code. -/
theorem inv_foldl (p : BL.toLattice.Plaquette)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (hnb : ∀ a b, b ∈ BL.nbrs a → dist a b ≤ 1) :
    ∀ (code : List (Fin (BL.D + 1))) (s : DState BL),
      Inv BL dist p s → Inv BL dist p (code.foldl (step BL) s)
  | [], _, h => h
  | c :: cs, s, h =>
      inv_foldl p htri hnb cs (step BL s c) (inv_step BL dist p htri hnb s c h)

/-- **`decode_dist_floor` (PROVED — the generic distance floor).**  Every
plaquette of a decoded polymer lies within `|X| − 1` metric steps of the
root: `∀ q ∈ decode BL p code, dist p q + 1 ≤ |decode BL p code|`. -/
theorem decode_dist_floor (p : BL.toLattice.Plaquette)
    (hself : dist p p = 0)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (hnb : ∀ a b, b ∈ BL.nbrs a → dist a b ≤ 1)
    (code : List (Fin (BL.D + 1))) :
    ∀ q, q ∈ decode BL p code →
      dist p q + 1 ≤ (decode BL p code).length :=
  (inv_foldl BL dist p htri hnb code (initState BL p)
    (inv_init BL dist p hself)).2.2

/-! ## 2. The z4 instance: every enumerated neighbour moves the potential by `≤ 1`

The (D2) L¹ potential metric `z4dist` (`SepLatticeZ4Close`) satisfies the
lattice-compatibility bound for the REAL degree-24 neighbour enumeration
`z4Nbrs`: every one of the 24 candidates has its base at `u`, `subE u m`, or
one `addE` step from `p.1` — all within one unit of potential. -/

/-- `subE` lowers the potential by at most one. -/
theorem sVertex_subE_le (v : Z4Vertex) (m : Dir4) :
    sVertex (subE v m) ≤ sVertex v := by
  obtain ⟨a, b, c, d⟩ := v
  cases m <;> simp [sVertex, subE] <;> omega

/-- `subE` lowers the potential by at least... i.e. the original potential is
within one of the decremented one (truncation-safe). -/
theorem sVertex_le_subE_succ (v : Z4Vertex) (m : Dir4) :
    sVertex v ≤ sVertex (subE v m) + 1 := by
  obtain ⟨a, b, c, d⟩ := v
  cases m <;> simp [sVertex, subE] <;> omega

/-- The potential window of an `edgePlaqs` member: within one unit of the
carrying edge's base potential (each of the six candidates per direction is
based at `u` or one `subE` step from `u`; with the base vertex destructured,
everything reduces to `Nat` arithmetic). -/
theorem edgePlaqs_window (q : Z4Plaq) (u : Z4Vertex) (d : Dir4)
    (h : q ∈ edgePlaqs u d) :
    sVertex q.1 ≤ sVertex u ∧ sVertex u ≤ sVertex q.1 + 1 := by
  obtain ⟨a, b, c, e⟩ := u
  cases d <;>
    simp only [edgePlaqs, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;>
    simp [sVertex, subE] <;>
    omega

/-- **`z4_nbrs_dist_le` (PROVED — the z4 lattice-compatibility bound).**
Every enumerated neighbour of `p` is within one unit of `p`'s potential:
`q ∈ z4Nbrs p → z4dist p q ≤ 1`.  Case split over the four `edgePlaqs`
blocks; the two far blocks are based one `addE` step up
(`sVertex_addE`), so their windows sit at `[s, s+1]` instead of
`[s−1, s]` — both within distance `1`. -/
theorem z4_nbrs_dist_le (p q : Z4Plaq) (h : q ∈ z4Nbrs p) :
    z4dist p q ≤ 1 := by
  unfold z4Nbrs at h
  have hs : sPlaq p = sVertex p.1 := rfl
  rcases List.mem_append.mp h with h' | h4
  · rcases List.mem_append.mp h' with h'' | h3
    · rcases List.mem_append.mp h'' with h1 | h2
      · -- block 1: base window [s−1, s]
        have := edgePlaqs_window q p.1 (dirsOf p.2).1 h1
        simp only [z4dist, sPlaq]
        omega
      · -- block 2: base window [s−1, s]
        have := edgePlaqs_window q p.1 (dirsOf p.2).2 h2
        simp only [z4dist, sPlaq]
        omega
    · -- block 3: base window [s, s+1] (one addE step up)
      have hw := edgePlaqs_window q (addE p.1 (dirsOf p.2).2) (dirsOf p.2).1 h3
      have ha : sVertex (addE p.1 (dirsOf p.2).2) = sVertex p.1 + 1 :=
        sVertex_addE p.1 (dirsOf p.2).2
      simp only [z4dist, sPlaq]
      omega
  · -- block 4: base window [s, s+1] (one addE step up)
    have hw := edgePlaqs_window q (addE p.1 (dirsOf p.2).1) (dirsOf p.2).2 h4
    have ha : sVertex (addE p.1 (dirsOf p.2).1) = sVertex p.1 + 1 :=
      sVertex_addE p.1 (dirsOf p.2).1
    simp only [z4dist, sPlaq]
    omega

/-! ## 3. The 4D payload: the size floor for decoded z4 polymers -/

/-- **`z4_decode_dist_floor` (PROVED).**  Every plaquette of a decoded z4
polymer lies within `|X| − 1` potential steps of the root. -/
theorem z4_decode_dist_floor (p : Z4Plaq) (code : List (Fin (z4Chain.D + 1))) :
    ∀ q, q ∈ decode z4Chain p code →
      z4dist p q + 1 ≤ (decode z4Chain p code).length :=
  decode_dist_floor z4Chain z4dist p
    (by simp only [z4dist]; omega)
    (fun a b c => by simp only [z4dist]; omega)
    z4_nbrs_dist_le
    code

/-- **`enum_reach_floor` (PROVED — THE size floor for the pinned loopy sum,
Milestone 13.1).**  Every enumerated z4 polymer `X ∈ enumPolys z4Chain p n`
containing a plaquette `q` at separation `≥ d` from the root has size
`≥ d + 1`:

    X ∈ enumPolys z4Chain p n  →  q ∈ X  →  d ≤ z4dist p q  →  d + 1 ≤ |X|.

This is the decoded-enumeration counterpart of (D2)'s
`connected_spanning_size_ge`, with the `AdjPath` datum REPLACED by the
decoder invariant — so it applies to the REAL animals of the (D1) loopy
connecting-cluster sum, at every grade `n`. -/
theorem enum_reach_floor (p : Z4Plaq) (n : Nat) (X : Polymer z4Lattice)
    (hX : X ∈ enumPolys z4Chain p n) (q : Z4Plaq) (hq : q ∈ X)
    (d : Nat) (hsep : d ≤ z4dist p q) : d + 1 ≤ X.length := by
  obtain ⟨code, _, rfl⟩ := List.mem_map.mp hX
  have hfloor := z4_decode_dist_floor p code q hq
  exact Nat.le_trans (Nat.succ_le_succ hsep) hfloor

end YMGap.Continuum.DecoderReachFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DecoderReachFloor.inv_init
#print axioms YMGap.Continuum.DecoderReachFloor.inv_step
#print axioms YMGap.Continuum.DecoderReachFloor.inv_foldl
#print axioms YMGap.Continuum.DecoderReachFloor.decode_dist_floor
#print axioms YMGap.Continuum.DecoderReachFloor.sVertex_subE_le
#print axioms YMGap.Continuum.DecoderReachFloor.sVertex_le_subE_succ
#print axioms YMGap.Continuum.DecoderReachFloor.edgePlaqs_window
#print axioms YMGap.Continuum.DecoderReachFloor.z4_nbrs_dist_le
#print axioms YMGap.Continuum.DecoderReachFloor.z4_decode_dist_floor
#print axioms YMGap.Continuum.DecoderReachFloor.enum_reach_floor
