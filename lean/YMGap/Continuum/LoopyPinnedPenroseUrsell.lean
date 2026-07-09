/-
`LoopyPinnedPenroseUrsell` — the PINNED LOOPY inhabitant of the (D1)-side
Penrose–Ursell datum (Milestone 13.1): the off-diagonal correlator field
`offCorr` is COMPUTED from the real decoded 4D animal enumeration — the graded
connecting-cluster activity sum over ALL exact-size polymers through the root
that BRIDGE separation `≥ d` in the (D2) metric — and the domination
`penrose_ursell` is PROVED from the decoder size floor, not carried.

# What was open, and what this closes (honest scope FIRST)

The (D1) atom as typed was discharged QUALIFIED (`MayerUrsellZ4PhysicalClose`,
commit `4c7c114`): its inhabitant pins a SINGLE-LINE `reconTransfer` model, and
the head-term arithmetic BYPASSES the (D2) geometry entirely — so the
"multi-plaquette" content lived only in the RHS count, not in the correlator.
This module supplies the LOOPY counterpart:

  * `loopyOffCorr p Vol d` — the graded bridging-cluster sum
    `Σ_{n < 2d+Vol} |{X ∈ enumPolys z4Chain p n : |X| = n, X reaches sep ≥ d}|
    · (coeffW w4 gr)^n` — a sum over ALL decoded connected 4D lattice animals
    through `p` (loops included) of their collapsed single-rep activities
    (`activity_single_rep`: `ζ(X) = (coeffW w r)^{|X|}`), restricted to
    clusters genuinely bridging the separation `d`.  This is the standard
    absolute connecting-cluster majorant series of the Mayer–Ursell expansion
    (unit Ursell weights), graded by TRUE cluster size.
  * `loopy_penrose_ursell` — the (D1)-side domination, PROVED: the low grades
    `n ≤ d` VANISH (the decoder size floor `DecoderReachFloor.enum_reach_floor`
    — the (D2) metric is LOAD-BEARING, not bypassed), and each surviving grade
    is dominated termwise by the KP summand `kpTerm` (filter ≤ full count,
    `1 ≤ eSurrogate^n`).
  * `loopyPinnedDatum : PenroseUrsellDatumG (z4ClusterCountBound p) w4 gr` —
    the A1-slot inhabitant with the pinned loopy `offCorr`, and
    `loopyBridgeDecomposition : BridgeDecomposition …` — the (D1) frontier-node
    inhabitant whose `offCorr` is the loopy sum (upgrading the single-line
    `bridgeDecomposition_z4_recon`).
  * `loopyOffCorr_decay` — the geometric decay `loopyOffCorr p Vol d ≤
    2·(15/32)^d` through the PROVED KP tail (`z4_genuine_threshold`).
  * NON-VACUITY: `loopyOffCorr_pos` — at the base plaquette the sum is
    STRICTLY POSITIVE (an explicit decoded 2-plaquette bridging animal,
    `witnessCode`), so the inhabitant is not the zero-correlator phantom.

# What remains open (AGENTS.md Rule 6 — NOT closed here)

`loopyOffCorr` is the absolute connecting-cluster MAJORANT sum, not the
signed physical Haar two-point function: the remaining identification —
that the REAL finite-volume heat-kernel truncated correlator is `≤` this
majorant (Ursell signs + the abstract↔real partition identity) — is the
named-open `AbstractPolymerXi.AbstractRealPartitionIdentity` / R1 wall,
UNTOUCHED.  Fixed spacing only (`ρ4 = 15/32 < 1`); NOT the spacing-uniform
continuum modulus; the frontier guard stays at 5; the Clay Yang–Mills mass
gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.Stage1LoopyReduction
import YMGap.Continuum.MayerUrsellZ4Physical
import YMGap.Continuum.MayerUrsellZ4PhysicalClose
import YMGap.Continuum.DecoderReachFloor
import YMGap.Continuum.AbstractPolymerXi

namespace YMGap.Continuum.LoopyPinnedPenroseUrsell

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Close
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.MayerUrsellZ4Physical
open YMGap.Continuum.MayerUrsellZ4PhysicalClose
open YMGap.Continuum.DecoderReachFloor
open YMGap.Continuum.AbstractPolymerXi

/-! ## 0. Small self-contained `Q'` helpers -/

/-- `a < b → b ≤ c → a < c` on `Q'` (local replica of the standard
cross-product proof; mirror of `Q'.lt_of_le_of_lt`). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hcd : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 had
    have hl : (a.den : Int) * (b.num * (c.den : Int))
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int))
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-- A single nonnegative-sequence term is dominated by any longer partial sum:
`k < N → g k ≤ finSum g N`. -/
theorem term_le_finSum (g : Nat → Q') (hg : ∀ i, (0 : Q') ≤ g i) :
    ∀ (k N : Nat), k < N → g k ≤ finSum g N
  | k, 0, h => absurd h (Nat.not_lt_zero k)
  | k, N + 1, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
      · exact Q'.le_trans' _ _ _ (term_le_finSum g hg k N h')
          (Q'.add_le_self_of_nonneg _ _ (hg N))
      · show g k ≤ finSum g k + g k
        have h0 : (0 : Q') + g k ≤ finSum g k + g k :=
          Q'.add_le_add_right _ _ _ (finSum_nonneg' g hg k)
        rwa [Q'.zero_add'] at h0

/-! ## 1. The pinned loopy bridging-cluster sum -/

/-- The BRIDGING test: does the polymer `X` reach a plaquette at (D2)
separation `≥ d` from the root `p`?  (`Bool`, so it filters.) -/
def reachB (p : z4Chain.toLattice.Plaquette) (X : Polymer z4Chain.toLattice)
    (d : Nat) : Bool :=
  X.any (fun q => decide (d ≤ z4dist p q))

/-- The grade-`n` bridging clusters through `p`: the decoded animals of the
REAL enumeration `enumPolys` with EXACT size `n` (true-size grading — the
grade-`n` slot of `kpTerm` stands for size-`n` clusters) that bridge
separation `≥ d`. -/
def bridgePolys (p : z4Chain.toLattice.Plaquette) (d n : Nat) :
    List (Polymer z4Chain.toLattice) :=
  (enumPolys z4Chain p n).filter (fun X => X.length == n && reachB p X d)

/-- The grade-`n` bridging weight: the bridging-cluster count times the
collapsed single-rep activity `(coeffW w4 gr)^n` (`activity_single_rep`:
the true activity of a size-`n` constrained connected polymer). -/
def bridgeWeight (p : z4Chain.toLattice.Plaquette) (d n : Nat) : Q' :=
  Q'.ofNat (bridgePolys p d n).length * (coeffW w4 gr) ^ n

/-- **The pinned loopy off-diagonal correlator** at bridging distance `d`:
the graded bridging-cluster activity sum over all grades below the
finite-volume truncation `2d + Vol`.  This is the absolute connecting-cluster
majorant sum of the Mayer–Ursell expansion for the z4 polymer gas — a sum
over genuinely LOOPY 4D animals, NOT a single-line spectral model. -/
def loopyOffCorr (p : z4Chain.toLattice.Plaquette) (Vol d : Nat) : Q' :=
  finSum (fun n => bridgeWeight p d n) (d + (d + Vol))

theorem bridgeWeight_nonneg (p : z4Chain.toLattice.Plaquette) (d n : Nat) :
    (0 : Q') ≤ bridgeWeight p d n :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg _)
    (Q'.pow_nonneg _ (coeffW_nonneg w4_nonneg gr) n)

/-! ## 2. The size floor: low grades vanish ((D2) LOAD-BEARING) -/

/-- **The size floor (PROVED — the (D2) metric at work).**  No exact-size-`n`
decoded animal through `p` bridges separation `≥ d` when `n ≤ d`: by the
decoder distance invariant (`enum_reach_floor`), reaching `z4dist ≥ d` forces
`|X| ≥ d + 1 > n`.  Hence the grade-`n` bridging list is EMPTY. -/
theorem bridgePolys_eq_nil (p : z4Chain.toLattice.Plaquette) (d n : Nat)
    (hn : n ≤ d) : bridgePolys p d n = [] := by
  cases hbp : bridgePolys p d n with
  | nil => rfl
  | cons X t =>
      exfalso
      have hX : X ∈ bridgePolys p d n := by
        rw [hbp]; exact List.mem_cons_self
      have hmem := List.mem_filter.mp hX
      have hand := (Bool.and_eq_true _ _).mp hmem.2
      have hlen : X.length = n := (beq_iff_eq).mp hand.1
      obtain ⟨q, hqX, hqd⟩ := List.any_eq_true.mp hand.2
      have hd' : d ≤ z4dist p q := of_decide_eq_true hqd
      have hfloor := enum_reach_floor p n X hmem.1 q hqX d hd'
      omega

/-- The grade-`n` bridging weight vanishes for `n ≤ d`. -/
theorem bridgeWeight_eqv_zero (p : z4Chain.toLattice.Plaquette) (d n : Nat)
    (hn : n ≤ d) : (bridgeWeight p d n).eqv 0 := by
  unfold bridgeWeight
  rw [bridgePolys_eq_nil p d n hn]
  show ((0 : Q') * (coeffW w4 gr) ^ n).eqv 0
  exact Q'.zero_mul_eqv _

/-- The whole grade prefix `n < M ≤ d` of the loopy sum vanishes. -/
theorem prefix_eqv_zero (p : z4Chain.toLattice.Plaquette) (d : Nat) :
    ∀ M, M ≤ d → (finSum (fun n => bridgeWeight p d n) M).eqv 0
  | 0, _ => Q'.eqv_of_eq rfl
  | M + 1, h => by
      show (finSum (fun n => bridgeWeight p d n) M + bridgeWeight p d M).eqv 0
      have h1 := prefix_eqv_zero p d M (Nat.le_of_succ_le h)
      have h2 := bridgeWeight_eqv_zero p d M (Nat.le_of_succ_le h)
      refine Q'.eqv_trans _ _ _ (add_eqv_congr_both _ _ _ _ h1 h2) ?_
      decide

/-! ## 3. Termwise KP domination and the PROVED `penrose_ursell` -/

/-- **Termwise KP domination (PROVED).**  Every grade's bridging weight is
dominated by the collapsed KP summand: the bridging count is a FILTER of the
enumeration whose full length IS `animalCount` (nothing free), and
`1 ≤ eSurrogate^n` supplies the tree-graph weight slot. -/
theorem bridgeWeight_le_kpTerm (p : z4Chain.toLattice.Plaquette) (d n : Nat) :
    bridgeWeight p d n ≤ kpTerm (z4ClusterCountBound p) w4 gr n := by
  unfold kpTerm
  have hpow_nn : (0 : Q') ≤ (coeffW w4 gr) ^ n :=
    Q'.pow_nonneg _ (coeffW_nonneg w4_nonneg gr) n
  have hcount : Q'.ofNat (bridgePolys p d n).length
      ≤ (z4ClusterCountBound p).animalCount n := by
    show Q'.ofNat (bridgePolys p d n).length
        ≤ Q'.ofNat (enumPolys z4Chain p n).length
    exact ClusterCount.ofNat_le_ofNat (List.length_filter_le _ _)
  have h1 : bridgeWeight p d n
      ≤ (z4ClusterCountBound p).animalCount n * (coeffW w4 gr) ^ n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcount hpow_nn
  have hAnn : (0 : Q')
      ≤ (z4ClusterCountBound p).animalCount n * (coeffW w4 gr) ^ n :=
    Q'.mul_nonneg _ _ ((z4ClusterCountBound p).animalCount_nonneg n) hpow_nn
  have hE : (1 : Q') ≤ eSurrogate ^ n := one_le_pow_loc (by decide) n
  have h2 : (z4ClusterCountBound p).animalCount n * (coeffW w4 gr) ^ n
      ≤ (z4ClusterCountBound p).animalCount n * (coeffW w4 gr) ^ n
          * eSurrogate ^ n := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hE hAnn
  exact Q'.le_trans' _ _ _ h1 h2

/-- **`loopy_penrose_ursell` (PROVED — the (D1)-side domination for the
pinned LOOPY correlator).**  Split the graded sum at `d`; the prefix
vanishes by the (D2) size floor; the tail is termwise KP-dominated:

    loopyOffCorr p Vol d  ≤  Σ_{m < d+Vol} kpTerm (z4ClusterCountBound p) w4 gr (d+m)
                           =  connTailPartialG (z4ClusterCountBound p) w4 gr d (d+Vol). -/
theorem loopy_penrose_ursell (p : z4Chain.toLattice.Plaquette) (Vol d : Nat) :
    loopyOffCorr p Vol d
      ≤ connTailPartialG (z4ClusterCountBound p) w4 gr d (d + Vol) := by
  have hsplit := finSum_split (fun n => bridgeWeight p d n) d (d + Vol)
  have hpre := prefix_eqv_zero p d d (Nat.le_refl d)
  have htot : (loopyOffCorr p Vol d).eqv
      (finSum (fun j => bridgeWeight p d (d + j)) (d + Vol)) := by
    refine Q'.eqv_trans _ _ _ hsplit ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hpre) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' _)
  have htail : finSum (fun j => bridgeWeight p d (d + j)) (d + Vol)
      ≤ finSum (fun j => kpTerm (z4ClusterCountBound p) w4 gr (d + j)) (d + Vol) :=
    CharacterTail.finSum_le_termwise _ _
      (fun j => bridgeWeight_le_kpTerm p d (d + j)) (d + Vol)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htot) htail

/-! ## 4. The pinned inhabitants -/

/-- **`loopyPinnedDatum` (PROVED — the pinned LOOPY A1-slot inhabitant).**
`offCorr` is COMPUTED from the decoded enumeration (the graded bridging-
cluster activity sum), `tailLen d = d + Vol`, and `penrose_ursell` is the
PROVED `loopy_penrose_ursell` — nothing is carried as data.  Contrast the
single-line `reconTransfer` inhabitant (`4c7c114`): here the correlator sums
over ALL bridging 4D animals (loops included) and the (D2) size floor is
load-bearing. -/
def loopyPinnedDatum (p : z4Chain.toLattice.Plaquette) (Vol : Nat) :
    PenroseUrsellDatumG (z4ClusterCountBound p) w4 gr where
  offCorr := loopyOffCorr p Vol
  tailLen := fun d => d + Vol
  tailLen_ge := fun d => Nat.le_add_right d Vol
  penrose_ursell := fun d => loopy_penrose_ursell p Vol d

/-- **`loopyBridgeDecomposition` (PROVED — the LOOPY (D1) frontier-node
inhabitant).**  The `BridgeDecomposition` whose `offCorr` is the pinned loopy
sum and whose `bridgeTerm` is the genuine `kpTerm` — upgrading the
single-line `bridgeDecomposition_z4_recon`.  (Not a guard type; conditional
frontier structure only.) -/
def loopyBridgeDecomposition (p : z4Chain.toLattice.Plaquette) (Vol : Nat) :
    BridgeDecomposition (z4ClusterCountBound p) w4 gr where
  offCorr := loopyOffCorr p Vol
  bridgeTerm := kpTerm (z4ClusterCountBound p) w4 gr
  tailLen := fun d => d + Vol
  tailLen_ge := fun d => Nat.le_add_right d Vol
  decompose := fun d => loopy_penrose_ursell p Vol d

/-- **`loopyOffCorr_decay` (PROVED).**  The pinned loopy correlator decays
geometrically at the PROVED 4D strong-coupling rate: `loopyOffCorr p Vol d ≤
2·ρ4^d`, `ρ4 = kpRatio (z4ClusterCountBound p) w4 gr ≃ 15/32 < 1`. -/
theorem loopyOffCorr_decay (p : z4Chain.toLattice.Plaquette) (Vol d : Nat) :
    loopyOffCorr p Vol d
      ≤ Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ d :=
  penroseUrsell_offCorr_decayG (z4ClusterCountBound p) w4_nonneg gr
    (z4_genuine_threshold p) (loopyPinnedDatum p Vol) d

/-! ## 5. NON-VACUITY: an explicit decoded bridging animal -/

/-- The base plaquette (origin, `x0x1`-plane). -/
def p0 : z4Chain.toLattice.Plaquette :=
  (((0 : Nat), (0 : Nat), (0 : Nat), (0 : Nat)), Z4Plane.p01)

/-- An explicit grade-2 code: symbol `12` descends to the first block-3
neighbour (base `addE` one step in `x1`, potential `+1`), symbol `24`
backtracks.  Decodes to a genuine 2-plaquette bridging animal. -/
def witnessCode : List (Fin (z4Chain.D + 1)) :=
  [⟨12, by decide⟩, ⟨24, by decide⟩]

theorem witnessCode_mem : witnessCode ∈ codes z4Chain 2 := by decide

/-- The decoded witness polymer. -/
def witnessX : Polymer z4Chain.toLattice := decode z4Chain p0 witnessCode

theorem witnessX_mem : witnessX ∈ enumPolys z4Chain p0 2 :=
  List.mem_map.mpr ⟨witnessCode, witnessCode_mem, rfl⟩

/-- The witness has exact size 2 and bridges separation `≥ 1` (kernel
computation on the explicit decode). -/
theorem witnessX_pred :
    (witnessX.length == 2 && reachB p0 witnessX 1) = true := by decide

theorem witnessX_bridge : witnessX ∈ bridgePolys p0 1 2 :=
  List.mem_filter.mpr ⟨witnessX_mem, witnessX_pred⟩

theorem bridgeCount_pos : 1 ≤ (bridgePolys p0 1 2).length :=
  List.length_pos_of_mem witnessX_bridge

/-- The witness grade's bridging weight is strictly positive. -/
theorem bridgeWeight_witness_pos : (0 : Q') < bridgeWeight p0 1 2 := by
  have h1 : (1 : Q') ≤ Q'.ofNat (bridgePolys p0 1 2).length :=
    Q'.le_trans' _ _ _ (by decide) (ClusterCount.ofNat_le_ofNat bridgeCount_pos)
  have hpw : (0 : Q') < (coeffW w4 gr) ^ 2 := by decide
  have h2 : (coeffW w4 gr) ^ 2 ≤ bridgeWeight p0 1 2 := by
    unfold bridgeWeight
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ h1
      (Q'.pow_nonneg _ (coeffW_nonneg w4_nonneg gr) 2)
  exact lt_of_lt_of_le hpw h2

/-- **`loopyOffCorr_pos` (PROVED — the non-phantom certificate).**  The
pinned loopy correlator is STRICTLY POSITIVE at the base plaquette
(`d = 1`, `Vol = 1`): the explicit decoded bridging animal contributes.
This is the exact contrast with the zero-correlator phantom `diagModel`
(`diagModel_corr_offdiag_zero`): the loopy inhabitant carries genuine
bridging-cluster content. -/
theorem loopyOffCorr_pos : (0 : Q') < loopyOffCorr p0 1 1 := by
  have hterm : bridgeWeight p0 1 2 ≤ loopyOffCorr p0 1 1 :=
    term_le_finSum (fun n => bridgeWeight p0 1 n)
      (fun n => bridgeWeight_nonneg p0 1 n) 2 3 (by decide)
  exact lt_of_lt_of_le bridgeWeight_witness_pos hterm

/-! ## 6. The A-side capstone reduces to A2 ALONE (at the pinned instance) -/

/-- **`stage1Loopy_pinned` (PROVED — the A-side collapses to A2).**  With the
pinned loopy datum filling the A1 slot, the whole `Stage1Loopy` capstone is
inhabited GIVEN only A2 (`BeyondTreePartitionIdentity`, carrying the
non-vacuous `SixJRecoupling`): the A-side of Sub-wall A now rests on exactly
ONE named atom.  Its `.decay` is the 4D loopy correlator decay at
`ρ4 ≃ 15/32 < 1` for the pinned bridging-cluster correlator. -/
def stage1Loopy_pinned [DecidableEq z4Chain.toLattice.Plaquette]
    (p : z4Chain.toLattice.Plaquette)
    (label : z4Chain.toLattice.Plaquette → Rep) (Vol : Nat)
    (bt : PartitionBeyondTree.BeyondTreePartitionIdentity
      (L := z4Chain.toLattice) w4 label) :
    Stage1Loopy p label where
  ursell := loopyPinnedDatum p Vol
  beyondTree := bt

/-! ## 7. Documentation: PROVED vs the OPEN wall (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `bridgePolys_eq_nil` / `bridgeWeight_eqv_zero` / `prefix_eqv_zero` — the
    size floor: grades `n ≤ d` carry NO bridging cluster ((D2) load-bearing
    via `DecoderReachFloor.enum_reach_floor`);
  * `bridgeWeight_le_kpTerm` — termwise KP domination (filtered count ≤ the
    genuine `animalCount`);
  * `loopy_penrose_ursell` — the (D1)-side domination for the pinned loopy
    correlator, PROVED (split + vanish + termwise);
  * `loopyPinnedDatum` / `loopyBridgeDecomposition` — the pinned loopy
    inhabitants of the A1 slot and the (D1) frontier node;
  * `loopyOffCorr_decay` — geometric decay at the proved `ρ4 ≃ 15/32`;
  * `witnessCode…loopyOffCorr_pos` — non-vacuity (an explicit decoded
    bridging animal; strictly positive correlator).

OPEN (NAMED, deliberately untouched — the honest residual):

  * the identification of `loopyOffCorr` (the absolute connecting-cluster
    majorant) with an UPPER bound on the real signed Haar two-point function
    — the Ursell-sign layer plus the abstract↔real partition identity
    (`AbstractPolymerXi.AbstractRealPartitionIdentity`, the R1 wall);
  * everything continuum: this is fixed spacing (`ρ4 = 15/32 < 1`), NOT the
    spacing-uniform modulus, NOT `singleStep`, NOT the Clay problem. -/

end YMGap.Continuum.LoopyPinnedPenroseUrsell

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.lt_of_lt_of_le
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.term_le_finSum
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.bridgeWeight_nonneg
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.bridgePolys_eq_nil
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.bridgeWeight_eqv_zero
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.prefix_eqv_zero
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.bridgeWeight_le_kpTerm
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.loopy_penrose_ursell
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.loopyPinnedDatum
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.loopyBridgeDecomposition
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.loopyOffCorr_decay
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.witnessX_pred
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.bridgeWeight_witness_pos
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.loopyOffCorr_pos
#print axioms YMGap.Continuum.LoopyPinnedPenroseUrsell.stage1Loopy_pinned
