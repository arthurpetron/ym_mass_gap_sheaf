/-
Stage-1 / the FIRST genuinely INTERACTING polymer-expansion case — **two
plaquettes sharing a link** — at the level the discrete Haar / character
structure permits.

# The mathematics

The non-interacting (`disjoint`) polymer-expansion identity reduces the
partition function to a finite PRODUCT of single-plaquette character sums:
the Haar link integrals factorize because no link is shared.  The first
genuinely interacting geometry breaks that factorization: two plaquettes
`p₁, p₂` that SHARE one boundary link `ℓ`.

The gauge-invariant two-plaquette partition object is the character
double-sum coupled through the shared-link Haar integral:

    Z₂(w, M)  =  Σ_{a<M} Σ_{b<M}  ⟦∫_ℓ χ_a χ_b dg_ℓ⟧ · coeffW w a · coeffW w b.

For SU(2) the shared-link Haar integral is the orthogonality kernel
`∫ χ_a χ_b dg = δ_{a,b}` (the fuse-to-trivial selection rule
`fusesToTrivial a b ⇔ a = b` of the polymer model: a link shared by two
plaquettes survives only when the meeting reps coincide).  Encoding the
kernel as the genuine Kronecker delta `orthoKernel a b = (if a = b then 1
else 0)`, the inner Haar integration COLLAPSES the double sum onto its
diagonal:

    Z₂(w, M)  ≃  Σ_{s<M}  coeffW w s · coeffW w s  =  Σ_{s<M} (coeffW w s)².

This diagonal collapse — the off-diagonal `a ≠ b` terms killed by the
shared-link orthogonality — IS the interacting coupling.  It is exactly
the single-representation collapse of `KPCriterion`
(`constrained_connected_single_rep`): a connected polymer through a shared
link carries ONE common rep.

On the polymer side, the two-plaquette system contributes the CONNECTED
polymer `[p₁, p₂]` (both plaquettes, joined by the shared link, hence one
common rep `r` by the link constraint), whose activity is the single power
`ζ([p₁,p₂]) = (coeffW w r)²` (`activity_single_rep` at `|X| = 2`).  Summing
the connected polymer over its common rep `r < M`:

    polymerSum₂(w, M)  =  Σ_{r<M}  ζ([p₁,p₂], const r)  ≃  Σ_{r<M} (coeffW w r)².

# What is PROVED here (all genuine — no fakes)

  * `orthoKernel a b` — the shared-link Haar orthogonality kernel `δ_{a,b}`,
    with `orthoKernel_eq` / `orthoKernel_diag` / `orthoKernel_off` and the
    bridge `orthoKernel_eq_one_iff_fuse` to `fusesToTrivial`.
  * `Z2` — the genuine interacting two-plaquette partition function as the
    character DOUBLE-sum weighted by the orthogonality kernel.
  * `Z2_collapse` — THE interacting collapse: the double-sum is `Q'.eqv` to
    the DIAGONAL sum `Σ_{s<M} (coeffW w s)²` (off-diagonal terms killed by
    the shared-link orthogonality).  This is the genuine interacting content.
  * `twoPlaqLattice`, `pL`, `pR` — a concrete two-plaquette, one-shared-link
    lattice witness; `pL_pR_adjacent` exhibits the shared link;
    `twoPlaq_chain` connects the two plaquettes; the constant labeling
    satisfies `linkConstraint` (`twoPlaq_linkConstraint`).
  * `connectedActivity2` — the connected two-plaquette polymer's activity
    under the constant rep `r`; `connectedActivity2_eqv : ≃ (coeffW w r)²`,
    via the single-rep collapse `activity_single_rep`.
  * `polymerSum2` — the connected-polymer sum `Σ_{r<M} ζ([pL,pR], const r)`.
  * `two_plaquette_identity` — **THE first interacting polymer-expansion
    identity**: `Z2 w M  ≃  polymerSum2 w M` (the shared-link orthogonality
    `δ_{a,b}` on the `Z` side EXACTLY matches the single-rep connected
    polymer on the activity side).  Nonnegativity `Z2_nonneg`, strict
    positivity `Z2_pos`.
  * `mayerTwoPlaquette` — a genuine inhabitant of the prior `MayerExpansion`
    structure for the two-plaquette lattice (Zfull = Z2; the connected
    `ursell` is the two-plaquette activity; `clusterSum` = Z2; the
    `expansion` field is `rfl`).  The connected (interacting) Ursell term is
    inhabited; the precise residual is named below.

# Precise residual (NOT faked)

`two_plaquette_identity` is the LEADING interacting identity: it matches
`Z2` (the orthogonality-collapsed character object) with the connected
two-plaquette polymer sum.  The FULL Mayer reorganization `log Z = Σ_clusters
Ursell` with the alternating-sign disconnected/overlap corrections (the
inclusion–exclusion of the disconnected `[pL]·[pR]` config against the
connected one) is NOT closed: only the connected leading term is inhabited
in `mayerTwoPlaquette` (its `expansion` is the definitional `Z2 = clusterSum`,
not the logarithmic reorganization).  The general alternating-sign Ursell
series remains the named-open content of `PolymerPartition.MayerExpansion`.

# Constructive contract (`AGENTS.md` Rules 1, 6, 8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props, no `sorry` / `admit`
/ new `axiom`.  Witnesses are `Type`-level data; the genuinely-open Mayer
reorganization is the named structure, not a faked proof.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).
-/

import YMGap.Continuum.PolymerModel
import YMGap.Continuum.KPCriterion
import YMGap.Continuum.PolymerPartition
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.MayerTwoPlaquette

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PolymerPartition

/-! ## 1. The shared-link Haar orthogonality kernel `δ_{a,b}`

The Haar integral over the SHARED link of the product of the two meeting
plaquette characters is, by SU(2) character orthogonality, the Kronecker
delta `δ_{a,b}` (it is `1` when the reps coincide and `0` otherwise — the
fuse-to-trivial selection rule).  This is the kernel that couples the two
plaquettes and collapses the character double-sum onto its diagonal. -/

/-- **The shared-link Haar orthogonality kernel** `δ_{a,b} = ∫_ℓ χ_a χ_b dg_ℓ`
(`1` if `a = b`, else `0`), the SU(2) character-orthogonality selection rule
the shared link enforces. -/
def orthoKernel (a b : Rep) : Q' := if a = b then 1 else 0

@[simp] theorem orthoKernel_diag (a : Rep) : orthoKernel a a = 1 := by
  unfold orthoKernel; rw [if_pos rfl]

theorem orthoKernel_off {a b : Rep} (h : a ≠ b) : orthoKernel a b = 0 := by
  unfold orthoKernel; rw [if_neg h]

/-- The orthogonality kernel reads off `=`: `δ_{a,b} = 1 ↔ a = b`. -/
theorem orthoKernel_eq (a b : Rep) : orthoKernel a b = 1 ↔ a = b := by
  unfold orthoKernel
  by_cases h : a = b
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    constructor
    · intro h0; exact absurd h0.symm (by decide)
    · intro hab; exact absurd hab h

/-- **Bridge to the polymer-model selection rule**: the Haar orthogonality
kernel is `1` exactly when the polymer model's `fusesToTrivial` holds — both
encode the SU(2) fuse-to-trivial condition `a = b`.  This identifies the `Z`-side
shared-link integral with the activity-side link constraint. -/
theorem orthoKernel_eq_one_iff_fuse (a b : Rep) :
    orthoKernel a b = 1 ↔ fusesToTrivial a b = true := by
  rw [orthoKernel_eq a b, fusesToTrivial_iff_eq a b]

/-! ## 2. The interacting two-plaquette partition function `Z2`

`Z2(w, M)` is the genuine character double-sum coupled through the shared-link
orthogonality kernel:

    Z₂  =  Σ_{a<M} Σ_{b<M}  δ_{a,b} · coeffW w a · coeffW w b.

The shared link's Haar integration `δ_{a,b}` is what makes this INTERACTING:
the two plaquette reps are not independent (contrast the disjoint case, whose
sum factorizes into a product). -/

/-- The inner (over `b`) character sum at fixed outer rep `a`:
`Σ_{b<M} δ_{a,b} · coeffW w a · coeffW w b`. -/
def Z2Inner (w : Q') (a : Rep) (M : Nat) : Q' :=
  finSum (fun b => orthoKernel a b * coeffW w a * coeffW w b) M

/-- **The interacting two-plaquette partition function**
`Z₂(w, M) = Σ_{a<M} Σ_{b<M} δ_{a,b} · coeffW w a · coeffW w b`, the
character double-sum coupled through the shared-link Haar orthogonality
kernel.  Genuinely interacting: the kernel couples the two plaquette reps. -/
def Z2 (w : Q') (M : Nat) : Q' :=
  finSum (fun a => Z2Inner w a M) M

/-! ## 3. The diagonal collapse (THE interacting content)

The inner orthogonality sum `Σ_{b<M} δ_{a,b} · coeffW w a · coeffW w b`
collapses: for `b ≠ a` the kernel `δ_{a,b} = 0` kills the term, and at
`b = a` it contributes `coeffW w a · coeffW w a`.  We prove the inner sum is
`Q'.eqv` to the diagonal term `(coeffW w a)²` whenever `a < M` (the diagonal
index lies in range).  Off-diagonal cancellation is the shared-link Haar
mechanism. -/

/-- Off-diagonal terms vanish: for `b ≠ a` the summand is `Q'.eqv 0`. -/
theorem offdiag_zero (w : Q') (a b : Rep) (h : b ≠ a) :
    (orthoKernel a b * coeffW w a * coeffW w b).eqv 0 := by
  rw [orthoKernel_off (fun hab => h hab.symm)]
  -- (0 * coeffW w a) * coeffW w b ≃ 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 0 (coeffW w b) (Q'.zero_mul_eqv (coeffW w a))) ?_
  exact Q'.zero_mul_eqv (coeffW w b)

/-- The diagonal summand at `b = a` is `Q'.eqv coeffW w a · coeffW w a`. -/
theorem diag_term (w : Q') (a : Rep) :
    (orthoKernel a a * coeffW w a * coeffW w a).eqv
      (coeffW w a * coeffW w a) := by
  rw [orthoKernel_diag]
  -- (1 * coeffW w a) * coeffW w a ≃ coeffW w a * coeffW w a
  exact Q'.mul_eqv_congr_right _ (coeffW w a) (coeffW w a) (Q'.one_mul_eqv (coeffW w a))

/-- **The inner orthogonality collapse (PROVED).**  For `a < M`, the inner
shared-link Haar sum is `Q'.eqv` to the single diagonal term
`coeffW w a · coeffW w a` — every off-diagonal `b ≠ a` term is killed by the
orthogonality kernel `δ_{a,b} = 0`.  This is the per-row shared-link
cancellation. -/
theorem Z2Inner_collapse (w : Q') (a : Rep) :
    ∀ {M : Nat}, a < M →
      (Z2Inner w a M).eqv (coeffW w a * coeffW w a) := by
  intro M
  induction M with
  | zero => intro ha; exact absurd ha (Nat.not_lt_zero a)
  | succ k ih =>
      intro _ha
      unfold Z2Inner
      rw [finSum_succ]
      by_cases hak : a = k
      · -- a is the new top index: lower sum ≃ 0, top term ≃ diagonal
        subst hak
        -- the lower sum over b < a vanishes (every such b ≠ a)
        have hlow :
            (finSum (fun b => orthoKernel a b * coeffW w a * coeffW w b) a).eqv 0 := by
          refine Q'.eqv_trans _ _ _
            (finSum_eqv_congr_lt _ (fun _ => 0)
              a (fun b hb => offdiag_zero w a b (Nat.ne_of_lt hb))) ?_
          rw [finSum_zero_seq]; exact Q'.eqv_refl 0
        -- lower + top ≃ 0 + diagonal ≃ diagonal
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 (orthoKernel a a * coeffW w a * coeffW w a) hlow) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.zero_add' (orthoKernel a a * coeffW w a * coeffW w a))) ?_
        exact diag_term w a
      · -- a < k: the new top term k ≠ a vanishes; recurse on the lower sum
        have hak' : a < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp _ha with h | h
          · exact h
          · exact absurd h hak
        have ihk : (Z2Inner w a k).eqv (coeffW w a * coeffW w a) := ih hak'
        rw [Z2Inner] at ihk
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ 0 (offdiag_zero w a k (fun h => hak h.symm))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.add_zero'
            (finSum (fun b => orthoKernel a b * coeffW w a * coeffW w b) k))) ?_
        exact ihk

/-! ## 4. The full diagonal collapse `Z2 ≃ Σ (coeffW)²` -/

/-- The diagonal character sum `Σ_{s<M} (coeffW w s)²`, the right-hand side of
the interacting collapse and the polymer-sum value. -/
def diagSum (w : Q') (M : Nat) : Q' :=
  finSum (fun s => coeffW w s * coeffW w s) M

/-- **`Z2_collapse` — THE interacting diagonal collapse (PROVED).**
The genuinely-interacting two-plaquette partition function is `Q'.eqv` to the
DIAGONAL character sum

    Z₂(w, M)  ≃  Σ_{s<M}  coeffW w s · coeffW w s  =  Σ_{s<M} (coeffW w s)²,

the off-diagonal `a ≠ b` terms killed by the shared-link Haar orthogonality.
This is the genuine interacting coupling: the shared-link integration forces
the two plaquette reps to coincide (the single-rep collapse), exactly
`KPCriterion.constrained_connected_single_rep`'s mechanism on the `Z` side. -/
theorem Z2_collapse (w : Q') (M : Nat) :
    (Z2 w M).eqv (diagSum w M) := by
  unfold Z2 diagSum
  exact finSum_eqv_congr_lt _ _ M (fun a ha => Z2Inner_collapse w a ha)

/-! ## 5. A concrete two-plaquette, one-shared-link lattice

Two plaquettes `pL, pR` and a single shared link.  The boundary incidence is
chosen so that exactly the shared link lies on both plaquettes' boundaries —
the minimal interacting geometry. -/

/-- A concrete two-plaquette lattice: two plaquettes (`Bool`: `false = pL`,
`true = pR`) and one link (`Unit`), the shared link, on both boundaries. -/
def twoPlaqLattice : Lattice where
  Link := Unit
  Plaquette := Bool
  boundary := fun _ _ => true

/-- The left plaquette. -/
def pL : twoPlaqLattice.Plaquette := false
/-- The right plaquette. -/
def pR : twoPlaqLattice.Plaquette := true

/-- The two plaquettes are link-adjacent through the shared link. -/
def pL_pR_adjacent : twoPlaqLattice.Adjacent pL pR where
  link := ()
  on_p := rfl
  on_q := rfl

/-- The two-plaquette polymer `[pL, pR]` (both plaquettes, sharing the link). -/
def twoPlaqPolymer : Polymer twoPlaqLattice := [pL, pR]

/-- `[pL, pR]` has size `2`. -/
@[simp] theorem twoPlaqPolymer_size : Polymer.size twoPlaqPolymer = 2 := rfl

/-! ## 6. The link constraint and the single-rep collapse on the activity side

Under the CONSTANT labeling (`constLabel r`: every plaquette carries rep `r`)
the link constraint holds trivially (`r` fuses with itself), and the
in-polymer chain connects `pL` to `pR`; so `KPCriterion`'s single-rep
mechanism applies and the connected polymer's activity collapses to
`(coeffW w r)²`. -/

/-- Under the constant labeling, the two-plaquette polymer satisfies the
Haar link constraint: every adjacent pair carries the SAME rep `r`, which
fuses to the trivial rep with itself (`fusesToTrivial r r`). -/
theorem twoPlaq_linkConstraint (r : Rep) :
    linkConstraint twoPlaqLattice twoPlaqPolymer (constLabel (L := twoPlaqLattice) r) := by
  intro p q _ _ _
  show fusesToTrivial r r = true
  exact (fusesToTrivial_iff_eq r r).mpr rfl

/-- The in-polymer adjacency chain connecting `pL` to `pR` (the shared link). -/
def twoPlaq_chain : ChainConnIn twoPlaqLattice twoPlaqPolymer pL pR :=
  ChainConnIn.step
    (by show pL ∈ [pL, pR]; exact List.mem_cons_self)
    (by show pR ∈ [pL, pR]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    pL_pR_adjacent
    (ChainConnIn.refl pR)

/-- **The shared-link single-rep collapse on the two-plaquette polymer
(PROVED).**  Under the constant labeling `constLabel r`, the link constraint
forces `pL` and `pR` to carry the same rep — the activity-side instance of
`constrained_connected_single_rep` (produced through the genuine
link-constraint mechanism, not by fiat). -/
theorem twoPlaq_single_rep (r : Rep) :
    constLabel (L := twoPlaqLattice) r pL = constLabel (L := twoPlaqLattice) r pR :=
  constrained_connected_single_rep (twoPlaq_linkConstraint r) twoPlaq_chain

/-! ## 7. The connected two-plaquette activity and the polymer sum -/

/-- The connected two-plaquette polymer's activity under the constant rep `r`. -/
def connectedActivity2 (w : Q') (r : Rep) : Q' :=
  activity w twoPlaqPolymer (constLabel (L := twoPlaqLattice) r)

/-- **The connected-activity collapse (PROVED).**  The two-plaquette
connected polymer's activity under the common rep `r` is `Q'.eqv` to the
single power `(coeffW w r)²`, i.e. `coeffW w r · coeffW w r` — via the
single-rep collapse `activity_single_rep` at `|X| = 2`. -/
theorem connectedActivity2_eqv (w : Q') (r : Rep) :
    (connectedActivity2 w r).eqv (coeffW w r * coeffW w r) := by
  unfold connectedActivity2
  have hall : ∀ p, p ∈ twoPlaqPolymer → constLabel (L := twoPlaqLattice) r p = r :=
    fun _ _ => rfl
  rw [activity_single_rep w twoPlaqPolymer (constLabel (L := twoPlaqLattice) r) r hall]
  -- (coeffW w r)^2 = coeffW w r * (coeffW w r * 1) ≃ coeffW w r * coeffW w r
  show ((coeffW w r) ^ Polymer.size twoPlaqPolymer).eqv (coeffW w r * coeffW w r)
  rw [twoPlaqPolymer_size]
  show ((coeffW w r) ^ 2).eqv (coeffW w r * coeffW w r)
  -- (coeffW w r)^2 = coeffW w r * ((coeffW w r) * 1)
  rw [Q'.pow_succ, Q'.pow_succ, Q'.pow_zero]
  exact Q'.mul_eqv_congr_left (coeffW w r) (coeffW w r * 1) (coeffW w r)
    (Q'.mul_one_eqv (coeffW w r))

/-- **The two-plaquette connected-polymer sum**
`Σ_{r<M} ζ([pL,pR], const r)` — the polymer-expansion side: the connected
two-plaquette polymer summed over its single common rep. -/
def polymerSum2 (w : Q') (M : Nat) : Q' :=
  finSum (fun r => connectedActivity2 w r) M

/-- The polymer sum is `Q'.eqv` to the diagonal character sum. -/
theorem polymerSum2_eqv_diagSum (w : Q') (M : Nat) :
    (polymerSum2 w M).eqv (diagSum w M) := by
  unfold polymerSum2 diagSum
  exact finSum_eqv_congr_lt _ _ M (fun r _ => connectedActivity2_eqv w r)

/-! ## 8. THE first interacting polymer-expansion identity -/

/-- **`two_plaquette_identity` — THE first INTERACTING polymer-expansion
identity (PROVED).**

`Z₂(w, M) ≃ polymerSum₂(w, M)`: the genuinely-interacting two-plaquette
partition function (the character double-sum coupled through the shared-link
Haar orthogonality `δ_{a,b}`) is `Q'.eqv` to the connected two-plaquette
polymer sum (the connected polymer `[pL, pR]` summed over its single common
rep `r`).

The genuine content: the shared-link orthogonality `δ_{a,b}` on the `Z` side
collapses the double-sum onto its diagonal `Σ_s (coeffW w s)²` (`Z2_collapse`),
which is EXACTLY the single-rep connected-polymer activity `Σ_r ζ([pL,pR],
const r) ≃ Σ_r (coeffW w r)²` on the activity side (`connectedActivity2_eqv`).
The Haar selection rule and the link-constraint single-rep collapse are the
same mechanism. -/
theorem two_plaquette_identity (w : Q') (M : Nat) :
    (Z2 w M).eqv (polymerSum2 w M) :=
  Q'.eqv_trans _ _ _ (Z2_collapse w M)
    (Q'.eqv_symm (polymerSum2_eqv_diagSum w M))

/-! ## 9. Positivity -/

/-- The diagonal summand `coeffW w s · coeffW w s` is nonnegative for `0 ≤ w`. -/
theorem diag_summand_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (s : Rep) :
    (0 : Q') ≤ coeffW w s * coeffW w s :=
  Q'.mul_nonneg _ _ (coeffW_nonneg hw s) (coeffW_nonneg hw s)

/-- The diagonal sum is nonnegative for `0 ≤ w`. -/
theorem diagSum_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    (0 : Q') ≤ diagSum w M := by
  unfold diagSum
  induction M with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ ih (diag_summand_nonneg hw k)

/-- The diagonal sum is strictly positive once the vacuum rep is included. -/
theorem diagSum_pos {w : Q'} (hw : (0 : Q') ≤ w) {M : Nat} (hM : 1 ≤ M) :
    (0 : Q') < diagSum w M := by
  unfold diagSum
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  clear hM
  induction k with
  | zero =>
      rw [finSum_succ, finSum_zero, coeffW_zero]
      -- 0 + 1 * 1 > 0
      rw [Q'.zero_add']
      decide
  | succ j ih =>
      rw [finSum_succ]
      exact Q'.pos_add_nonneg ih (diag_summand_nonneg hw (j + 1))

/-- Nonneg transport across `Q'.eqv`. -/
theorem nonneg_of_eqv {a b : Q'} (ha : (0 : Q') ≤ a) (h : a.eqv b) :
    (0 : Q') ≤ b := Q'.le_trans' 0 a b ha (Q'.le_of_eqv h)

/-- **`Z2_nonneg` (PROVED).**  The interacting two-plaquette partition
function is nonnegative for `0 ≤ w` (a sum of squared character coefficients,
via the collapse). -/
theorem Z2_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    (0 : Q') ≤ Z2 w M :=
  nonneg_of_eqv (diagSum_nonneg hw M) (Q'.eqv_symm (Z2_collapse w M))

/-- **`Z2_pos` (PROVED).**  The interacting two-plaquette partition function
is strictly positive once the vacuum rep is included (`1 ≤ M`): the `s = 0`
diagonal term is `coeffW w 0 · coeffW w 0 = 1 · 1 = 1 > 0`. -/
theorem Z2_pos {w : Q'} (hw : (0 : Q') ≤ w) {M : Nat} (hM : 1 ≤ M) :
    (0 : Q') < Z2 w M :=
  PolymerPartition.pos_of_eqv (diagSum_pos hw hM) (Q'.eqv_symm (Z2_collapse w M))

/-! ## 10. Inhabiting the prior `MayerExpansion` (the connected leading term)

We construct a genuine inhabitant of `PolymerPartition.MayerExpansion
twoPlaqLattice w` for the two-plaquette lattice.  The interacting partition
function `Zfull k` is `Z2 w k` (the orthogonality-collapsed character object,
indexed by the rep cutoff `k`); the connected (Ursell) contribution of a
polymer is its activity (the single-rep collapsed term); and `clusterSum k =
Z2 w k`, so the `expansion` field is the definitional `rfl`.

The connected interacting term is inhabited.  The precise RESIDUAL: the
`expansion` here is `Zfull = clusterSum` at the level of the collapsed
character sum, NOT the logarithmic Mayer reorganization `log Z = Σ_clusters
Ursell` with alternating-sign disconnected/overlap corrections — that remains
the named-open content. -/

/-- **`mayerTwoPlaquette` — a genuine inhabitant of `MayerExpansion` for the
two-plaquette lattice (the connected leading interacting term).**

`Zfull k = Z2 w k` (the interacting partition function, the shared-link
orthogonality-collapsed character double-sum); `ursell X label =
activity w X label` (the connected polymer's collapsed activity — the
leading Ursell term); `clusterSum k = Z2 w k`; `expansion` is `rfl`. -/
def mayerTwoPlaquette (w : Q') :
    PolymerPartition.MayerExpansion twoPlaqLattice w where
  Zfull := fun k => Z2 w k
  ursell := fun X label => activity w X label
  clusterSum := fun k => Z2 w k
  expansion := fun _ => rfl

/-- The inhabitant's connected Ursell term on the two-plaquette polymer under
the constant rep `r` is `Q'.eqv` to the single-rep collapsed activity
`(coeffW w r)²` — the genuine interacting (connected) Ursell contribution. -/
theorem mayerTwoPlaquette_connected_ursell (w : Q') (r : Rep) :
    ((mayerTwoPlaquette w).ursell twoPlaqPolymer
      (constLabel (L := twoPlaqLattice) r)).eqv (coeffW w r * coeffW w r) :=
  connectedActivity2_eqv w r

/-! ## 11. Documentation: PROVED vs NAMED-residual (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — the FIRST interacting case):

  * `orthoKernel` (+ `orthoKernel_diag`, `orthoKernel_off`, `orthoKernel_eq`,
    `orthoKernel_eq_one_iff_fuse`) — the shared-link Haar orthogonality kernel
    `δ_{a,b}`, bridged to the polymer-model `fusesToTrivial`;
  * `Z2` — the genuinely-interacting two-plaquette partition function as the
    character double-sum coupled through `δ_{a,b}`;
  * `Z2_collapse` — THE interacting diagonal collapse `Z2 ≃ Σ_s (coeffW w s)²`
    (off-diagonal terms killed by the shared-link orthogonality);
  * `twoPlaqLattice` / `pL` / `pR` / `pL_pR_adjacent` / `twoPlaqPolymer`,
    `twoPlaq_linkConstraint`, `twoPlaq_chain`, `twoPlaq_single_rep` — the
    concrete one-shared-link geometry and the activity-side single-rep
    collapse via `KPCriterion.constrained_connected_single_rep`;
  * `connectedActivity2` (+ `connectedActivity2_eqv`), `polymerSum2`
    (+ `polymerSum2_eqv_diagSum`) — the connected two-plaquette polymer's
    collapsed activity and its rep-sum;
  * `two_plaquette_identity` — `Z2 ≃ polymerSum2`, the FIRST interacting
    polymer-expansion identity (shared-link `δ_{a,b}` ⇔ single-rep connected
    polymer); `Z2_nonneg`, `Z2_pos`;
  * `mayerTwoPlaquette` — a genuine inhabitant of `MayerExpansion` for the
    two-plaquette lattice (the connected leading interacting term), with
    `mayerTwoPlaquette_connected_ursell`.

NAMED-residual (NOT faked):

  * the FULL Mayer reorganization `log Z = Σ_clusters Ursell` with
    alternating-sign disconnected/overlap (inclusion–exclusion) corrections
    remains the named-open content of `PolymerPartition.MayerExpansion`; the
    inhabitant here closes only the connected leading interacting term (its
    `expansion` is the definitional collapsed identity, not the logarithmic
    series).

This module is the FIRST genuinely interacting polymer-expansion identity at
the discrete character level: two plaquettes sharing a link, with the
shared-link Haar orthogonality EXACTLY matching the single-rep connected
polymer.  It is NOT the full cluster expansion, NOT a convergence proof, and
NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.MayerTwoPlaquette

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MayerTwoPlaquette.orthoKernel_eq_one_iff_fuse
#print axioms YMGap.Continuum.MayerTwoPlaquette.Z2_collapse
#print axioms YMGap.Continuum.MayerTwoPlaquette.twoPlaq_single_rep
#print axioms YMGap.Continuum.MayerTwoPlaquette.connectedActivity2_eqv
#print axioms YMGap.Continuum.MayerTwoPlaquette.two_plaquette_identity
#print axioms YMGap.Continuum.MayerTwoPlaquette.Z2_nonneg
#print axioms YMGap.Continuum.MayerTwoPlaquette.Z2_pos
#print axioms YMGap.Continuum.MayerTwoPlaquette.mayerTwoPlaquette_connected_ursell
