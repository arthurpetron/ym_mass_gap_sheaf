/-
The **beyond-tree partition identity**: the single-link `m`-fold STAR folds
(no 6j), and the genuine residual is the closed-fusion-loop 6j / Biedenharn–
Elliott datum — Wall-2 Phase B, sharpening `LoopyLinkIntegral`.

# What this module delivers (honest, tiered scope)

`LoopyLinkIntegral` proved the `m = 2` (orthogonality `δ_{a,b}`) and `m = 3`
(triple-character `∫χ_aχ_bχ_c = N_{abc}`) shared-link key facts and built the
`loopyRealPartition` reduction STRUCTURE.  This module answers the sharper
question — *where does the abstract↔real identity actually break past two
shared links?* — with a precise reduction + refutation:

## D1 (PROVED, axiom-clean): the single ≥3-STAR folds, NO 6j

A link shared by `m` plaquettes carrying reps `r₀,…,r_{m-1}` gives the Haar
integral `L_m(r) = ∫_{SU(2)} ∏_i χ_{r_i} dg`.  We realize it constructively as
the **caterpillar fold** `nFoldFuse`: the coefficient of `χ_c` in the product
`∏ χ_{r_i}`, built by *one trivalent Clebsch–Gordan vertex per added
plaquette*:

    nFoldFuse D []       c  =  δ_{c,0}                         (= orthoKernel c 0)
    nFoldFuse D (r::rs)  c  =  Σ_{d<D} nFoldFuse D rs d · N_{d,r}^c

and `nFoldCharInt D rs = nFoldFuse D rs 0` (project onto the trivial channel,
`∫χ_c = δ_{c,0}`).  Each step is a SINGLE finite fusion sum — a trivalent
vertex — so the whole `m`-fold star is a *caterpillar tree of trivalent
vertices*: **NO 6j appears**.  We PROVE the corners:

  * `nFoldCharInt_nil`   : `∫ 1 = 1`;
  * `nFoldCharInt_single`: `∫χ_a = δ_{a,0}`;
  * `nFoldCharInt_two`   : `∫χ_aχ_b = δ_{a,b}` (= `MayerTwoPlaquette.orthoKernel`);
  * `nFoldCharInt_three` : `∫χ_aχ_bχ_c = N_{cba}` (= `LoopyLinkIntegral.tripleCharInt`),

each by the same `finSum_delta_left` orthogonality collapse (the character
orthogonality `∫χ_dχ_c = δ_{d,c}` re-used at every vertex).  This DISCHARGES
the "star = 6j" mislabel: a single ≥3-shared link folds by iterated
Clebsch–Gordan + orthogonality, with no recoupling coefficient.

## D2 (NAMED residual): the closed-fusion-loop 6j / Biedenharn–Elliott datum

The genuine obstruction is NOT the star but the *closed loop of fusion
channels* (the tetrahedron `{j₁…j₆}`).  Its defining datum is the SU(2) 6j /
Racah recoupling coefficient: the change of coupling basis between two channel
trees of four reps.  We name it `SixJRecoupling` (a `Q'`-kernel over `Fin 6 →
Rep`, nonnegativity, and the `biedenharn_elliott` Racah recoupling identity),
and prove the constraint is **non-vacuous** (`sixj ≡ 0` FAILS it,
`sixj_zero_fails`), so it is NOT trivially inhabitable.  The beyond-tree
identity `BeyondTreePartitionIdentity` bundles this 6j datum with the
abstract↔real identity — its projection to `AbstractRealPartitionIdentity` is
supplied, and it is LEFT UNINHABITED (the 6j is the frontier).

## Honest refutation + structural caveat (the sharpest points)

  * **Option (A) — "extend tree → single loop" is a NON-target.**
    `loopyLike_two_iff_treeLike` (imported): `LoopyLike 2 = TreeLike` is a
    *≤2-shared-link* bound, NOT acyclicity; a single plaquette cycle already
    satisfies it and re-pins via `δ_{r,r}=1` (proved on the correlator side in
    `CycleMayer.cycleG_collapse`).  Nothing there is the wall.  We re-expose
    this as `single_loop_is_treeLike`.
  * **`AbstractRealPartitionIdentity` is under-specified.**  Its `Zreal` is a
    free function pinned only by `Ξ ≃ Zreal`, so it is TRIVIALLY inhabitable
    (`trivialAbstractRealIdentity`, `Zreal := Ξ`).  It does not by itself
    enforce the ≥3-link Haar content.  `SixJRecoupling`, by contrast, IS a
    genuine constraint (`sixj_zero_fails`) — that is where the real content
    lives.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `List` / `Fin` core only.  No `Classical.*`, no
`Real`, no `native_decide` (only `decide`/`omega` on decidable `Nat`/`Q'`
facts).  No `sorry` / `admit` / new `axiom`.  All witnesses are `Type`-level
data; the 6j / Biedenharn–Elliott datum is a NAMED obligation, never faked.
Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.LoopyLinkIntegral

namespace YMGap.Continuum.PartitionBeyondTree

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.MayerTwoPlaquette
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.TreePartitionIdentity
open YMGap.Continuum.LoopyLinkIntegral

variable {L : Lattice}

/-! ## 0. Small reusable helpers (`finSum` δ-collapse, `orthoKernel` facts) -/

/-- `finSum` of a nonnegative sequence is nonnegative (`RationalTail.finSum`). -/
theorem finSum_nonneg_local {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ (finSum_nonneg_local hf n) (hf n)

/-- The orthogonality kernel is symmetric: `δ_{a,b} = δ_{b,a}`. -/
theorem orthoKernel_symm (a b : Rep) : orthoKernel a b = orthoKernel b a := by
  unfold orthoKernel
  by_cases h : a = b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

/-- The orthogonality kernel is nonnegative (`0` or `1`). -/
theorem orthoKernel_nonneg (a b : Rep) : (0 : Q') ≤ orthoKernel a b := by
  unfold orthoKernel
  by_cases h : a = b
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

/-- **The generic Kronecker-δ finite-sum collapse.**  If `ind` is a Kronecker
delta at `e` (`ind d ≃ 0` off `e`, `ind e ≃ 1`), then the coupled sum
`Σ_{d<D} ind d · g d` collapses to the single diagonal `g e` whenever `e < D`.
This is the SU(2) character-orthogonality mechanism (`∫χ_dχ_c = δ_{d,c}`)
factored out once; every fold vertex below re-uses it.  Mirrors
`MayerTwoPlaquette.Z2Inner_collapse` / `LoopyLinkIntegral.tripleFusionSum_collapse`. -/
theorem finSum_delta_left (ind g : Nat → Q') (e : Nat)
    (hoff : ∀ d, d ≠ e → (ind d).eqv 0) (hdiag : (ind e).eqv 1) :
    ∀ {D : Nat}, e < D → (finSum (fun d => ind d * g d) D).eqv (g e) := by
  intro D
  induction D with
  | zero => intro he; exact absurd he (Nat.not_lt_zero e)
  | succ k ih =>
      intro he
      rw [finSum_succ]
      by_cases hek : e = k
      · subst hek
        have hlow : (finSum (fun d => ind d * g d) e).eqv 0 := by
          refine Q'.eqv_trans _ _ _
            (finSum_eqv_congr_lt _ (fun _ => 0) e (fun d hd => ?_)) ?_
          · exact Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right (ind d) 0 (g d) (hoff d (Nat.ne_of_lt hd)))
              (Q'.zero_mul_eqv (g d))
          · rw [finSum_zero_seq]; exact Q'.eqv_refl 0
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 (ind e * g e) hlow) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.zero_add' (ind e * g e))) ?_
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (ind e) 1 (g e) hdiag) (Q'.one_mul_eqv (g e))
      · have hek' : e < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp he with h | h
          · exact h
          · exact absurd h hek
        have ihk := ih hek'
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ 0
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right (ind k) 0 (g k) (hoff k (fun h => hek h.symm)))
              (Q'.zero_mul_eqv (g k)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.add_zero' (finSum (fun d => ind d * g d) k))) ?_
        exact ihk

/-! ## 1. The `fusionOK` triangle characterization + the degenerate `fusionInd`
values (bridge to `orthoKernel`). -/

/-- The SU(2) fusion predicate as an explicit triangle+parity conjunction. -/
theorem fusionOK_iff (a b s : Nat) :
    fusionOK a b s = true ↔
      (Nat.max a b - Nat.min a b ≤ s ∧ s ≤ a + b ∧ (a + b + s) % 2 = 0) := by
  unfold fusionOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- **Degenerate corner (first slot trivial):** `N_{0,b,c} = δ_{b,c}`, i.e.
`fusionInd 0 b c = orthoKernel b c`.  (`χ_0·χ_b = χ_b`, so `χ_c` occurs iff
`c = b`.)  This is the m=1 orthogonality that closes the caterpillar's first
vertex. -/
theorem fusionInd_zero_left (b c : Rep) : fusionInd 0 b c = orthoKernel b c := by
  unfold fusionInd orthoKernel
  have hmax : Nat.max 0 b = b := Nat.zero_max b
  have hmin : Nat.min 0 b = 0 := Nat.zero_min b
  by_cases h : b = c
  · subst h
    have hok : fusionOK 0 b b = true :=
      (fusionOK_iff 0 b b).mpr (by rw [hmax, hmin]; refine ⟨?_, ?_, ?_⟩ <;> omega)
    rw [if_pos hok, if_pos rfl]
  · have hno : ¬ fusionOK 0 b c = true := by
      rw [fusionOK_iff, hmax, hmin]
      rintro ⟨h1, h2, _⟩
      rw [Nat.sub_zero] at h1
      rw [Nat.zero_add] at h2
      exact h (Nat.le_antisymm h1 h2)
    rw [if_neg hno, if_neg h]

/-- **Degenerate corner (third slot trivial):** `N_{a,b,0} = δ_{a,b}`, i.e.
`fusionInd a b 0 = orthoKernel a b` — the fuse-to-trivial selection rule
`χ_0 ∈ χ_a·χ_b ⇔ a = b`, exactly `PolymerModel.fusesToTrivial`.  This is the
final "integrate to the trivial channel" vertex of the caterpillar. -/
theorem fusionInd_fuse_zero (a b : Rep) : fusionInd a b 0 = orthoKernel a b := by
  unfold fusionInd orthoKernel
  by_cases h : a = b
  · subst h
    have hok : fusionOK a a 0 = true := (fusesToTrivial_iff_eq a a).mpr rfl
    rw [if_pos hok, if_pos rfl]
  · have hno : ¬ fusionOK a b 0 = true := fun hc => h ((fusesToTrivial_iff_eq a b).mp hc)
    rw [if_neg hno, if_neg h]

/-! ## 2. The caterpillar fold `nFoldFuse` — the `m`-fold single-link star (D1)

`nFoldFuse D rs c` is the coefficient of `χ_c` in the product `∏_{r∈rs} χ_r`,
built one trivalent Clebsch–Gordan vertex per plaquette.  The `m`-fold star
Haar integral is its projection onto the trivial channel,
`nFoldCharInt D rs = nFoldFuse D rs 0` (using `∫χ_c = δ_{c,0}`).  The cutoff
`D` is the honest finite-support truncation. -/

/-- **The caterpillar (single-link `m`-fold star) fold.**  One finite fusion
sum per added plaquette — a trivalent vertex — so the whole star is an acyclic
caterpillar of trivalent vertices: NO 6j. -/
def nFoldFuse (D : Nat) : List Rep → Rep → Q'
  | [], c => orthoKernel c 0
  | r :: rs, c => finSum (fun d => nFoldFuse D rs d * fusionInd d r c) D

/-- **The `m`-fold single-link star Haar integral** `∫_{SU(2)} ∏_{r∈rs} χ_r`,
as the trivial-channel coefficient of the caterpillar fold. -/
def nFoldCharInt (D : Nat) (rs : List Rep) : Q' := nFoldFuse D rs 0

/-- **The caterpillar recursion (structural).**  Each added plaquette contracts
through EXACTLY ONE trivalent fusion vertex `Σ_d (·) · N_{d,r}^c` — the manifest
"no 6j" content: a single ≥`m`-star is an acyclic tree of trivalent vertices. -/
theorem nFoldFuse_cons (D : Nat) (r : Rep) (rs : List Rep) (c : Rep) :
    nFoldFuse D (r :: rs) c
      = finSum (fun d => nFoldFuse D rs d * fusionInd d r c) D := rfl

/-- The fold is nonnegative (a nested sum of products of nonnegative
`orthoKernel` / `fusionInd` values). -/
theorem nFoldFuse_nonneg (D : Nat) : ∀ (rs : List Rep) (c : Rep),
    (0 : Q') ≤ nFoldFuse D rs c := by
  intro rs
  induction rs with
  | nil => intro c; exact orthoKernel_nonneg c 0
  | cons r rs ih =>
      intro c
      show (0 : Q') ≤ finSum (fun d => nFoldFuse D rs d * fusionInd d r c) D
      exact finSum_nonneg_local
        (fun d => Q'.mul_nonneg _ _ (ih d) (fusionInd_nonneg d r c)) D

/-- The `m`-fold star integral is nonnegative. -/
theorem nFoldCharInt_nonneg (D : Nat) (rs : List Rep) :
    (0 : Q') ≤ nFoldCharInt D rs := nFoldFuse_nonneg D rs 0

/-! ## 3. The proved corners `m = 0, 1, 2, 3` -/

/-- **`m = 0`:** `∫ 1 = 1` (the empty product). -/
theorem nFoldCharInt_nil (D : Nat) : nFoldCharInt D [] = 1 := by
  show orthoKernel 0 0 = 1
  exact orthoKernel_diag 0

/-- **`m = 1` (the single-character integral):** the coefficient of `χ_c` in
`χ_b` is `δ_{b,c}` — `nFoldFuse D [b] c ≃ δ_{b,c}` (for `0 < D`), via the first
orthogonality vertex `Σ_x δ_{x,0}·N_{x,b}^c = N_{0,b,c} = δ_{b,c}`. -/
theorem nFoldFuse_single {D : Nat} (hD : 0 < D) (b c : Rep) :
    (nFoldFuse D [b] c).eqv (orthoKernel b c) := by
  have h1 : (nFoldFuse D [b] c).eqv (fusionInd 0 b c) := by
    show (finSum (fun x => nFoldFuse D [] x * fusionInd x b c) D).eqv (fusionInd 0 b c)
    exact finSum_delta_left (fun x => nFoldFuse D [] x) (fun x => fusionInd x b c) 0
      (fun d hd => Q'.eqv_of_eq (show nFoldFuse D [] d = 0 from orthoKernel_off hd))
      (Q'.eqv_of_eq (show nFoldFuse D [] 0 = 1 from orthoKernel_diag 0)) hD
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_of_eq (fusionInd_zero_left b c))

/-- **`m = 1`:** `∫χ_b = δ_{b,0}`. -/
theorem nFoldCharInt_single {D : Nat} (hD : 0 < D) (b : Rep) :
    (nFoldCharInt D [b]).eqv (orthoKernel b 0) := nFoldFuse_single hD b 0

/-- **`m = 2` (fold value):** the coefficient of `χ_c` in `χ_a·χ_b` is
`N_{b,a,c}` — `nFoldFuse D [a,b] c ≃ fusionInd b a c` (for `0 < D`, `b < D`).
Two vertices: the inner one gives `δ_{b,x}`, the outer contracts to
`N_{b,a,c}`. -/
theorem nFoldFuse_pair {D : Nat} (hD : 0 < D) (a b c : Rep) (hb : b < D) :
    (nFoldFuse D [a, b] c).eqv (fusionInd b a c) := by
  have hcongr : (finSum (fun x => nFoldFuse D [b] x * fusionInd x a c) D).eqv
      (finSum (fun x => orthoKernel b x * fusionInd x a c) D) :=
    finSum_eqv_congr_lt _ _ D (fun x _ =>
      Q'.mul_eqv_congr_right (nFoldFuse D [b] x) (orthoKernel b x) (fusionInd x a c)
        (nFoldFuse_single hD b x))
  have hcoll : (finSum (fun x => orthoKernel b x * fusionInd x a c) D).eqv
      (fusionInd b a c) :=
    finSum_delta_left (fun x => orthoKernel b x) (fun x => fusionInd x a c) b
      (fun d hd => Q'.eqv_of_eq (orthoKernel_off (fun h => hd h.symm)))
      (Q'.eqv_of_eq (orthoKernel_diag b)) hb
  show (finSum (fun x => nFoldFuse D [b] x * fusionInd x a c) D).eqv (fusionInd b a c)
  exact Q'.eqv_trans _ _ _ hcongr hcoll

/-- **`m = 2` (the two-character integral):** `∫χ_aχ_b = δ_{a,b}`, matching
`MayerTwoPlaquette.orthoKernel`.  Folds from the fold value `N_{b,a,0} = δ_{b,a}
= δ_{a,b}` — the proved 2-fold orthogonality, no 6j. -/
theorem nFoldCharInt_two {D : Nat} (hD : 0 < D) (a b : Rep) (hb : b < D) :
    (nFoldCharInt D [a, b]).eqv (orthoKernel a b) := by
  show (nFoldFuse D [a, b] 0).eqv (orthoKernel a b)
  refine Q'.eqv_trans _ _ _ (nFoldFuse_pair hD a b 0 hb) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (fusionInd_fuse_zero b a))
    (Q'.eqv_of_eq (orthoKernel_symm b a))

/-- **`m = 3` (the triple-character integral):** `∫χ_aχ_bχ_c = N_{cba}`,
matching `LoopyLinkIntegral.tripleCharInt c b a` (the single-6j key fact,
`= fusionInd c b a`).  Three trivalent vertices, each closed by the same
orthogonality collapse — the caterpillar terminates, NO closed loop, NO 6j.
(The value is `N_{cba}`; since the SU(2) fusion multiplicity is permutation-
symmetric, this is the genuine `∫χ_aχ_bχ_c`.) -/
theorem nFoldCharInt_three {D : Nat} (hD : 0 < D) (a b c : Rep)
    (hc : c < D) (ha : a < D) :
    (nFoldCharInt D [a, b, c]).eqv (tripleCharInt c b a) := by
  have hstart : nFoldFuse D [a, b, c] 0
      = finSum (fun x => nFoldFuse D [b, c] x * fusionInd x a 0) D := rfl
  have hcongr : (finSum (fun x => nFoldFuse D [b, c] x * fusionInd x a 0) D).eqv
      (finSum (fun x => fusionInd c b x * fusionInd x a 0) D) :=
    finSum_eqv_congr_lt _ _ D (fun x _ =>
      Q'.mul_eqv_congr_right (nFoldFuse D [b, c] x) (fusionInd c b x) (fusionInd x a 0)
        (nFoldFuse_pair hD b c x hc))
  have hcongr2 : (finSum (fun x => fusionInd c b x * fusionInd x a 0) D).eqv
      (finSum (fun x => orthoKernel x a * fusionInd c b x) D) :=
    finSum_eqv_congr_lt _ _ D (fun x _ =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (fusionInd c b x) (fusionInd x a 0) (orthoKernel x a)
          (Q'.eqv_of_eq (fusionInd_fuse_zero x a)))
        (Q'.mul_comm_eqv (fusionInd c b x) (orthoKernel x a)))
  have hcoll : (finSum (fun x => orthoKernel x a * fusionInd c b x) D).eqv
      (fusionInd c b a) :=
    finSum_delta_left (fun x => orthoKernel x a) (fun x => fusionInd c b x) a
      (fun d hd => Q'.eqv_of_eq (orthoKernel_off hd))
      (Q'.eqv_of_eq (orthoKernel_diag a)) ha
  show (nFoldFuse D [a, b, c] 0).eqv (tripleCharInt c b a)
  rw [hstart]
  exact Q'.eqv_trans _ _ _ hcongr (Q'.eqv_trans _ _ _ hcongr2 hcoll)

/-! ## 4. The genuine residual: the closed-fusion-loop 6j / Biedenharn–Elliott
datum (D2). -/

/-- Assemble a `Fin 6 → Rep` tetrahedron label from six reps (total, no
`Classical`).  Slots: `0↦a 1↦b 2↦c 3↦d 4↦e 5↦f`. -/
def mk6 (a b c d e f : Rep) : Fin 6 → Rep := fun i =>
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c
  else if i.val = 3 then d else if i.val = 4 then e else f

/-- **`SixJRecoupling` — the closed-fusion-loop 6j / Racah datum (NAMED
frontier).**

The genuine content past two shared links is NOT the star (D1 folds it) but the
*closed loop of fusion channels* — the Ponzano–Regge tetrahedron.  Its datum is
the SU(2) 6j coefficient, carried here as a `Q'`-kernel over `Fin 6 → Rep`
with:

  * `nonneg` — the (normalized, dim-absorbed) 6j is nonnegative;
  * `biedenharn_elliott` — the **Racah recoupling identity**: each left-coupled
    caterpillar term (four reps `a,b,c,d` coupled through the left channel `e`)
    re-expands over the right-coupling channels `f`, weighted by the 6j
    `{a b e; c d f}`:

        N_{a,b}^e · N_{e,c}^d  ≃  Σ_{f<D} sixj{a,b,c,d,e,f} · (N_{b,c}^f · N_{a,f}^d).

This is the DEFINING change-of-coupling-basis property of the 6j — the pentagon
/ Biedenharn–Elliott content, and precisely the datum absent from the scalar
activity.  It is a genuine constraint (`sixj_zero_fails`), left UNINHABITED:
this is the irreducible `m ≥ 4` frontier. -/
structure SixJRecoupling where
  /-- The 6j / Racah recoupling coefficient `{a b e; c d f}`. -/
  sixj : (Fin 6 → Rep) → Q'
  /-- The (dim-absorbed) 6j is nonnegative. -/
  nonneg : ∀ j, (0 : Q') ≤ sixj j
  /-- **The Biedenharn–Elliott / Racah recoupling identity** — the closed-loop
  change of coupling basis for four reps.  The lone open content. -/
  biedenharn_elliott : ∀ (D : Nat) (a b c d e : Rep),
    (fusionInd a b e * fusionInd e c d).eqv
      (finSum (fun f => sixj (mk6 a b c d e f) * (fusionInd b c f * fusionInd a f d)) D)

/-- **The 6j constraint is NON-VACUOUS** (so `SixJRecoupling` is NOT trivially
inhabitable).  The all-zero recoupling `sixj ≡ 0` FAILS `biedenharn_elliott`:
at `a=b=c=d=e=0` the left side is `N_{0,0}^0·N_{0,0}^0 = 1·1 = 1`, but with
`sixj ≡ 0` the right side is a sum of `0·(·) ≃ 0`, and `1 ≄ 0`.  Hence the
frontier datum carries real content — it is not the empty obligation. -/
theorem sixj_zero_fails :
    ¬ (∀ (D : Nat) (a b c d e : Rep),
        (fusionInd a b e * fusionInd e c d).eqv
          (finSum (fun f => (0 : Q') * (fusionInd b c f * fusionInd a f d)) D)) := by
  intro h
  -- Left side at all-zero: fusionInd 0 0 0 * fusionInd 0 0 0 = 1 * 1
  have hleft : (fusionInd 0 0 0 * fusionInd 0 0 0) = (1 : Q') * 1 := by
    have h000 : fusionInd 0 0 0 = 1 := by
      unfold fusionInd
      rw [if_pos ((fusionOK_iff 0 0 0).mpr (by decide))]
    rw [h000]
  -- Right side at cutoff D = 1: sum of a single 0·(·) term ≃ 0
  have hrsum : (finSum (fun f => (0 : Q') * (fusionInd 0 0 f * fusionInd 0 f 0)) 1).eqv 0 := by
    show (finSum (fun _ => (0 : Q') * (0 : Q')) 0
        + (0 : Q') * (fusionInd 0 0 0 * fusionInd 0 0 0)).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  have hbad := h 1 0 0 0 0 0
  rw [hleft] at hbad
  -- 1*1 ≃ 0, contradiction
  have h1 : ((1 : Q') * 1).eqv 0 := Q'.eqv_trans _ _ _ hbad hrsum
  have : (1 : Q').eqv 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv 1)) h1
  exact absurd this (by decide)

/-! ## 5. The beyond-tree partition identity: reduction to the 6j datum, and
the honest structural caveat. -/

/-- **The beyond-tree abstract↔real identity, reduced to the 6j datum.**  It
bundles the closed-fusion-loop `SixJRecoupling` (the frontier) WITH the
abstract↔real identity `Ξ ≃ Zreal`.  This is the honest reduction: the
beyond-tree identity is exactly "a 6j datum plus the identity it enables".
Left UNINHABITED — the `recoup` field is the irreducible open content. -/
structure BeyondTreePartitionIdentity [DecidableEq L.Plaquette]
    (w : Q') (label : L.Plaquette → Rep) where
  /-- The closed-fusion-loop 6j / Racah datum (the frontier). -/
  recoup : SixJRecoupling
  /-- The real (spin-network) partition function over the plaquette list. -/
  Zreal : List (Polymer L) → Q'
  /-- The abstract↔real identity `Ξ ≃ Zreal`. -/
  identity : ∀ Γ, (Xi w Γ label).eqv (Zreal Γ)

/-- The beyond-tree identity forgets to a plain `AbstractRealPartitionIdentity`
(the 6j datum is extra structure).  So inhabiting the 6j-aware beyond-tree
identity is at least as strong as the R1 wall. -/
def BeyondTreePartitionIdentity.toAbstract [DecidableEq L.Plaquette]
    {w : Q'} {label : L.Plaquette → Rep}
    (B : BeyondTreePartitionIdentity (L := L) w label) :
    AbstractRealPartitionIdentity (L := L) w label where
  Zreal := B.Zreal
  identity := B.identity

/-- **Structural caveat (the sharpest honest point).**  `AbstractRealPartition
Identity` on its own is TRIVIALLY inhabitable: its `Zreal` is a free function
pinned only by `Ξ ≃ Zreal`, so `Zreal := Ξ` with `eqv_refl` works.  Hence it
does NOT by itself enforce the ≥3-shared-link Haar content — the real content
must be carried by a genuine, constrained datum (`SixJRecoupling`,
`sixj_zero_fails`), not by this bare identity. -/
def trivialAbstractRealIdentity [DecidableEq L.Plaquette]
    (w : Q') (label : L.Plaquette → Rep) :
    AbstractRealPartitionIdentity (L := L) w label where
  Zreal := fun Γ => Xi w Γ label
  identity := fun _ => Q'.eqv_refl _

/-- The trivial inhabitant's real partition function IS `Ξ` (a sanity
unfolding, witnessing the under-specification). -/
theorem trivialAbstractRealIdentity_Zreal [DecidableEq L.Plaquette]
    (w : Q') (label : L.Plaquette → Rep) (Γ : List (Polymer L)) :
    (trivialAbstractRealIdentity (L := L) w label).Zreal Γ = Xi w Γ label := rfl

/-! ## 6. Refutation of option (A): tree → single loop is a NON-target. -/

/-- **Option (A) is a non-target.**  `LoopyLike 2 = TreeLike` is a
*≤2-shared-link* incidence bound, NOT acyclicity: a single plaquette cycle
(every link shared by exactly two plaquettes) already satisfies `TreeLike`.
So "extend the tree case to a single loop" adds nothing at the incidence level
— re-exposed from `LoopyLinkIntegral.loopyLike_two_iff_treeLike`.  (On the
correlator side the single loop re-pins via `δ_{r,r}=1`,
`CycleMayer.cycleG_collapse`: zero new datum.)  The genuine wall is the
≥3-shared-link closed *fusion-channel* loop (the 6j), NOT the plaquette
loop. -/
theorem single_loop_is_treeLike (Γ : List (Polymer L)) :
    LoopyLike 2 L Γ ↔ TreeLike L Γ := loopyLike_two_iff_treeLike Γ

/-! ## 7. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — finite `Q'` combinatorics, the proved 2-fold
orthogonality, and the SU(2) Clebsch–Gordan fusion `fusionOK`; NO 6j network):

  * `finSum_delta_left` — the reusable Kronecker-δ orthogonality collapse;
  * `orthoKernel_symm` / `orthoKernel_nonneg`, `fusionOK_iff`,
    `fusionInd_zero_left` / `fusionInd_fuse_zero` — the degenerate corners
    bridging `fusionInd` to `orthoKernel`;
  * `nFoldFuse` / `nFoldCharInt` (+ `nFoldFuse_cons`, `nFoldFuse_nonneg`,
    `nFoldCharInt_nonneg`) — the caterpillar `m`-fold single-link star fold
    (one trivalent vertex per plaquette; NO 6j);
  * `nFoldCharInt_nil` / `nFoldCharInt_single` / `nFoldCharInt_two` /
    `nFoldCharInt_three` — the star corners `∫1 = 1`, `∫χ_b = δ_{b,0}`,
    `∫χ_aχ_b = δ_{a,b}` (= `orthoKernel`), `∫χ_aχ_bχ_c = N_{cba}`
    (= `tripleCharInt`) — the star FOLDS, discharging the "star = 6j" mislabel;
  * `sixj_zero_fails` — the 6j / Biedenharn–Elliott constraint is non-vacuous;
  * `BeyondTreePartitionIdentity.toAbstract` — the reduction wires to the R1
    wall;
  * `trivialAbstractRealIdentity` (+ `_Zreal`) — the structural caveat: the bare
    abstract↔real identity is trivially inhabitable, so the real content lives in
    the constrained 6j datum, not the identity;
  * `single_loop_is_treeLike` — option (A) (tree → single loop) is a non-target.

NAMED-open (NOT faked, NO inhabitant):

  * `SixJRecoupling` — the closed-fusion-loop SU(2) 6j / Racah recoupling datum
    (the `m ≥ 4` tetrahedron): the lone irreducible frontier whose inhabitation
    would let the redefined spin-network activity match the real Haar `Zreal`
    past two shared links;
  * `BeyondTreePartitionIdentity` — the beyond-tree abstract↔real identity
    bundling that 6j datum with `Ξ ≃ Zreal`; left uninhabited.

This module is the single-link star FOLD (no 6j) + the precise 6j frontier and
its non-vacuity.  It is NOT the general `m ≥ 4` 6j network, NOT the full loopy
cluster expansion, NOT a continuum limit, and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.PartitionBeyondTree

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PartitionBeyondTree.finSum_delta_left
#print axioms YMGap.Continuum.PartitionBeyondTree.orthoKernel_symm
#print axioms YMGap.Continuum.PartitionBeyondTree.orthoKernel_nonneg
#print axioms YMGap.Continuum.PartitionBeyondTree.fusionOK_iff
#print axioms YMGap.Continuum.PartitionBeyondTree.fusionInd_zero_left
#print axioms YMGap.Continuum.PartitionBeyondTree.fusionInd_fuse_zero
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldFuse_cons
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldFuse_nonneg
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldCharInt_nonneg
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldCharInt_nil
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldFuse_single
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldCharInt_single
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldFuse_pair
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldCharInt_two
#print axioms YMGap.Continuum.PartitionBeyondTree.nFoldCharInt_three
#print axioms YMGap.Continuum.PartitionBeyondTree.sixj_zero_fails
#print axioms YMGap.Continuum.PartitionBeyondTree.BeyondTreePartitionIdentity.toAbstract
#print axioms YMGap.Continuum.PartitionBeyondTree.trivialAbstractRealIdentity
#print axioms YMGap.Continuum.PartitionBeyondTree.single_loop_is_treeLike
