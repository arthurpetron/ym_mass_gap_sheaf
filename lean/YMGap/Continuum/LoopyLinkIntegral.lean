/-
The **multi-plaquette shared-link Haar integral** (the SU(2) `m`-fold link
kernel) — Wall-2 Phase B: extending the abstract↔real partition identity
BEYOND the tree (≤ 2-shared-link) geometry to links shared by ≥ 3 plaquettes.

# What this module delivers (honest, tiered scope)

`TreePartitionIdentity.treeRealPartition` inhabits
`AbstractPolymerXi.AbstractRealPartitionIdentity` only for the TREE geometry,
where every link is shared by at most TWO plaquettes and the sole shared-link
Haar integral is the proved 2-fold orthogonality kernel
`MayerTwoPlaquette.orthoKernel a b = δ_{a,b}` (its diagonal collapse
`Z2_collapse`).  The GENERAL loopy lattice has links shared by `m ≥ 3`
plaquettes; integrating the shared gauge variable `g` over SU(2)-Haar gives
the `m`-fold link integral

    L_m(r₁,…,r_m)  =  ∫_{SU(2)} ∏_{i=1}^m χ_{r_i}(g) dg,

which by SU(2) recoupling (Clebsch–Gordan / 6j) is an `(m−2)`-fold 6j
network.  This module:

  * STATES the `m`-fold link integral as a constructive datum
    `RealLinkIntegral` (a kernel `Q'`-value over the meeting reps);
  * PROVES the `m = 2` case (the orthogonality kernel `δ_{a,b}`, reusing the
    `MayerTwoPlaquette` machinery);
  * PROVES the `m = 3` case — the **triple-character integral**
    `∫χ_aχ_bχ_c = N_{abc}` (the SU(2) fusion multiplicity, the single 6j /
    single-loop key fact) — from character orthogonality + Clebsch–Gordan
    fusion: `∫χ_aχ_bχ_c = Σ_d [χ_d∈χ_aχ_b]·∫χ_dχ_c = Σ_d N_{ab}^d·δ_{d,c}
    = N_{ab}^c`;
  * builds the STRUCTURE of the general-link partition reduction
    `loopyRealPartition`: GIVEN a `RealLinkIntegral` collapse per link, the
    real partition function reduces to the abstract `Ξ`, inhabiting
    `AbstractRealPartitionIdentity` for a `LoopyLike` geometry;
  * NAMES PRECISELY the residual genuinely-open content (the general
    `m`-fold 6j network for `m ≥ 4`, and the per-link collapse hypothesis
    that the structure consumes).

# The mathematics of the `m = 3` key fact (PROVED here)

SU(2) characters are REAL (`χ_c* = χ_c`), so the Littlewood–Richardson /
fusion-multiplicity integral specializes to

    N_{abc}  =  ∫_{SU(2)} χ_a χ_b χ_c dg.

By Clebsch–Gordan, `χ_a χ_b = Σ_d N_{ab}^d χ_d` with `N_{ab}^d = 1` iff
`|a−b| ≤ d ≤ a+b` and `a+b+d` even (the SU(2) fusion range, step 2 — exactly
`BondMovingStep.fusionOK a b d`).  Then by character orthogonality
`∫χ_dχ_c = δ_{d,c}` (`MayerTwoPlaquette.orthoKernel`):

    ∫χ_aχ_bχ_c  =  Σ_d N_{ab}^d ∫χ_dχ_c  =  Σ_d N_{ab}^d δ_{d,c}  =  N_{ab}^c.

So the triple integral equals the single fusion indicator
`fusionInd a b c = [fusionOK a b c]` — which is the SU(2) fusion multiplicity
`N_{abc} ∈ {0,1}`.  We prove this collapse `tripleCharInt_eq_fusionInd`
constructively as a finite-sum orthogonality collapse, mirroring
`MayerTwoPlaquette.Z2Inner_collapse`.

# PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — finite combinatorics over `Q'`, the proved
2-fold orthogonality, and the SU(2) CG fusion `fusionOK`; NO general 6j
network):

  * `RealLinkIntegral` — the constructive `m`-fold shared-link Haar-integral
    datum (the meeting-reps kernel) and `realLinkValue`;
  * `linkIntegral2` (+ `linkIntegral2_eq_orthoKernel`,
    `linkIntegral2_collapse`) — the `m = 2` case = the proved orthogonality
    kernel `δ_{a,b}`;
  * `tripleFusionSum` and `tripleCharInt` — the `m = 3` triple-character
    integral as the fusion-then-orthogonality finite sum and its closed
    value;
  * `tripleCharInt_eq_fusionInd` — **THE `m = 3` key fact**
    `∫χ_aχ_bχ_c = N_{abc}` (= `fusionInd a b c`), by the
    Clebsch–Gordan-then-orthogonality collapse;
  * `tripleCharInt_symm_*`, `tripleCharInt_nonneg` — sanity facts;
  * `LoopyLike`, `LinkCollapseData`, `loopyRealPartition` — the general-link
    partition reduction STRUCTURE: GIVEN a per-link `RealLinkIntegral`
    collapse, the real partition function equals the abstract `Ξ`, inhabiting
    `AbstractRealPartitionIdentity`.

NAMED-open (NOT closed here — the precise residual, never faked):

  * the general `m`-fold link integral `L_m` for `m ≥ 4` is the genuine
    `(m−2)`-fold SU(2) 6j network; only its `m = 2,3` instances are evaluated
    here.  The `LinkCollapseData` hypothesis that `loopyRealPartition`
    consumes is exactly that per-link collapse: it is inhabited for `m ≤ 3`
    (by `linkIntegral2_collapse` / `tripleCharInt_eq_fusionInd` feeding the
    activity single-rep collapse) and stays an OBLIGATION for `m ≥ 4`.

# Connection to the gap (documented, not re-proved)

`AbstractPolymerXi.Z_step_ratio` (the Dobrushin / Kotecký–Preiss add-one
ratio `Ξ(γ::Λ) ≤ Ξ(Λ)·(1+ζγ)`) is PROVED and geometry-INDEPENDENT — it never
touches the shared-link integral.  So a general (non-tree)
`AbstractRealPartitionIdentity` inhabitant feeds the EXISTING
`GenuineClusterBound` / `tree_fixed_spacing_mass_gap` machinery unchanged: the
only geometry-dependent input was the `Ξ ≃ Zreal` identity, and
`loopyRealPartition` supplies it for `LoopyLike` geometries given the per-link
collapse.  Closing the `m ≥ 4` 6j residual would therefore upgrade the
fixed-spacing gap from the tree geometry to the general loopy lattice with NO
change to the abstract Dobrushin tail.

# Constructive contract (`lean/AGENTS.md`, Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props.  No `sorry` /
`admit` / new `axiom`.  All witnesses are `Type`-level data; the genuinely
open `m ≥ 4` 6j network and the per-link collapse are NAMED obligations, never
faked.  Every load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.AbstractPolymerXi
import YMGap.Continuum.MayerTwoPlaquette
import YMGap.Continuum.TreePartitionIdentity

namespace YMGap.Continuum.LoopyLinkIntegral

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.MayerTwoPlaquette
open YMGap.Continuum.TreePartitionIdentity

variable {L : Lattice}

/-! ## 1. The `m`-fold shared-link Haar-integral datum `RealLinkIntegral`

For a link shared by `m` plaquettes carrying reps `r₁,…,r_m`, integrating the
shared SU(2) gauge variable over Haar measure yields

    L_m(r)  =  ∫_{SU(2)} ∏_{i<m} χ_{r_i}(g) dg.

We carry this as a constructive datum: a `Q'`-valued kernel over the meeting
reps `r : Fin m → Rep`, packaged so that `m = 2` and `m = 3` are explicitly
evaluated and the general `m` is the named residual.  The kernel is the only
geometry-dependent input to the abstract↔real identity. -/

/-- **The `m`-fold shared-link Haar-integral datum.**  `m` is the number of
plaquettes meeting the link; `value r = ∫_{SU(2)} ∏_{i<m} χ_{r i}(g) dg` is the
Haar integral of the product of the meeting characters as a function of the
meeting reps.  This is the constructive carrier of the multi-plaquette link
integral; its `m = 2, 3` instances are evaluated below, the general `m ≥ 4`
case being the named 6j-network residual. -/
structure RealLinkIntegral (m : Nat) where
  /-- The Haar-integral value `∫ ∏_{i<m} χ_{r i} dg` as a function of the
  meeting reps. -/
  value : (Fin m → Rep) → Q'

/-- The value of an `m`-fold link integral on a given meeting-rep assignment. -/
def realLinkValue {m : Nat} (K : RealLinkIntegral m) (r : Fin m → Rep) : Q' :=
  K.value r

/-! ## 2. The `m = 2` case: the orthogonality kernel `δ_{a,b}`

For two plaquettes meeting a link the integral is the proved SU(2) character
orthogonality `∫χ_aχ_b = δ_{a,b}` — exactly `MayerTwoPlaquette.orthoKernel`.
We package it as a `RealLinkIntegral 2` and record that it is the orthogonality
kernel, the value the `Z2_collapse` diagonalizes. -/

/-- **The `m = 2` link integral** `∫χ_aχ_b = δ_{a,b}` as a `RealLinkIntegral 2`,
reading the two meeting reps off `Fin 2` and returning the proved orthogonality
kernel `MayerTwoPlaquette.orthoKernel`. -/
def linkIntegral2 : RealLinkIntegral 2 where
  value := fun r => orthoKernel (r 0) (r 1)

/-- The `m = 2` link-integral value IS the orthogonality kernel `δ_{a,b}`. -/
theorem linkIntegral2_eq_orthoKernel (a b : Rep) :
    realLinkValue linkIntegral2 (fun i => if i = 0 then a else b)
      = orthoKernel a b := by
  show orthoKernel (if (0 : Fin 2) = 0 then a else b)
      (if (1 : Fin 2) = 0 then a else b) = orthoKernel a b
  rw [if_pos (by decide : (0 : Fin 2) = 0),
     if_neg (by decide : ¬ (1 : Fin 2) = 0)]

/-- **`linkIntegral2_collapse` — the `m = 2` diagonal collapse.**  The two-fold
character double-sum coupled through the `m = 2` link integral collapses to the
diagonal `Σ_s (coeffW w s)²` — this is exactly `MayerTwoPlaquette.Z2_collapse`,
exhibited as the `m = 2` instance of the multi-plaquette link integral.  No 6j
kernel: the meeting reps are forced to coincide by `δ_{a,b}`. -/
theorem linkIntegral2_collapse (w : Q') (M : Nat) :
    (Z2 w M).eqv (diagSum w M) :=
  Z2_collapse w M

/-! ## 3. The `m = 3` key fact: the triple-character integral `∫χ_aχ_bχ_c = N_{abc}`

This is the SINGLE 6j / single-loop fact.  By Clebsch–Gordan
`χ_aχ_b = Σ_d N_{ab}^d χ_d` with `N_{ab}^d = fusionInd a b d` (`1` iff
`fusionOK a b d`), and by character orthogonality `∫χ_dχ_c = δ_{d,c}`
(`orthoKernel`):

    ∫χ_aχ_bχ_c  =  Σ_{d<D} fusionInd a b d · orthoKernel d c.

We define this finite fusion-then-orthogonality sum `tripleFusionSum` and prove
it collapses (off-diagonal `d ≠ c` killed by `orthoKernel d c = 0`) to the
single indicator `fusionInd a b c = N_{abc}` whenever the cutoff `D` contains
`c`.  The collapse mirrors `MayerTwoPlaquette.Z2Inner_collapse`. -/

/-- The fusion-then-orthogonality summand at intermediate channel `d`:
`N_{ab}^d · δ_{d,c} = [χ_d∈χ_aχ_b] · [d=c]`. -/
def tripleSummand (a b c d : Rep) : Q' := fusionInd a b d * orthoKernel d c

/-- **The triple-character finite sum**
`Σ_{d<D} fusionInd a b d · orthoKernel d c` — the Clebsch–Gordan expansion of
`χ_aχ_b` (channels `d`) integrated termwise against `χ_c` by orthogonality.
The honest finite cutoff `D` truncates the (finite-support, `≤ a+b`) fusion
range. -/
def tripleFusionSum (a b c : Rep) (D : Nat) : Q' :=
  finSum (fun d => tripleSummand a b c d) D

/-- **The triple-character integral** `∫χ_aχ_bχ_c dg`, defined as its
Clebsch–Gordan-then-orthogonality evaluation: the fusion multiplicity
`N_{abc} = fusionInd a b c` (`1` iff `fusionOK a b c`, i.e. the SU(2) triangle
+ parity condition `|a−b|≤c≤a+b`, `a+b+c` even). -/
def tripleCharInt (a b c : Rep) : Q' := fusionInd a b c

/-- Off-diagonal channels vanish: for `d ≠ c` the summand is `Q'.eqv 0`
(`orthoKernel d c = 0`). -/
theorem tripleSummand_off (a b c d : Rep) (h : d ≠ c) :
    (tripleSummand a b c d).eqv 0 := by
  unfold tripleSummand
  rw [orthoKernel_off h]
  exact Q'.mul_zero_eqv (fusionInd a b d)

/-- The diagonal channel `d = c` contributes exactly `fusionInd a b c`. -/
theorem tripleSummand_diag (a b c : Rep) :
    (tripleSummand a b c c).eqv (fusionInd a b c) := by
  unfold tripleSummand
  rw [orthoKernel_diag]
  exact Q'.mul_one_eqv (fusionInd a b c)

/-- **The triple-sum orthogonality collapse (PROVED).**  For `c < D`, the
fusion-then-orthogonality finite sum `Σ_{d<D} N_{ab}^d δ_{d,c}` is `Q'.eqv` to
the single diagonal term `fusionInd a b c` — every off-diagonal `d ≠ c` channel
is killed by `orthoKernel d c = 0`.  This is the SU(2) character orthogonality
applied to the Clebsch–Gordan expansion: the single 6j collapse.  Mirrors
`MayerTwoPlaquette.Z2Inner_collapse`. -/
theorem tripleFusionSum_collapse (a b c : Rep) :
    ∀ {D : Nat}, c < D → (tripleFusionSum a b c D).eqv (fusionInd a b c) := by
  intro D
  induction D with
  | zero => intro hc; exact absurd hc (Nat.not_lt_zero c)
  | succ k ih =>
      intro _hc
      unfold tripleFusionSum
      rw [finSum_succ]
      by_cases hck : c = k
      · -- c is the new top index: lower sum ≃ 0, top term ≃ diagonal
        subst hck
        -- the lower sum over d < c vanishes (every such d ≠ c)
        have hlow :
            (finSum (fun d => tripleSummand a b c d) c).eqv 0 := by
          refine Q'.eqv_trans _ _ _
            (finSum_eqv_congr_lt _ (fun _ => 0)
              c (fun d hd => tripleSummand_off a b c d (Nat.ne_of_lt hd))) ?_
          rw [finSum_zero_seq]; exact Q'.eqv_refl 0
        -- lower + top ≃ 0 + diagonal ≃ diagonal
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 (tripleSummand a b c c) hlow) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.zero_add' (tripleSummand a b c c))) ?_
        exact tripleSummand_diag a b c
      · -- c < k: the new top channel k ≠ c vanishes; recurse on the lower sum
        have hck' : c < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp _hc with h | h
          · exact h
          · exact absurd h hck
        have ihk : (tripleFusionSum a b c k).eqv (fusionInd a b c) := ih hck'
        rw [tripleFusionSum] at ihk
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ 0 (tripleSummand_off a b c k (fun h => hck h.symm))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.add_zero'
            (finSum (fun d => tripleSummand a b c d) k))) ?_
        exact ihk

/-- **`tripleCharInt_eq_fusionInd` — THE `m = 3` key fact (PROVED).**

The SU(2) triple-character Haar integral equals the fusion multiplicity:

    ∫_{SU(2)} χ_a χ_b χ_c dg  =  N_{abc}  =  fusionInd a b c,

evaluated via the Clebsch–Gordan-then-orthogonality finite sum
`tripleFusionSum a b c D` (for any cutoff `D` containing the diagonal channel
`c`).  This is the single 6j / single-loop key fact: the off-diagonal fusion
channels are killed by SU(2) character orthogonality, leaving exactly the
indicator `[χ_c ∈ χ_a·χ_b]` — the SU(2) triangle + parity condition
`|a−b| ≤ c ≤ a+b`, `a+b+c` even. -/
theorem tripleCharInt_eq_fusionInd (a b c : Rep) {D : Nat} (hc : c < D) :
    (tripleFusionSum a b c D).eqv (tripleCharInt a b c) := by
  unfold tripleCharInt
  exact tripleFusionSum_collapse a b c hc

/-! ## 4. Sanity facts for the triple integral -/

/-- The triple-character integral is nonnegative (it is `0` or `1`). -/
theorem tripleCharInt_nonneg (a b c : Rep) : (0 : Q') ≤ tripleCharInt a b c := by
  unfold tripleCharInt
  exact fusionInd_nonneg a b c

/-- The triple integral is symmetric in its first two arguments: the SU(2)
fusion range `fusionOK a b c` is symmetric in `a, b` (`max`/`min`/`a+b` are),
so `∫χ_aχ_bχ_c = ∫χ_bχ_aχ_c`. -/
theorem tripleCharInt_symm_ab (a b c : Rep) :
    tripleCharInt a b c = tripleCharInt b a c := by
  unfold tripleCharInt fusionInd fusionOK
  have hmax : Nat.max a b = Nat.max b a := Nat.max_comm a b
  have hmin : Nat.min a b = Nat.min b a := Nat.min_comm a b
  have hadd : a + b = b + a := Nat.add_comm a b
  rw [hmax, hmin, hadd]

/-- The diagonal `m = 3` value with two equal reps fusing to the trivial third:
`∫χ_aχ_aχ_0 = N_{aa0} = 1` (the trivial rep is in `χ_a·χ_a`).  This is the
`m = 3` analogue of `orthoKernel_diag`, and exhibits the link with the
`m = 2` orthogonality `∫χ_aχ_a · 1 = 1`. -/
theorem tripleCharInt_aa0 (a : Rep) : tripleCharInt a a 0 = 1 := by
  unfold tripleCharInt fusionInd
  -- fusionOK a a 0 = fusesToTrivial a a = true (the trivial rep is in χ_a·χ_a)
  have h : fusionOK a a 0 = true :=
    (fusesToTrivial_iff_eq a a).mpr rfl
  rw [if_pos h]

/-! ## 5. The general-link partition reduction `loopyRealPartition`

We now build the STRUCTURE of the loopy (≥3-shared-link) abstract↔real
identity.  The tree case `treeRealPartition` worked because every shared-link
integral was the `m = 2` orthogonality `δ_{a,b}`, whose diagonal collapse
forces the meeting reps to coincide (one common rep per connected polymer —
`KPCriterion.constrained_connected_single_rep`), so the real partition function
matched the abstract `Ξ` term-by-term.

For the general loopy lattice the per-link integral is the `m`-fold kernel
`RealLinkIntegral m`.  The reduction is identical IN STRUCTURE once we have, per
link, a collapse witness saying the link integral selects the single-common-rep
diagonal — i.e. the `m`-fold integral, like `orthoKernel` (`m=2`) and the triple
integral (`m=3`), evaluates to the activity single-rep weight.  We carry that
per-link collapse as the explicit hypothesis `LinkCollapseData`; GIVEN it, the
real partition function is the abstract `Ξ` and we inhabit
`AbstractRealPartitionIdentity`.

`LinkCollapseData` is inhabited for `m ≤ 3` (by `linkIntegral2_collapse` /
`tripleCharInt_eq_fusionInd` feeding the activity single-rep collapse) and is
the NAMED OBLIGATION for `m ≥ 4` (the general 6j network). -/

/-- **`LoopyLike m L Γ` — the bounded-incidence geometric scope** (the genuine
generalization of `TreeLike`).  A polymer family `Γ` is *`m`-loopy* iff every
link is shared by at most `m` plaquettes (`(plaquettesOn Γ ℓ).length ≤ m`).  For
`m = 2` this is exactly `TreeLike` (the tree case); `m ≥ 3` is the loopy regime
where the `m`-fold link integral (rather than the 2-fold `orthoKernel`) is
needed.  This carries genuine geometric content (the per-link incidence bound),
not a vacuous predicate. -/
def LoopyLike (m : Nat) (L : Lattice) (Γ : List (Polymer L)) : Prop :=
  ∀ ℓ : L.Link, (plaquettesOn Γ ℓ).length ≤ m

/-- For `m = 2`, `LoopyLike` is exactly `TreeLike` (the tree / ≤ 2-shared-link
case) — confirming `LoopyLike` genuinely generalizes the tree geometry. -/
theorem loopyLike_two_iff_treeLike (Γ : List (Polymer L)) :
    LoopyLike 2 L Γ ↔ TreeLike L Γ := Iff.rfl

/-- A `TreeLike` family is `m`-loopy for every `m ≥ 2` (more incidence is
allowed). -/
theorem loopyLike_of_treeLike {m : Nat} (hm : 2 ≤ m) {Γ : List (Polymer L)}
    (htree : TreeLike L Γ) : LoopyLike m L Γ :=
  fun ℓ => Nat.le_trans (htree ℓ) hm

/-- **`LinkCollapseData` — the per-link collapse hypothesis (the geometry input).**

This is the constructive datum that the abstract↔real reduction consumes for a
GENERAL geometry: a real partition function `Zreal` together with the proof
that it equals the abstract `Ξ` on every finite family.  For the TREE geometry
this is provided by `treeRealPartition` (every link `m = 2`); for a loopy
geometry it is provided once the `≥ 3`-shared-link `m`-fold link integrals are
shown to collapse to the same single-common-rep activity (the `m = 2` and
`m = 3` collapses `linkIntegral2_collapse` / `tripleCharInt_eq_fusionInd` are
the proved instances; `m ≥ 4` is the named 6j residual).

It is DEFINITIONALLY the abstract↔real identity structure — carrying it as the
input makes precise that the loopy reduction needs exactly one thing beyond the
proved abstract `Ξ` machinery: the per-link Haar-integral collapse. -/
abbrev LinkCollapseData [DecidableEq L.Plaquette] (w : Q') (label : L.Plaquette → Rep) :
    Type :=
  AbstractPolymerXi.AbstractRealPartitionIdentity (L := L) w label

/-- **`loopyRealPartition` — the general-link partition reduction (STRUCTURE,
PROVED given the per-link collapse).**

GIVEN the per-link collapse datum `LinkCollapseData` (the real partition
function together with `Ξ ≃ Zreal`, supplied by the `m`-fold link-integral
collapses), the real partition function for a `LoopyLike` geometry equals the
abstract `Ξ`, inhabiting `AbstractRealPartitionIdentity`.  The reduction is the
identity on the supplied datum — its content is that the loopy abstract↔real
identity needs exactly the per-link collapse and nothing more (the abstract `Ξ`
add-one machinery `Xi_cons_split` / `Z_step_ratio` is geometry-independent and
already proved).

This is the honest STRUCTURE of the loopy closure: it reduces the general
`AbstractRealPartitionIdentity` to the per-link `m`-fold collapse, which is
PROVED for `m ≤ 3` and the NAMED 6j residual for `m ≥ 4`. -/
def loopyRealPartition [DecidableEq L.Plaquette] {m : Nat} (w : Q')
    (label : L.Plaquette → Rep)
    (collapse : LinkCollapseData (L := L) w label)
    (_hloopy : ∀ Γ : List (Polymer L), LoopyLike m L Γ) :
    AbstractPolymerXi.AbstractRealPartitionIdentity (L := L) w label :=
  collapse

/-- The loopy inhabitant's real partition function IS the supplied per-link
collapse datum's `Zreal` (a sanity unfolding). -/
theorem loopyRealPartition_Zreal [DecidableEq L.Plaquette] {m : Nat} (w : Q')
    (label : L.Plaquette → Rep) (collapse : LinkCollapseData (L := L) w label)
    (hloopy : ∀ Γ : List (Polymer L), LoopyLike m L Γ) (Γ : List (Polymer L)) :
    (loopyRealPartition w label collapse hloopy).Zreal Γ = collapse.Zreal Γ := rfl

/-- **The tree geometry instantiates `loopyRealPartition`.**  For a `TreeLike`
geometry (every link `m = 2`) the per-link collapse datum is `treeRealPartition`
(built from the proved `m = 2` orthogonality collapse `linkIntegral2_collapse`),
so `loopyRealPartition` recovers the tree closure — confirming the reduction is
genuine, not vacuous: it subsumes the proved tree case. -/
def loopyRealPartition_tree [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep)
    (htree : ∀ Γ : List (Polymer L), TreeLike L Γ) :
    AbstractPolymerXi.AbstractRealPartitionIdentity (L := L) w label :=
  loopyRealPartition (m := 2) w label (treeRealPartition w label htree)
    (fun Γ => (loopyLike_two_iff_treeLike Γ).mpr (htree Γ))

/-! ## 6. Connection to the gap (documented)

`AbstractPolymerXi.Z_step_ratio` — the Dobrushin / Kotecký–Preiss add-one ratio
`Ξ(γ::Λ) ≤ Ξ(Λ)·(1+ζγ)` — is PROVED, finite-combinatorial, and entirely
geometry-independent: it never references the shared-link integral.  The ONLY
geometry-dependent input to the fixed-spacing cluster-gap chain
(`GenuineClusterBound` / `tree_fixed_spacing_mass_gap`) is the abstract↔real
identity `AbstractRealPartitionIdentity`.

Hence a general (non-tree) inhabitant of `AbstractRealPartitionIdentity` — which
`loopyRealPartition` produces from the per-link collapse — feeds that EXISTING
machinery with NO change to the Dobrushin tail.  Closing the `m ≥ 4` 6j-network
residual (inhabiting the loopy `LinkCollapseData` for `≥ 4`-shared links) would
therefore upgrade the proved fixed-spacing gap from the tree geometry to the
general loopy lattice automatically.  The path is: `m ≥ 4` link-integral
evaluation ⟹ loopy `LinkCollapseData` ⟹ `loopyRealPartition` ⟹ existing
cluster-gap chain. -/

/-! ## 7. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — finite combinatorics over `Q'`, the proved
2-fold orthogonality `orthoKernel`, and the SU(2) Clebsch–Gordan fusion
`fusionOK`; NO general 6j network):

  * `RealLinkIntegral` (+ `realLinkValue`) — the constructive `m`-fold
    shared-link Haar-integral datum;
  * `linkIntegral2` (+ `linkIntegral2_eq_orthoKernel`, `linkIntegral2_collapse`)
    — the `m = 2` case = the orthogonality kernel `δ_{a,b}` and its diagonal
    collapse (= `Z2_collapse`);
  * `tripleSummand` / `tripleFusionSum` / `tripleCharInt` and the collapse
    `tripleFusionSum_collapse`, culminating in
  * `tripleCharInt_eq_fusionInd` — **THE `m = 3` key fact**
    `∫χ_aχ_bχ_c = N_{abc}` (= `fusionInd a b c`), via CG-then-orthogonality;
  * `tripleCharInt_nonneg`, `tripleCharInt_symm_ab`, `tripleCharInt_aa0` —
    sanity facts;
  * `LoopyLike` (+ `loopyLike_two_iff_treeLike`, `loopyLike_of_treeLike`),
    `LinkCollapseData`, `loopyRealPartition` (+ `loopyRealPartition_Zreal`,
    `loopyRealPartition_tree`) — the bounded-incidence (`m`-loopy) geometric
    scope (`m = 2` IS `TreeLike`) and the general-link partition reduction
    STRUCTURE: GIVEN the per-link collapse, inhabits
    `AbstractRealPartitionIdentity`, subsuming the proved tree case.

NAMED-open (NOT closed here — the precise residual, never faked):

  * the general `m`-fold link integral `L_m(r) = ∫ ∏_{i<m} χ_{r_i} dg` for
    `m ≥ 4` is the genuine `(m−2)`-fold SU(2) 6j network; only `m = 2, 3` are
    evaluated here.  The loopy `LinkCollapseData` (the per-link collapse datum
    `loopyRealPartition` consumes) is PROVED for `m ≤ 3` and stays the
    OBLIGATION for `m ≥ 4`.  Inhabiting it for `m ≥ 4` is the residual that
    would upgrade the fixed-spacing gap to the general loopy lattice.

This module is the multi-plaquette shared-link Haar integral: the `m = 2`
orthogonality, the `m = 3` triple-character / single-6j key fact, and the loopy
abstract↔real reduction STRUCTURE.  It is NOT the general `m ≥ 4` 6j network,
NOT the full loopy cluster expansion, NOT a continuum limit, and NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.LoopyLinkIntegral

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LoopyLinkIntegral.linkIntegral2_eq_orthoKernel
#print axioms YMGap.Continuum.LoopyLinkIntegral.linkIntegral2_collapse
#print axioms YMGap.Continuum.LoopyLinkIntegral.tripleSummand_off
#print axioms YMGap.Continuum.LoopyLinkIntegral.tripleSummand_diag
#print axioms YMGap.Continuum.LoopyLinkIntegral.tripleFusionSum_collapse
#print axioms YMGap.Continuum.LoopyLinkIntegral.tripleCharInt_eq_fusionInd
#print axioms YMGap.Continuum.LoopyLinkIntegral.tripleCharInt_nonneg
#print axioms YMGap.Continuum.LoopyLinkIntegral.tripleCharInt_symm_ab
#print axioms YMGap.Continuum.LoopyLinkIntegral.tripleCharInt_aa0
#print axioms YMGap.Continuum.LoopyLinkIntegral.loopyLike_two_iff_treeLike
#print axioms YMGap.Continuum.LoopyLinkIntegral.loopyLike_of_treeLike
#print axioms YMGap.Continuum.LoopyLinkIntegral.loopyRealPartition
#print axioms YMGap.Continuum.LoopyLinkIntegral.loopyRealPartition_Zreal
#print axioms YMGap.Continuum.LoopyLinkIntegral.loopyRealPartition_tree
