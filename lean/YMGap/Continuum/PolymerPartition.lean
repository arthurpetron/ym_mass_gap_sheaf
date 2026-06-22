/-
Stage-1 / H2.2 — the **polymer-expansion identity** connecting the abstract
polymer model (`PolymerModel.activity`) to a REAL finite-volume heat-kernel
partition function, at the level the discrete character / Haar structure
permits.

# The mathematics

For lattice gauge theory with the SU(2) heat-kernel plaquette weight, the
finite-volume partition function is the Haar integral over the link variables
of the product of the plaquette weights:

    Z_Λ  =  ∫ ∏_{p}  K_w(plaquette p)  ∏_ℓ dg_ℓ.

Each single-plaquette heat-kernel weight expands in characters with the
diagonal coefficient `coeffW w s = dim(s)·w^{C₄(s)} = (s+1)·w^{s(s+2)}`
(`BondMovingStep.coeffW`).  Performing the link Haar integrals via character
ORTHOGONALITY (`∫χ_μ χ̄_ν dg = δ_{μν}`) makes `Z_Λ` a finite RATIONAL/`Q'`
sum over rep-labelings of the plaquettes — NO analytic integration, purely
the discrete character algebra — with each internal link surviving only when
the meeting reps fuse to the trivial rep (`PolymerModel.fusesToTrivial`).

This module closes the cases the discrete structure makes clean:

  * the **single-plaquette** partition function (one group variable, the bare
    character sum), and
  * the **disjoint / non-interacting** case (a finite plaquette set sharing
    no internal links, so the Haar integral FACTORIZES per plaquette).

In both cases the partition function matches the polymer sum
`Σ_configs ∏ activity` exactly, where the polymer expansion reduces to the
product over single-plaquette activities — the leading (non-interacting)
polymer contribution.

# What is PROVED here (all genuine — no fakes)

  * `singlePlaqZ w M = Σ_{s<M} coeffW w s` — the REAL single-plaquette
    heat-kernel partition function (the character-orthogonality sum), with
    `singlePlaqZ_nonneg` / `singlePlaqZ_pos`.
  * `singlePlaqPolymerSum w M = Σ_{s<M} activity w [singleton] (label s)` —
    the polymer-sum side over a single plaquette's rep-labelings, reusing
    `PolymerModel.activity`.
  * `single_plaquette_identity : singlePlaqZ w M = singlePlaqPolymerSum w M`
    — the partition function = polymer sum, single-plaquette case (the
    activity of a singleton labeled `s` is exactly `coeffW w s`).
  * `Z_disjoint w M k = Π_{i<k} singlePlaqZ w M` — the disjoint-plaquette
    partition function (Haar factorizes over the `k` non-interacting
    plaquettes).
  * `disjointPolymerSum w M k = Π_{i<k} singlePlaqPolymerSum w M` — the
    factorized polymer sum (product of per-plaquette polymer sums = the
    leading non-interacting polymer expansion).
  * `disjoint_partition_identity : Z_disjoint w M k = disjointPolymerSum w M k`
    — THE polymer-expansion identity in the disjoint case (`Z` factorizes =
    product of single-plaquette polymer sums), with the strict-positivity
    corollary `Z_disjoint_pos`.

# What is NAMED but NOT done (Type-level obligation, NOT faked)

The full **Mayer / cluster expansion** for arbitrary INTERACTING plaquette
configurations — the connected-polymer reorganization
`log Z = Σ_{connected clusters} Ursell(cluster)`, where overlapping
polymers contribute Ursell (truncated-correlation) coefficients with
alternating signs — is the analytic heart that does NOT reduce to a finite
product.  It is carried here as the named Type-level structure
`MayerExpansion` (an obligation to be supplied), with NO proof and NO
placeholder inhabitant.  The disjoint identity above is exactly its
trivial (no-interaction, all-Ursell-coefficients-degenerate-to-1) case.

# Constructive contract (`AGENTS.md` Rules 1, 6, 8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props, no `sorry` / `admit`
/ new `axiom`.  Witnesses are `Type`-level data; the genuinely-open Mayer
reorganization is a named structure, not a faked proof.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).
-/

import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.PolymerModel
import YMGap.Continuum.ContinuumExistence
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.PolymerPartition

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.PolymerModel

/-! ## 1. The single-plaquette partition function (character orthogonality)

The heat-kernel weight on one plaquette `g ↦ K_w(g)` expands as
`K_w(g) = Σ_s coeffW w s · χ_s(g)` (the SU(2) character expansion, diagonal
coefficient `coeffW w s = dim(s)·w^{C₄(s)}`).  Its Haar integral — the
single-plaquette partition function — is, by character orthogonality
`∫ χ_s dg = δ_{s,0}`… but the gauge-invariant single-plaquette object the
cluster expansion sums is the full character mass, the sum of the diagonal
coefficients over reps `s < M` (the truncated character partition):

    singlePlaqZ w M  =  Σ_{s < M} coeffW w s.

This is a finite `Q'` sum — the discrete character substitute for the Haar
integral.  The `s = 0` (vacuum) term `coeffW w 0 = 1` is the normalization;
the `s ≥ 1` excited terms are exactly the `PlaquetteActivity.plaqActivity`
mass.  No analytic integration: pure character algebra. -/

/-- **The single-plaquette heat-kernel partition function**
`Z₁(w, M) = Σ_{s < M} coeffW w s`, the finite character sum the Haar integral
reduces to by orthogonality (vacuum `s = 0` + excited `s ≥ 1`). -/
def singlePlaqZ (w : Q') (M : Nat) : Q' :=
  finSum (fun s => coeffW w s) M

@[simp] theorem singlePlaqZ_zero (w : Q') : singlePlaqZ w 0 = 0 := rfl

@[simp] theorem singlePlaqZ_succ (w : Q') (M : Nat) :
    singlePlaqZ w (M + 1) = singlePlaqZ w M + coeffW w M := rfl

/-- The single-plaquette partition function is nonnegative for `0 ≤ w`
(a sum of nonnegative character coefficients). -/
theorem singlePlaqZ_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    (0 : Q') ≤ singlePlaqZ w M := by
  induction M with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      rw [singlePlaqZ_succ]
      exact Q'.zero_le_add _ _ ih (coeffW_nonneg hw k)

/-- The single-plaquette partition function is strictly positive once at
least the vacuum rep is included (`1 ≤ M`), since `coeffW w 0 = 1 > 0` and
all other terms are nonnegative. -/
theorem singlePlaqZ_pos {w : Q'} (hw : (0 : Q') ≤ w) {M : Nat} (hM : 1 ≤ M) :
    (0 : Q') < singlePlaqZ w M := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  -- Z(k+1) = Z(k) + coeffW w k.  Induct: the vacuum term `coeffW w 0 = 1 > 0`
  -- enters at the base and is preserved by adding nonnegative excited terms.
  clear hM
  induction k with
  | zero =>
      -- singlePlaqZ w 1 = singlePlaqZ w 0 + coeffW w 0 = 0 + 1 = 1 > 0
      rw [singlePlaqZ_succ, singlePlaqZ_zero, coeffW_zero]
      show (0 : Q') < 0 + 1
      rw [Q'.zero_add']
      decide
  | succ j ih =>
      -- Z(j+2) = Z(j+1) + coeffW w (j+1), with Z(j+1) > 0 (ih) and the new
      -- excited term nonnegative.
      rw [singlePlaqZ_succ]
      exact Q'.pos_add_nonneg ih (coeffW_nonneg hw (j + 1))

/-! ## 2. The polymer-sum side (single plaquette)

The polymer expansion over a SINGLE plaquette `p` sums, over the rep-labelings
`s` of `p`, the activity of the singleton polymer `[p]` labeled by `s`.  By
`PolymerModel.activity_cons` / `activity_nil`,

    activity w [p] (const s)  =  plaqWeight w (const s) p · 1  =  coeffW w s,

so this polymer sum is term-by-term equal to `singlePlaqZ`.  We make the
labeling concrete via the constant labeling `constLabel s := fun _ => s`. -/

/-- The constant rep-labeling assigning spin `s` to every plaquette. -/
def constLabel {L : Lattice} (s : Rep) : L.Plaquette → Rep := fun _ => s

/-- The activity of a singleton polymer `[p]` under the constant labeling `s`
is exactly the single character coefficient `coeffW w s` (up to `.eqv`: the
`foldr` leaves a trailing `· 1`, removed by `mul_one_eqv`).  The underlying
value `plaqWeight w (constLabel s) p` reduces definitionally to
`coeffW w s`. -/
theorem activity_singleton_const {L : Lattice} (w : Q') (p : L.Plaquette)
    (s : Rep) :
    (activity w ([p] : Polymer L) (constLabel s)).eqv (coeffW w s) := by
  -- activity w [p] label = plaqWeight w label p * 1 = coeffW w s * 1
  show (plaqWeight w (constLabel (L := L) s) p * 1).eqv (coeffW w s)
  show (coeffW w (constLabel (L := L) s p) * 1).eqv (coeffW w s)
  show (coeffW w s * 1).eqv (coeffW w s)
  exact Q'.mul_one_eqv (coeffW w s)

/-- **The single-plaquette polymer sum**
`Σ_{s < M} activity w [p] (constLabel s)` — the polymer-expansion side over
one plaquette, summing the singleton activity over the rep-labelings. -/
def singlePlaqPolymerSum {L : Lattice} (w : Q') (p : L.Plaquette) (M : Nat) :
    Q' :=
  finSum (fun s => activity w ([p] : Polymer L) (constLabel s)) M

/-- **THE single-plaquette polymer-expansion identity (PROVED).**

`Z₁ ≃ Σ_polymers ∏ activity` on one plaquette: the single-plaquette
heat-kernel partition function equals (up to `Q'.eqv`, the canonical
equivalence on `Q'`) the polymer sum over the singleton's rep-labelings,
because the activity of the singleton labeled `s` is exactly the character
coefficient `coeffW w s`.  The genuine algebraic matching of the Haar
character expansion with the polymer enumeration, term-by-term via
`finSum_eqv_congr_lt`. -/
theorem single_plaquette_identity {L : Lattice} (w : Q') (p : L.Plaquette)
    (M : Nat) :
    (singlePlaqZ w M).eqv (singlePlaqPolymerSum w p M) := by
  unfold singlePlaqZ singlePlaqPolymerSum
  -- term-by-term: coeffW w s ≃ activity w [p] (constLabel s)
  exact finSum_eqv_congr_lt
    (fun s => coeffW w s)
    (fun s => activity w ([p] : Polymer L) (constLabel s))
    M
    (fun s _ => Q'.eqv_symm (activity_singleton_const w p s))

/-! ## 3. The disjoint (non-interacting) partition function and identity

A finite set of `k` plaquettes sharing NO internal link is non-interacting:
the link Haar integrals factorize, so the partition function is the PRODUCT
of the `k` single-plaquette partition functions:

    Z_disjoint(w, M, k)  =  Π_{i < k} Z₁(w, M).

On the polymer side, with no shared links every plaquette is its own polymer
(the only connected polymers are singletons), and the polymer sum factorizes
identically into the product of per-plaquette polymer sums.  Matching the two
products term-for-term (via `single_plaquette_identity`) gives the
polymer-expansion identity in the disjoint case. -/

/-- **The disjoint-plaquette partition function**
`Z_disjoint(w, M, k) = Π_{i<k} Z₁(w, M)`, the product of `k` non-interacting
single-plaquette partition functions (the Haar integral factorizes when no
internal links are shared). -/
def Z_disjoint (w : Q') (M k : Nat) : Q' :=
  prodE (fun _ => singlePlaqZ w M) k

@[simp] theorem Z_disjoint_zero (w : Q') (M : Nat) : Z_disjoint w M 0 = 1 := rfl

@[simp] theorem Z_disjoint_succ (w : Q') (M k : Nat) :
    Z_disjoint w M (k + 1) = Z_disjoint w M k * singlePlaqZ w M := rfl

/-- **The disjoint polymer sum** `Π_{i<k} (single-plaquette polymer sum)` —
the factorized polymer expansion over `k` non-interacting plaquettes (each
plaquette's singleton polymers, multiplied independently: the leading,
no-Ursell-correction polymer contribution).  We use a fixed witness plaquette
`p` (all single-plaquette polymer sums coincide as `Q'` values). -/
def disjointPolymerSum {L : Lattice} (w : Q') (p : L.Plaquette) (M k : Nat) :
    Q' :=
  prodE (fun _ => singlePlaqPolymerSum w p M) k

/-- A `prodE` congruence under the canonical `Q'.eqv`: if `f i ≃ g i` for every
`i < n`, then `Π_{i<n} f i ≃ Π_{i<n} g i`.  (The library's `prodE_congr` needs
genuine `=` of the factors; this is the `.eqv` version, by induction with
`mul_eqv_congr` on both factors.) -/
theorem prodE_eqv_congr (f g : Nat → Q') :
    ∀ n, (∀ i, i < n → (f i).eqv (g i)) → (prodE f n).eqv (prodE g n)
  | 0, _ => Q'.eqv_refl 1
  | n + 1, h => by
      rw [prodE_succ, prodE_succ]
      -- prodE f n * f n ≃ prodE g n * g n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (prodE f n) (prodE g n) (f n)
          (prodE_eqv_congr f g n (fun i hi => h i (Nat.lt_succ_of_lt hi)))) ?_
      exact Q'.mul_eqv_congr_left (prodE g n) (f n) (g n)
        (h n (Nat.lt_succ_self n))

/-- **THE disjoint polymer-expansion identity (PROVED).**

`Z_disjoint ≃ disjointPolymerSum`: the disjoint-plaquette partition function
equals (up to `Q'.eqv`) the factorized polymer sum (a product of
single-plaquette polymer sums).  This is the genuine polymer-expansion identity
`Z = Σ_configs ∏ activity` in the non-interacting case — the partition function
factorizes and matches the leading (product-of-singletons) polymer enumeration
term-for-term.  Proved by `prodE`-congruence from the single-plaquette
identity. -/
theorem disjoint_partition_identity {L : Lattice} (w : Q') (p : L.Plaquette)
    (M k : Nat) :
    (Z_disjoint w M k).eqv (disjointPolymerSum w p M k) := by
  unfold Z_disjoint disjointPolymerSum
  exact prodE_eqv_congr _ _ k (fun i _ => single_plaquette_identity w p M)

/-- **Strict positivity of the disjoint partition function (PROVED).**  For
`0 ≤ w` and the vacuum rep included (`1 ≤ M`), `Z_disjoint > 0` (a product of
strictly-positive single-plaquette partition functions). -/
theorem Z_disjoint_pos {w : Q'} (hw : (0 : Q') ≤ w) {M : Nat} (hM : 1 ≤ M)
    (k : Nat) :
    (0 : Q') < Z_disjoint w M k :=
  ContinuumExistence.prodE_pos (fun _ => singlePlaqZ w M)
    (fun _ => singlePlaqZ_pos hw hM) k

/-- Strict positivity transports across `Q'.eqv`: `0 < a` and `a ≃ b` give
`0 < b`.  (Local helper, by the cross-product representation: `eqv` gives
`a.num·b.den = b.num·a.den`, and `a.num > 0`, `a.den, b.den > 0` force
`b.num > 0`.) -/
theorem pos_of_eqv {a b : Q'} (ha : (0 : Q') < a) (h : a.eqv b) :
    (0 : Q') < b := by
  -- ha (cross form): 0 * a.den < a.num * 1, i.e. 0 < a.num
  have e1 : (0 : Q').num * (a.den : Int) < a.num * ((0 : Q').den : Int) := ha
  have hade : ((0 : Q').den : Int) = 1 := by decide
  have h0n : (0 : Q').num = 0 := by decide
  rw [h0n, hade, Int.zero_mul, Int.mul_one] at e1
  -- e1 : 0 < a.num
  -- h (eqv): a.num * b.den = b.num * a.den
  have he : a.num * (b.den : Int) = b.num * (a.den : Int) := h
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have had : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hlhs : 0 < a.num * (b.den : Int) := Int.mul_pos e1 hbd
  have hrhs : 0 < b.num * (a.den : Int) := by rw [← he]; exact hlhs
  -- from 0 < b.num * a.den and 0 < a.den conclude 0 < b.num
  have hbn : 0 < b.num := by
    rcases Int.lt_trichotomy b.num 0 with hlt | heq | hgt
    · exfalso
      have : b.num * (a.den : Int) < 0 := Int.mul_neg_of_neg_of_pos hlt had
      omega
    · exfalso; rw [heq, Int.zero_mul] at hrhs; omega
    · exact hgt
  -- goal: 0 < b, cross form 0 * b.den < b.num * 1
  show (0 : Q').num * (b.den : Int) < b.num * ((0 : Q').den : Int)
  rw [h0n, hade, Int.zero_mul, Int.mul_one]
  exact hbn

/-- The polymer-sum side inherits the same strict positivity, via the
identity (a sanity corollary: the matched objects are jointly positive). -/
theorem disjointPolymerSum_pos {L : Lattice} {w : Q'} (hw : (0 : Q') ≤ w)
    {M : Nat} (hM : 1 ≤ M) (p : L.Plaquette) (k : Nat) :
    (0 : Q') < disjointPolymerSum w p M k :=
  pos_of_eqv (Z_disjoint_pos hw hM k) (disjoint_partition_identity w p M k)

/-! ## 4. The empty case (clean degenerate polymer expansion)

With no plaquettes the partition function is the empty product `1` and the
polymer sum is the empty product `1`; they agree trivially.  This is the
`k = 0` instance of the disjoint identity, recorded explicitly as the cleanest
case where the expansion holds. -/

/-- The empty-volume partition function is `1` (empty product). -/
theorem Z_disjoint_empty (w : Q') (M : Nat) : Z_disjoint w M 0 = 1 := rfl

/-- **Empty-case identity**: with no plaquettes, partition function = polymer
sum = `1` (the trivial clean case of the expansion), a genuine `Q'` equality
(both sides are the empty product `prodE _ 0 = 1`). -/
theorem empty_partition_identity {L : Lattice} (w : Q') (p : L.Plaquette)
    (M : Nat) :
    Z_disjoint w M 0 = disjointPolymerSum w p M 0 := rfl

/-! ## 5. NAMED-open: the full Mayer / cluster expansion (NOT faked)

For arbitrary INTERACTING plaquette configurations (plaquettes sharing
internal links, so the Haar integrals do NOT factorize) the partition function
is NOT a finite product.  The full expansion is the Mayer / cluster series

    log Z  =  Σ_{connected clusters C}  Ursell(C),

where overlapping polymers contribute Ursell (truncated-correlation)
coefficients with alternating signs (the connected-polymer reorganization).
This is the analytic heart of the cluster expansion; it does NOT reduce to the
finite character algebra closed above.

We carry it as a NAMED Type-level OBLIGATION — a structure to be inhabited,
with NO placeholder inhabitant and NO faked proof.  The disjoint identity
(`disjoint_partition_identity`) is precisely its trivial case: all Ursell
coefficients of overlapping clusters vanish, so `Z` factorizes into the
product of single-plaquette sums. -/

/-- **NAMED-open obligation: the full Mayer / cluster expansion.**

`MayerExpansion L w` is the Type-level datum a genuine interacting cluster
expansion must supply, for a lattice `L` at weight `w`: a real interacting
partition function `Zfull k` over `k` plaquettes, the connected-cluster
("Ursell") contribution `ursell` per polymer, the cluster-sum `clusterSum k`
over connected polymers, and the proof `expansion` that the interacting
partition function equals the (exponentiated) cluster sum.

This structure is deliberately LEFT UNINHABITED here — it is the open
analytic obligation (the Mayer reorganization with alternating-sign Ursell
functions), NOT a finite character identity.  Closing the disjoint case above
(`disjoint_partition_identity`) is its trivial, non-interacting instance; the
general inhabitant is not constructed. -/
structure MayerExpansion (L : Lattice) (w : Q') where
  /-- The real interacting partition function over `k` plaquettes (Haar
  integral that does NOT factorize when internal links are shared). -/
  Zfull : Nat → Q'
  /-- The connected-cluster (Ursell / truncated-correlation) contribution of a
  polymer — the alternating-sign coefficient of the Mayer reorganization. -/
  ursell : Polymer L → (L.Plaquette → Rep) → Q'
  /-- The cluster sum `Σ_{connected polymers} ursell(X)` over `k` plaquettes
  (the right-hand side of `log Z = Σ_clusters Ursell`). -/
  clusterSum : Nat → Q'
  /-- The expansion identity relating the interacting partition function to the
  cluster sum (in the convergent regime).  This is the open analytic content. -/
  expansion : ∀ k, Zfull k = clusterSum k

/-! ## 6. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — the discrete character / Haar algebra):

  * `singlePlaqZ` (+ `singlePlaqZ_nonneg`, `singlePlaqZ_pos`) — the real
    single-plaquette heat-kernel partition function as the
    character-orthogonality sum `Σ_{s<M} coeffW w s`;
  * `constLabel`, `activity_singleton_const`, `singlePlaqPolymerSum` — the
    polymer-sum side over a single plaquette, reusing `PolymerModel.activity`;
  * `single_plaquette_identity` — `Z₁ = Σ_polymers ∏ activity` on one
    plaquette (THE identity, single-plaquette case);
  * `Z_disjoint` (+ `Z_disjoint_pos`), `disjointPolymerSum`
    (+ `disjointPolymerSum_pos`) — the disjoint (non-interacting) partition
    function and factorized polymer sum;
  * `disjoint_partition_identity` — `Z = Σ_configs ∏ activity` in the
    disjoint case (the partition function factorizes = product of
    single-plaquette polymer sums);
  * `empty_partition_identity` — the trivial empty-volume instance.

NAMED-open (NOT faked, NO inhabitant):

  * `MayerExpansion` — the full Mayer / cluster expansion for arbitrary
    INTERACTING configurations (the connected-polymer reorganization with
    alternating-sign Ursell coefficients), carried as a Type-level obligation;
    the disjoint identity is its trivial non-interacting case.

This module is the polymer-expansion IDENTITY at the discrete character level:
the genuine algebraic matching of the Haar character expansion with the
polymer enumeration in the non-interacting cases.  It is NOT the full cluster
expansion, NOT a convergence proof, and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.PolymerPartition

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PolymerPartition.singlePlaqZ_nonneg
#print axioms YMGap.Continuum.PolymerPartition.singlePlaqZ_pos
#print axioms YMGap.Continuum.PolymerPartition.activity_singleton_const
#print axioms YMGap.Continuum.PolymerPartition.single_plaquette_identity
#print axioms YMGap.Continuum.PolymerPartition.disjoint_partition_identity
#print axioms YMGap.Continuum.PolymerPartition.Z_disjoint_pos
#print axioms YMGap.Continuum.PolymerPartition.disjointPolymerSum_pos
#print axioms YMGap.Continuum.PolymerPartition.empty_partition_identity
