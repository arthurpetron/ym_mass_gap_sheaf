/-
Loop 7 — the Kotecký–Preiss polymer-sum bound CARRIED BY THE GENUINE
lattice-animal count, retiring the fake `ClusterCount` dependency.

# What this module delivers (honest underclaim)

`Continuum/KPCriterion.lean` proves the KP criterion `kp_criterion_of_count`
CONDITIONAL on a `ClusterCountBound L p`.  Two inhabitants of that interface
exist in the tree:

  * `Continuum/ClusterCount.lean`'s `toyClusterCountBound` — the FAKE one:
    `animalCount n := ofNat (deg^(2n))` is free data with a constant
    `polymerToWalk := Walk.nil p` injection that never reads a polymer.
  * `Continuum/BddLatticeAnimal.lean`'s `clusterCountBound_of_bdd` — the
    GENUINE one: `animalCount n := |((codes n).map (decode p))|` is the real
    cardinality of an actual list of polymers produced by the real DFS
    `decode`, and `count_le` is the PROVED lattice-animal bound
    `animalCount n ≤ ((D+1)²)^n`.

This module instantiates `kp_criterion_of_count` on the GENUINE inhabitant
`zChainClusterCountBound` (the integer plaquette chain `zChain`, `D = 3`, so
`K = (D+1)² = 16`) at a concrete strong-coupling weight, and PROVES the KP
polymer-sum bound rests on the real animal count.

## The threshold arithmetic (the crux), computed not assumed

`kpRatio cc w r = cc.K · coeffW w r · eSurrogate` with, for `zChain`,
`cc.K = animalK zChain = ofNat ((3+1)·(3+1)) = 16` and `eSurrogate = 3`.
The fundamental EXCITED rep is `r = 1` (`Rep := Nat`); its coefficient is
`coeffW w 1 = dimQ 1 · w^{C₄(1)} = 2 · w³` (`coeffW_one`, `dimQ 1 = 2`,
`c4 1 = 1·3 = 3`).  Hence

    kpRatio (zChainClusterCountBound p) w 1  =  16 · (2 w³) · 3  =  96 · w³.

We pick `w = 1/6`.  Then `w³ = 1/216` and `96 · (1/216) = 96/216 = 4/9`, and
`4/9 ≤ 1/2` (cross-multiplied `4·2 = 8 ≤ 9 = 1·9`).  So

    kpRatio (zChainClusterCountBound p) (1/6) 1  =  4/9  ≤  1/2.    ✓

(The mission's slack check `coeffW w 1 = 2·(1/6)³ = 1/108 ≤ 1/96` is the same
inequality divided by `K·e = 48`.)  This concrete rational `≤` is decidable on
`Q'` via the `Int` cross-product (`Q'.le`), kept axiom-clean (`decide` on a
pure decidable `Q'` proposition; no `Classical`/`Decidable` leak).

## What this is, and what it is NOT

This is FINITE-VOLUME STRONG-COUPLING combinatorics at a CONCRETE weight
`w = 1/6` on a 1D plaquette chain: the KP geometric polymer sum converges
(`≤ 2`) using the GENUINE `|enumPolys|` cardinality, not the `deg^{2n}` free
data, not a posited interface.  It supersedes any KP bound resting on
`ClusterCount.toyClusterCountBound`.

It is NOT a uniform-in-`w` statement, NOT the continuum (`a → 0`) limit, NOT
a multi-plaquette correlator, and NOT the 4D Yang–Mills mass gap.  The genuine
upper-bound (over-count) anchoring of `animalCount` against the TRUE polymer
count remains the named `BddLatticeAnimal.DecodeComplete` obligation
(`count_le`, the field the criterion consumes, does not need it).

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props.  No `sorry` / `admit`
/ new `axiom`.  All witnesses are `Type`-level data; the count is a real
cardinality, never invented.
-/

import YMGap.Continuum.KPCriterion
import YMGap.Continuum.BddLatticeAnimal

namespace YMGap.Continuum.GenuineKP

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.BddLatticeAnimal

/-! ## 1. The concrete strong-coupling weight and the fundamental excited rep -/

/-- The concrete strong-coupling weight `w = 1/6` (well inside the
`coeffW_succ_ratio` regime `0 ≤ w ≤ 1/2`).  At this weight the `zChain`
KP ratio for the fundamental excited rep is exactly `4/9 ≤ 1/2`. -/
def gw : Q' := Q'.mkPos 1 6 (by decide)

theorem gw_nonneg : (0 : Q') ≤ gw := by decide

/-- The fundamental EXCITED representation index `r = 1` (`Rep := Nat`,
the doubled spin `s = 1`), whose activity coefficient is
`coeffW w 1 = dimQ 1 · w^{C₄(1)} = 2 w³` (`coeffW_one`). -/
def gr : Rep := 1

/-! ## 2. The threshold arithmetic (the crux — PROVED by computation)

`kpRatio (zChainClusterCountBound p) gw gr = 16 · (2·(1/6)³) · 3 = 96/216 =
4/9 ≤ 1/2`.  `kpRatio` and `coeffW`/`qpow`/`animalK` are all closed-form
rational expressions at the concrete `gw`, `gr`, so the inequality reduces to a
decidable `Int` cross-product on `Q'`. -/

/-- The leading activity coefficient at `w = 1/6` is `coeffW (1/6) 1 = 2·(1/6)³
= 1/108` (`= 2/216`).  Computed, not assumed (`coeffW w 1 = 2 w³`). -/
theorem coeffW_gw_gr : coeffW gw gr = Q'.mkPos 2 216 (by decide) := by decide

/-- **The strong-coupling threshold (the crux — PROVED).**

    kpRatio (zChainClusterCountBound p) gw gr  ≤  1/2.

Concretely `16 · (2·(1/6)³) · 3 = 96·(1/216) = 4/9 ≤ 1/2`.  The value of
`kpRatio` does NOT depend on `p` (it reads only `cc.K = animalK zChain = 16`
and `coeffW gw gr`, both `p`-independent), so the bound holds for every
plaquette `p` of the chain.  Decidable on `Q'` via the `Int` cross-product,
axiom-clean. -/
theorem genuine_threshold (p : zChain.toLattice.Plaquette) :
    kpRatio (zChainClusterCountBound p) gw gr ≤ Q'.mkPos 1 2 (by decide) := by
  -- `kpRatio cc w r = cc.K · coeffW w r · eSurrogate`; for `zChain`,
  -- `cc.K = animalK zChain` is `p`-independent, so the ratio is the closed,
  -- `p`-free rational `animalK zChain · coeffW gw gr · eSurrogate`.
  show animalK zChain * coeffW gw gr * eSurrogate ≤ Q'.mkPos 1 2 (by decide)
  decide

/-! ## 3. The genuine KP polymer-sum bound (PROVED)

Apply `kp_criterion_of_count` to the GENUINE `zChainClusterCountBound` with the
proved threshold.  The resulting geometric sum bound `≤ 2` therefore rests on
the real `|enumPolys|` animal cardinality (`count_le = animalCount_le_pow`),
not on the fake `deg^{2n}` free data. -/

/-- **`genuineKP_sum_le_two` (the genuine KP polymer-sum bound — PROVED).**

For every plaquette `p` of the chain and every truncation `N`, the collapsed
KP geometric sum over the fundamental excited rep, weighted by the GENUINE
animal count `animalCount = |enumPolys|`, is bounded by `2`:

    ∑_{n < N}  animalCount(zChain,p,n) · (coeffW (1/6) 1)^n · 3^n  ≤  2.

PROOF.  `kp_criterion_of_count` applied to `zChainClusterCountBound p`
(`count_le = animalCount_le_pow`, the proved lattice-animal bound on the real
list length) with `gw_nonneg` and the proved threshold `genuine_threshold p`.
The `kpTerm` here unfolds to
`cc.animalCount n · (coeffW gw gr)^n · eSurrogate^n` with
`cc.animalCount = BddLatticeAnimal.animalCount zChain p` — the genuine
cardinality of `(codes zChain n).map (decode zChain p)`. -/
theorem genuineKP_sum_le_two (p : zChain.toLattice.Plaquette) (N : Nat) :
    finSum (fun n => kpTerm (zChainClusterCountBound p) gw gr n) N
      ≤ Q'.ofNat 2 :=
  kp_criterion_of_count (zChainClusterCountBound p) gw_nonneg gr
    (genuine_threshold p) N

/-! ## 4. Non-vacuity / honesty: the count is the genuine cardinality, and the
animal class is non-empty.

We confirm (a) that the `animalCount` field powering `genuineKP_sum_le_two` is
DEFINITIONALLY the `BddLatticeAnimal.animalCount` cardinality
(`|enumPolys|`), via the proved `enumPolys_length` exact code count; and
(b) that the `zChain` animal class is genuinely inhabited — the singleton
`[p]` is a real connected size-`1` animal through `p`. -/

/-- **The count is the genuine cardinality (witness).**  The `animalCount`
field of `zChainClusterCountBound p` — the very count `genuineKP_sum_le_two`
sums against — is, at every `n`, the length of the actual decoded-polymer list
`enumPolys zChain p n = (codes zChain n).map (decode zChain p)`, equal to the
exact code count `(3+1)^(2(n-1)) = 4^(2(n-1))`.  This is NOT free data: it is a
real list cardinality (cf. `BddLatticeAnimal.enumPolys_length`). -/
theorem genuine_count_is_cardinality (p : zChain.toLattice.Plaquette) (n : Nat) :
    (zChainClusterCountBound p).animalCount n
      = Q'.ofNat ((enumPolys zChain p n).length) := rfl

/-- The genuine `count_le` field is the proved lattice-animal bound (`K = 16`,
`animalCount n ≤ 16^n`), not a posited inequality.  Recorded to make explicit
that `genuineKP_sum_le_two` consumes the REAL bound. -/
theorem genuine_count_le (p : zChain.toLattice.Plaquette) (n : Nat) :
    (zChainClusterCountBound p).animalCount n ≤ (zChainClusterCountBound p).K ^ n :=
  (zChainClusterCountBound p).count_le n

/-- **Non-vacuity witness: the animal class is inhabited.**  The singleton
`[p]` is a genuine connected size-`1` lattice animal through `p` on `zChain`
(`size = 1`, `p ∈ [p]`, `Nodup`, internally connected via
`connectedIn_singleton`).  So the count `genuineKP_sum_le_two` sums against is
over a NON-EMPTY animal class — the bound is not vacuous. -/
theorem zChain_animal_nonempty (p : zChain.toLattice.Plaquette) :
    IsClusterThrough zChain p 1 [p] :=
  ⟨rfl, List.mem_cons_self,
   List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
   ⟨connectedIn_singleton p⟩⟩

/-! ## 5. Documentation: PROVED, and the supersession (AGENTS.md Rule 6)

PROVED in this module, axiom-clean (`[propext]` / `[propext, Quot.sound]`):

  * `coeffW_gw_gr` — `coeffW (1/6) 1 = 1/108` (the computed leading coefficient);
  * `genuine_threshold` — `kpRatio (zChainClusterCountBound p) (1/6) 1 = 4/9 ≤
    1/2` (the strong-coupling crux, computed not assumed);
  * `genuineKP_sum_le_two` — the KP geometric polymer-sum bound `≤ 2` resting on
    the GENUINE `|enumPolys|` animal count (`count_le = animalCount_le_pow`);
  * `genuine_count_is_cardinality` / `genuine_count_le` — the count is the real
    list cardinality and the bound is the proved lattice-animal bound;
  * `zChain_animal_nonempty` — the animal class is inhabited (non-vacuity).

SUPERSESSION (honest).  `genuineKP_sum_le_two` supersedes any KP bound resting
on `ClusterCount.toyClusterCountBound` (whose `animalCount = ofNat(deg^{2n})`
is free data with a polymer-blind `Walk.nil p` injection).  The genuine path —
`BddLatticeAnimal.clusterCountBound_of_bdd` / `zChainClusterCountBound` — is now
the canonical instantiation of `kp_criterion_of_count`.  `ClusterCount.lean` is
retained (downstream imports) but its inhabitant is deprecation-bannered; the
genuine count is the one used here.

SCOPE (underclaim).  Finite-volume strong-coupling combinatorics at the
concrete weight `w = 1/6` on the 1D plaquette chain.  NOT uniform-in-`w`, NOT
the continuum (`a → 0`) limit, NOT a multi-plaquette correlator, NOT the 4D
Yang–Mills mass gap.  The genuine over-count of the TRUE polymer count remains
the named `BddLatticeAnimal.DecodeComplete` obligation (the `count_le` field
this module consumes does not depend on it). -/

end YMGap.Continuum.GenuineKP

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GenuineKP.coeffW_gw_gr
#print axioms YMGap.Continuum.GenuineKP.genuine_threshold
#print axioms YMGap.Continuum.GenuineKP.genuineKP_sum_le_two
#print axioms YMGap.Continuum.GenuineKP.genuine_count_is_cardinality
#print axioms YMGap.Continuum.GenuineKP.genuine_count_le
#print axioms YMGap.Continuum.GenuineKP.zChain_animal_nonempty
