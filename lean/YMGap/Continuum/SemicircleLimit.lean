/-
# The semicircle Riemann limit at the CReal-level completeness interface

This module assembles the unconditional convergence of the rational semicircle
Riemann sums `seqSemi n = semiSum (n+1)` of `√(1 − x²)` at the CReal-level
(eventual-in-approx) completeness interface `CReal.ModCauchyEv` /
`CReal.completeLimitCauchy`.

## The two ingredients and the one residual

The completeness datum `ModCauchyEv seqSemi` has three pieces of content:

  1. **The index-indexed inner regularity modulus** — DISCHARGED upstream
     (`SemicircleInnerModulus.seqSemi_regularIdx` /
     `seqSemi_uniformInnerModulusIdx`): the per-term Cauchy modulus, with the
     growing `(i+1)` term count absorbed by the weight `2/(i+1)`.

  2. **The antitone outer modulus + the EVENTUAL outer two-sided bound** — the
     inter-resolution Riemann estimate.  At the CReal-level interface this is the
     genuine Bishop-Cauchy form

         ∀ ε>0, ∀ m,n ≥ M ε, ∃ K, ∀ k ≥ K,
           |(seqSemi m).approx k − (seqSemi n).approx k| ≤ ε,

     i.e. `|semiSum (m+1) − semiSum (n+1)| ≤ ε` as constructive reals.  This is
     the EVENTUAL-in-`k` form, NOT the all-`k` form: it matches the natural
     √-Hölder Riemann mesh estimate (which controls the LIMITS of the two Riemann
     sums, eventual in the approximation index), and so avoids the all-`k`
     delicacy near the integrand's slow points (`heronSeq` of `√` of a near-zero
     radicand is a crude rational at small `k`).  The per-cell input is the proved
     √-Hölder bound `SemicircleConverge.nodeWeight_holder`; the residual is the
     cell-matching combinatorics assembling it into the inter-resolution sum
     estimate.  It is carried as the named datum `InterResBound`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `InterResBound` — the precise eventual-outer inter-resolution residual,
    packaged as `Type`-level data (an outer modulus `M`, a per-pair approximation
    threshold `boundK`, the eventual two-sided bound, and antitonicity of `M`).
    This is exactly the `ModCauchyEv` outer datum for `seqSemi`.
  * `semiModCauchyEv : InterResBound → ModCauchyEv seqSemi` — the ASSEMBLY of the
    completeness datum from the proved inner modulus (Loop 21) and the
    inter-resolution outer bound.  The inner-modulus residual is GONE; only the
    outer inter-resolution bound remains, and at the EASIER CReal-level interface.
  * `semiIntEv : InterResBound → CReal` — the genuine limit
    `completeLimitCauchy seqSemi (semiModCauchyEv irb)`.
  * `semiIntEv_converges` — the limit IS the limit of the Riemann sums.
  * `semiIntEv_nonneg` / `semiIntEv_leRat_two` — the proved per-`n` enclosure
    `0 ≤ seqSemi n ≤ 2` PASSES TO THE LIMIT (unconditional, given `irb`),
    mirroring `SemicircleIntegral.semiInt_nonneg` / `semiInt_leRat_two`.

## What remains (the single residual)

  * `InterResBound` — the inter-resolution Riemann estimate at the CReal-level
    (eventual-in-`k`) interface.  Strictly EASIER than the prior all-`k`
    `SemicircleConverge.UniformRiemannBound`: the eventual form is the natural
    √-Hölder Riemann statement.  Its per-cell input (`nodeWeight_holder`) is
    proved; the cell-matching combinatorics (common refinement of the two
    rational meshes `2/(m+1)`, `2/(n+1)`) is the residual.

## Path for the general integrand `U_a·U_b·R`

The SAME assembly works for `RiemannConverge`: replace the integrand `√(1−x²)`
by `U_a(x)·U_b(x)·√(1−x²)` (the Chebyshev-U product is a `QPoly` at the rational
node).  The inner modulus is the product modulus (QPoly Lipschitz + the proved
√ modulus); the eventual-outer inter-resolution bound is the same cell-matching
machinery with the per-cell modulus enlarged by the QPoly Lipschitz factor.  The
CReal-level completeness backbone (`completeLimitCauchy`) is integrand-agnostic.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  PROVED: the completeness-datum assembly from the proved inner
modulus + the inter-resolution outer datum, and the limit/converges/nonneg/`≤ 2`
passes.  NAMED-open: the single residual `InterResBound` (the CReal-level
inter-resolution Riemann estimate).  Axiom-gate: `[propext]` / `[propext,
Quot.sound]`.
-/

import YMGap.Continuum.SemicircleInnerModulus
import YMGap.Constructive.CRealCompleteCauchy

namespace YMGap.Continuum.SemicircleLimit

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleConverge
open YMGap.Continuum.SemicircleInnerModulus

/-! ## 1. The inter-resolution residual (the eventual-outer datum)

This is the single remaining residual for unconditional semicircle convergence,
stated at the CReal-level (eventual-in-`k`) completeness interface — the form the
natural √-Hölder Riemann estimate delivers.  It packages exactly the
`ModCauchyEv.M` / `ModCauchyEv.boundK` / `ModCauchyEv.bound` / `ModCauchyEv.Mmono`
fields for `seqSemi`.  Type-level data (AGENTS.md Rule 8). -/

/-- **The inter-resolution Riemann residual (eventual-outer form).**

A resolution threshold `M : Q' → Nat` (antitone) together with a per-pair
approximation threshold `boundK` such that for `m, n ≥ M ε` the Riemann sums
`seqSemi m`, `seqSemi n` agree to within `ε` for every approximation index
`k ≥ boundK ε m n` — the genuine Bishop-Cauchy (eventual-in-`k`) statement that
the Riemann sequence is `CReal`-Cauchy.  Its per-cell input is the proved
√-Hölder bound `SemicircleConverge.nodeWeight_holder`; the residual is the
cell-matching combinatorics.  EASIER than the all-`k`
`SemicircleConverge.UniformRiemannBound`. -/
def InterResBound : Type :=
  Σ' M : Q' → Nat,
    Σ' boundK : Q' → Nat → Nat → Nat,
      (∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, M ε ≤ m → M ε ≤ n →
        ∀ k : Nat, boundK ε m n ≤ k →
          (seqSemi m).approx k ≤ (seqSemi n).approx k + ε
            ∧ (seqSemi n).approx k ≤ (seqSemi m).approx k + ε)
      ∧ (∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ)

/-! ## 2. The completeness-datum assembly

`ModCauchyEv seqSemi` from the proved index-indexed inner modulus (Loop 21) and
the inter-resolution outer datum.  The inner-modulus residual is DISCHARGED; only
the outer datum `InterResBound` is supplied. -/

/-- **The eventual-outer modulus-Cauchy datum for `seqSemi`**, assembled from the
proved index-indexed inner regularity modulus
(`SemicircleInnerModulus.seqSemiReg` / `seqSemi_regularIdx`) and the
inter-resolution outer datum `irb : InterResBound`. -/
def semiModCauchyEv (irb : InterResBound) : CReal.ModCauchyEv seqSemi where
  M := irb.1
  reg := seqSemiReg
  boundK := irb.2.1
  bound := irb.2.2.1
  regular := fun i ε hε p qq hp hqq => seqSemi_regularIdx i ε hε p qq hp hqq
  Mmono := irb.2.2.2

/-! ## 3. The genuine semicircle integral (CReal-level limit) -/

/-- **The semicircle integral** `∫_{−1}^1 √(1−x²)` as a constructive real, GIVEN
the inter-resolution residual `irb : InterResBound`.  Built by the CReal-level
completeness backbone `CReal.completeLimitCauchy` (the index-absorbing diagonal of
the eventual-outer modulus-Cauchy datum).  The inner-modulus residual is gone;
this is the genuine limit modulo the single outer inter-resolution bound. -/
def semiIntEv (irb : InterResBound) : CReal :=
  CReal.completeLimitCauchy seqSemi (semiModCauchyEv irb)

/-- **The limit IS the limit of the Riemann sums** (`ConvergesTo`). -/
theorem semiIntEv_converges (irb : InterResBound) :
    CReal.ConvergesTo seqSemi (semiIntEv irb) :=
  CReal.convergesTo_completeLimitCauchy seqSemi (semiModCauchyEv irb)

/-! ## 4. The enclosure passes to the limit -/

/-- **`semiIntEv ≥ 0`** — the limit of the proved-nonneg Riemann sums is `≥ 0`.
Mirrors `SemicircleIntegral.semiInt_nonneg`: at scale `ε`, work at `q = ½ε`; the
convergence gives a term `seqSemi Nstage` within `q` of the limit, and the
per-term eventual nonnegativity gives `0 ≤ (seqSemi Nstage).approx n + q`;
chaining and collapsing `q + q ≤ ε` yields `geRat (semiIntEv) 0`. -/
theorem semiIntEv_nonneg (irb : InterResBound) :
    ExpPos.geRat (semiIntEv irb) 0 := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := semiIntEv_converges irb (HalfPow.half * ε) hq
  obtain ⟨Napx, hbound⟩ := hstage Nstage (Nat.le_refl _)
  obtain ⟨Mge, hge⟩ := seqSemi_nonneg Nstage (HalfPow.half * ε) hq
  refine ⟨max Napx Mge, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Mge ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hA : (0 : Q') ≤ (seqSemi Nstage).approx n + HalfPow.half * ε := hge n hn2
  have hB : (seqSemi Nstage).approx n ≤ (semiIntEv irb).approx n + HalfPow.half * ε :=
    (hbound n hn1).1
  have hchain : (0 : Q') ≤ ((semiIntEv irb).approx n + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hA (Q'.add_le_add_right _ _ (HalfPow.half * ε) hB)
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv ((semiIntEv irb).approx n) (HalfPow.half * ε) (HalfPow.half * ε)))
    ?_
  refine Q'.add_le_add_left _ (HalfPow.half * ε + HalfPow.half * ε) ε ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves ε)

/-- **`semiIntEv ≤ 2`** — the limit of the proved `≤ 2` Riemann sums is `≤ 2`.
Dual of `semiIntEv_nonneg` (mirrors `SemicircleIntegral.semiInt_leRat_two`). -/
theorem semiIntEv_leRat_two (irb : InterResBound) :
    CReal.leRat (semiIntEv irb) (2 : Q') := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := semiIntEv_converges irb (HalfPow.half * ε) hq
  obtain ⟨Napx, hbound⟩ := hstage Nstage (Nat.le_refl _)
  obtain ⟨Mle, hle⟩ := seqSemi_leRat_two Nstage (HalfPow.half * ε) hq
  refine ⟨max Napx Mle, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Mle ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hB : (semiIntEv irb).approx n ≤ (seqSemi Nstage).approx n + HalfPow.half * ε :=
    (hbound n hn1).2
  have hA : (seqSemi Nstage).approx n ≤ (2 : Q') + HalfPow.half * ε := hle n hn2
  have hchain : (semiIntEv irb).approx n ≤ ((2 : Q') + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hB (Q'.add_le_add_right _ _ (HalfPow.half * ε) hA)
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv (2 : Q') (HalfPow.half * ε) (HalfPow.half * ε)))
    ?_
  refine Q'.add_le_add_left _ (HalfPow.half * ε + HalfPow.half * ε) ε ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves ε)

end YMGap.Continuum.SemicircleLimit

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `InterResBound` — the precise CReal-level (eventual-in-`k`) inter-resolution
    Riemann residual, `Type`-level data; exactly the `ModCauchyEv` outer datum.
  * `semiModCauchyEv` — the completeness-datum assembly from the PROVED
    index-indexed inner modulus (Loop 21: `seqSemiReg` / `seqSemi_regularIdx`)
    and the inter-resolution outer datum.  The inner-modulus residual is
    discharged; only the outer datum is supplied.
  * `semiIntEv` / `semiIntEv_converges` — the genuine CReal-level limit and its
    convergence certificate (the diagonal of the eventual-outer modulus-Cauchy
    datum, `CReal.completeLimitCauchy`).
  * `semiIntEv_nonneg` / `semiIntEv_leRat_two` — the proved per-`n` enclosure
    `0 ≤ seqSemi n ≤ 2` PASSED TO THE LIMIT.

**NAMED-open (the single residual).**
  * `InterResBound` — the inter-resolution Riemann estimate at the EASIER
    CReal-level (eventual-in-`k`) interface (vs. the all-`k`
    `SemicircleConverge.UniformRiemannBound`).  Per-cell input
    `SemicircleConverge.nodeWeight_holder` is PROVED; the residual is the
    cell-matching common-refinement combinatorics for the two rational meshes.

So semicircle convergence is UNCONDITIONAL modulo the single CReal-level
inter-resolution residual `InterResBound`; the inner-modulus residual and the
all-`k` delicacy are both eliminated.  The general U-orthogonality integrand
`U_a·U_b·√(1−x²)` reuses the SAME assembly (integrand-agnostic backbone, product
inner modulus, enlarged per-cell modulus).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.SemicircleLimit.semiModCauchyEv
#print axioms YMGap.Continuum.SemicircleLimit.semiIntEv_converges
#print axioms YMGap.Continuum.SemicircleLimit.semiIntEv_nonneg
#print axioms YMGap.Continuum.SemicircleLimit.semiIntEv_leRat_two
