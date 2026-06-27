/-
Track B — a GENUINE, NON-CIRCULAR tie of the REAL Wilson connected correlator to
the abstract clustering rate, by DOMINATION (not by definitional reflexivity).

# Why this module exists (what it de-fakes)

`Continuum/UniformClusterFromKP.lean` carries `RealCorrelatorLink` whose
`matches_abstract` demands a termwise `eqv` to the ABSTRACT one-mode correlator
`corr (gapModel Λ) n = (sep Λ)^n`.  The only existing inhabitant
(`WilsonCorrelator.genuineRealCorrelatorLink`) is CIRCULAR: its `wilsonCorr` is
DEFINED to be `corr (wilsonSpectralModel Λ)`, which carries the SAME spectral
data as `gapModel Λ`, so `matches_abstract` is `eqv_refl` over a definitional
coincidence.  The real object (the SU(2) character double-sum `wilsonG`) never
appears.

This module ties the GENUINE real object instead.  The genuine connected
correlator is `WilsonConnCorr.wilsonG` — a vacuum-subtracted SU(2)-character
DOUBLE-sum (NOT defined to equal any abstract `corr`), with the PROVED single-rep
collapse `wilsonG_collapse` and the PROVED geometric decay `wilsonG_decay`
(rate `ρ = 2w³`).  We use the single-excited-rep chain `wilsonG w 2 n`
(`M + 1 = 2`, one common excited rep `r = 1` along the chain of `n + 1`
plaquettes), whose decay is `wilsonG w 2 n ≤ ρ^{n+1}`, derived from
`wilsonG_decay` (NOT posited).

# The crux: `eqv` is too strong, DOMINATION is the honest tie

The abstract one-mode model is indexed by VOLUME `Λ` and decays at the located
separator `sep Λ` (`corr (gapModel Λ) n = (sep Λ)^n`).  The genuine `wilsonG` is
indexed by CHAIN-LENGTH and decays at `ρ = 2w³`.  These are DIFFERENT models with
DIFFERENT rates; they do NOT coincide termwise by `eqv`.  So a literal genuine
inhabitant of `RealCorrelatorLink` (which demands `eqv`) is BLOCKED — the only way
to make `eqv` hold is the circular definition this module exists to remove.

What DOES hold genuinely is DOMINATION: the real correlator is bounded ABOVE by
the abstract one, hence clusters at least as fast.  The two arithmetic facts that
make this work are PROVED here:

  * `sep_ge_eighth : 1/8 ≤ sep Λ`  — the abstract separator has a positive floor
    (`margin Λ ≤ 7/8`, so `sep Λ = 1 − margin Λ ≥ 1/8`);
  * `rho_le_eighth : ρ ≤ 1/8`  at strong coupling `0 ≤ w ≤ 1/4`
    (`ρ = 2w³ ≤ 2·(1/4)³ = 1/32 ≤ 1/8`).

Together: `ρ ≤ 1/8 ≤ sep Λ`, so `ρ ≤ sep Λ` UNCONDITIONALLY in Λ (at
`0 ≤ w ≤ 1/4`).  Combined with `ρ ≤ 1` this gives, for the single-excited-rep
chain,

    realCorr Λ n  :=  wilsonG w 2 n  ≤  ρ^{n+1}  ≤  ρ·(sep Λ)^n  ≤  (sep Λ)^n
                   =  corr (gapModel Λ) n,

the genuine domination — every step from a PROVED fact about the real `wilsonG`
double-sum, none from a definitional coincidence.

# The honest deliverable (per the loop charter)

  * `RealCorrelatorDomination` — a NEW weaker named structure (fields `realCorr`
    and `dominated : ∀ Λ n, realCorr Λ n ≤ corr (gapModel Λ) n`).  This is the
    honest tie: the real correlator is DOMINATED BY (not equal to) the abstract
    one, so it clusters at least as fast.
  * `genuineCorrDomination w hw0 hw : RealCorrelatorDomination` — the GENUINE
    inhabitant: `realCorr Λ n := wilsonG w 2 n` (the genuine single-excited-rep
    character double-sum, INDEPENDENT of Λ — the real object does not depend on
    the abstract volume index), and `dominated` is DERIVED from `wilsonG_decay`
    + `rho_le_sep` + `ρ ≤ 1`.  NOT `eqv_refl`, NOT a definitional coincidence.
  * `genuineCorrDomination_cluster` — `realCorr Λ n ≤ (sep Λ)^n`, the abstract
    clustering rate now provably bounding the REAL correlator.

# Honest scope / what stays open

This is the SINGLE-LINE connecting-chain geometry at ONE excited rep (the chain
`wilsonG w 2 n` whose collapse is the genuine single-rep chain `ρ^{n+1}`).  The
FULL interacting multi-plaquette correlator remains the separate named wall
(`WilsonConnCorr.WilsonGMatchesAbstract` for the general geometry).  And the tie
here is DOMINATION, not exact `eqv` — exact `eqv` is genuinely false (different
models / rates); domination is the honest content.  The circular
`WilsonCorrelator.genuineRealCorrelatorLink` is SUPERSEDED for the clustering
CONCLUSION (which is all the cluster bound consumes): the real `wilsonG`
double-sum is now genuinely shown to cluster at the abstract rate WITHOUT defining
it equal to the abstract `corr`.

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` arithmetic, the reused PROVED `wilsonG_decay`,
`wilsonG_collapse`, `pow_le_pow_of_le`, and the monotonicity lemmas.  No
`Classical.*`, no `Real`, no `native_decide`, no `decide` on non-decidable props,
no `sorry` / `admit` / new `axiom`, no `Prop := True`.  `realCorr` is the genuine
`wilsonG` double-sum; the domination is DERIVED from the proved decay, NOT from
defining things equal.  Witnesses are `Type`-level data.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.WilsonConnCorr
import YMGap.Continuum.TransferCorr
import YMGap.Continuum.UniformClusterFromKP

namespace YMGap.Continuum.GenuineCorrLink

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.UniformClusterFromKP
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport

/-! ## 1. The abstract separator has a positive floor `sep Λ ≥ 1/8`

`margin Λ ≤ 7/8` (`UniformClusterFromKP.margin_le`), so
`sep Λ = 1 − margin Λ ≥ 1 − 7/8 = 1/8`.  This is the Λ-independent floor of the
abstract clustering rate — the thing that lets the genuine `ρ` be dominated. -/

/-- The common floor value `1/8` (the heat-kernel separator `w³` at `w = 1/2`, and
the floor of the abstract `sep Λ`). -/
def eighth : Q' := Q'.mkPos 1 8 (by decide)

/-- **The abstract separator floor (PROVED).**  `1/8 ≤ sep Λ` for every volume
`Λ`: from `margin Λ ≤ 7/8` and `sep Λ = 1 − margin Λ`.  The num-level identity
`(1 − margin).num = margin.den − margin.num` (mirrors `sep_nonneg`). -/
theorem sep_ge_eighth (Λ : Nat) : eighth ≤ sep Λ := by
  -- margin Λ ≤ 7/8.
  have hm : margin Λ ≤ Q'.mkPos 7 8 (by decide) := margin_le Λ
  -- num-level: margin.num · 8 ≤ 7 · margin.den.
  have hmnum : (margin Λ).num * (8 : Int) ≤ (7 : Int) * ((margin Λ).den : Int) := by
    have h : (margin Λ).num * ((Q'.mkPos 7 8 (by decide)).den : Int)
           ≤ (Q'.mkPos 7 8 (by decide)).num * ((margin Λ).den : Int) := hm
    have hn : (Q'.mkPos 7 8 (by decide)).num = 7 := rfl
    have hd : ((Q'.mkPos 7 8 (by decide)).den : Int) = 8 := rfl
    rw [hn, hd] at h; exact h
  -- goal: eighth ≤ sep Λ = 1 − margin Λ = 1 + -(margin Λ).
  show eighth ≤ (1 : Q') - margin Λ
  show eighth ≤ (1 : Q') + -(margin Λ)
  -- num-level: eighth.num · (1+-margin).den ≤ (1+-margin).num · eighth.den.
  show (eighth.num) * (((1 : Q') + -(margin Λ)).den : Int)
      ≤ ((1 : Q') + -(margin Λ)).num * (eighth.den : Int)
  -- (1 + -margin).num = margin.den − margin.num ; .den = margin.den.
  have hnum : ((1 : Q') + -(margin Λ)).num
      = ((margin Λ).den : Int) - (margin Λ).num := by
    show (1 : Q').num * ((margin Λ).den : Int)
        + (-(margin Λ)).num * ((1 : Q').den : Int)
        = ((margin Λ).den : Int) - (margin Λ).num
    have hon : (1 : Q').num = 1 := rfl
    have hod : ((1 : Q').den : Int) = 1 := rfl
    have hneg : (-(margin Λ)).num = -(margin Λ).num := rfl
    rw [hon, hod, hneg]; omega
  have hden : (((1 : Q') + -(margin Λ)).den : Int) = ((margin Λ).den : Int) := by
    show ((1 * (margin Λ).den : Nat) : Int) = ((margin Λ).den : Int)
    push_cast; omega
  have hen : eighth.num = 1 := rfl
  have hed : (eighth.den : Int) = 8 := rfl
  rw [hnum, hden, hen, hed]
  -- 1 · margin.den ≤ (margin.den − margin.num) · 8, i.e. margin.den ≤ 8·margin.den − 8·margin.num.
  -- From hmnum: 8·margin.num ≤ 7·margin.den ⟹ 8·(den−num) ≥ 8den−7den = den.
  omega

/-! ## 2. The genuine geometric rate is below the floor `ρ ≤ 1/8`

`ρ = coeffW w 1 = 2w³` (`WilsonConnCorr.rho`).  At strong coupling
`0 ≤ w ≤ 1/4`, `ρ = 2w³ ≤ 2·(1/4)³ = 2/64 = 1/32 ≤ 1/8`.  (Mirrors
`WilsonConnCorr.rho_le_quarter`, tightened to `1/8` under the stronger
`w ≤ 1/4`.) -/

/-- The strong-coupling threshold `w₀ = 1/4` for the domination (tighter than the
`1/2` used for `ρ ≤ 1/4`). -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- **`ρ ≤ 1/8` (PROVED).**  At strong coupling `0 ≤ w ≤ 1/4`,
`ρ = coeffW w 1 = dimQ 1 · w³ = 2w³ ≤ 2·(1/4)³ = 1/32 ≤ 1/8`.  Monotone in `w`
via `heatKernelSep_mono`, then a concrete `decide` at `w = 1/4`. -/
theorem rho_le_eighth {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ quarter) :
    rho w ≤ eighth := by
  unfold rho
  rw [coeffW_one_eq w]
  -- dimQ 1 · w³ ≤ dimQ 1 · (1/4)³ = 2 · 1/64 = 1/32 ≤ 1/8
  have hsep : heatKernelSep w ≤ heatKernelSep quarter := heatKernelSep_mono hw0 hw
  have hstep : dimQ 1 * heatKernelSep w ≤ dimQ 1 * heatKernelSep quarter :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsep (dimQ_nonneg 1)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- dimQ 1 · (1/4)³ = 2 · 1/64 = 1/32 ≤ 1/8, decidable
  show dimQ 1 * heatKernelSep quarter ≤ eighth
  decide

/-- **`ρ ≤ sep Λ` (PROVED, UNIFORM IN Λ).**  The genuine geometric rate is
dominated by the abstract separator at EVERY volume: `ρ ≤ 1/8 ≤ sep Λ` at strong
coupling `0 ≤ w ≤ 1/4`.  This is the key quantitative verdict: the real
correlator's decay rate `ρ` never exceeds the abstract clustering rate `sep Λ`. -/
theorem rho_le_sep {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ quarter) (Λ : Nat) :
    rho w ≤ sep Λ :=
  Q'.le_trans' _ _ _ (rho_le_eighth hw0 hw) (sep_ge_eighth Λ)

/-- `ρ ≤ 1` (the per-step factor is sub-unital): `ρ ≤ 1/8 ≤ 1`. -/
theorem rho_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ quarter) :
    rho w ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (rho_le_eighth hw0 hw) (by decide)

/-- `0 ≤ ρ`. -/
theorem rho_nonneg' {w : Q'} (hw0 : (0 : Q') ≤ w) : (0 : Q') ≤ rho w :=
  WilsonConnCorr.rho_nonneg hw0

/-! ## 3. The single-excited-rep chain `wilsonG w 2 n` and its decay `≤ ρ^{n+1}`

`wilsonG w 2 n = wilsonG w (1 + 1) n` is the genuine character double-sum at
`M + 1 = 2` (vacuum row `a = 0` plus the single excited rep `r = 1`).  Its proved
decay (`wilsonG_decay` at `M = 1`) is `wilsonG w 2 n ≤ (ofNat 1 · ρ)·ρ^n`, and
`ofNat 1 · ρ ≃ ρ`, so `wilsonG w 2 n ≤ ρ·ρ^n = ρ^{n+1}`.  This is the real
object's decay — NOT posited. -/

/-- **The single-excited-rep chain decay (PROVED).**  `wilsonG w 2 n ≤ ρ^{n+1}`,
the proved `wilsonG_decay` at `M = 1` with the constant `ofNat 1 · ρ` simplified
to `ρ`.  The genuine real correlator at one excited rep decays as `ρ^{n+1}`. -/
theorem wilsonG_two_decay {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (n : Nat) :
    wilsonG w 2 n ≤ (rho w) ^ (n + 1) := by
  -- wilsonG w (1+1) n ≤ (ofNat 1 · ρ)·ρ^n
  have hdec : wilsonG w (1 + 1) n ≤ (Q'.ofNat 1 * rho w) * (rho w) ^ n :=
    wilsonG_decay hw0 hw 1 n
  refine Q'.le_trans' _ _ _ hdec ?_
  -- (ofNat 1 · ρ)·ρ^n ≃ ρ·ρ^n = ρ^{n+1}
  refine Q'.le_of_eqv ?_
  show ((Q'.ofNat 1 * rho w) * (rho w) ^ n).eqv ((rho w) ^ (n + 1))
  -- ofNat 1 · ρ ≃ 1 · ρ ≃ ρ
  have h1 : (Q'.ofNat 1 * rho w).eqv (rho w) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (rho w) (by decide))
      (Q'.one_mul_eqv (rho w))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ (rho w) ((rho w) ^ n) h1) ?_
  -- ρ·ρ^n = ρ^{n+1}
  rw [Q'.pow_succ]
  exact Q'.eqv_refl _

/-! ## 4. `ρ^{n+1} ≤ (sep Λ)^n` — the domination of the rate

`ρ^{n+1} = ρ·ρ^n ≤ ρ·(sep Λ)^n` (since `ρ^n ≤ (sep Λ)^n` from `ρ ≤ sep Λ`, both
nonneg, via `pow_le_pow_of_le`) `≤ 1·(sep Λ)^n ≃ (sep Λ)^n` (since `ρ ≤ 1`). -/

/-- **The rate domination (PROVED).**  `ρ^{n+1} ≤ (sep Λ)^n` at strong coupling
`0 ≤ w ≤ 1/4`: `ρ^{n+1} = ρ·ρ^n ≤ ρ·(sep Λ)^n ≤ (sep Λ)^n`, using `ρ ≤ sep Λ`
(`rho_le_sep`) and `ρ ≤ 1` (`rho_le_one`).  The genuine `wilsonG` rate is
dominated by the abstract clustering rate. -/
theorem rho_pow_succ_le_sep_pow {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ quarter)
    (Λ n : Nat) :
    (rho w) ^ (n + 1) ≤ (sep Λ) ^ n := by
  -- ρ^{n+1} = ρ · ρ^n
  have heq : ((rho w) ^ (n + 1)) = rho w * (rho w) ^ n := Q'.pow_succ (rho w) n
  rw [heq]
  -- ρ^n ≤ (sep Λ)^n
  have hpow : (rho w) ^ n ≤ (sep Λ) ^ n :=
    pow_le_pow_of_le (rho_nonneg' hw0) (rho_le_sep hw0 hw Λ) n
  -- ρ · ρ^n ≤ ρ · (sep Λ)^n
  have h1 : rho w * (rho w) ^ n ≤ rho w * (sep Λ) ^ n :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (rho_nonneg' hw0)
  -- ρ · (sep Λ)^n ≤ 1 · (sep Λ)^n
  have h2 : rho w * (sep Λ) ^ n ≤ (1 : Q') * (sep Λ) ^ n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (rho_le_one hw0 hw)
      (Q'.pow_nonneg (sep Λ) (sep_nonneg Λ) n)
  refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 ?_)
  exact Q'.le_of_eqv (Q'.one_mul_eqv ((sep Λ) ^ n))

/-! ## 5. The genuine domination structure and its inhabitant

`corr (gapModel Λ) n = (sep Λ)^n` (the one-mode abstract correlator, read off the
structure).  Chaining `wilsonG_two_decay` with `rho_pow_succ_le_sep_pow` gives the
genuine domination `wilsonG w 2 n ≤ (sep Λ)^n = corr (gapModel Λ) n`. -/

/-- `corr (gapModel Λ) n ≃ (sep Λ)^n` (the one excited mode of weight `1`):
`corr = 0 + 1·sep^n ≃ sep^n`. -/
theorem corr_gapModel_eqv (Λ n : Nat) :
    (corr (gapModel Λ) n).eqv ((sep Λ) ^ n) := by
  show (finSum (fun _ => (1 : Q') * (sep Λ) ^ n) 1).eqv ((sep Λ) ^ n)
  show ((0 : Q') + (1 : Q') * (sep Λ) ^ n).eqv ((sep Λ) ^ n)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
  exact Q'.one_mul_eqv ((sep Λ) ^ n)

/-- **The genuine domination (PROVED).**  The real single-excited-rep correlator
is bounded above by the abstract one-mode correlator at the located rate:

    wilsonG w 2 n  ≤  corr (gapModel Λ) n   (= (sep Λ)^n),

for every volume `Λ` and separation `n`, at strong coupling `0 ≤ w ≤ 1/4`.  Every
step is from a PROVED fact about the genuine `wilsonG` character double-sum
(`wilsonG_two_decay`, `rho_pow_succ_le_sep_pow`) — none from a definitional
coincidence. -/
theorem wilsonG_two_dominates {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ quarter)
    (Λ n : Nat) :
    wilsonG w 2 n ≤ corr (gapModel Λ) n := by
  -- w ≤ 1/4 ≤ 1/2, so wilsonG_two_decay applies.
  have hw2 : w ≤ half :=
    Q'.le_trans' _ _ _ hw (by decide)
  -- wilsonG w 2 n ≤ ρ^{n+1} ≤ (sep Λ)^n ≃ corr (gapModel Λ) n.
  refine Q'.le_trans' _ _ _ (wilsonG_two_decay hw0 hw2 n) ?_
  refine Q'.le_trans' _ _ _ (rho_pow_succ_le_sep_pow hw0 hw Λ n) ?_
  exact Q'.ge_of_eqv (corr_gapModel_eqv Λ n)

/-- **The honest tie: a DOMINATION structure (NOT exact `eqv`).**  A
`RealCorrelatorDomination` carries a candidate real connected-correlator family
`realCorr Λ n` together with a proof that it is DOMINATED BY (bounded above by)
the abstract one-mode correlator `corr (gapModel Λ) n`.  Unlike
`RealCorrelatorLink` (which demands a termwise `eqv`, satisfiable only by the
circular definition), domination is the genuine content available for the REAL
`wilsonG` double-sum: the two are DIFFERENT models with DIFFERENT rates, but the
real one decays at least as fast.  Domination is all the clustering CONCLUSION
needs. -/
structure RealCorrelatorDomination where
  /-- The candidate real connected-correlator family (the genuine `wilsonG`
  character double-sum). -/
  realCorr : Nat → Nat → Q'
  /-- The genuine tie: the real correlator is bounded above by the abstract
  one-mode correlator at the located clustering rate — DOMINATION, not `eqv`. -/
  dominated : ∀ Λ n, realCorr Λ n ≤ corr (gapModel Λ) n

/-- **THE GENUINE INHABITANT (NOT circular).**  A `RealCorrelatorDomination` whose
`realCorr` is the ACTUAL `wilsonG`-based connected correlator (the genuine
single-excited-rep character double-sum `wilsonG w 2 n`, INDEPENDENT of the
abstract volume index `Λ` — the real object does not know about `Λ`), and whose
`dominated` is the PROVED `wilsonG_two_dominates` (derived from `wilsonG_decay` +
`ρ ≤ sep Λ` + `ρ ≤ 1`).  This is NOT `eqv_refl` and NOT a definitional
coincidence: `realCorr` is the genuine character double-sum, the bound comes from
the proved geometric decay.  Valid at strong coupling `0 ≤ w ≤ 1/4`. -/
def genuineCorrDomination {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ quarter) :
    RealCorrelatorDomination where
  realCorr := fun _Λ n => wilsonG w 2 n
  dominated := fun Λ n => wilsonG_two_dominates hw0 hw Λ n

/-- The inhabitant's correlator family IS the genuine `wilsonG` double-sum (not
the abstract `corr`): `realCorr Λ n = wilsonG w 2 n`. -/
@[simp] theorem genuineCorrDomination_realCorr {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ quarter) (Λ n : Nat) :
    (genuineCorrDomination hw0 hw).realCorr Λ n = wilsonG w 2 n := rfl

/-- **The clustering conclusion off the genuine domination (PROVED).**  The REAL
correlator clusters at the abstract located rate: `realCorr Λ n ≤ (sep Λ)^n`.
Composing the inhabitant's `dominated` with `corr (gapModel Λ) n ≃ (sep Λ)^n`.
This is the genuine tie of the REAL `wilsonG` double-sum to the abstract
clustering rate `sep Λ` — WITHOUT the circular definition. -/
theorem genuineCorrDomination_cluster {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ quarter) (Λ n : Nat) :
    (genuineCorrDomination hw0 hw).realCorr Λ n ≤ (sep Λ) ^ n :=
  Q'.le_trans' _ _ _ ((genuineCorrDomination hw0 hw).dominated Λ n)
    (Q'.le_of_eqv (corr_gapModel_eqv Λ n))

/-- **Re-export: the genuine real correlator clusters at rate `sep Λ < 1`
(PROVED).**  `wilsonG w 2 n ≤ (sep Λ)^n` directly (the inhabitant's conclusion
unfolded onto the real object), the genuine geometric clustering of the actual
character double-sum at the abstract located rate. -/
theorem wilsonG_two_cluster {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ quarter)
    (Λ n : Nat) :
    wilsonG w 2 n ≤ (sep Λ) ^ n :=
  genuineCorrDomination_cluster hw0 hw Λ n

/-! ## 6. Documentation: PROVED vs honest-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — the REAL correlator tied to the abstract rate by
DOMINATION, no circularity):

  * `sep_ge_eighth` — the abstract separator floor `1/8 ≤ sep Λ`;
  * `rho_le_eighth`, `rho_le_sep`, `rho_le_one` — the genuine rate `ρ = 2w³` is
    `≤ 1/8 ≤ sep Λ` (UNIFORM in Λ) at strong coupling `0 ≤ w ≤ 1/4`;
  * `wilsonG_two_decay` — the genuine single-excited-rep decay `wilsonG w 2 n ≤
    ρ^{n+1}` (the PROVED `wilsonG_decay` at `M = 1`);
  * `rho_pow_succ_le_sep_pow` — `ρ^{n+1} ≤ (sep Λ)^n` (the rate domination);
  * `wilsonG_two_dominates` — `wilsonG w 2 n ≤ corr (gapModel Λ) n`, the genuine
    domination of the real correlator by the abstract one;
  * `RealCorrelatorDomination` + `genuineCorrDomination` — the honest tie
    structure and its GENUINE inhabitant (`realCorr` IS the `wilsonG` double-sum,
    `dominated` is DERIVED from the decay — NOT `eqv_refl`);
  * `genuineCorrDomination_cluster`, `wilsonG_two_cluster` — the REAL correlator
    clusters at the abstract located rate `sep Λ`.

HONEST-open / out of scope (NOT faked):

  * Exact `eqv` (the original `RealCorrelatorLink.matches_abstract`) is genuinely
    FALSE here: `wilsonG` (rate `ρ`) and `corr (gapModel)` (rate `sep Λ`) are
    DIFFERENT models with DIFFERENT rates; the only way to force `eqv` is the
    circular definition (`WilsonCorrelator.genuineRealCorrelatorLink`).  We
    deliver DOMINATION instead — the honest content for the clustering
    conclusion.
  * The FULL interacting multi-plaquette / loopy correlator stays the separate
    named wall; this is the single-line chain at ONE excited rep.

This module SUPERSEDES the circular `genuineRealCorrelatorLink` for the clustering
CONCLUSION: the real `wilsonG` character double-sum is now genuinely shown to be
dominated by — hence to cluster at least as fast as — the abstract correlator,
with every step from a PROVED fact and NONE from defining the real object equal to
the abstract one.  It is NOT a continuum limit and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.GenuineCorrLink

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GenuineCorrLink.sep_ge_eighth
#print axioms YMGap.Continuum.GenuineCorrLink.rho_le_eighth
#print axioms YMGap.Continuum.GenuineCorrLink.rho_le_sep
#print axioms YMGap.Continuum.GenuineCorrLink.rho_le_one
#print axioms YMGap.Continuum.GenuineCorrLink.wilsonG_two_decay
#print axioms YMGap.Continuum.GenuineCorrLink.rho_pow_succ_le_sep_pow
#print axioms YMGap.Continuum.GenuineCorrLink.corr_gapModel_eqv
#print axioms YMGap.Continuum.GenuineCorrLink.wilsonG_two_dominates
#print axioms YMGap.Continuum.GenuineCorrLink.genuineCorrDomination
#print axioms YMGap.Continuum.GenuineCorrLink.genuineCorrDomination_cluster
#print axioms YMGap.Continuum.GenuineCorrLink.wilsonG_two_cluster
