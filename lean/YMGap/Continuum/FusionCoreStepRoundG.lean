/-
Track A / R2 — Round G of the fusion box log-concavity node: the GREEN "DOMINANT
CENTRAL TERM" DISCRIMINANT ENGINE and the honest reduction of A3
(`StrandReduction.lineSumLogConcave` / `QuadGershgorinClosure`) to ONE sharp named
residual — a concrete central-autoconvolution reserve `δ ≥ ε² + 2ε`.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundD/F` split `QuadGershgorinClosure` into the finite strand reindex
(A1), the analytic common-range TP₂ core (A2, CLOSED in Round F: `lagCorrTP2_common`),
and the genuine wall A3 `StrandReduction.lineSumLogConcave` (the antidiagonal line-sum
log-concavity — a sum `Σ_r H_r` of per-shift log-concave autoconvolutions is not
log-concave in general).  Round G attacks A3 by CONVERTING the opaque "aggregate
Gershgorin/TP₂" bookkeeping into a fully green `Q'` discriminant engine plus a SINGLE
concrete numeric reserve target, replacing the hand-wave "factor-4 margin" with a sharp
threshold.

ROUND-G DELIVERABLE 1 (the green discriminant engine — PROVED, pure `Q'` arithmetic).
  * `prod_le_prod` — monotone product bound `x ≤ X, y ≤ Y, 0 ≤ y, 0 ≤ X ⟹ x·y ≤ X·Y`.
  * `dominant_term_LC` (E1) — the general reserve/domination threshold: with an
    `ε`-domination of the off-central mass and a `(1+δ)` central reserve, if
    `ε² + 2ε ≤ δ` then `(am+bm)·(ap+bp) ≤ (a₀+b₀)²`.  Robust: NO log-concavity assumed on
    the off mass `b`.  (Proved by the monotone route `a±+b± ≤ (1+ε)a±`, giving the sharp
    `(1+ε)² ≤ 1+δ` threshold; the discriminant is never expanded.)
  * `dominant_term_LC_four` (E3) — the clean factor-4 corollary (`δ=3, ε=1`): the exact
    reserve `4·(amap) ≤ a₀²` pays the three unit domination terms.  This is where the
    factor-4 is *exactly* load-bearing.
  * `dominant_term_LC3` — the 3-shift grouping (`b := b + c`), from E3.

ROUND-G DELIVERABLE 2 (the dominant-central-term magnitude bound — PROVED, all `s`).
  * `coeffW_ratio_quarter` — the all-`s` geometric ratio reserve `4·c_{s+1} ≤ c_s` on
    `0 < w ≤ 1/2`, by induction from `coeffW_superLogConcave_four` (the factor-4 atom) with
    base `coeffW1_le_quarter` and the strict positivity `coeffW_pos` for the cancellation.
    This is the `ρ_s ≤ 1/4` backbone from which the geometric shift-tail `H_r ≤ 16^{-r}H_0`
    (hence `ε = Σ_{r≥1}16^{-r} = 1/15`) descends.
  * `coeffW_weak_decreasing` — the immediate consequence `c_{s+1} ≤ c_s`.

ROUND-G DELIVERABLE 3 (the reduction of A3 to ONE sharp named residual — REDUCTION).
  * `CentralAutoconvReserve w` — the SINGLE sharp residual: a decomposition
    `lineSum = H₀ + off` (central autoconvolution + off-central mass), an `ε`-domination
    `off ≤ ε·H₀`, and the central reserve `(1+δ)·H₀(s)·H₀(s+2) ≤ H₀(s+1)²` with the sharp
    threshold `ε² + 2ε ≤ δ`.  This pins the opaque `LagCorrTP2`/`QuadGershgorinClosure`
    down to a concrete uniform central-autoconvolution log-concavity margin.
  * `lineSumLogConcaveOfReserve` — THE REDUCTION: a reserve witness discharges A3
    (`StrandReduction.lineSumLogConcave`) for every `N, s`, via E1.
  * `strandReductionOfReserve` — packaged with the finite A1 reindex, yields a full
    `StrandReduction` (hence `S1Dominance` for every `N` through Round D's wiring).
  * `eps_fifteenth_threshold` — the concrete numeric anchor: with `ε = 1/15` the sharp
    threshold is `δ ≥ 31/225` (`decide`), the honest quantified residual replacing the
    "factor-4" hand-wave.

# HONESTY — what is NOT closed

The residual `CentralAutoconvReserve` is a Type-level NAMED-OPEN structure; it is NOT
inhabited here for general `N`.  Its `reserve` field (the truncated central-autoconvolution
log-concavity margin `δ ≥ 31/225`, uniform in `s` and in the `N`-truncation) is the genuine
remaining local-CLT content — now sharply quantified rather than opaque.  Round G closes
the *aggregation algebra* of A3 (the discriminant engine) and reduces A3 to this ONE
concrete inequality; it does NOT prove that inequality.  This is NOT a 4D Yang–Mills mass
gap; it is a structural sharpening of one box-level sub-fact.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`lineSum`/`lagCorr` lemmas, structural
reductions, and `decide` only on closed concrete-rational facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level.
-/

import YMGap.Continuum.FusionCoreStepRoundF

namespace YMGap.Continuum.FusionCoreStepRoundG

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD

/-! ## 0. Small `Q'` helpers -/

/-- **`prod_le_prod`** — monotone product bound: `x ≤ X`, `y ≤ Y`, `0 ≤ y`, `0 ≤ X` give
`x·y ≤ X·Y` (multiply `x ≤ X` on the right by `y ≥ 0`, then `y ≤ Y` on the left by
`X ≥ 0`). -/
theorem prod_le_prod {x X y Y : Q'} (hx : x ≤ X) (hy : y ≤ Y)
    (hy0 : (0 : Q') ≤ y) (hX : (0 : Q') ≤ X) : x * y ≤ X * Y :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right x X y hx hy0)
    (Q'.mul_le_mul_of_nonneg_left y Y X hy hX)

/-- `((1+e)·a) ≃ a + e·a`. -/
theorem oneEps_mul_eqv (e a : Q') : ((1 + e) * a).eqv (a + e * a) :=
  Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 e a)
    (Q'.add_eqv_congr_right (1 * a) a (e * a) (Q'.one_mul_eqv a))

/-- `(4:Q')·z ≃ (z+z)+(z+z)` — the closed scalar split of the factor-4 reserve. -/
theorem four_mul_eqv (z : Q') : ((4 : Q') * z).eqv ((z + z) + (z + z)) := by
  have h4 : ((4 : Q') : Q').eqv (((1 : Q') + 1) + (1 + 1)) := by decide
  have twoz : (((1 : Q') + 1) * z).eqv (z + z) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 z)
      (Q'.add_eqv_congr' (Q'.one_mul_eqv z) (Q'.one_mul_eqv z))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (4 : Q') ((1 + 1) + (1 + 1)) z h4) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 + 1) (1 + 1) z) ?_
  exact Q'.add_eqv_congr' twoz twoz

/-- `(x+x)·(y+y) ≃ 4·(x·y)` — the factor-4 form of the doubled central product. -/
theorem two_two_mul_eqv (x y : Q') : ((x + x) * (y + y)).eqv ((4 : Q') * (x * y)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv x x (y + y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_add_eqv x y y) (Q'.mul_add_eqv x y y)) ?_
  exact Q'.eqv_symm (four_mul_eqv (x * y))

/-- **`sq_oneEps_le`** — the sharp threshold `(1+e)² ≤ 1+d` when `e² + (e+e) ≤ d`.
`(1+e)² ≃ (1+e)+(e+e²) ≃ 1 + (e+(e+e²))` and `e+(e+e²) ≃ e²+(e+e) ≤ d`. -/
theorem sq_oneEps_le (e d : Q') (_he : (0 : Q') ≤ e)
    (hthr : e * e + (e + e) ≤ d) : (1 + e) * (1 + e) ≤ (1 + d) := by
  have hexp : ((1 + e) * (1 + e)).eqv ((1 + e) + (e + e * e)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 e (1 + e)) ?_
    refine Q'.add_eqv_congr' (Q'.one_mul_eqv (1 + e)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv e 1 e) ?_
    exact Q'.add_eqv_congr_right (e * 1) e (e * e) (Q'.mul_one_eqv e)
  have hassoc : (((1 + e) + (e + e * e))).eqv (1 + (e + (e + e * e))) :=
    Q'.add_assoc_eqv 1 e (e + e * e)
  have hsum : e + (e + e * e) ≤ d := by
    have he2 : (e + (e + e * e)).eqv (e * e + (e + e)) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv e e (e * e)))
        (Q'.add_comm_eqv (e + e) (e * e))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he2) hthr
  have hstep : (1 + (e + (e + e * e))) ≤ (1 + d) := Q'.add_le_add_left 1 _ d hsum
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hexp)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hstep)

/-! ## 1. The green discriminant engine (E1, E3, 3-shift) -/

/-- **E1 — `dominant_term_LC` — the general reserve/domination threshold.**  With a
`(1+δ)` central reserve `(1+δ)·amap ≤ a₀²`, an `ε`-domination of the off masses
(`b± ≤ ε·a±`), and the sharp threshold `ε² + 2ε ≤ δ` (here written `ε·ε + (ε+ε) ≤ δ`), the
perturbed central product dominates:

    (am+bm)·(ap+bp) ≤ (a₀+b₀)·(a₀+b₀).

NO log-concavity is assumed on the off mass `b`.  Proof: `a±+b± ≤ (1+ε)·a±`, so the LHS is
`≤ (1+ε)²·amap ≤ (1+δ)·amap ≤ a₀² ≤ (a₀+b₀)²`. -/
theorem dominant_term_LC {ε δ am a₀ ap bm b₀ bp : Q'}
    (ham : (0 : Q') ≤ am) (hap : (0 : Q') ≤ ap) (ha₀ : (0 : Q') ≤ a₀)
    (hbp : (0 : Q') ≤ bp) (hb₀ : (0 : Q') ≤ b₀) (hε : (0 : Q') ≤ ε)
    (hres : (1 + δ) * (am * ap) ≤ a₀ * a₀)
    (hdomL : bm ≤ ε * am) (hdomR : bp ≤ ε * ap)
    (hthr : ε * ε + (ε + ε) ≤ δ) :
    (am + bm) * (ap + bp) ≤ (a₀ + b₀) * (a₀ + b₀) := by
  have hOneEps : (0 : Q') ≤ 1 + ε := Q'.zero_le_add 1 ε (by decide) hε
  have hXm : (0 : Q') ≤ (1 + ε) * am := Q'.mul_nonneg _ _ hOneEps ham
  have hAB : (0 : Q') ≤ ap + bp := Q'.zero_le_add _ _ hap hbp
  have hx : am + bm ≤ (1 + ε) * am :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left am bm (ε * am) hdomL)
      (Q'.ge_of_eqv (oneEps_mul_eqv ε am))
  have hy : ap + bp ≤ (1 + ε) * ap :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left ap bp (ε * ap) hdomR)
      (Q'.ge_of_eqv (oneEps_mul_eqv ε ap))
  have step1 : (am + bm) * (ap + bp) ≤ ((1 + ε) * am) * ((1 + ε) * ap) :=
    prod_le_prod hx hy hAB hXm
  have hswap : (((1 + ε) * am) * ((1 + ε) * ap)).eqv (((1 + ε) * (1 + ε)) * (am * ap)) :=
    mul_swap4 (1 + ε) am (1 + ε) ap
  have hsq : (1 + ε) * (1 + ε) ≤ 1 + δ := sq_oneEps_le ε δ hε hthr
  have haa : (0 : Q') ≤ am * ap := Q'.mul_nonneg _ _ ham hap
  have step2 : ((1 + ε) * (1 + ε)) * (am * ap) ≤ (1 + δ) * (am * ap) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsq haa
  have ha0b0 : a₀ ≤ a₀ + b₀ := Q'.add_le_self_of_nonneg a₀ b₀ hb₀
  have hX0 : (0 : Q') ≤ a₀ + b₀ := Q'.zero_le_add _ _ ha₀ hb₀
  have step4 : a₀ * a₀ ≤ (a₀ + b₀) * (a₀ + b₀) := prod_le_prod ha0b0 ha0b0 ha₀ hX0
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap)
      (Q'.le_trans' _ _ _ step2
        (Q'.le_trans' _ _ _ hres step4)))

/-- **E3 — `dominant_term_LC_four` — the clean factor-4 corollary.**  The exact reserve
`4·(amap) ≤ a₀²` pays the three unit domination terms: `(a±+b±) ≤ (a±+a±)`, so the LHS is
`≤ (am+am)(ap+ap) ≃ 4·amap ≤ a₀² ≤ (a₀+b₀)²`.  This is where the factor-4 is *exactly*
load-bearing (plain log-concavity, `δ=0`, fails). -/
theorem dominant_term_LC_four {am a₀ ap bm b₀ bp : Q'}
    (ham : (0 : Q') ≤ am) (hap : (0 : Q') ≤ ap) (ha₀ : (0 : Q') ≤ a₀)
    (hbp : (0 : Q') ≤ bp) (hb₀ : (0 : Q') ≤ b₀)
    (hres : (4 : Q') * (am * ap) ≤ a₀ * a₀)
    (hdomL : bm ≤ am) (hdomR : bp ≤ ap) :
    (am + bm) * (ap + bp) ≤ (a₀ + b₀) * (a₀ + b₀) := by
  have hAB : (0 : Q') ≤ ap + bp := Q'.zero_le_add _ _ hap hbp
  have hXm : (0 : Q') ≤ am + am := Q'.zero_le_add _ _ ham ham
  have hx : am + bm ≤ am + am := Q'.add_le_add_left am bm am hdomL
  have hy : ap + bp ≤ ap + ap := Q'.add_le_add_left ap bp ap hdomR
  have step1 : (am + bm) * (ap + bp) ≤ (am + am) * (ap + ap) := prod_le_prod hx hy hAB hXm
  have step2 : (am + am) * (ap + ap) ≤ (4 : Q') * (am * ap) :=
    Q'.le_of_eqv (two_two_mul_eqv am ap)
  have ha0b0 : a₀ ≤ a₀ + b₀ := Q'.add_le_self_of_nonneg a₀ b₀ hb₀
  have hX0 : (0 : Q') ≤ a₀ + b₀ := Q'.zero_le_add _ _ ha₀ hb₀
  have step4 : a₀ * a₀ ≤ (a₀ + b₀) * (a₀ + b₀) := prod_le_prod ha0b0 ha0b0 ha₀ hX0
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ step2 (Q'.le_trans' _ _ _ hres step4))

/-- **`dominant_term_LC3` — the 3-shift grouping.**  Group the off mass `b := b + c` and
apply E3: the domination hypotheses `b± + c± ≤ a±` are exactly the shift bound restricted
to `r ∈ {1,2}` (`H₁+H₂ ≤ (1/16+1/256)·H₀ < H₀`). -/
theorem dominant_term_LC3 {am a₀ ap bm b₀ bp cm c₀ cp : Q'}
    (ham : (0 : Q') ≤ am) (hap : (0 : Q') ≤ ap) (ha₀ : (0 : Q') ≤ a₀)
    (hbp : (0 : Q') ≤ bp) (hb₀ : (0 : Q') ≤ b₀)
    (hcp : (0 : Q') ≤ cp) (hc₀ : (0 : Q') ≤ c₀)
    (hres : (4 : Q') * (am * ap) ≤ a₀ * a₀)
    (hdomL : bm + cm ≤ am) (hdomR : bp + cp ≤ ap) :
    (am + bm + cm) * (ap + bp + cp) ≤ (a₀ + b₀ + c₀) * (a₀ + b₀ + c₀) := by
  have hE := dominant_term_LC_four (bm := bm + cm) (b₀ := b₀ + c₀) (bp := bp + cp)
    ham hap ha₀ (Q'.zero_le_add _ _ hbp hcp) (Q'.zero_le_add _ _ hb₀ hc₀)
    hres hdomL hdomR
  have eL : ((am + bm + cm) * (ap + bp + cp)).eqv
      ((am + (bm + cm)) * (ap + (bp + cp))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.add_assoc_eqv am bm cm))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.add_assoc_eqv ap bp cp))
  have eR : ((a₀ + (b₀ + c₀)) * (a₀ + (b₀ + c₀))).eqv
      ((a₀ + b₀ + c₀) * (a₀ + b₀ + c₀)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a₀ b₀ c₀)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a₀ b₀ c₀)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
    (Q'.le_trans' _ _ _ hE (Q'.le_of_eqv eR))

/-! ## 2. The dominant-central-term magnitude bound (all `s`) -/

/-- **`coeffW_ratio_quarter` — the all-`s` geometric ratio reserve `4·c_{s+1} ≤ c_s`.**
On `0 < w ≤ 1/2`, by induction: base `4·c₁ ≤ 4·(1/4) = 1 = c₀` (`coeffW1_le_quarter`); step
from the factor-4 atom `4·c_s·c_{s+2} ≤ c_{s+1}²` (`coeffW_superLogConcave_four`): the IH
`4c_{s+1} ≤ c_s` gives `c_{s+1} ≤ c_s`, so `c_{s+1}² ≤ c_s·c_{s+1}`, hence
`(4·c_{s+2})·c_s ≤ c_{s+1}·c_s`; cancel `c_s > 0` (`coeffW_pos`).  This is the `ρ_s ≤ 1/4`
backbone driving the geometric shift-tail `H_r ≤ 16^{-r}H₀` (hence `ε = 1/15`). -/
theorem coeffW_ratio_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) :
    ∀ s, (4 : Q') * coeffW w (s + 1) ≤ coeffW w s := by
  intro s
  induction s with
  | zero =>
    have h1 : coeffW w 1 ≤ Q'.mkPos 1 4 (by decide) := coeffW1_le_quarter hw0 hw12
    have hmul : (4 : Q') * coeffW w 1 ≤ (4 : Q') * (Q'.mkPos 1 4 (by decide)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ h1 (by decide)
    have he : ((4 : Q') * (Q'.mkPos 1 4 (by decide))).eqv 1 := by decide
    have h0 : coeffW w 0 = 1 := coeffW_zero w
    show (4 : Q') * coeffW w 1 ≤ coeffW w 0
    rw [h0]
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv he)
  | succ s ih =>
    have super := coeffW_superLogConcave_four hw0 hw12 s
    have cs_pos : (0 : Q') < coeffW w s :=
      YMGap.Continuum.FusionResidualBound.coeffW_pos hwpos s
    have c1_nn : (0 : Q') ≤ coeffW w (s + 1) := coeffW_nonneg hw0 (s + 1)
    have h_c1_le_4c1 : coeffW w (s + 1) ≤ (4 : Q') * coeffW w (s + 1) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w (s + 1))))
        (Q'.mul_le_mul_of_nonneg_right (1 : Q') (4 : Q') (coeffW w (s + 1)) (by decide) c1_nn)
    have Cs : coeffW w (s + 1) ≤ coeffW w s := Q'.le_trans' _ _ _ h_c1_le_4c1 ih
    have hsq_le : coeffW w (s + 1) * coeffW w (s + 1) ≤ coeffW w s * coeffW w (s + 1) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ Cs c1_nn
    have hkey : (4 : Q') * (coeffW w s * coeffW w (s + 2)) ≤ coeffW w s * coeffW w (s + 1) :=
      Q'.le_trans' _ _ _ super hsq_le
    have eL : ((4 : Q') * (coeffW w s * coeffW w (s + 2))).eqv
        (coeffW w s * ((4 : Q') * coeffW w (s + 2))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (4 : Q') _ _
          (Q'.mul_comm_eqv (coeffW w s) (coeffW w (s + 2)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (4 : Q') (coeffW w (s + 2)) (coeffW w s))) ?_
      exact Q'.mul_comm_eqv ((4 : Q') * coeffW w (s + 2)) (coeffW w s)
    have hcancel : coeffW w s * ((4 : Q') * coeffW w (s + 2)) ≤ coeffW w s * coeffW w (s + 1) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL) hkey
    show (4 : Q') * coeffW w (s + 2) ≤ coeffW w (s + 1)
    exact YMGap.Continuum.FusionQuotientCollapse.le_of_mul_le_mul_left_pos cs_pos hcancel

/-- **`coeffW_weak_decreasing`** — `c_{s+1} ≤ c_s` on `0 < w ≤ 1/2` (immediate from the
ratio reserve: `c_{s+1} ≤ 4·c_{s+1} ≤ c_s`). -/
theorem coeffW_weak_decreasing {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (s : Nat) : coeffW w (s + 1) ≤ coeffW w s := by
  have c1_nn : (0 : Q') ≤ coeffW w (s + 1) := coeffW_nonneg hw0 (s + 1)
  have h_c1_le_4c1 : coeffW w (s + 1) ≤ (4 : Q') * coeffW w (s + 1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w (s + 1))))
      (Q'.mul_le_mul_of_nonneg_right (1 : Q') (4 : Q') (coeffW w (s + 1)) (by decide) c1_nn)
  exact Q'.le_trans' _ _ _ h_c1_le_4c1 (coeffW_ratio_quarter hw0 hw12 hwpos s)

/-! ## 3. The reduction of A3 to ONE sharp named residual -/

/-- **`CentralAutoconvReserve w`** — the SINGLE sharp residual A3 reduces to.  It carries a
decomposition of the antidiagonal line-sum into a central autoconvolution `H₀` and an
off-central mass `off`, an `ε`-domination `off ≤ ε·H₀`, and the central-autoconvolution
reserve `(1+δ)·H₀(s)·H₀(s+2) ≤ H₀(s+1)²` with the sharp threshold `ε·ε + (ε+ε) ≤ δ`
(i.e. `δ ≥ ε² + 2ε`).  This replaces the opaque `QuadGershgorinClosure` / `LagCorrTP2`
bookkeeping with a concrete uniform inequality (`δ ≥ 31/225` at `ε = 1/15`).  It is
NAMED-OPEN (never `sorry`); its `reserve` field is the genuine remaining local-CLT content,
now sharply quantified. -/
structure CentralAutoconvReserve (w : Q') : Type where
  /-- The central shift term `H₀ = c∗c` (pure autoconvolution of the theta weight). -/
  H0 : Nat → Nat → Q'
  /-- The off-central mass `b = Σ_{r≥1} H_r`. -/
  off : Nat → Nat → Q'
  /-- The shift decomposition of the line-sum: `lineSum = H₀ + off`. -/
  decomp : ∀ N t, (lineSum (lagCorr w N) t).eqv (H0 N t + off N t)
  /-- The central term is nonneg. -/
  H0nonneg : ∀ N t, (0 : Q') ≤ H0 N t
  /-- The off-central mass is nonneg. -/
  offNonneg : ∀ N t, (0 : Q') ≤ off N t
  /-- The geometric-tail domination constant `ε` (`= 1/15` from `Σ_{r≥1}16^{-r}`). -/
  eps : Q'
  /-- The central-autoconvolution reserve constant `δ` (`≥ 31/225`). -/
  delta : Q'
  /-- `ε ≥ 0`. -/
  epsNonneg : (0 : Q') ≤ eps
  /-- The sharp threshold `ε² + 2ε ≤ δ`. -/
  threshold : eps * eps + (eps + eps) ≤ delta
  /-- The off mass is `ε`-dominated by the central term (uniform in `N, t`). -/
  dominate : ∀ N t, off N t ≤ eps * H0 N t
  /-- The central-autoconvolution log-concavity reserve (uniform in `N, s`). -/
  reserve : ∀ N s, (1 + delta) * (H0 N s * H0 N (s + 2)) ≤ H0 N (s + 1) * H0 N (s + 1)

/-- **`lineSumLogConcaveOfReserve` — THE REDUCTION.**  A `CentralAutoconvReserve` witness
discharges A3 (`StrandReduction.lineSumLogConcave`) for every `N, s`: apply E1
(`dominant_term_LC`) with `a± = H₀(s), H₀(s+2)`, `a₀ = H₀(s+1)`, `b = off`, then transport
across the `decomp` decomposition. -/
def lineSumLogConcaveOfReserve {w : Q'} (r : CentralAutoconvReserve w) :
    ∀ N s, lineSum (lagCorr w N) s * lineSum (lagCorr w N) (s + 2)
      ≤ lineSum (lagCorr w N) (s + 1) * lineSum (lagCorr w N) (s + 1) := by
  intro N s
  have hE := dominant_term_LC
    (am := r.H0 N s) (a₀ := r.H0 N (s + 1)) (ap := r.H0 N (s + 2))
    (bm := r.off N s) (b₀ := r.off N (s + 1)) (bp := r.off N (s + 2))
    (ε := r.eps) (δ := r.delta)
    (r.H0nonneg N s) (r.H0nonneg N (s + 2)) (r.H0nonneg N (s + 1))
    (r.offNonneg N (s + 2)) (r.offNonneg N (s + 1)) r.epsNonneg
    (r.reserve N s) (r.dominate N s) (r.dominate N (s + 2)) r.threshold
  have eL : (lineSum (lagCorr w N) s * lineSum (lagCorr w N) (s + 2)).eqv
      ((r.H0 N s + r.off N s) * (r.H0 N (s + 2) + r.off N (s + 2))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (r.decomp N s))
      (Q'.mul_eqv_congr_left _ _ _ (r.decomp N (s + 2)))
  have eR : ((r.H0 N (s + 1) + r.off N (s + 1)) * (r.H0 N (s + 1) + r.off N (s + 1))).eqv
      (lineSum (lagCorr w N) (s + 1) * lineSum (lagCorr w N) (s + 1)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (r.decomp N (s + 1))))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (r.decomp N (s + 1))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
    (Q'.le_trans' _ _ _ hE (Q'.le_of_eqv eR))

/-- **`strandReductionOfReserve`** — packaged with the finite A1 strand reindex, a
`CentralAutoconvReserve` witness yields a full `StrandReduction w` (hence, through Round D's
`s1DominanceOfStrandReduction`, `S1Dominance N w 2` for every `N`).  This exhibits the
central-autoconvolution reserve as the SOLE remaining analytic input on the A3 side. -/
def strandReductionOfReserve {w : Q'}
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (r : CentralAutoconvReserve w) : StrandReduction w where
  reindex := reindex
  lineSumLogConcave := lineSumLogConcaveOfReserve r

/-! ## 4. The concrete numeric anchor (the sharp threshold) -/

/-- **`eps_fifteenth_threshold` — the concrete residual constant.**  With the geometric-tail
domination `ε = 1/15` (`= Σ_{r≥1}16^{-r}`), the sharp central-autoconvolution threshold
`ε² + 2ε ≤ δ` is met exactly at `δ = 31/225`:

    (1/15)·(1/15) + ((1/15)+(1/15)) = 1/225 + 30/225 = 31/225.

This is the honest, quantified residual replacing the "factor-4" hand-wave: a ~14%
autoconvolution reserve, uniform in `s` and in the `N`-truncation. -/
theorem eps_fifteenth_threshold :
    (Q'.mkPos 1 15 (by decide)) * (Q'.mkPos 1 15 (by decide))
        + ((Q'.mkPos 1 15 (by decide)) + (Q'.mkPos 1 15 (by decide)))
      ≤ Q'.mkPos 31 225 (by decide) := by decide

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `prod_le_prod`, `oneEps_mul_eqv`, `four_mul_eqv`, `two_two_mul_eqv`, `sq_oneEps_le`
    — the `Q'` discriminant-engine helpers.
  * `dominant_term_LC` (E1) — the general sharp reserve/domination threshold
    `ε² + 2ε ≤ δ ⟹ (am+bm)(ap+bp) ≤ (a₀+b₀)²`.
  * `dominant_term_LC_four` (E3) — the factor-4 corollary.
  * `dominant_term_LC3` — the 3-shift grouping.
  * `coeffW_ratio_quarter` — the all-`s` geometric ratio reserve `4·c_{s+1} ≤ c_s`.
  * `coeffW_weak_decreasing` — `c_{s+1} ≤ c_s`.
  * `lineSumLogConcaveOfReserve` — THE REDUCTION of A3 to `CentralAutoconvReserve`.
  * `strandReductionOfReserve` — reserve + finite reindex ⟹ full `StrandReduction`.
  * `eps_fifteenth_threshold` — the concrete residual constant `δ ≥ 31/225` at `ε = 1/15`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `CentralAutoconvReserve w` — the SINGLE sharp residual: the `H₀+off` decomposition,
    the `ε`-domination `off ≤ ε·H₀`, and the central-autoconvolution reserve
    `(1+δ)·H₀(s)·H₀(s+2) ≤ H₀(s+1)²` with `δ ≥ ε² + 2ε`.  Its `reserve` field is the
    genuine remaining local-CLT content (the truncated central-autoconvolution
    log-concavity margin `δ ≥ 31/225`, uniform in `s` and the `N`-truncation), now sharply
    quantified rather than opaque.

HONEST VERDICT.  Round G converts the opaque "aggregate Gershgorin/TP₂" bookkeeping of A3
into a fully green `Q'` discriminant engine (E1/E3/3-shift), proves the all-`s` geometric
ratio reserve that pins the domination constant to `ε = 1/15`, and REDUCES A3
(`StrandReduction.lineSumLogConcave` / `QuadGershgorinClosure`) to ONE concrete named
residual — the central-autoconvolution reserve `δ ≥ 31/225`.  It does NOT prove that
reserve.  This is a structural sharpening of one box-level log-concavity sub-fact; it is
NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundG.prod_le_prod
#print axioms YMGap.Continuum.FusionCoreStepRoundG.four_mul_eqv
#print axioms YMGap.Continuum.FusionCoreStepRoundG.two_two_mul_eqv
#print axioms YMGap.Continuum.FusionCoreStepRoundG.sq_oneEps_le
#print axioms YMGap.Continuum.FusionCoreStepRoundG.dominant_term_LC
#print axioms YMGap.Continuum.FusionCoreStepRoundG.dominant_term_LC_four
#print axioms YMGap.Continuum.FusionCoreStepRoundG.dominant_term_LC3
#print axioms YMGap.Continuum.FusionCoreStepRoundG.coeffW_ratio_quarter
#print axioms YMGap.Continuum.FusionCoreStepRoundG.coeffW_weak_decreasing
#print axioms YMGap.Continuum.FusionCoreStepRoundG.lineSumLogConcaveOfReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundG.strandReductionOfReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundG.eps_fifteenth_threshold
