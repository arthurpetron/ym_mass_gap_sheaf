/-
Heat-kernel pointwise positivity, Part 4-GEN (gap G1, the `ϑ₃`-factor for ALL a) —
lifting the Jacobi theta partial PRODUCT

    ϑ₃(x) = ∏_{n≥1} (1 − a^{2n})·(1 + 2·a^{2n-1}·x + a^{4n-2})

from the small-`a` regime (`a ≤ 1/16`, `a·a ≤ 1/2`, smallness `Σ Tcoef ≤ 1/2`) to
ALL `a ∈ (0,1)`, mirroring how `HeatKernelConvGen.lean` lifted the `S`-factor.

# What this module closes

`Continuum/ThetaConv.lean` built `ϑ₃(x)` as a genuine convergent `CReal`
(`thetaConvCReal`) and assembled the full manifest-nonneg object
`R = ϑ₃·S ≥ 0` (`R_geRat_zero_sixteenth`), but ONLY in the smallness regime
`a ≤ 1/16`.  Two restrictions entered there:

  * `a·a ≤ 1/2` — needed ONLY to dominate the decay base `a·a` by `1/2` so the
    `1/2`-hardcoded engine `crealOfGeoIncrement` applies.  We remove it by
    feeding the GENERAL-BASE engine `HKConvGen.crealOfGeoIncrementBase` (decay
    base `r = a·a < 1` itself), exactly as `HeatKernelConvGen` did for `S`.

  * smallness `∀ L, finSum (Tcoef a) L ≤ 1/2` — needed ONLY for the
    product-MAGNITUDE bound `Ppart a x L ≤ 2`.  We remove it with an
    `a`-dependent magnitude bound `Ppart a x L ≤ Bmag a` obtained by a
    **prefix split**: choose a cutoff `K = thetaCutoff a` (via the general
    `rⁿ→0` modulus `HKConvGen.pow_base_le` at base `a·a`) past which the
    SHIFTED coefficient sequence has all partial sums `≤ 1/2`; then
    `Ppart ≤ prodUp (Tcoef a) K · 2` by the existing Weierstrass bound
    `ThetaConv.prodUpBound` applied to the shifted sequence.

# The increment bound (now base `a·a`, no smallness)

`dBound a l = 6·geoAmp a l = 6a·(a·a)^l` EXACTLY (via `ThetaConv.geoAmp_eqv`), so
the per-factor deviation already decays at base `a·a` with constant `6a` — no
smallness needed.  With `|Ppart l| ≤ Bmag a`, the single-step increment
`|Ppart l · dev_l| ≤ Bmag a · 6a · (a·a)^l =: Cgen a · (a·a)^l`, which is exactly
the `geoIncrBase (Cgen a) (a·a)` interface of `crealOfGeoIncrementBase`.

# The deliverable

  * `thetaConvCRealGen a x (0<a)(a<1)(−1≤x)(x≤1)` — `ϑ₃(x)` as a convergent
    `CReal` for ALL `a ∈ (0,1)`, `−1 ≤ x ≤ 1`, with `approx N = Ppart a x N`
    and the explicit base-`(a·a)` modulus.  No `a·a ≤ 1/2`, no smallness.
  * `thetaConvCRealGen_approx`, `_approx_nonneg`, `_geRat_zero`.
  * `R_geRat_zero_gen` — the assembled `R = ϑ₃·S ≥ 0` for ALL `a ∈ (0,1)`,
    both factors genuine convergent `CReal`s (mirrors `R_geRat_zero_sixteenth`).

# The precise remaining gap (honest, per AGENTS.md Rule 6)

  (G2) The IDENTITY `K_t(x) = (ϑ₃/2a)·S(x)` (differentiated Jacobi triple
       product) remains the separate analytic gap.  Convergence (G1) of BOTH
       factors as `CReal`s is now CLOSED for all `a ∈ (0,1)`.

Everything below is fully proved and axiom-gated (`[propext]` or
`[propext, Quot.sound]`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.ThetaConv
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.HeatKernelPos2
import YMGap.Continuum.KPLimit
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealMul
import YMGap.Constructive.RationalTail
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.ThetaConvGen

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.HKPos
open YMGap.Continuum.ThetaConv
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow

/-! ## 1. Shifted-sequence factorization of `prodUp`

`prodUp T (K + M) = prodUp T K · prodUp (shiftSeq T K) M`, where
`shiftSeq T K j = T (K + j)`.  This lets us apply the Weierstrass magnitude
bound `prodUpBound` to the SHIFTED coefficient sequence (whose partial sums are
`≤ 1/2` past the cutoff), and absorb the finite prefix `prodUp T K` into a
constant. -/

/-- The shifted sequence `shiftSeq T K j = T (K + j)`. -/
def shiftSeq (T : Nat → Q') (K : Nat) (j : Nat) : Q' := T (K + j)

/-- `prodUp T (K + M) ≃ prodUp T K · prodUp (shiftSeq T K) M`.  Induction on `M`. -/
theorem prodUp_shift_eqv (T : Nat → Q') (K : Nat) :
    ∀ M, (prodUp T (K + M)).eqv (prodUp T K * prodUp (shiftSeq T K) M)
  | 0 => by
      -- prodUp T (K+0) = prodUp T K ;  RHS = prodUp T K · 1 ≃ prodUp T K
      show (prodUp T (K + 0)).eqv (prodUp T K * prodUp (shiftSeq T K) 0)
      have h : K + 0 = K := rfl
      rw [h]
      show (prodUp T K).eqv (prodUp T K * (1 : Q'))
      exact Q'.eqv_symm (Q'.mul_one_eqv (prodUp T K))
  | M + 1 => by
      -- prodUp T (K + (M+1)) = prodUp T (K+M) · T (K+M)
      -- RHS = prodUp T K · (prodUp (shiftSeq T K) M · (1 + shiftSeq T K M))
      have he : K + (M + 1) = (K + M) + 1 := by omega
      show (prodUp T (K + (M + 1))).eqv
          (prodUp T K * prodUp (shiftSeq T K) (M + 1))
      rw [he]
      show (prodUp T ((K + M) + 1)).eqv
          (prodUp T K * (prodUp (shiftSeq T K) M * (1 + shiftSeq T K M)))
      -- LHS = prodUp T (K+M) · (1 + T (K+M)) ;  shiftSeq T K M = T (K+M)
      show (prodUp T (K + M) * (1 + T (K + M))).eqv
          (prodUp T K * (prodUp (shiftSeq T K) M * (1 + T (K + M))))
      -- prodUp T (K+M) ≃ prodUp T K · prodUp (shiftSeq T K) M  (ih)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (1 + T (K + M)) (prodUp_shift_eqv T K M)) ?_
      -- (P·Q)·f ≃ P·(Q·f)
      exact Q'.mul_assoc_eqv (prodUp T K) (prodUp (shiftSeq T K) M) (1 + T (K + M))

/-! ## 2. The cutoff `thetaCutoff a` and the shifted smallness `Σ shifted ≤ 1/2`

`Tcoef a k ≤ 3a·(a·a)^k` (since `c = a^{2k+1} = a·(a·a)^k ≤ 1`, so `2c + c² ≤ 3c`).
Hence the SHIFTED coefficients `Tcoef a (K + j) ≤ (3a·(a·a)^K)·(a·a)^j`, and their
partial sums are `≤ (3a·(a·a)^K)·H`, `H = 1/(1−a·a)`.  Choosing `K` so that
`(a·a)^K ≤ δ := (1/2)/((3a)·H)` (via `pow_base_le`) makes this `≤ 1/2`. -/

/-- `3a = a + (a + a)`, kept additively. -/
def threeA (a : Q') : Q' := a + (a + a)

theorem threeA_nonneg {a : Q'} (ha0 : (0 : Q') < a) : (0 : Q') ≤ threeA a :=
  Q'.zero_le_add _ _ (Q'.le_of_lt ha0)
    (Q'.zero_le_add _ _ (Q'.le_of_lt ha0) (Q'.le_of_lt ha0))

theorem threeA_pos {a : Q'} (ha0 : (0 : Q') < a) : (0 : Q') < threeA a := by
  show (0 : Q') < a + (a + a)
  exact Q'.pos_of_lt_of_le ha0
    (Q'.add_le_self_of_nonneg a (a + a)
      (Q'.zero_le_add _ _ (Q'.le_of_lt ha0) (Q'.le_of_lt ha0)))

/-- `1 ≤ prodUp T L` for a nonnegative sequence (each factor `1 + T_k ≥ 1`). -/
theorem prodUp_ge_one {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k) :
    ∀ L, (1 : Q') ≤ prodUp T L
  | 0 => Q'.le_refl' 1
  | L + 1 => by
      rw [prodUp_succ]
      -- 1 ≤ prodUp T L ≤ prodUp T L · (1 + T L)
      have ih := prodUp_ge_one hT L
      have hPnn : (0 : Q') ≤ prodUp T L := prodUp_nonneg hT L
      have h1le : (1 : Q') ≤ 1 + T L := Q'.add_le_self_of_nonneg 1 (T L) (hT L)
      refine Q'.le_trans' _ _ _ ih ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv (prodUp T L)))) ?_
      exact Q'.mul_le_mul_of_nonneg_left 1 (1 + T L) (prodUp T L) h1le hPnn

/-- The geometric-series majorant `H a = 1/(1 − a·a) = divPos 1 (1 + (−(a·a)))`. -/
def Hgeo (a : Q') : Q' := HKConv.divPos 1 (1 + (-(a * a)))

theorem Hgeo_nonneg (a : Q') : (0 : Q') ≤ Hgeo a :=
  HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide)))

/-- `0 < threeA a · Hgeo a` for `0 < a < 1`. -/
theorem threeA_Hgeo_pos {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) :
    (0 : Q') < threeA a * Hgeo a := by
  have h3 : (0 : Q') < threeA a := threeA_pos ha0
  have hH : (0 : Q') < Hgeo a := by
    refine HKConv.divPos_pos ?_
    show 0 < (1 : Q').num
    decide
  exact HKPos.q_mul_pos h3 hH

/-- The cutoff tolerance `δ = (1/2)/(3a·H) = divPos half (threeA a · Hgeo a)`. -/
def thetaDelta (a : Q') : Q' := HKConv.divPos half (threeA a * Hgeo a)

theorem thetaDelta_pos {a : Q'} (ha0 : (0 : Q') < a) : (0 : Q') < thetaDelta a := by
  refine HKConv.divPos_pos ?_
  show 0 < half.num
  decide

/-- The cutoff `thetaCutoff a = powBaseCutoff (a·a) (thetaDelta a)`. -/
def thetaCutoff (a : Q') : Nat := powBaseCutoff (a * a) (thetaDelta a)

/-- `a·a < 1` for `0 < a < 1`. -/
theorem aa_lt_one {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) : a * a < (1 : Q') := by
  have haa_le_a : a * a ≤ a :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right a 1 a (Q'.le_of_lt ha1) (Q'.le_of_lt ha0))
      (Q'.le_of_eqv (Q'.one_mul_eqv a))
  exact HKPos.q_lt_of_le_of_lt haa_le_a ha1

/-- The defining property of the cutoff: `(a·a)^(thetaCutoff a) ≤ thetaDelta a`. -/
theorem aa_pow_cutoff_le {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) :
    (a * a) ^ (thetaCutoff a) ≤ thetaDelta a :=
  HKConvGen.pow_base_le_cutoff (HKPos.q_mul_pos ha0 ha0) (aa_lt_one ha0 ha1)
    (thetaDelta_pos ha0)

/-! ## 3. The per-term geometric bound and the shifted smallness -/

/-- `Tcoef a k ≤ threeA a · (a·a)^k` (`= 3a·(a²)^k`) under `0 < a < 1`.
Termwise: `c_k = geoAmp a k ≃ a·(a·a)^k`, `c_k ≤ 1`, so `2c + c² ≤ 3c`. -/
theorem Tcoef_le_geo {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (k : Nat) :
    Tcoef a k ≤ threeA a * (a * a) ^ k := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a k := Q'.le_of_lt (HKPos.pow_pos ha0 (2 * k + 1))
  have hc1 : HKPos.geoAmp a k ≤ (1 : Q') :=
    HKPos.pow_le_one (Q'.le_of_lt ha0) (Q'.le_of_lt ha1) (2 * k + 1)
  -- c_k = a·(a·a)^k  (exact, ThetaConv.geoAmp_eqv)
  have hc_eq : (HKPos.geoAmp a k).eqv (a * (a * a) ^ k) := ThetaConv.geoAmp_eqv a k
  -- Tcoef = (c + c) + c·c ≤ c + (c + c) = threeA' built from c
  have hcc : HKPos.geoAmp a k * HKPos.geoAmp a k ≤ HKPos.geoAmp a k :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ 1 _ hc1 hc0)
      (Q'.le_of_eqv (Q'.mul_one_eqv (HKPos.geoAmp a k)))
  have hT3 : Tcoef a k ≤ HKPos.geoAmp a k + (HKPos.geoAmp a k + HKPos.geoAmp a k) := by
    show (HKPos.geoAmp a k + HKPos.geoAmp a k) + HKPos.geoAmp a k * HKPos.geoAmp a k ≤ _
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (HKPos.geoAmp a k + HKPos.geoAmp a k) _ _ hcc) ?_
    exact Q'.le_of_eqv
      (Q'.add_assoc_eqv (HKPos.geoAmp a k) (HKPos.geoAmp a k) (HKPos.geoAmp a k))
  -- 3 copies of c ≃ threeA a · (a·a)^k  via c ≃ a·(a·a)^k and distribution
  have hdist : (HKPos.geoAmp a k + (HKPos.geoAmp a k + HKPos.geoAmp a k)).eqv
      (threeA a * (a * a) ^ k) := by
    -- c + (c + c) ≃ a·p + (a·p + a·p),  p = (a·a)^k
    have hinner : (HKPos.geoAmp a k + HKPos.geoAmp a k).eqv
        (a * (a * a) ^ k + a * (a * a) ^ k) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (HKPos.geoAmp a k) hc_eq)
        (Q'.add_eqv_congr_left (a * (a * a) ^ k) _ _ hc_eq)
    have hstep : (HKPos.geoAmp a k + (HKPos.geoAmp a k + HKPos.geoAmp a k)).eqv
        (a * (a * a) ^ k + (a * (a * a) ^ k + a * (a * a) ^ k)) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (HKPos.geoAmp a k + HKPos.geoAmp a k) hc_eq)
        (Q'.add_eqv_congr_left (a * (a * a) ^ k) _ _ hinner)
    refine Q'.eqv_trans _ _ _ hstep ?_
    -- a·p + (a·p + a·p) ≃ (a + (a+a))·p = threeA a · p
    show (a * (a * a) ^ k + (a * (a * a) ^ k + a * (a * a) ^ k)).eqv
        ((a + (a + a)) * (a * a) ^ k)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a (a + a) ((a * a) ^ k)) ?_
    exact Q'.add_eqv_congr_left (a * (a * a) ^ k) _ _ (Q'.add_mul_eqv a a ((a * a) ^ k))
  exact Q'.le_trans' _ _ _ hT3 (Q'.le_of_eqv hdist)

/-- The shifted coefficient bound `shiftSeq (Tcoef a) K j ≤ (threeA a·(a·a)^K)·(a·a)^j`. -/
theorem shift_Tcoef_le {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (K j : Nat) :
    shiftSeq (Tcoef a) K j ≤ (threeA a * (a * a) ^ K) * (a * a) ^ j := by
  show Tcoef a (K + j) ≤ (threeA a * (a * a) ^ K) * (a * a) ^ j
  refine Q'.le_trans' _ _ _ (Tcoef_le_geo ha0 ha1 (K + j)) ?_
  -- threeA a · (a·a)^(K+j) ≃ (threeA a·(a·a)^K)·(a·a)^j
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (threeA a) _ _ (Q'.pow_add_eqv (a * a) K j)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (threeA a) ((a * a) ^ K) ((a * a) ^ j))

/-- **The shifted smallness `∀ M, finSum (shiftSeq (Tcoef a) K) M ≤ 1/2`** at the
cutoff `K = thetaCutoff a`.  The shifted coefficients are dominated by the
geometric `(threeA a·(a·a)^K)·(a·a)^j`, summing under
`(threeA a·(a·a)^K)·Hgeo a ≤ (threeA a·δ)·H = 1/2`. -/
theorem shift_smallness {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (K : Nat) (hKδ : (a * a) ^ K ≤ thetaDelta a) (M : Nat) :
    finSum (shiftSeq (Tcoef a) K) M ≤ half := by
  have haa0 : (0 : Q') < a * a := HKPos.q_mul_pos ha0 ha0
  have haa1 : a * a < (1 : Q') := aa_lt_one ha0 ha1
  -- f0 := threeA a · (a·a)^K  ;  r := a·a  ;  H := Hgeo a
  have hf0nn : (0 : Q') ≤ threeA a * (a * a) ^ K :=
    Q'.mul_nonneg _ _ (threeA_nonneg ha0) (Q'.pow_nonneg _ (Q'.le_of_lt haa0) K)
  -- geometric series bound: finSum shift ≤ f0 · H
  have hgeo : finSum (shiftSeq (Tcoef a) K) M
      ≤ (threeA a * (a * a) ^ K) * Hgeo a := by
    -- termwise ≤ f0·(a·a)^j, then geom_series_le_base after pulling out f0
    have hterm : finSum (shiftSeq (Tcoef a) K) M
        ≤ finSum (fun j => (threeA a * (a * a) ^ K) * (a * a) ^ j) M :=
      CharacterTail.finSum_le_termwise _ _ (fun j => shift_Tcoef_le ha0 ha1 K j) M
    refine Q'.le_trans' _ _ _ hterm ?_
    -- finSum (fun j => f0·(a·a)^j) M ≃ f0 · finSum (a·a)^j M ≤ f0·H
    have hpull : (finSum (fun j => (threeA a * (a * a) ^ K) * (a * a) ^ j) M).eqv
        ((threeA a * (a * a) ^ K) * finSum (fun j => (a * a) ^ j) M) :=
      Q'.eqv_symm (RationalTail.const_mul_finSum (fun j => (a * a) ^ j)
        (threeA a * (a * a) ^ K) M)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (HKConvGen.geom_series_le_base haa0 haa1 M) hf0nn
  refine Q'.le_trans' _ _ _ hgeo ?_
  -- (threeA a·(a·a)^K)·H ≤ (threeA a·δ)·H = half
  -- step 1: (a·a)^K ≤ δ  ⟹  threeA a·(a·a)^K ≤ threeA a·δ
  have hpowδ : (a * a) ^ K ≤ thetaDelta a := hKδ
  have h1 : (threeA a * (a * a) ^ K) * Hgeo a
      ≤ (threeA a * thetaDelta a) * Hgeo a := by
    refine Q'.mul_le_mul_of_nonneg_right _ _ (Hgeo a) ?_ (Hgeo_nonneg a)
    exact Q'.mul_le_mul_of_nonneg_left _ _ (threeA a) hpowδ (threeA_nonneg ha0)
  refine Q'.le_trans' _ _ _ h1 ?_
  -- (threeA a · δ) · H ≃ (threeA a · H) · δ ≃ half  (δ = divPos half (threeA·H))
  have hreassoc : ((threeA a * thetaDelta a) * Hgeo a).eqv
      ((threeA a * Hgeo a) * thetaDelta a) := by
    -- (A·δ)·H ≃ A·(δ·H) ≃ A·(H·δ) ≃ (A·H)·δ
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (threeA a) (thetaDelta a) (Hgeo a)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (threeA a) _ _ (Q'.mul_comm_eqv (thetaDelta a) (Hgeo a))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (threeA a) (Hgeo a) (thetaDelta a))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
  -- (threeA·H)·δ ≃ δ·(threeA·H) ≃ half  via divPos cancellation (δ = divPos half (threeA·H))
  have hpos : 0 < (threeA a * Hgeo a).num :=
    CReal.num_pos_of_pos (threeA_Hgeo_pos ha0 ha1)
  -- (D · δ) ≃ (δ · D) ≃ half
  have hcomm : ((threeA a * Hgeo a) * thetaDelta a).eqv
      (thetaDelta a * (threeA a * Hgeo a)) :=
    Q'.mul_comm_eqv (threeA a * Hgeo a) (thetaDelta a)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) ?_
  show (thetaDelta a * (threeA a * Hgeo a)) ≤ half
  show (HKConv.divPos half (threeA a * Hgeo a) * (threeA a * Hgeo a)) ≤ half
  exact Q'.le_of_eqv (HKConv.divPos_mul_eqv (p := half) (D := threeA a * Hgeo a) hpos)

/-! ## 5. The `a`-dependent product-magnitude bound `Ppart a x L ≤ Bmag a`

`prodUp` is monotone nondecreasing (each factor `1 + T_k ≥ 1`).  Split `L` at the
cutoff `K = thetaCutoff a`:

  * `L ≤ K`:  `prodUp T L ≤ prodUp T K ≤ prodUp T K · 2`.
  * `K ≤ L`, `L = K + M`:  `prodUp T (K+M) ≃ prodUp T K · prodUp (shift T K) M`,
    and `prodUp (shift T K) M ≤ 2` by `prodUpBound` (shifted smallness §4). -/

/-- `prodUp` is monotone nondecreasing for a nonnegative sequence: each factor
`1 + T_k ≥ 1`, so appending one cannot decrease the product. -/
theorem prodUp_monotone {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k) :
    ∀ L, prodUp T L ≤ prodUp T (L + 1)
  | L => by
      rw [prodUp_succ]
      -- prodUp T L ≤ prodUp T L · (1 + T L)  since 1 + T L ≥ 1 and prodUp ≥ 0
      have hPnn : (0 : Q') ≤ prodUp T L := prodUp_nonneg hT L
      have h1le : (1 : Q') ≤ 1 + T L := Q'.add_le_self_of_nonneg 1 (T L) (hT L)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv (prodUp T L)))) ?_
      exact Q'.mul_le_mul_of_nonneg_left 1 (1 + T L) (prodUp T L) h1le hPnn

theorem prodUp_le_add {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k) (L : Nat) :
    ∀ d, prodUp T L ≤ prodUp T (L + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      have e : L + (d + 1) = (L + d) + 1 := by omega
      rw [e]
      exact Q'.le_trans' _ _ _ (prodUp_le_add hT L d) (prodUp_monotone hT (L + d))

theorem prodUp_le_of_le {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k) {L L' : Nat}
    (h : L ≤ L') : prodUp T L ≤ prodUp T L' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact prodUp_le_add hT L d

/-- The `a`-dependent magnitude bound constant `Bmag a = prodUp (Tcoef a) K · 2`,
`K = thetaCutoff a`. -/
def Bmag (a : Q') : Q' := prodUp (Tcoef a) (thetaCutoff a) * Q'.ofNat 2

theorem Bmag_nonneg {a : Q'} (ha0 : (0 : Q') < a) : (0 : Q') ≤ Bmag a :=
  Q'.mul_nonneg _ _ (prodUp_nonneg (Tcoef_nonneg ha0) (thetaCutoff a)) (by decide)

/-- **`prodUp (Tcoef a) L ≤ Bmag a` for all `L`** (the prefix-split magnitude
bound, valid for ALL `a ∈ (0,1)`). -/
theorem prodUp_Tcoef_le_Bmag {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (L : Nat) : prodUp (Tcoef a) L ≤ Bmag a := by
  have hTnn : ∀ k, (0 : Q') ≤ Tcoef a k := Tcoef_nonneg ha0
  have hKδ : (a * a) ^ (thetaCutoff a) ≤ thetaDelta a := aa_pow_cutoff_le ha0 ha1
  -- The shifted product is ≤ 2 by prodUpBound applied to shiftSeq (Tcoef a) K
  have hPK_nn : (0 : Q') ≤ prodUp (Tcoef a) (thetaCutoff a) :=
    prodUp_nonneg hTnn (thetaCutoff a)
  by_cases hLK : L ≤ thetaCutoff a
  · -- prodUp T L ≤ prodUp T K ≤ prodUp T K · 2 = Bmag
    refine Q'.le_trans' _ _ _ (prodUp_le_of_le hTnn hLK) ?_
    show prodUp (Tcoef a) (thetaCutoff a) ≤ prodUp (Tcoef a) (thetaCutoff a) * Q'.ofNat 2
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) ?_
    exact Q'.mul_le_mul_of_nonneg_left 1 (Q'.ofNat 2) _ (by decide) hPK_nn
  · -- K ≤ L ; write L = K + M
    have hKL : thetaCutoff a ≤ L := Nat.le_of_not_le hLK
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hKL
    -- prodUp T (K+M) ≃ prodUp T K · prodUp (shift T K) M
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (prodUp_shift_eqv (Tcoef a) (thetaCutoff a) M)) ?_
    -- prodUp T K · prodUp (shift T K) M ≤ prodUp T K · 2 = Bmag
    show prodUp (Tcoef a) (thetaCutoff a) * prodUp (shiftSeq (Tcoef a) (thetaCutoff a)) M
        ≤ Bmag a
    show prodUp (Tcoef a) (thetaCutoff a) * prodUp (shiftSeq (Tcoef a) (thetaCutoff a)) M
        ≤ prodUp (Tcoef a) (thetaCutoff a) * Q'.ofNat 2
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hPK_nn
    -- prodUp (shift) M ≤ 2  via prodUpBound (shifted nonneg + shifted smallness)
    refine prodUpBound (fun k => hTnn (thetaCutoff a + k)) ?_ M
    intro M'
    exact shift_smallness ha0 ha1 (thetaCutoff a) hKδ M'

/-- **`Ppart a x L ≤ Bmag a`** — the magnitude bound on the genuine partial
product, for ALL `a ∈ (0,1)`, `−1 ≤ x ≤ 1`.  Chains
`Ppart ≤ prodUp (Tcoef a) ≤ Bmag a`. -/
theorem Ppart_le_Bmag {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (L : Nat) : Ppart a x L ≤ Bmag a :=
  Q'.le_trans' _ _ _ (Ppart_le_prodUp ha0 ha1 hx hx1 L)
    (prodUp_Tcoef_le_Bmag ha0 ha1 L)

/-! ## 6. The two-sided single-step increment bound at base `a·a`

`dBound a l = 6·geoAmp a l = 6a·(a·a)^l` exactly, so the per-factor deviation
decays at base `a·a` with constant `6a` — NO smallness.  With `|Ppart| ≤ Bmag a`,
the single-step increment `|Ppart l · dev_l| ≤ Bmag a · 6a · (a·a)^l`. -/

/-- `sixA a = 6a = (a + (a + a)) + (a + (a + a))`, kept additively. -/
def sixA (a : Q') : Q' := threeA a + threeA a

theorem sixA_nonneg {a : Q'} (ha0 : (0 : Q') < a) : (0 : Q') ≤ sixA a :=
  Q'.zero_le_add _ _ (threeA_nonneg ha0) (threeA_nonneg ha0)

/-- Pure associativity normal form: both bracketings of `6t` agree,
`(t+(t+t)) + (t+(t+t)) ≃ (t+t) + ((t+t)+(t+t))`. -/
theorem q_six_regroup (t : Q') :
    ((t + (t + t)) + (t + (t + t))).eqv ((t + t) + ((t + t) + (t + t))) := by
  -- Normalize both sides to the fully left-associated `(((((t+t)+t)+t)+t)+t)`.
  -- LHS: (t+(t+t)) + (t+(t+t))
  -- step A: t+(t+t) ≃ (t+t)+t  (symm assoc)
  have hA : (t + (t + t)).eqv ((t + t) + t) := Q'.eqv_symm (Q'.add_assoc_eqv t t t)
  -- LHS ≃ ((t+t)+t) + ((t+t)+t)
  have hL1 : ((t + (t + t)) + (t + (t + t))).eqv (((t + t) + t) + ((t + t) + t)) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hA)
      (Q'.add_eqv_congr_left _ _ _ hA)
  -- ((t+t)+t) + ((t+t)+t) ≃ (((t+t)+t) + (t+t)) + t   (symm assoc)
  have hL2 : (((t + t) + t) + ((t + t) + t)).eqv
      ((((t + t) + t) + (t + t)) + t) :=
    Q'.eqv_symm (Q'.add_assoc_eqv ((t + t) + t) (t + t) t)
  -- (((t+t)+t)+(t+t)) ≃ ((((t+t)+t)+t)+t)   (symm assoc on inner (t+t))
  have hL3 : ((((t + t) + t) + (t + t)) + t).eqv
      (((((t + t) + t) + t) + t) + t) :=
    Q'.add_eqv_congr_right _ _ t (Q'.eqv_symm (Q'.add_assoc_eqv ((t + t) + t) t t))
  have hLfull : ((t + (t + t)) + (t + (t + t))).eqv
      (((((t + t) + t) + t) + t) + t) :=
    Q'.eqv_trans _ _ _ hL1 (Q'.eqv_trans _ _ _ hL2 hL3)
  -- RHS: (t+t) + ((t+t)+(t+t))
  -- ((t+t)+(t+t)) ≃ (((t+t)+t)+t)
  have hR0 : ((t + t) + (t + t)).eqv (((t + t) + t) + t) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (t + t) t t)
  -- (t+t) + ((t+t)+(t+t)) ≃ (t+t) + (((t+t)+t)+t)
  have hR1 : ((t + t) + ((t + t) + (t + t))).eqv
      ((t + t) + (((t + t) + t) + t)) :=
    Q'.add_eqv_congr_left (t + t) _ _ hR0
  -- (t+t) + (((t+t)+t)+t) ≃ ((t+t)+((t+t)+t)) + t  (symm assoc)
  have hR2 : ((t + t) + (((t + t) + t) + t)).eqv
      (((t + t) + ((t + t) + t)) + t) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (t + t) ((t + t) + t) t)
  -- (t+t)+((t+t)+t) ≃ ((t+t)+(t+t))+t ≃ (((t+t)+t)+t)+t ... build to left-assoc-5 then +t
  have hR3a : ((t + t) + ((t + t) + t)).eqv (((t + t) + (t + t)) + t) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (t + t) (t + t) t)
  have hR3b : (((t + t) + (t + t)) + t).eqv ((((t + t) + t) + t) + t) :=
    Q'.add_eqv_congr_right _ _ t hR0
  have hR3 : (((t + t) + ((t + t) + t)) + t).eqv (((((t + t) + t) + t) + t) + t) :=
    Q'.add_eqv_congr_right _ _ t (Q'.eqv_trans _ _ _ hR3a hR3b)
  have hRfull : ((t + t) + ((t + t) + (t + t))).eqv
      (((((t + t) + t) + t) + t) + t) :=
    Q'.eqv_trans _ _ _ hR1 (Q'.eqv_trans _ _ _ hR2 hR3)
  exact Q'.eqv_trans _ _ _ hLfull (Q'.eqv_symm hRfull)

/-- `dBound a l ≃ sixA a · (a·a)^l` (`6·a^{2l+1} = 6a·(a²)^l`, EXACT). -/
theorem dBound_eqv_geo (a : Q') (l : Nat) :
    (dBound a l).eqv (sixA a * (a * a) ^ l) := by
  -- dBound = two c + (two c + two c),  c = geoAmp a l ≃ a·(a·a)^l
  -- = (c+c) + ((c+c)+(c+c)) = 6 copies of c ≃ 6·(a·(a·a)^l) = sixA a·(a·a)^l
  have hc : (HKPos.geoAmp a l).eqv (a * (a * a) ^ l) := ThetaConv.geoAmp_eqv a l
  -- dBound a l = (c + c) + ((c + c) + (c + c))
  show ((HKPos.geoAmp a l + HKPos.geoAmp a l)
      + ((HKPos.geoAmp a l + HKPos.geoAmp a l)
        + (HKPos.geoAmp a l + HKPos.geoAmp a l))).eqv (sixA a * (a * a) ^ l)
  -- Replace each c by a·p, p = (a·a)^l
  have hcc : (HKPos.geoAmp a l + HKPos.geoAmp a l).eqv
      (a * (a * a) ^ l + a * (a * a) ^ l) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (HKPos.geoAmp a l) hc)
      (Q'.add_eqv_congr_left (a * (a * a) ^ l) _ _ hc)
  have hrepl : ((HKPos.geoAmp a l + HKPos.geoAmp a l)
      + ((HKPos.geoAmp a l + HKPos.geoAmp a l)
        + (HKPos.geoAmp a l + HKPos.geoAmp a l))).eqv
      ((a * (a * a) ^ l + a * (a * a) ^ l)
        + ((a * (a * a) ^ l + a * (a * a) ^ l)
          + (a * (a * a) ^ l + a * (a * a) ^ l))) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hcc)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hcc)
          (Q'.add_eqv_congr_left _ _ _ hcc)))
  refine Q'.eqv_trans _ _ _ hrepl ?_
  -- 6 copies of (a·p) ≃ sixA a · p = (threeA a + threeA a)·p
  -- distribute: (threeA a + threeA a)·p ≃ threeA a·p + threeA a·p, and
  -- threeA a · p ≃ a·p + (a·p + a·p)
  show ((a * (a * a) ^ l + a * (a * a) ^ l)
      + ((a * (a * a) ^ l + a * (a * a) ^ l)
        + (a * (a * a) ^ l + a * (a * a) ^ l))).eqv
      ((threeA a + threeA a) * (a * a) ^ l)
  refine Q'.eqv_symm ?_
  -- (threeA + threeA)·p ≃ threeA·p + threeA·p
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (threeA a) (threeA a) ((a * a) ^ l)) ?_
  -- threeA a · p ≃ a·p + (a·p + a·p)  (= (a+(a+a))·p distributed)
  have hthree : (threeA a * (a * a) ^ l).eqv
      (a * (a * a) ^ l + (a * (a * a) ^ l + a * (a * a) ^ l)) := by
    show ((a + (a + a)) * (a * a) ^ l).eqv _
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a (a + a) ((a * a) ^ l)) ?_
    exact Q'.add_eqv_congr_left (a * (a * a) ^ l) _ _ (Q'.add_mul_eqv a a ((a * a) ^ l))
  -- threeA·p + threeA·p ≃ (a·p+(a·p+a·p)) + (a·p+(a·p+a·p))
  -- regroup to ((a·p+a·p) + ((a·p+a·p)+(a·p+a·p)))
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hthree)
      (Q'.add_eqv_congr_left _ _ _ hthree)) ?_
  -- now both sides are 6 copies of (a·p) but bracketed differently:
  -- LHS' = (ap+(ap+ap)) + (ap+(ap+ap)) ;  target = (ap+ap)+((ap+ap)+(ap+ap))
  -- prove by sum-of-6 associativity normal form
  exact q_six_regroup (a * (a * a) ^ l)

/-- The general-`a` engine increment constant `Cgen a = Bmag a · sixA a`
(`= |Ppart|-bound · 6a`). -/
def Cgen (a : Q') : Q' := Bmag a * sixA a

theorem Cgen_nonneg {a : Q'} (ha0 : (0 : Q') < a) : (0 : Q') ≤ Cgen a :=
  Q'.mul_nonneg _ _ (Bmag_nonneg ha0) (sixA_nonneg ha0)

/-- `dBound a l ≤ sixA a · (a·a)^l`. -/
theorem dBound_le_geo (a : Q') (l : Nat) : dBound a l ≤ sixA a * (a * a) ^ l :=
  Q'.le_of_eqv (dBound_eqv_geo a l)

/-- **Upper increment bound:** `Ppart l · dev_l ≤ Cgen a · (a·a)^l`. -/
theorem incr_le_gen {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (l : Nat) : Ppart a x l * devFac a x l ≤ Cgen a * (a * a) ^ l := by
  have hBnn : (0 : Q') ≤ Bmag a := Bmag_nonneg ha0
  have hPnn : (0 : Q') ≤ Ppart a x l := Ppart_nonneg ha0 ha1 hx l
  have hPle : Ppart a x l ≤ Bmag a := Ppart_le_Bmag ha0 ha1 hx hx1 l
  have hPlo : -(Bmag a) ≤ Ppart a x l := by
    have hneg0 : -(Bmag a) ≤ (0 : Q') := by
      have := Q'.neg_le_neg hBnn
      rwa [show (-(0 : Q')) = 0 from rfl] at this
    exact Q'.le_trans' _ _ _ hneg0 hPnn
  have hdlo : -(dBound a l) ≤ devFac a x l := neg_dBound_le_devFac ha0 ha1 hx hx1 l
  have hdhi : devFac a x l ≤ dBound a l := devFac_le ha0 ha1 hx hx1 l
  have hdBnn : (0 : Q') ≤ dBound a l := dBound_nonneg ha0 l
  -- Ppart · dev ≤ Bmag · dBound
  have hmul : Ppart a x l * devFac a x l ≤ Bmag a * dBound a l :=
    Q'.mul_le_of_bounds hBnn hdBnn hPlo hPle hdlo hdhi
  -- Bmag · dBound ≤ Bmag · (sixA·(a·a)^l) = (Bmag·sixA)·(a·a)^l = Cgen·(a·a)^l
  have hmono : Bmag a * dBound a l ≤ Bmag a * (sixA a * (a * a) ^ l) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Bmag a) (dBound_le_geo a l) hBnn
  have hassoc : (Bmag a * (sixA a * (a * a) ^ l)).eqv (Cgen a * (a * a) ^ l) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Bmag a) (sixA a) ((a * a) ^ l))
  exact Q'.le_trans' _ _ _ hmul (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hassoc))

/-- **Lower increment bound:** `−(Cgen a · (a·a)^l) ≤ Ppart l · dev_l`. -/
theorem neg_incr_le_gen {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (l : Nat) : -(Cgen a * (a * a) ^ l) ≤ Ppart a x l * devFac a x l := by
  have hBnn : (0 : Q') ≤ Bmag a := Bmag_nonneg ha0
  have hPnn : (0 : Q') ≤ Ppart a x l := Ppart_nonneg ha0 ha1 hx l
  have hPle : Ppart a x l ≤ Bmag a := Ppart_le_Bmag ha0 ha1 hx hx1 l
  have hPlo : -(Bmag a) ≤ Ppart a x l := by
    have hneg0 : -(Bmag a) ≤ (0 : Q') := by
      have := Q'.neg_le_neg hBnn
      rwa [show (-(0 : Q')) = 0 from rfl] at this
    exact Q'.le_trans' _ _ _ hneg0 hPnn
  have hdlo : -(dBound a l) ≤ devFac a x l := neg_dBound_le_devFac ha0 ha1 hx hx1 l
  have hdhi : devFac a x l ≤ dBound a l := devFac_le ha0 ha1 hx hx1 l
  have hdBnn : (0 : Q') ≤ dBound a l := dBound_nonneg ha0 l
  -- -dev ∈ [-dBound, dBound]
  have hndlo : -(dBound a l) ≤ -(devFac a x l) := Q'.neg_le_neg hdhi
  have hndhi : -(devFac a x l) ≤ dBound a l :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hdlo) (Q'.le_of_eqv (Q'.neg_neg_eqv (dBound a l)))
  have hmul : Ppart a x l * (-(devFac a x l)) ≤ Bmag a * dBound a l :=
    Q'.mul_le_of_bounds hBnn hdBnn hPlo hPle hndlo hndhi
  have hmono : Bmag a * dBound a l ≤ Bmag a * (sixA a * (a * a) ^ l) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Bmag a) (dBound_le_geo a l) hBnn
  have hassoc : (Bmag a * (sixA a * (a * a) ^ l)).eqv (Cgen a * (a * a) ^ l) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Bmag a) (sixA a) ((a * a) ^ l))
  have hupper : Ppart a x l * (-(devFac a x l)) ≤ Cgen a * (a * a) ^ l :=
    Q'.le_trans' _ _ _ hmul (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hassoc))
  -- Ppart·(-dev) ≃ -(Ppart·dev)
  have heq : (Ppart a x l * (-(devFac a x l))).eqv (-(Ppart a x l * devFac a x l)) :=
    Q'.mul_neg_eqv (Ppart a x l) (devFac a x l)
  have hneg : -(Ppart a x l * devFac a x l) ≤ Cgen a * (a * a) ^ l :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hupper
  refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hneg) ?_
  exact Q'.le_of_eqv (Q'.neg_neg_eqv (Ppart a x l * devFac a x l))

/-! ## 7. `ϑ₃(x)` as a convergent `CReal` for ALL `a ∈ (0,1)` (the deliverable)

Feed the partial products `Ppart a x` to the general-base engine
`HKConvGen.crealOfGeoIncrementBase` with the two-sided base-`(a·a)` increment
bound of §6 at the constant `Cgen a`.  No `a·a ≤ 1/2`, no smallness. -/

/-- **THE DELIVERABLE: `ϑ₃(x)` as a convergent `CReal` for ALL `a ∈ (0,1)`,
`−1 ≤ x ≤ 1`** — no `a·a ≤ 1/2`, no smallness.  `approx N = Ppart a x N`
(the genuine finite truncation `∏_{k<N}(1−a^{2k+2})·factorₖ`); the Cauchy modulus
is the base-`(a·a)` modulus inherited from `crealOfGeoIncrementBase` at the
`a`-dependent constant `Cgen a = Bmag a · 6a`. -/
def thetaConvCRealGen {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal :=
  HKConvGen.crealOfGeoIncrementBase (Ppart a x) (Cgen a) (a * a)
    (Cgen_nonneg ha0)
    (HKPos.q_mul_pos ha0 ha0)
    (aa_lt_one ha0 ha1)
    -- hup : Ppart (l+1) ≤ Ppart l + geoIncrBase (Cgen a) (a·a) l
    (fun l => by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Ppart_succ_eqv a x l)) ?_
      refine Q'.add_le_add_left (Ppart a x l) _ (HKConvGen.geoIncrBase (Cgen a) (a * a) l) ?_
      show Ppart a x l * devFac a x l ≤ Cgen a * (a * a) ^ l
      exact incr_le_gen ha0 ha1 hx hx1 l)
    -- hlo : Ppart l ≤ Ppart (l+1) + geoIncrBase (Cgen a) (a·a) l
    (fun l => by
      have heq : (Ppart a x (l + 1) + HKConvGen.geoIncrBase (Cgen a) (a * a) l).eqv
          ((Ppart a x l + Ppart a x l * devFac a x l) + Cgen a * (a * a) ^ l) :=
        Q'.add_eqv_congr_right _ _ (Cgen a * (a * a) ^ l) (Ppart_succ_eqv a x l)
      refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv heq)
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg (Ppart a x l)
          (Ppart a x l * devFac a x l + Cgen a * (a * a) ^ l) ?_)
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.add_assoc_eqv (Ppart a x l) (Ppart a x l * devFac a x l)
            (Cgen a * (a * a) ^ l))))
      -- 0 ≤ Ppart l·dev + Cgen·(a·a)^l  ⟺  -(Cgen·(a·a)^l) ≤ Ppart l·dev
      have hlo := neg_incr_le_gen ha0 ha1 hx hx1 l
      have h1 : -(Cgen a * (a * a) ^ l) + Cgen a * (a * a) ^ l
          ≤ Ppart a x l * devFac a x l + Cgen a * (a * a) ^ l :=
        Q'.add_le_add_right _ _ (Cgen a * (a * a) ^ l) hlo
      refine Q'.le_trans' _ _ _ ?_ h1
      exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (Cgen a * (a * a) ^ l)))
    -- modulus : ∃ δ>0, (Cgen a · H)·δ ≤ ε,  δ = divPos ε (Cgen a · H)
    (fun ε hε => by
      have hKpos : 0 < (Cgen a * HKConv.divPos 1 (1 + (-(a * a)))).num := by
        have hCpos : (0 : Q') ≤ Cgen a := Cgen_nonneg ha0
        -- Cgen a · H may be zero only if Cgen a = 0; here Cgen a > 0 since Bmag>0, sixA>0
        have hCgen_pos : (0 : Q') < Cgen a := by
          have hB : (0 : Q') < Bmag a := by
            show (0 : Q') < prodUp (Tcoef a) (thetaCutoff a) * Q'.ofNat 2
            exact HKPos.q_mul_pos
              (Q'.pos_of_lt_of_le (CReal.pos_of_num_pos (by decide))
                (prodUp_ge_one (Tcoef_nonneg ha0) (thetaCutoff a)))
              (by decide)
          have hsix : (0 : Q') < sixA a := by
            show (0 : Q') < threeA a + threeA a
            exact Q'.pos_of_lt_of_le (threeA_pos ha0)
              (Q'.add_le_self_of_nonneg (threeA a) (threeA a) (threeA_nonneg ha0))
          exact HKPos.q_mul_pos hB hsix
        have hDpos : (0 : Q') < HKConv.divPos 1 (1 + (-(a * a))) :=
          HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
        exact CReal.num_pos_of_pos (HKPos.q_mul_pos hCgen_pos hDpos)
      refine ⟨HKConv.divPos ε (Cgen a * HKConv.divPos 1 (1 + (-(a * a)))),
        HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
      exact HKConv.divPos_mul_eqv hKpos)

/-- `ϑ₃`'s `N`-th approximation is exactly the finite-volume partial product. -/
@[simp] theorem thetaConvCRealGen_approx {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) :
    (thetaConvCRealGen ha0 ha1 hx hx1).approx N = Ppart a x N := rfl

/-- Every approximation of the general-`a` `ϑ₃` `CReal` is `≥ 0`. -/
theorem thetaConvCRealGen_approx_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) :
    (0 : Q') ≤ (thetaConvCRealGen ha0 ha1 hx hx1).approx N := by
  rw [thetaConvCRealGen_approx]
  exact Ppart_nonneg ha0 ha1 hx N

/-- **The general-`a` `ϑ₃` `CReal`'s limit is `≥ 0`** (`ExpPos.geRat … 0`), for ALL
`a ∈ (0,1)`, `−1 ≤ x ≤ 1`. -/
theorem thetaConvCRealGen_geRat_zero {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ExpPos.geRat (thetaConvCRealGen ha0 ha1 hx hx1) 0 := by
  apply ExpPos.geRat_of_eventually
  exact ⟨0, fun N _ => thetaConvCRealGen_approx_nonneg ha0 ha1 hx hx1 N⟩

/-! ## 8. The assembled `R = ϑ₃·S ≥ 0` for ALL `a ∈ (0,1)`

Both factors are now genuine convergent `CReal`s for the full range of `a`:
`ϑ₃ = thetaConvCRealGen` (this module) and `S = sConvCReal_general`
(`HeatKernelConvGen`).  Their product's limit is `≥ 0` via
`HKConvGen.R_geRat_zero_of_theta_general` (which packages
`HKPos2.mul_geRat_zero`), with the `Θ`-hypothesis discharged by
`thetaConvCRealGen_approx_nonneg`.  This MIRRORS `ThetaConv.R_geRat_zero_sixteenth`
but removes the `a ≤ 1/16` restriction entirely. -/

/-- **THE FULL `R(x) = ϑ₃(x)·S(x) ≥ 0` as a `CReal`, for ALL `a ∈ (0,1)`,
`−1 ≤ x ≤ 1`.**  Both factors are genuine convergent `CReal`s with explicit
base-`(a·a)` moduli (`thetaConvCRealGen` and `sConvCReal_general`); their
product's limit is `≥ 0`.  This is the assembled manifest nonnegativity of the
heat-kernel product object for the full continuum range of `a`, modulo only the
separate G2 identity `K_t = R`. -/
theorem R_geRat_zero_gen {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ExpPos.geRat
      (CReal.mul (thetaConvCRealGen ha0 ha1 hx hx1)
        (HKConvGen.sConvCReal_general ha0 ha1 hx)) 0 :=
  HKConvGen.R_geRat_zero_of_theta_general ha0 ha1 hx
    (thetaConvCRealGen ha0 ha1 hx hx1)
    (thetaConvCRealGen_approx_nonneg ha0 ha1 hx hx1)

end YMGap.Continuum.ThetaConvGen

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through reused `Nat`/`Int`/`omega`/`finSum`/`decide`
helpers).  No `Classical.*`, no `native_decide`, no `sorry`. -/

#print axioms YMGap.Continuum.ThetaConvGen.prodUp_shift_eqv
#print axioms YMGap.Continuum.ThetaConvGen.prodUp_ge_one
#print axioms YMGap.Continuum.ThetaConvGen.aa_pow_cutoff_le
#print axioms YMGap.Continuum.ThetaConvGen.Tcoef_le_geo
#print axioms YMGap.Continuum.ThetaConvGen.shift_smallness
#print axioms YMGap.Continuum.ThetaConvGen.prodUp_Tcoef_le_Bmag
#print axioms YMGap.Continuum.ThetaConvGen.Ppart_le_Bmag
#print axioms YMGap.Continuum.ThetaConvGen.dBound_eqv_geo
#print axioms YMGap.Continuum.ThetaConvGen.incr_le_gen
#print axioms YMGap.Continuum.ThetaConvGen.neg_incr_le_gen
#print axioms YMGap.Continuum.ThetaConvGen.thetaConvCRealGen
#print axioms YMGap.Continuum.ThetaConvGen.thetaConvCRealGen_approx_nonneg
#print axioms YMGap.Continuum.ThetaConvGen.thetaConvCRealGen_geRat_zero
#print axioms YMGap.Continuum.ThetaConvGen.R_geRat_zero_gen
