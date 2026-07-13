/-
Growing-anchor retained-core tail for the moving-determinant route.

The quadratic cutoff is much deeper than the scale-linear theta core.  This
module splits at `growingAnchor k = 2(k+2)` and derives a uniform dyadic
enclosure of the remaining retained diagonal window.  The proof is symbolic:
one harmonic block contributes at most `1/2`, the polynomial head is absorbed
by geometric decay, and the already-proved `1/8` PF2 tail step controls every
later coefficient.

The tail ledger closes every omitted quadratic-cutoff contribution by the
single bound `dyad (2 * (k + 2) + 5)` for `k ≥ 38`.  After exact theta
rescaling, the only surviving finite-theta residual in this module is

`(qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
    dyad (2 * (k + 2) + 5) ≤ growingHeadThetaCore k`.

The theorem `normalizedGlobalSlack_nonneg_of_theta_head_linear_dyad` consumes
exactly that inequality and proves nonnegativity of the global slack.  The
displayed finite-theta inequality itself is not discharged here.
-/

import YMGap.Continuum.HarmonicMovingDeterminantAllTail
import YMGap.Continuum.HarmonicHalfEdgeDominance
import YMGap.Continuum.HarmonicThetaRepresentation
import YMGap.Continuum.CumulativeBulkShift
import YMGap.Constructive.GeomBeatsLinear

namespace YMGap.Continuum.HarmonicMovingDeterminantGrowingTail

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CumulativeBulkShift
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicHalfEdgeDominance
open YMGap.Continuum.HarmonicMovingDeterminantAllTail
open YMGap.Continuum.HarmonicMovingDeterminantDirect
open YMGap.Continuum.HarmonicMovingDeterminantRecurrence
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Block powers and the growing-anchor head -/

private theorem qpow_eqv_pow (q : Q') : ∀ n, qpow q n ≈ q ^ n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      refine Q'.eqv_trans _ (q ^ n * q) _
        (Q'.mul_eqv_congr_right _ _ q (qpow_eqv_pow q n)) ?_
      exact Q'.mul_comm_eqv (q ^ n) q

/-- Repeating the harmonic block estimate: `a` blocks of length `k+2`
contribute at most `(1/2)^a`. -/
theorem harmonic_blocks_le_half_pow (k a : Nat) :
    qpow (harmW k) ((k + 2) * a) ≤ HalfPow.half ^ a := by
  let p := qpow (harmW k) (k + 2)
  have hp0 : (0 : Q') ≤ p := qpow_nonneg _ (harmW_nonneg k) _
  have hp : p ≤ HalfPow.half := by
    dsimp only [p]
    exact harmonic_block_power_le_half k
  have hmono := FusedAmplitudeDerivation.qpow_mono_base hp0 hp a
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (HeatKernelRGStep.qpow_qpow
      (harmW k) (k + 2) a)))
    (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv (qpow_eqv_pow HalfPow.half a)))

/-- The coefficient at the growing anchor is already below `2^-83` on the
entire tail `k ≥ 38`.  No concrete tail scale is enumerated. -/
theorem growingAnchor_coeff_le_dyad83 {k : Nat} (hk : 38 ≤ k) :
    coeffW (harmW k) (growingAnchor k) ≤ dyad 83 := by
  let m := k + 2
  let n := 2 * m + 1
  let b := 2 * m + 3
  let a := 4 * m + 4
  have hexp : c4 (growingAnchor k) = (k + 2) * a := by
    change (2 * m) * (2 * m + 2) = m * a
    have hi : 2 * (2 * m + 2) = 4 * m + 4 := by omega
    calc
      (2 * m) * (2 * m + 2) = m * (2 * (2 * m + 2)) := by ac_rfl
      _ = m * (4 * m + 4) := by rw [hi]
      _ = m * a := by rfl
  have hpow : qpow (harmW k) (c4 (growingAnchor k)) ≤
      HalfPow.half ^ a := by
    rw [hexp]
    exact harmonic_blocks_le_half_pow k a
  have hn : growingAnchor k + 1 = n := by
    unfold growingAnchor
    dsimp only [m, n]
  have hab : a = n + b := by
    dsimp only [m, n, b, a]
    omega
  have hgeom : Q'.ofNat n * HalfPow.half ^ n ≤ (1 : Q') :=
    geom_beats_linear HalfPow.half_nonneg (by decide) n
  have hb0 : (0 : Q') ≤ HalfPow.half ^ b :=
    Q'.pow_nonneg _ HalfPow.half_nonneg b
  have hmul :
      (Q'.ofNat n * HalfPow.half ^ n) * HalfPow.half ^ b ≤
        (1 : Q') * HalfPow.half ^ b :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hgeom hb0
  have hpowSplit : HalfPow.half ^ a ≈
      HalfPow.half ^ n * HalfPow.half ^ b := by
    rw [hab]
    exact SU3CharFactor.pow_add_eqv HalfPow.half n b
  have hhead : coeffW (harmW k) (growingAnchor k) ≤
      HalfPow.half ^ b := by
    unfold coeffW dimQ
    rw [hn]
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat n)
      hpow (HeatKernelRGStep.zero_le_ofNat n)
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hpowSplit)
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n)
            (HalfPow.half ^ n) (HalfPow.half ^ b)))))
        (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv _))))
  have hb83 : 83 ≤ b := by
    dsimp only [b, m]
    omega
  obtain ⟨d, hbd⟩ := Nat.le.dest hb83
  have hant : HalfPow.half ^ b ≤ HalfPow.half ^ 83 := by
    rw [← hbd]
    exact ExpNeg.pow_half_antitone 83 d
  unfold dyad
  exact Q'.le_trans' _ _ _ hhead hant

/-- Scale-sensitive version of the growing-anchor estimate.  The fixed
`2^-83` bound above is its `k ≥ 38` corollary; retaining the exponent is
essential when the tail is multiplied by polynomial normalizer bounds. -/
theorem growingAnchor_coeff_le_linear_dyad (k : Nat) :
    coeffW (harmW k) (growingAnchor k) ≤ dyad (2 * (k + 2) + 3) := by
  let m := k + 2
  let n := 2 * m + 1
  let b := 2 * m + 3
  let a := 4 * m + 4
  have hexp : c4 (growingAnchor k) = (k + 2) * a := by
    change (2 * m) * (2 * m + 2) = m * a
    have hi : 2 * (2 * m + 2) = 4 * m + 4 := by omega
    calc
      (2 * m) * (2 * m + 2) = m * (2 * (2 * m + 2)) := by ac_rfl
      _ = m * (4 * m + 4) := by rw [hi]
      _ = m * a := by rfl
  have hpow : qpow (harmW k) (c4 (growingAnchor k)) ≤
      HalfPow.half ^ a := by
    rw [hexp]
    exact harmonic_blocks_le_half_pow k a
  have hn : growingAnchor k + 1 = n := by
    unfold growingAnchor
    dsimp only [m, n]
  have hab : a = n + b := by
    dsimp only [m, n, b, a]
    omega
  have hgeom : Q'.ofNat n * HalfPow.half ^ n ≤ (1 : Q') :=
    geom_beats_linear HalfPow.half_nonneg (by decide) n
  have hb0 : (0 : Q') ≤ HalfPow.half ^ b :=
    Q'.pow_nonneg _ HalfPow.half_nonneg b
  have hmul :
      (Q'.ofNat n * HalfPow.half ^ n) * HalfPow.half ^ b ≤
        (1 : Q') * HalfPow.half ^ b :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hgeom hb0
  have hpowSplit : HalfPow.half ^ a ≈
      HalfPow.half ^ n * HalfPow.half ^ b := by
    rw [hab]
    exact SU3CharFactor.pow_add_eqv HalfPow.half n b
  have hhead : coeffW (harmW k) (growingAnchor k) ≤
      HalfPow.half ^ b := by
    unfold coeffW dimQ
    rw [hn]
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat n)
      hpow (HeatKernelRGStep.zero_le_ofNat n)
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hpowSplit)
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n)
            (HalfPow.half ^ n) (HalfPow.half ^ b)))))
        (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv _))))
  unfold dyad
  dsimp only [b, m] at hhead ⊢
  exact hhead

/-! ## 2. Exact split of the retained diagonal core -/

def growingDiagTail (k : Nat) : Q' :=
  tailWindow (harmW k * harmW k) 2 (growingAnchor k + 1)
    (Ncut k - growingAnchor k)

theorem harmonicD_eq_growingHead_add_tail (k : Nat) :
    harmonicD k ≈
      coordNormSq (harmW k) (growingAnchor k) + growingDiagTail k := by
  let f := fun s => coeffW (harmW k) s * coeffW (harmW k) s
  let M := Ncut k - growingAnchor k
  have hcut : growingAnchor k + M = Ncut k :=
    Nat.add_sub_of_le (growingAnchor_le_Ncut k)
  have hsplit := FusionCoreStepRoundH.fsum_split_at
    f (growingAnchor k + 1) M
  have htail : fsum (fun j => f (growingAnchor k + 1 + j)) M ≈
      growingDiagTail k := by
    unfold growingDiagTail tailWindow
    rw [MovingCutoff.fsum_eq_finSum]
    exact finSum_eqv_congr _ _ (fun j => by
      dsimp only [f]
      exact coeffSqTerm_eqv_tailTerm k (growingAnchor k + 1 + j)) M
  unfold harmonicD coordNormSq
  dsimp only [f, M] at hsplit htail ⊢
  rw [show Ncut k + 1 = growingAnchor k + 1 +
      (Ncut k - growingAnchor k) by omega]
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr_left _ _ _ htail)

/-! ## 3. Uniform enclosure of the retained tail -/

private theorem double_dyad_succ_le (r : Nat) :
    dyad (r + 1) + dyad (r + 1) ≤ dyad r := by
  unfold dyad
  change HalfPow.half * HalfPow.half ^ r +
      HalfPow.half * HalfPow.half ^ r ≤ HalfPow.half ^ r
  exact Q'.le_of_eqv (ExpNeg.two_halves (HalfPow.half ^ r))

/-- The first coefficient after the growing anchor is at most `2^-86`.
The three extra dyadic powers are the exact `1/8` PF2 step. -/
theorem growingAnchor_succ_coeff_le_dyad86 {k : Nat} (hk : 38 ≤ k) :
    coeffW (harmW k) (growingAnchor k + 1) ≤ dyad 86 := by
  let e := Q'.mkPos 1 8 (by decide)
  have hstep : coeffW (harmW k) (growingAnchor k + 1) ≤
      e * coeffW (harmW k) (growingAnchor k) :=
    tail_eighth_of_growing_anchor k (Nat.le_refl _)
  have he0 : (0 : Q') ≤ e := by decide
  have hscaled : e * coeffW (harmW k) (growingAnchor k) ≤
      e * dyad 83 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (growingAnchor_coeff_le_dyad83 hk) he0
  have heighth : e ≈ HalfPow.half ^ 3 := by
    dsimp only [e]
    decide
  have hdyad : e * dyad 83 ≈ dyad 86 := by
    unfold dyad
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right e (HalfPow.half ^ 3)
        (HalfPow.half ^ 83) heighth) ?_
    exact Q'.eqv_symm (SU3CharFactor.pow_add_eqv HalfPow.half 3 83)
  exact Q'.le_trans' _ _ _ hstep
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hdyad))

/-- Scale-sensitive first omitted coefficient bound. -/
theorem growingAnchor_succ_coeff_le_linear_dyad (k : Nat) :
    coeffW (harmW k) (growingAnchor k + 1) ≤
      dyad (2 * (k + 2) + 6) := by
  let e := Q'.mkPos 1 8 (by decide)
  let b := 2 * (k + 2) + 3
  have hstep : coeffW (harmW k) (growingAnchor k + 1) ≤
      e * coeffW (harmW k) (growingAnchor k) :=
    tail_eighth_of_growing_anchor k (Nat.le_refl _)
  have hscaled : e * coeffW (harmW k) (growingAnchor k) ≤
      e * dyad b :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (growingAnchor_coeff_le_linear_dyad k) (by decide)
  have heighth : e ≈ HalfPow.half ^ 3 := by
    dsimp only [e]
    decide
  have hdyad : e * dyad b ≈ dyad (3 + b) := by
    unfold dyad
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right e (HalfPow.half ^ 3)
        (HalfPow.half ^ b) heighth) ?_
    exact Q'.eqv_symm (SU3CharFactor.pow_add_eqv HalfPow.half 3 b)
  have hidx : 3 + b = 2 * (k + 2) + 6 := by
    dsimp only [b]
    omega
  rw [hidx] at hdyad
  exact Q'.le_trans' _ _ _ hstep
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hdyad))

/-- The square at the head of the retained tail is at most `2^-172`. -/
theorem growingAnchor_succ_sq_le_dyad172 {k : Nat} (hk : 38 ≤ k) :
    coeffSqTerm k (growingAnchor k + 1) ≤ dyad 172 := by
  have hc := growingAnchor_succ_coeff_le_dyad86 hk
  have hsq : coeffW (harmW k) (growingAnchor k + 1) *
        coeffW (harmW k) (growingAnchor k + 1) ≤
      dyad 86 * dyad 86 :=
    Q'.mul_le_mul_of_nonneg hc hc (dyad_nonneg 86)
      (coeffW_nonneg (harmW_nonneg k) (growingAnchor k + 1))
  have hdyad : dyad 86 * dyad 86 ≈ dyad 172 := by
    unfold dyad
    exact Q'.eqv_symm (SU3CharFactor.pow_add_eqv HalfPow.half 86 86)
  unfold coeffSqTerm
  exact Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hdyad)

/-- Scale-sensitive square at the head of the retained tail. -/
theorem growingAnchor_succ_sq_le_linear_dyad (k : Nat) :
    coeffSqTerm k (growingAnchor k + 1) ≤
      dyad (4 * (k + 2) + 12) := by
  let b := 2 * (k + 2) + 6
  have hc := growingAnchor_succ_coeff_le_linear_dyad k
  have hsq : coeffW (harmW k) (growingAnchor k + 1) *
        coeffW (harmW k) (growingAnchor k + 1) ≤
      dyad b * dyad b :=
    Q'.mul_le_mul_of_nonneg hc hc (dyad_nonneg b)
      (coeffW_nonneg (harmW_nonneg k) (growingAnchor k + 1))
  have hdyad : dyad b * dyad b ≈ dyad (b + b) := by
    unfold dyad
    exact Q'.eqv_symm (SU3CharFactor.pow_add_eqv HalfPow.half b b)
  have hidx : b + b = 4 * (k + 2) + 12 := by
    dsimp only [b]
    omega
  rw [hidx] at hdyad
  unfold coeffSqTerm
  exact Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hdyad)

/-- Every squared coefficient after the growing anchor contracts by at least
`1/64`, hence by the coarser geometric ratio `1/2`. -/
theorem growingTail_sq_step_half (k j : Nat) :
    coeffSqTerm k (growingAnchor k + 1 + (j + 1)) ≤
      HalfPow.half * coeffSqTerm k (growingAnchor k + 1 + j) := by
  let a := growingAnchor k + 1 + j
  let e := Q'.mkPos 1 8 (by decide)
  have ha : growingAnchor k ≤ a := by
    dsimp only [a]
    omega
  have hstep : coeffW (harmW k) (a + 1) ≤
      e * coeffW (harmW k) a :=
    tail_eighth_of_growing_anchor k ha
  have hnext0 : (0 : Q') ≤ coeffW (harmW k) (a + 1) :=
    coeffW_nonneg (harmW_nonneg k) (a + 1)
  have hec0 : (0 : Q') ≤ e * coeffW (harmW k) a :=
    Q'.mul_nonneg _ _ (by decide)
      (coeffW_nonneg (harmW_nonneg k) a)
  have hsq : coeffW (harmW k) (a + 1) * coeffW (harmW k) (a + 1) ≤
      (e * coeffW (harmW k) a) * (e * coeffW (harmW k) a) :=
    Q'.mul_le_mul_of_nonneg hstep hstep hec0 hnext0
  have he2 : e * e ≤ HalfPow.half := by
    dsimp only [e]
    decide
  have hca2 : (0 : Q') ≤
      coeffW (harmW k) a * coeffW (harmW k) a :=
    Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) a)
      (coeffW_nonneg (harmW_nonneg k) a)
  have hscaled : (e * e) *
        (coeffW (harmW k) a * coeffW (harmW k) a) ≤
      HalfPow.half *
        (coeffW (harmW k) a * coeffW (harmW k) a) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ he2 hca2
  have hreassoc :
      (e * coeffW (harmW k) a) * (e * coeffW (harmW k) a) ≈
        (e * e) * (coeffW (harmW k) a * coeffW (harmW k) a) := by
    ring_qeqv
  unfold coeffSqTerm
  dsimp only [a] at hsq hca2 hscaled hreassoc ⊢
  rw [show growingAnchor k + 1 + (j + 1) =
      (growingAnchor k + 1 + j) + 1 by omega]
  exact Q'.le_trans' _ _ _ hsq
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) hscaled)

/-- Uniform symbolic enclosure of the entire retained diagonal window. -/
theorem growingDiagTail_le_dyad171 {k : Nat} (hk : 38 ≤ k) :
    growingDiagTail k ≤ dyad 171 := by
  let f : Nat → Q' := fun j =>
    coeffSqTerm k (growingAnchor k + 1 + j)
  have hf0 : f 0 ≤ dyad 172 := by
    dsimp only [f]
    simpa only [Nat.add_zero] using growingAnchor_succ_sq_le_dyad172 hk
  have hdom : ∀ j, f (j + 1) ≤ HalfPow.half * f j := by
    intro j
    dsimp only [f]
    exact growingTail_sq_step_half k j
  have hsum := CharacterTail.geom_series_le f (dyad 172) HalfPow.half
    (dyad 172 + dyad 172) HalfPow.half_nonneg
    (Q'.zero_le_add _ _ (dyad_nonneg 172) (dyad_nonneg 172))
    hf0 hdom (by
      refine Q'.le_of_eqv (Q'.add_eqv_congr_left (dyad 172) _ _ ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv HalfPow.half (dyad 172) (dyad 172)) ?_
      exact ExpNeg.two_halves (dyad 172))
    (Ncut k - growingAnchor k)
  have htail : growingDiagTail k ≈
      finSum f (Ncut k - growingAnchor k) := by
    unfold growingDiagTail tailWindow
    dsimp only [f]
    exact finSum_eqv_congr _ _ (fun j =>
      Q'.eqv_symm (coeffSqTerm_eqv_tailTerm k
        (growingAnchor k + 1 + j))) _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htail)
    (Q'.le_trans' _ _ _ hsum (double_dyad_succ_le 171))

/-- Scale-sensitive diagonal-tail enclosure.  Its exponent grows linearly,
so later multiplication by any fixed-degree cutoff polynomial remains
absorbable by geometric decay. -/
theorem growingDiagTail_le_linear_dyad (k : Nat) :
    growingDiagTail k ≤ dyad (4 * (k + 2) + 11) := by
  let r := 4 * (k + 2) + 11
  let f : Nat → Q' := fun j =>
    coeffSqTerm k (growingAnchor k + 1 + j)
  have hf0 : f 0 ≤ dyad (r + 1) := by
    dsimp only [f, r]
    simpa only [Nat.add_zero] using growingAnchor_succ_sq_le_linear_dyad k
  have hdom : ∀ j, f (j + 1) ≤ HalfPow.half * f j := by
    intro j
    dsimp only [f]
    exact growingTail_sq_step_half k j
  have hsum := CharacterTail.geom_series_le f (dyad (r + 1)) HalfPow.half
    (dyad (r + 1) + dyad (r + 1)) HalfPow.half_nonneg
    (Q'.zero_le_add _ _ (dyad_nonneg (r + 1)) (dyad_nonneg (r + 1)))
    hf0 hdom (by
      refine Q'.le_of_eqv (Q'.add_eqv_congr_left (dyad (r + 1)) _ _ ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv HalfPow.half (dyad (r + 1)) (dyad (r + 1))) ?_
      exact ExpNeg.two_halves (dyad (r + 1)))
    (Ncut k - growingAnchor k)
  have htail : growingDiagTail k ≈
      finSum f (Ncut k - growingAnchor k) := by
    unfold growingDiagTail tailWindow
    dsimp only [f]
    exact finSum_eqv_congr _ _ (fun j =>
      Q'.eqv_symm (coeffSqTerm_eqv_tailTerm k
        (growingAnchor k + 1 + j))) _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htail)
    (Q'.le_trans' _ _ _ hsum (double_dyad_succ_le r))

/-! ## 4. The retained adjacent-correlation tail -/

def growingAdjTail (k : Nat) : Q' :=
  fsum (fun j =>
    coeffW (harmW k) (growingAnchor k + 1 + j) *
      coeffW (harmW k) (growingAnchor k + 1 + j + 1))
    (Ncut k - (growingAnchor k + 1))

private theorem growingAnchor_succ_le_Ncut {k : Nat} (hk : 38 ≤ k) :
    growingAnchor k + 1 ≤ Ncut k := by
  have hk1 : 1 ≤ k := by omega
  have hpred := growingAnchor_le_lastCutoff (k - 1)
  have hback : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  rw [hback] at hpred
  have hN : 1 ≤ Ncut k := by
    unfold Ncut
    exact Nat.mul_pos (by omega) (by omega)
  omega

/-- Exact adjacent-core split at the same growing anchor as the diagonal
split. -/
theorem harmonicA_eq_growingHead_add_tail {k : Nat} (hk : 38 ≤ k) :
    harmonicA k ≈
      adjCorr (harmW k) (growingAnchor k + 1) + growingAdjTail k := by
  let f := fun a => coeffW (harmW k) a * coeffW (harmW k) (a + 1)
  let M := Ncut k - (growingAnchor k + 1)
  have hcut : growingAnchor k + 1 + M = Ncut k :=
    Nat.add_sub_of_le (growingAnchor_succ_le_Ncut hk)
  have hsplit := FusionCoreStepRoundH.fsum_split_at
    f (growingAnchor k + 1) M
  unfold harmonicA adjCorr growingAdjTail
  dsimp only [f, M] at hsplit ⊢
  rw [hcut] at hsplit
  exact hsplit

/-- The adjacent retained tail is paid by `1/8` of the diagonal retained
tail, using the same PF2 ratio at every edge. -/
theorem growingAdjTail_le_eighth_diag {k : Nat} (hk : 38 ≤ k) :
    growingAdjTail k ≤
      Q'.mkPos 1 8 (by decide) * growingDiagTail k := by
  let e := Q'.mkPos 1 8 (by decide)
  let M := Ncut k - (growingAnchor k + 1)
  let edge := fun j =>
    coeffW (harmW k) (growingAnchor k + 1 + j) *
      coeffW (harmW k) (growingAnchor k + 1 + j + 1)
  let sq := fun j =>
    coeffW (harmW k) (growingAnchor k + 1 + j) *
      coeffW (harmW k) (growingAnchor k + 1 + j)
  have hterm : ∀ j, edge j ≤ e * sq j := by
    intro j
    let a := growingAnchor k + 1 + j
    have ha : growingAnchor k ≤ a := by
      dsimp only [a]
      omega
    have hs : coeffW (harmW k) (a + 1) ≤
        e * coeffW (harmW k) a :=
      tail_eighth_of_growing_anchor k ha
    have hm := Q'.mul_le_mul_of_nonneg_left _ _
      (coeffW (harmW k) a) hs (coeffW_nonneg (harmW_nonneg k) a)
    change coeffW (harmW k) a * coeffW (harmW k) (a + 1) ≤
      e * (coeffW (harmW k) a * coeffW (harmW k) a)
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (by ring_qeqv))
  have hsum : fsum edge M ≤ e * fsum sq M := by
    have hs : fsum edge M ≤ fsum (fun j => e * sq j) M := by
      rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
      exact CharacterTail.finSum_le_termwise _ _ hterm M
    exact Q'.le_trans' _ _ _ hs
      (Q'.ge_of_eqv (by
        rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
        exact const_mul_finSum sq e M))
  have hsq0 : ∀ j, (0 : Q') ≤ sq j := by
    intro j
    dsimp only [sq]
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) _)
      (coeffW_nonneg (harmW_nonneg k) _)
  have hlen : M + 1 = Ncut k - growingAnchor k := by
    dsimp only [M]
    have hc := growingAnchor_succ_le_Ncut hk
    omega
  have hprefix : fsum sq M ≤ fsum sq (Ncut k - growingAnchor k) := by
    rw [← hlen]
    exact AFRateCalibration.fsum_le_of_le hsq0 (by omega)
  have he0 : (0 : Q') ≤ e := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ e hprefix he0
  have hdiag : fsum sq (Ncut k - growingAnchor k) ≈ growingDiagTail k := by
    unfold growingDiagTail tailWindow
    rw [MovingCutoff.fsum_eq_finSum]
    dsimp only [sq]
    exact finSum_eqv_congr _ _ (fun j => by
      change coeffSqTerm k (growingAnchor k + 1 + j) ≈
        tailTerm (harmW k * harmW k) 2 (growingAnchor k + 1 + j)
      exact coeffSqTerm_eqv_tailTerm k (growingAnchor k + 1 + j)) _
  unfold growingAdjTail
  dsimp only [edge, sq, M, e] at hsum hscaled hdiag ⊢
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hdiag)))

/-- Uniform dyadic enclosure of the entire retained adjacent tail. -/
theorem growingAdjTail_le_dyad174 {k : Nat} (hk : 38 ≤ k) :
    growingAdjTail k ≤ dyad 174 := by
  let e := Q'.mkPos 1 8 (by decide)
  have htail := growingAdjTail_le_eighth_diag hk
  have he0 : (0 : Q') ≤ e := by decide
  have hscaled : e * growingDiagTail k ≤ e * dyad 171 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (growingDiagTail_le_dyad171 hk) he0
  have heighth : e ≈ HalfPow.half ^ 3 := by
    dsimp only [e]
    decide
  have hdyad : e * dyad 171 ≈ dyad 174 := by
    unfold dyad
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right e (HalfPow.half ^ 3)
        (HalfPow.half ^ 171) heighth) ?_
    exact Q'.eqv_symm (SU3CharFactor.pow_add_eqv HalfPow.half 3 171)
  dsimp only [e] at hscaled
  exact Q'.le_trans' _ _ _ htail
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hdyad))

/-- Scale-sensitive adjacent-tail enclosure. -/
theorem growingAdjTail_le_linear_dyad {k : Nat} (hk : 38 ≤ k) :
    growingAdjTail k ≤ dyad (4 * (k + 2) + 14) := by
  let e := Q'.mkPos 1 8 (by decide)
  let r := 4 * (k + 2) + 11
  have htail := growingAdjTail_le_eighth_diag hk
  have hscaled : e * growingDiagTail k ≤ e * dyad r :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (growingDiagTail_le_linear_dyad k) (by decide)
  have heighth : e ≈ HalfPow.half ^ 3 := by
    dsimp only [e]
    decide
  have hdyad : e * dyad r ≈ dyad (3 + r) := by
    unfold dyad
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right e (HalfPow.half ^ 3)
        (HalfPow.half ^ r) heighth) ?_
    exact Q'.eqv_symm (SU3CharFactor.pow_add_eqv HalfPow.half 3 r)
  have hidx : 3 + r = 4 * (k + 2) + 14 := by
    dsimp only [r]
    omega
  rw [hidx] at hdyad
  dsimp only [e] at hscaled
  exact Q'.le_trans' _ _ _ htail
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hdyad))

/-! ## 5. Retained Dirichlet-deficit package -/

def growingHeadDeficit (k : Nat) : Q' :=
  coordNormSq (harmW k) (growingAnchor k) -
    adjCorr (harmW k) (growingAnchor k + 1)

def growingTailDeficit (k : Nat) : Q' :=
  growingDiagTail k - growingAdjTail k

/-- The vacuum endpoint in the exact finite Dirichlet identity gives a
cutoff-independent `1/2` lower bound for the ordinary deficit `D_N-A_N`. -/
theorem half_le_standard_deficit (w : Q') (N : Nat) :
    HalfPow.half ≤ coordNormSq w N - adjCorr w N := by
  let C0 := coeffW w 0 * coeffW w 0
  let CN := coeffW w N * coeffW w N
  let E := dirichletEnergy w N
  let X := coordNormSq w N - adjCorr w N
  have hCN : (0 : Q') ≤ CN := by
    dsimp only [CN]
    exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _
  have hE : (0 : Q') ≤ E := by
    dsimp only [E]
    exact dirichletEnergy_nonneg w N
  have hrest : (0 : Q') ≤ CN + E :=
    Q'.zero_le_add _ _ hCN hE
  have hC0 : C0 ≈ (1 : Q') := by
    dsimp only [C0]
    rw [coeffW_zero]
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv 1) (Q'.eqv_refl 1)
  have hC0R : C0 ≤ C0 + CN + E := by
    have hadd := Q'.add_le_add_left C0 0 (CN + E) hrest
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (QPoly.q_add_zero_eqv C0))
      (Q'.le_trans' _ _ _ hadd
        (Q'.ge_of_eqv (Q'.add_assoc_eqv C0 CN E)))
  have hR : (1 : Q') ≤ C0 + CN + E :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hC0) hC0R
  have hid := twice_norm_sub_corr_eq_boundary_dirichlet w N
  change Q'.ofNat 2 * X ≈ C0 + CN + E at hid
  have htwo : (1 : Q') ≤ Q'.ofNat 2 * X :=
    Q'.le_trans' _ _ _ hR (Q'.ge_of_eqv hid)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half htwo
    HalfPow.half_nonneg
  have hright : HalfPow.half * (Q'.ofNat 2 * X) ≈ X := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half (Q'.ofNat 2) X)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ X
        (by decide : HalfPow.half * Q'.ofNat 2 ≈ (1 : Q'))) ?_
    exact Q'.one_mul_eqv X
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_one_eqv HalfPow.half))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))

private theorem growingDiagTail_nonneg (k : Nat) :
    (0 : Q') ≤ growingDiagTail k := by
  unfold growingDiagTail tailWindow
  rw [← MovingCutoff.fsum_eq_finSum]
  exact fsum_nonneg (fun j => tailTerm_nonneg
    (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) 2
    (growingAnchor k + 1 + j)) _

private theorem growingAdjTail_nonneg (k : Nat) :
    (0 : Q') ≤ growingAdjTail k := by
  unfold growingAdjTail
  exact fsum_nonneg (fun j => Q'.mul_nonneg _ _
    (coeffW_nonneg (harmW_nonneg k) (growingAnchor k + 1 + j))
    (coeffW_nonneg (harmW_nonneg k) (growingAnchor k + 1 + j + 1))) _

private theorem growingAdjTail_le_diag {k : Nat} (hk : 38 ≤ k) :
    growingAdjTail k ≤ growingDiagTail k := by
  let e := Q'.mkPos 1 8 (by decide)
  have htail := growingAdjTail_le_eighth_diag hk
  have hscale : e * growingDiagTail k ≤
      (1 : Q') * growingDiagTail k :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide)
      (growingDiagTail_nonneg k)
  exact Q'.le_trans' _ _ _ htail
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv (Q'.one_mul_eqv _)))

/-- The omitted retained piece of the Dirichlet deficit is nonnegative. -/
theorem growingTailDeficit_nonneg {k : Nat} (hk : 38 ≤ k) :
    (0 : Q') ≤ growingTailDeficit k := by
  unfold growingTailDeficit
  exact Q'.sub_nonneg_of_le (growingAdjTail_le_diag hk)

private theorem sub_le_self_of_nonneg (a b : Q') (hb : (0 : Q') ≤ b) :
    a - b ≤ a := by
  have hneg : -b ≤ (0 : Q') := by
    have h := Q'.neg_le_neg hb
    simpa only using h
  have hadd := Q'.add_le_add_left a (-b) 0 hneg
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (QPoly.q_add_zero_eqv a))

/-- The omitted retained piece of the Dirichlet deficit is uniformly at most
`2^-171`; subtracting the adjacent tail only improves the estimate. -/
theorem growingTailDeficit_le_dyad171 {k : Nat} (hk : 38 ≤ k) :
    growingTailDeficit k ≤ dyad 171 := by
  unfold growingTailDeficit
  exact Q'.le_trans' _ _ _
    (sub_le_self_of_nonneg _ _ (growingAdjTail_nonneg k))
    (growingDiagTail_le_dyad171 hk)

/-- Scale-sensitive upper enclosure for the omitted Dirichlet deficit. -/
theorem growingTailDeficit_le_linear_dyad (k : Nat) :
    growingTailDeficit k ≤ dyad (4 * (k + 2) + 11) := by
  unfold growingTailDeficit
  exact Q'.le_trans' _ _ _
    (sub_le_self_of_nonneg _ _ (growingAdjTail_nonneg k))
    (growingDiagTail_le_linear_dyad k)

/-- The retained head deficit itself is nonnegative.  It is the ordinary
deficit through `anchor+1`, whose universal `1/2` vacuum reserve pays the
single terminal square (already below `2^-172`). -/
theorem growingHeadDeficit_nonneg {k : Nat} (hk : 38 ≤ k) :
    (0 : Q') ≤ growingHeadDeficit k := by
  let n := growingAnchor k
  let S := coeffW (harmW k) (n + 1) * coeffW (harmW k) (n + 1)
  let X := coordNormSq (harmW k) (n + 1) - adjCorr (harmW k) (n + 1)
  have hS : S ≤ dyad 172 := by
    dsimp only [S, n]
    exact growingAnchor_succ_sq_le_dyad172 hk
  have hdyad : dyad 172 ≤ HalfPow.half := by
    unfold dyad
    have hpow := ExpNeg.pow_half_antitone 1 171
    simpa only using hpow
  have hSX : S ≤ X :=
    Q'.le_trans' _ _ _ hS
      (Q'.le_trans' _ _ _ hdyad (half_le_standard_deficit _ _))
  have hsub : (0 : Q') ≤ X - S := Q'.sub_nonneg_of_le hSX
  have hD := coordNormSq_succ (harmW k) n
  have hreplace : X ≈
      (coordNormSq (harmW k) n + S) - adjCorr (harmW k) (n + 1) := by
    dsimp only [X, S]
    exact Q'.add_eqv_congr_right _ _ _ hD
  have hcollapse :
      ((coordNormSq (harmW k) n + S) - adjCorr (harmW k) (n + 1)) - S ≈
        coordNormSq (harmW k) n - adjCorr (harmW k) (n + 1) := by
    refine Q'.eqv_trans _
      ((coordNormSq (harmW k) n + S) +
        ((-adjCorr (harmW k) (n + 1)) + (-S))) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      ((coordNormSq (harmW k) n + (-adjCorr (harmW k) (n + 1))) +
        (S + (-S))) _ ?_ ?_
    · exact QPoly.q_interchange
        (coordNormSq (harmW k) n) S
        (-adjCorr (harmW k) (n + 1)) (-S)
    · refine Q'.eqv_trans _
        ((coordNormSq (harmW k) n + (-adjCorr (harmW k) (n + 1))) + 0) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv S)) ?_
      exact QPoly.q_add_zero_eqv _
  have hEq : X - S ≈ growingHeadDeficit k := by
    unfold growingHeadDeficit
    change X - S ≈
      coordNormSq (harmW k) n - adjCorr (harmW k) (n + 1)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-S) hreplace) hcollapse
  exact Q'.le_trans' _ _ _ hsub (Q'.le_of_eqv hEq)

/-- Exact SOS reserve presentation of the mismatched head: take the standard
deficit one node later and remove only its terminal diagonal square. -/
theorem growingHeadDeficit_eq_standard_sub_terminal (k : Nat) :
    (coordNormSq (harmW k) (growingAnchor k + 1) -
        adjCorr (harmW k) (growingAnchor k + 1)) -
      coeffSqTerm k (growingAnchor k + 1) ≈ growingHeadDeficit k := by
  let n := growingAnchor k
  let S := coeffW (harmW k) (n + 1) * coeffW (harmW k) (n + 1)
  have hD := coordNormSq_succ (harmW k) n
  have hreplace :
      coordNormSq (harmW k) (n + 1) - adjCorr (harmW k) (n + 1) ≈
        (coordNormSq (harmW k) n + S) - adjCorr (harmW k) (n + 1) := by
    dsimp only [S]
    exact Q'.add_eqv_congr_right _ _ _ hD
  unfold coeffSqTerm growingHeadDeficit
  change (coordNormSq (harmW k) (n + 1) - adjCorr (harmW k) (n + 1)) - S ≈
    coordNormSq (harmW k) n - adjCorr (harmW k) (n + 1)
  refine Q'.eqv_trans _
    (((coordNormSq (harmW k) n + S) - adjCorr (harmW k) (n + 1)) - S) _
    (Q'.add_eqv_congr_right _ _ (-S) hreplace) ?_
  refine Q'.eqv_trans _
    ((coordNormSq (harmW k) n + S) +
      ((-adjCorr (harmW k) (n + 1)) + (-S))) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    ((coordNormSq (harmW k) n + (-adjCorr (harmW k) (n + 1))) +
      (S + (-S))) _ ?_ ?_
  · exact QPoly.q_interchange
      (coordNormSq (harmW k) n) S
      (-adjCorr (harmW k) (n + 1)) (-S)
  · refine Q'.eqv_trans _
      ((coordNormSq (harmW k) n + (-adjCorr (harmW k) (n + 1))) + 0) _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv S)) ?_
    exact QPoly.q_add_zero_eqv _

/-- Scale-sensitive vacuum reserve for the retained head.  The only loss from
the universal `1/2` Dirichlet reserve is the exponentially small terminal
square. -/
theorem half_sub_linear_dyad_le_growingHeadDeficit (k : Nat) :
    HalfPow.half - dyad (4 * (k + 2) + 12) ≤ growingHeadDeficit k := by
  let X := coordNormSq (harmW k) (growingAnchor k + 1) -
    adjCorr (harmW k) (growingAnchor k + 1)
  let S := coeffSqTerm k (growingAnchor k + 1)
  let E := dyad (4 * (k + 2) + 12)
  have hS : S ≤ E := growingAnchor_succ_sq_le_linear_dyad k
  have hneg := Q'.neg_le_neg hS
  have hleft := Q'.add_le_add_left HalfPow.half (-E) (-S) hneg
  have hbase := Q'.add_le_add_right HalfPow.half X (-S)
    (half_le_standard_deficit (harmW k) (growingAnchor k + 1))
  have hchain : HalfPow.half - E ≤ X - S :=
    Q'.le_trans' _ _ _ hleft hbase
  exact Q'.le_trans' _ _ _ hchain
    (Q'.le_of_eqv (growingHeadDeficit_eq_standard_sub_terminal k))

/-- Exact retained-head plus tail decomposition of the full Dirichlet
deficit `D-A`. -/
theorem harmonicDeficit_eq_growingHead_add_tail {k : Nat} (hk : 38 ≤ k) :
    harmonicD k - harmonicA k ≈
      growingHeadDeficit k + growingTailDeficit k := by
  have hD := harmonicD_eq_growingHead_add_tail k
  have hA := harmonicA_eq_growingHead_add_tail hk
  unfold growingHeadDeficit growingTailDeficit
  refine Q'.eqv_trans _
    ((coordNormSq (harmW k) (growingAnchor k) + growingDiagTail k) -
      (adjCorr (harmW k) (growingAnchor k + 1) + growingAdjTail k)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      hD (Q'.neg_eqv_congr _ _ hA)
  · refine Q'.eqv_trans _
      ((coordNormSq (harmW k) (growingAnchor k) + growingDiagTail k) +
        (-(adjCorr (harmW k) (growingAnchor k + 1)) +
          (-growingAdjTail k))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_eqv
          (adjCorr (harmW k) (growingAnchor k + 1)) (growingAdjTail k))
    · exact QPoly.q_interchange
        (coordNormSq (harmW k) (growingAnchor k)) (growingDiagTail k)
        (-adjCorr (harmW k) (growingAnchor k + 1)) (-growingAdjTail k)

/-- The full Dirichlet deficit lies above its growing retained head. -/
theorem growingHeadDeficit_le_harmonicDeficit {k : Nat} (hk : 38 ≤ k) :
    growingHeadDeficit k ≤ harmonicD k - harmonicA k := by
  have htail := growingTailDeficit_nonneg hk
  have hadd := Q'.add_le_add_left (growingHeadDeficit k) 0
    (growingTailDeficit k) htail
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv _)) hadd)
    (Q'.ge_of_eqv (harmonicDeficit_eq_growingHead_add_tail hk))

/-- The full Dirichlet deficit differs from its retained head by at most the
uniform dyadic tail budget. -/
theorem harmonicDeficit_le_growingHead_add_dyad171 {k : Nat} (hk : 38 ≤ k) :
    harmonicD k - harmonicA k ≤
      growingHeadDeficit k + dyad 171 := by
  have hadd := Q'.add_le_add_left (growingHeadDeficit k)
    (growingTailDeficit k) (dyad 171)
    (growingTailDeficit_le_dyad171 hk)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (harmonicDeficit_eq_growingHead_add_tail hk)) hadd

/-! ## 6. Positivity-facing normalized carrier -/

/-- On the all-tail range, the exact normalized spacing gain is at most
`1/8`. -/
theorem normalizedSpacingGain_le_eighth {k : Nat} (hk : 38 ≤ k) :
    normalizedSpacingGain k ≤ Q'.mkPos 1 8 (by decide) := by
  let m := k + 2
  let p := 2 * m + 1
  let q := (m + 1) * (m + 1)
  have hm : 24 ≤ m := by
    dsimp only [m]
    omega
  have hp3 : p ≤ 3 * m := by
    dsimp only [p]
    omega
  have h8 : 8 * p ≤ 24 * m := by
    have h := Nat.mul_le_mul_left 8 hp3
    omega
  have h24 : 24 * m ≤ m * m := Nat.mul_le_mul_right m hm
  have hmm : m * m ≤ q := by
    dsimp only [q]
    exact Nat.mul_le_mul (Nat.le_succ m) (Nat.le_succ m)
  have hcross : p * 8 ≤ q := by
    omega
  have hclosed : normalizedSpacingGainClosed k ≤
      Q'.mkPos 1 8 (by decide) := by
    unfold normalizedSpacingGainClosed
    change Q'.ofNat p * unit q (Nat.mul_pos (by omega) (by omega)) ≤
      Q'.mkPos 1 8 (by decide)
    show (Q'.ofNat p * unit q _).num *
        ((Q'.mkPos 1 8 _).den : Int) ≤
      (Q'.mkPos 1 8 _).num *
        ((Q'.ofNat p * unit q _).den : Int)
    rw [Q'.mul_num_cast, Q'.mul_den_cast, unit_num, unit_den]
    change (p : Int) * 1 * 8 ≤ 1 * (1 * (q : Int))
    simp only [Int.mul_one, Int.one_mul]
    exact_mod_cast hcross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedSpacingGain_eq_closed k)) hclosed

theorem normalizedSpacingGain_nonneg (k : Nat) :
    (0 : Q') ≤ normalizedSpacingGain k := by
  have hclosed : (0 : Q') ≤ normalizedSpacingGainClosed k := by
    unfold normalizedSpacingGainClosed
    exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (unit_nonneg _ _)
  exact Q'.le_trans' _ _ _ hclosed
    (Q'.ge_of_eqv (normalizedSpacingGain_eq_closed k))

/-- Both signs in the all-tail carrier are now justified: the demand
coefficient is nonnegative and no larger than the shell fraction. -/
theorem normalizedDemandCoeff_nonneg {k : Nat} (hk : 38 ≤ k) :
    (0 : Q') ≤ normalizedDemandCoeff k := by
  unfold normalizedDemandCoeff
  exact Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _
    (normalizedSpacingGain_le_eighth hk) (by
      unfold shellDropFraction
      decide))

theorem normalizedDemandCoeff_le_shell (k : Nat) :
    normalizedDemandCoeff k ≤ shellDropFraction := by
  unfold normalizedDemandCoeff
  exact sub_le_self_of_nonneg _ _ (normalizedSpacingGain_nonneg k)

def growingHeadBoundaryCore (k : Nat) : Q' :=
  (shellDropFraction * growingHeadDeficit (k + 1)) *
      coordNormSq (harmW k) (growingAnchor k) -
    (normalizedDemandCoeff k * growingHeadDeficit k) *
      coordNormSq (harmW (k + 1)) (growingAnchor (k + 1))

/-- The retained-head Dirichlet numerator after exact theta scaling. -/
def growingHeadThetaDeficit (k : Nat) : Q' :=
  integerThetaSum (harmW k) (growingAnchor k) -
    harmW k * halfThetaSum (harmW k) (growingAnchor k + 1)

/-- The last non-tail carrier as a division-free two-weight theta cross. -/
def growingHeadThetaCore (k : Nat) : Q' :=
  (shellDropFraction * growingHeadThetaDeficit (k + 1)) *
      integerThetaSum (harmW k) (growingAnchor k) -
    (normalizedDemandCoeff k * growingHeadThetaDeficit k) *
      integerThetaSum (harmW (k + 1)) (growingAnchor (k + 1))

theorem growingHeadDeficit_theta_eqv (k : Nat) :
    qpow (harmW k) 2 * growingHeadDeficit k ≈
      growingHeadThetaDeficit k := by
  let w := harmW k
  let n := growingAnchor k
  have hD := coordNormSq_theta_eqv w n
  have hA0 := adjCorr_theta_eqv w (n + 1)
  have hq2 : qpow w 2 ≈ w * w := by
    change ((1 : Q') * w) * w ≈ w * w
    exact Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)
  have hA : qpow w 2 * adjCorr w (n + 1) ≈
      w * halfThetaSum w (n + 1) := by
    refine Q'.eqv_trans _ ((w * w) * adjCorr w (n + 1)) _
      (Q'.mul_eqv_congr_right _ _ _ hq2) ?_
    refine Q'.eqv_trans _ (w * (w * adjCorr w (n + 1))) _
      (Q'.mul_assoc_eqv w w _) ?_
    exact Q'.mul_eqv_congr_left w _ _ hA0
  unfold growingHeadDeficit growingHeadThetaDeficit
  dsimp only [w, n] at hD hA ⊢
  refine Q'.eqv_trans _
    (qpow (harmW k) 2 * coordNormSq (harmW k) (growingAnchor k) +
      -(qpow (harmW k) 2 *
        adjCorr (harmW k) (growingAnchor k + 1))) _ ?_ ?_
  · refine Q'.eqv_trans _
      (qpow (harmW k) 2 * coordNormSq (harmW k) (growingAnchor k) +
        qpow (harmW k) 2 *
          (-adjCorr (harmW k) (growingAnchor k + 1))) _
      (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv _ _)
  · exact Q'.add_eqv_congr' hD (Q'.neg_eqv_congr _ _ hA)

/-- Multiplying by the two positive theta normalizers turns the retained-head
carrier into the exact two-weight theta cross. -/
theorem growingHeadBoundaryCore_theta_eqv (k : Nat) :
    (qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
        growingHeadBoundaryCore k ≈ growingHeadThetaCore k := by
  let S0 := qpow (harmW k) 2
  let S1 := qpow (harmW (k + 1)) 2
  let H0 := growingHeadDeficit k
  let H1 := growingHeadDeficit (k + 1)
  let D0 := coordNormSq (harmW k) (growingAnchor k)
  let D1 := coordNormSq (harmW (k + 1)) (growingAnchor (k + 1))
  let T0 := growingHeadThetaDeficit k
  let T1 := growingHeadThetaDeficit (k + 1)
  let I0 := integerThetaSum (harmW k) (growingAnchor k)
  let I1 := integerThetaSum (harmW (k + 1)) (growingAnchor (k + 1))
  have hH0 : S0 * H0 ≈ T0 := growingHeadDeficit_theta_eqv k
  have hH1 : S1 * H1 ≈ T1 := growingHeadDeficit_theta_eqv (k + 1)
  have hD0 : S0 * D0 ≈ I0 := coordNormSq_theta_eqv _ _
  have hD1 : S1 * D1 ≈ I1 := coordNormSq_theta_eqv _ _
  have hpos : (S0 * S1) * ((shellDropFraction * H1) * D0) ≈
      (shellDropFraction * T1) * I0 := by
    refine Q'.eqv_trans _
      ((shellDropFraction * (S1 * H1)) * (S0 * D0)) _ ?_ ?_
    · ring_qeqv
    · refine Q'.eqv_trans _
        ((shellDropFraction * T1) * (S0 * D0)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left shellDropFraction _ _ hH1)) ?_
      exact Q'.mul_eqv_congr_left (shellDropFraction * T1) _ _ hD0
  have hneg : (S0 * S1) * ((normalizedDemandCoeff k * H0) * D1) ≈
      (normalizedDemandCoeff k * T0) * I1 := by
    refine Q'.eqv_trans _
      ((normalizedDemandCoeff k * (S0 * H0)) * (S1 * D1)) _ ?_ ?_
    · ring_qeqv
    · refine Q'.eqv_trans _
        ((normalizedDemandCoeff k * T0) * (S1 * D1)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left (normalizedDemandCoeff k) _ _ hH0)) ?_
      exact Q'.mul_eqv_congr_left (normalizedDemandCoeff k * T0) _ _ hD1
  unfold growingHeadBoundaryCore growingHeadThetaCore
  dsimp only [S0, S1, H0, H1, D0, D1, T0, T1, I0, I1] at hpos hneg ⊢
  refine Q'.eqv_trans _
    ((qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
        ((shellDropFraction * growingHeadDeficit (k + 1)) *
          coordNormSq (harmW k) (growingAnchor k)) +
      -((qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
        ((normalizedDemandCoeff k * growingHeadDeficit k) *
          coordNormSq (harmW (k + 1)) (growingAnchor (k + 1))))) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
          ((shellDropFraction * growingHeadDeficit (k + 1)) *
            coordNormSq (harmW k) (growingAnchor k)) +
        (qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
          (-((normalizedDemandCoeff k * growingHeadDeficit k) *
            coordNormSq (harmW (k + 1)) (growingAnchor (k + 1))))) _
      (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _)
  · exact Q'.add_eqv_congr' hpos (Q'.neg_eqv_congr _ _ hneg)

/-- Exact carrier after substituting the retained head/tail decompositions.
This is the positivity-facing form for the next stage; no tail term is
dropped. -/
def growingBoundaryCore (k : Nat) : Q' :=
  (shellDropFraction *
      (growingHeadDeficit (k + 1) + growingTailDeficit (k + 1))) *
      (coordNormSq (harmW k) (growingAnchor k) + growingDiagTail k) -
    (normalizedDemandCoeff k *
      (growingHeadDeficit k + growingTailDeficit k)) *
      (coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
        growingDiagTail (k + 1))

def growingPositiveTailError (k : Nat) : Q' :=
  (shellDropFraction * growingHeadDeficit (k + 1)) * growingDiagTail k +
    (shellDropFraction * growingTailDeficit (k + 1)) *
      (coordNormSq (harmW k) (growingAnchor k) + growingDiagTail k)

def growingNegativeTailError (k : Nat) : Q' :=
  (normalizedDemandCoeff k * growingHeadDeficit k) * growingDiagTail (k + 1) +
    (normalizedDemandCoeff k * growingTailDeficit k) *
      (coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
        growingDiagTail (k + 1))

def growingHeadDiagEnvelope (k : Nat) : Q' :=
  Q'.ofNat (growingAnchor k + 1) *
    (Q'.ofNat (growingAnchor k + 1) * Q'.ofNat (growingAnchor k + 1))

/-- Explicit polynomial-times-dyadic upper envelope for the adverse tail. -/
def growingNegativeTailEnvelope (k : Nat) : Q' :=
  let B := growingHeadDiagEnvelope k + growingHeadDiagEnvelope (k + 1) + (1 : Q')
  let E := dyad (4 * (k + 2) + 11)
  B * E + B * E

private theorem nat_cube_le_two_pow_of_ten : ∀ n : Nat, 10 ≤ n →
    n ^ 3 ≤ 2 ^ n
  | 0, hn => by omega
  | n + 1, hn => by
      by_cases hbase : n = 9
      · subst n
        decide
      have hn10 : 10 ≤ n := by omega
      have ih := nat_cube_le_two_pow_of_ten n hn10
      have h4n : 4 * n ≤ n * n := by
        have hm := Nat.mul_le_mul_right n (show 4 ≤ n by omega)
        simpa only [Nat.mul_comm] using hm
      have h3n1 : 3 * n + 1 ≤ n * n := by
        exact Nat.le_trans (by omega) h4n
      have hsmall : 3 * n * n + (3 * n + 1) ≤ 4 * n * n := by
        have hadd := Nat.add_le_add_left h3n1 (3 * n * n)
        have heq : 3 * n * n + n * n = 4 * n * n := by
          rw [← Nat.add_mul]
          congr 1
          omega
        exact Nat.le_trans hadd (Nat.le_of_eq heq)
      have h4nn : 4 * n * n ≤ n * n * n :=
        Nat.mul_le_mul_right n h4n
      have h4nn' : 4 * n * n ≤ n ^ 3 := by
        simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one,
          Nat.mul_assoc] using h4nn
      have hstep : (n + 1) ^ 3 ≤ 2 * (n ^ 3) := by
        calc
          (n + 1) ^ 3 = n ^ 3 + (3 * n * n + (3 * n + 1)) := by
            simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one,
              Nat.add_mul, Nat.mul_add, Nat.succ_mul,
              Nat.zero_mul, Nat.add_zero, Nat.zero_add]
            ac_rfl
          _ ≤ n ^ 3 + 4 * n * n := Nat.add_le_add_left hsmall _
          _ ≤ n ^ 3 + n ^ 3 := Nat.add_le_add_left h4nn' _
          _ = 2 * (n ^ 3) := by omega
      have hscaled := Nat.mul_le_mul_left 2 ih
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      exact Nat.le_trans hstep hscaled

private theorem ofNat_twoPow_mul_dyad_self : ∀ n : Nat,
    Q'.ofNat (2 ^ n) * dyad n ≈ (1 : Q')
  | 0 => by
      unfold dyad
      rw [Q'.pow_zero]
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (by decide)
  | n + 1 => by
      have ih := ofNat_twoPow_mul_dyad_self n
      unfold dyad at ih ⊢
      rw [Nat.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _
        ((Q'.ofNat (2 ^ n) * HalfPow.half ^ n) *
          (Q'.ofNat 2 * HalfPow.half)) _ ?_ ?_
      · refine Q'.eqv_trans _
          ((Q'.ofNat (2 ^ n) * Q'.ofNat 2) *
            (HalfPow.half * HalfPow.half ^ n)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv (2 ^ n) 2))
        · ring_qeqv
      · refine Q'.eqv_trans _ ((1 : Q') * (1 : Q')) _
          (Q'.eqv_trans _ ((1 : Q') * (Q'.ofNat 2 * HalfPow.half)) _
            (Q'.mul_eqv_congr_right _ _ _ ih)
            (Q'.mul_eqv_congr_left 1 _ _ (by decide))) ?_
        exact Q'.one_mul_eqv 1

private theorem ofNat_twoPow_mul_dyad_add (n r : Nat) :
    Q'.ofNat (2 ^ n) * dyad (n + r) ≈ dyad r := by
  have hsplit : dyad (n + r) ≈ dyad n * dyad r := by
    unfold dyad
    exact SU3CharFactor.pow_add_eqv HalfPow.half n r
  refine Q'.eqv_trans _
    (Q'.ofNat (2 ^ n) * (dyad n * dyad r)) _
    (Q'.mul_eqv_congr_left _ _ _ hsplit) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (2 ^ n) * dyad n) * dyad r) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((1 : Q') * dyad r) _
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_twoPow_mul_dyad_self n)) ?_
  exact Q'.one_mul_eqv _

private theorem dyad_add_le (r d : Nat) : dyad (r + d) ≤ dyad r := by
  unfold dyad
  exact ExpNeg.pow_half_antitone r d

/-- Above the all-tail threshold, the cubic retained-head envelope is itself
absorbed by one scale-linear power of two. -/
theorem growingHeadDiagEnvelope_le_twoPow {k : Nat} (hk : 38 ≤ k) :
    growingHeadDiagEnvelope k ≤ Q'.ofNat (2 ^ (growingAnchor k + 1)) := by
  let x := growingAnchor k + 1
  have hx : 10 ≤ x := by
    dsimp only [x]
    unfold growingAnchor
    omega
  have hnat : x * (x * x) ≤ 2 ^ x := by
    have h := nat_cube_le_two_pow_of_ten x hx
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul,
      Nat.mul_assoc] using h
  have hq : Q'.ofNat (x * (x * x)) ≤ Q'.ofNat (2 ^ x) :=
    MovingCutoff.ofNat_le_ofNat' hnat
  have heq : Q'.ofNat x * (Q'.ofNat x * Q'.ofNat x) ≈
      Q'.ofNat (x * (x * x)) := by
    refine Q'.eqv_trans _ (Q'.ofNat x * Q'.ofNat (x * x)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv x x))) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv x (x * x))
  unfold growingHeadDiagEnvelope
  dsimp only [x] at hq heq ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hq

/-- The polynomial-times-dyadic adverse envelope collapses to one explicit
scale-linear dyadic.  Thus no polynomial prefactor remains in the final
two-weight theta residual. -/
theorem growingNegativeTailEnvelope_le_linear_dyad {k : Nat} (hk : 38 ≤ k) :
    growingNegativeTailEnvelope k ≤ dyad (2 * (k + 2) + 5) := by
  let x := growingAnchor k + 1
  let y := growingAnchor (k + 1) + 1
  let D0 := growingHeadDiagEnvelope k
  let D1 := growingHeadDiagEnvelope (k + 1)
  let E := dyad (4 * (k + 2) + 11)
  let T := dyad (x + 7)
  have hyx : y = x + 2 := by
    dsimp only [x, y]
    unfold growingAnchor
    omega
  have hEidx0 : 4 * (k + 2) + 11 = x + (x + 9) := by
    dsimp only [x]
    unfold growingAnchor
    omega
  have hEidx1 : 4 * (k + 2) + 11 = y + (x + 7) := by
    rw [hyx]
    omega
  have hEidxT : 4 * (k + 2) + 11 = (x + 7) + (x + 2) := by
    dsimp only [x]
    unfold growingAnchor
    omega
  have hD0 := growingHeadDiagEnvelope_le_twoPow hk
  have hD1 := growingHeadDiagEnvelope_le_twoPow
    (show 38 ≤ k + 1 by omega)
  have hE0 : (0 : Q') ≤ E := dyad_nonneg _
  have hD0Eraw : D0 * E ≤ Q'.ofNat (2 ^ x) * E := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hD0 hE0
  have hD1Eraw : D1 * E ≤ Q'.ofNat (2 ^ y) * E := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hD1 hE0
  have hcancel0 : Q'.ofNat (2 ^ x) * E ≈ dyad (x + 9) := by
    dsimp only [E]
    rw [hEidx0]
    exact ofNat_twoPow_mul_dyad_add x (x + 9)
  have hcancel1 : Q'.ofNat (2 ^ y) * E ≈ T := by
    dsimp only [E, T]
    rw [hEidx1]
    exact ofNat_twoPow_mul_dyad_add y (x + 7)
  have hT09 : dyad (x + 9) ≤ T := by
    have h := dyad_add_le (x + 7) 2
    dsimp only [T]
    simpa only [Nat.add_assoc] using h
  have hD0E : D0 * E ≤ T :=
    Q'.le_trans' _ _ _ hD0Eraw
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcancel0) hT09)
  have hD1E : D1 * E ≤ T :=
    Q'.le_trans' _ _ _ hD1Eraw (Q'.le_of_eqv hcancel1)
  have hEle : E ≤ T := by
    have h := dyad_add_le (x + 7) (x + 2)
    dsimp only [E, T]
    rw [hEidxT]
    exact h
  have hBE : (D0 + D1 + (1 : Q')) * E ≤ (T + T) + T := by
    have hsplit : (D0 + D1 + (1 : Q')) * E ≈
        (D0 * E + D1 * E) + E := by
      refine Q'.eqv_trans _ ((D0 + D1) * E + (1 : Q') * E) _
        (Q'.add_mul_eqv _ _ _) ?_
      refine Q'.eqv_trans _ ((D0 * E + D1 * E) + (1 : Q') * E) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_mul_eqv _ _ _)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv E)
    have hsum := AFRateCalibration.q_add_le_add
      (AFRateCalibration.q_add_le_add hD0E hD1E) hEle
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hsum
  have hdouble := AFRateCalibration.q_add_le_add hBE hBE
  have hsix : ((T + T) + T) + ((T + T) + T) ≈ Q'.ofNat 6 * T := by
    have hT : T ≈ Q'.ofNat 1 * T := by
      refine Q'.eqv_trans _ ((1 : Q') * T) _
        (Q'.eqv_symm (Q'.one_mul_eqv T)) ?_
      exact Q'.mul_eqv_congr_right _ _ T (by decide)
    have hthree : (T + T) + T ≈ Q'.ofNat 3 * T := by
      refine Q'.eqv_trans _
        ((Q'.ofNat 1 * T + Q'.ofNat 1 * T) + Q'.ofNat 1 * T) _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' hT hT) hT) ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat 1 + Q'.ofNat 1) * T + Q'.ofNat 1 * T) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))) ?_
      refine Q'.eqv_trans _
        (((Q'.ofNat 1 + Q'.ofNat 1) + Q'.ofNat 1) * T) _
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_right _ _ T (by decide)
    refine Q'.eqv_trans _
      (Q'.ofNat 3 * T + Q'.ofNat 3 * T) _
      (Q'.add_eqv_congr' hthree hthree) ?_
    refine Q'.eqv_trans _ ((Q'.ofNat 3 + Q'.ofNat 3) * T) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ T (by decide)
  have h68 : Q'.ofNat 6 * T ≤ Q'.ofNat 8 * T :=
    Q'.mul_le_mul_of_nonneg_right _ _ T (by decide) (dyad_nonneg _)
  have h8collapse : Q'.ofNat 8 * T ≈ dyad (x + 4) := by
    have h8 : Q'.ofNat 8 ≈ Q'.ofNat (2 ^ 3) := by decide
    have hidx : x + 7 = 3 + (x + 4) := by omega
    dsimp only [T]
    rw [hidx]
    refine Q'.eqv_trans _ (Q'.ofNat (2 ^ 3) * dyad (3 + (x + 4))) _
      (Q'.mul_eqv_congr_right _ _ _ h8) ?_
    exact ofNat_twoPow_mul_dyad_add 3 (x + 4)
  have hgoalidx : x + 4 = 2 * (k + 2) + 5 := by
    dsimp only [x]
    unfold growingAnchor
    omega
  unfold growingNegativeTailEnvelope
  dsimp only [D0, D1, E] at hdouble ⊢
  rw [hgoalidx] at h8collapse
  exact Q'.le_trans' _ _ _ hdouble
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsix)
      (Q'.le_trans' _ _ _ h68 (Q'.le_of_eqv h8collapse)))

private theorem dyad_le_one (r : Nat) : dyad r ≤ (1 : Q') := by
  unfold dyad
  have h := ExpNeg.pow_half_antitone 0 r
  have h' : HalfPow.half ^ r ≤ HalfPow.half ^ 0 := by
    simpa only [Nat.zero_add] using h
  exact Q'.le_trans' _ _ _ h' (Q'.le_of_eqv (by
    rw [Q'.pow_zero]
    exact Q'.eqv_refl _))

theorem growingHeadDiag_le_envelope (k : Nat) :
    coordNormSq (harmW k) (growingAnchor k) ≤ growingHeadDiagEnvelope k := by
  let a := growingAnchor k
  let C := Q'.ofNat (a + 1) * Q'.ofNat (a + 1)
  have hterm : ∀ i, i < a + 1 →
      coeffW (harmW k) i * coeffW (harmW k) i ≤ C := by
    intro i hi
    have hq : qpow (harmW k) (c4 i) ≤ (1 : Q') :=
      HeatKernelGap.qpow_le_one (harmW_nonneg k) (harmW_le_one k) _
    have hc : coeffW (harmW k) i ≤ Q'.ofNat (i + 1) := by
      unfold coeffW dimQ
      have hm := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (i + 1)) hq
        (HeatKernelRGStep.zero_le_ofNat _)
      exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_one_eqv _))
    have hia : Q'.ofNat (i + 1) ≤ Q'.ofNat (a + 1) :=
      MovingCutoff.ofNat_le_ofNat' (by omega)
    have hca : coeffW (harmW k) i ≤ Q'.ofNat (a + 1) :=
      Q'.le_trans' _ _ _ hc hia
    exact Q'.mul_le_mul_of_nonneg hca hca
      (HeatKernelRGStep.zero_le_ofNat _)
      (coeffW_nonneg (harmW_nonneg k) i)
  have hsum := CumulativeBulkShift.fsum_le_const
    (h := fun i => coeffW (harmW k) i * coeffW (harmW k) i)
    (C := C) (n := a + 1) hterm
  unfold coordNormSq growingHeadDiagEnvelope
  dsimp only [a, C] at hsum ⊢
  exact hsum

private theorem growingHeadDiagEnvelope_nonneg (k : Nat) :
    (0 : Q') ≤ growingHeadDiagEnvelope k := by
  unfold growingHeadDiagEnvelope
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (HeatKernelRGStep.zero_le_ofNat _))

private theorem growingHeadDeficit_le_diagEnvelope {k : Nat} (_hk : 38 ≤ k) :
    growingHeadDeficit k ≤ growingHeadDiagEnvelope k := by
  unfold growingHeadDeficit
  exact Q'.le_trans' _ _ _
    (sub_le_self_of_nonneg _ _
      (adjCorr_nonneg (harmW_nonneg k) (growingAnchor k + 1)))
    (growingHeadDiag_le_envelope k)

/-- The adverse tail is not merely finite: it is bounded by an explicit
degree-three head envelope times the scale-sensitive dyadic decay. -/
theorem growingNegativeTailError_le_envelope {k : Nat} (hk : 38 ≤ k) :
    growingNegativeTailError k ≤ growingNegativeTailEnvelope k := by
  let D0 := growingHeadDiagEnvelope k
  let D1 := growingHeadDiagEnvelope (k + 1)
  let B := D0 + D1 + (1 : Q')
  let E := dyad (4 * (k + 2) + 11)
  have hD00 : (0 : Q') ≤ D0 := growingHeadDiagEnvelope_nonneg k
  have hD10 : (0 : Q') ≤ D1 := growingHeadDiagEnvelope_nonneg (k + 1)
  have hE0 : (0 : Q') ≤ E := dyad_nonneg _
  have hB0 : (0 : Q') ≤ B :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hD00 hD10) (by decide)
  have hc0 := normalizedDemandCoeff_nonneg hk
  have hc1 : normalizedDemandCoeff k ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (normalizedDemandCoeff_le_shell k) (by
      unfold shellDropFraction
      decide)
  have hH0 := growingHeadDeficit_le_diagEnvelope hk
  have hT0 := growingTailDeficit_le_linear_dyad k
  have hU0 := growingDiagTail_le_linear_dyad (k + 1)
  have hEE : dyad (4 * (k + 1 + 2) + 11) ≤ E := by
    dsimp only [E]
    unfold dyad
    have hpow := ExpNeg.pow_half_antitone (4 * (k + 2) + 11) 4
    have hidx : 4 * (k + 1 + 2) + 11 = (4 * (k + 2) + 11) + 4 := by
      omega
    rw [hidx]
    exact hpow
  have hU : growingDiagTail (k + 1) ≤ E :=
    Q'.le_trans' _ _ _ hU0 hEE
  have hH0nn := growingHeadDeficit_nonneg hk
  have hT0nn := growingTailDeficit_nonneg hk
  have hU0nn := growingDiagTail_nonneg (k + 1)
  have hcoefHead : normalizedDemandCoeff k * growingHeadDeficit k ≤ D0 := by
    have hm := Q'.mul_le_mul_of_nonneg hc1 hH0 (by decide) hH0nn
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv D0))
  have hfirst0 : (0 : Q') ≤
      normalizedDemandCoeff k * growingHeadDeficit k :=
    Q'.mul_nonneg _ _ hc0 hH0nn
  have hfirst :
      (normalizedDemandCoeff k * growingHeadDeficit k) *
          growingDiagTail (k + 1) ≤ B * E := by
    have hm := Q'.mul_le_mul_of_nonneg hcoefHead hU hD00 hU0nn
    have hD0B : D0 ≤ B := by
      dsimp only [B]
      have hrest : (0 : Q') ≤ D1 + (1 : Q') :=
        Q'.zero_le_add _ _ hD10 (by decide)
      have hadd := Q'.add_le_add_left D0 0 (D1 + 1) hrest
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv D0))
        (Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv (Q'.add_assoc_eqv D0 D1 1)))
    exact Q'.le_trans' _ _ _ hm
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hD0B hE0)
  have hcoefTail : normalizedDemandCoeff k * growingTailDeficit k ≤ E := by
    have hm := Q'.mul_le_mul_of_nonneg hc1 hT0 (by decide) hT0nn
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv E))
  have hheadNext :
      coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) ≤ D1 :=
    growingHeadDiag_le_envelope (k + 1)
  have hU1 : growingDiagTail (k + 1) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hU (dyad_le_one _)
  have hsumNext :
      coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
          growingDiagTail (k + 1) ≤ D1 + (1 : Q') :=
    AFRateCalibration.q_add_le_add hheadNext hU1
  have htailFactor0 : (0 : Q') ≤
      normalizedDemandCoeff k * growingTailDeficit k :=
    Q'.mul_nonneg _ _ hc0 hT0nn
  have hnext0 : (0 : Q') ≤
      coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
        growingDiagTail (k + 1) :=
    Q'.zero_le_add _ _
      (coordNormSq_nonneg (harmW_nonneg (k + 1)) _)
      (growingDiagTail_nonneg (k + 1))
  have hsecondRaw :
      (normalizedDemandCoeff k * growingTailDeficit k) *
          (coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
            growingDiagTail (k + 1)) ≤ E * (D1 + (1 : Q')) :=
    Q'.mul_le_mul_of_nonneg hcoefTail hsumNext
      hE0 hnext0
  have hD1B : D1 + (1 : Q') ≤ B := by
    dsimp only [B]
    have hadd := Q'.add_le_add_right (0 : Q') D0 (D1 + 1) hD00
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (QPoly.q_zero_add_eqv (D1 + 1)))
      (Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv (Q'.add_assoc_eqv D0 D1 1)))
  have hsecond :
      (normalizedDemandCoeff k * growingTailDeficit k) *
          (coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
            growingDiagTail (k + 1)) ≤ B * E := by
    exact Q'.le_trans' _ _ _ hsecondRaw
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ E hD1B hE0)
        (Q'.le_of_eqv (Q'.mul_comm_eqv E B)))
  unfold growingNegativeTailError growingNegativeTailEnvelope
  dsimp only [D0, D1, B, E] at hfirst hsecond ⊢
  exact AFRateCalibration.q_add_le_add hfirst hsecond

/-- Final adverse-tail estimate with no polynomial prefactor. -/
theorem growingNegativeTailError_le_linear_dyad {k : Nat} (hk : 38 ≤ k) :
    growingNegativeTailError k ≤ dyad (2 * (k + 2) + 5) :=
  Q'.le_trans' _ _ _ (growingNegativeTailError_le_envelope hk)
    (growingNegativeTailEnvelope_le_linear_dyad hk)

private theorem scaled_two_by_two_split
    (c H T D U : Q') :
    (c * (H + T)) * (D + U) ≈
      (c * H) * D + ((c * H) * U + (c * T) * (D + U)) := by
  refine Q'.eqv_trans _ ((c * H + c * T) * (D + U)) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_add_eqv c H T)) ?_
  refine Q'.eqv_trans _
    ((c * H) * (D + U) + (c * T) * (D + U)) _
    (Q'.add_mul_eqv (c * H) (c * T) (D + U)) ?_
  refine Q'.eqv_trans _
    (((c * H) * D + (c * H) * U) + (c * T) * (D + U)) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv (c * H) D U)) ?_
  exact Q'.add_assoc_eqv ((c * H) * D) ((c * H) * U)
    ((c * T) * (D + U))

/-- Exact retained-head plus signed-tail correction identity. -/
theorem growingBoundaryCore_eq_head_add_errors (k : Nat) :
    growingBoundaryCore k ≈
      (growingHeadBoundaryCore k + growingPositiveTailError k) -
        growingNegativeTailError k := by
  let P0 := (shellDropFraction * growingHeadDeficit (k + 1)) *
    coordNormSq (harmW k) (growingAnchor k)
  let PE := growingPositiveTailError k
  let N0 := (normalizedDemandCoeff k * growingHeadDeficit k) *
    coordNormSq (harmW (k + 1)) (growingAnchor (k + 1))
  let NE := growingNegativeTailError k
  have hP :
      (shellDropFraction *
        (growingHeadDeficit (k + 1) + growingTailDeficit (k + 1))) *
        (coordNormSq (harmW k) (growingAnchor k) + growingDiagTail k) ≈
      P0 + PE := by
    dsimp only [P0, PE]
    exact scaled_two_by_two_split shellDropFraction
      (growingHeadDeficit (k + 1)) (growingTailDeficit (k + 1))
      (coordNormSq (harmW k) (growingAnchor k)) (growingDiagTail k)
  have hN :
      (normalizedDemandCoeff k *
        (growingHeadDeficit k + growingTailDeficit k)) *
        (coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
          growingDiagTail (k + 1)) ≈
      N0 + NE := by
    dsimp only [N0, NE]
    exact scaled_two_by_two_split (normalizedDemandCoeff k)
      (growingHeadDeficit k) (growingTailDeficit k)
      (coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)))
      (growingDiagTail (k + 1))
  unfold growingBoundaryCore growingHeadBoundaryCore
  dsimp only [P0, PE, N0, NE] at hP hN ⊢
  refine Q'.eqv_trans _ ((P0 + PE) + -(N0 + NE)) _
    (Q'.add_eqv_congr' hP (Q'.neg_eqv_congr _ _ hN)) ?_
  refine Q'.eqv_trans _ ((P0 + PE) + ((-N0) + (-NE))) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv N0 NE)) ?_
  refine Q'.eqv_trans _ ((P0 + (-N0)) + (PE + (-NE))) _
    (QPoly.q_interchange P0 PE (-N0) (-NE)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv (P0 + (-N0)) PE (-NE))

theorem growingPositiveTailError_nonneg {k : Nat} (hk : 38 ≤ k) :
    (0 : Q') ≤ growingPositiveTailError k := by
  unfold growingPositiveTailError
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by unfold shellDropFraction; decide)
        (growingHeadDeficit_nonneg (show 38 ≤ k + 1 by omega)))
      (growingDiagTail_nonneg k))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by unfold shellDropFraction; decide)
        (growingTailDeficit_nonneg (show 38 ≤ k + 1 by omega)))
      (Q'.zero_le_add _ _
        (coordNormSq_nonneg (harmW_nonneg k) (growingAnchor k))
        (growingDiagTail_nonneg k)))

theorem growingNegativeTailError_nonneg {k : Nat} (hk : 38 ≤ k) :
    (0 : Q') ≤ growingNegativeTailError k := by
  have hc0 := normalizedDemandCoeff_nonneg hk
  unfold growingNegativeTailError
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hc0 (growingHeadDeficit_nonneg hk))
      (growingDiagTail_nonneg (k + 1)))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hc0 (growingTailDeficit_nonneg hk))
      (Q'.zero_le_add _ _
        (coordNormSq_nonneg (harmW_nonneg (k + 1)) (growingAnchor (k + 1)))
        (growingDiagTail_nonneg (k + 1))))

/-- Exact sign consumer: after the exponentially small adverse tail is paid
by the retained head, the full growing carrier is nonnegative. -/
theorem growingBoundaryCore_nonneg_of_head_budget {k : Nat} (hk : 38 ≤ k)
    (hbudget : growingNegativeTailError k ≤ growingHeadBoundaryCore k) :
    (0 : Q') ≤ growingBoundaryCore k := by
  have hpos := growingPositiveTailError_nonneg hk
  have hhead : growingNegativeTailError k ≤
      growingHeadBoundaryCore k + growingPositiveTailError k := by
    have hadd := Q'.add_le_add_left (growingHeadBoundaryCore k) 0
      (growingPositiveTailError k) hpos
    exact Q'.le_trans' _ _ _ hbudget
      (Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (QPoly.q_add_zero_eqv _)) hadd)
  have hsub : (0 : Q') ≤
      (growingHeadBoundaryCore k + growingPositiveTailError k) -
        growingNegativeTailError k := Q'.sub_nonneg_of_le hhead
  exact Q'.le_trans' _ _ _ hsub
    (Q'.ge_of_eqv (growingBoundaryCore_eq_head_add_errors k))

theorem allTailBoundaryCore_eq_growingBoundaryCore {k : Nat} (hk : 38 ≤ k) :
    allTailBoundaryCore k ≈ growingBoundaryCore k := by
  have hE0 := harmonicDeficit_eq_growingHead_add_tail hk
  have hE1 := harmonicDeficit_eq_growingHead_add_tail (show 38 ≤ k + 1 by omega)
  have hD0 := harmonicD_eq_growingHead_add_tail k
  have hD1 := harmonicD_eq_growingHead_add_tail (k + 1)
  have hpos :
      (shellDropFraction * (harmonicD (k + 1) - harmonicA (k + 1))) *
          harmonicD k ≈
        (shellDropFraction *
          (growingHeadDeficit (k + 1) + growingTailDeficit (k + 1))) *
          (coordNormSq (harmW k) (growingAnchor k) + growingDiagTail k) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (harmonicD k)
        (Q'.mul_eqv_congr_left shellDropFraction _ _ hE1)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ hD0
  have hneg :
      (normalizedDemandCoeff k * (harmonicD k - harmonicA k)) *
          harmonicD (k + 1) ≈
        (normalizedDemandCoeff k *
          (growingHeadDeficit k + growingTailDeficit k)) *
          (coordNormSq (harmW (k + 1)) (growingAnchor (k + 1)) +
            growingDiagTail (k + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (harmonicD (k + 1))
        (Q'.mul_eqv_congr_left (normalizedDemandCoeff k) _ _ hE0)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ hD1
  unfold allTailBoundaryCore growingBoundaryCore
  exact Q'.add_eqv_congr' hpos (Q'.neg_eqv_congr _ _ hneg)

theorem allTailBoundaryCore_nonneg_of_head_budget {k : Nat} (hk : 38 ≤ k)
    (hbudget : growingNegativeTailError k ≤ growingHeadBoundaryCore k) :
    (0 : Q') ≤ allTailBoundaryCore k := by
  exact Q'.le_trans' _ _ _
    (growingBoundaryCore_nonneg_of_head_budget hk hbudget)
    (Q'.le_of_eqv (Q'.eqv_symm
      (allTailBoundaryCore_eq_growingBoundaryCore hk)))

/-- End-to-end sign consumer for the normalized determinant slack.  Its sole
remaining premise is the explicit retained-head payment against the proved
exponential adverse tail. -/
theorem normalizedGlobalSlack_nonneg_of_growing_head_budget
    {k : Nat} (hk : 38 ≤ k)
    (hbudget : growingNegativeTailError k ≤ growingHeadBoundaryCore k) :
    (0 : Q') ≤ normalizedGlobalSlack k := by
  have hcore := allTailBoundaryCore_nonneg_of_head_budget hk hbudget
  have hform : (0 : Q') ≤ allTailBoundaryForm k := by
    unfold allTailBoundaryForm
    exact Q'.zero_le_add _ _ hcore hcore
  exact Q'.le_trans' _ _ _ hform
    (Q'.le_of_eqv (Q'.eqv_symm
      (normalizedGlobalSlack_eq_allTailBoundaryForm k)))

/-- A fully explicit sufficient condition for the normalized slack: it is
enough for the retained-head carrier to dominate the proved
polynomial-times-dyadic envelope. -/
theorem normalizedGlobalSlack_nonneg_of_growing_head_envelope
    {k : Nat} (hk : 38 ≤ k)
    (henvelope : growingNegativeTailEnvelope k ≤ growingHeadBoundaryCore k) :
    (0 : Q') ≤ normalizedGlobalSlack k := by
  exact normalizedGlobalSlack_nonneg_of_growing_head_budget hk
    (Q'.le_trans' _ _ _ (growingNegativeTailError_le_envelope hk) henvelope)

/-- The smallest unscaled retained-head residual after the entire omitted
tail has been paid: one scale-linear dyadic lower margin. -/
theorem normalizedGlobalSlack_nonneg_of_growing_head_linear_dyad
    {k : Nat} (hk : 38 ≤ k)
    (hhead : dyad (2 * (k + 2) + 5) ≤ growingHeadBoundaryCore k) :
    (0 : Q') ≤ normalizedGlobalSlack k := by
  exact normalizedGlobalSlack_nonneg_of_growing_head_budget hk
    (Q'.le_trans' _ _ _ (growingNegativeTailError_le_linear_dyad hk) hhead)

/-- Theta-normalized form of the final retained-head premise.  Positivity of
the scale is proved, so the finite-theta inequality cancels back to the
original unscaled envelope without any quotient. -/
theorem normalizedGlobalSlack_nonneg_of_theta_head_envelope
    {k : Nat} (hk : 38 ≤ k)
    (htheta :
      (qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
          growingNegativeTailEnvelope k ≤ growingHeadThetaCore k) :
    (0 : Q') ≤ normalizedGlobalSlack k := by
  let S := qpow (harmW k) 2 * qpow (harmW (k + 1)) 2
  have hS : (0 : Q') < S := Q'.mul_pos
    (qpow_pos (harmW_pos k) 2) (qpow_pos (harmW_pos (k + 1)) 2)
  have hscaled : S * growingNegativeTailEnvelope k ≤
      S * growingHeadBoundaryCore k :=
    Q'.le_trans' _ _ _ htheta
      (Q'.le_of_eqv (Q'.eqv_symm
        (growingHeadBoundaryCore_theta_eqv k)))
  have henvelope : growingNegativeTailEnvelope k ≤ growingHeadBoundaryCore k :=
    Q'.le_of_mul_le_mul_left hscaled hS
  exact normalizedGlobalSlack_nonneg_of_growing_head_envelope hk henvelope

/-- Exact finite-theta form of the smallest remaining residual.  The entire
quadratic-cutoff tail is reduced to the displayed single dyadic term. -/
theorem normalizedGlobalSlack_nonneg_of_theta_head_linear_dyad
    {k : Nat} (hk : 38 ≤ k)
    (htheta :
      (qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
          dyad (2 * (k + 2) + 5) ≤ growingHeadThetaCore k) :
    (0 : Q') ≤ normalizedGlobalSlack k := by
  let S := qpow (harmW k) 2 * qpow (harmW (k + 1)) 2
  have hS : (0 : Q') < S := Q'.mul_pos
    (qpow_pos (harmW_pos k) 2) (qpow_pos (harmW_pos (k + 1)) 2)
  have hscaled : S * dyad (2 * (k + 2) + 5) ≤
      S * growingHeadBoundaryCore k :=
    Q'.le_trans' _ _ _ htheta
      (Q'.le_of_eqv (Q'.eqv_symm
        (growingHeadBoundaryCore_theta_eqv k)))
  have hhead : dyad (2 * (k + 2) + 5) ≤ growingHeadBoundaryCore k :=
    Q'.le_of_mul_le_mul_left hscaled hS
  exact normalizedGlobalSlack_nonneg_of_growing_head_linear_dyad hk hhead

#print axioms harmonic_blocks_le_half_pow
#print axioms growingAnchor_coeff_le_dyad83
#print axioms growingAnchor_coeff_le_linear_dyad
#print axioms growingDiagTail
#print axioms harmonicD_eq_growingHead_add_tail
#print axioms growingAnchor_succ_coeff_le_dyad86
#print axioms growingAnchor_succ_coeff_le_linear_dyad
#print axioms growingAnchor_succ_sq_le_dyad172
#print axioms growingAnchor_succ_sq_le_linear_dyad
#print axioms growingTail_sq_step_half
#print axioms growingDiagTail_le_dyad171
#print axioms growingDiagTail_le_linear_dyad
#print axioms growingAdjTail
#print axioms harmonicA_eq_growingHead_add_tail
#print axioms growingAdjTail_le_eighth_diag
#print axioms growingAdjTail_le_dyad174
#print axioms growingAdjTail_le_linear_dyad
#print axioms growingHeadDeficit
#print axioms growingTailDeficit
#print axioms half_le_standard_deficit
#print axioms growingTailDeficit_nonneg
#print axioms growingTailDeficit_le_dyad171
#print axioms growingTailDeficit_le_linear_dyad
#print axioms growingHeadDeficit_nonneg
#print axioms growingHeadDeficit_eq_standard_sub_terminal
#print axioms half_sub_linear_dyad_le_growingHeadDeficit
#print axioms harmonicDeficit_eq_growingHead_add_tail
#print axioms growingHeadDeficit_le_harmonicDeficit
#print axioms harmonicDeficit_le_growingHead_add_dyad171
#print axioms normalizedSpacingGain_le_eighth
#print axioms normalizedSpacingGain_nonneg
#print axioms normalizedDemandCoeff_nonneg
#print axioms normalizedDemandCoeff_le_shell
#print axioms growingHeadBoundaryCore
#print axioms growingHeadThetaDeficit
#print axioms growingHeadThetaCore
#print axioms growingHeadDeficit_theta_eqv
#print axioms growingHeadBoundaryCore_theta_eqv
#print axioms growingBoundaryCore
#print axioms growingPositiveTailError
#print axioms growingNegativeTailError
#print axioms growingHeadDiagEnvelope
#print axioms growingNegativeTailEnvelope
#print axioms growingHeadDiagEnvelope_le_twoPow
#print axioms growingNegativeTailEnvelope_le_linear_dyad
#print axioms growingHeadDiag_le_envelope
#print axioms growingNegativeTailError_le_envelope
#print axioms growingNegativeTailError_le_linear_dyad
#print axioms growingBoundaryCore_eq_head_add_errors
#print axioms growingPositiveTailError_nonneg
#print axioms growingNegativeTailError_nonneg
#print axioms growingBoundaryCore_nonneg_of_head_budget
#print axioms allTailBoundaryCore_eq_growingBoundaryCore
#print axioms allTailBoundaryCore_nonneg_of_head_budget
#print axioms normalizedGlobalSlack_nonneg_of_growing_head_budget
#print axioms normalizedGlobalSlack_nonneg_of_growing_head_envelope
#print axioms normalizedGlobalSlack_nonneg_of_growing_head_linear_dyad
#print axioms normalizedGlobalSlack_nonneg_of_theta_head_envelope
#print axioms normalizedGlobalSlack_nonneg_of_theta_head_linear_dyad

end YMGap.Continuum.HarmonicMovingDeterminantGrowingTail
