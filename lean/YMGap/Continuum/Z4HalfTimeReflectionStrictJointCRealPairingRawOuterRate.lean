/-
# Raw outer Cauchy rate for the strict staged reflection pairing

The key point is the tolerance choice.  For

  h := (1/2) * epsilon,
  q := h * h,
  K := C + q.num.toNat + 1,
  t := q * invSucc (K - 1),

put `delta = slack = (1/2) * t`.  This works for every positive rational
`epsilon`, including arbitrarily large epsilon.  In particular, the proof
below does not silently assume `slack <= C`: it first proves `t <= 1`, then
`slack <= 1`, and only afterwards absorbs the slack into the enlarged budget
index `K`.

The second half packages the pointwise pairings of two staged-seminorm Cauchy
representatives as a `CReal` sequence and gives an explicit (not necessarily
antitone) raw `CReal.LeRatBound`.  Antitone closure should be a separate leaf,
using `CRealRateClosure`, before invoking `completeLimitFromRate`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStagePairingContinuity
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingAnchorBound
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Constructive.CRealCompleteRate

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingRawOuterRate

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingAnchorBound
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStagePairingContinuity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. A total, division-free continuity budget -/

/-- The square occurring on the right side of the staged continuity budget. -/
def strictJointCylinderPairingBudgetSquare (epsilon : Q') : Q' :=
  (HalfPow.half * epsilon) * (HalfPow.half * epsilon)

/-- The natural budget index.  The `q.num.toNat` summand is what makes the
choice uniform for large `epsilon`; omitting it would only control a bounded
tolerance range. -/
def strictJointCylinderPairingBudgetIndex (C : Nat) (epsilon : Q') : Nat :=
  C + (strictJointCylinderPairingBudgetSquare epsilon).num.toNat + 1

/-- The unhalved core scale `t = q / K`, written with `invSucc (K-1)` and no
division operation. -/
def strictJointCylinderPairingCoreScale (C : Nat) (epsilon : Q') : Q' :=
  strictJointCylinderPairingBudgetSquare epsilon *
    Q'.invSucc (strictJointCylinderPairingBudgetIndex C epsilon - 1)

/-- The common choice used for both `delta` and the regularity-free `slack`. -/
def strictJointCylinderPairingContinuityScale (C : Nat) (epsilon : Q') : Q' :=
  HalfPow.half * strictJointCylinderPairingCoreScale C epsilon

theorem strictJointCylinderPairingBudgetSquare_pos
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < strictJointCylinderPairingBudgetSquare epsilon := by
  have hh : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  exact Q'.mul_pos hh hh

theorem strictJointCylinderPairingContinuityScale_pos
    (C : Nat) {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < strictJointCylinderPairingContinuityScale C epsilon := by
  apply ExpNeg.half_mul_pos
  exact Q'.mul_pos
    (strictJointCylinderPairingBudgetSquare_pos hepsilon)
    (Q'.invSucc_pos _)

/-- The core scale is at most one.  The proof explicitly uses
`K - 1 >= q.num.toNat`; this is the step that makes the formula safe when
`epsilon` is large. -/
theorem strictJointCylinderPairingCoreScale_le_one
    (C : Nat) (epsilon : Q')
    (hq : (0 : Q') <= strictJointCylinderPairingBudgetSquare epsilon) :
    strictJointCylinderPairingCoreScale C epsilon <= 1 := by
  let q := strictJointCylinderPairingBudgetSquare epsilon
  let K := strictJointCylinderPairingBudgetIndex C epsilon
  have hqIndex : q.num.toNat <= K - 1 := by
    dsimp [q, K, strictJointCylinderPairingBudgetIndex]
    omega
  have hinv : Q'.invSucc (K - 1) <= Q'.invSucc q.num.toNat :=
    ExpNeg.invSucc_le_of_le hqIndex
  have hscaled : q * Q'.invSucc (K - 1) <=
      q * Q'.invSucc q.num.toNat :=
    Q'.mul_le_mul_of_nonneg_left _ _ q hinv hq
  exact Q'.le_trans' _ _ _ hscaled
    (ExpNeg.mul_invSucc_toNat_le_one q hq)

/-- In particular the actual slack is at most one.  Nothing downstream is
allowed to assume this fact without passing through this theorem. -/
theorem strictJointCylinderPairingContinuityScale_le_one
    (C : Nat) (epsilon : Q')
    (hq : (0 : Q') <= strictJointCylinderPairingBudgetSquare epsilon) :
    strictJointCylinderPairingContinuityScale C epsilon <= 1 := by
  let t := strictJointCylinderPairingCoreScale C epsilon
  have ht0 : (0 : Q') <= t := by
    dsimp [t, strictJointCylinderPairingCoreScale]
    exact Q'.mul_nonneg _ _ hq (Q'.invSucc_nonneg _)
  have hhalf : HalfPow.half * t <= 1 * t :=
    Q'.mul_le_mul_of_nonneg_right HalfPow.half 1 t (by decide) ht0
  exact Q'.le_trans' _ _ _ hhalf
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv t))
      (strictJointCylinderPairingCoreScale_le_one C epsilon hq))

/-- The concrete budget consumed by
`strictJointCylinderStageReflectionBilinear_difference_leRat`.

This theorem is stronger than the advertised `1 <= C` interface: it holds for
every natural `C`.  Later pairing code still uses `C >= 1`, because that is the
canonical property of the common anchor ceiling. -/
theorem strictJointCylinderPairingContinuityScale_budget
    (C : Nat) {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (strictJointCylinderPairingContinuityScale C epsilon +
        strictJointCylinderPairingContinuityScale C epsilon) *
      (Q'.ofNat C + strictJointCylinderPairingContinuityScale C epsilon) <=
        strictJointCylinderPairingBudgetSquare epsilon := by
  let q := strictJointCylinderPairingBudgetSquare epsilon
  let K := strictJointCylinderPairingBudgetIndex C epsilon
  let t := strictJointCylinderPairingCoreScale C epsilon
  let delta := strictJointCylinderPairingContinuityScale C epsilon
  have hqpos : (0 : Q') < q := by
    exact strictJointCylinderPairingBudgetSquare_pos hepsilon
  have hq0 : (0 : Q') <= q := Q'.le_of_lt hqpos
  have htpos : (0 : Q') < t := by
    dsimp [t, strictJointCylinderPairingCoreScale]
    exact Q'.mul_pos hqpos (Q'.invSucc_pos _)
  have ht0 : (0 : Q') <= t := Q'.le_of_lt htpos
  have hdeltaOne : delta <= 1 := by
    exact strictJointCylinderPairingContinuityScale_le_one C epsilon hq0
  have hK : 1 <= K := by
    dsimp [K, strictJointCylinderPairingBudgetIndex]
    omega
  have hC1K : C + 1 <= K := by
    dsimp [K, strictJointCylinderPairingBudgetIndex]
    omega
  have hsumEqv : (Q'.ofNat C + 1).eqv (Q'.ofNat (C + 1)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Q'.ofNat C) 1 (Q'.ofNat 1) (by decide))
      (Q'.eqv_symm (Q'.ofNat_add_eqv C 1))
  have hfactor : Q'.ofNat C + delta <= Q'.ofNat K := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (Q'.ofNat C) delta 1 hdeltaOne) ?_
    exact le_of_eqv_le hsumEqv (Q'.ofNat_le_ofNat hC1K)
  have hproduct : t * (Q'.ofNat C + delta) <= t * Q'.ofNat K :=
    Q'.mul_le_mul_of_nonneg_left _ _ t hfactor ht0
  have hdouble : (delta + delta).eqv t := by
    dsimp [delta, strictJointCylinderPairingContinuityScale]
    exact ExpNeg.two_halves t
  have hleft : (delta + delta) * (Q'.ofNat C + delta) <=
      t * Q'.ofNat K := by
    exact le_of_eqv_le
      (Q'.mul_eqv_congr_right _ _ _ hdouble) hproduct
  have hbudget : t * Q'.ofNat K <= q := by
    dsimp [t, q, K, strictJointCylinderPairingCoreScale,
      strictJointCylinderPairingBudgetIndex]
    exact Q'.budget_le (HalfPow.half * epsilon)
      (C + (strictJointCylinderPairingBudgetSquare epsilon).num.toNat + 1)
      hK
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt (ExpNeg.half_mul_pos epsilon hepsilon))
        (Q'.le_of_lt (ExpNeg.half_mul_pos epsilon hepsilon)))
  exact Q'.le_trans' _ _ _ hleft hbudget

/-! ## 2. The pairing sequence and its raw outer rate -/

variable {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
  (hle : coupling <= anchorCoupling)

private abbrev StageSeminorm : SquaredSeminorm :=
  strictJointCylinderStageSquaredSeminorm hcoupling hle

/-- Termwise strict reflection pairing of two staged-seminorm Cauchy
representatives. -/
def strictJointCylinderPairingSequence
    (X Y : (StageSeminorm hcoupling hle).Cauchy) (n : Nat) : CReal :=
  strictJointCylinderStageReflectionBilinear
    hcoupling hle (X.seq n) (Y.seq n)

/-- A common integral diagonal bound for both representatives. -/
def strictJointCylinderPairingNormCeil
    (X Y : (StageSeminorm hcoupling hle).Cauchy) : Nat :=
  max (strictJointCylinderCauchyNormCeil hcoupling hle X)
    (strictJointCylinderCauchyNormCeil hcoupling hle Y)

theorem strictJointCylinderPairing_one_le_normCeil
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    1 <= strictJointCylinderPairingNormCeil hcoupling hle X Y := by
  exact Nat.le_trans
    (strictJointCylinderCauchy_one_le_normCeil hcoupling hle X)
    (Nat.le_max_left _ _)

/-- The distance tolerance supplied to both representative moduli. -/
def strictJointCylinderPairingDelta
    (X Y : (StageSeminorm hcoupling hle).Cauchy) (epsilon : Q') : Q' :=
  strictJointCylinderPairingContinuityScale
    (strictJointCylinderPairingNormCeil hcoupling hle X Y) epsilon

/-- A raw outer rate: it simultaneously passes both finite anchor bases and
both squared-distance moduli at the concrete continuity scale.

No monotonicity of the input `Cauchy.modulus` fields is assumed, so this raw
rate is intentionally not claimed antitone. -/
def strictJointCylinderPairingRawRate
    (X Y : (StageSeminorm hcoupling hle).Cauchy) (epsilon : Q') : Nat :=
  max
    (max (strictJointCylinderCauchyNormBase hcoupling hle X)
      (strictJointCylinderCauchyNormBase hcoupling hle Y))
    (max (X.modulus (strictJointCylinderPairingDelta hcoupling hle X Y epsilon))
      (Y.modulus (strictJointCylinderPairingDelta hcoupling hle X Y epsilon)))

/-- The termwise pairings satisfy the regularity-free, two-sided outer Cauchy
bound at the explicit raw rate. -/
theorem strictJointCylinderPairingSequence_raw_leRatBound
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.LeRatBound
      (strictJointCylinderPairingSequence hcoupling hle X Y)
      (strictJointCylinderPairingRawRate hcoupling hle X Y) := by
  intro epsilon hepsilon m n hm hn
  let C := strictJointCylinderPairingNormCeil hcoupling hle X Y
  let delta := strictJointCylinderPairingDelta hcoupling hle X Y epsilon
  have hm' :
      max
        (max (strictJointCylinderCauchyNormBase hcoupling hle X)
          (strictJointCylinderCauchyNormBase hcoupling hle Y))
        (max (X.modulus delta) (Y.modulus delta)) <= m := by
    simpa [strictJointCylinderPairingRawRate, delta] using hm
  have hn' :
      max
        (max (strictJointCylinderCauchyNormBase hcoupling hle X)
          (strictJointCylinderCauchyNormBase hcoupling hle Y))
        (max (X.modulus delta) (Y.modulus delta)) <= n := by
    simpa [strictJointCylinderPairingRawRate, delta] using hn
  have hXBaseM : strictJointCylinderCauchyNormBase hcoupling hle X <= m :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm'
  have hYBaseM : strictJointCylinderCauchyNormBase hcoupling hle Y <= m :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm'
  have hXBaseN : strictJointCylinderCauchyNormBase hcoupling hle X <= n :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn'
  have hYBaseN : strictJointCylinderCauchyNormBase hcoupling hle Y <= n :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn'
  have hXModM : X.modulus delta <= m :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm'
  have hYModM : Y.modulus delta <= m :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm'
  have hXModN : X.modulus delta <= n :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn'
  have hYModN : Y.modulus delta <= n :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn'
  have hdelta : (0 : Q') < delta := by
    dsimp [delta, strictJointCylinderPairingDelta]
    exact strictJointCylinderPairingContinuityScale_pos C hepsilon
  have hleftDist :
      CReal.leRat
        (strictJointCylinderStageReflectionDistSq
          hcoupling hle (X.seq m) (X.seq n)) delta := by
    exact X.isCauchy delta hdelta m n hXModM hXModN
  have hrightDist :
      CReal.leRat
        (strictJointCylinderStageReflectionDistSq
          hcoupling hle (Y.seq m) (Y.seq n)) delta := by
    exact Y.isCauchy delta hdelta m n hYModM hYModN
  have hrightBound :
      CReal.leRat
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle (Y.seq m) (Y.seq m))
        (Q'.ofNat C) := by
    refine CReal.leRat_mono
      (strictJointCylinderCauchy_self_leRat_normCeil
        hcoupling hle Y m hYBaseM) ?_
    dsimp [C, strictJointCylinderPairingNormCeil]
    exact Q'.ofNat_le_ofNat (Nat.le_max_right _ _)
  have hleft'Bound :
      CReal.leRat
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle (X.seq n) (X.seq n))
        (Q'.ofNat C) := by
    refine CReal.leRat_mono
      (strictJointCylinderCauchy_self_leRat_normCeil
        hcoupling hle X n hXBaseN) ?_
    dsimp [C, strictJointCylinderPairingNormCeil]
    exact Q'.ofNat_le_ofNat (Nat.le_max_left _ _)
  have hbudget :
      (delta + delta) * (Q'.ofNat C + delta) <=
        (HalfPow.half * epsilon) * (HalfPow.half * epsilon) := by
    dsimp [delta, strictJointCylinderPairingDelta]
    exact strictJointCylinderPairingContinuityScale_budget C hepsilon
  simpa [strictJointCylinderPairingSequence] using
    (strictJointCylinderStageReflectionBilinear_difference_leRat
      hcoupling hle
      (X.seq m) (X.seq n) (Y.seq m) (Y.seq n)
      epsilon delta (Q'.ofNat C) delta
      hepsilon hdelta hdelta hleftDist hrightDist
      hrightBound hleft'Bound hbudget)

#print axioms strictJointCylinderPairingContinuityScale_budget
#print axioms strictJointCylinderPairingSequence_raw_leRatBound

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingRawOuterRate
