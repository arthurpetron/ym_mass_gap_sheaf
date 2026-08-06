/-
Track 11.7-fusion / R2s -- summable physical p=2 dyadic gap budget.

This module completes the symbolic budget step begun by
`P2DyadicFusionGapEnvelope`.  A single honest finite-cutoff refined remainder
field is transported through the existing inverse-square window theorem.  The
physical mode-one square mismatch then has the explicit summable envelope

    6*u_k + 2*d_(k+1) + d_k,

where `u_k=(1/12)2^-k` and `d_k` is the exact `normEigShift2` defect at
`N_k=(k+2)^2`.  Finite sums are bounded by a closed expression assembled from
one geometric budget and two shifted inverse-square windows.

The last structure in the file accepts only the already-honest quotient
spectral sandwich and half-floor.  It compiles the symbolic envelope into
`SpectrumPinnedP2SummableAdditiveGapData`, hence into the genuine
`BlockingStep.Φ` defect identity and positive product floor.  No large
per-scale quotient is evaluated.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicFusionGapEnvelope

namespace YMGap.Continuum.P2DyadicFusionGapBudget

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CutoffTailRefinedCarrier
open YMGap.Continuum.LargeFieldSuppression
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionAdditiveGap
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedFusionReferenceGap
open YMGap.Continuum.ProductFloor
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The dyadic square is automatically inverse-square -/

/-- The strict right-fold power used by the heat-kernel files agrees
semantically with the constructive rational left-fold power. -/
theorem qpow_eqv_pow (w : Q') : forall n,
    qpow w n ≈ w ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := qpow_eqv_pow w n
      show qpow w n * w ≈ w * w ^ n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih) ?_
      exact Q'.mul_comm_eqv (w ^ n) w

/-- `u_k` is below the unit fraction `1/(k+2)`.  The factor `1/12` pays
for the one-index shift, so no fitted inverse-square constant is needed. -/
theorem dyadicMargin_le_unitSucc2 (k : Nat) :
    dyadicMargin k <= unit (k + 2) (by omega) := by
  have hpow : qpow half k <= Q'.invSucc k :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow half k))
      (HalfPow.pow_half_le_invSucc k)
  have h1 : dyadicMargin k <= SpectralLocalizationCrux.q112 * Q'.invSucc k :=
    Q'.mul_le_mul_of_nonneg_left _ _ SpectralLocalizationCrux.q112 hpow (by decide)
  have h2 : SpectralLocalizationCrux.q112 * Q'.invSucc k <=
      half * Q'.invSucc k :=
    Q'.mul_le_mul_of_nonneg_right _ _ (Q'.invSucc k)
      (by decide) (Q'.invSucc_nonneg k)
  have h3 := HalfPow.half_mul_invSucc_le k
  have heq : Q'.invSucc (k + 1) = unit (k + 2) (by omega) := by
    rfl
  rw [heq] at h3
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)

/-- Squaring `1/(k+2)` gives exactly the offset-two inverse-square term. -/
theorem unitSucc2_square_eqv_invSqTerm (k : Nat) :
    unit (k + 2) (by omega) * unit (k + 2) (by omega) ≈
      invSqTerm 2 (by decide) k := by
  unfold invSqTerm
  let hk : 0 < k + 2 := by omega
  let hkk : 0 < (k + 2) * (k + 2) := Nat.mul_pos hk hk
  change (unit (k + 2) hk * unit (k + 2) hk).num *
      ((unit ((k + 2) * (k + 2)) hkk).den : Int) =
    (unit ((k + 2) * (k + 2)) hkk).num *
      ((unit (k + 2) hk * unit (k + 2) hk).den : Int)
  rw [Q'.mul_den_cast, unit_num]
  change ((1 : Int) * 1) *
      ((unit ((k + 2) * (k + 2)) hkk).den : Int) =
    1 * (((unit (k + 2) hk).den : Int) *
      ((unit (k + 2) hk).den : Int))
  repeat rw [unit_den]
  rw [Int.natCast_mul, Int.one_mul]

theorem dyadicMargin_square_le_invSqTerm (k : Nat) :
    dyadicMargin k * dyadicMargin k <= invSqTerm 2 (by decide) k := by
  have hsq := BondMovingQuadratic.sq_le_sq
    (dyadicMargin_nonneg k) (dyadicMargin_le_unitSucc2 k)
  exact Q'.le_trans' _ _ _ hsq
    (Q'.le_of_eqv (unitSucc2_square_eqv_invSqTerm k))

/-! ## 2. Honest refined cutoff carrier and its window modulus -/

/-- The remaining finite-cutoff analytic input along the dyadic schedule.
`Cq` is data; the only theorem field is the exact quadratic-plus-derived-tail
bound already isolated by `CutoffTailRefinedCarrier`. -/
structure DyadicP2RefinedCutoffData (D : DyadicP2CoeffTailData) : Type where
  Cq : Q'
  Cq_nonneg : (0 : Q') <= Cq
  refinedBound : forall k,
    CutoffTailRefinedBound (Ncut k) (dyadicWeight_nonneg k)
      (dyadicWeight_le_one k) Cq 1

/-- Exact physical/reference cutoff defect on the compiled dyadic family. -/
def cutoffDefect {D : DyadicP2CoeffTailData}
    (_R : DyadicP2RefinedCutoffData D) (k : Nat) : Q' :=
  modeOneRefinedDefect D.toControlFamily k

theorem cutoffDefect_eq_moving {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (k : Nat) :
    cutoffDefect R k =
      movingRefinedDefect dyadicWeight dyadicWeight_nonneg dyadicWeight_le_one
        (fun _ => 1) k := by
  rfl

/-- The explicit bound for a defect window starting at `N`. -/
def cutoffWindowBound {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (N : Nat) : Q' :=
  R.Cq * pot 2 (by decide) N + Q'.ofNat 3 * pot 2 (by decide) N

/-- The existing corrected-carrier theorem supplies every shifted window.
The algebraic quadratic majorant is discharged here by
`dyadicMargin_square_le_invSqTerm`; it is not another field. -/
theorem cutoffDefect_window_le {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (N M : Nat) :
    tailSum (cutoffDefect R) N M <= cutoffWindowBound R N := by
  rw [show cutoffDefect R =
      movingRefinedDefect dyadicWeight dyadicWeight_nonneg dyadicWeight_le_one
        (fun _ => 1) from funext (cutoffDefect_eq_moving R)]
  exact movingRefinedDefect_window_modulus
    dyadicWeight dyadicWeight_nonneg dyadicWeight_le_one
    (fun _ => 1) dyadicMargin R.Cq R.Cq R.Cq_nonneg R.Cq_nonneg
    (fun k => Q'.le_of_eqv (one_sub_dyadicWeight_eqv_margin k))
    R.refinedBound
    (fun k => Q'.mul_le_mul_of_nonneg_left _ _ R.Cq
      (dyadicMargin_square_le_invSqTerm k) R.Cq_nonneg)
    N M

/-! ## 3. Finite-sum algebra -/

/-- `tailSum` distributes over a pointwise sum, as a semantic equality. -/
theorem tailSum_add_eqv (f g : Nat -> Q') (N : Nat) : forall M,
    tailSum (fun k => f k + g k) N M ≈
      tailSum f N M + tailSum g N M
  | 0 => Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' 0))
  | M + 1 => by
      rw [tailSum_succ, tailSum_succ, tailSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (N + M) + g (N + M))
          (tailSum_add_eqv f g N M)) ?_
      exact Q'.add_swap_inner
        (tailSum f N M) (tailSum g N M) (f (N + M)) (g (N + M))

/-- Shifting the summand by one is the same as starting the tail window at
one. -/
theorem tailSum_shift_one (f : Nat -> Q') : forall M,
    tailSum (fun k => f (k + 1)) 0 M = tailSum f 1 M
  | 0 => rfl
  | M + 1 => by
      rw [tailSum_succ, tailSum_succ, tailSum_shift_one f M]
      congr 2
      omega

/-! ## 4. Pointwise physical envelope -/

/-- Geometric reference part of the physical mismatch. -/
def referenceLoss (k : Nat) : Q' := Q'.ofNat 6 * dyadicMargin k

/-- The two shifted cutoff errors produced by the square Lipschitz bridge. -/
def cutoffLoss {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (k : Nat) : Q' :=
  Q'.ofNat 2 * cutoffDefect R (k + 1) + cutoffDefect R k

/-- Complete additive power-gap envelope. -/
def physicalGapEnvelope {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (k : Nat) : Q' :=
  referenceLoss k + cutoffLoss R k

/-- Physical mode-one fine-square-minus-coarse is bounded by the explicit
dyadic envelope. -/
theorem physical_squareGap_le_envelope {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (k : Nat) :
    fusionModeQ D.toControlFamily modeOne (k + 1) *
          fusionModeQ D.toControlFamily modeOne (k + 1) +
        -(fusionModeQ D.toControlFamily modeOne k) <=
      physicalGapEnvelope R k := by
  have hbridge := modeOne_squareGap_le_refinedGap_add_defects
    D.toControlFamily k
  have href := control_refined_squareGap_le_six_margin D k
  exact Q'.le_trans' _ _ _ hbridge
    (Q'.add_le_add href (Q'.le_refl' _))

theorem qpow_two_eqv (x : Q') : qpow x 2 ≈ x * x := by
  unfold qpow
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

/-- Additive-compiler form of the same pointwise statement. -/
theorem physical_powerGap_le_envelope {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (k : Nat) :
    qpow (fusionModeQ D.toControlFamily modeOne (k + 1)) 2 -
        fusionModeQ D.toControlFamily modeOne k <=
      physicalGapEnvelope R k := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _
      (-(fusionModeQ D.toControlFamily modeOne k))
      (qpow_two_eqv (fusionModeQ D.toControlFamily modeOne (k + 1)))))
    (physical_squareGap_le_envelope R k)

/-! ## 5. Uniform finite budget -/

theorem one_sub_half_pos : (0 : Q') < (1 : Q') - half := by decide

/-- Exact geometric-series budget for the `6*u_k` reference part. -/
def referenceBudget : Q' :=
  (Q'.ofNat 6 * SpectralLocalizationCrux.q112) *
    Q'.divPos 1 ((1 : Q') - half) one_sub_half_pos

theorem referenceLoss_le_geom (k : Nat) :
    referenceLoss k <=
      geomMajorant (Q'.ofNat 6 * SpectralLocalizationCrux.q112) half k := by
  exact Q'.le_of_eqv (Q'.eqv_symm
    (Q'.mul_assoc_eqv (Q'.ofNat 6) SpectralLocalizationCrux.q112
      (qpow half k)))

theorem referenceLoss_sum_le (n : Nat) :
    tailSum referenceLoss 0 n <= referenceBudget := by
  rw [← lossSum_eq_tailSum0 referenceLoss n]
  exact Q'.le_trans' _ _ _
    (LargeFieldSuppression.lossSum_le_termwise referenceLoss_le_geom n)
    (geomBudget_le (by decide) half_nonneg one_sub_half_pos n)

/-- Sum of the shifted cutoff losses. -/
def cutoffLossBudget {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) : Q' :=
  Q'.ofNat 2 * cutoffWindowBound R 1 + cutoffWindowBound R 0

theorem cutoffLoss_sum_le {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (n : Nat) :
    tailSum (cutoffLoss R) 0 n <= cutoffLossBudget R := by
  have hadd := tailSum_add_eqv
    (fun k => Q'.ofNat 2 * cutoffDefect R (k + 1))
    (cutoffDefect R) 0 n
  have hscale := tailSum_const_mul (Q'.ofNat 2)
    (fun k => cutoffDefect R (k + 1)) 0 n
  have hshape : tailSum (cutoffLoss R) 0 n ≈
      Q'.ofNat 2 * tailSum (cutoffDefect R) 1 n +
        tailSum (cutoffDefect R) 0 n := by
    refine Q'.eqv_trans _ _ _ hadd ?_
    refine Q'.add_eqv_congr_right _ _ (tailSum (cutoffDefect R) 0 n) ?_
    refine Q'.eqv_trans _ _ _ hscale ?_
    rw [tailSum_shift_one]
    exact Q'.eqv_refl _
  have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    (cutoffDefect_window_le R 1 n) (by decide)
  have hsum := Q'.add_le_add hfirst (cutoffDefect_window_le R 0 n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape) hsum

/-- Total finite additive-gap budget. -/
def physicalGapBudget {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) : Q' :=
  referenceBudget + cutoffLossBudget R

theorem physicalGapEnvelope_sum_le {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (n : Nat) :
    tailSum (physicalGapEnvelope R) 0 n <= physicalGapBudget R := by
  have hshape := tailSum_add_eqv referenceLoss (cutoffLoss R) 0 n
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
    (Q'.add_le_add (referenceLoss_sum_le n) (cutoffLoss_sum_le R n))

/-- The exact budget requested by the quotient-loss compiler, which sums
twice the additive envelope. -/
def quotientLossBudget {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) : Q' :=
  Q'.ofNat 2 * physicalGapBudget R

theorem twice_physicalGapEnvelope_lossSum_le
    {D : DyadicP2CoeffTailData}
    (R : DyadicP2RefinedCutoffData D) (n : Nat) :
    lossSum (fun k => Q'.ofNat 2 * physicalGapEnvelope R k) n <=
      quotientLossBudget R := by
  rw [lossSum_eq_tailSum0]
  have hscale := tailSum_const_mul (Q'.ofNat 2)
    (physicalGapEnvelope R) 0 n
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
      (physicalGapEnvelope_sum_le R n) (by decide))

/-! ## 6. Compile to the genuine Phi/product-floor consumer -/

/-- The remaining physical adjacent-scale sandwich.  Map identification is
already contained in `data`; this structure adds only the half-floor used to
remove the quotient. -/
structure DyadicP2PhysicalAdditiveInput
    (D : DyadicP2CoeffTailData) (R : DyadicP2RefinedCutoffData D)
    (B : BlockingStep (fusionSeparator D.toControlFamily modeOne)) : Type where
  data : SpectrumPinnedP2QuotientDefectPowerData
    1 D.toControlFamily modeOne B
  fineSquareHalf : forall k,
    half <= qpow (fusionModeQ D.toControlFamily modeOne (k + 1)) 2

/-- The full summable additive-gap carrier: physical pointwise gap and all
partial-sum bounds are now derived from the symbolic schedule. -/
def DyadicP2PhysicalAdditiveInput.toSummableAdditive
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (P : DyadicP2PhysicalAdditiveInput D R B) :
    SpectrumPinnedP2SummableAdditiveGapData
      1 D.toControlFamily modeOne B where
  data := P.data
  finePowerHalf := P.fineSquareHalf
  envelope := physicalGapEnvelope R
  powerGapLe := physical_powerGap_le_envelope R
  lossBound := quotientLossBudget R
  envelopeSumLe := twice_physicalGapEnvelope_lossSum_le R

/-- The resulting carrier identifies the actual `BlockingStep.Φ` action on
the dyadic mode-one trajectory. -/
theorem DyadicP2PhysicalAdditiveInput.blockDefectPowerOnTrajectory
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (P : DyadicP2PhysicalAdditiveInput D R B) :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator D.toControlFamily modeOne) B.Φ
      P.data.toCrossMul.factor :=
  P.toSummableAdditive.blockDefectPowerOnTrajectory

/-- The compiled quotient losses carry a strictly positive rational product
floor as explicit data. -/
def DyadicP2PhysicalAdditiveInput.factorProductFloorRat
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (P : DyadicP2PhysicalAdditiveInput D R B) :
    Σ' (eps : Q'), (0 : Q') < eps ∧ forall n,
      eps <= RGGapPersistence.prodPrefix P.data.toCrossMul.factor n :=
  P.toSummableAdditive.factorProductFloorRat

end YMGap.Continuum.P2DyadicFusionGapBudget

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicFusionGapBudget.dyadicMargin_square_le_invSqTerm
#print axioms YMGap.Continuum.P2DyadicFusionGapBudget.cutoffDefect_window_le
#print axioms YMGap.Continuum.P2DyadicFusionGapBudget.physical_powerGap_le_envelope
#print axioms YMGap.Continuum.P2DyadicFusionGapBudget.twice_physicalGapEnvelope_lossSum_le
#print axioms YMGap.Continuum.P2DyadicFusionGapBudget.DyadicP2PhysicalAdditiveInput.toSummableAdditive
#print axioms YMGap.Continuum.P2DyadicFusionGapBudget.DyadicP2PhysicalAdditiveInput.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2DyadicFusionGapBudget.DyadicP2PhysicalAdditiveInput.factorProductFloorRat
