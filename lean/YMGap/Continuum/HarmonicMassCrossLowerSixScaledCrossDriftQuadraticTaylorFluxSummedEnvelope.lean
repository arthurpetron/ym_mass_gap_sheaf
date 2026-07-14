/-
Summed Gaussian envelope for the cleared lower-six Taylor flux.

The finite-D remainder is not pointwise nonnegative, even after its positive
Hermite mass is restored.  This file supplies a linearly tapered Bernoulli
head below the complete mass sum and reduces the summed block to one explicit
remainder payment against a closed square-root-window polynomial.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative
import YMGap.Continuum.RDThetaCentered

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.RDThetaCentered
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- Complete positive Hermite mass over the shared physical modes. -/
def lowerSixHermiteMassSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1))
    (growingAnchor k)

def lowerSixHermiteWeightSum (k : Nat) : Q' :=
  finSum (fun j => lowerSixModeWeight k (j + 1)) (growingAnchor k)

/-- Complete signed finite-D Hermite remainder over those modes. -/
def lowerSixHermiteRemainderSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDiscreteHermiteRemainder k (j + 1))
    (growingAnchor k)

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

theorem lowerSixHermiteMassSum_eqv_scaledWeightSum (k : Nat) :
    lowerSixHermiteMassSum k ≈
      (Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) *
        lowerSixHermiteWeightSum k := by
  let C := Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  unfold lowerSixHermiteMassSum lowerSixHermiteWeightSum
  refine Q'.eqv_trans _
      (finSum (fun j => C * lowerSixModeWeight k (j + 1))
        (growingAnchor k)) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _ (fun _ => by
      unfold lowerSixDiscreteHermiteMassNumerator
      exact Q'.eqv_refl _) _
  · exact Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun j => lowerSixModeWeight k (j + 1)) C (growingAnchor k))

private theorem square_harmW_le_one (k : Nat) :
    harmW k * harmW k ≤ (1 : Q') := by
  have hmul := Q'.mul_le_mul_of_nonneg
    (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.one_mul_eqv 1))

private abbrev PE := RingNormaliser.PolyExpr

private def pOneSubSquareL : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .add (.const 1) (.neg (.mul w w))

private def pOneSubSquareR : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .mul u (.add (.const 1) w)

private theorem pOneSubSquare_normal :
    RingNormaliser.normalize pOneSubSquareL =
      RingNormaliser.normalize pOneSubSquareR := by decide

private theorem oneSubSquare_algebra (u : Q') :
    (1 : Q') + -(((1 : Q') + -u) * ((1 : Q') + -u)) ≈
      u * ((1 : Q') + ((1 : Q') + -u)) := by
  simpa [pOneSubSquareL, pOneSubSquareR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pOneSubSquareL pOneSubSquareR pOneSubSquare_normal (fun _ => u))

private theorem one_sub_harmW_square_eqv (k : Nat) :
    (1 : Q') - harmW k * harmW k ≈
      harmU k * ((1 : Q') + harmW k) := by
  change (1 : Q') + -(harmW k * harmW k) ≈
    harmU k * ((1 : Q') + harmW k)
  unfold harmW oneSub
  exact oneSubSquare_algebra _

private theorem one_sub_harmW_square_le_two_harmU (k : Nat) :
    (1 : Q') - harmW k * harmW k ≤ Q'.ofNat 2 * harmU k := by
  have hsum : (1 : Q') + harmW k ≤ (1 : Q') + 1 :=
    Q'.add_le_add_left (1 : Q') _ _ (harmW_le_one k)
  have hmul : harmU k * ((1 : Q') + harmW k) ≤
      harmU k * ((1 : Q') + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (harmU_nonneg k)
  have htwo : harmU k * ((1 : Q') + 1) ≈
      Q'.ofNat 2 * harmU k := by
    refine Q'.eqv_trans _ (((1 : Q') + 1) * harmU k) _
      (Q'.mul_comm_eqv _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (one_sub_harmW_square_eqv k))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv htwo))

/-- Linearly tapered Bernoulli cell on the full square-root head. -/
def lowerSixHermiteLinearHeadCell (k n : Nat) : Q' :=
  (1 : Q') - Q'.ofNat (n * n) *
    ((1 : Q') - harmW k * harmW k)

def lowerSixHermiteLinearHeadSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixHermiteLinearHeadCell k (j + 1))
    (thetaWindowLeft k)

def lowerSixHermiteLinearHeadMassFloor (k : Nat) : Q' :=
  (Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) *
    lowerSixHermiteLinearHeadSum k

private theorem thetaWindowLeft_two_sq_le_den
    {k n : Nat} (hn : n ≤ thetaWindowLeft k) :
    2 * (n * n) ≤ k + 2 := by
  let c := thetaWindowCenter k
  have h2n : 2 * n ≤ c := by
    dsimp only [c]
    unfold thetaWindowLeft at hn
    omega
  have hsquare : (2 * n) * (2 * n) ≤ c * c :=
    Nat.mul_le_mul h2n h2n
  have hcSq : c * c ≤ 2 * (k + 2) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hfour : 4 * (n * n) ≤ 2 * (k + 2) + 1 := by
    have heq : 4 * (n * n) = (2 * n) * (2 * n) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq]
    exact Nat.le_trans hsquare hcSq
  omega

theorem lowerSixHermiteLinearHeadCell_nonnegative
    {k n : Nat} (hn : n ≤ thetaWindowLeft k) :
    (0 : Q') ≤ lowerSixHermiteLinearHeadCell k n := by
  have hmargin := one_sub_harmW_square_le_two_harmU k
  have hn0 : (0 : Q') ≤ Q'.ofNat (n * n) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (n * n)) hmargin hn0
  have hnat := thetaWindowLeft_two_sq_le_den hn
  have hunit :
      Q'.ofNat (n * n) * (Q'.ofNat 2 * harmU k) ≤ (1 : Q') := by
    unfold harmU unit
    show (Q'.ofNat (n * n) *
          (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega))).num *
          ((1 : Q').den : Int) ≤
        (1 : Q').num *
          (Q'.ofNat (n * n) *
            (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega))).den
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
      Int.mul_one, Int.one_mul]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    push_cast
    have hnat' : n * n * 2 ≤ k + 1 + 1 := by omega
    exact_mod_cast hnat'
  unfold lowerSixHermiteLinearHeadCell
  exact Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ hmul hunit)

theorem lowerSixHermiteLinearHeadSum_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixHermiteLinearHeadSum k := by
  unfold lowerSixHermiteLinearHeadSum
  let f := fun j => lowerSixHermiteLinearHeadCell k (j + 1)
  have hf : ∀ j, j < thetaWindowLeft k → (0 : Q') ≤ f j := by
    intro j hj
    exact lowerSixHermiteLinearHeadCell_nonnegative (by omega)
  have hrec : ∀ N, N ≤ thetaWindowLeft k → (0 : Q') ≤ finSum f N := by
    intro N hN
    induction N with
    | zero => exact Q'.le_refl' 0
    | succ M ih =>
        rw [finSum_succ]
        exact Q'.zero_le_add _ _ (ih (by omega)) (hf M (by omega))
  exact hrec _ (Nat.le_refl _)

private theorem finSum_one_eqv_ofNat : ∀ N,
    finSum (fun _ => (1 : Q')) N ≈ Q'.ofNat N
  | 0 => by decide
  | N + 1 => by
      rw [finSum_succ]
      refine Q'.eqv_trans _ (Q'.ofNat N + (1 : Q')) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ (finSum_one_eqv_ofNat N)
      · exact Q'.eqv_trans _ (Q'.ofNat N + Q'.ofNat 1) _
          (Q'.add_eqv_congr_left _ _ _ (by decide))
          (Q'.eqv_symm (Q'.ofNat_add_eqv N 1))

private theorem finSum_shifted_squares_eqv_sumSq : ∀ N,
    finSum (fun j => Q'.ofNat ((j + 1) * (j + 1))) N ≈
      Q'.ofNat (sumSq N)
  | 0 => by decide
  | N + 1 => by
      rw [finSum_succ]
      refine Q'.eqv_trans _
        (Q'.ofNat (sumSq N) + Q'.ofNat ((N + 1) * (N + 1))) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_shifted_squares_eqv_sumSq N)
      · rw [sumSq]
        exact Q'.eqv_symm
          (Q'.ofNat_add_eqv (sumSq N) ((N + 1) * (N + 1)))

/-- Closed form of the tapered mass head. -/
theorem lowerSixHermiteLinearHeadSum_eqv_closed (k : Nat) :
    lowerSixHermiteLinearHeadSum k ≈
      Q'.ofNat (thetaWindowLeft k) +
        -(((1 : Q') - harmW k * harmW k) *
          Q'.ofNat (sumSq (thetaWindowLeft k))) := by
  let d := thetaWindowLeft k
  let delta := (1 : Q') - harmW k * harmW k
  let Sq := fun j => Q'.ofNat ((j + 1) * (j + 1))
  have hterm : ∀ j, lowerSixHermiteLinearHeadCell k (j + 1) ≈
      (1 : Q') + (-delta) * Sq j := by
    intro j
    unfold lowerSixHermiteLinearHeadCell
    dsimp only [delta, Sq]
    apply Q'.add_eqv_congr_left
    refine Q'.eqv_trans _
      (-(((1 : Q') - harmW k * harmW k) *
        Q'.ofNat ((j + 1) * (j + 1)))) _ ?_ ?_
    · exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv _ _)
    · exact Q'.eqv_symm (Q'.neg_mul_eqv _ _)
  have hpoint := RationalTail.finSum_eqv_congr _ _ hterm d
  have hsplit := RationalTail.finSum_add
    (fun _ => (1 : Q')) (fun j => (-delta) * Sq j) d
  have hscaled := Q'.eqv_symm
    (RationalTail.const_mul_finSum Sq (-delta) d)
  have hsquares : finSum Sq d ≈ Q'.ofNat (sumSq d) := by
    dsimp only [Sq, d]
    exact finSum_shifted_squares_eqv_sumSq _
  unfold lowerSixHermiteLinearHeadSum
  dsimp only [d, delta, Sq] at hpoint hsplit hscaled hsquares ⊢
  refine Q'.eqv_trans _ _ _ hpoint ?_
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.eqv_trans _
      (Q'.ofNat (thetaWindowLeft k) +
        (-((1 : Q') - harmW k * harmW k)) *
          Q'.ofNat (sumSq (thetaWindowLeft k))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (finSum_one_eqv_ofNat _)
      (Q'.eqv_trans _ _ _ hscaled
        (Q'.mul_eqv_congr_left _ _ _ hsquares))
  · exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv _ _)

/-- The full Hermite mass dominates the linearly tapered square-root head. -/
theorem lowerSixHermiteLinearHeadMassFloor_le_mass
    {k : Nat} (hk : 38 ≤ k) :
    lowerSixHermiteLinearHeadMassFloor k ≤ lowerSixHermiteMassSum k := by
  let sigma := harmW k * harmW k
  let W := fun j => lowerSixModeWeight k (j + 1)
  let L := fun j => lowerSixHermiteLinearHeadCell k (j + 1)
  let C := Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  have hsigma0 : (0 : Q') ≤ sigma :=
    Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hsigma1 : sigma ≤ (1 : Q') := square_harmW_le_one k
  have hterm : ∀ j, j < thetaWindowLeft k → L j ≤ W j := by
    intro j _
    have hbern := MovingCutoff.qpow_ge_bernoulli hsigma0 hsigma1
      ((j + 1) * (j + 1))
    dsimp only [L, W, sigma]
    unfold lowerSixHermiteLinearHeadCell lowerSixModeWeight
    exact hbern
  have hprefix : lowerSixHermiteLinearHeadSum k ≤
      finSum W (thetaWindowLeft k) := by
    unfold lowerSixHermiteLinearHeadSum
    exact YMGap.Constructive.finSum_le_lt L W (thetaWindowLeft k) hterm
  have hWnonneg : ∀ j, (0 : Q') ≤ W j := by
    intro j
    dsimp only [W]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hleft : thetaWindowLeft k ≤ growingAnchor k := by
    have hc := thetaWindowCenter_le_harmonicDen hk
    unfold thetaWindowLeft growingAnchor
    have hdiv := Nat.div_le_self (thetaWindowCenter k) 2
    omega
  have hfull : finSum W (thetaWindowLeft k) ≤
      lowerSixHermiteWeightSum k := by
    unfold lowerSixHermiteWeightSum
    exact RationalTail.finSum_monotone_of_nonneg W hWnonneg
      (thetaWindowLeft k) (growingAnchor k) hleft
  have hweight : lowerSixHermiteLinearHeadSum k ≤
      lowerSixHermiteWeightSum k := Q'.le_trans' _ _ _ hprefix hfull
  have hD : (0 : Q') ≤ Q'.ofNat (k + 2) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hC : (0 : Q') ≤ C :=
    Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hD 3)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C hweight hC
  unfold lowerSixHermiteLinearHeadMassFloor
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.eqv_symm
      (lowerSixHermiteMassSum_eqv_scaledWeightSum k)))

theorem lowerSixHermiteMassSum_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixHermiteMassSum k := by
  unfold lowerSixHermiteMassSum
  let f := fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1)
  have hf : ∀ j, (0 : Q') ≤ f j := by
    intro j
    dsimp only [f]
    unfold lowerSixDiscreteHermiteMassNumerator lowerSixModeWeight
    have hD : (0 : Q') ≤ Q'.ofNat (k + 2) :=
      HeatKernelRGStep.zero_le_ofNat _
    have hW : (0 : Q') ≤
        qpow (harmW k * harmW k) ((j + 1) * (j + 1)) :=
      qpow_nonneg _
        (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hD 3)) hW
  have hsum := RationalTail.finSum_monotone_of_nonneg f hf
    0 (growingAnchor k) (Nat.zero_le _)
  exact hsum

private def pQuarterEnvelopeL : PE :=
  .mul (.const 4) (.add (.var 0) (.var 1))

private def pQuarterEnvelopeR : PE :=
  .add (.add (.var 0) (.mul (.const 4) (.var 1)))
    (.mul (.const 3) (.var 0))

private theorem pQuarterEnvelope_normal :
    RingNormaliser.normalize pQuarterEnvelopeL =
      RingNormaliser.normalize pQuarterEnvelopeR := by decide

private theorem quarterEnvelope_algebra (M R : Q') :
    Q'.ofNat 4 * (M + R) ≈
      (M + Q'.ofNat 4 * R) + Q'.ofNat 3 * M := by
  simpa [pQuarterEnvelopeL, pQuarterEnvelopeR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pQuarterEnvelopeL pQuarterEnvelopeR pQuarterEnvelope_normal
      (fun | 0 => M | _ => R))

theorem lowerSixMass_add_remainderSum_nonnegative_of_quarter_envelope
    (k : Nat)
    (hquarter : (0 : Q') ≤
      lowerSixHermiteMassSum k +
        Q'.ofNat 4 * lowerSixHermiteRemainderSum k) :
    (0 : Q') ≤
      lowerSixHermiteMassSum k + lowerSixHermiteRemainderSum k := by
  let M := lowerSixHermiteMassSum k
  let R := lowerSixHermiteRemainderSum k
  have hM : (0 : Q') ≤ M := lowerSixHermiteMassSum_nonnegative k
  have h3M : (0 : Q') ≤ Q'.ofNat 3 * M :=
    Q'.mul_nonneg _ _ (by decide) hM
  have hsum : (0 : Q') ≤ (M + Q'.ofNat 4 * R) + Q'.ofNat 3 * M :=
    Q'.zero_le_add _ _ hquarter h3M
  have hscaled : (0 : Q') ≤ Q'.ofNat 4 * (M + R) :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (quarterEnvelope_algebra M R)))
  have hzero : Q'.ofNat 4 * (0 : Q') ≤ Q'.ofNat 4 * (M + R) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 4))) hscaled
  exact Q'.le_of_mul_le_mul_left hzero (by decide)

/-- Sharp current interface: four copies of the negative summed remainder
must be paid only by the explicit tapered mass head. -/
theorem lowerSixMass_add_remainderSum_nonnegative_of_linearHead_payment
    {k : Nat} (hk : 48 ≤ k)
    (hpayment :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k) :
    (0 : Q') ≤
      lowerSixHermiteMassSum k + lowerSixHermiteRemainderSum k := by
  let H := lowerSixHermiteLinearHeadMassFloor k
  let M := lowerSixHermiteMassSum k
  let R := lowerSixHermiteRemainderSum k
  have hHM : H ≤ M :=
    lowerSixHermiteLinearHeadMassFloor_le_mass (by omega)
  have hsub : (0 : Q') ≤ H + -(-(Q'.ofNat 4 * R)) :=
    Q'.sub_nonneg_of_le hpayment
  have hcancel : H + -(-(Q'.ofNat 4 * R)) ≈
      H + Q'.ofNat 4 * R :=
    Q'.add_eqv_congr_left H _ _ (Q'.neg_neg_eqv _)
  have hHplus : (0 : Q') ≤ H + Q'.ofNat 4 * R :=
    Q'.le_trans' _ _ _ hsub (Q'.le_of_eqv hcancel)
  have hmove := Q'.add_le_add_right H M (Q'.ofNat 4 * R) hHM
  have hquarter : (0 : Q') ≤ M + Q'.ofNat 4 * R :=
    Q'.le_trans' _ _ _ hHplus hmove
  exact lowerSixMass_add_remainderSum_nonnegative_of_quarter_envelope k hquarter

/-! ## Final two-residual split -/

/-- The upper Hermite-flux endpoint grouped with the exact prefix Taylor
correction.  The lower endpoint has already been paid in the imported file. -/
def lowerSixUpperFluxPrefixBlock (k : Nat) : Q' :=
  lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1) +
    lowerSixQuadraticTaylorClearingScale k *
      lowerSixQuadraticTaylorPrefixRemainder k

private def pClearedThreeBlocksL : PE :=
  let E : PE := .var 0
  let U : PE := .var 1
  let L : PE := .var 2
  let M : PE := .var 3
  let R : PE := .var 4
  let P : PE := .var 5
  .add (.add E (.add (.add (.add U (.neg L)) M) R)) P

private def pClearedThreeBlocksR : PE :=
  let E : PE := .var 0
  let U : PE := .var 1
  let L : PE := .var 2
  let M : PE := .var 3
  let R : PE := .var 4
  let P : PE := .var 5
  .add (.add (.add E (.neg L)) (.add U P)) (.add M R)

private theorem pClearedThreeBlocks_normal :
    RingNormaliser.normalize pClearedThreeBlocksL =
      RingNormaliser.normalize pClearedThreeBlocksR := by decide

private theorem clearedThreeBlocks_algebra (E U L M R P : Q') :
    (E + (((U + -L) + M) + R)) + P ≈
      ((E + -L) + (U + P)) + (M + R) := by
  simpa [pClearedThreeBlocksL, pClearedThreeBlocksR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pClearedThreeBlocksL pClearedThreeBlocksR
      pClearedThreeBlocks_normal
      (fun | 0 => E | 1 => U | 2 => L | 3 => M | 4 => R | _ => P))

theorem lowerSixClearedFluxExpression_eqv_three_blocks (k : Nat) :
    lowerSixQuadraticTaylorClearedFluxExpression k ≈
      ((lowerSixQuadraticTaylorClearingScale k *
            lowerSixQuadraticTaylorEndpointAugmentation k +
          -lowerSixDiscreteHermiteFluxNumerator k 1) +
        lowerSixUpperFluxPrefixBlock k) +
      (lowerSixHermiteMassSum k + lowerSixHermiteRemainderSum k) := by
  unfold lowerSixQuadraticTaylorClearedFluxExpression
    lowerSixUpperFluxPrefixBlock lowerSixHermiteMassSum
    lowerSixHermiteRemainderSum
  exact clearedThreeBlocks_algebra _ _ _ _ _ _

/-- The complete cleared expression follows from exactly two remaining
analytic inputs: the upper-flux/prefix block and the explicit tapered-head
payment for the summed remainder. -/
theorem lowerSixClearedFluxExpression_nonnegative_of_two_payments
    {k : Nat} (hk : 247 ≤ k)
    (hupper : (0 : Q') ≤ lowerSixUpperFluxPrefixBlock k)
    (hremainder :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k) :
    (0 : Q') ≤ lowerSixQuadraticTaylorClearedFluxExpression k := by
  have hend := lowerSixEndpoint_add_lowerFlux_nonnegative hk
  have hmass :=
    lowerSixMass_add_remainderSum_nonnegative_of_linearHead_payment
      (show 48 ≤ k by omega) hremainder
  have hsum : (0 : Q') ≤
      ((lowerSixQuadraticTaylorClearingScale k *
            lowerSixQuadraticTaylorEndpointAugmentation k +
          -lowerSixDiscreteHermiteFluxNumerator k 1) +
        lowerSixUpperFluxPrefixBlock k) +
      (lowerSixHermiteMassSum k + lowerSixHermiteRemainderSum k) :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hend hupper) hmass
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixClearedFluxExpression_eqv_three_blocks k)))

theorem lowerSixQuadraticPayment_of_two_summed_payments
    {k : Nat} (hk : 247 ≤ k)
    (hupper : (0 : Q') ≤ lowerSixUpperFluxPrefixBlock k)
    (hremainder :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k) :
    -YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep.lowerSixScaledLinearCrossPaymentResidual k ≤
      YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment.lowerSixScaledQuadraticCrossWindowSuffix k := by
  exact lowerSixQuadraticPayment_of_clearedFluxExpression_nonnegative
    (show 48 ≤ k by omega)
    (lowerSixClearedFluxExpression_nonnegative_of_two_payments
      hk hupper hremainder)

#print axioms lowerSixHermiteMassSum_eqv_scaledWeightSum
#print axioms lowerSixHermiteLinearHeadCell_nonnegative
#print axioms lowerSixHermiteLinearHeadSum_nonnegative
#print axioms lowerSixHermiteLinearHeadSum_eqv_closed
#print axioms lowerSixHermiteLinearHeadMassFloor_le_mass
#print axioms lowerSixHermiteMassSum_nonnegative
#print axioms lowerSixMass_add_remainderSum_nonnegative_of_quarter_envelope
#print axioms lowerSixMass_add_remainderSum_nonnegative_of_linearHead_payment
#print axioms lowerSixClearedFluxExpression_eqv_three_blocks
#print axioms lowerSixClearedFluxExpression_nonnegative_of_two_payments
#print axioms lowerSixQuadraticPayment_of_two_summed_payments

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
