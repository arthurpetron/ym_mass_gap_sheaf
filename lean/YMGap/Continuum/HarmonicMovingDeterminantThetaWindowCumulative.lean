/-
Cumulative Abel certificate for the square-root theta proof window.

The pointwise route is machine-refuted in the frozen predecessor.  This file
keeps the exact cancellations by separating every central cell into an
unweighted signed slope carrier and a nonnegative decreasing Gaussian weight,
then applies finite Abel summation to prefix sums of the carrier.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowSign

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCumulative

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowSign
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- Signed carrier after removing the decreasing Gaussian square weight. -/
def thetaCentralCarrier (k j : Nat) : Q' :=
  let n := thetaWindowLeft k + j
  sevenDirichletProfile k * Q'.ofNat (n * n) +
    -(Q'.ofNat 4 * (thetaRootSlope k n * thetaRootSlope k n))

/-- Complementary Gaussian weight in the exact central factorization. -/
def thetaCentralWeight (k j : Nat) : Q' :=
  let n := thetaWindowLeft k + j
  qpow (harmW k * harmW k) (n * n)

def thetaCentralAbelPrefix (k p : Nat) : Q' :=
  abelPrefix (thetaCentralCarrier k) p

theorem thetaCentralCarrier_mul_weight (k j : Nat) :
    thetaCentralCarrier k j * thetaCentralWeight k j ≈
      thetaCoreIncrement k (thetaWindowLeft k + j) := by
  dsimp only [thetaCentralCarrier, thetaCentralWeight]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ _) ?_
  exact Q'.eqv_symm
    (thetaCoreIncrement_slope_factor k (thetaWindowLeft k + j))

theorem thetaCentralWeight_nonnegative (k j : Nat) :
    (0 : Q') ≤ thetaCentralWeight k j := by
  unfold thetaCentralWeight
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _

private theorem harmW_sq_le_one (k : Nat) :
    harmW k * harmW k ≤ (1 : Q') := by
  have hmul := Q'.mul_le_mul_of_nonneg
    (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.one_mul_eqv 1))

theorem thetaCentralWeight_antitone (k j : Nat) :
    thetaCentralWeight k (j + 1) ≤ thetaCentralWeight k j := by
  unfold thetaCentralWeight
  have hexp :
      (thetaWindowLeft k + j) * (thetaWindowLeft k + j) ≤
        (thetaWindowLeft k + (j + 1)) *
          (thetaWindowLeft k + (j + 1)) := by
    exact Nat.mul_le_mul (by omega) (by omega)
  exact HeatKernelRGStep.qpow_antitone
    (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k))
    (harmW_sq_le_one k)
    _ _ hexp

theorem thetaProofCentralReserve_eqv_weighted_carrier (k : Nat) :
    thetaProofCentralReserve k ≈
      finSum (fun j => thetaCentralCarrier k j * thetaCentralWeight k j)
        (thetaWindowCenter k - thetaWindowLeft k + 1) := by
  unfold thetaProofCentralReserve
  exact RationalTail.finSum_eqv_congr _ _
    (fun j => Q'.eqv_symm (thetaCentralCarrier_mul_weight k j)) _

/-- Genuine cumulative closure: nonnegative carrier prefixes, rather than
pointwise carriers, imply nonnegativity of the full central reserve. -/
theorem thetaProofCentralReserve_nonnegative_of_prefix {k : Nat}
    (hprefix : ∀ p,
      p ≤ thetaWindowCenter k - thetaWindowLeft k →
      (0 : Q') ≤ thetaCentralAbelPrefix k p) :
    (0 : Q') ≤ thetaProofCentralReserve k := by
  let n := thetaWindowCenter k - thetaWindowLeft k
  have hweighted : (0 : Q') ≤
      finSum (fun j => thetaCentralCarrier k j * thetaCentralWeight k j)
        (n + 1) := by
    apply finite_abel_nonnegative_of_prefix
    · intro p hp
      dsimp only [thetaCentralAbelPrefix]
      exact hprefix p hp
    · intro p _
      exact thetaCentralWeight_nonnegative k p
    · intro p _
      exact thetaCentralWeight_antitone k p
  dsimp only [n] at hweighted
  exact Q'.le_trans' _ _ _ hweighted
    (Q'.ge_of_eqv (thetaProofCentralReserve_eqv_weighted_carrier k))

/-- All unweighted cumulative carrier prefixes are positive at the threshold
scale, including prefixes ending after the individual cells turn negative. -/
theorem thetaCentralAbelPrefix_k38_nonnegative (p : Nat) (hp : p ≤ 5) :
    (0 : Q') ≤ thetaCentralAbelPrefix 38 p := by
  have hp' : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by
    omega
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold thetaCentralAbelPrefix abelPrefix thetaCentralCarrier thetaRootSlope
      thetaWindowLeft thetaWindowCenter thetaWindowLength sevenDirichletProfile
      harmW harmU ReciprocalBernoulliUpper.oneSub unit fsum qpow <;>
    decide

theorem thetaProofCentralReserve_k38_nonnegative :
    (0 : Q') ≤ thetaProofCentralReserve 38 := by
  apply thetaProofCentralReserve_nonnegative_of_prefix
  intro p hp
  have hlen : thetaWindowCenter 38 - thetaWindowLeft 38 = 5 := by
    rw [thetaWindowCenter_k38, thetaWindowLeft_k38]
  rw [hlen] at hp
  exact thetaCentralAbelPrefix_k38_nonnegative p hp

/-- Exact cumulative reserve payment for the narrower two-tail partition at
the threshold scale. -/
theorem thetaProof_window_payment_k38 :
    thetaLeftLoss 38 + thetaProofRightLoss 38 ≤
      thetaProofCentralReserve 38 := by
  unfold thetaLeftLoss thetaProofRightLoss thetaLeftTailSum
    thetaProofRightTailSum thetaProofCentralReserve thetaCoreIncrement
    thetaWindowLeft thetaWindowCenter thetaWindowLength sevenDirichletProfile
    thetaDirichletCell thetaRootTerm integerThetaTerm harmW harmU
    ReciprocalBernoulliUpper.oneSub unit
    ChebOrthoMidpointEst.isqrt ChebOrthoMidpointEst.isqrtAux finSum qpow
  decide

#print axioms thetaCentralCarrier
#print axioms thetaCentralWeight
#print axioms thetaCentralAbelPrefix
#print axioms thetaCentralCarrier_mul_weight
#print axioms thetaCentralWeight_nonnegative
#print axioms thetaCentralWeight_antitone
#print axioms thetaProofCentralReserve_eqv_weighted_carrier
#print axioms thetaProofCentralReserve_nonnegative_of_prefix
#print axioms thetaCentralAbelPrefix_k38_nonnegative
#print axioms thetaProofCentralReserve_k38_nonnegative
#print axioms thetaProof_window_payment_k38

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCumulative
