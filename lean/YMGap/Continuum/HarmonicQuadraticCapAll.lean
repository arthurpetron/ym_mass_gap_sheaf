/-
# Uniform quadratic carrier: two-seed reduction and normalized barriers

The positive-tail identity shows that the all-crossing quadratic cap does not
require separate control of every possible crossing.  A nonnegative terminal
gap at node one makes every later carrier a suffix of the node-one carrier.
Consequently the uniform problem reduces exactly to the two seeds `s = 0,1`.

The second part records the scale-normalized carrier and the rational barrier

    6 + 3/(2 (k+2)).

This is strictly below the existing `864/125` normalized moment budget for
every `k >= 5`.  The definitions are cleared-denominator friendly so that the
remaining all-scale induction can retain the cancellations between successive
harmonic weights.
-/

import YMGap.Continuum.HarmonicSchurRotationAll
import YMGap.Continuum.HarmonicSignedChordQuadraticCap

namespace YMGap.Continuum.HarmonicQuadraticCapAll

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicSchurRotationAll
open YMGap.Continuum.HarmonicSignedChordQuadraticCap
open YMGap.Continuum.HarmonicSignedChordQuantitative
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem ofNat_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Q'.ofNat_succ_pos m

private theorem cutoffScale_mul_invSq_eqv_one (k : Nat) :
    Q'.ofNat ((k + 2) * (k + 2)) * invSqTerm 2 (by decide) k ≈
      (1 : Q') := by
  unfold invSqTerm unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

/-- The terminal-corrected quadratic carrier at the physical cutoff. -/
def quadraticNodeTotal (k s : Nat) : Q' :=
  signedChordQuadraticNodeMoment k s (Ncut k - 1 - s) +
    (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k)

/-- The natural `D_k^2` denominator of the quadratic carrier. -/
def quadraticNodeNormDen (k : Nat) : Q' :=
  harmonicD k * harmonicD k

theorem quadraticNodeNormDen_pos (k : Nat) :
    (0 : Q') < quadraticNodeNormDen k := by
  unfold quadraticNodeNormDen
  exact Q'.mul_pos (harmonicD_pos k) (harmonicD_pos k)

/-- Dimensionless quadratic carrier
`(k+2)^2 * total / D_k^2`. -/
def normalizedQuadraticNodeTotal (k s : Nat) : Q' :=
  Q'.divPos
    (Q'.ofNat ((k + 2) * (k + 2)) * quadraticNodeTotal k s)
    (quadraticNodeNormDen k) (quadraticNodeNormDen_pos k)

/-- Candidate induction barrier for the dimensionless carrier. -/
def quadraticNodeBarrier (k : Nat) : Q' :=
  Q'.ofNat 6 + Q'.mkPos 3 2 (by decide) * harmU k

/-- The normalized constant already present in `signedChordMomentCap`. -/
def quadraticNodeCapConstant : Q' := Q'.mkPos 864 125 (by decide)

/-- The candidate barrier has uniform room inside the signed-chord budget.
At the endpoint `k=5` this is the exact comparison
`87/14 < 864/125`; later scales only decrease the unit fraction. -/
theorem quadraticNodeBarrier_le_capConstant {k : Nat} (hk : 5 ≤ k) :
    quadraticNodeBarrier k ≤ quadraticNodeCapConstant := by
  have hu : harmU k ≤ Q'.mkPos 1 7 (by decide) := by
    unfold harmU
    simpa [unit] using
      (unit_antitone (a := 7) (b := k + 2)
        (by decide) (by omega) (by omega))
  have hscaled :
      Q'.mkPos 3 2 (by decide) * harmU k ≤
        Q'.mkPos 3 2 (by decide) * Q'.mkPos 1 7 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hu (by decide)
  have hadd := Q'.add_le_add_left (Q'.ofNat 6) _ _ hscaled
  exact Q'.le_trans' _ _ _ hadd (by decide)

/-- Cleared form of the normalized barrier, suitable for an all-scale
integer/rational induction without quotient monotonicity bookkeeping. -/
def QuadraticNodeBarrierCertificate (k s : Nat) : Prop :=
  Q'.ofNat ((k + 2) * (k + 2)) * quadraticNodeTotal k s ≤
    quadraticNodeBarrier k * quadraticNodeNormDen k

/-- Exact normalization of the pre-existing signed-chord cap. -/
theorem cutoffScale_mul_signedChordMomentCap_eqv (k : Nat) :
    Q'.ofNat ((k + 2) * (k + 2)) * signedChordMomentCap k ≈
      quadraticNodeCapConstant * quadraticNodeNormDen k := by
  let M := Q'.ofNat ((k + 2) * (k + 2))
  let p := Q'.mkPos 24 25 (by decide)
  let c := Q'.mkPos 18 5 (by decide)
  let u := invSqTerm 2 (by decide) k
  let X := harmonicD k * harmonicD k
  have hscale : M * u ≈ (1 : Q') := by
    dsimp only [M, u]
    exact cutoffScale_mul_invSq_eqv_one k
  have hcoef : p * c + p * c ≈ quadraticNodeCapConstant := by
    dsimp only [p, c, quadraticNodeCapConstant]
    decide
  have hshape :
      M * ((p * (c * (u * X))) + (p * (c * (u * X)))) ≈
        (p * c + p * c) * ((M * u) * X) := by
    ring_qeqv
  have hcoefSub :
      (p * c + p * c) * ((M * u) * X) ≈
        quadraticNodeCapConstant * ((M * u) * X) :=
    Q'.mul_eqv_congr_right _ _ _ hcoef
  have hscaleX : (M * u) * X ≈ (1 : Q') * X :=
    Q'.mul_eqv_congr_right _ _ _ hscale
  have hscaleSub :
      quadraticNodeCapConstant * ((M * u) * X) ≈
        quadraticNodeCapConstant * ((1 : Q') * X) :=
    Q'.mul_eqv_congr_left _ _ _ hscaleX
  have hone : quadraticNodeCapConstant * ((1 : Q') * X) ≈
      quadraticNodeCapConstant * X :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv X)
  unfold signedChordMomentCap signedChordMomentCore quadraticNodeNormDen
  change M * ((p * (c * (u * X))) + (p * (c * (u * X)))) ≈
    quadraticNodeCapConstant * X
  exact Q'.eqv_trans _ _ _ hshape
    (Q'.eqv_trans _ _ _ hcoefSub (Q'.eqv_trans _ _ _ hscaleSub hone))

/-- A cleared normalized barrier certificate implies the original raw cap.
This is the algebraic bridge needed by both seed lanes. -/
theorem quadraticNodeTotal_le_cap_of_barrierCertificate
    {k s : Nat} (hk : 5 ≤ k) (h : QuadraticNodeBarrierCertificate k s) :
    quadraticNodeTotal k s ≤ signedChordMomentCap k := by
  have hD0 : (0 : Q') ≤ quadraticNodeNormDen k :=
    Q'.le_of_lt (quadraticNodeNormDen_pos k)
  have hbar := Q'.mul_le_mul_of_nonneg_right _ _ (quadraticNodeNormDen k)
    (quadraticNodeBarrier_le_capConstant hk) hD0
  have hscaled :
      Q'.ofNat ((k + 2) * (k + 2)) * quadraticNodeTotal k s ≤
        quadraticNodeCapConstant * quadraticNodeNormDen k :=
    Q'.le_trans' _ _ _ h hbar
  have hcap := cutoffScale_mul_signedChordMomentCap_eqv k
  have hscaledCap :
      Q'.ofNat ((k + 2) * (k + 2)) * quadraticNodeTotal k s ≤
        Q'.ofNat ((k + 2) * (k + 2)) * signedChordMomentCap k :=
    Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hcap)
  exact le_of_mul_le_mul_left_pos
    (ofNat_pos_local (Nat.mul_pos (by omega) (by omega))) hscaledCap

/-- If node one is already on the nonnegative side and the two seed carriers
fit the budget at every scale, then every admissible first crossing fits the
budget.  For `s>0`, suffix monotonicity compares the carrier directly with the
`s=1` seed; the first-crossing sign hypotheses need no further relaxation. -/
theorem uniformQuadraticNodeCap_of_zero_one
    (hboundaryOne : ∀ k : Nat, 5 ≤ k →
      (0 : Q') ≤ trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k 1))
    (hzero : ∀ k : Nat, 5 ≤ k → quadraticNodeTotal k 0 ≤ signedChordMomentCap k)
    (hone : ∀ k : Nat, 5 ≤ k → quadraticNodeTotal k 1 ≤ signedChordMomentCap k) :
    UniformQuadraticNodeCap := by
  intro k s hk hsL _hfirst _hboundary
  by_cases hs0 : s = 0
  · subst s
    simpa [quadraticNodeTotal] using hzero k hk
  · have h1s : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
    have h1L : 1 ≤ Ncut k - 1 := Nat.le_trans h1s hsL
    have hsuffix := signedChordQuadraticNodeMoment_suffix_le_of_boundary
      k (Ncut k - 1) 1 s h1L h1s hsL (hboundaryOne k hk)
    have hadd := Q'.add_le_add_right _ _
      (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) hsuffix
    exact Q'.le_trans' _ _ _ hadd (by
      simpa [quadraticNodeTotal] using hone k hk)

/-! ## Exact base-scale audits for the normalized induction

These are derived character sums, not numerical estimates.  They certify the
strictly stronger normalized barrier at the first two all-scale indices. -/

theorem quadraticNodeBarrierCertificate_k5_s0 :
    QuadraticNodeBarrierCertificate 5 0 := by
  unfold QuadraticNodeBarrierCertificate quadraticNodeTotal quadraticNodeBarrier
    quadraticNodeNormDen signedChordQuadraticNodeMoment
    harmonicChordQuadraticCumulative harmonicChordQuadraticWeight
    harmonicChordQuadraticFactor harmonicEndpointQuadraticCorrection intervalSum
    trapezoidTerminalCorrection trapezoidNodeCoeff harmonicD harmonicA twoInvSq
    oldAdj oldDiag coordNormSq adjCorr driftSqFactor driftRatio driftDen harmW harmU
    oneSub unit invSqTerm coeffW dimQ c4 Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem quadraticNodeBarrierCertificate_k6_s0 :
    QuadraticNodeBarrierCertificate 6 0 := by
  unfold QuadraticNodeBarrierCertificate quadraticNodeTotal quadraticNodeBarrier
    quadraticNodeNormDen signedChordQuadraticNodeMoment
    harmonicChordQuadraticCumulative harmonicChordQuadraticWeight
    harmonicChordQuadraticFactor harmonicEndpointQuadraticCorrection intervalSum
    trapezoidTerminalCorrection trapezoidNodeCoeff harmonicD harmonicA twoInvSq
    oldAdj oldDiag coordNormSq adjCorr driftSqFactor driftRatio driftDen harmW harmU
    oneSub unit invSqTerm coeffW dimQ c4 Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem quadraticNodeBarrierCertificate_k5_s1 :
    QuadraticNodeBarrierCertificate 5 1 := by
  unfold QuadraticNodeBarrierCertificate quadraticNodeTotal quadraticNodeBarrier
    quadraticNodeNormDen signedChordQuadraticNodeMoment
    harmonicChordQuadraticCumulative harmonicChordQuadraticWeight
    harmonicChordQuadraticFactor harmonicEndpointQuadraticCorrection intervalSum
    trapezoidTerminalCorrection trapezoidNodeCoeff harmonicD harmonicA twoInvSq
    oldAdj oldDiag coordNormSq adjCorr driftSqFactor driftRatio driftDen harmW harmU
    oneSub unit invSqTerm coeffW dimQ c4 Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem quadraticNodeBarrierCertificate_k6_s1 :
    QuadraticNodeBarrierCertificate 6 1 := by
  unfold QuadraticNodeBarrierCertificate quadraticNodeTotal quadraticNodeBarrier
    quadraticNodeNormDen signedChordQuadraticNodeMoment
    harmonicChordQuadraticCumulative harmonicChordQuadraticWeight
    harmonicChordQuadraticFactor harmonicEndpointQuadraticCorrection intervalSum
    trapezoidTerminalCorrection trapezoidNodeCoeff harmonicD harmonicA twoInvSq
    oldAdj oldDiag coordNormSq adjCorr driftSqFactor driftRatio driftDen harmW harmU
    oneSub unit invSqTerm coeffW dimQ c4 Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

/-- Exact fence around a false all-scale strategy: even after the natural
`(k+2)^2/D_k^2` normalization, the node-one carrier is not decreasing from
`k=5` to `k=6`.  A valid induction must track barrier slack (or an equivalent
cross-scale cancellation), rather than assert monotonicity of the carrier. -/
theorem normalizedQuadraticNodeTotal_s1_not_antitone_k5_k6 :
    ¬ (normalizedQuadraticNodeTotal 6 1 ≤
      normalizedQuadraticNodeTotal 5 1) := by
  unfold normalizedQuadraticNodeTotal quadraticNodeTotal quadraticNodeNormDen
    signedChordQuadraticNodeMoment harmonicChordQuadraticCumulative
    harmonicChordQuadraticWeight harmonicChordQuadraticFactor
    harmonicEndpointQuadraticCorrection intervalSum trapezoidTerminalCorrection
    trapezoidNodeCoeff harmonicD harmonicA twoInvSq oldAdj oldDiag coordNormSq
    adjCorr driftSqFactor driftRatio driftDen harmW harmU oneSub unit invSqTerm
    coeffW dimQ c4 Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

#print axioms quadraticNodeNormDen_pos
#print axioms quadraticNodeBarrier_le_capConstant
#print axioms cutoffScale_mul_signedChordMomentCap_eqv
#print axioms quadraticNodeTotal_le_cap_of_barrierCertificate
#print axioms uniformQuadraticNodeCap_of_zero_one
#print axioms quadraticNodeBarrierCertificate_k5_s0
#print axioms quadraticNodeBarrierCertificate_k6_s0
#print axioms quadraticNodeBarrierCertificate_k5_s1
#print axioms quadraticNodeBarrierCertificate_k6_s1
#print axioms normalizedQuadraticNodeTotal_s1_not_antitone_k5_k6

end YMGap.Continuum.HarmonicQuadraticCapAll
