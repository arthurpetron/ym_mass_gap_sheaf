/-
`HarmonicFusedSchurObstruction` moves the coupled Schur construction to the
actual harmonic-weight fused masses

  1 - lamPW (harmW k) (Ncut k) 1.

It proves the exact adjacent-correlation quotient formula, nonnegativity of
every harmonic mass and shell, strict shell positivity at the first harmonic
pair, and a first genuinely off-endpoint operator/spacing step.  It also
translates the harmonic bulk-theta estimate into a same-weight normalizer
stability theorem.

The tempting use of that theorem across consecutive harmonic scales is then
machine-refuted: changing `harmW 1` to `harmW 2` grows the retained normalizer
by more than the complete cutoff-tail allowance `2/(1+2)^2`.  Thus the
remaining all-k cross law needs a weight-drift estimate; the proved cutoff-tail
bound alone cannot supply it.
-/

import YMGap.Continuum.FusedSchurSpacingBridge
import YMGap.Continuum.HarmonicBulkThetaTail
import YMGap.Continuum.EndpointCutoffTwoParameter
import YMGap.Continuum.AllWindowCorrDirichlet
import YMGap.Continuum.CutoffCorrelationMonotone

namespace YMGap.Continuum.HarmonicFusedSchurObstruction

set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.CorrectedCarrierOperatorBridge
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-! ## 1. The actual harmonic fused mass -/

def harmonicMass (k : Nat) : Q' :=
  (1 : Q') - lamPW (harmW k) (Ncut k) 1

theorem harmW_pos (k : Nat) : (0 : Q') < harmW k := by
  have hu : harmU k < (1 : Q') := by
    show (harmU k).num * ((1 : Q').den : Int) <
      (1 : Q').num * ((harmU k).den : Int)
    unfold harmU unit
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    exact_mod_cast (by omega : 1 < k + 2)
  unfold harmW oneSub
  exact ClusteringImpliesGap.sub_pos_of_lt hu

/-- The actual mass is the exact normalized Dirichlet deficit `(D-A)/D`. -/
theorem harmonicMass_eq_ratio (k : Nat) :
    harmonicMass k ≈
      Q'.divPos
        (coordNormSq (harmW k) (Ncut k) - adjCorr (harmW k) (Ncut k))
        (coordNormSq (harmW k) (Ncut k))
        (coordNormSq_pos (harmW_nonneg k) (Ncut k)) := by
  let w := harmW k
  let N := Ncut k
  let A := adjCorr w N
  let D := coordNormSq w N
  have hv := vacNorm_fundamental_eq_ratio (harmW_nonneg k) (harmW_le_one k) N
  have hlam := lamPW_eq_vacNorm_p2 (harmW_nonneg k) (harmW_le_one k) N 0
  have heig : lamPW w N 1 ≈
      Q'.divPos A D (coordNormSq_pos (harmW_nonneg k) N) :=
    Q'.eqv_trans _ _ _ hlam hv
  have hD := coordNormSq_pos (harmW_nonneg k) N
  unfold harmonicMass
  change (1 : Q') - lamPW w N 1 ≈ Q'.divPos (D - A) D hD
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ heig))
    (HeatKernelRGStep.one_sub_divPos_eqv A D hD)

theorem harmonicMass_nonneg (k : Nat) : (0 : Q') <= harmonicMass k := by
  let diff := coordNormSq (harmW k) (Ncut k) - adjCorr (harmW k) (Ncut k)
  let D := coordNormSq (harmW k) (Ncut k)
  have hdiff : (0 : Q') <= diff :=
    Q'.sub_nonneg_of_le (adjCorr_le_coordNormSq (harmW k) (Ncut k))
  have hratio : (0 : Q') <= Q'.divPos diff D
      (coordNormSq_pos (harmW_nonneg k) (Ncut k)) :=
    Q'.mul_nonneg _ _ hdiff (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.le_trans' _ _ _ hratio (Q'.ge_of_eqv (harmonicMass_eq_ratio k))

/-! ## 2. Consecutive rotated harmonic mass blocks -/

def harmonicMassOp (k : Nat) : CompactTransferGNS.FiniteOp :=
  rotatedFusedOp (harmonicMass k) (harmonicMass (k + 1))

def harmonicHead (k : Nat) : Q' :=
  rot00 (harmonicMass k) (harmonicMass (k + 1))

def harmonicShell (k : Nat) : Q' :=
  rot11 (harmonicMass k) (harmonicMass (k + 1))

def harmonicCoupling (k : Nat) : Q' :=
  rot01 (harmonicMass k) (harmonicMass (k + 1))

theorem harmonicShell_nonneg (k : Nat) : (0 : Q') <= harmonicShell k := by
  unfold harmonicShell rot11
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (by decide)) (harmonicMass_nonneg k))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (by decide)) (harmonicMass_nonneg (k + 1)))

theorem harmonicShell_zero_pos : (0 : Q') < harmonicShell 0 := by decide

def harmonicErosionZero : Q' :=
  shellLoss (harmonicCoupling 0) (harmonicShell 0) harmonicShell_zero_pos

def harmonicSchurZero : Q' :=
  schurMass (harmonicHead 0) (harmonicShell 0) (harmonicCoupling 0)
    harmonicShell_zero_pos

def harmonicSpacing (k : Nat) : Q' := unit (Ncut k) (Ncut_pos k)

theorem harmonicSpacing_pos (k : Nat) : (0 : Q') < harmonicSpacing k :=
  unit_pos (Ncut k) (Ncut_pos k)

theorem harmonicSpacing_contracts (k : Nat) :
    harmonicSpacing (k + 1) <= harmonicSpacing k := by
  exact unit_antitone (Ncut_pos k) (Ncut_pos (k + 1)) (by
    unfold Ncut
    exact Nat.mul_le_mul (by omega) (by omega))

theorem harmonicErosionZero_nonneg : (0 : Q') <= harmonicErosionZero := by
  unfold harmonicErosionZero shellLoss Q'.divPos
  exact Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (harmonicCoupling 0))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem harmonicCoupling_size_zero :
    harmonicCoupling 0 * harmonicCoupling 0 <=
      harmonicErosionZero * harmonicShell 0 := by
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.divPos_mul_eqv
        (harmonicCoupling 0 * harmonicCoupling 0)
        (harmonicShell 0) harmonicShell_zero_pos))

/-- A closed-rational, genuinely off-endpoint Schur/spacing step. -/
theorem harmonicSchur_spacing_cross_zero :
    harmonicSchurZero * harmonicSpacing 1 <=
      harmonicMass 1 * harmonicSpacing 0 := by
  decide

/-- The corresponding first actual harmonic-weight operator cross law. -/
theorem harmonic_operator_spacing_cross_zero :
    harmonicHead 0 * harmonicSpacing 1 <=
      (harmonicErosionZero + harmonicMass 1) * harmonicSpacing 0 := by
  exact spacing_cross_of_schur harmonicShell_zero_pos
    harmonicErosionZero_nonneg
    (Q'.le_of_lt (harmonicSpacing_pos 1))
    (harmonicSpacing_contracts 0)
    harmonicCoupling_size_zero
    harmonicSchur_spacing_cross_zero

/-! ## 3. What the harmonic bulk-theta normalizer estimate really proves -/

/-- The coordinate norm is exactly the finite squared-theta normalizer. -/
theorem coordNormSq_eq_Zsum_sq (w : Q') (N : Nat) :
    coordNormSq w N ≈ Zsum (w * w) (N + 1) := by
  unfold coordNormSq Zsum
  exact fsum_eqv_congr _ _
    (fun s => coeffW_sq_eqv w s)
    (N + 1)

private theorem Zsum_le_succ {w : Q'} (hw : (0 : Q') <= w) (N : Nat) :
    Zsum w N <= Zsum w (N + 1) := by
  show Zsum w N <= Zsum w N +
    dimQ N * (dimQ N * qpow w (c4 N))
  exact Q'.add_le_self_of_nonneg _ _ (Zsum_summand_nonneg hw N)

/-- The bulk-theta theorem controls every further cutoff at the *same* harmonic
weight by `2/(k+2)^2`, now stated directly for the physical normalizer `D`. -/
theorem harmonic_same_weight_normalizer_extension_le (k M : Nat) :
    coordNormSq (harmW k) (Ncut k + M) <=
      coordNormSq (harmW k) (Ncut k) +
        Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
  have htail := Zsum_sq_cutoff_extension_le k (M + 1)
  have hidx : Ncut k + M + 1 = Ncut k + (M + 1) := by omega
  have hbase : Zsum (harmW k * harmW k) (Ncut k) <=
      coordNormSq (harmW k) (Ncut k) := by
    have hs := Zsum_le_succ
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) (Ncut k)
    exact Q'.le_trans' _ _ _ hs
      (Q'.ge_of_eqv (coordNormSq_eq_Zsum_sq (harmW k) (Ncut k)))
  have hadd := Q'.add_le_add_right
    (Zsum (harmW k * harmW k) (Ncut k))
    (coordNormSq (harmW k) (Ncut k))
    (Q'.ofNat 2 * invSqTerm 2 (by decide) k) hbase
  have hcoord := coordNormSq_eq_Zsum_sq (harmW k) (Ncut k + M)
  rw [hidx] at hcoord
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hcoord)
    (Q'.le_trans' _ _ _ htail hadd)

/-- **Exact obstruction.**  Replacing "same harmonic weight" by the next
harmonic weight is false: already `k=1`, the retained normalizer growth exceeds
the complete `2/(k+2)^2` cutoff-tail allowance. -/
theorem no_inter_scale_normalizer_extension_at_one :
    not (coordNormSq (harmW 2) (Ncut 2) <=
      coordNormSq (harmW 1) (Ncut 1) +
        Q'.ofNat 2 * invSqTerm 2 (by decide) 1) := by
  decide

end YMGap.Continuum.HarmonicFusedSchurObstruction

#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmW_pos
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonicMass_eq_ratio
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonicMass_nonneg
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonicShell_nonneg
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonicShell_zero_pos
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonicCoupling_size_zero
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonicSchur_spacing_cross_zero
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonic_operator_spacing_cross_zero
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.coordNormSq_eq_Zsum_sq
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.harmonic_same_weight_normalizer_extension_le
#print axioms YMGap.Continuum.HarmonicFusedSchurObstruction.no_inter_scale_normalizer_extension_at_one
