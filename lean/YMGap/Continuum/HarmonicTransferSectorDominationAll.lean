/-
This module discharges the scalar sector residual from
`HarmonicTransferOperatorIdentification` at every harmonic scale.

For the character profile

  c_s = (s+1) * (harmW k)^(s(s+2)),

write `D_N = sum_{s=0}^N c_s^2` and
`A_N = sum_{s=0}^{N-1} c_s c_{s+1}`.  The full half-edge dominance theorem,
specialized to its zeroth prefix, states exactly

  D_N * (2 * w^3) <= (2 * A_N) * 1.

The identities `c_0 = 1` and `c_1 = 2*w^3` identify the two boundary factors.
Cancelling the positive factor two gives `w^3 * D_N <= A_N`.  Division by the
strictly positive `D_N`, followed by the exact fused identity
`lamPW = A_N / D_N`, proves the requested comparison for every `k` without a
finite scale split.
-/

import YMGap.Continuum.HarmonicHalfEdgeDominance
import YMGap.Continuum.HarmonicTransferOperatorIdentification

namespace YMGap.Continuum.HarmonicTransferSectorDominationAll

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicHalfEdgeDominance
open YMGap.Continuum.HarmonicTransferOperatorIdentification
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. Zeroth half-edge specialization -/

/-- The full harmonic half-edge estimate at prefix zero is exactly the
cleared-denominator comparison `w^3 * D_N <= A_N`. -/
theorem heatKernelSep_mul_coordNormSq_le_adjCorr (k : Nat) :
    heatKernelSep (harmW k) * coordNormSq (harmW k) (Ncut k) <=
      adjCorr (harmW k) (Ncut k) := by
  have hN : 1 <= Ncut k := by
    unfold Ncut
    exact Nat.mul_pos (by omega) (by omega)
  have hL : Ncut k - 1 + 1 = Ncut k := Nat.sub_add_cancel hN
  have h := harmonic_halfEdge_full k (p := 0)
    (by omega : 0 <= Ncut k - 1)
  dsimp only at h
  rw [hL] at h
  let w := harmW k
  let D := coordNormSq w (Ncut k)
  let A := adjCorr w (Ncut k)
  have hDfull : profileD (coeffW w) (Ncut k) = D := rfl
  have hAfull : profileA (coeffW w) (Ncut k) = A := rfl
  have hDzero : profileD (coeffW w) 0 ≈ (1 : Q') := by
    unfold profileD
    simp only [fsum_succ, fsum_zero, coeffW_zero, Q'.zero_add']
    exact Q'.one_mul_eqv 1
  have hHzero : halfEdgeNum (coeffW w) 0 ≈
      Q'.ofNat 2 * heatKernelSep w := by
    unfold halfEdgeNum profileA
    simp only [fsum_zero, Q'.zero_add', coeffW_zero]
    change (1 : Q') * coeffW w 1 ≈ Q'.ofNat 2 * heatKernelSep w
    unfold coeffW dimQ c4 heatKernelSep
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.eqv_refl _)
  rw [hDfull, hAfull] at h
  have h2 : Q'.ofNat 2 * (heatKernelSep w * D) <=
      Q'.ofNat 2 * A := by
    have eL : D * halfEdgeNum (coeffW w) 0 ≈
        Q'.ofNat 2 * (heatKernelSep w * D) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left D _ _ hHzero) ?_
      ring_qeqv
    have eR : (A + A) * profileD (coeffW w) 0 ≈
        Q'.ofNat 2 * A := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (A + A) _ _ hDzero) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ?_
      have htwo : Q'.ofNat 2 ≈ (1 : Q') + (1 : Q') := by decide
      refine Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ A htwo) ?_)
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 A) ?_
      exact Q'.add_eqv_congr' (Q'.one_mul_eqv A) (Q'.one_mul_eqv A)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv eR))
  exact Q'.le_of_mul_le_mul_left h2 (by decide)

/-! ## 2. Exact quotient identification -/

/-- Every harmonic heat-kernel fundamental eigenvalue is bounded by the
Peter--Weyl-normalized fused eigenvalue at the quadratic cutoff. -/
theorem heatKernelSep_le_lamPW_all (k : Nat) :
    heatKernelSep (harmW k) <= lamPW (harmW k) (Ncut k) 1 := by
  let D := coordNormSq (harmW k) (Ncut k)
  let A := adjCorr (harmW k) (Ncut k)
  have hD : (0 : Q') < D := coordNormSq_pos (harmW_nonneg k) (Ncut k)
  have hcross : heatKernelSep (harmW k) * D <= A :=
    heatKernelSep_mul_coordNormSq_le_adjCorr k
  have hratio : heatKernelSep (harmW k) <= Q'.divPos A D hD :=
    Q'.le_divPos_of_mul_le A D hD hcross
  have hvac := vacNorm_fundamental_eq_ratio
    (harmW_nonneg k) (harmW_le_one k) (Ncut k)
  have hlam := lamPW_eq_vacNorm_p2
    (harmW_nonneg k) (harmW_le_one k) (Ncut k) 0
  have heq : lamPW (harmW k) (Ncut k) 1 ≈ Q'.divPos A D hD :=
    Q'.eqv_trans _ _ _ hlam hvac
  exact Q'.le_trans' _ _ _ hratio (Q'.ge_of_eqv heq)

/-- Equivalent margin comparison: the fused harmonic gap is no larger than
the fundamental heat-kernel character gap. -/
theorem harmonicMass_le_heatKernelMargin (k : Nat) :
    HarmonicFusedSchurObstruction.harmonicMass k <=
      (1 : Q') - heatKernelSep (harmW k) := by
  unfold HarmonicFusedSchurObstruction.harmonicMass
  have hneg := Q'.neg_le_neg (heatKernelSep_le_lamPW_all k)
  exact Q'.add_le_add_left (1 : Q') _ _ hneg

/-! ## 3. Residual closure and unconditional character-GNS consequences -/

/-- The all-scale scalar sector residual is now inhabited structurally. -/
def harmonicTransferSectorDominationAll : HarmonicTransferSectorDomination :=
  fun k => ⟨heatKernelSep_le_lamPW_all k⟩

/-- Unconditional located character-spectrum gap with fused separator. -/
def harmonicCharLocatedGap_all (k : Nat) :=
  harmonicCharLocatedGap harmonicTransferSectorDominationAll k

/-- Its margin is exactly the actual harmonic mass. -/
theorem harmonicChar_gapMargin_eq_all (k : Nat) :
    (harmonicCharLocatedGap_all k).gapMargin =
      HarmonicFusedSchurObstruction.harmonicMass k := rfl

/-- Unconditional spectral-gap datum on the established character GNS
transfer operator. -/
def harmonicCharSpectralGapData_all
    (k : Nat) (t : Q') (ht : (0 : Q') <= t) :=
  harmonicCharSpectralGapData harmonicTransferSectorDominationAll k t ht

/-- Unconditional operator-form gap on that character GNS transfer operator. -/
def harmonicCharFormGap_all
    (k : Nat) (t : Q') (ht : (0 : Q') <= t) :=
  harmonicCharFormGap harmonicTransferSectorDominationAll k t ht

end YMGap.Continuum.HarmonicTransferSectorDominationAll

#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.heatKernelSep_mul_coordNormSq_le_adjCorr
#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.heatKernelSep_le_lamPW_all
#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.harmonicMass_le_heatKernelMargin
#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.harmonicTransferSectorDominationAll
#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.harmonicCharLocatedGap_all
#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.harmonicChar_gapMargin_eq_all
#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.harmonicCharSpectralGapData_all
#print axioms YMGap.Continuum.HarmonicTransferSectorDominationAll.harmonicCharFormGap_all
