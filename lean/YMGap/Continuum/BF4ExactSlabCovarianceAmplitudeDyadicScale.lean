/-
# Dyadic support growth of the guarded covariance amplitude

The guarded one-face covariance response carries one explicit enumeration
factor `2^(M+1) * 625^(M+1)`, where `M` is the connected observable-carrier
support size.  This module factors that term out of the complete covariance
amplitude, keeps the remaining rational coefficient support-free, and combines
it with the quartic four-dimensional shell count under one dyadic exponent
linear in `M`.
-/

import YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse
import YMGap.Continuum.Z4LinfGeometricSum

namespace YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabSummedCouplingDefects
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DyadicGeometricCutoff
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay (blockLength)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4LinfGeometricSum

local infix:50 " ≈ " => Q'.eqv

/-- Exact support-dependent enumeration count in every singleton insertion
amplitude attached to `P`. -/
def supportEnumerationCount {left : List Z4Link}
    (P : ProbeCarrier left) : Nat :=
  2 ^ (P.animal.support.length + 1) *
    625 ^ (P.animal.support.length + 1)

/-- The singleton insertion amplitude after removing its support-enumeration
count. -/
def insertionAmplitudeBase {left : List Z4Link}
    (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c b : Q') : Q' :=
  ((c*b+c*b)*probePrefactor w hd (left.length+4)) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd))
      (HKPos.one_sub_pos hs)

private theorem mul_swap_right (a b c : Q') :
    (a*b)*c ≈ (a*c)*b := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- Exact factorization of the singleton insertion amplitude into a
support-free rational base and the natural enumeration count. -/
theorem amplitude_factor {left : List Z4Link}
    (P : ProbeCarrier left) (w : Q')
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c b : Q') :
    amplitude P w hd hs c b ≈
      insertionAmplitudeBase (left := left) w hd hs c b *
        Q'.ofNat (supportEnumerationCount P) := by
  unfold amplitude insertionAmplitudeBase supportEnumerationCount
  exact mul_swap_right _ _ _

/-- Complete covariance amplitude after removing the common support count. -/
def covarianceAmplitudeBase {left : List Z4Link}
    (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c : Q') : Q' :=
  insertionAmplitudeBase (left := left) w hd hs (c*c) (prefixCap w) *
      inverseFaceFloor w hd +
    (c*(insertionAmplitudeBase (left := left) w hd hs c (prefixCap w) *
        inverseFaceFloor w hd) +
      c*(insertionAmplitudeBase (left := left) w hd hs c (prefixCap w) *
        inverseFaceFloor w hd))

/-- The complete guarded covariance amplitude has exactly one copy of the
support enumeration count. -/
theorem covarianceAmplitude_factor {left : List Z4Link}
    (P : ProbeCarrier left) (w : Q')
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c : Q') :
    covarianceAmplitude hd hs P c ≈
      covarianceAmplitudeBase (left := left) w hd hs c *
        Q'.ofNat (supportEnumerationCount P) := by
  let S := Q'.ofNat (supportEnumerationCount P)
  let squareBase := insertionAmplitudeBase (left := left) w hd hs (c*c) (prefixCap w)
  let singleBase := insertionAmplitudeBase (left := left) w hd hs c (prefixCap w)
  let floor := inverseFaceFloor w hd
  have hsquare := amplitude_factor P w hd hs (c*c) (prefixCap w)
  have hsingle := amplitude_factor P w hd hs c (prefixCap w)
  have hreplace :
      covarianceAmplitude hd hs P c ≈
        (squareBase*S)*floor +
          (c*((singleBase*S)*floor) + c*((singleBase*S)*floor)) := by
    unfold covarianceAmplitude
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ floor hsquare)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left c _ _
          (Q'.mul_eqv_congr_right _ _ floor hsingle))
        (Q'.mul_eqv_congr_left c _ _
          (Q'.mul_eqv_congr_right _ _ floor hsingle)))
  have hsquareMove : (squareBase*S)*floor ≈ (squareBase*floor)*S :=
    mul_swap_right squareBase S floor
  have hsingleMove : c*((singleBase*S)*floor) ≈
      (c*(singleBase*floor))*S := by
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  have hterms :
      (squareBase*S)*floor +
          (c*((singleBase*S)*floor) + c*((singleBase*S)*floor)) ≈
        (squareBase*floor)*S +
          ((c*(singleBase*floor))*S + (c*(singleBase*floor))*S) :=
    Q'.add_eqv_congr' hsquareMove
      (Q'.add_eqv_congr' hsingleMove hsingleMove)
  have hinner :
      (c*(singleBase*floor))*S + (c*(singleBase*floor))*S ≈
        (c*(singleBase*floor) + c*(singleBase*floor))*S :=
    Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
  have houter :
      (squareBase*floor)*S +
          (c*(singleBase*floor) + c*(singleBase*floor))*S ≈
        ((squareBase*floor) +
          (c*(singleBase*floor) + c*(singleBase*floor)))*S :=
    Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
  exact Q'.eqv_trans _ _ _ hreplace
    (Q'.eqv_trans _ _ _ hterms
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hinner)
        (by
          simpa only [covarianceAmplitudeBase, S, squareBase, singleBase,
            floor] using houter)))

/-- The singleton insertion base is nonnegative whenever both observable caps
are nonnegative. -/
theorem insertionAmplitudeBase_nonnegative {left : List Z4Link}
    {w c b : Q'} (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (hc : (0 : Q') ≤ c) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ insertionAmplitudeBase (left := left) w hd hs c b := by
  unfold insertionAmplitudeBase
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ hc hb)
        (Q'.mul_nonneg _ _ hc hb))
      (probePrefactor_nonnegative w hd _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- The support-free covariance amplitude base is nonnegative. -/
theorem covarianceAmplitudeBase_nonnegative {left : List Z4Link}
    {w c : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (hc : (0 : Q') ≤ c) :
    (0 : Q') ≤ covarianceAmplitudeBase (left := left) w hd hs c := by
  unfold covarianceAmplitudeBase
  have hinverse : (0 : Q') ≤ inverseFaceFloor w hd :=
    Q'.le_of_lt (inverseFaceFloor_pos w hd)
  have hprefix : (0 : Q') ≤ prefixCap w := prefixCap_nonnegative hw0
  have hsquare : (0 : Q') ≤ c * c := Q'.mul_nonneg _ _ hc hc
  have hlarge := Q'.mul_nonneg _ _
    (insertionAmplitudeBase_nonnegative (left := left)
      hd hs hsquare hprefix) hinverse
  have hsmall := Q'.mul_nonneg _ _
    (insertionAmplitudeBase_nonnegative (left := left)
      hd hs hc hprefix) hinverse
  exact Q'.zero_le_add _ _ hlarge
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ hc hsmall)
      (Q'.mul_nonneg _ _ hc hsmall))

/-- Support-free coefficient after including the four-dimensional shell
geometric-series inverse. -/
def covarianceShellBase {left : List Z4Link}
    (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c shellRate : Q') (hshell : shellRate < (1 : Q')) : Q' :=
  covarianceAmplitudeBase (left := left) w hd hs c *
    Q'.recipPos (1 + -shellRate) (HKPos.one_sub_pos hshell)

/-- The support-free shell coefficient is nonnegative. -/
theorem covarianceShellBase_nonnegative {left : List Z4Link}
    {w c shellRate : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (hc : (0 : Q') ≤ c) (hshell : shellRate < (1 : Q')) :
    (0 : Q') ≤ covarianceShellBase (left := left) w hd hs c shellRate hshell := by
  unfold covarianceShellBase
  exact Q'.mul_nonneg _ _
    (covarianceAmplitudeBase_nonnegative hw0 hd hs hc)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- Exact factorization of the coefficient used by `dyadicBlockCutoff`: all
carrier and shell-count growth is one natural factor. -/
theorem covarianceShellCoefficient_factor {left : List Z4Link}
    (P : ProbeCarrier left) (w : Q')
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c shellRate : Q') (hshell : shellRate < (1 : Q'))
    (shellCount : Nat) :
    ((covarianceAmplitude hd hs P c * Q'.ofNat shellCount) *
        Q'.recipPos (1 + -shellRate) (HKPos.one_sub_pos hshell)) ≈
      covarianceShellBase (left := left) w hd hs c shellRate hshell *
        Q'.ofNat (supportEnumerationCount P * shellCount) := by
  have hamplitude := covarianceAmplitude_factor P w hd hs c
  have hreplace :
      ((covarianceAmplitude hd hs P c * Q'.ofNat shellCount) *
          Q'.recipPos (1 + -shellRate) (HKPos.one_sub_pos hshell)) ≈
        (((covarianceAmplitudeBase (left := left) w hd hs c *
            Q'.ofNat (supportEnumerationCount P)) *
            Q'.ofNat shellCount) *
          Q'.recipPos (1 + -shellRate) (HKPos.one_sub_pos hshell)) :=
    Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hamplitude)
  exact Q'.eqv_trans _ _ _ hreplace (by
    unfold covarianceShellBase
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
      Q'.ofNat_den_cast, Int.natCast_mul]
    ac_rfl)

/-- The carrier enumeration factor alone fits below eleven dyadic bits per
support plaquette. -/
theorem supportEnumerationCount_le_two_pow {left : List Z4Link}
    (P : ProbeCarrier left) :
    supportEnumerationCount P ≤
      2 ^ (11 * (P.animal.support.length + 1)) := by
  let M := P.animal.support.length
  have h625 : 625 ≤ 2 ^ 10 := by decide
  have hp := Nat.pow_le_pow_left h625 (M + 1)
  calc
    supportEnumerationCount P ≤ 2 ^ (M + 1) * (2 ^ 10) ^ (M + 1) := by
      unfold supportEnumerationCount M
      exact Nat.mul_le_mul_left _ hp
    _ = (2 * 2 ^ 10) ^ (M + 1) := by rw [Nat.mul_pow]
    _ = (2 ^ 11) ^ (M + 1) := by
      congr 2
    _ = 2 ^ (11 * (M + 1)) := by rw [← Nat.pow_mul]

/-- After the quartic shell multiplicity is included, the complete natural
count still fits below one dyadic exponent linear in support. -/
theorem supportEnumerationCount_mul_countCap_le_two_pow
    {left : List Z4Link} (P : ProbeCarrier left) (r : Q') :
    supportEnumerationCount P * countCap r P.animal.support.length ≤
      2 ^ (15 * P.animal.support.length + 4 * blockLength r 4 + 26) := by
  let M := P.animal.support.length
  have hsupport := supportEnumerationCount_le_two_pow P
  have hshell := countCap_le_two_pow r M
  calc
    supportEnumerationCount P * countCap r M ≤
        2 ^ (11 * (M + 1)) *
          2 ^ (4 * M + 4 * blockLength r 4 + 15) :=
      Nat.mul_le_mul hsupport hshell
    _ = 2 ^ (15 * M + 4 * blockLength r 4 + 26) := by
      rw [← Nat.pow_add]
      congr 1
      omega

/-- The combined carrier and shell count is strictly positive. -/
theorem supportEnumerationCount_mul_countCap_pos
    {left : List Z4Link} (P : ProbeCarrier left) (r : Q') :
    0 < supportEnumerationCount P * countCap r P.animal.support.length := by
  have hsupport : 0 < supportEnumerationCount P := by
    unfold supportEnumerationCount
    exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hbase : 0 <
      2 * (P.animal.support.length + blockLength r 4) + 1 := by
    omega
  have hcount : 0 < countCap r P.animal.support.length := by
    unfold countCap
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.pow_pos hbase) (by decide)) (by decide)
  exact Nat.mul_pos hsupport hcount

/-- The actual shell cutoff for the guarded covariance amplitude is bounded by
a support-free denominator precision plus an exponent linear in the carrier
support and the geometric block length. -/
theorem dyadicBlockCutoff_le_supportLinear {left : List Z4Link}
    (P : ProbeCarrier left) {w r c epsilon : Q'}
    (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (hc : (0 : Q') ≤ c) (hepsilon : (0 : Q') < epsilon) :
    dyadicBlockCutoff hr0 hr1 P.animal.support.length
        (covarianceAmplitude hd hs P c) epsilon ≤
      blockLength (entropyRate 16 (r ^ blockLength r 4)) 0 *
        (denominatorBitPrecision
            (HKConv.divPos epsilon
              (1 + covarianceShellBase (left := left) w hd hs c
                (entropyRate 16 (r ^ blockLength r 4))
                (block_rate_lt_one hr0 hr1))) +
          (15 * P.animal.support.length + 4 * blockLength r 4 + 26)) := by
  let shellRate := entropyRate 16 (r ^ blockLength r 4)
  let shellCount := countCap r P.animal.support.length
  let combinedCount := supportEnumerationCount P * shellCount
  let base := covarianceShellBase (left := left) w hd hs c shellRate
    (block_rate_lt_one hr0 hr1)
  let coefficient :=
    ((covarianceAmplitude hd hs P c * Q'.ofNat shellCount) *
      Q'.recipPos (1 + -shellRate)
        (HKPos.one_sub_pos (block_rate_lt_one hr0 hr1)))
  have hbase : (0 : Q') ≤ base :=
    covarianceShellBase_nonnegative hw0 hd hs hc
      (block_rate_lt_one hr0 hr1)
  have hfactor : coefficient ≈ base * Q'.ofNat combinedCount := by
    simpa only [coefficient, base, combinedCount, shellCount, shellRate] using
      covarianceShellCoefficient_factor P w hd hs c shellRate
        (block_rate_lt_one hr0 hr1) shellCount
  have hcoefficient : (0 : Q') ≤ coefficient :=
    Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ hbase (ClusterCount.ofNat_nonneg combinedCount))
      (Q'.ge_of_eqv hfactor)
  have hcount : combinedCount ≤
      2 ^ (15 * P.animal.support.length + 4 * blockLength r 4 + 26) := by
    simpa only [combinedCount, shellCount] using
      supportEnumerationCount_mul_countCap_le_two_pow P r
  have hcountPos : 0 < combinedCount := by
    simpa only [combinedCount, shellCount] using
      supportEnumerationCount_mul_countCap_pos P r
  have hbits : 0 <
      15 * P.animal.support.length + 4 * blockLength r 4 + 26 := by
    omega
  unfold dyadicBlockCutoff
  dsimp only
  exact cutoff_le_base_precision_add_count_bits_of_positive_bits
    hcoefficient hbase hepsilon hcountPos hbits hcount
    (Q'.le_of_eqv hfactor)

/-- Monotone version with any certified upper bound for the carrier support. -/
theorem dyadicBlockCutoff_le_supportUpperBound {left : List Z4Link}
    (P : ProbeCarrier left) {w r c epsilon : Q'}
    (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (hc : (0 : Q') ≤ c) (hepsilon : (0 : Q') < epsilon)
    (supportCap : Nat) (hsupport : P.animal.support.length ≤ supportCap) :
    dyadicBlockCutoff hr0 hr1 P.animal.support.length
        (covarianceAmplitude hd hs P c) epsilon ≤
      blockLength (entropyRate 16 (r ^ blockLength r 4)) 0 *
        (denominatorBitPrecision
            (HKConv.divPos epsilon
              (1 + covarianceShellBase (left := left) w hd hs c
                (entropyRate 16 (r ^ blockLength r 4))
                (block_rate_lt_one hr0 hr1))) +
          (15 * supportCap + 4 * blockLength r 4 + 26)) := by
  have hcutoff := dyadicBlockCutoff_le_supportLinear P hw0 hd hs hr0 hr1 hc hepsilon
  exact Nat.le_trans hcutoff (Nat.mul_le_mul_left _ (by omega))

end YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale

#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.supportEnumerationCount
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.amplitude_factor
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.covarianceAmplitudeBase
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.covarianceAmplitude_factor
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.covarianceShellBase
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.covarianceShellCoefficient_factor
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.supportEnumerationCount_le_two_pow
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.supportEnumerationCount_mul_countCap_le_two_pow
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.dyadicBlockCutoff_le_supportLinear
#print axioms YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale.dyadicBlockCutoff_le_supportUpperBound
