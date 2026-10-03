/-
# The actual OWN odd mean at every terminal depth

At fixed nome 1/16 and width two, retain BOTH original terminal messages
and the complete original spatial weight. All-insertion terminal transport
and actual fringe peeling identify their odd numerator and partition with
the literal six-face cube integrals. The constructed relative Haar shape
then bounds the EXISTING interacting mean by 1/4, at every guarded cutoff
and every depth. Bare Haar amplitudes are not substituted for partitions.

This pays a finite weighted mean estimate, not the tested-overlap floor,
signed gain, changing-family survival or continuum Yang--Mills claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
import YMGap.Continuum.QuaternionHaarRelativeShapePair

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight (spatialWeight_haar_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (mean mean_pin)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome smallNome_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval (bentObservableInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (bent_haar_zero)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarRelativeShapePair

local notation "N" => List.length (baseLinks 2)
local notation:max "H" p:arg => quaternionHaar N p
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight weightedMass terminalMessage cubeTerminal
  cubeWeight bentObservable mean

def pairShapeError : Q' := 2*terminalRadius+terminalRadius*terminalRadius
def partitionFactor : Q' := 1-actionDeviation-(1+actionDeviation)*pairShapeError
def numeratorFactor : Q' := 2*actionDeviation+2*(1+actionDeviation)*pairShapeError
def meanCap : Q' := Q'.mkPos 1 4 (by decide)

/-- The ORIGINAL odd partition at depths (n+1,n). -/
def originalOddPartition (K n : Nat) : Q' :=
  weightedMass smallNome K 2
    (polyMul (terminalMessage smallNome K 2 (n+1)) (terminalMessage smallNome K 2 n))

/-- The literal original numerator has exactly the same two terminal factors. -/
def originalOddNumerator (K n : Nat) : Q' :=
  weightedMass smallNome K 2 (polyMul
    (polyMul (terminalMessage smallNome K 2 (n+1)) bentObservable)
    (terminalMessage smallNome K 2 n))

def cubeOddBackground (K n : Nat) : RatPoly :=
  polyMul (cubeWeight smallNome K)
    (polyMul (cubeTerminal K (n+1)) (cubeTerminal K n))

private theorem weight_supported (K : Nat) :
    SupportedQuaternionBlocks N (cubeWeight smallNome K) := by
  unfold cubeWeight
  exact YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence.heatProduct_supported
    smallNome K 2 cubeFaces

private theorem weighted_core (K : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks N p)
    (hi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i p) :
    weightedMass smallNome K 2 p ≈ H (polyMul (cubeWeight smallNome K) p) := by
  unfold weightedMass
  exact Q'.eqv_trans _ _ _
    (spatialWeight_haar_active smallNome K 2 p hp (fun i h =>
      hi i (fringeBlocks_lt 2 i h)
        (fun hc => ((fringeBlocks_mem_iff 2 i).mp h).2 (cubeIndices_active i hc))))
    (haar_of_coeff (blocks := N) ((activeSpatialWeight_cube smallNome K).mul_right p))

/-- Reusable full ORIGINAL source transport. Only the supplied insertion is
required to be cube-local; the raw original terminal messages are not. -/
theorem original_terminal_pair_weighted_pin (K m n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks N p)
    (hpi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i p) :
    weightedMass smallNome K 2 (polyMul
      (polyMul (terminalMessage smallNome K 2 m) p) (terminalMessage smallNome K 2 n)) ≈
    H (polyMul (cubeWeight smallNome K)
      (polyMul (polyMul (cubeTerminal K m) p) (cubeTerminal K n))) := by
  have hfirst := (terminalMessage_cubeTerminal K m).mul (SupportedHaarEqv.refl N p)
    hp (cubeTerminal_supported K m)
  have hpair := hfirst.mul (terminalMessage_cubeTerminal K n)
    (terminalMessage_supported smallNome K 2 n)
    (supported_polyMul (cubeTerminal_supported K m) hp)
  have htest := hpair (spatialWeight smallNome K 2) (spatialWeight_supported smallNome K 2)
  have hweighted : weightedMass smallNome K 2 (polyMul
      (polyMul (terminalMessage smallNome K 2 m) p) (terminalMessage smallNome K 2 n)) ≈
      weightedMass smallNome K 2 (polyMul (polyMul (cubeTerminal K m) p) (cubeTerminal K n)) := by
    unfold weightedMass
    exact htest
  exact Q'.eqv_trans _ _ _ hweighted
    (weighted_core K
      (supported_polyMul (supported_polyMul (cubeTerminal_supported K m) hp)
        (cubeTerminal_supported K n))
      (fun i hi hn => quaternionBlockIndependent_polyMul
        (quaternionBlockIndependent_polyMul (cubeTerminal_independent K m i hi hn)
          (hpi i hi hn)) (cubeTerminal_independent K n i hi hn)))

theorem original_terminal_weighted_pin (K n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks N p)
    (hpi : ∀ i, i < N → i ∉ cubeIndices → QuaternionBlockIndependent i p) :
    weightedMass smallNome K 2 (polyMul (terminalMessage smallNome K 2 n) p) ≈
      H (polyMul (cubeWeight smallNome K) (polyMul (cubeTerminal K n) p)) := by
  have h := original_terminal_pair_weighted_pin K n 0 hp hpi
  have hz : terminalMessage smallNome K 2 0 = polyOne := by unfold terminalMessage; rfl
  have hc : cubeTerminal K 0 = polyOne := by unfold cubeTerminal; rfl
  rw [hz, hc] at h
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (weightedMass_congr smallNome K 2
    (RatPolyCoeffEqv.mul_one _))) (Q'.eqv_trans _ _ _ h
      (haar_of_coeff (blocks := N) ((RatPolyCoeffEqv.refl _).mul
        (RatPolyCoeffEqv.mul_one _))))

theorem originalOddPartition_cube_pin (K n : Nat) :
    originalOddPartition K n ≈ H (cubeOddBackground K n) := by
  have h := original_terminal_pair_weighted_pin K (n+1) n (supported_one N)
    (fun i _ _ =>
      YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini.quaternionBlockIndependent_polyOne i)
  unfold originalOddPartition cubeOddBackground
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (weightedMass_congr smallNome K 2
    ((RatPolyCoeffEqv.mul_one _).mul (RatPolyCoeffEqv.refl _))))
    (Q'.eqv_trans _ _ _ h (haar_of_coeff (blocks := N)
      ((RatPolyCoeffEqv.refl _).mul
        ((RatPolyCoeffEqv.mul_one _).mul (RatPolyCoeffEqv.refl _)))))

theorem originalOddNumerator_cube_pin (K n : Nat) :
    originalOddNumerator K n ≈ H (polyMul (cubeOddBackground K n) bentObservable) := by
  have h := original_terminal_pair_weighted_pin K (n+1) n bentObservable_supported
    bentObservable_cube_independent
  have he : RatPolyCoeffEqv
      (polyMul (cubeWeight smallNome K)
        (polyMul (polyMul (cubeTerminal K (n+1)) bentObservable) (cubeTerminal K n)))
      (polyMul (cubeOddBackground K n) bentObservable) := by
    unfold cubeOddBackground
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.var 2)))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (by decide) (fun
        | 0 => cubeWeight smallNome K
        | 1 => cubeTerminal K (n+1)
        | 2 => cubeTerminal K n
        | _ => bentObservable)
  exact Q'.eqv_trans _ _ _ h (haar_of_coeff (blocks := N) he)

private def actionInterval (K : Nat) (hK : 1 ≤ K) :
    Interval N (cubeWeight smallNome K) (1+actionDeviation) := by
  have P := (sharpCubeRemainder K hK).add (Interval.one N)
  have he : RatPolyCoeffEqv (cubeWeight smallNome K)
      (polyAdd (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) polyOne) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.const 1))) (.const 1)) (.var 0)
      (by decide) (fun _ => cubeWeight smallNome K)).symm
  exact (Interval.ofCoeff (weight_supported K) he P).changeCap (Q'.add_comm_eqv _ _)

private theorem haar_one : H polyOne ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one N)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem action_remainder_mass (K : Nat) :
    H (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) + 1 ≈
      H (cubeWeight smallNome K) := by
  have hp : RatPolyCoeffEqv
      (polyAdd (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) polyOne)
      (cubeWeight smallNome K) := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.neg (.const 1))) (.const 1)) (.var 0)
    (by decide) (fun _ => cubeWeight smallNome K)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm haar_one))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append N _ _))
      (haar_of_coeff (blocks := N) hp))

private theorem lower_of_abs_sub (x y e : Q') (h : Q'.abs (x-y) ≤ e) : y-e ≤ x := by
  have hl : -e ≤ x-y := Q'.le_trans' _ _ _ (Q'.neg_le_neg h)
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs (x-y)))
      (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
  have hh := Q'.add_le_add_left y _ _ hl
  have he : y+(x-y) ≈ x := poly_identity_of_normal_eq
    (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
    (by decide) (fun | 0 => x | _ => y)
  exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv he)

private theorem action_mass_lower (K : Nat) (hK : 1 ≤ K) :
    1-actionDeviation ≤ H (cubeWeight smallNome K) := by
  have h := (sharpCubeRemainder K hK).haar_bound
  have hl : -actionDeviation ≤ H (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg h)
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs _))
        (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
  have he : -actionDeviation+1 ≈ 1-actionDeviation := Q'.add_comm_eqv _ _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ 1 hl)
      (Q'.le_of_eqv (action_remainder_mass K)))

private theorem action_bent_abs (K : Nat) (hK : 1 ≤ K) :
    Q'.abs (H (polyMul (cubeWeight smallNome K) bentObservable)) ≤ 2*actionDeviation := by
  have h := ((sharpCubeRemainder K hK).mul bentObservableInterval).haar_bound
  have hp : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) bentObservable)
        bentObservable) (polyMul (cubeWeight smallNome K) bentObservable) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.neg (.const 1))) (.var 1)) (.var 1))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun | 0 => cubeWeight smallNome K | _ => bentObservable)
  have he : H (polyMul (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) bentObservable) ≈
      H (polyMul (cubeWeight smallNome K) bentObservable) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _).symm)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm bent_haar_zero))
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append N _ _))
          (haar_of_coeff (blocks := N) hp)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

attribute [local irreducible] originalOddPartition originalOddNumerator cubeOddBackground

private theorem terminal_pair_error (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) {T : RatPoly} {C : Q'}
    (I : Interval N T C) :
    Q'.abs (H (polyMul T (polyMul (cubeTerminal K (n+1)) (cubeTerminal K n))) -
      (H (cubeTerminal K (n+1))*H (cubeTerminal K n))*H T) ≤
      C*pairShapeError*(H (cubeTerminal K (n+1))*H (cubeTerminal K n)) := by
  simpa only [pairShapeError] using pair_shape_insertion_bound
    (cubeTerminal_supported K (n+1)) (cubeTerminal_supported K n) I
    (cubeTerminal_mass_positive K hK hhead (n+1))
    (cubeTerminal_mass_positive K hK hhead n) (by decide : (0 : Q') ≤ terminalRadius)
    (cubeTerminal_variance_bound K hK hhead (n+1))
    (cubeTerminal_variance_bound K hK hhead n)

/-- The denominator is the ACTUAL original odd partition, with its
constructed amplitude product retained rather than assumed to be one. -/
theorem originalOddPartition_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    partitionFactor*(H (cubeTerminal K (n+1))*H (cubeTerminal K n)) ≤
      originalOddPartition K n := by
  let A := H (cubeTerminal K (n+1))*H (cubeTerminal K n)
  let v := H (cubeWeight smallNome K)
  let e := (1+actionDeviation)*pairShapeError
  have ha : (0 : Q') ≤ A := Q'.le_of_lt (Q'.mul_pos
    (cubeTerminal_mass_positive K hK hhead (n+1))
    (cubeTerminal_mass_positive K hK hhead n))
  have herr := terminal_pair_error K hK hhead n (actionInterval K hK)
  have hl : A*v-e*A ≤ H (cubeOddBackground K n) := by
    unfold cubeOddBackground
    exact lower_of_abs_sub _ _ _ herr
  have hbase : (1-actionDeviation)*A ≤ A*v :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ A (action_mass_lower K hK) ha)
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  have he : partitionFactor*A ≈ (1-actionDeviation)*A-e*A := by
    unfold partitionFactor e
    exact poly_identity_of_normal_eq
      (.mul (.add (.add (.const 1) (.neg (.var 0)))
        (.neg (.mul (.add (.const 1) (.var 0)) (.var 1)))) (.var 2))
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 2))
        (.neg (.mul (.mul (.add (.const 1) (.var 0)) (.var 1)) (.var 2))))
      (by decide) (fun
        | 0 => actionDeviation
        | 1 => pairShapeError
        | _ => A)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-(e*A)) hbase)
      (Q'.le_trans' _ _ _ hl (Q'.ge_of_eqv (originalOddPartition_cube_pin K n))))

theorem originalOddPartition_positive (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (0 : Q') < originalOddPartition K n :=
  HeatKernelRGStep.lt_of_lt_of_le
    (Q'.mul_pos (by decide : (0 : Q') < partitionFactor)
      (Q'.mul_pos (cubeTerminal_mass_positive K hK hhead (n+1))
        (cubeTerminal_mass_positive K hK hhead n)))
    (originalOddPartition_floor K hK hhead n)

private theorem abs_from_sub_error (x y e : Q') (h : Q'.abs (x-y) ≤ e) :
    Q'.abs x ≤ e+Q'.abs y := by
  have he : (x-y)+y ≈ x := poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
    (by decide) (fun | 0 => x | _ => y)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (Q'.add_le_add_right _ _ _ h))

theorem originalOddNumerator_abs_le (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    Q'.abs (originalOddNumerator K n) ≤
      numeratorFactor*(H (cubeTerminal K (n+1))*H (cubeTerminal K n)) := by
  let A := H (cubeTerminal K (n+1))*H (cubeTerminal K n)
  let T := polyMul (cubeWeight smallNome K) bentObservable
  let e := ((1+actionDeviation)*2)*pairShapeError
  have ha : (0 : Q') ≤ A := Q'.le_of_lt (Q'.mul_pos
    (cubeTerminal_mass_positive K hK hhead (n+1))
    (cubeTerminal_mass_positive K hK hhead n))
  have herr := terminal_pair_error K hK hhead n ((actionInterval K hK).mul bentObservableInterval)
  have hraw := abs_from_sub_error _ _ _ herr
  have hbase : Q'.abs (A*H T) ≤ A*(2*actionDeviation) := by
    have h := ExpNeg.abs_mul_le A (H T)
    rw [ExpNeg.abs_of_nonneg ha] at h
    exact Q'.le_trans' _ _ _ h
      (Q'.mul_le_mul_of_nonneg_left _ _ A (action_bent_abs K hK) ha)
  have he : e*A+A*(2*actionDeviation) ≈ numeratorFactor*A := by
    unfold e numeratorFactor
    exact poly_identity_of_normal_eq
      (.add (.mul (.mul (.mul (.add (.const 1) (.var 0)) (.const 2)) (.var 1)) (.var 2))
        (.mul (.var 2) (.mul (.const 2) (.var 0))))
      (.mul (.add (.mul (.const 2) (.var 0))
        (.mul (.mul (.const 2) (.add (.const 1) (.var 0))) (.var 1))) (.var 2))
      (by decide) (fun
        | 0 => actionDeviation
        | 1 => pairShapeError
        | _ => A)
  have hpin : originalOddNumerator K n ≈
      H (polyMul T (polyMul (cubeTerminal K (n+1)) (cubeTerminal K n))) := by
    have hp : RatPolyCoeffEqv (polyMul (cubeOddBackground K n) bentObservable)
        (polyMul T (polyMul (cubeTerminal K (n+1)) (cubeTerminal K n))) := by
      unfold cubeOddBackground T
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
        (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => cubeWeight smallNome K
          | 1 => cubeTerminal K (n+1)
          | 2 => cubeTerminal K n
          | _ => bentObservable)
    exact Q'.eqv_trans _ _ _ (originalOddNumerator_cube_pin K n)
      (haar_of_coeff (blocks := N) hp)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left (e*A) _ _ hbase) (Q'.le_of_eqv he)))

/-- The ratio is pinned to the EXISTING edge mean with its original
odd-law center; no replacement mean is introduced. -/
theorem mean_odd_ratio_pin (K : Nat) (hhead : headCutoff smallNome ≤ K) (n : Nat)
    (hZ : (0 : Q') < originalOddPartition K n) :
    mean smallNome_pos (by decide) K 2 hhead n bentObservable ≈
      Q'.divPos (originalOddNumerator K n) (originalOddPartition K n) hZ := by
  have h := mean_pin smallNome_pos (by decide) K 2 hhead n bentObservable_supported
  have hm : middleRatio smallNome_pos (by decide) K 2 hhead (n+1) n bentObservable ≈
      Q'.divPos (originalOddNumerator K n) (originalOddPartition K n) hZ := by
    unfold middleRatio massRatio originalOddNumerator originalOddPartition Q'.divPos
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ h hm

/-- Literally the original interacting OWN mean at the supplied depth. -/
def originalOddMean (K : Nat) (_hK : 1 ≤ K) (hhead : headCutoff smallNome ≤ K) (n : Nat) : Q' :=
  mean smallNome_pos (by decide) K 2 hhead n bentObservable

theorem originalOddMean_pin (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    originalOddMean K hK hhead n ≈
      Q'.divPos (originalOddNumerator K n) (originalOddPartition K n)
        (originalOddPartition_positive K hK hhead n) :=
  mean_odd_ratio_pin K hhead n (originalOddPartition_positive K hK hhead n)

attribute [local irreducible] originalOddMean

theorem originalOddMean_bounds (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    -meanCap ≤ originalOddMean K hK hhead n ∧ originalOddMean K hK hhead n ≤ meanCap := by
  let A := H (cubeTerminal K (n+1))*H (cubeTerminal K n)
  have ha : (0 : Q') ≤ A := Q'.le_of_lt (Q'.mul_pos
    (cubeTerminal_mass_positive K hK hhead (n+1))
    (cubeTerminal_mass_positive K hK hhead n))
  have hN := originalOddNumerator_abs_le K hK hhead n
  have hZ := originalOddPartition_floor K hK hhead n
  have hscalar : numeratorFactor ≤ meanCap*partitionFactor := by decide
  have hcap : Q'.abs (originalOddNumerator K n) ≤ meanCap*originalOddPartition K n :=
    Q'.le_trans' _ _ _ hN
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ A hscalar ha)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
          (Q'.mul_le_mul_of_nonneg_left _ _ meanCap hZ (by decide))))
  have hu := Q'.le_trans' _ _ _ (Q'.le_abs_self _) hcap
  have hn := Q'.le_trans' _ _ _ (Q'.neg_le_abs _) hcap
  have hl : -meanCap*originalOddPartition K n ≤ originalOddNumerator K n :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_mul_eqv _ _))
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg hn) (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
  have hp := originalOddMean_pin K hK hhead n
  exact ⟨Q'.le_trans' _ _ _
      (Q'.le_divPos_of_mul_le _ _ (originalOddPartition_positive K hK hhead n) hl)
      (Q'.ge_of_eqv hp),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (Q'.divPos_le_of_le_mul _ _ (originalOddPartition_positive K hK hhead n) hu)⟩

theorem originalOddMean_abs_le (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    Q'.abs (originalOddMean K hK hhead n) ≤ meanCap :=
  Q'.abs_le (originalOddMean_bounds K hK hhead n).1 (originalOddMean_bounds K hK hhead n).2

theorem existingMean_abs_le (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    Q'.abs (mean smallNome_pos (by decide) K 2 hhead n bentObservable) ≤ meanCap := by
  have h := originalOddMean_abs_le K hK hhead n
  unfold originalOddMean at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.cubeOddBackground
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.original_terminal_pair_weighted_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.original_terminal_weighted_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddPartition_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddNumerator_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddPartition_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddPartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddNumerator_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.mean_odd_ratio_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddMean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddMean_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddMean_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.originalOddMean_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean.existingMean_abs_le
