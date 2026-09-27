/-
# Spatial control of the ORIGINAL signed covariance response under the old guard

Retain the actual two endpoint partitions. A one-face relative floor and
the proved two-probe clustering estimate bound changes of the three moments
p, q and pq. Recombining them bounds the complete signed covariance response,
and therefore its already constructed rooted sum, without taking absolute
values term by term over three-mark cores or paying their collarCost.

Both observables use ONE supplied connected carrier. Distance is from that
carrier to the inserted face, not the full three-mark diameter for arbitrarily
separated probes. All heatRatio, remainder and entropy small-nome guards are
retained. The budget has no ambient face count or representation cutoff;
its coupling and probe-support dependence is explicit. The final passage
removes only the heat cutoff at fixed volume and nome. No weakening of the
guard, physical-spacing estimate, thermodynamic rate or Clay closure follows.
-/

import YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
import YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
import YMGap.Continuum.BF4ExactSlabRootedResponseResummation
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.BF4ExactSlabSummedCouplingDefects

namespace YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison (ratio_difference_bound)
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation (connectedNumerator)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabRootedResponseResummation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget (twoProbeBudget)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabSummedCouplingDefects (amplitude singleton_budget)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem appended_physical {extent : Nat} {ids : List Nat} {id : Nat}
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    ∀ j, j ∈ ids++[id] → j ∈ slabPhysicalFaceEdges extent := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hi j hj
  · have he := List.mem_singleton.mp hj
    subst j
    exact hid

private theorem budget_nonnegative {w c d : Q'} (hw : (0 : Q') ≤ w)
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hc : (0 : Q') ≤ c) (hd0 : (0 : Q') ≤ d) :
    (0 : Q') ≤ distanceBudget P Q w hd hs c d :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hc hd0) (Q'.mul_nonneg _ _ hc hd0))
      (probePrefactor_nonnegative w hd _))
    (tailBudget_nonnegative _ _ _ (adjustedCoreRate_nonnegative hw hd) hs)

private theorem relative_square {z r ell inv d : Q'}
    (hz : (0 : Q') ≤ z) (hi : (0 : Q') ≤ inv) (hd : (0 : Q') ≤ d)
    (hpin : inv*ell ≈ 1) (hfloor : ell*z ≤ r) :
    d*(z*z) ≤ (d*inv)*(r*z) := by
  have hp : inv*(ell*z) ≈ z :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpin) (Q'.one_mul_eqv _))
  have hzr : z ≤ inv*r := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor hi)
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hzr hz) hd
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => d | 1 => inv | 2 => r | _ => z)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

/-- Only ONE relative face floor is paid, after the original covariance estimate. -/
def momentBudget {left : List Z4Link} (P : ProbeCarrier left) (face : Z4Plaq) (c : Q') : Q' :=
  distanceBudget P (singletonCarrier face) w hd hs c (prefixCap w) * inverseFaceFloor w hd

/-- The three changes needed for covariance, not a sum over rooted cores. -/
def covarianceBudget {left : List Z4Link} (P : ProbeCarrier left) (face : Z4Plaq) (c : Q') : Q' :=
  momentBudget hd hs P face (c*c) + (c*momentBudget hd hs P face c + c*momentBudget hd hs P face c)

/-- Explicit amplitude with no insertion position, ambient extent or cutoff. -/
def covarianceAmplitude {left : List Z4Link} (P : ProbeCarrier left) (c : Q') : Q' :=
  amplitude P w hd hs (c*c) (prefixCap w)*inverseFaceFloor w hd +
    (c*(amplitude P w hd hs c (prefixCap w)*inverseFaceFloor w hd) +
      c*(amplitude P w hd hs c (prefixCap w)*inverseFaceFloor w hd))

theorem covarianceBudget_geometric {left : List Z4Link} (P : ProbeCarrier left) (face : Z4Plaq) (c : Q') :
    covarianceBudget hd hs P face c ≈ covarianceAmplitude hd hs P c *
      (entropyRate 625 (adjustedCoreRate w hd))^(linfDist P.animal.root face-P.animal.support.length) := by
  let r := (entropyRate 625 (adjustedCoreRate w hd))^(linfDist P.animal.root face-P.animal.support.length)
  have h (a : Q') : momentBudget hd hs P face a ≈
      (amplitude P w hd hs a (prefixCap w)*r)*inverseFaceFloor w hd :=
    Q'.mul_eqv_congr_right _ _ _ (singleton_budget P face w hd hs a (prefixCap w))
  have he := Q'.add_eqv_congr' (h (c*c)) (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left c _ _ (h c)) (Q'.mul_eqv_congr_left c _ _ (h c)))
  exact Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 3)) (.var 4))
      (.add (.mul (.var 2) (.mul (.mul (.var 1) (.var 3)) (.var 4)))
        (.mul (.var 2) (.mul (.mul (.var 1) (.var 3)) (.var 4)))))
    (.mul (.add (.mul (.var 0) (.var 4))
      (.add (.mul (.var 2) (.mul (.var 1) (.var 4)))
        (.mul (.var 2) (.mul (.var 1) (.var 4))))) (.var 3))
    (by decide) (fun
      | 0 => amplitude P w hd hs (c*c) (prefixCap w)
      | 1 => amplitude P w hd hs c (prefixCap w)
      | 2 => c
      | 3 => r
      | _ => inverseFaceFloor w hd))

include hw0 hw1 hsmall in
/-- Complete original selected action at both endpoints, with no face-count loss. -/
theorem finite_moment_insertion_bound (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) (stage : Nat) :
    Q'.abs (finiteValue w hw0 hw1 extent (ids++[id]) (appended_physical hi hid) p stage +
      -(finiteValue w hw0 hw1 extent ids hi p stage)) ≤ momentBudget hd hs P (slabPlaquetteAt extent id) c := by
  let K := headCutoff w+stage
  let B := polynomialProduct (faceHeatPolynomial w K extent) ids
  let Z := heatProductHaar w (blocks extent) extent ids K
  let R := heatProductHaar w (blocks extent) extent (ids++[id]) K
  let D := distanceBudget P (singletonCarrier (slabPlaquetteAt extent id)) w hd hs c (prefixCap w)
  have hZ : (0 : Q') < Z := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partition_floor hw0 hw1 extent ids hi K (Nat.le_add_right _ _))
  have hR : (0 : Q') < R := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 (ids++[id]))
    (partition_floor hw0 hw1 extent (ids++[id]) (appended_physical hi hid) K (Nat.le_add_right _ _))
  have hF : (1 + -heatRemainderBound w)*Z ≤ R :=
    Q'.le_trans' _ _ _
      (insertFace_lower (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall extent id hid K
        (headProduct_certificate hw0 hw1 K extent (Nat.le_add_right _ _) ids hi))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm B _))
        (Q'.eqv_symm (partition_append_face w K extent ids id))))
  have hb : Q'.abs (connectedNumerator w K extent ids p (faceHeatPolynomial w K extent id)) ≤ D*(Z*Z) :=
    connectedNumerator_distance_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs K extent p
      (faceHeatPolynomial w K extent id) c (prefixCap w) Ip (facePrefixInterval hw0 hw1 K extent id hid)
      left (edgesOf (slabPlaquetteAt extent id)) P (singletonCarrier (slabPlaquetteAt extent id))
      hp (heatFace_local w K extent id) ids hn hi
  have hD := budget_nonnegative (Q'.le_of_lt hw0) hd hs P
    (singletonCarrier (slabPlaquetteAt extent id)) Ip.nonnegative (prefixCap_nonnegative hw0)
  have hrel := relative_square (Q'.le_of_lt hZ) (Q'.le_of_lt (inverseFaceFloor_pos w hd)) hD
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ (HKPos.one_sub_pos hd))) hF
  have hdet := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (face_insertion_determinant w K extent ids id p)))
    (Q'.le_trans' _ _ _ hb hrel)
  exact ratio_difference_bound _ _ R Z (momentBudget hd hs P (slabPlaquetteAt extent id) c) hR hZ hdet

include hw0 hw1 hsmall in
/-- p and q retain a common fixed carrier; pq adds no distant connecting corridor. -/
theorem finite_covariance_insertion_bound (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    {p q : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) (hq : LinkLocal extent left q)
    (stage : Nat) :
    Q'.abs (finiteCovariance w hw0 hw1 extent (ids++[id]) (appended_physical hi hid) p q stage +
      -(finiteCovariance w hw0 hw1 extent ids hi p q stage)) ≤ covarianceBudget hd hs P (slabPlaquetteAt extent id) c :=
  covariance_difference_bound _ _ _ _ _ _ c _ _ _
    (finiteValue_abs_bound w hw0 hw1 extent (ids++[id]) (appended_physical hi hid) p c Ip stage)
    (finiteValue_abs_bound w hw0 hw1 extent ids hi q c Iq stage)
    (finite_moment_insertion_bound hw0 hw1 hsmall hd hs extent ids hn hi id hid (Ip.mul Iq)
      left P (hp.mul hq) stage)
    (finite_moment_insertion_bound hw0 hw1 hsmall hd hs extent ids hn hi id hid Ip left P hp stage)
    (finite_moment_insertion_bound hw0 hw1 hsmall hd hs extent ids hn hi id hid Iq left P hq stage)

include hw0 hw1 hsmall in
/-- The entire signed response is controlled with its EXACT endpoint denominator. -/
theorem signed_response_bound (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    {p q : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) (hq : LinkLocal extent left q)
    (K : Nat) (hK : headCutoff w ≤ K) :
    Q'.abs (response w K extent ids id p q) ≤
      covarianceBudget hd hs P (slabPlaquetteAt extent id) c * responseDenominator w K extent ids id := by
  have hstage := finite_covariance_insertion_bound hw0 hw1 hsmall hd hs extent ids hn hi id hid Ip Iq left P hp hq
    (K-headCutoff w)
  have hpin := finite_response_cleared w hw0 hw1 extent ids hi id hid p q (K-headCutoff w)
  rw [Nat.add_sub_of_le hK] at hpin
  have hden := Q'.le_of_lt (responseDenominator_positive w hw0 hw1 extent ids hi id hid K hK)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.abs_mul_nonneg_right _ hden))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hstage hden))

include hw0 hw1 hsmall in
/-- This bounds the existing rooted SIGNED sum, not its termwise absolute majorant. -/
theorem rooted_signed_response_bound (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    {p q : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) (hq : LinkLocal extent left q)
    (K : Nat) (hK : headCutoff w ≤ K) :
    Q'.abs (rootedResponse w K extent id p q left left ids) ≤
      covarianceBudget hd hs P (slabPlaquetteAt extent id) c * responseDenominator w K extent ids id :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr
    (response_resummed_filtered w K extent p q left left Ip.support Iq.support hp hq ids hn id)))
    (signed_response_bound hw0 hw1 hsmall hd hs extent ids hn hi id hid Ip Iq left P hp hq K hK)

include hw0 hw1 hsmall in
/-- Existing fixed-volume, fixed-nome cutoff-removed covariance; no new limit. -/
theorem covariance_insertion_bound (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    {p q : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) (hq : LinkLocal extent left q) :
    CReal.leEv (CReal.abs (CReal.sub
      (covariance w hw0 hw1 extent (ids++[id]) (appended_physical hi hid) p q)
      (covariance w hw0 hw1 extent ids hi p q)))
      (CReal.ofQ' (covarianceBudget hd hs P (slabPlaquetteAt extent id) c)) :=
  covariance_response_bound_eventually w hw0 hw1 extent ids hi id hid p q _ (headCutoff w)
    (signed_response_bound hw0 hw1 hsmall hd hs extent ids hn hi id hid Ip Iq left P hp hq)

end YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse

#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.momentBudget
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.covarianceBudget
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.covarianceAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.covarianceBudget_geometric
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.finite_moment_insertion_bound
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.finite_covariance_insertion_bound
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.signed_response_bound
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.rooted_signed_response_bound
#print axioms YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse.covariance_insertion_bound
