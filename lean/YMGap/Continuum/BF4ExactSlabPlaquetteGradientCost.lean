/-
# Explicit original-action cost of the constructed plaquette gradient family

The actual fundamental-character gradient has value/derivative caps
(4096,32768). The incident signed sum therefore has caps proportional only
to its local absolute coefficient sum. Six incident faces and four links
per face turn the diagonal score cost into 24*C(w)^2 times the GLOBAL sum
of coefficient squares, with no additional family-size/extent factor.

C(w) is explicit and nome-dependent. No uniform near-one estimate, strict
energy floor, OS gap or continuum assertion follows from this upper bound.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteSecondAngularInterval
import YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy
import YMGap.Continuum.BF4ExactSlabWardIncidenceSum

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalWardScoreBound
open YMGap.Continuum.BF4ExactSlabOriginalWardLocality
open YMGap.Continuum.BF4ExactSlabWardFamilyCost
open YMGap.Continuum.BF4ExactSlabPlaquetteGradient
open YMGap.Continuum.BF4ExactSlabPlaquetteWardEnergy
open YMGap.Continuum.BF4ExactSlabPlaquetteSecondAngularInterval
open YMGap.Continuum.BF4ExactSlabWardIncidenceSum
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularProductBounds
open YMGap.Continuum.QuaternionHaarSecondAngularBounds
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- The explicit nome-dependent coefficient of the local score cap. -/
def scoreCoefficient (w : Q') : Q' := wardScoreCap w 4096 32768

def coefficientSquares (extent : Nat) (c : Nat → Q') : Q' :=
  listQSum (fun id => c id*c id) (slabPhysicalFaceEdges extent)

def incidentAbs (extent : Nat) (link : Z4Link) (c : Nat → Q') : Q' :=
  listQSum (fun id => Q'.abs (c id)) (incidentIds extent link)

variable (extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
local notation "swap" => linkHeadSwap extent link hl

/-- Actual first and second derivatives of the fundamental character. -/
def faceGradientBound {i j : Nat} (hi : i < 4) (hj : j < 4) (face : Z4Plaq) :
    AngularBound (blocks extent) i j
      (angularDerivative i j (reindexQuaternionPolynomial swap (faceCharacter extent face))) 4096 32768 := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  unfold faceCharacter characterPolynomial
  rw [reindexQuaternionPolynomial_smul]
  exact AngularBound.ofCarrier hb hi hj
    (angularDerivative_supported hb hi hj (polySmul_supported (reindex_supported swap _) 2))
    (RatPolyCoeffEqv.haarCarrier (angularDerivative_smul i j 2 _))
    ((angularSmul hb hi hj 2 (selectedPlaquetteSecondAngularInterval hi hj extent link hl face)).changeCaps
      (by decide) (by decide))

private def termGradientBound {i j : Nat} (hi : i < 4) (hj : j < 4)
    (c : Nat → Q') (id : Nat) :
    AngularBound (blocks extent) i j
      (angularDerivative i j (reindexQuaternionPolynomial swap (term extent c id)))
      (4096*Q'.abs (c id)) (32768*Q'.abs (c id)) := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  unfold term
  rw [reindexQuaternionPolynomial_smul]
  exact AngularBound.ofCarrier hb hi hj
    (angularDerivative_supported hb hi hj (polySmul_supported (reindex_supported swap _) (c id)))
    (RatPolyCoeffEqv.haarCarrier (angularDerivative_smul i j (c id) _))
    ((angularSmul hb hi hj (c id) (faceGradientBound extent link hl hi hj (slabPlaquetteAt extent id))).changeCaps
      (Q'.mul_comm_eqv _ _) (Q'.mul_comm_eqv _ _))

private def sumGradientBound {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    ∀ ids : List Nat, AngularBound (blocks extent) i j
      (angularDerivative i j (reindexQuaternionPolynomial swap (finitePolySum (term extent c) ids)))
      (4096*listQSum (fun id => Q'.abs (c id)) ids)
      (32768*listQSum (fun id => Q'.abs (c id)) ids)
  | [] => AngularBound.zero.changeCaps (Q'.eqv_symm (Q'.mul_zero_eqv _)) (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | id :: ids => by
      have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
      rw [finitePolySum, reindexQuaternionPolynomial_add]
      exact AngularBound.ofCarrier hb hi hj
        (angularDerivative_supported hb hi hj (supported_add (reindex_supported swap _) (reindex_supported swap _)))
        (RatPolyCoeffEqv.haarCarrier (angularDerivative_add i j _ _))
        (((termGradientBound extent link hl hi hj c id).add hb hi hj
          (sumGradientBound hi hj c ids)).changeCaps
            (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)))

/-- The constructed original-coordinate test supplies its own derivative cap.
The double-reindex pin is transported through the next angular derivative too. -/
def testAngularBound {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    AngularBound (blocks extent) i j
      (reindexQuaternionPolynomial swap (test extent link hl i j c))
      (4096*incidentAbs extent link c) (32768*incidentAbs extent link c) := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  let df := angularDerivative i j (reindexQuaternionPolynomial swap (incidentObservable extent link c))
  let P := sumGradientBound extent link hl hi hj c (incidentIds extent link)
  exact AngularBound.ofCarrier hb hi hj (reindex_supported swap _)
    (carrierOfPrefix (reindex_supported swap (reindexQuaternionPolynomial swap df)) P.value.support
      (reindex_twice_prefix swap df)) P

private theorem scoreCap_factor (w L : Q') :
    wardScoreCap w (4096*L) (32768*L) ≈ scoreCoefficient w * L :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.mul (.const 32768) (.var 2)))
      (.mul (.const 2) (.mul (.var 1) (.mul (.const 4096) (.var 2)))))
    (.mul (.add (.mul (.var 0) (.const 32768))
      (.mul (.const 2) (.mul (.var 1) (.const 4096)))) (.var 2))
    (by decide) (fun n => if n = 0 then incidentValueCap w else if n = 1 then incidentDerivativeCap w else L)

/-- Local original score cap, linear in the LOCAL absolute coefficient sum. -/
def gradientScoreInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    Interval (blocks extent) (originalScore w K extent link hl i j (test extent link hl i j c))
      (scoreCoefficient w * incidentAbs extent link c) :=
  (originalScoreInterval w K extent link hl hw0 hw1 hi hj (testAngularBound extent link hl hi hj c)).changeCap
    (scoreCap_factor w _)

variable (w : Q') (K : Nat)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- Six-face Cauchy--Schwarz converts the actual local score cost to local
coefficient squares. The normalization is the unchanged original partition. -/
theorem gradient_score_square_le (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    normalizedMoment (blocks extent) W
      (polyMul (originalScore w K extent link hl i j (test extent link hl i j c))
        (originalScore w K extent link hl i j (test extent link hl i j c)))
      (fullPartition_positive w K extent hw0 hw1 hK) ≤
      (6*(scoreCoefficient w*scoreCoefficient w))*listQSum (fun id => c id*c id) (incidentIds extent link) := by
  let C := scoreCoefficient w
  let L := incidentAbs extent link c
  let B := listQSum (fun id => c id*c id) (incidentIds extent link)
  have hcost := Interval.normalized_square_le
    (Interval.squareBound (gradientScoreInterval extent link hl hw0 hw1 K hi hj c))
    (headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ h => h))
    (fullPartition_positive w K extent hw0 hw1 hK)
  have hpin : (C*L)*(C*L) ≈ (C*C)*(L*L) :=
    poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun n => if n = 0 then C else L)
  have hlast : (C*C)*(Q'.ofNat 6*B) ≈ (6*(C*C))*B :=
    poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 0)) (.mul (.const 6) (.var 1)))
      (.mul (.mul (.const 6) (.mul (.var 0) (.var 0))) (.var 1)) (by decide)
      (fun n => if n = 0 then C else B)
  exact Q'.le_trans' _ _ _ hcost (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (incident_abs_sum_square_le_six extent link c) (SumOfSquares.q_mul_self_nonneg C))
      (Q'.le_of_eqv hlast)))

private theorem sum_le {Index : Type} (f g : Index → Q') : ∀ xs : List Index,
    (∀ x, x ∈ xs → f x ≤ g x) → listQSum f xs ≤ listQSum g xs
  | [], _ => Q'.le_refl' _
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (sum_le f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- At most four selected links charge a face. The only global observable
budget is the sum of its coefficient squares, not its squared global l1 norm. -/
theorem diagonal_cost_le (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q')
    (xs : List (PhysicalLink extent)) (hxs : xs.Nodup) :
    listQSum (fun l => normalizedMoment (blocks extent) W
      (polyMul (score w K extent i j (tests extent i j c) l) (score w K extent i j (tests extent i j c) l))
      (fullPartition_positive w K extent hw0 hw1 hK)) xs ≤
      (24*(scoreCoefficient w*scoreCoefficient w))*coefficientSquares extent c := by
  let C := scoreCoefficient w
  let b : PhysicalLink extent → Q' := fun l => listQSum (fun id => c id*c id) (incidentIds extent l.val)
  have ht := sum_le _ (fun l => (6*(C*C))*b l) xs
    (fun l _ => gradient_score_square_le extent l.val l.property w K hw0 hw1 hK hi hj c)
  have h0 : (0 : Q') ≤ 6*(C*C) := Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg C)
  have hlast : (6*(C*C))*(Q'.ofNat 4*coefficientSquares extent c) ≈ (24*(C*C))*coefficientSquares extent c :=
    poly_identity_of_normal_eq (.mul (.mul (.const 6) (.mul (.var 0) (.var 0))) (.mul (.const 4) (.var 1)))
      (.mul (.mul (.const 24) (.mul (.var 0) (.var 0))) (.var 1)) (by decide)
      (fun n => if n = 0 then C else coefficientSquares extent c)
  exact Q'.le_trans' _ _ _ ht
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left (6*(C*C)) b xs))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (coefficient_square_incidence_le_four extent c xs hxs) h0) (Q'.le_of_eqv hlast)))

/-- The actual whole-observable energy now has an explicit nome-dependent
coefficient-square cost. A useful energy LOWER bound is still missing. -/
theorem energy_squared_le_explicit_cost (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q')
    (xs : List (PhysicalLink extent)) (hxs : xs.Nodup) :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    let E := energySum w K extent i j c xs hW
    E*E ≤ normalizedVariance (blocks extent) W (observable extent c) hW *
      (Q'.ofNat 25 * ((24*(scoreCoefficient w*scoreCoefficient w))*coefficientSquares extent c)) := by
  let H := headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ h => h)
  let hW := fullPartition_positive w K extent hw0 hw1 hK
  exact Q'.le_trans' _ _ _ (energySum_squared_le_variance_cost w K extent hw0 hw1 hK hi hj c xs hxs)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (diagonal_cost_le extent w K hw0 hw1 hK hi hj c xs hxs) (by decide))
      (normalizedVariance_nonnegative H hW (observable_supported extent c)))

end YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost.faceGradientBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost.testAngularBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost.gradientScoreInterval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost.gradient_score_square_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost.diagonal_cost_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradientCost.energy_squared_le_explicit_cost
