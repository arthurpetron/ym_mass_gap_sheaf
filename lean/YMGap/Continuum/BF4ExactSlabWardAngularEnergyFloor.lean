/-
# Six-direction Ward energy retains a positive local heat comparison

Two applications of the actual six-face heat floor pay for BOTH incident
factors in R*A^2*(D f)^2. The head-linear Haar identity then gives a lower
bound by the square of the same observable in the retained background.
Constants depend on nome, not cutoff or extent at the stated late cutoff.
This is not the OS transfer energy and is not a physical spectral gap.
-/

import YMGap.Continuum.QuaternionHaarLinearAngularEnergy
import YMGap.Continuum.BF4ExactSlabWardGradientEnergy
import YMGap.Continuum.BF4ExactSlabLocalStarComparison

namespace YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalHaarWard
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabWardGradientEnergy
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)
local notation "swap" => linkHeadSwap extent link hl
local notation "A" => reindexQuaternionPolynomial swap (incidentHeat w K extent link)
local notation "R" => reindexQuaternionPolynomial swap (complementHeat w K extent link)

include hw0 hw1 hK

/-- The old actual six-face comparison transported to the SAME head frame. -/
theorem head_incident_bounds {p : RatPoly} (hp : SupportedQuaternionBlocks (blocks extent) p)
    (P : Certificate (blocks extent) p) :
    lowerFactor w * quaternionHaar (blocks extent) p ≤
      quaternionHaar (blocks extent) (polyMul p A) ∧
    quaternionHaar (blocks extent) (polyMul p A) ≤
      upperFactor w * quaternionHaar (blocks extent) p := by
  have h := atMostSix_bounds hw0 hw1 K extent hK (reindex_certificate swap hp P)
    (incidentIds extent link) (fun _ h => incidentIds_physical h) (incidentIds_length_le_six extent link)
  have hm := quaternionHaar_reindex swap p hp
  have hx := reindex_pair swap p (incidentHeat w K extent link) hp (incidentHeat_supported w K extent link)
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hm))
      (Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv hx)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hx)
      (Q'.le_trans' _ _ _ h.2 (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hm)))⟩

/-- The additional incident factor in the Ward score is explicitly paid twice. -/
theorem energyNumerator_floor {i j : Nat} (hi : i < 4) (hj : j < 4) (f : RatPoly) :
    (lowerFactor w * lowerFactor w) * quaternionHaar (blocks extent)
      (polyMul R (polyMul
        (angularDerivative i j (reindexQuaternionPolynomial swap f))
        (angularDerivative i j (reindexQuaternionPolynomial swap f)))) ≤
      energyNumerator w K extent link hl i j f := by
  let df := angularDerivative i j (reindexQuaternionPolynomial swap f)
  let p := polyMul R (polyMul df df)
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have hdf := angularDerivative_supported hb hi hj (reindex_supported swap f)
  have hp : SupportedQuaternionBlocks (blocks extent) p :=
    supported_polyMul (reindex_supported swap _) (supported_polyMul hdf hdf)
  have hA := reindex_certificate swap (incidentHeat_supported w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (incidentIds extent link)
      (fun _ h => incidentIds_physical h))
  have hR := reindex_certificate swap (complementHeat_supported w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ h => complementIds_physical h))
  have P : Certificate (blocks extent) p := hR.mul (.square df hdf)
  have h1 := (head_incident_bounds hw0 hw1 K extent hK link hl hp P).1
  have h2 := (head_incident_bounds hw0 hw1 K extent hK link hl
    (supported_polyMul hp (reindex_supported swap _)) (P.mul hA)).1
  have he : RatPolyCoeffEqv (polyMul (polyMul p A) A)
      (polyMul R (polyMul A (polyMul A (polyMul df df)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1)) (.var 1))
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.mul (.var 2) (.var 2)))))
      (by decide) (fun | 0 => R | 1 => A | _ => df)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h1
      (Q'.le_of_lt (lowerFactor_positive hw0 hw1)))
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (haar_of_coeff he))))

/-- The exact summed energy dominates the retained square of a head-linear
original observable. The degree is structural, not an assumed norm bound. -/
theorem linear_energy_floor (f : RatPoly)
    (hd : HasQuaternionBlockDegree 0 1 (reindexQuaternionPolynomial swap f)) :
    (3*(lowerFactor w*lowerFactor w)) * quaternionHaar (blocks extent)
      (polyMul R (polyMul (reindexQuaternionPolynomial swap f) (reindexQuaternionPolynomial swap f))) ≤
      sixValue (fun i j => energyNumerator w K extent link hl i j f) := by
  let fp := reindexQuaternionPolynomial swap f
  let m := fun i j => quaternionHaar (blocks extent)
    (polyMul R (polyMul (angularDerivative i j fp) (angularDerivative i j fp)))
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have hid : sixValue m ≈ 3 * quaternionHaar (blocks extent) (polyMul R (polyMul fp fp)) := by
    have ht := retained_linear_energy (blocks extent-1) R fp
      (complementHeat_headIndependent w K extent link hl) hd
    rw [Nat.sub_add_cancel hb] at ht
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_six (blocks extent) R _)) ht
  have hsum := sixValue_mono (fun i j => (lowerFactor w*lowerFactor w)*m i j)
    (fun i j => energyNumerator w K extent link hl i j f)
    (fun _ _ hi hj => energyNumerator_floor hw0 hw1 K extent hK link hl hi hj f)
  have halg : (3*(lowerFactor w*lowerFactor w)) * quaternionHaar (blocks extent) (polyMul R (polyMul fp fp)) ≈
      (lowerFactor w*lowerFactor w) * (3 * quaternionHaar (blocks extent) (polyMul R (polyMul fp fp))) :=
    poly_identity_of_normal_eq (.mul (.mul (.const 3) (.mul (.var 0) (.var 0))) (.var 1))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.const 3) (.var 1))) (by decide)
      (fun n => if n = 0 then lowerFactor w else quaternionHaar (blocks extent) (polyMul R (polyMul fp fp)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halg)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hid))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (sixValue_mul_left _ m)) hsum))

/-- Restore the original full action on the square side too. The sole
comparison cost is the selected link's at-most-six heat factors. -/
theorem linear_full_energy_floor (f : RatPoly)
    (hf : SupportedQuaternionBlocks (blocks extent) f)
    (hd : HasQuaternionBlockDegree 0 1 (reindexQuaternionPolynomial swap f)) :
    (3*(lowerFactor w*lowerFactor w)) * quaternionHaar (blocks extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
        (polyMul f f)) ≤
      upperFactor w * sixValue (fun i j => energyNumerator w K extent link hl i j f) := by
  let fp := reindexQuaternionPolynomial swap f
  let p := polyMul R (polyMul fp fp)
  let z := quaternionHaar (blocks extent) p
  let a := 3*(lowerFactor w*lowerFactor w)
  have hp : SupportedQuaternionBlocks (blocks extent) p :=
    supported_polyMul (reindex_supported swap _) (supported_polyMul (reindex_supported swap _) (reindex_supported swap _))
  have P : Certificate (blocks extent) p :=
    (reindex_certificate swap (complementHeat_supported w K extent link)
      (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
        (fun _ h => complementIds_physical h))).mul (.square fp (reindex_supported swap f))
  have hcap := (head_incident_bounds hw0 hw1 K extent hK link hl hp P).2
  have hpin : quaternionHaar (blocks extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)) (polyMul f f)) ≈
      quaternionHaar (blocks extent) (polyMul p A) := by
    have h := fullAction_pair_pin w K extent link hl (polyMul f f) (supported_polyMul hf hf)
    rw [reindexQuaternionPolynomial_mul] at h
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ h (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
        (by decide) (fun | 0 => R | 1 => A | _ => fp))))
  have hfloor := linear_energy_floor hw0 hw1 K extent hK link hl f hd
  have hcomm : a*(upperFactor w*z) ≈ upperFactor w*(a*z) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => a | 1 => upperFactor w | _ => z)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left a _ _ hpin))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hcap
      (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg (lowerFactor w))))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor (Q'.le_of_lt (upperFactor_positive hw0)))))

end YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor

#print axioms YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor.head_incident_bounds
#print axioms YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor.energyNumerator_floor
#print axioms YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor.linear_energy_floor
#print axioms YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor.linear_full_energy_floor
