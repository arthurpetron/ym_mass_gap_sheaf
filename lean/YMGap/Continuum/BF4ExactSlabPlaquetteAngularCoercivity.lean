/-
# An actual positive coefficient floor for six-direction plaquette Ward energy

The incident signed source is head-linear and is EXACTLY the existing
physical plaquette sourceSpan. The proved angular identity and local heat
comparison therefore let its full-action square coercivity bound the actual
Ward energy of the WHOLE signed plaquette observable at this link.

All constants are explicit and positive at fixed strict nome, independent of
extent and late cutoff. The original partition is retained on both sides.
No covering-link sum, variance floor, OS transfer bound or continuum claim is
included here. In particular angular energy is not OS transfer energy.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear
import YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor

namespace YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabWardGradientEnergy
open YMGap.Continuum.BF4ExactSlabWardFamilyCost
open YMGap.Continuum.BF4ExactSlabWardAngularEnergyFloor
open YMGap.Continuum.BF4ExactSlabPlaquetteGradient
open YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- Explicit numerator-side constant; positive at each strict nome. -/
def floorCoefficient (w : Q') : Q' :=
  (3*(lowerFactor w*lowerFactor w))*BF4ExactSlabPlaquetteBoundaryWindow.lower w

/-- Explicit comparison cost, with no volume or cutoff in its definition. -/
def costCoefficient (w : Q') : Q' :=
  (600*BF4ExactSlabPlaquetteBoundaryWindow.upper w)*upperFactor w

theorem floorCoefficient_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < floorCoefficient w :=
  Q'.mul_pos (Q'.mul_pos (by decide)
    (Q'.mul_pos (lowerFactor_positive hw0 hw1) (lowerFactor_positive hw0 hw1)))
    (BF4ExactSlabPlaquetteBoundaryWindow.lower_positive hw0 hw1)

theorem costCoefficient_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < costCoefficient w :=
  Q'.mul_pos (Q'.mul_pos (by decide) (BF4ExactSlabPlaquetteBoundaryWindow.upper_positive hw0))
    (upperFactor_positive hw0)

variable (w : Q') (K extent : Nat) (link : Z4Link)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- Reuse the existing ORIGINAL full-square coercivity on the actual incident
source, rather than assume a new gradient-Gram bound. -/
theorem incident_source_coercivity (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) (c : Nat → Q') :
    BF4ExactSlabPlaquetteBoundaryWindow.lower w * quaternionHaar (blocks extent) W *
      listQSum (fun id => c id*c id) (incidentIds extent link) ≤
      (600*BF4ExactSlabPlaquetteBoundaryWindow.upper w) *
        quaternionHaar (blocks extent) (polyMul W
          (polyMul (incidentObservable extent link c) (incidentObservable extent link c))) := by
  have h := family_partition_coercivity hw0 hw1 K extent hK (slabPhysicalFaceEdges extent)
    (fun _ h => h) (CayleyParentInj.range_nodup _)
    (incidentPlaquettes extent link) (incidentPlaquettes_nodup extent link)
    (fun _ h => incidentPlaquettes_physical extent link h) (incidentCoefficient extent c)
  have hs := sourceSpan_incident extent link c
  have hp : sourceEnergy w K extent (slabPhysicalFaceEdges extent)
      (incidentCoefficient extent c) (incidentPlaquettes extent link) ≈
      quaternionHaar (blocks extent) (polyMul W
        (polyMul (incidentObservable extent link c) (incidentObservable extent link c))) :=
    haar_of_coeff ((hs.mul hs).mul_left W)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _
    (coefficientSquares_incident extent link c)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hp)))

/-- At the selected link, the WHOLE observable has the same derivative energy
as its incident part; the action and normalization have not changed. -/
theorem whole_energy_incident (hl : link ∈ boundaryCompleteSlabLinks extent)
    {i j : Nat} (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    energyNumerator w K extent link hl i j (observable extent c) ≈
      energyNumerator w K extent link hl i j (incidentObservable extent link c) := by
  have h := observable_derivative_incident extent link hl hi hj c
  exact haar_of_coeff ((((h.mul h).mul_left _).mul_left _).mul_left _)

/-- A positive, cutoff/extent-independent-at-fixed-nome floor on the ACTUAL
six-direction energy of the whole signed observable, localized at one link.
The coefficient budget includes exactly that link's incident faces. -/
theorem incident_energy_coercivity (hl : link ∈ boundaryCompleteSlabLinks extent)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w ≤ K) (c : Nat → Q') :
    floorCoefficient w * quaternionHaar (blocks extent) W *
      listQSum (fun id => c id*c id) (incidentIds extent link) ≤
      costCoefficient w * sixValue (fun i j => energyNumerator w K extent link hl i j (observable extent c)) := by
  let a := 3*(lowerFactor w*lowerFactor w)
  let b := 600*BF4ExactSlabPlaquetteBoundaryWindow.upper w
  let L := BF4ExactSlabPlaquetteBoundaryWindow.lower w
  let Z := quaternionHaar (blocks extent) W
  let C := listQSum (fun id => c id*c id) (incidentIds extent link)
  have hsource := Q'.mul_le_mul_of_nonneg_left _ _ a
    (incident_source_coercivity w K extent link hw0 hw1 hK c)
    (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg (lowerFactor w)))
  have henergy := Q'.mul_le_mul_of_nonneg_left _ _ b
    (linear_full_energy_floor hw0 hw1 K extent hK link hl (incidentObservable extent link c)
      (incidentObservable_supported extent link c) (incidentObservable_head_degree_one extent link hl c))
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt (BF4ExactSlabPlaquetteBoundaryWindow.upper_positive hw0)))
  have hpin := sixValue_congr _ _ (fun _ _ hi hj => whole_energy_incident w K extent link hl hi hj c)
  have hstart : (a*L)*Z*C ≈ a*(L*Z*C) :=
    poly_identity_of_normal_eq (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (by decide)
      (fun | 0 => a | 1 => L | 2 => Z | _ => C)
  have hcomm (x : Q') : a*(b*x) ≈ b*(a*x) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => a | 1 => b | _ => x)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstart)
    (Q'.le_trans' _ _ _ hsource (Q'.le_trans' _ _ _ (Q'.le_of_eqv (hcomm _))
      (Q'.le_trans' _ _ _ henergy
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
          (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hpin))))))

/-- The SAME original positive partition cancels once, leaving the actual
normalized six-direction energies. No whole-volume partition floor is spent. -/
theorem incident_normalized_energy_coercivity (hl : link ∈ boundaryCompleteSlabLinks extent)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w ≤ K) (c : Nat → Q') :
    let hW := fullPartition_positive w K extent hw0 hw1 hK
    floorCoefficient w * listQSum (fun id => c id*c id) (incidentIds extent link) ≤
      costCoefficient w * sixValue (fun i j => linkEnergy w K extent link hl i j (observable extent c) hW) := by
  let hW := fullPartition_positive w K extent hw0 hw1 hK
  let Z := quaternionHaar (blocks extent) W
  let r := Q'.recipPos Z hW
  let a := floorCoefficient w
  let C := listQSum (fun id => c id*c id) (incidentIds extent link)
  have hc : (a*Z*C)*r ≈ a*C :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => a | 1 => Z | 2 => C | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hW))
        (Q'.mul_one_eqv _))
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ r
    (incident_energy_coercivity w K extent link hl hw0 hw1 hK c)
    (Q'.le_of_lt (Q'.recipPos_pos Z hW))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (sixValue_mul_right r _)))))

end YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity.floorCoefficient_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity.costCoefficient_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity.incident_source_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity.whole_energy_incident
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity.incident_energy_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularCoercivity.incident_normalized_energy_coercivity
