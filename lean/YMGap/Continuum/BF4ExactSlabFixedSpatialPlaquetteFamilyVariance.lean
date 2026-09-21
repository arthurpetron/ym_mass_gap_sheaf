/-
# A signed plaquette-family floor on the SAME completed physical carrier

At radius zero the reflected chart square is the ordinary square of the
literal placed family. The selected-action affine coercivity therefore
applies to BOTH finite moments with their common original partition.
Their joint cutoff/boundary-time limits preserve the coefficient-square
floor, and the existing centering stream realizes it as the norm of an
actual vector in the existing completed vacuum complement.

The positive constant depends only on fixed strict nome, not spatial width,
face count, coefficients, cutoff or boundary time. Different widths have
different carriers; no spatial identification, changing-spacing survival,
transfer-energy comparison, continuum QFT or physical mass gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
import YMGap.Continuum.Z4TimeShiftedEmbeddedRegion
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing (faceSpan)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily (sourceSpan)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamily
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit zero physicalTime_zero)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation (timeShiftPlaquette_injective)
open YMGap.Continuum.Z4TimeShiftedEmbeddedRegion

local infix:50 " ≈ " => Q'.eqv

private theorem shifted_source (extent shift : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q') :
    sourceSpan extent (fun p => c (timeUnshiftPlaquette shift p)) (qs.map (timeShiftPlaquette shift)) =
      faceSpan extent (qs.map (fun p => (c p, timeShiftPlaquette shift p))) := by
  simp only [sourceSpan, List.map_map, Function.comp_def, timeUnshiftPlaquette_timeShiftPlaquette]

private theorem shifted_budget (shift : Nat) (c : Z4Plaq → Q') : ∀ qs : List Z4Plaq,
    listQSum (fun p => c (timeUnshiftPlaquette shift p)*c (timeUnshiftPlaquette shift p))
      (qs.map (timeShiftPlaquette shift)) ≈ listQSum (fun p => c p*c p) qs
  | [] => Q'.eqv_refl _
  | p::qs => by
      simp only [List.map_cons, listQSum, timeUnshiftPlaquette_timeShiftPlaquette]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (shifted_budget shift c qs)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "x" => familySpan width qs c hqs
local notation "J" => jointPairing hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width

attribute [local irreducible] chartScalar jointPairing chartJointLimit

/-- The literal chain law, not the surrounding cube action, supplies this
bound at EVERY regulator stage. Time placement preserves the signed budget. -/
theorem chart_variance_floor (hn : qs.Nodup) (stage t : Nat) :
    varianceFloor w hw0 * listQSum (fun p => c p*c p) qs ≤
      chartScalar hw0 hw1 width stage 0 x x t +
      -(chartScalar hw0 hw1 width stage 0 x (unit width) t *
        chartScalar hw0 hw1 width stage 0 x (unit width) t) := by
  let E := adjacentEvenExtent (width+t)
  let shift := (width+1)+t
  let qst := qs.map (timeShiftPlaquette shift)
  let ct := fun p => c (timeUnshiftPlaquette shift p)
  have hnt : qst.Nodup := CayleyPruferInjection.nodup_map_of_injOn _ qs hn
    (fun _ _ _ _ h => timeShiftPlaquette_injective shift h)
  have hpt : ∀ p, p ∈ qst → p ∈ boundaryCompleteSlabPlaquettes E := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact spatialFaces_shift_physical
      (by dsimp [E, adjacentEvenExtent, centralExtent]; omega)
      (by dsimp [E, shift, adjacentEvenExtent, centralExtent]; omega) (hqs q hq)
  have h := finiteValue_variance_floor hw0 hw1 E (chainIds E width (width+1) (t+t))
    (fun _ hi => chainIds_physical hi) (chainIds_nodup _ _ _ _) qst hnt hpt ct stage
  change varianceFloor w hw0 * listQSum (fun p => ct p*ct p) qst ≤ _ at h
  have hp := shifted_source E shift qs c
  change sourceSpan E ct qst = faceSpan E (placedTerms width t qs c) at hp
  rw [hp] at h
  have hm := chartScalar_mean_finiteValue hw0 hw1 width qs c hqs stage t
  have hs := chartScalar_square_finiteValue hw0 hw1 width qs c hqs stage t
  have hv := Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm) (Q'.mul_eqv_congr_left _ _ _ hm)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ (shifted_budget shift c qs)))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv hv))

/-- Both finite moments converge to the original joint pairing, with its
existing explicit regulator moduli; products pass through convergence. -/
theorem family_variance_converges :
    ConvergesTo (fun k => ofQ'
      (chartScalar hw0 hw1 width k 0 x x k +
        -(chartScalar hw0 hw1 width k 0 x (unit width) k *
          chartScalar hw0 hw1 width k 0 x (unit width) k)))
      (sub (J x x) (mul (J x (unit width)) (J x (unit width)))) := by
  have hx : BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius (x).val ≤ 0 := by
    rw [familySpan_radius]; exact Nat.le_refl 0
  have ha := ArctanTrigConvergesProof.convergesTo_of_equiv
    (chartJoint_diagonal_converges hw0 hw1 width 0 x x hx hx)
    (Equiv.symm (jointPairing_chart hw0 hw1 width 0 x x hx hx))
  have hb := ArctanTrigConvergesProof.convergesTo_of_equiv
    (chartJoint_diagonal_converges hw0 hw1 width 0 x (unit width) hx (Nat.le_refl 0))
    (Equiv.symm (jointPairing_chart hw0 hw1 width 0 x (unit width) hx (Nat.le_refl 0)))
  have h := TrigAddCReal.convergesTo_add ha (TrigAddCReal.convergesTo_neg
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hb hb))
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro k
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- The original connected moment retains the same coefficient floor after
BOTH cutoff and boundary-time limits, at every fixed spatial width. -/
theorem family_joint_variance_floor (hn : qs.Nodup) :
    leEv (ofQ' (varianceFloor w hw0 * listQSum (fun p => c p*c p) qs))
      (jointCenteredMoment hw0 hw1 width 0 x x) := by
  have h := leEv_of_convergesTo_le
    (CReal.convergesTo_const (ofQ' (varianceFloor w hw0 * listQSum (fun p => c p*c p) qs)))
    (family_variance_converges hw0 hw1 width qs c hqs)
    (fun k => leEv_ofQ'_of_approx_ge (fun _ => chart_variance_floor hw0 hw1 width qs c hqs hn k k))
  have he : Equiv (sub (J x x) (mul (J x (unit width)) (J x (unit width))))
      (jointCenteredMoment hw0 hw1 width 0 x x) := by
    unfold jointCenteredMoment
    rw [physicalTime_zero]
    exact Equiv_add (Equiv.refl _) (neg_congr
      (TrigSignedAdd.mul_congr_right (jointPairing_symm hw0 hw1 width x (unit width))))
  exact leEv_trans h (leEv_of_equiv he)

/-- Existing actual centering stream, in the existing completed complement. -/
def familyExcitation : UnitComplement hw0 hw1 width :=
  ⟨centeredVector hw0 hw1 width x, centeredVector_orthogonal hw0 hw1 width x⟩

/-- Norm coercivity on these actual completed vectors. No ordinary/reflected
norm identification was assumed; the radius-zero chart proved the join. -/
theorem familyExcitation_norm_floor (hn : qs.Nodup) :
    RCle (Quotient.mk crealSetoid (ofQ' (varianceFloor w hw0 * listQSum (fun p => c p*c p) qs)))
      (B (familyExcitation hw0 hw1 width qs c hqs).val (familyExcitation hw0 hw1 width qs c hqs).val) := by
  change RCle _ (B (centeredVector hw0 hw1 width x) (centeredVector hw0 hw1 width x))
  rw [centeredVector_pairing]
  exact family_joint_variance_floor hw0 hw1 width qs c hqs hn

/-- Positive coefficient budget excludes the actual completed zero. -/
theorem familyExcitation_ne_zero (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun p => c p*c p) qs) :
    (familyExcitation hw0 hw1 width qs c hqs).val ≠ jointEmbedSpan hw0 hw1 width (zero width) := by
  intro hz
  have h := familyExcitation_norm_floor hw0 hw1 width qs c hqs hn
  rw [hz, jointCompletedZero_norm] at h
  have hle : varianceFloor w hw0 * listQSum (fun p => c p*c p) qs ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (Q'.mul_pos (varianceFloor_positive hw0 hw1) hc) hle)

/-- SAME completed physical time and original connected correlator, for the
same family vector whose nonzero norm was just bounded. -/
theorem familyExcitation_correlator_pin (n : Nat) :
    B (familyExcitation hw0 hw1 width qs c hqs).val
      (jointCompletedTime hw0 hw1 width n (familyExcitation hw0 hw1 width qs c hqs).val) =
      Quotient.mk crealSetoid (jointCenteredMoment hw0 hw1 width n x x) :=
  centeredVector_time_pairing hw0 hw1 width n x x

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.chart_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.family_variance_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.family_joint_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.familyExcitation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.familyExcitation_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.familyExcitation_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.familyExcitation_correlator_pin
