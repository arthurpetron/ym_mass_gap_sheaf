/-
# The actual shifted probe and full action under one temporal sweep

The two centered endpoint observables are the pre-existing original lower
and upper enlargements. At every margin, their full finite-action integral
equals the same insertion against the swept action. No heat term is dropped.
All twelve selected tube sides reduce to their literal spatial-link pairs.

This is a raw fixed-cutoff moment identity, not yet a lower bound, a pin of
the compact sixteen-block tube product, or a limit/certificate evaluation.
-/

import YMGap.Continuum.BF4ExactSlabTemporalSweep
import YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

def centeredWeights (c : Q') : List (Nat × Q') := [(1,1),(0,-c)]

/-- Actual original endpoint insertions; no independently chosen probe. -/
def insertProbe (margin : Nat) (c d : Q') (background : RatPoly) : RatPoly :=
  polyMul (polyAdd (upper (enlarge margin shiftedProbe)) (polySmul (-c) polyOne))
    (polyMul (polyAdd (lower (enlarge margin shiftedProbe)) (polySmul (-d) polyOne)) background)

def probeFactors (w : Q') (K margin : Nat) (c d : Q') : List FaceFactor :=
  (sliceFace margin 3, centeredWeights c) :: (sliceFace margin 0, centeredWeights d) ::
    actionFactors w K (responseExtent margin)

theorem probeFactors_physical (w : Q') (K margin : Nat) (c d : Q') :
    ∀ f, f ∈ probeFactors w K margin c d → f.1 ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slice_physical margin ⟨3,by decide⟩
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact slice_physical margin ⟨0,by decide⟩
    · exact actionFactors_physical w K _ f hf

theorem slice_not_swept (margin time cut : Nat) : ¬ Swept cut (sliceFace margin time) := by
  intro h
  have he : Dir4.x1 = .x3 := h.1
  cases he

private theorem centered_slice_factor (margin time cut : Nat) (c : Q') :
    RatPolyCoeffEqv
      (factor (sweptCharacter (responseExtent margin) cut) (sliceFace margin time, centeredWeights c))
      (polyAdd (characterPolynomial (correctedSlabPlaquettePolynomial (responseExtent margin)
        (sliceFace margin time)).scalar 1) (polySmul (-c) polyOne)) := by
  simp only [factor, centeredWeights, finitePolySum, sweptCharacter,
    if_neg (slice_not_swept margin time cut)]
  change RatPolyCoeffEqv (polyAdd (polySmul 1 _) (polySmul (-c) polyOne)) _
  exact (RatPolyCoeffEqv.one_smul _).add (RatPolyCoeffEqv.refl _)

private theorem swept_cons (extent cut : Nat) (f : FaceFactor) (fs : List FaceFactor) :
    sweptProduct extent cut (f::fs) =
      polyMul (factor (sweptCharacter extent cut) f) (sweptProduct extent cut fs) := rfl

/-- Both endpoint factors retain their ORIGINAL meanings at every sweep stage. -/
theorem probe_product_pin (w : Q') (K margin cut : Nat) (c d : Q') :
    RatPolyCoeffEqv (sweptProduct (responseExtent margin) cut (probeFactors w K margin c d))
      (insertProbe margin c d (sweptProduct (responseExtent margin) cut
        (actionFactors w K (responseExtent margin)))) := by
  unfold insertProbe probeFactors
  rw [swept_cons, swept_cons]
  rw [lower_shifted_probe_pin, upper_shifted_probe_pin]
  apply RatPolyCoeffEqv.mul
  · exact centered_slice_factor margin 3 cut c
  · apply RatPolyCoeffEqv.mul
    · exact centered_slice_factor margin 0 cut d
    · exact RatPolyCoeffEqv.refl _

/-- Full original raw moment, arbitrary cutoff, margin and rational centers. -/
theorem shifted_probe_action_sweep (w : Q') (K margin stop : Nat) (c d : Q') :
    quaternionHaar (blocks margin) (insertProbe margin c d (fullHeatProduct w K (1+margin))) ≈
      quaternionHaar (blocks margin) (insertProbe margin c d
        (sweptProduct (responseExtent margin) stop (actionFactors w K (responseExtent margin)))) := by
  have hzero := probe_product_pin w K margin 0 c d
  change RatPolyCoeffEqv _ (insertProbe margin c d
    (sweptProduct (centralExtent (1+margin)) 0 (actionFactors w K (centralExtent (1+margin))))) at hzero
  rw [full_action_zero] at hzero
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_carrier (RatPolyCoeffEqv.haarCarrier hzero)))
    (Q'.eqv_trans _ _ _ (sweep_haar _ stop _ (probeFactors_physical w K margin c d))
      (haar_of_carrier (RatPolyCoeffEqv.haarCarrier (probe_product_pin w K margin stop c d))))

theorem tube_sides_swept (margin : Nat) :
    ∀ face, face ∈ tubeSides margin → Swept (margin+3) face := by
  have hc : baseSides.all (fun f => decide ((dirsOf f.2).2 = Dir4.x3 ∧ f.1.2.2.2 < 3)) = true := by decide +kernel
  intro face hf
  obtain ⟨f,hbase,rfl⟩ := List.mem_map.mp hf
  have h := of_decide_eq_true (List.all_eq_true.mp hc f hbase)
  refine ⟨h.1, ?_⟩
  change f.1.2.2.2 + margin < margin+3
  have ht := h.2
  omega

/-- All twelve side characters are simultaneously their actual relative pairs. -/
theorem tube_side_character_pin (margin : Nat) (face : Z4Plaq) (hf : face ∈ tubeSides margin) (spin : Nat) :
    sweptCharacter (responseExtent margin) (margin+3) face spin = relativeCharacter (responseExtent margin) face spin :=
  if_pos (tube_sides_swept margin face hf)

end YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.centeredWeights
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.insertProbe
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.probeFactors
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.probeFactors_physical
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.slice_not_swept
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.probe_product_pin
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.shifted_probe_action_sweep
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.tube_sides_swept
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep.tube_side_character_pin
