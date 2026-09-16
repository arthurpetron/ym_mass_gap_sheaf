/-
# Original two-layer Haar gluing at fixed spatial width

One common temporal sweep is applied to the original action and the signed
spatial endpoint insertions. Its five physical face families become
V0 * K01 * V1 * K12 * V2. Only the middle spatial links are then integrated;
V1 occurs ONCE and both endpoint weights stay outside that integral.

This is the original SELECTED window action, not the full ambient action
with its surrounding interactions dropped. It is a finite pairing identity
and does not construct a
stationary vacuum, identify powers of an operator on one OS carrier, pass a
cutoff-dependent boundary function through a limit, or prove a spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
import YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
import YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (integrateQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

def spatialHeat (w : Q') (K extent width time : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (spatialIds extent width time)

/-- Every temporal face retains its full finite relative-character heat sum. -/
def kineticHeat (w : Q') (K extent width time : Nat) : RatPoly :=
  product (relativeCharacter extent) (heatFactors w K extent (temporalIds extent width time))

def originalAction (w : Q') (K extent width start : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (windowIds extent width start)

def middleIntegrand (w : Q') (K extent width start : Nat) : RatPoly :=
  polyMul (kineticHeat w K extent width start)
    (polyMul (spatialHeat w K extent width (start+1))
      (kineticHeat w K extent width (start+1)))

/-- Stable original block coordinates; unrelated middle-slice blocks integrate
the normalized constant, rather than requiring a recoding of the carrier. -/
def middleSchedule (extent start : Nat) : List Nat :=
  (List.range (blocks extent)).filter fun b => decide
    ((correctedSlabLinkAt extent b).2 ≠ .x3 ∧
      (correctedSlabLinkAt extent b).1.2.2.2 = start+1)

def gluedMiddle (w : Q') (K extent width start : Nat) : RatPoly :=
  integrateQuaternionBlocks (middleSchedule extent start)
    (middleIntegrand w K extent width start)

private def sweptHeat (w : Q') (K extent cut : Nat) (ids : List Nat) : RatPoly :=
  sweptProduct extent cut (heatFactors w K extent ids)

private theorem sweptHeat_append (w : Q') (K extent cut : Nat) (xs ys : List Nat) :
    RatPolyCoeffEqv (sweptHeat w K extent cut (xs++ys))
      (polyMul (sweptHeat w K extent cut xs) (sweptHeat w K extent cut ys)) := by
  simpa only [sweptHeat, heatFactors, List.map_append] using
    swept_append extent cut (heatFactors w K extent xs) (heatFactors w K extent ys)

private theorem sweptHeat_perm (w : Q') (K extent cut : Nat) {xs ys : List Nat}
    (h : xs.Perm ys) : RatPolyCoeffEqv (sweptHeat w K extent cut xs) (sweptHeat w K extent cut ys) :=
  polynomialProduct_perm _ (h.map (fun id => (slabPlaquetteAt extent id, heatWeights w K)))

private theorem sweptHeat_five (w : Q') (K extent cut : Nat) (a b c d e : List Nat) :
    RatPolyCoeffEqv (sweptHeat w K extent cut (a++(b++(c++(d++e)))))
      (polyMul (sweptHeat w K extent cut a)
        (polyMul (sweptHeat w K extent cut b)
          (polyMul (sweptHeat w K extent cut c)
            (polyMul (sweptHeat w K extent cut d) (sweptHeat w K extent cut e))))) :=
  (sweptHeat_append w K extent cut a (b++(c++(d++e)))).trans
    (((sweptHeat_append w K extent cut b (c++(d++e))).trans
      (((sweptHeat_append w K extent cut c (d++e)).trans
        ((sweptHeat_append w K extent cut d e).mul_left _)).mul_left _)).mul_left _)

private theorem heatFactors_physical {w : Q'} {K extent : Nat} {ids : List Nat}
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    ∀ f, f ∈ heatFactors w K extent ids → f.1 ∈ boundaryCompleteSlabPlaquettes extent := by
  intro f hf
  obtain ⟨id,hid,rfl⟩ := List.mem_map.mp hf
  exact slabPlaquetteAt_mem (hi id hid)

private theorem spatialFactors_spatial (w : Q') (K extent width time : Nat) :
    ∀ f, f ∈ heatFactors w K extent (spatialIds extent width time) →
      (dirsOf f.1.2).2 ≠ .x3 := by
  intro f hf
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
  exact ((spatialIds_mem_iff extent width time id).mp hi).2.2.2.2.2

private theorem spatialHeat_swept (w : Q') (K extent width time cut : Nat) :
    sweptHeat w K extent cut (spatialIds extent width time) = spatialHeat w K extent width time := by
  rw [sweptHeat, spatialFactors_swept_eq_zero extent cut _
    (spatialFactors_spatial w K extent width time), heatFactors_zero]
  rfl

private theorem kineticHeat_swept (w : Q') (K extent width time cut : Nat) (ht : time < cut) :
    sweptHeat w K extent cut (temporalIds extent width time) = kineticHeat w K extent width time := by
  apply polynomialProduct_congr
  intro f hf
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
  have hi' := (temporalIds_mem_iff extent width time id).mp hi
  have hs : Swept cut (slabPlaquetteAt extent id) :=
    ⟨hi'.2.2.2.2.2, by rw [hi'.2.2.2.2.1]; exact ht⟩
  simp only [factor, sweptCharacter, if_pos hs]

set_option maxHeartbeats 1000000 in
/-- The common sweep gives two literal kinetic layers and exactly three
spatial weights. In particular the middle spatial heat is not squared. -/
theorem swept_window_factorization (w : Q') (K extent width start : Nat) :
    RatPolyCoeffEqv
      (sweptProduct extent (start+2) (heatFactors w K extent (windowIds extent width start)))
      (polyMul (spatialHeat w K extent width start)
        (polyMul (kineticHeat w K extent width start)
          (polyMul (spatialHeat w K extent width (start+1))
            (polyMul (kineticHeat w K extent width (start+1))
              (spatialHeat w K extent width (start+2)))))) := by
  have hp := sweptHeat_perm w K extent (start+2) (twoLayerIds_perm_window extent width start).symm
  simp only [twoLayerIds, List.append_assoc] at hp
  have h := hp.trans (sweptHeat_five w K extent (start+2)
    (spatialIds extent width start) (temporalIds extent width start)
    (spatialIds extent width (start+1)) (temporalIds extent width (start+1))
    (spatialIds extent width (start+2)))
  simpa only [spatialHeat_swept,
    kineticHeat_swept w K extent width start (start+2) (by omega),
    kineticHeat_swept w K extent width (start+1) (start+2) (by omega)] using h

private theorem spatialHeat_endpoint_local (w : Q') (K extent width start time : Nat)
    (ht : time = start ∨ time = start+2) :
    BlockLocal (blocks extent) (fun b => EndpointLink start (correctedSlabLinkAt extent b))
      (spatialHeat w K extent width time) := by
  rw [spatialHeat, ← heatFactors_zero]
  apply endpointFactors_local extent start _ (spatialFactors_spatial w K extent width time)
  intro f hf
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
  rw [((spatialIds_mem_iff extent width time id).mp hi).2.2.2.2.1]
  exact ht

/-- Endpoint insertions and endpoint spatial weights are independent of
every integrated block; ALL middle-dependent action factors stay inside. -/
theorem middle_haar_gluing (w : Q') (K extent width start : Nat) (p : RatPoly)
    (hp : BlockLocal (blocks extent)
      (fun b => EndpointLink start (correctedSlabLinkAt extent b)) p) :
    quaternionHaar (blocks extent)
      (polyMul (polyMul p (polyMul (spatialHeat w K extent width start)
        (spatialHeat w K extent width (start+2)))) (middleIntegrand w K extent width start)) ≈
    quaternionHaar (blocks extent)
      (polyMul (polyMul p (polyMul (spatialHeat w K extent width start)
        (spatialHeat w K extent width (start+2)))) (gluedMiddle w K extent width start)) := by
  apply quaternionHaar_polyMul_eq_after_integratingBlocks_of_local
    (hp.mul ((spatialHeat_endpoint_local w K extent width start start (Or.inl rfl)).mul
      (spatialHeat_endpoint_local w K extent width start (start+2) (Or.inr rfl))))
  intro b hb
  have hm := List.mem_filter.mp hb
  have ht := (of_decide_eq_true hm.2).2
  refine ⟨List.mem_range.mp hm.1, ?_⟩
  intro he
  rcases he.2 with he | he <;> omega

/-- SAME original finite action and signed endpoint face observables, after
one common gauge change and genuine middle-slice Haar integration. The
geometric containment guards are recorded by `windowFaces_mem_iff`; the
algebra also holds for clipped windows. No positivity or gap is assumed. -/
theorem original_twoLayer_gluing (w : Q') (K extent width start : Nat) (probes : List FaceFactor)
    (hphys : ∀ f, f ∈ probes → f.1 ∈ boundaryCompleteSlabPlaquettes extent)
    (hsp : ∀ f, f ∈ probes → (dirsOf f.1.2).2 ≠ .x3)
    (ht : ∀ f, f ∈ probes → f.1.1.2.2.2 = start ∨ f.1.1.2.2.2 = start+2) :
    quaternionHaar (blocks extent)
      (polyMul (sweptProduct extent 0 probes) (originalAction w K extent width start)) ≈
    quaternionHaar (blocks extent)
      (polyMul (polyMul (sweptProduct extent 0 probes)
        (polyMul (spatialHeat w K extent width start) (spatialHeat w K extent width (start+2))))
        (gluedMiddle w K extent width start)) := by
  have hs := sweep_product_haar extent (start+2) probes
    (heatFactors w K extent (windowIds extent width start)) hphys
    (heatFactors_physical (fun _ hi => windowIds_physical hi))
  rw [spatialFactors_swept_eq_zero extent (start+2) probes hsp, heatFactors_zero] at hs
  have hf := haar_of_coeff_eqv (blocks extent)
    ((swept_window_factorization w K extent width start).mul_left (sweptProduct extent 0 probes))
  have hr := haar_of_coeff_eqv (blocks extent) (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.mul (.var 4) (.var 5))))))
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.mul (.var 3) (.var 4))))
    (by decide)
    (fun | 0 => sweptProduct extent 0 probes | 1 => spatialHeat w K extent width start
         | 2 => kineticHeat w K extent width start | 3 => spatialHeat w K extent width (start+1)
         | 4 => kineticHeat w K extent width (start+1) | _ => spatialHeat w K extent width (start+2)))
  exact Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _ hf (Q'.eqv_trans _ _ _ hr
    (middle_haar_gluing w K extent width start _ (endpointFactors_local extent start probes hsp ht))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.spatialHeat
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.kineticHeat
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.originalAction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.middleIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.middleSchedule
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.gluedMiddle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.swept_window_factorization
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.middle_haar_gluing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing.original_twoLayer_gluing
