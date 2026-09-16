/-
# One common sweep of the original finite chronological action

For any finite number of time layers, the original duplicate-free face
list becomes V0*K01*V1*...*K(n-1,n)*Vn under one common Haar-preserving
temporal gauge sweep. Signed spatial-face insertions are carried by the
same change of variables and remain unchanged. Each spatial heat occurs once.

This is still on the original ambient coordinates. Identification of the
whole arbitrary-length chain with the compact ordered-chain recurrence
requires its carrier placement; one-step pins alone do not prove that.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def originalChainAction (w : Q') (K extent width start steps : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (chainIds extent width start steps)

/-- Actual spatial/kinetic factors in chronological order on one ambient slab. -/
def ambientChain (w : Q') (K extent width start : Nat) : Nat → RatPoly
  | 0 => spatialHeat w K extent width start
  | steps+1 => polyMul (spatialHeat w K extent width start)
      (polyMul (kineticHeat w K extent width start)
        (ambientChain w K extent width (start+1) steps))

private theorem spatial_swept (w : Q') (K extent width time cut : Nat) :
    sweptProduct extent cut (heatFactors w K extent (spatialIds extent width time)) =
      spatialHeat w K extent width time := by
  rw [spatialFactors_swept_eq_zero extent cut _ ?_, heatFactors_zero]
  · rfl
  · intro f hf
    obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
    exact ((spatialIds_mem_iff extent width time id).mp hi).2.2.2.2.2

private theorem temporal_swept (w : Q') (K extent width time cut : Nat) (ht : time < cut) :
    sweptProduct extent cut (heatFactors w K extent (temporalIds extent width time)) =
      kineticHeat w K extent width time := by
  apply polynomialProduct_congr
  intro f hf
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
  have hi' := (temporalIds_mem_iff extent width time id).mp hi
  have hs : Swept cut (slabPlaquetteAt extent id) :=
    ⟨hi'.2.2.2.2.2, by rw [hi'.2.2.2.2.1]; exact ht⟩
  simp only [factor,sweptCharacter,if_pos hs]

private theorem swept_three (extent cut : Nat) (a b c : List FaceFactor) :
    RatPolyCoeffEqv (sweptProduct extent cut (a++(b++c)))
      (polyMul (sweptProduct extent cut a)
        (polyMul (sweptProduct extent cut b) (sweptProduct extent cut c))) :=
  (swept_append extent cut a (b++c)).trans ((swept_append extent cut b c).mul_left _)

/-- Exact factorization after one sweep; the statement also covers clipped windows. -/
theorem swept_chain_factorization (w : Q') (K extent width start steps cut : Nat)
    (hc : start+steps ≤ cut) :
    RatPolyCoeffEqv
      (sweptProduct extent cut (heatFactors w K extent (chainIds extent width start steps)))
      (ambientChain w K extent width start steps) := by
  induction steps generalizing start with
  | zero =>
      rw [chainIds,spatial_swept,ambientChain]
      exact .refl _
  | succ steps ih =>
      have h := swept_three extent cut
        (heatFactors w K extent (spatialIds extent width start))
        (heatFactors w K extent (temporalIds extent width start))
        (heatFactors w K extent (chainIds extent width (start+1) steps))
      rw [spatial_swept,temporal_swept w K extent width start cut (by omega)] at h
      have h' := h.trans ((ih (start+1) (by omega)).mul_left _ |>.mul_left _)
      simpa only [chainIds,heatFactors,List.map_append,ambientChain] using h'

/-- Original selected action and signed spatial observables share ONE
Haar-preserving change of variables before any polynomial iteration. -/
theorem original_chain_pairing (w : Q') (K extent width start steps : Nat)
    (probes : List FaceFactor)
    (hphys : ∀ f, f ∈ probes → f.1 ∈ boundaryCompleteSlabPlaquettes extent)
    (hsp : ∀ f, f ∈ probes → (dirsOf f.1.2).2 ≠ .x3) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (sweptProduct extent 0 probes) (originalChainAction w K extent width start steps)) ≈
      quaternionHaar (boundaryCompleteSlabLinks extent).length
        (polyMul (sweptProduct extent 0 probes) (ambientChain w K extent width start steps)) := by
  have ha : ∀ f, f ∈ heatFactors w K extent (chainIds extent width start steps) →
      f.1 ∈ boundaryCompleteSlabPlaquettes extent := by
    intro f hf
    obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
    exact slabPlaquetteAt_mem (chainIds_physical hi)
  have hs := sweep_product_haar extent (start+steps) probes
    (heatFactors w K extent (chainIds extent width start steps)) hphys ha
  rw [spatialFactors_swept_eq_zero extent (start+steps) probes hsp,heatFactors_zero] at hs
  exact Q'.eqv_trans _ _ _ hs
    (haar_of_coeff ((swept_chain_factorization w K extent width start steps (start+steps)
      (Nat.le_refl _)).mul_left _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction.originalChainAction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction.ambientChain
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction.swept_chain_factorization
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction.original_chain_pairing
