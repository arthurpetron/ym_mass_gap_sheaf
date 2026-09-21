/-
# The actual spatial plaquette is an eigenvector of the bare kinetic map

For an original spatial face whose four links are active, constructive list
selection exposes exactly those four heat factors without changing the full
active kernel.  The generic product-heat plaquette transmission then gives the
tested-Haar eigenvalue `w^12` for the literal fundamental face character.

This concerns only the bare kinetic map `P`.  It is not an eigenidentity for
the interacting transfer `P(V * -)`, and supplies no response or limiting
lower bound.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPlaquette
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
  (StrictSliceLink active_index_iff FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPlaquette
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Strict spatial padding proves the activity premise for every original
face at the base width; no analytic activity assumption is needed. -/
theorem plaquette_active_after_padding {base width : Nat} (hwidth : base < width)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) : FullyActive width face := by
  intro l hl
  have hb := face_link_mem_base hf hl
  have hw := face_link_mem_base (spatialFaces_mono (Nat.le_of_lt hwidth) hf) hl
  apply (active_index_iff width l hw).mpr
  rcases l with ⟨⟨x, y, z, t⟩, dir⟩
  have hs := (baseLinks_mem_iff base ((x, y, z, t), dir)).mp hb
  change dir ≠ .x3 ∧ x ≤ base ∧ y ≤ base ∧ z ≤ base ∧ t = 0 at hs
  simp only [StrictSliceLink, SliceLink]
  exact ⟨⟨hs.1, by omega, by omega, by omega, hs.2.2.2.2⟩,
    by omega, by omega, by omega⟩

/-- The literal fundamental character of an active original spatial face has
the exact four-link kinetic eigenvalue. -/
theorem plaquette_kinetic_eigen (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width)
    (w : Q') (K : Nat) (hK : 1 ≤ K) :
    SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width)
        (characterPolynomial (plaquette width face).scalar 1))
      (polySmul (qpow w 12) (characterPolynomial (plaquette width face).scalar 1)) := by
  let la : Z4Link := (face.1, (dirsOf face.2).1)
  let lb : Z4Link := (face.1, (dirsOf face.2).2)
  let lc : Z4Link := (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
  let ld : Z4Link := (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
  let a := (baseLinks width).idxOf la
  let b := (baseLinks width).idxOf ld
  let c := (baseLinks width).idxOf lc
  let d := (baseLinks width).idxOf lb
  have hla : la ∈ baseLinks width := face_link_mem_base hf (by simp [la, edgesOf])
  have hlb : lb ∈ baseLinks width := face_link_mem_base hf (by simp [lb, edgesOf])
  have hlc : lc ∈ baseLinks width := face_link_mem_base hf (by simp [lc, edgesOf])
  have hld : ld ∈ baseLinks width := face_link_mem_base hf (by simp [ld, edgesOf])
  have hlinks : (la ≠ lb ∧ (la ≠ lc ∧ la ≠ ld)) ∧
      ((lb ≠ lc ∧ lb ≠ ld) ∧ lc ≠ ld) := by
    simpa only [la, lb, lc, ld, edgesOf, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil, or_false, not_or, not_false_eq_true,
      and_true] using edgesOf_nodup face
  have hne {u v : Z4Link} (hu : u ∈ baseLinks width) (hv : v ∈ baseLinks width)
      (hne : u ≠ v) : (baseLinks width).idxOf u ≠ (baseLinks width).idxOf v :=
    fun he => hne (idxOf_injective_on_members hu hv he)
  have hab : a ≠ b := hne hla hld hlinks.1.2.2
  have hac : a ≠ c := hne hla hlc hlinks.1.2.1
  have had : a ≠ d := hne hla hlb hlinks.1.1
  have hbc : b ≠ c := hne hld hlc (Ne.symm hlinks.2.2)
  have hbd : b ≠ d := hne hld hlb (Ne.symm hlinks.2.1.2)
  have hcd : c ≠ d := hne hlc hlb (Ne.symm hlinks.2.1.1)
  have ha : a ∈ activeBlocks width := hactive la (by simp [la, edgesOf])
  have hb : b ∈ activeBlocks width := hactive ld (by simp [ld, edgesOf])
  have hc : c ∈ activeBlocks width := hactive lc (by simp [lc, edgesOf])
  have hd : d ∈ activeBlocks width := hactive lb (by simp [lb, edgesOf])
  let r0 := eraseIndex a (activeBlocks width)
  let r1 := eraseIndex b r0
  let r2 := eraseIndex c r1
  let r3 := eraseIndex d r2
  have hb0 : b ∈ r0 := by
    have hm := (select_perm a ha).mem_iff.mp hb
    exact (List.mem_cons.mp hm).resolve_left (fun h => hab h.symm)
  have hc0 : c ∈ r0 := by
    have hm := (select_perm a ha).mem_iff.mp hc
    exact (List.mem_cons.mp hm).resolve_left (fun h => hac h.symm)
  have hd0 : d ∈ r0 := by
    have hm := (select_perm a ha).mem_iff.mp hd
    exact (List.mem_cons.mp hm).resolve_left (fun h => had h.symm)
  have hc1 : c ∈ r1 := by
    have hm := (select_perm b hb0).mem_iff.mp hc0
    exact (List.mem_cons.mp hm).resolve_left (fun h => hbc h.symm)
  have hd1 : d ∈ r1 := by
    have hm := (select_perm b hb0).mem_iff.mp hd0
    exact (List.mem_cons.mp hm).resolve_left (fun h => hbd h.symm)
  have hd2 : d ∈ r2 := by
    have hm := (select_perm c hc1).mem_iff.mp hd1
    exact (List.mem_cons.mp hm).resolve_left (fun h => hcd h.symm)
  have hp : (activeBlocks width).Perm (a::b::c::d::r3) :=
    (select_perm a ha).trans (List.Perm.cons a
      ((select_perm b hb0).trans (List.Perm.cons b
        ((select_perm c hc1).trans (List.Perm.cons c (select_perm d hd2))))))
  have hgeneric := productMap_plaquette_of_perm (N width) w K hK a b c d
    (activeBlocks width) r3 (activeBlocks_nodup width) (activeBlocks_lt width) hp
  have hsource : RatPolyCoeffEqv
      (characterPolynomial (plaquette width face).scalar 1)
      (SU2QuaternionFundamentalPlaquetteTube.plaquette a b c d) := by
    have h := characterPolynomial_coeffEqv (plaquette_fourWord hf).scalar 1
    simpa only [a, b, c, d, la, lb, lc, ld,
      SU2QuaternionFundamentalPlaquetteTube.plaquette,
      SU2QuaternionOrientedWordSelection.word, orientedCoordinateQuaternion] using h
  exact (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier (productMap_congr (N width) w K
        (activeBlocks width) hsource))).trans
    (hgeneric.trans (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier (hsource.smul (qpow w 12)).symm)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic.plaquette_kinetic_eigen
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic.plaquette_active_after_padding
