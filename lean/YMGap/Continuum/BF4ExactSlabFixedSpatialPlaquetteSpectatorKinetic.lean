/-
# Spectator-modulated transmission for the original active plaquette

The full kinetic map transports a plaquette times a polynomial independent
of its four links by the exact factor w^12. The entire original active
kernel and its transformed spectator remain; this is not an eigenidentity
for the interacting transfer or a continuum estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorKinetic

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
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPlaquette
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local notation:max "N" width:arg => List.length (baseLinks width)


open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)

/-- Exact transmission retains the full transformed spectator. -/
theorem plaquette_spectator_kinetic (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width)
    (w : Q') (K : Nat) (hK : 1 ≤ K)
    (A : RatPoly) (hA : SupportedQuaternionBlocks (N width) A)
    (hAI : ∀ l, l ∈ edgesOf face →
      QuaternionBlockIndependent ((baseLinks width).idxOf l) A) :
    SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width)
        (polyMul (characterPolynomial (plaquette width face).scalar 1) A))
      (polySmul (qpow w 12)
        (polyMul (characterPolynomial (plaquette width face).scalar 1)
          (productMap (N width) w K (activeBlocks width) A))) := by
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
  have hsource : RatPolyCoeffEqv
      (characterPolynomial (plaquette width face).scalar 1)
      (SU2QuaternionFundamentalPlaquetteTube.plaquette a b c d) := by
    have h := characterPolynomial_coeffEqv (plaquette_fourWord hf).scalar 1
    simpa only [a, b, c, d, la, lb, lc, ld,
      SU2QuaternionFundamentalPlaquetteTube.plaquette,
      SU2QuaternionOrientedWordSelection.word, orientedCoordinateQuaternion] using h

  have hm (p : RatPoly) : RatPolyCoeffEqv
      (productMap (N width) w K (activeBlocks width) p)
      (productMap (N width) w K (a::b::c::d::r3) p) :=
    partialHaarHeads_congr (N width)
      ((polynomialProduct_perm _ hp).mul_right p)
  have hgeneric := selected_pairing_spectator_full (N width) w K hK a b c d r3
    (hp.nodup_iff.mp (activeBlocks_nodup width))
    (fun i hi => activeBlocks_lt width i (hp.mem_iff.mpr hi))
    A hA
    (hAI la (by simp [la, edgesOf]))
    (hAI ld (by simp [ld, edgesOf]))
    (hAI lc (by simp [lc, edgesOf]))
    (hAI lb (by simp [lb, edgesOf]))
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      ((productMap_congr (N width) w K (activeBlocks width)
        (hsource.mul_right A)).trans (hm _)))).trans
    (hgeneric.trans (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        ((hsource.symm.mul (hm A).symm).smul (qpow w 12)))))

#print axioms plaquette_spectator_kinetic

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorKinetic
