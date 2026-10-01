/-
# Exact full-range heat image of an actual spatial plaquette square

Every edge of an original spatial face occurs in the full base-link range.
Constructive list selection therefore exposes its four distinct heat factors,
and the generic plaquette-square transmission applies without an activity
hypothesis.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition (faceSlots)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
  (idxOf_injective_on_members)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPlaquette
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex select_perm)
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Computed four-link presentation of the actual spatial face, retaining the
permutation of the complete original carrier and its literal scalar pin. -/
structure FullRangePlaquetteSelection
    (width : Nat) (face : Z4Plaq) where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  rest : List Nat
  perm : (List.range (N width)).Perm (a::b::c::d::rest)
  slots : (faceSlots width face).Perm [a,b,c,d]
  scalar : RatPolyCoeffEqv (plaquette width face).scalar
    (word a b c d false false true true).scalar

/-- The original geometric selection is reusable by differential consumers;
no new activity, exposure or distinctness hypothesis is requested. -/
def fullRangePlaquetteSelection
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    FullRangePlaquetteSelection width face := by
  let la : Z4Link := (face.1, (dirsOf face.2).1)
  let lb : Z4Link := (face.1, (dirsOf face.2).2)
  let lc : Z4Link :=
    (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
  let ld : Z4Link :=
    (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
  let a := (baseLinks width).idxOf la
  let b := (baseLinks width).idxOf ld
  let c := (baseLinks width).idxOf lc
  let d := (baseLinks width).idxOf lb
  have hla : la ∈ baseLinks width :=
    face_link_mem_base hf (by simp [la, edgesOf])
  have hlb : lb ∈ baseLinks width :=
    face_link_mem_base hf (by simp [lb, edgesOf])
  have hlc : lc ∈ baseLinks width :=
    face_link_mem_base hf (by simp [lc, edgesOf])
  have hld : ld ∈ baseLinks width :=
    face_link_mem_base hf (by simp [ld, edgesOf])
  have hlinks : (la ≠ lb ∧ (la ≠ lc ∧ la ≠ ld)) ∧
      ((lb ≠ lc ∧ lb ≠ ld) ∧ lc ≠ ld) := by
    simpa only [la, lb, lc, ld, edgesOf, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or,
      not_false_eq_true, and_true] using edgesOf_nodup face
  have hne {u v : Z4Link} (hu : u ∈ baseLinks width)
      (hv : v ∈ baseLinks width) (huv : u ≠ v) :
      (baseLinks width).idxOf u ≠ (baseLinks width).idxOf v :=
    fun he => huv (idxOf_injective_on_members hu hv he)
  have hab : a ≠ b := hne hla hld hlinks.1.2.2
  have hac : a ≠ c := hne hla hlc hlinks.1.2.1
  have had : a ≠ d := hne hla hlb hlinks.1.1
  have hbc : b ≠ c := hne hld hlc (Ne.symm hlinks.2.2)
  have hbd : b ≠ d := hne hld hlb (Ne.symm hlinks.2.1.2)
  have hcd : c ≠ d := hne hlc hlb (Ne.symm hlinks.2.1.1)
  have ha : a ∈ List.range (N width) :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hla)
  have hb : b ∈ List.range (N width) :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hld)
  have hc : c ∈ List.range (N width) :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hlc)
  have hd : d ∈ List.range (N width) :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hlb)
  let r0 := eraseIndex a (List.range (N width))
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
  have hp : (List.range (N width)).Perm (a::b::c::d::r3) :=
    (select_perm a ha).trans (List.Perm.cons a
      ((select_perm b hb0).trans (List.Perm.cons b
        ((select_perm c hc1).trans
          (List.Perm.cons c (select_perm d hd2))))))
  have hscalar : RatPolyCoeffEqv (plaquette width face).scalar
      (word a b c d false false true true).scalar := by
    have h := (plaquette_fourWord hf).scalar
    simpa only [a, b, c, d, la, lb, lc, ld,
      SU2QuaternionOrientedWordSelection.word,
      orientedCoordinateQuaternion] using h
  have hslots : (faceSlots width face).Perm [a,b,c,d] := by
    change [a,d,c,b].Perm [a,b,c,d]
    exact List.Perm.cons a (List.reverse_perm [d,c,b]).symm
  exact ⟨a, b, c, d, r3, hp, hslots, hscalar⟩

/-- The full product heat sends the actual fundamental plaquette character
to `w^12` times itself. -/
theorem plaquette_fullRange
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (w : Q') (K : Nat) (hK : 1 ≤ K) :
    let f := characterPolynomial (plaquette width face).scalar 1
    SupportedHaarEqv (N width)
      (productMap (N width) w K (List.range (N width)) f)
      (polySmul (qpow w 12) f) := by
  dsimp only
  let S := fullRangePlaquetteSelection width face hf
  have hgeneric := productMap_plaquette_of_perm
    (N width) w K hK S.a S.b S.c S.d (List.range (N width)) S.rest
    (CayleyParentInj.range_nodup (N width)) (fun i hi => List.mem_range.mp hi) S.perm
  have hsource : RatPolyCoeffEqv
      (characterPolynomial (plaquette width face).scalar 1)
      (characterPolynomial
        (word S.a S.b S.c S.d false false true true).scalar 1) :=
    characterPolynomial_coeffEqv S.scalar 1
  exact (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        (productMap_congr (N width) w K (List.range (N width)) hsource))).trans
    (hgeneric.trans (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        (hsource.smul (qpow w 12)).symm)))

/-- The full product heat sends the actual fundamental plaquette square to
its vacuum channel plus `w^32` times its actual label-two character. -/
theorem plaquetteSquare_fullRange
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (w : Q') (K : Nat) (hK : 2 ≤ K) :
    let f := characterPolynomial (plaquette width face).scalar 1
    let chi2 := characterPolynomial (plaquette width face).scalar 2
    SupportedHaarEqv (N width)
      (productMap (N width) w K (List.range (N width)) (polyMul f f))
      (polyAdd polyOne (polySmul (qpow w 32) chi2)) := by
  dsimp only
  let S := fullRangePlaquetteSelection width face hf
  have hgeneric := productMap_plaquetteSquare_of_perm
    (N width) w K hK S.a S.b S.c S.d (List.range (N width)) S.rest
    (CayleyParentInj.range_nodup (N width)) (fun i hi => List.mem_range.mp hi) S.perm
  have hsource1 : RatPolyCoeffEqv
      (characterPolynomial (plaquette width face).scalar 1)
      (characterPolynomial
        (word S.a S.b S.c S.d false false true true).scalar 1) :=
    characterPolynomial_coeffEqv S.scalar 1
  have hsource2 : RatPolyCoeffEqv
      (characterPolynomial (plaquette width face).scalar 2)
      (characterPolynomial
        (word S.a S.b S.c S.d false false true true).scalar 2) :=
    characterPolynomial_coeffEqv S.scalar 2
  exact (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        (productMap_congr (N width) w K (List.range (N width))
          (hsource1.mul hsource1)))).trans
    (hgeneric.trans (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.refl polyOne).add
          (hsource2.smul (qpow w 32))).symm)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare.plaquette_fullRange
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare.plaquetteSquare_fullRange
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare.fullRangePlaquetteSelection
