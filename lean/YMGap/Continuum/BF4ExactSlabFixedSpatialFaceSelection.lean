/-
# Exact face selection on the original fixed spatial carrier

Any one of a spatial plaquette's four links can be integrated against a
supported spectator independent of that coordinate. Every positive-spin
character vanishes, so its finite heat prefix removes exactly to one.
The quaternion word is pinned on the literal width-only carrier; no
corrected-slab substitution or condition on the coupling is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
import YMGap.Continuum.SU2QuaternionOrientedWordSelection
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local notation "N" width => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Every edge of an actual source face is an actual source coordinate. -/
theorem face_link_mem_base {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) {l : Z4Link} (hl : l ∈ edgesOf face) :
    l ∈ baseLinks width := by
  obtain ⟨hx,hy,hz,ht,hsp⟩ := (spatialFaces_mem_iff width face).mp hf
  have hb := face_edge_box hx hy hz hl
  have he := spatial_face_edge face hsp l hl
  exact (baseLinks_mem_iff width l).mpr
    ⟨he.1,hb.1,hb.2.1,hb.2.2,he.2.trans ht⟩

/-- The ordered original face is the same four-coordinate quaternion word. -/
theorem plaquette_fourWord {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) :
    PolyQuaternionCoeffEqv (plaquette width face)
      (word
        ((baseLinks width).idxOf (face.1, (dirsOf face.2).1))
        ((baseLinks width).idxOf (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2))
        ((baseLinks width).idxOf (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1))
        ((baseLinks width).idxOf (face.1, (dirsOf face.2).2))
        false false true true) := by
  let a : Z4Link := (face.1, (dirsOf face.2).1)
  let b : Z4Link := (face.1, (dirsOf face.2).2)
  let c : Z4Link := (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
  let d : Z4Link := (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
  have ha : a ∈ baseLinks width := face_link_mem_base hf (by simp [a, edgesOf])
  have hb : b ∈ baseLinks width := face_link_mem_base hf (by simp [b, edgesOf])
  have hc : c ∈ baseLinks width := face_link_mem_base hf (by simp [c, edgesOf])
  have hd : d ∈ baseLinks width := face_link_mem_base hf (by simp [d, edgesOf])
  change PolyQuaternionCoeffEqv
    (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
      (PolyQuaternion.mul PolyQuaternion.one (link width a)) (link width d))
      (PolyQuaternion.conj (link width c))) (PolyQuaternion.conj (link width b)))
    (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
      (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf a))
      (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf d)))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf c))))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf b))))
  simp only [link, if_pos ha, if_pos hb, if_pos hc, if_pos hd]
  exact (((PolyQuaternionCoeffEqv.one_mul _).mul (.refl _)).mul (.refl _)).mul (.refl _)

/-- Positive-spin cancellation at any one of the four original links. -/
theorem character_haar_zero {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (spin : Nat) (hs : 0 < spin) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) q) :
    quaternionHaar (N width)
      (polyMul (characterPolynomial (plaquette width face).scalar spin) q) ≈ 0 := by
  let a : Z4Link := (face.1, (dirsOf face.2).1)
  let b : Z4Link := (face.1, (dirsOf face.2).2)
  let c : Z4Link := (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
  let d : Z4Link := (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
  have ha : a ∈ baseLinks width := face_link_mem_base hf (by simp [a, edgesOf])
  have hb : b ∈ baseLinks width := face_link_mem_base hf (by simp [b, edgesOf])
  have hc : c ∈ baseLinks width := face_link_mem_base hf (by simp [c, edgesOf])
  have hd : d ∈ baseLinks width := face_link_mem_base hf (by simp [d, edgesOf])
  have hn : (a ≠ b ∧ (a ≠ c ∧ a ≠ d)) ∧ ((b ≠ c ∧ b ≠ d) ∧ c ≠ d) := by
    simpa only [edgesOf, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      using edgesOf_nodup face
  have hne {u v : Z4Link} (hu : u ∈ baseLinks width) (hv : v ∈ baseLinks width)
      (hne : u ≠ v) : (baseLinks width).idxOf u ≠ (baseLinks width).idxOf v :=
    fun he => hne (idxOf_injective_on_members hu hv he)
  have had := hne ha hd hn.1.2.2
  have hac := hne ha hc hn.1.2.1
  have hab := hne ha hb hn.1.1
  have hdc := hne hd hc (Ne.symm hn.2.2)
  have hdb := hne hd hb (Ne.symm hn.2.1.2)
  have hcb := hne hc hb (Ne.symm hn.2.1.1)
  have hai := List.idxOf_lt_length_of_mem ha
  have hbi := List.idxOf_lt_length_of_mem hb
  have hci := List.idxOf_lt_length_of_mem hc
  have hdi := List.idxOf_lt_length_of_mem hd
  have hsize : 3 < N width := by omega
  have hm : (baseLinks width).idxOf l = (baseLinks width).idxOf a ∨
      (baseLinks width).idxOf l = (baseLinks width).idxOf d ∨
      (baseLinks width).idxOf l = (baseLinks width).idxOf c ∨
      (baseLinks width).idxOf l = (baseLinks width).idxOf b := by
    have he : l = a ∨ l = b ∨ l = c ∨ l = d := by
      simpa only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] using hl
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((characterPolynomial_coeffEqv (plaquette_fourWord hf).scalar spin).mul_right q))
    (any_slot_zero hsize ⟨_,hai⟩ ⟨_,hdi⟩ ⟨_,hci⟩ ⟨_,hbi⟩
      had hac hab hdc hdb hcb false false true true spin hs q hq
      ((baseLinks width).idxOf l) hm (independent_has_degree_zero hi))

private theorem sum_insert_zero {A : Type} (blocks : Nat) (f : A → RatPoly)
    (q : RatPoly) (hz : ∀ a, quaternionHaar blocks (polyMul (f a) q) ≈ 0) :
    ∀ xs : List A, quaternionHaar blocks (polyMul (finitePolySum f xs) q) ≈ 0
  | [] => Q'.eqv_refl 0
  | a :: xs => by
      change quaternionHaar blocks
        (polyMul (polyAdd (f a) (finitePolySum f xs)) q) ≈ 0
      rw [polyMul_add_left_exact]
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (hz a) (sum_insert_zero blocks f q hz xs))
          (Q'.eqv_of_eq (Q'.add_zero' 0)))

/-- Exact finite heat-factor removal, with no positivity or coupling restriction. -/
theorem heatFace_haar_remove (w : Q') (K : Nat) {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) q) :
    quaternionHaar (N width)
      (polyMul (heatPrefix w K (plaquette width face).scalar) q) ≈
      quaternionHaar (N width) q := by
  have hz : quaternionHaar (N width)
      (polyMul (heatRemainder w K (plaquette width face).scalar) q) ≈ 0 := by
    apply sum_insert_zero
    intro j
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) _ _)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (character_haar_zero hf l hl (1+j) (by omega) q hq hi))
          (Q'.mul_zero_eqv _)))
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff ((heatPrefix_split w K (plaquette width face).scalar).mul_right q)) ?_
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (haar_of_coeff (RatPolyCoeffEqv.one_mul q)) hz)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection.face_link_mem_base
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection.plaquette_fourWord
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection.character_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection.heatFace_haar_remove
