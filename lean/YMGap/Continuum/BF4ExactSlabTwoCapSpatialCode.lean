/-
# Two original spatial odd faces have one common projection

This is an all-spin statement about the original nonzero pair, not a
power-42 restriction. The joint channel puts both caps in one replica;
the means channel puts one probe-aligned cap in each. In either case,
one cap, the second cap's time, and the replica split recover both
spatial lists. Higher labels and configuration counting remain separate.
-/

import YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation
import YMGap.Continuum.BF4ExactSlabPairChannelParity

namespace YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation
open YMGap.Continuum.BF4ExactSlabSingleSpatialCap
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabMomentFaceParity
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut

local infix:50 " ≈ " => Q'.eqv

def spatialList (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : List Z4Plaq :=
  spatialOddFaces margin pair.1 ++ spatialOddFaces margin pair.2

def firstCap (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Z4Plaq :=
  (spatialList margin pair).headD (capFace margin 0)

def secondCap (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Z4Plaq :=
  (spatialList margin pair).tail.headD (capFace margin 0)

def layout (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  (spatialOddFaces margin pair.1).length

theorem spatialList_two (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hs : pairSpatial margin pair=2) : spatialList margin pair=[firstCap margin pair,secondCap margin pair] := by
  have hl : (spatialList margin pair).length=2 := by
    rw [spatialList,List.length_append]
    exact hs
  cases he : spatialList margin pair with
  | nil => rw [he] at hl; contradiction
  | cons a rest =>
    cases rest with
    | nil => simp only [he,List.length_cons,List.length_nil] at hl; omega
    | cons b tail =>
      have ht : tail=[] := List.length_eq_zero_iff.mp (by
        simp only [he,List.length_cons] at hl
        omega)
      subst tail
      simp only [firstCap,secondCap,he,List.headD_cons,List.tail_cons]

theorem two_spatial_distribution (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (hs : pairSpatial margin pair=2) :
    if jointCheck margin pair then
      ((spatialOddFaces margin pair.1).length=2 ∧ (spatialOddFaces margin pair.2).length=0) ∨
        ((spatialOddFaces margin pair.1).length=0 ∧ (spatialOddFaces margin pair.2).length=2)
    else (spatialOddFaces margin pair.1).length=1 ∧ (spatialOddFaces margin pair.2).length=1 := by
  have hc := nonzero_pair_channel_checks margin pair hne
  have hl := (moment_face_parities margin true (jointCheck margin pair) pair.1 hc.1).2
  have hr := (moment_face_parities margin false (!(jointCheck margin pair)) pair.2 hc.2).2
  unfold pairSpatial at hs
  cases hj : jointCheck margin pair <;>
    simp only [hj,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true] at hl hr ⊢
  · constructor <;> omega
  · by_cases hz : (spatialOddFaces margin pair.1).length=0
    · exact Or.inr ⟨hz,by omega⟩
    · exact Or.inl ⟨by omega,by omega⟩

theorem two_caps_projection (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (hs : pairSpatial margin pair=2) :
    faceAt 0 (firstCap margin pair)=faceAt 0 (secondCap margin pair) := by
  have hc := nonzero_pair_channel_checks margin pair hne
  have hd := two_spatial_distribution margin pair hne hs
  have hl := spatialList_two margin pair hs
  cases hj : jointCheck margin pair <;>
    simp only [hj,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true] at hc hd
  · have hleft := single_spatial_cap_pin margin true pair.1 hd.1 hc.1
    have hright := single_spatial_cap_pin margin false pair.2 hd.2 hc.2
    simp only [firstCap,secondCap,spatialList,hleft,hright,List.cons_append,List.nil_append,
      List.headD_cons,List.tail_cons,faceAt,capFace]
  · rcases hd with hd | hd
    · have hr := List.length_eq_zero_iff.mp hd.2
      simp only [spatialList,hr,List.append_nil] at hl
      exact joint_two_spatial_projection margin true pair.1 _ _ hl hc.1
    · have hleft := List.length_eq_zero_iff.mp hd.1
      simp only [spatialList,hleft,List.nil_append] at hl
      exact joint_two_spatial_projection margin false pair.2 _ _ hl hc.2

theorem append_split_injective {A : Type} : ∀ (left right left' right' : List A),
    left.length=left'.length → left++right=left'++right' → left=left' ∧ right=right'
  | [], right, [], right', _, he => ⟨rfl,he⟩
  | [], _, _::_, _, hl, _ => by cases hl
  | _::_, _, [], _, hl, _ => by cases hl
  | a::left, right, b::left', right', hl, he => by
    have hh := List.cons.inj he
    have ht := append_split_injective left right left' right' (Nat.succ.inj hl) hh.2
    exact ⟨by rw [hh.1,ht.1],ht.2⟩

theorem two_caps_recover_spatial {margin : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : pairSpatial margin left=2) (hr : pairSpatial margin right=2)
    (hfirst : firstCap margin left=firstCap margin right)
    (hsecond : secondCap margin left=secondCap margin right) (hsplit : layout margin left=layout margin right) :
    spatialOddFaces margin left.1=spatialOddFaces margin right.1 ∧
      spatialOddFaces margin left.2=spatialOddFaces margin right.2 := by
  apply append_split_injective _ _ _ _ hsplit
  change spatialList margin left=spatialList margin right
  rw [spatialList_two margin left hl,spatialList_two margin right hr,hfirst,hsecond]

theorem channel_eq_of_spatial_eq {margin : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : ¬pairTerm margin left.1 left.2 ≈ 0) (hr : ¬pairTerm margin right.1 right.2 ≈ 0)
    (hs : spatialOddFaces margin left.1=spatialOddFaces margin right.1) :
    jointCheck margin left=jointCheck margin right := by
  have hcl := (nonzero_pair_channel_checks margin left hl).1
  have hcr := (nonzero_pair_channel_checks margin right hr).1
  have hpl := (moment_face_parities margin true (jointCheck margin left) left.1 hcl).2
  have hpr := (moment_face_parities margin true (jointCheck margin right) right.1 hcr).2
  rw [hs] at hpl
  cases hjl : jointCheck margin left <;> cases hjr : jointCheck margin right
  · rfl
  · simp only [hjl,hjr,Bool.false_eq_true,↓reduceIte] at hpl hpr
    omega
  · simp only [hjl,hjr,Bool.false_eq_true,↓reduceIte] at hpl hpr
    omega
  · rfl

end YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode

#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.spatialList
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.firstCap
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.secondCap
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.layout
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.spatialList_two
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.two_spatial_distribution
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.two_caps_projection
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.append_split_injective
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.two_caps_recover_spatial
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode.channel_eq_of_spatial_eq
