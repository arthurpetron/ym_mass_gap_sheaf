/-
# Symmetry of the original selected-chain reflected form

The actual centered selected face list is reflection-permuted. Its heat
product is therefore invariant under the original orientation-correct
reflection. The same link reflection is an involution, including the
time-link conjugation signs. Product-Haar invariance then proves symmetry
of the mixed reflected numerator for arbitrary supported polynomials.

The existing literal span placement and original bilinear pin carry this
identity to diagonal finite window ratios. Both signed source spans,
the retained cutoff and the SAME selected partition are unchanged. This
is a finite symmetry input to the existing reflected window limit, not a
new completed physical transfer or a continuum mass-gap assertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive
import YMGap.Continuum.SU2QuaternionCoordinateConjugation
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance (faceHeat_reflection)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization (blockCount)
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction (selectedHeat selectedHeat_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction (originalChainAction)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan placedSpan_reflection)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionCoordinateConjugation (signSelectedPolynomial_involutive_prefix)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private def coordinateMap {blocks : Nat} (R : QuaternionBlockInvolution blocks) (i : Nat) : Nat :=
  4*R.map (i/4)+i%4

private theorem coordinateMap_lt {blocks : Nat} (R : QuaternionBlockInvolution blocks)
    {i : Nat} (hi : i < 4*blocks) : coordinateMap R i < 4*blocks := by
  have hb : i/4 < blocks := by omega
  have hm := R.map_lt (i/4) hb
  unfold coordinateMap
  omega

private theorem coordinateMap_involutive {blocks : Nat} (R : QuaternionBlockInvolution blocks)
    {i : Nat} (hi : i < 4*blocks) : coordinateMap R (coordinateMap R i) = i := by
  have hb : i/4 < blocks := by omega
  have hd : (4*R.map (i/4)+i%4)/4 = R.map (i/4) := by omega
  have hr : (4*R.map (i/4)+i%4)%4 = i%4 := by omega
  simp only [coordinateMap, hd, hr, R.involutive _ hb]
  omega

private theorem coordinateMap_perm {blocks : Nat} (R : QuaternionBlockInvolution blocks) :
    ((List.range (4*blocks)).map (coordinateMap R)).Perm (List.range (4*blocks)) := by
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · exact YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn _ _
      (YMGap.Continuum.CayleyParentInj.range_nodup _)
      (fun a ha b hb he => by
        have h := congrArg (coordinateMap R) he
        rw [coordinateMap_involutive R (List.mem_range.mp ha),
          coordinateMap_involutive R (List.mem_range.mp hb)] at h
        exact h)
  · exact YMGap.Continuum.CayleyParentInj.range_nodup _
  · intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact List.mem_range.mpr (coordinateMap_lt R (List.mem_range.mp hj))
    · intro hi
      exact List.mem_map.mpr ⟨coordinateMap R i,
        List.mem_range.mpr (coordinateMap_lt R (List.mem_range.mp hi)),
        coordinateMap_involutive R (List.mem_range.mp hi)⟩

private def parityStep (selected : Nat → Bool) (m : List Nat) (p : Bool) (i : Nat) : Bool :=
  if selected i then xor p (decide (exponentAt m i % 2 = 1)) else p

private theorem parityStep_comm (selected : Nat → Bool) (m : List Nat) (p : Bool) (i j : Nat) :
    parityStep selected m (parityStep selected m p i) j =
      parityStep selected m (parityStep selected m p j) i := by
  unfold parityStep
  cases selected i <;> cases selected j <;> cases p <;>
    cases decide (exponentAt m i % 2 = 1) <;> cases decide (exponentAt m j % 2 = 1) <;> rfl

private theorem parityFold_perm (selected : Nat → Bool) (m : List Nat)
    {xs ys : List Nat} (h : xs.Perm ys) (p : Bool) :
    xs.foldl (parityStep selected m) p = ys.foldl (parityStep selected m) p := by
  induction h generalizing p with
  | nil => rfl
  | cons _ _ ih => exact ih _
  | swap i j xs =>
      simp only [List.foldl_cons]
      rw [parityStep_comm]
  | trans _ _ ih ih' => exact (ih p).trans (ih' p)

private theorem parity_reindex {blocks : Nat} (R : QuaternionBlockInvolution blocks)
    (selected : Nat → Bool)
    (hselected : ∀ i, i < 4*blocks → selected (coordinateMap R i) = selected i) (m : List Nat) :
    selectedExponentParity (4*blocks) selected (reindexQuaternionExponents R m) =
      selectedExponentParity (4*blocks) selected m := by
  have hf : ∀ xs : List Nat, (∀ i, i ∈ xs → i < 4*blocks) → ∀ p : Bool,
      xs.foldl (parityStep selected (reindexQuaternionExponents R m)) p =
        (xs.map (coordinateMap R)).foldl (parityStep selected m) p := by
    intro xs
    induction xs with
    | nil => intro _ _; rfl
    | cons i xs ih =>
        intro hx p
        simp only [List.foldl_cons, List.map_cons]
        have hi := hx i List.mem_cons_self
        have hs : parityStep selected (reindexQuaternionExponents R m) p i =
            parityStep selected m p (coordinateMap R i) := by
          unfold parityStep
          rw [exponentAt_reindexQuaternionExponents R m hi, hselected i hi]
          rfl
        rw [hs]
        exact ih (fun j hj => hx j (List.mem_cons_of_mem i hj)) _
  exact (hf (List.range (4*blocks)) (fun _ hi => List.mem_range.mp hi) false).trans
    (parityFold_perm selected m (coordinateMap_perm R) false)

private theorem reindex_sign_comm {blocks : Nat} (R : QuaternionBlockInvolution blocks)
    (selected : Nat → Bool)
    (hselected : ∀ i, i < 4*blocks → selected (coordinateMap R i) = selected i) (p : RatPoly) :
    reindexQuaternionPolynomial R (signSelectedPolynomial (4*blocks) selected p) =
      signSelectedPolynomial (4*blocks) selected (reindexQuaternionPolynomial R p) := by
  simp only [reindexQuaternionPolynomial, signSelectedPolynomial, List.map_map]
  apply List.map_congr_left
  intro t _
  change (reindexQuaternionExponents R t.1,
      if selectedExponentParity (4*blocks) selected t.1 then -t.2 else t.2) =
    (reindexQuaternionExponents R t.1,
      if selectedExponentParity (4*blocks) selected (reindexQuaternionExponents R t.1) then -t.2 else t.2)
  rw [parity_reindex R selected hselected t.1]

private theorem reindex_twice_prefix {blocks : Nat} (R : QuaternionBlockInvolution blocks) :
    ∀ p : RatPoly, QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial R (reindexQuaternionPolynomial R p)) p
  | [] => .nil
  | t::ts => by
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro i hi
        change exponentAt (reindexQuaternionExponents R (reindexQuaternionExponents R t.1)) i =
          exponentAt t.1 i
        rw [exponentAt_reindexQuaternionExponents R _ hi]
        change exponentAt (reindexQuaternionExponents R t.1) (coordinateMap R i) = exponentAt t.1 i
        rw [exponentAt_reindexQuaternionExponents R _ (coordinateMap_lt R hi)]
        change exponentAt t.1 (coordinateMap R (coordinateMap R i)) = exponentAt t.1 i
        rw [coordinateMap_involutive R hi]
      · exact reindex_twice_prefix R ts

private theorem timeVector_reflection (extent i : Nat) (hi : i < 4*(B extent)) :
    correctedSlabTimeVectorCoordinate extent
      (coordinateMap (correctedSlabQuaternionBlockInvolution extent) i) =
      correctedSlabTimeVectorCoordinate extent i := by
  have hb : i/4 < B extent := by omega
  have hd : (4*correctedSlabLinkReflectBlock extent (i/4)+i%4)/4 =
      correctedSlabLinkReflectBlock extent (i/4) := by omega
  have hr : (4*correctedSlabLinkReflectBlock extent (i/4)+i%4)%4 = i%4 := by omega
  change correctedSlabTimeVectorCoordinate extent
    (4*correctedSlabLinkReflectBlock extent (i/4)+i%4) = correctedSlabTimeVectorCoordinate extent i
  unfold correctedSlabTimeVectorCoordinate
  rw [hd, hr, correctedSlabLinkAt_reflectBlock (List.mem_range.mpr hb), timeReflectLink_direction]

/-- The actual sign-corrected reflection is an involution on the finite
coordinate prefix; no algebraic involution is assumed as extra data. -/
theorem reflection_involutive_prefix (extent : Nat) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv (B extent)
      (reflectCorrectedSlabPolynomial extent (reflectCorrectedSlabPolynomial extent p)) p := by
  unfold reflectCorrectedSlabPolynomial
  rw [reindex_sign_comm _ _ (timeVector_reflection extent)]
  exact (signSelectedPolynomial_involutive_prefix (B extent)
    (correctedSlabTimeVectorCoordinate extent) _).trans
      (reindex_twice_prefix (correctedSlabQuaternionBlockInvolution extent) p)

private theorem reflected_product (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    ReflectionImage extent (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polynomialProduct (fun id => faceHeatPolynomial w K extent (slabFaceReflectId extent id)) ids)
  | [], _ => ReflectionImage.one extent
  | id::ids, hi => (faceHeat_reflection w K (hi id List.mem_cons_self)).mul
      (reflected_product w K extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

/-- Reflection invariance of the SAME literal centered selected-chain action. -/
theorem originalChain_reflection (w : Q') (K radius width start depth : Nat)
    (hcenter : start+depth=radius+1) :
    ReflectionImage (adjacentEvenExtent radius)
      (originalChainAction w K (adjacentEvenExtent radius) width start (2*depth))
      (originalChainAction w K (adjacentEvenExtent radius) width start (2*depth)) := by
  have h := reflected_product w K (adjacentEvenExtent radius) (selectedIds radius width start depth)
    (fun _ hi => chainIds_physical hi)
  have hp := polynomialProduct_perm (faceHeatPolynomial w K (adjacentEvenExtent radius))
    (selectedIds_reflection_perm (width := width) hcenter)
  simp only [polynomialProduct, List.foldr_map] at hp
  exact h.trans (PaddedPolynomialCoeffEqv.of_coeff hp)

/-- Mixed original reflected Haar symmetry follows from the actual action
permutation, Haar invariance and reflection involution. Only support is required. -/
theorem originalChain_reflected_symm (w : Q') (K radius width start depth : Nat)
    (hcenter : start+depth=radius+1) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blockCount radius) p)
    (hq : SupportedQuaternionBlocks (blockCount radius) q) :
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q)
        (originalChainAction w K (adjacentEvenExtent radius) width start (2*depth))) ≈
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) q) p)
        (originalChainAction w K (adjacentEvenExtent radius) width start (2*depth))) := by
  have ha := selectedHeat_supported w K radius (selectedIds radius width start depth)
  have hrp : ReflectionImage (adjacentEvenExtent radius)
      (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p :=
    .of_prefix (reflection_involutive_prefix (adjacentEvenExtent radius) p)
  have hrq : ReflectionImage (adjacentEvenExtent radius) q
      (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) q) := .refl _ _
  have hr := (hrp.mul hrq).mul (originalChain_reflection w K radius width start depth hcenter)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_reflectCorrectedSlabPolynomial _ _
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq) ha)))
    (Q'.eqv_trans _ _ _ (PaddedPolynomialCoeffEqv.haar hr (reflectCorrectedSlabPolynomial_support _ _)
      (supported_polyMul (supported_polyMul hp (reflectCorrectedSlabPolynomial_support _ _)) ha))
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).mul_right _)))

/-- The same reciprocal multiplies both original mixed numerators. -/
theorem originalChain_finiteValue_reflected_symm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (hcenter : start+depth=radius+1) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blockCount radius) p)
    (hq : SupportedQuaternionBlocks (blockCount radius) q) (stage : Nat) :
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q) stage ≈
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) q) p) stage := by
  apply Q'.mul_eqv_congr_right
  exact originalChain_reflected_symm w (headCutoff w+stage) radius width start depth hcenter p q hp hq

private theorem finite_reflected_image {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (p p' q : RatPoly)
    (hp' : SupportedQuaternionBlocks (blockCount radius) p')
    (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hr : ReflectionImage (adjacentEvenExtent radius) p p') (stage : Nat) :
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q) stage ≈
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi) (polyMul p' q) stage := by
  have ha := selectedHeat_supported w (headCutoff w+stage) radius (selectedIds radius width start depth)
  apply Q'.mul_eqv_congr_right
  exact ((PaddedPolynomialCoeffEqv.mul hr (.refl _ q)).mul (.refl _
    (selectedHeat w (headCutoff w+stage) radius (selectedIds radius width start depth)))).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq) ha)
      (supported_polyMul (supported_polyMul hp' hq) ha)

private theorem mirror_within (h : Nat) (xs : List (Q' × List (Nat × List FaceFactor))) :
    ∀ x, x ∈ mirrorSpan h xs → ∀ e, e ∈ x.2 → e.1 ≤ 2*h := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact mirrorSchedule_within h y.2

private theorem mirror_faces {width : Nat} (h : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hx : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ x, x ∈ mirrorSpan h xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces h y.2 (hx y hy)

/-- Diagonal finite reflected symmetry on the actual scheduled rational
span, with fixed source coefficients, retained cutoff and selected partition. -/
theorem reflectedWindowRatio_symm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : List (Q' × List (Nat × List FaceFactor)))
    (hxwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h)
    (hxfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (hywithin : ∀ y, y ∈ ys → ∀ e, e ∈ y.2 → e.1 ≤ h)
    (hyfaces : ∀ y, y ∈ ys → ∀ e, e ∈ y.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (stage t : Nat) :
    windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      t (2*h) t (polyMul (sourceSpan width (mirrorSpan h xs)) (sourceSpan width ys)) ≈
    windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      t (2*h) t (polyMul (sourceSpan width (mirrorSpan h ys)) (sourceSpan width xs)) := by
  let radius := width+t+h
  let start := width+1
  let E := adjacentEvenExtent radius
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent radius; omega
  have hcenter : start+t+h=radius+1 := by unfold start radius; omega
  have ht : start+(t+(2*h+t)) ≤ E := by unfold E adjacentEvenExtent centralExtent radius start; omega
  have hcount : t+(2*h+t)=2*(t+h) := by omega
  let p := placedSpan E (start+t) xs
  let q := placedSpan E (start+t) ys
  let rp := placedSpan E (start+t) (mirrorSpan h xs)
  let rq := placedSpan E (start+t) (mirrorSpan h ys)
  have hp := placedSpan_supported E (start+t) xs
  have hq := placedSpan_supported E (start+t) ys
  have hrp := placedSpan_supported E (start+t) (mirrorSpan h xs)
  have hrq := placedSpan_supported E (start+t) (mirrorSpan h ys)
  have hleft := finite_reflected_image hw0 hw1 radius width start (t+h) p rp q hrp hq
    (placedSpan_reflection hw hcenter xs hxwithin hxfaces) stage
  have hright := finite_reflected_image hw0 hw1 radius width start (t+h) q rq p hrq hp
    (placedSpan_reflection hw hcenter ys hywithin hyfaces) stage
  have hs := originalChain_finiteValue_reflected_symm hw0 hw1 radius width start (t+h)
    (by omega) p q hp hq stage
  have hmixed := Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft) (Q'.eqv_trans _ _ _ hs hright)
  have hpx := windowRatio_span_mul_originalFiniteValue hw0 hw1 (m := t) (L := 2*h) (n := t)
    hw ht (mirrorSpan h xs) ys (mirror_within h xs) (mirror_faces h xs hxfaces)
    (fun y hy e he => by have := hywithin y hy e he; omega) hyfaces stage
  have hpy := windowRatio_span_mul_originalFiniteValue hw0 hw1 (m := t) (L := 2*h) (n := t)
    hw ht (mirrorSpan h ys) xs (mirror_within h ys) (mirror_faces h ys hyfaces)
    (fun x hx e he => by have := hxwithin x hx e he; omega) hxfaces stage
  apply Q'.eqv_trans _ _ _ hpx
  apply Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hpy)
  simpa only [selectedIds, hcount] using hmixed

end YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry.reflection_involutive_prefix
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry.originalChain_reflection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry.originalChain_reflected_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry.originalChain_finiteValue_reflected_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry.reflectedWindowRatio_symm
