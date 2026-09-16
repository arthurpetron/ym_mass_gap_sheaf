/-
# Finite rational spans of literal scheduled spatial probes

Compile finite rational sums of scheduled signed face-character products
on the source window and on the original slab. The bilinear pin retains
every mixed term and every signed coefficient. Each pair of schedules is
their literal append, so the existing original-window pin applies before
linearity assembles the two sums. The selected chain, heat cutoff and
normalizing partition remain unchanged throughout.

This supplies the original-observable equality needed to apply selected
site-reflection positivity to finite spans, rather than just to one
character product. The reflected schedule, one-sided geometry and limiting
positivity are separate consumers; arbitrary coordinate polynomials are
not thereby identified with physical observables.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow (windowRatio_originalFiniteValue)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- Finite signed rational combinations of actual source schedules. -/
def sourceSpan (width : Nat) (xs : List (Q' × List (Nat × List FaceFactor))) : RatPoly :=
  finitePolySum (fun x => polySmul x.1 (windowProbe width x.2)) xs

/-- The same coefficients and schedules, placed literally in the original slab. -/
def placedSpan (extent start : Nat) (xs : List (Q' × List (Nat × List FaceFactor))) : RatPoly :=
  finitePolySum (fun x => polySmul x.1 (sweptProduct extent 0 (placeWindowProbes start x.2))) xs

private theorem sum_supported {A : Type} {blocks : Nat} (f : A → RatPoly) :
    (xs : List A) → (∀ a, a ∈ xs → SupportedQuaternionBlocks blocks (f a)) →
      SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [], _ => fun _ ht => False.elim (List.not_mem_nil ht)
  | a::xs, h => supported_add (h a List.mem_cons_self)
      (sum_supported f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem sourceSpan_supported (width L : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ L) :
    SupportedQuaternionBlocks ((L+1)*(N width)) (sourceSpan width xs) :=
  sum_supported _ xs (fun x hx => supported_smul (windowProbe_supported width L x.2 (hwithin x hx)) x.1)

theorem placedSpan_supported (extent start : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor))) :
    SupportedQuaternionBlocks (B extent) (placedSpan extent start xs) :=
  sum_supported _ xs (fun x _ => supported_smul
    (product_supported (sweptCharacter extent 0) (swept_character_supported extent 0)
      (placeWindowProbes start x.2)) x.1)

private theorem sum_congr {A : Type} (f g : A → RatPoly) :
    (xs : List A) → (∀ a, a ∈ xs → RatPolyCoeffEqv (f a) (g a)) →
      RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => RatPolyCoeffEqv.refl _
  | a::xs, h => (h a List.mem_cons_self).add
      (sum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem sum_mul {A : Type} (f : A → RatPoly) (p : RatPoly) :
    (xs : List A) → RatPolyCoeffEqv (polyMul (finitePolySum f xs) p)
      (finitePolySum (fun a => polyMul (f a) p) xs)
  | [] => RatPolyCoeffEqv.refl _
  | a::xs => by
      change RatPolyCoeffEqv (polyMul (polyAdd (f a) (finitePolySum f xs)) p) _
      rw [polyMul_add_left_exact]
      exact (RatPolyCoeffEqv.refl _).add (sum_mul f p xs)

private theorem mul_sum {A : Type} (p : RatPoly) (f : A → RatPoly) :
    (xs : List A) → RatPolyCoeffEqv (polyMul p (finitePolySum f xs))
      (finitePolySum (fun a => polyMul p (f a)) xs)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | a::xs => (RatPolyCoeffEqv.mul_add_right p (f a) (finitePolySum f xs)).trans
      ((RatPolyCoeffEqv.refl _).add (mul_sum p f xs))

private theorem sum_product {A C : Type} (f : A → RatPoly) (g : C → RatPoly)
    (xs : List A) (ys : List C) :
    RatPolyCoeffEqv (polyMul (finitePolySum f xs) (finitePolySum g ys))
      (finitePolySum (fun a => finitePolySum (fun b => polyMul (f a) (g b)) ys) xs) :=
  (sum_mul f (finitePolySum g ys) xs).trans
    (sum_congr _ _ xs (fun a _ => mul_sum (f a) g ys))

private theorem sum_pin {A : Type} (F G : RatPoly → Q')
    (hzero : F polyZero ≈ G polyZero)
    (hFadd : ∀ p q, F (polyAdd p q) ≈ F p + F q)
    (hGadd : ∀ p q, G (polyAdd p q) ≈ G p + G q)
    (f g : A → RatPoly) :
    (xs : List A) → (∀ a, a ∈ xs → F (f a) ≈ G (g a)) →
      F (finitePolySum f xs) ≈ G (finitePolySum g xs)
  | [], _ => hzero
  | a::xs, h => Q'.eqv_trans _ _ _ (hFadd _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (h a List.mem_cons_self)
        (sum_pin F G hzero hFadd hGadd f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))))
        (Q'.eqv_symm (hGadd _ _)))

private theorem smul_pin (F G : RatPoly → Q')
    (hF : ∀ c p, F (polySmul c p) ≈ c * F p)
    (hG : ∀ c p, G (polySmul c p) ≈ c * G p)
    (c : Q') {p q : RatPoly} (h : F p ≈ G q) :
    F (polySmul c p) ≈ G (polySmul c q) :=
  Q'.eqv_trans _ _ _ (hF c p)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ h) (Q'.eqv_symm (hG c q)))

private theorem scaled_product (a b : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul a p) (polySmul b q))
      (polySmul a (polySmul b (polyMul p q))) :=
  (RatPolyCoeffEqv.polyMul_smul_left a p (polySmul b q)).trans
    ((RatPolyCoeffEqv.polyMul_smul_right b p q).smul a)

section FiniteValue

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent : Nat) (ids : List Nat)
  (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (stage : Nat)

private theorem finite_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    finiteValue w hw0 hw1 extent ids hids p stage ≈ finiteValue w hw0 hw1 extent ids hids q stage := by
  unfold finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (h.mul_right _))

private theorem finite_zero : finiteValue w hw0 hw1 extent ids hids polyZero stage ≈ 0 :=
  Q'.zero_mul_eqv _

private theorem finite_add (p q : RatPoly) :
    finiteValue w hw0 hw1 extent ids hids (polyAdd p q) stage ≈
      finiteValue w hw0 hw1 extent ids hids p stage + finiteValue w hw0 hw1 extent ids hids q stage := by
  unfold finiteValue numerator
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_append _ _ _))
    (Q'.add_mul_eqv _ _ _)

private theorem finite_smul (c : Q') (p : RatPoly) :
    finiteValue w hw0 hw1 extent ids hids (polySmul c p) stage ≈
      c * finiteValue w hw0 hw1 extent ids hids p stage := by
  unfold finiteValue numerator
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ c _ p)
          (Q'.mul_eqv_congr_left c _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))))
    (Q'.mul_assoc_eqv _ _ _)

end FiniteValue

private theorem schedule_pair_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start m L n extent : Nat} (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent)
    (fs gs : List (Nat × List FaceFactor))
    (hfwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hffaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (hgwithin : ∀ e, e ∈ gs → e.1 ≤ L)
    (hgfaces : ∀ e, e ∈ gs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) (stage : Nat) :
    windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n
        (polyMul (windowProbe width fs) (windowProbe width gs)) ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start (m+(L+n)))
        (fun _ hi => chainIds_physical hi)
        (polyMul (sweptProduct extent 0 (placeWindowProbes (start+m) fs))
          (sweptProduct extent 0 (placeWindowProbes (start+m) gs))) stage := by
  have hwithin : ∀ e, e ∈ fs++gs → e.1 ≤ L := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hfwithin e he
    · exact hgwithin e he
  have hfaces : ∀ e, e ∈ fs++gs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hffaces e he
    · exact hgfaces e he
  have hsource : RatPolyCoeffEqv (windowProbe width (fs++gs))
      (polyMul (windowProbe width fs) (windowProbe width gs)) := polynomialProduct_append _ fs gs
  have hplaced : RatPolyCoeffEqv (sweptProduct extent 0 (placeWindowProbes (start+m) (fs++gs)))
      (polyMul (sweptProduct extent 0 (placeWindowProbes (start+m) fs))
        (sweptProduct extent 0 (placeWindowProbes (start+m) gs))) := by
    simp only [placeWindowProbes, List.flatMap_append]
    exact polynomialProduct_append _ _ _
  exact Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n hsource.symm)
    (Q'.eqv_trans _ _ _ (windowRatio_originalFiniteValue hw0 hw1 hw ht (fs++gs) hwithin hfaces stage)
      (finite_congr hw0 hw1 extent (chainIds extent width start (m+(L+n)))
        (fun _ hi => chainIds_physical hi) stage hplaced))

/-- Bilinear original pin for arbitrary finite rational spans of actual
scheduled probes. Both sums, all cross terms and the SAME chain partition
are retained. There is no positivity premise on their coefficients. -/
theorem windowRatio_span_mul_originalFiniteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start m L n extent : Nat} (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent)
    (xs ys : List (Q' × List (Nat × List FaceFactor)))
    (hxwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ L)
    (hxfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (hywithin : ∀ y, y ∈ ys → ∀ e, e ∈ y.2 → e.1 ≤ L)
    (hyfaces : ∀ y, y ∈ ys → ∀ e, e ∈ y.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) (stage : Nat) :
    windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n
        (polyMul (sourceSpan width xs) (sourceSpan width ys)) ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start (m+(L+n)))
        (fun _ hi => chainIds_physical hi)
        (polyMul (placedSpan extent (start+m) xs) (placedSpan extent (start+m) ys)) stage := by
  let F : RatPoly → Q' := windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n
  let G : RatPoly → Q' := fun p => finiteValue w hw0 hw1 extent
    (chainIds extent width start (m+(L+n))) (fun _ hi => chainIds_physical hi) p stage
  have hFC : ∀ {p q}, RatPolyCoeffEqv p q → F p ≈ F q :=
    fun {_ _} h => windowRatio_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n h
  have hGC : ∀ {p q}, RatPolyCoeffEqv p q → G p ≈ G q :=
    fun {_ _} h => finite_congr hw0 hw1 extent (chainIds extent width start (m+(L+n)))
      (fun _ hi => chainIds_physical hi) stage h
  have hFA : ∀ p q, F (polyAdd p q) ≈ F p + F q :=
    windowRatio_add hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n
  have hGA : ∀ p q, G (polyAdd p q) ≈ G p + G q :=
    finite_add hw0 hw1 extent (chainIds extent width start (m+(L+n)))
      (fun _ hi => chainIds_physical hi) stage
  have hFS : ∀ c p, F (polySmul c p) ≈ c * F p :=
    windowRatio_smul hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m L n
  have hGS : ∀ c p, G (polySmul c p) ≈ c * G p :=
    finite_smul hw0 hw1 extent (chainIds extent width start (m+(L+n)))
      (fun _ hi => chainIds_physical hi) stage
  have hFzero : F polyZero ≈ 0 :=
    Q'.eqv_trans _ _ _ (hFC (RatPolyCoeffEqv.zero_smul polyOne).symm)
      (Q'.eqv_trans _ _ _ (hFS 0 polyOne) (Q'.zero_mul_eqv _))
  have hzero : F polyZero ≈ G polyZero := Q'.eqv_trans _ _ _ hFzero
    (Q'.eqv_symm (finite_zero hw0 hw1 extent (chainIds extent width start (m+(L+n)))
      (fun _ hi => chainIds_physical hi) stage))
  let f := fun x : Q' × List (Nat × List FaceFactor) => polySmul x.1 (windowProbe width x.2)
  let g := fun x : Q' × List (Nat × List FaceFactor) =>
    polySmul x.1 (sweptProduct extent 0 (placeWindowProbes (start+m) x.2))
  have hpairs : ∀ x, x ∈ xs → ∀ y, y ∈ ys → F (polyMul (f x) (f y)) ≈ G (polyMul (g x) (g y)) := by
    intro x hx y hy
    have h := schedule_pair_pin hw0 hw1 hw ht x.2 y.2
      (hxwithin x hx) (hxfaces x hx) (hywithin y hy) (hyfaces y hy) stage
    exact Q'.eqv_trans _ _ _ (hFC (scaled_product x.1 y.1 _ _))
      (Q'.eqv_trans _ _ _ (smul_pin F G hFS hGS x.1 (smul_pin F G hFS hGS y.1 h))
        (Q'.eqv_symm (hGC (scaled_product x.1 y.1 _ _))))
  exact Q'.eqv_trans _ _ _ (hFC (sum_product f f xs ys))
    (Q'.eqv_trans _ _ _
      (sum_pin F G hzero hFA hGA _ _ xs (fun x hx =>
        sum_pin F G hzero hFA hGA _ _ ys (hpairs x hx)))
      (Q'.eqv_symm (hGC (sum_product g g xs ys))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan.sourceSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan.placedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan.sourceSpan_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan.placedSpan_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan.windowRatio_span_mul_originalFiniteValue
