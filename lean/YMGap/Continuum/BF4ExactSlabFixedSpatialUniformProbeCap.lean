/-
# A computed time-label-independent bound for the actual reflected pairing

Erase only the scheduled times, retaining every signed coefficient, face
word, repeated factor and list order. Lifting changes exponent lists but
not coefficients, and polynomial multiplication retains its Cartesian
coefficient list. Thus the existing polynomial interval compiler returns
one rational cap for every time relabelling of these same presentations.

The actual normalized window ratios satisfy this bound by the zero-step
transfer bracket. Their already constructed time limits, including the
intrinsic reflected pairing, satisfy the same bound. No new state or norm
is substituted. The cap depends on width and the displayed signed face
words, not time labels, boundary distances, nome or retained heat cutoff.
It is a presentation bound, not an OS-norm estimate or physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (sourceProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (windowProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection (mirrorSchedule)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftHead liftBoundary)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Literal coefficient ledger: no collection of like monomials. -/
def coefficients (p : RatPoly) : List Q' := p.map Prod.snd

theorem coefficients_add (p q : RatPoly) :
    coefficients (polyAdd p q) = coefficients p ++ coefficients q :=
  List.map_append

theorem coefficients_smul (c : Q') (p : RatPoly) :
    coefficients (polySmul c p) = (coefficients p).map (fun a => c*a) := by
  simp only [coefficients, polySmul, List.map_map, Function.comp_def]

/-- Exponents do not participate in the Cartesian coefficient product. -/
theorem coefficients_mul (p q : RatPoly) :
    coefficients (polyMul p q) =
      (coefficients p).flatMap (fun a => (coefficients q).map (fun b => a*b)) := by
  simp only [coefficients, polyMul, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def]

theorem coefficients_mul_congr {p p' q q' : RatPoly}
    (hp : coefficients p = coefficients p') (hq : coefficients q = coefficients q') :
    coefficients (polyMul p q) = coefficients (polyMul p' q') := by
  rw [coefficients_mul, coefficients_mul, hp, hq]

theorem coefficients_liftBoundary (blocks : Nat) (p : RatPoly) :
    coefficients (liftBoundary blocks p) = coefficients p := by
  induction blocks with
  | zero => rfl
  | succ blocks ih =>
      change coefficients (liftHead (liftBoundary blocks p)) = coefficients p
      simpa only [coefficients, liftHead, List.map_map, Function.comp_def] using ih

private def coefficientCap : List Q' → Q'
  | [] => 0
  | c::cs => (c*c+1) + coefficientCap cs

private theorem polynomialCap_coefficients (p : RatPoly) :
    polynomialCap p = coefficientCap (coefficients p) := by
  induction p with
  | nil => rfl
  | cons term rest ih =>
      change (term.2*term.2+1) + polynomialCap rest =
        (term.2*term.2+1) + coefficientCap (coefficients rest)
      rw [ih]

theorem polynomialCap_congr {p q : RatPoly} (h : coefficients p = coefficients q) :
    polynomialCap p = polynomialCap q := by
  rw [polynomialCap_coefficients, polynomialCap_coefficients, h]

/-- Erasure retains each ordered signed face word and removes its time label. -/
def eraseSchedule (fs : List (Nat × List FaceFactor)) : List (List FaceFactor) :=
  fs.map Prod.snd

abbrev ErasedSpan := List (Q' × List (List FaceFactor))

def eraseSpan (xs : Span) : ErasedSpan :=
  xs.map (fun x => (x.1, eraseSchedule x.2))

/-- Arbitrary time maps, including noninjective maps, preserve the ledger. -/
def relabelSchedule (timeMap : Nat → Nat) (fs : List (Nat × List FaceFactor)) :
    List (Nat × List FaceFactor) :=
  fs.map (fun e => (timeMap e.1, e.2))

def relabelSpan (timeMap : Nat → Nat) (xs : Span) : Span :=
  xs.map (fun x => (x.1, relabelSchedule timeMap x.2))

theorem eraseSchedule_relabel (timeMap : Nat → Nat) (fs : List (Nat × List FaceFactor)) :
    eraseSchedule (relabelSchedule timeMap fs) = eraseSchedule fs := by
  simp only [eraseSchedule, relabelSchedule, List.map_map, Function.comp_def]

theorem eraseSpan_relabel (timeMap : Nat → Nat) (xs : Span) :
    eraseSpan (relabelSpan timeMap xs) = eraseSpan xs := by
  simp only [eraseSpan, relabelSpan, List.map_map, Function.comp_def, eraseSchedule_relabel]

theorem eraseSpan_mirror (h : Nat) (xs : Span) :
    eraseSpan (mirrorSpan h xs) = eraseSpan xs := by
  simp only [eraseSpan, mirrorSpan, eraseSchedule, mirrorSchedule,
    List.map_map, Function.comp_def]

theorem eraseSpan_encodeChart (h : Nat) (xs : DistanceSpan) :
    eraseSpan (encodeChart h xs) = eraseSpan xs := by
  simp only [eraseSpan, encodeChart, eraseSchedule, encodeSchedule,
    List.map_map, Function.comp_def]

/-- Computational source polynomial with no time data in its input. -/
def erasedProbe (width : Nat) (fs : List (List FaceFactor)) : RatPoly :=
  polynomialProduct (sourceProbe width) fs

def erasedSpanPolynomial (width : Nat) (xs : ErasedSpan) : RatPoly :=
  finitePolySum (fun x => polySmul x.1 (erasedProbe width x.2)) xs

theorem coefficients_windowProbe (width : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    coefficients (windowProbe width fs) = coefficients (erasedProbe width (eraseSchedule fs))
  | [] => rfl
  | e::es => by
      change coefficients (polyMul (liftBoundary (e.1*(N width)) (sourceProbe width e.2))
          (windowProbe width es)) =
        coefficients (polyMul (sourceProbe width e.2) (erasedProbe width (eraseSchedule es)))
      exact coefficients_mul_congr (coefficients_liftBoundary _ _)
        (coefficients_windowProbe width es)

theorem coefficients_sourceSpan (width : Nat) : (xs : Span) →
    coefficients (sourceSpan width xs) =
      coefficients (erasedSpanPolynomial width (eraseSpan xs))
  | [] => rfl
  | x::xs => by
      change coefficients (polyAdd (polySmul x.1 (windowProbe width x.2)) (sourceSpan width xs)) =
        coefficients (polyAdd (polySmul x.1 (erasedProbe width (eraseSchedule x.2)))
          (erasedSpanPolynomial width (eraseSpan xs)))
      rw [coefficients_add, coefficients_add, coefficients_smul, coefficients_smul,
        coefficients_windowProbe, coefficients_sourceSpan width xs]

theorem coefficients_windowProbe_relabel (width : Nat) (timeMap : Nat → Nat)
    (fs : List (Nat × List FaceFactor)) :
    coefficients (windowProbe width (relabelSchedule timeMap fs)) = coefficients (windowProbe width fs) := by
  rw [coefficients_windowProbe, coefficients_windowProbe, eraseSchedule_relabel]

theorem coefficients_sourceSpan_relabel (width : Nat) (timeMap : Nat → Nat) (xs : Span) :
    coefficients (sourceSpan width (relabelSpan timeMap xs)) = coefficients (sourceSpan width xs) := by
  rw [coefficients_sourceSpan, coefficients_sourceSpan, eraseSpan_relabel]

/-- The bound is computed from width and erased signed face words only. -/
def probeCap (width : Nat) (xs ys : ErasedSpan) : Q' :=
  polynomialCap (polyMul (erasedSpanPolynomial width xs) (erasedSpanPolynomial width ys))

def uniformCap (width : Nat) (xs ys : Span) : Q' :=
  probeCap width (eraseSpan xs) (eraseSpan ys)

theorem uniformCap_nonnegative (width : Nat) (xs ys : Span) :
    (0 : Q') ≤ uniformCap width xs ys :=
  polynomialCap_nonnegative _

theorem uniformCap_relabel (width : Nat) (leftTime rightTime : Nat → Nat) (xs ys : Span) :
    uniformCap width (relabelSpan leftTime xs) (relabelSpan rightTime ys) =
      uniformCap width xs ys := by
  simp only [uniformCap, eraseSpan_relabel]

theorem mixedProduct_cap (width h : Nat) (xs ys : Span) :
    polynomialCap (mixedProduct width h xs ys) = uniformCap width xs ys := by
  apply polynomialCap_congr
  unfold mixedProduct
  apply coefficients_mul_congr
  · rw [coefficients_sourceSpan, eraseSpan_mirror]
  · exact coefficients_sourceSpan width ys

theorem mixedProduct_cap_relabel (width h : Nat) (leftTime rightTime : Nat → Nat)
    (xs ys : Span) :
    polynomialCap (mixedProduct width h (relabelSpan leftTime xs) (relabelSpan rightTime ys)) =
      uniformCap width xs ys :=
  (mixedProduct_cap width h _ _).trans (uniformCap_relabel width leftTime rightTime xs ys)

/-- Actual normalized ratios, with both terminal messages and the same
partition, lie in their constructed polynomial interval. -/
theorem windowRatio_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    -polynomialCap p ≤ windowRatio hw0 hw1 K width hK m L n p ∧
      windowRatio hw0 hw1 K width hK m L n p ≤ polynomialCap p := by
  have hb := windowRatio_later_bounds hw0 hw1 K width hK m L 0 n
    (polynomialInterval ((L+1)*(N width)) p hp) (Nat.zero_le n)
  exact hb

/-- No physical-face hypothesis is needed for the polynomial bound itself;
the reflected form's original-observable domain is a valid specialization. -/
theorem reflectedRatio_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (h m n : Nat)
    (xs ys : Span) (hy : Within h ys) :
    -uniformCap width xs ys ≤ windowRatio hw0 hw1 K width hK m (2*h) n (mixedProduct width h xs ys) ∧
      windowRatio hw0 hw1 K width hK m (2*h) n (mixedProduct width h xs ys) ≤ uniformCap width xs ys := by
  have hb := windowRatio_bounds hw0 hw1 K width hK m (2*h) n (mixedProduct width h xs ys)
    (mixedProduct_supported width h xs ys hy)
  rw [mixedProduct_cap] at hb
  exact hb

/-- The same label-independent bound on the already constructed mixed form. -/
theorem form_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (hx : Within h xs) (hy : Within h ys) (stage : Nat) :
    leEv (ofQ' (-uniformCap width xs ys)) (form hw0 hw1 width h xs ys hx hy stage) ∧
      leEv (form hw0 hw1 width h xs ys hx hy stage) (ofQ' (uniformCap width xs ys)) := by
  have hseq := form_converges hw0 hw1 width h xs ys hx hy stage
  constructor
  · refine leEv_of_ofQ'_limit_le (convergesTo_const _) hseq ?_
    intro epsilon he
    refine ⟨0, fun t _ => ?_⟩
    exact Q'.le_trans' _ _ _
      (reflectedRatio_bounds hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        h t t xs ys hy).1
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))
  · refine leEv_of_ofQ'_limit_le hseq (convergesTo_const _) ?_
    intro epsilon he
    refine ⟨0, fun t _ => ?_⟩
    exact Q'.le_trans' _ _ _
      (reflectedRatio_bounds hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        h t t xs ys hy).2
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))

/-- Intrinsic physical lags select only exponent positions, not this cap. -/
theorem pairing_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan) (stage : Nat) :
    leEv (ofQ' (-uniformCap width xs ys)) (pairing hw0 hw1 width xs ys stage) ∧
      leEv (pairing hw0 hw1 width xs ys stage) (ofQ' (uniformCap width xs ys)) := by
  let H := max (radius xs) (radius ys)
  have hb := form_bounds hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
    (encodeChart_within H xs (Nat.le_max_left _ _))
    (encodeChart_within H ys (Nat.le_max_right _ _)) stage
  simpa only [uniformCap, eraseSpan_encodeChart] using hb

/-- Both presentations may be relabelled independently. The cap contains
neither map and is uniform even when the computed common radius changes. -/
theorem pairing_relabel_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (leftTime rightTime : Nat → Nat) (xs ys : DistanceSpan) (stage : Nat) :
    leEv (ofQ' (-uniformCap width xs ys))
        (pairing hw0 hw1 width (relabelSpan leftTime xs) (relabelSpan rightTime ys) stage) ∧
      leEv (pairing hw0 hw1 width (relabelSpan leftTime xs) (relabelSpan rightTime ys) stage)
        (ofQ' (uniformCap width xs ys)) := by
  have hb := pairing_bounds hw0 hw1 width (relabelSpan leftTime xs) (relabelSpan rightTime ys) stage
  rw [uniformCap_relabel] at hb
  exact hb

end YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_mul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_mul_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_liftBoundary
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.polynomialCap_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.eraseSchedule_relabel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.eraseSpan_relabel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.eraseSpan_mirror
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.eraseSpan_encodeChart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_windowProbe
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_sourceSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_windowProbe_relabel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.coefficients_sourceSpan_relabel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.uniformCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.uniformCap_relabel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.mixedProduct_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.mixedProduct_cap_relabel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.windowRatio_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.reflectedRatio_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.form_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.pairing_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap.pairing_relabel_bounds
