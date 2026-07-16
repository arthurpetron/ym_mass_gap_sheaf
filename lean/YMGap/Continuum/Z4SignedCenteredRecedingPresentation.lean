/-
# Conditional receding-centered evaluation of signed cylinder presentations

A signed centered chart of radius `r` already carries canonical roots in the
corner box of side `2*r+1`.  We feed those roots to the rational centered
diagonal with base `2*r+1`.  Geometrically this merely chooses a (deliberately
non-minimal) centered exhaustion around the signed origin of the chart; no new
finite amplitude is introduced.

The physical thermodynamic input remains the named proposition
`SignedCenteredPresentationVolumeModulus`.  From it we construct a Bishop
`CReal`.  A second named proposition,
`SignedCenteredPresentationComparisonModulus`, is the exact stagewise datum
needed to identify two signed presentations.  Translation of a chart changes
only its signed center, so its rational diagonal is termwise identical and
full `Int^4` covariance follows conditionally without an additional physical
assumption.

Nothing in this file inhabits either physical modulus or asserts an
unconditional infinite-volume state.
-/

import YMGap.Constructive.CRealAdd
import YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
import YMGap.Continuum.Z4SignedCenteredRecedingDiagonal

namespace YMGap.Continuum.Z4SignedCenteredRecedingPresentation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The signed chart carried by the existing rational diagonal -/

/-- The corner-box side carried by a signed centered chart. -/
def signedCenteredPresentationDiagonalBase
    (presentation : SignedCenteredCylinderPresentation) : Nat :=
  centeredBoxBase presentation.chart.radius

/-- The actual exact-rational stage law attached to a signed presentation. -/
def couplingParametricSignedCenteredPresentationSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (presentation : SignedCenteredCylinderPresentation)
    (stage : Nat) : Q' :=
  couplingParametricCenteredRecedingCylinderSequence
    coupling hcoupling
    (signedCenteredPresentationDiagonalBase presentation)
    presentation.chart.roots presentation.predicate stage

/-- The precise physical input required for the presentation's receding
diagonal.  This is an alias of the uninhabited volume modulus, not an axiom. -/
def SignedCenteredPresentationVolumeModulus
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (presentation : SignedCenteredCylinderPresentation) : Prop :=
  CenteredRecedingVolumeModulus coupling hcoupling
    (signedCenteredPresentationDiagonalBase presentation)
    presentation.chart.roots presentation.predicate

theorem signedCenteredPresentation_rootsCanonical
    (presentation : SignedCenteredCylinderPresentation) :
    ∀ root, root ∈ presentation.chart.roots →
      root ∈ canonicalSurfacePolymers
        (signedCenteredPresentationDiagonalBase presentation) := by
  exact presentation.chart.rootsCanonical

theorem signedCenteredPresentationVolumeModulus_rootsCanonical
    {coupling : Q'} {hcoupling : (0 : Q') ≤ coupling}
    {presentation : SignedCenteredCylinderPresentation}
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation) :
    ∀ root, root ∈ presentation.chart.roots →
      root ∈ canonicalSurfacePolymers
        (signedCenteredPresentationDiagonalBase presentation) := by
  exact hvolume.1

/-- The signed displacement which identifies the chart's relative centered
coordinates with the nonnegative corner coordinates consumed by the rational
diagonal. -/
def signedCenteredChartDiagonalOrigin
    (chart : SignedCenteredCylinderChart) : SignedZ4Vector :=
  signedAdd chart.center
    (signedNeg
      ((Int.ofNat chart.radius, Int.ofNat chart.radius,
        Int.ofNat chart.radius, Int.ofNat chart.radius) : SignedZ4Vector))

theorem signedTranslate_from_diagonalOrigin
    (chart : SignedCenteredCylinderChart)
    (plaquette : ClusterCount4DProgress.Z4Plaq) :
    signedTranslatePlaquette (signedCenteredChartDiagonalOrigin chart)
        (natPlaquetteToSigned plaquette) =
      signedTranslatePlaquette chart.center
        (natPlaquetteToCenteredSigned chart.radius plaquette) := by
  rcases chart with ⟨⟨ca, cb, cc, cd⟩, radius, roots, hroots⟩
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  apply Prod.ext
  · simp only [signedCenteredChartDiagonalOrigin, signedTranslatePlaquette,
      signedTranslateVertex, signedAdd, signedNeg, natPlaquetteToSigned,
      natVertexToSigned, natPlaquetteToCenteredSigned,
      natVertexToCenteredSigned, natCoordinateToCenteredSigned,
      Int.ofNat_eq_natCast]
    simp only [Int.sub_eq_add_neg, Int.add_left_comm, Int.add_comm]
  · rfl

/-- The roots passed to the diagonal represent exactly the chart's signed
geometric supports after translating by the explicit chart origin. -/
theorem signedCanonicalRootSupport_translate_diagonalOrigin
    (chart : SignedCenteredCylinderChart) (root : List Nat) :
    (signedCanonicalRootSupport (centeredBoxBase chart.radius) root).map
        (signedTranslatePlaquette
          (signedCenteredChartDiagonalOrigin chart)) =
      chart.rootSupport root := by
  unfold signedCanonicalRootSupport
    SignedCenteredCylinderChart.rootSupport
  rw [List.map_map]
  apply List.map_congr_left
  intro plaquette _
  simp only [Function.comp_apply]
  exact signedTranslate_from_diagonalOrigin chart plaquette

theorem couplingParametricSignedCenteredPresentationSequence_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (presentation : SignedCenteredCylinderPresentation) (stage : Nat) :
    (0 : Q') ≤ couplingParametricSignedCenteredPresentationSequence
      coupling hcoupling presentation stage := by
  exact couplingParametricCenteredRecedingCylinderSequence_nonnegative
    hcoupling (signedCenteredPresentationDiagonalBase presentation)
      presentation.chart.roots presentation.predicate stage

theorem couplingParametricSignedCenteredPresentationSequence_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (presentation : SignedCenteredCylinderPresentation) (stage : Nat) :
    couplingParametricSignedCenteredPresentationSequence
        coupling hcoupling presentation stage ≤ (1 : Q') := by
  exact couplingParametricCenteredRecedingCylinderSequence_le_one
    hcoupling (signedCenteredPresentationDiagonalBase presentation)
      presentation.chart.roots presentation.predicate stage

/-! ## 2. Conditional constructive-real evaluation -/

def couplingParametricSignedCenteredPresentationValueOfVolumeModulus
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation)
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation) : CReal :=
  couplingParametricCenteredRecedingCylinderLimitOfVolumeModulus
    coupling hcoupling hle presentation.predicate hvolume

@[simp] theorem couplingParametricSignedCenteredPresentationValue_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation)
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation) (stage : Nat) :
    (couplingParametricSignedCenteredPresentationValueOfVolumeModulus
      coupling hcoupling hle presentation hvolume).approx stage =
      couplingParametricSignedCenteredPresentationSequence
        coupling hcoupling presentation stage := rfl

theorem couplingParametricSignedCenteredPresentationValue_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation)
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation) :
    CReal.ofQ' 0 ≤
      couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle presentation hvolume := by
  exact couplingParametricCenteredRecedingCylinderLimit_nonnegative
    hcoupling hle presentation.predicate hvolume

theorem couplingParametricSignedCenteredPresentationValue_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation)
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation) :
    couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle presentation hvolume ≤ CReal.ofQ' 1 := by
  exact couplingParametricCenteredRecedingCylinderLimit_le_one
    hcoupling hle presentation.predicate hvolume

/-! ## 3. Exact ignored-coordinate refinement -/

def signedCenteredCylinderChartAppendRoots
    (chart : SignedCenteredCylinderChart)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers (centeredBoxBase chart.radius)) :
    SignedCenteredCylinderChart where
  center := chart.center
  radius := chart.radius
  roots := chart.roots ++ extra
  rootsCanonical := by
    intro root hroot
    rcases List.mem_append.mp hroot with hleft | hright
    · exact chart.rootsCanonical root hleft
    · exact hextra root hright

def signedCenteredCylinderPresentationAppendIgnored
    (presentation : SignedCenteredCylinderPresentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers
        (centeredBoxBase presentation.chart.radius)) :
    SignedCenteredCylinderPresentation where
  chart := signedCenteredCylinderChartAppendRoots
    presentation.chart extra hextra
  predicate := extendCylinderPredicate
    presentation.chart.roots.length presentation.predicate

theorem centeredRecedingStageRoots_append
    (base stage : Nat) (roots extra : List (List Nat)) :
    centeredRecedingStageRoots base stage (roots ++ extra) =
      centeredRecedingStageRoots base stage roots ++
        centeredRecedingStageRoots base stage extra := by
  simp [centeredRecedingStageRoots, centeredOffsetCylinderRoots]

theorem centeredRecedingCylinderEvent_appendIgnored
    (base stage : Nat) (roots extra : List (List Nat))
    (predicate : List Bool → Bool) :
    centeredRecedingCylinderEvent base stage (roots ++ extra)
        (extendCylinderPredicate roots.length predicate) =
      centeredRecedingCylinderEvent base stage roots predicate := by
  unfold centeredRecedingCylinderEvent
  rw [centeredRecedingStageRoots_append]
  rw [← centeredRecedingStageRoots_length base stage roots]
  exact cylinderEvent_append_extend _ _ _

theorem couplingParametricSignedCenteredPresentationSequence_appendIgnored
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (presentation : SignedCenteredCylinderPresentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers
        (centeredBoxBase presentation.chart.radius))
    (stage : Nat) :
    couplingParametricSignedCenteredPresentationSequence coupling hcoupling
        (signedCenteredCylinderPresentationAppendIgnored
          presentation extra hextra) stage =
      couplingParametricSignedCenteredPresentationSequence coupling hcoupling
        presentation stage := by
  unfold couplingParametricSignedCenteredPresentationSequence
    signedCenteredPresentationDiagonalBase
    signedCenteredCylinderPresentationAppendIgnored
    signedCenteredCylinderChartAppendRoots
    couplingParametricCenteredRecedingCylinderSequence
  simp only
  rw [centeredRecedingCylinderEvent_appendIgnored]

theorem spinSummedCylinderBoundaryCoefficient_mono
    {smaller larger : Nat} (hcount : smaller ≤ larger) :
    spinSummedCylinderBoundaryCoefficient smaller ≤
      spinSummedCylinderBoundaryCoefficient larger := by
  unfold spinSummedCylinderBoundaryCoefficient
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.ofNat_le_ofNat hcount)
    (Q'.zero_le_add _ _
      (ExpNeg.ofNat_nonneg' 2) (ExpNeg.ofNat_nonneg' 2))

/-- Appending ignored coordinates does not require a new physical estimate:
the finite event is exactly the old event, and the larger root-count
coefficient only weakens the supplied bound. -/
theorem signedCenteredPresentationVolumeModulus_appendIgnored
    {coupling : Q'} {hcoupling : (0 : Q') ≤ coupling}
    {presentation : SignedCenteredCylinderPresentation}
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers
        (centeredBoxBase presentation.chart.radius)) :
    SignedCenteredPresentationVolumeModulus coupling hcoupling
      (signedCenteredCylinderPresentationAppendIgnored
        presentation extra hextra) := by
  change CenteredRecedingVolumeModulus coupling hcoupling
    (centeredBoxBase presentation.chart.radius)
    (presentation.chart.roots ++ extra)
    (extendCylinderPredicate presentation.chart.roots.length
      presentation.predicate)
  change CenteredRecedingVolumeModulus coupling hcoupling
    (centeredBoxBase presentation.chart.radius)
    presentation.chart.roots presentation.predicate at hvolume
  constructor
  · intro root hroot
    rcases List.mem_append.mp hroot with hleft | hright
    · exact hvolume.1 root hleft
    · exact hextra root hright
  · intro cutoff earlier later hstage
    have hraw := hvolume.2 cutoff hstage
    rw [centeredRecedingCylinderEvent_appendIgnored,
      centeredRecedingCylinderEvent_appendIgnored]
    refine Q'.le_trans' _ _ _ hraw ?_
    apply Q'.mul_le_mul_of_nonneg_right
    · apply spinSummedCylinderBoundaryCoefficient_mono
      simp only [List.length_append]
      omega
    · exact Q'.pow_nonneg HalfPow.half (by decide) earlier

private theorem equiv_ofQ'_of_eqv_refinement_local {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hepsilon))

private theorem creal_equiv_of_approx_eqv_refinement_local {A B : CReal}
    (h : ∀ stage, A.approx stage ≈ B.approx stage) :
    CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal
    (fun stage => equiv_ofQ'_of_eqv_refinement_local (h stage))

theorem couplingParametricSignedCenteredPresentationValue_appendIgnored
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation)
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers
        (centeredBoxBase presentation.chart.radius)) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle
        (signedCenteredCylinderPresentationAppendIgnored
          presentation extra hextra)
        (signedCenteredPresentationVolumeModulus_appendIgnored
          hvolume extra hextra))
      (couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle presentation hvolume) := by
  apply creal_equiv_of_approx_eqv_refinement_local
  intro stage
  exact Q'.eqv_of_eq
    (couplingParametricSignedCenteredPresentationSequence_appendIgnored
      hcoupling presentation extra hextra stage)

/-! ## 4. Explicit stagewise comparison input and CReal descent -/

def signedCenteredPresentationComparisonCoefficient
    (left right : SignedCenteredCylinderPresentation) : Q' :=
  spinSummedJointCylinderCoefficient left.chart.roots.length +
    spinSummedJointCylinderCoefficient right.chart.roots.length

theorem signedCenteredPresentationComparisonCoefficient_nonnegative
    (left right : SignedCenteredCylinderPresentation) :
    (0 : Q') ≤ signedCenteredPresentationComparisonCoefficient left right := by
  unfold signedCenteredPresentationComparisonCoefficient
  exact Q'.zero_le_add _ _
    (spinSummedJointCylinderCoefficient_nonnegative
      left.chart.roots.length)
    (spinSummedJointCylinderCoefficient_nonnegative
      right.chart.roots.length)

/-- A rational-stage comparison sufficient to identify two conditional
limits.  Supplying this proposition is physical work; it is not constructed
here from semantic presentation equivalence. -/
def SignedCenteredPresentationComparisonModulus
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (left right : SignedCenteredCylinderPresentation) : Prop :=
  ∀ stage,
    Q'.abs
        (couplingParametricSignedCenteredPresentationSequence
            coupling hcoupling left stage -
          couplingParametricSignedCenteredPresentationSequence
            coupling hcoupling right stage) ≤
      signedCenteredPresentationComparisonCoefficient left right *
        HalfPow.half ^ stage

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

theorem couplingParametricSignedCenteredPresentationValue_equiv_of_comparison
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {left right : SignedCenteredCylinderPresentation}
    (hleft : SignedCenteredPresentationVolumeModulus
      coupling hcoupling left)
    (hright : SignedCenteredPresentationVolumeModulus
      coupling hcoupling right)
    (hcompare : SignedCenteredPresentationComparisonModulus
      coupling hcoupling left right) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle left hleft)
      (couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle right hright) := by
  intro epsilon hepsilon
  let coefficient := signedCenteredPresentationComparisonCoefficient left right
  let scaledTolerance := epsilon * Q'.invSucc coefficient.num.toNat
  have hcoefficient : (0 : Q') ≤ coefficient :=
    signedCenteredPresentationComparisonCoefficient_nonnegative left right
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
  have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
      hcoefficient (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ stage) scaledTolerance coefficient
    (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
  have habs : Q'.abs
      (couplingParametricSignedCenteredPresentationSequence
          coupling hcoupling left stage -
        couplingParametricSignedCenteredPresentationSequence
          coupling hcoupling right stage) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hcompare stage)
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

/-! ## 5. Full signed translation covariance of the conditional diagonal -/

theorem couplingParametricSignedCenteredPresentationSequence_translate
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (shift : SignedZ4Vector)
    (presentation : SignedCenteredCylinderPresentation) (stage : Nat) :
    couplingParametricSignedCenteredPresentationSequence
        coupling hcoupling (presentation.translate shift) stage =
      couplingParametricSignedCenteredPresentationSequence
        coupling hcoupling presentation stage := by
  cases presentation
  rfl

theorem signedCenteredPresentationVolumeModulus_translate
    {coupling : Q'} {hcoupling : (0 : Q') ≤ coupling}
    (shift : SignedZ4Vector)
    {presentation : SignedCenteredCylinderPresentation}
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation) :
    SignedCenteredPresentationVolumeModulus coupling hcoupling
      (presentation.translate shift) := by
  cases presentation
  exact hvolume

private theorem equiv_ofQ'_of_eqv_local {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hepsilon))

private theorem creal_equiv_of_approx_eqv_local {A B : CReal}
    (h : ∀ stage, A.approx stage ≈ B.approx stage) :
    CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal
    (fun stage => equiv_ofQ'_of_eqv_local (h stage))

/-- Conditional covariance under every signed `Int^4` translation.  The
translated volume modulus is the same datum definitionally because the
rational law uses coordinates relative to the translated center. -/
theorem couplingParametricSignedCenteredPresentationValue_translate
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (shift : SignedZ4Vector)
    (presentation : SignedCenteredCylinderPresentation)
    (hvolume : SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle (presentation.translate shift)
        (signedCenteredPresentationVolumeModulus_translate shift hvolume))
      (couplingParametricSignedCenteredPresentationValueOfVolumeModulus
        coupling hcoupling hle presentation hvolume) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact Q'.eqv_of_eq
    (couplingParametricSignedCenteredPresentationSequence_translate
      hcoupling shift presentation stage)

#print axioms signedCenteredPresentation_rootsCanonical
#print axioms signedTranslate_from_diagonalOrigin
#print axioms signedCanonicalRootSupport_translate_diagonalOrigin
#print axioms couplingParametricSignedCenteredPresentationSequence_nonnegative
#print axioms couplingParametricSignedCenteredPresentationSequence_le_one
#print axioms couplingParametricSignedCenteredPresentationValueOfVolumeModulus
#print axioms couplingParametricSignedCenteredPresentationValue_nonnegative
#print axioms couplingParametricSignedCenteredPresentationValue_le_one
#print axioms centeredRecedingCylinderEvent_appendIgnored
#print axioms spinSummedCylinderBoundaryCoefficient_mono
#print axioms signedCenteredPresentationVolumeModulus_appendIgnored
#print axioms couplingParametricSignedCenteredPresentationValue_appendIgnored
#print axioms signedCenteredPresentationComparisonCoefficient_nonnegative
#print axioms couplingParametricSignedCenteredPresentationValue_equiv_of_comparison
#print axioms couplingParametricSignedCenteredPresentationSequence_translate
#print axioms signedCenteredPresentationVolumeModulus_translate
#print axioms couplingParametricSignedCenteredPresentationValue_translate

end YMGap.Continuum.Z4SignedCenteredRecedingPresentation
