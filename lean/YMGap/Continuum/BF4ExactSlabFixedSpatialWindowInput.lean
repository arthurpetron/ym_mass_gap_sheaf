/-
# Linear boundary-input functionals for the actual observed window

The numerator J(h) pairs the actual half-open observed-window message with
the finite terminal message u_n under the original V-weighted Haar mass.
The comparison mass Z(h) uses the SAME window with no observation, namely
T^L h. Both are rational-linear in the boundary input, with arbitrary signed
scalars and no support premise needed for these algebraic identities.

A supported certified input has Z(h) >= 0, including Z(h) = 0. The computed
window interval gives -c*Z(h) <= J(h) <= c*Z(h), without dividing by Z(h),
requiring strict positivity, or changing any action factor. These bounds
apply to certified residuals in boundary comparisons. No stationary law,
geometric observable identification, reflected OS or mass-gap claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
import YMGap.Continuum.SU2QuaternionHeadWindowBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepWeightCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (iterateStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
  (weightedMass_congr weightedMass_add weightedMass_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem windowMessage_input_swap (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) (f p : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight L f p)
      (windowMessage blocks kernel weight L p f) :=
  partialHaarHeads_congr (L*blocks)
    ((RatPolyCoeffEqv.mul_comm f p).mul_right (halfOpenAction blocks kernel weight L))

/-- Exact input congruence with the full observed window retained. -/
theorem windowMessage_input_congr (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) {f g : RatPoly} (h : RatPolyCoeffEqv f g) (p : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight L f p)
      (windowMessage blocks kernel weight L g p) :=
  partialHaarHeads_congr (L*blocks)
    ((h.mul_right p).mul_right (halfOpenAction blocks kernel weight L))

/-- Input additivity is independent of the support or sign of the probe. -/
theorem windowMessage_input_add (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) (f g p : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight L (polyAdd f g) p)
      (polyAdd (windowMessage blocks kernel weight L f p)
        (windowMessage blocks kernel weight L g p)) :=
  (windowMessage_input_swap blocks kernel weight L (polyAdd f g) p).trans
    ((windowMessage_add blocks kernel weight L p f g).trans
      ((windowMessage_input_swap blocks kernel weight L f p).symm.add
        (windowMessage_input_swap blocks kernel weight L g p).symm))

/-- Arbitrary signed rational homogeneity in the boundary input. -/
theorem windowMessage_input_smul (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) (c : Q') (f p : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight L (polySmul c f) p)
      (polySmul c (windowMessage blocks kernel weight L f p)) :=
  (windowMessage_input_swap blocks kernel weight L (polySmul c f) p).trans
    ((windowMessage_smul blocks kernel weight L p c f).trans
      ((windowMessage_input_swap blocks kernel weight L f p).symm.smul c))

/-- Unnormalized numerator of the actual window with boundary input h. -/
def inputNumerator (w : Q') (K width L n : Nat) (h p : RatPoly) : Q' :=
  weightedMass w K width
    (polyMul (windowMessage (N width) (kineticWeight w K width) (spatialWeight w K width) L h p)
      (terminalMessage w K width n))

/-- Unobserved mass of the SAME window and terminal message. -/
def inputPartition (w : Q') (K width L n : Nat) (h : RatPoly) : Q' :=
  weightedMass w K width
    (polyMul (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) L h)
      (terminalMessage w K width n))

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks terminalMessage

private theorem pairing_add (w : Q') (K width : Nat) (f g r : RatPoly) :
    weightedMass w K width (polyMul (polyAdd f g) r) ≈
      weightedMass w K width (polyMul f r) + weightedMass w K width (polyMul g r) := by
  rw [polyMul_add_left_exact]
  exact weightedMass_add w K width _ _

private theorem pairing_smul (w : Q') (K width : Nat) (c : Q') (f r : RatPoly) :
    weightedMass w K width (polyMul (polySmul c f) r) ≈
      c * weightedMass w K width (polyMul f r) :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_left c f r))
    (weightedMass_smul w K width c _)

theorem inputNumerator_congr (w : Q') (K width L n : Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) (p : RatPoly) :
    inputNumerator w K width L n f p ≈ inputNumerator w K width L n g p :=
  weightedMass_congr w K width
    ((windowMessage_input_congr (N width) (kineticWeight w K width) (spatialWeight w K width) L h p).mul_right
      (terminalMessage w K width n))

theorem inputNumerator_add (w : Q') (K width L n : Nat) (f g p : RatPoly) :
    inputNumerator w K width L n (polyAdd f g) p ≈
      inputNumerator w K width L n f p + inputNumerator w K width L n g p :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width
      ((windowMessage_input_add (N width) (kineticWeight w K width) (spatialWeight w K width) L f g p).mul_right
        (terminalMessage w K width n)))
    (pairing_add w K width _ _ _)

theorem inputNumerator_smul (w : Q') (K width L n : Nat) (c : Q') (f p : RatPoly) :
    inputNumerator w K width L n (polySmul c f) p ≈ c * inputNumerator w K width L n f p :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width
      ((windowMessage_input_smul (N width) (kineticWeight w K width) (spatialWeight w K width) L c f p).mul_right
        (terminalMessage w K width n)))
    (pairing_smul w K width c _ _)

/-- The unit probe identifies numerator and partition coefficient-sensitively. -/
theorem inputNumerator_one (w : Q') (K width L n : Nat) (f : RatPoly) :
    inputNumerator w K width L n f polyOne ≈ inputPartition w K width L n f :=
  weightedMass_congr w K width
    ((windowMessage_one (N width) (kineticWeight w K width) (spatialWeight w K width) L f).mul_right
      (terminalMessage w K width n))

theorem inputPartition_congr (w : Q') (K width L n : Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) :
    inputPartition w K width L n f ≈ inputPartition w K width L n g :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (inputNumerator_one w K width L n f))
    (Q'.eqv_trans _ _ _ (inputNumerator_congr w K width L n h polyOne)
      (inputNumerator_one w K width L n g))

theorem inputPartition_add (w : Q') (K width L n : Nat) (f g : RatPoly) :
    inputPartition w K width L n (polyAdd f g) ≈
      inputPartition w K width L n f + inputPartition w K width L n g :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (inputNumerator_one w K width L n (polyAdd f g)))
    (Q'.eqv_trans _ _ _ (inputNumerator_add w K width L n f g polyOne)
      (Q'.add_eqv_congr' (inputNumerator_one w K width L n f) (inputNumerator_one w K width L n g)))

theorem inputPartition_smul (w : Q') (K width L n : Nat) (c : Q') (f : RatPoly) :
    inputPartition w K width L n (polySmul c f) ≈ c * inputPartition w K width L n f :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (inputNumerator_one w K width L n (polySmul c f)))
    (Q'.eqv_trans _ _ _ (inputNumerator_smul w K width L n c f polyOne)
      (Q'.mul_eqv_congr_left c _ _ (inputNumerator_one w K width L n f)))

/-- No strict-positive input mass is required: zero-mass certified residuals
remain admissible for this unnormalized comparison. -/
theorem inputPartition_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat) {h : RatPoly}
    (hh : SupportedQuaternionBlocks (N width) h) (H : Certificate (N width) h) :
    (0 : Q') ≤ inputPartition w K width L n h :=
  weightedMass_nonnegative hw0 hw1 K width hK
    ((iterateStep_certificate hw0 hw1 K width hK L h hh H).mul
      (terminalMessage_certificate hw0 hw1 K width hK n))

/-- The full-window cap bounds the actual numerator by the SAME unobserved
mass. This statement also applies when that comparison mass is zero. -/
theorem inputNumerator_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat) {h p : RatPoly} {c : Q'}
    (hh : SupportedQuaternionBlocks (N width) h) (H : Certificate (N width) h)
    (I : Interval ((L+1)*(N width)) p c) :
    -(c * inputPartition w K width L n h) ≤ inputNumerator w K width L n h p ∧
      inputNumerator w K width L n h p ≤ c * inputPartition w K width L n h := by
  have U := windowMessage_upper_certificate (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK) L hh H I
  have D := windowMessage_lower_certificate (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK) L hh H I
  have R := terminalMessage_certificate hw0 hw1 K width hK n
  have hu : (0 : Q') ≤ c * inputPartition w K width L n h + -(inputNumerator w K width L n h p) :=
    Q'.le_trans' _ _ _ (weightedMass_nonnegative hw0 hw1 K width hK (U.mul R))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (pairing_add w K width _ _ _)
        (Q'.add_eqv_congr' (pairing_smul w K width c _ _)
          (Q'.eqv_trans _ _ _ (pairing_smul w K width (-1) _ _)
            (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
              (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))))
  have hl : (0 : Q') ≤ inputNumerator w K width L n h p + c * inputPartition w K width L n h :=
    Q'.le_trans' _ _ _ (weightedMass_nonnegative hw0 hw1 K width hK (D.mul R))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (pairing_add w K width _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (pairing_smul w K width c _ _))))
  exact ⟨Q'.neg_le_of_zero_le_add hl, Q'.le_of_sub_nonneg hu⟩

/-- Absolute-value form, without a positive-mass hypothesis or normalization. -/
theorem inputNumerator_abs_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (L n : Nat) {h p : RatPoly} {c : Q'}
    (hh : SupportedQuaternionBlocks (N width) h) (H : Certificate (N width) h)
    (I : Interval ((L+1)*(N width)) p c) :
    Q'.abs (inputNumerator w K width L n h p) ≤ c * inputPartition w K width L n h :=
  let B := inputNumerator_bounds hw0 hw1 K width hK L n hh H I
  Q'.abs_le B.1 B.2

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.windowMessage_input_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.windowMessage_input_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.windowMessage_input_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputNumerator_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputNumerator_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputNumerator_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputNumerator_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputPartition_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputPartition_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputPartition_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputPartition_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputNumerator_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput.inputNumerator_abs_le
