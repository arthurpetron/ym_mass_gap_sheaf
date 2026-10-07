/-
# Original heat curvature with six adaptive polynomial coefficients

Both signs of the actual mixed heat entries construct the lower frozen
Hessian bound for arbitrary supported polynomial coefficients. All ordered
cross terms remain. The coefficient count is six rotations at ONE block,
not the number of active blocks. No derivative acts on a coefficient.

This supplies the local adaptive input missing from the rational-direction
API. Whole-product assembly, conditional Gram/order reflection, the actual
weighted score estimate and scaling control remain separate obligations.
-/

import YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope
import YMGap.Continuum.SU2QuaternionHeatLogCurvature

namespace YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt)
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff)
open YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope

/-- Fixed order of the six unoriented coordinate-plane rotations. -/
def sixPlane (i : Fin 6) : Fin 4 × Fin 4 :=
  match i.val with
  | 0 => (⟨0, by decide⟩, ⟨1, by decide⟩)
  | 1 => (⟨0, by decide⟩, ⟨2, by decide⟩)
  | 2 => (⟨0, by decide⟩, ⟨3, by decide⟩)
  | 3 => (⟨1, by decide⟩, ⟨2, by decide⟩)
  | 4 => (⟨1, by decide⟩, ⟨3, by decide⟩)
  | _ => (⟨2, by decide⟩, ⟨3, by decide⟩)

/-- The original ordered mixed log-Hessian entry at the selected block. -/
def frozenSixEntry (s : Nat) (h : RatPoly) (i j : Fin 6) : RatPoly :=
  logHessianNumerator h
    (4*s+(sixPlane i).1.val) (4*s+(sixPlane i).2.val)
    (4*s+(sixPlane j).1.val) (4*s+(sixPlane j).2.val)

/-- Explicit frozen quadratic form: no coefficient is differentiated. -/
def frozenSixHeatEnvelope (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K a b s : Nat) (u : Fin 6 → RatPoly) : RatPoly :=
  let h := heatAt a b w K
  matrixEnvelope (polyMul (cap (logCurvatureCap w hw0 hw1)) (polyMul h h))
    u (frozenSixEntry s h)

/-- Constructed lower frozen-direction curvature on the ORIGINAL factor.
The polynomial coefficients may depend on the very coordinates rotated;
the claim remains the frozen matrix sum, not a variable-field square. -/
def heat_frozen_six_curvature_certificate
    {blocks a b s : Nat} (ha : a < blocks) (hb : b < blocks) (hs : s < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (u : Fin 6 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (frozenSixHeatEnvelope w hw0 hw1 K a b s u) := by
  apply six_polynomial_matrix_envelope_certificate _ u _ hu
  · intro i j
    exact (heatLogHessianBounds ha hb hs hs
      (sixPlane i).1.isLt (sixPlane i).2.isLt
      (sixPlane j).1.isLt (sixPlane j).2.isLt hw0 hw1 K hK).1
  · intro i j
    exact (heatLogHessianBounds ha hb hs hs
      (sixPlane i).1.isLt (sixPlane i).2.isLt
      (sixPlane j).1.isLt (sixPlane j).2.isLt hw0 hw1 K hK).2

end YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature

#print axioms YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature.heat_frozen_six_curvature_certificate
