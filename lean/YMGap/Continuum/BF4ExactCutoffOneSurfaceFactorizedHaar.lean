/-
# Factorized exact Haar certificate for the cutoff-one BF4 surfaces

This module connects the literal 72-face/116-link corrected-slab surface
network and its already-proved five-based-cycle marginal to the constructive
factorized Haar evaluator.  It exposes the remaining finite campaign as one
explicit Boolean calculation over the certified list of 128 closed surfaces.

The six-face sphere is evaluated by the same contractor on its proved
five-chord word, supplying a small end-to-end regression certificate.

## Axiom gate

Finite lists and the audited factorized Haar theorem only.  No Classical.*,
native_decide, sorry, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
import YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The literal plaquette-character factors, kept separate rather than
expanded into their exponentially larger monolithic product. -/
def correctedSlabSpinNetworkFactors
    (extent : Nat)
    (faceLabel :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    List RatPoly :=
  (boundaryCompleteSlabPlaquettes extent).map
    (correctedSlabPlaquetteSpinFactor extent faceLabel)

private theorem factorProduct_map
    (factor : α → RatPoly) : ∀ items : List α,
    factorProduct (items.map factor) =
      items.foldr (fun item total => polyMul (factor item) total) polyOne
  | [] => rfl
  | _ :: rest => by
      simp only [List.map_cons, factorProduct, List.foldr]
      rw [factorProduct_map factor rest]

/-- The factor list is definitionally faithful to the original corrected-slab
integrand; no analytic or algebraic quotient is used at this seam. -/
theorem factorProduct_correctedSlabSpinNetworkFactors
    (extent : Nat)
    (faceLabel :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    factorProduct (correctedSlabSpinNetworkFactors extent faceLabel) =
      exactCorrectedSlabSpinNetworkIntegrand extent faceLabel := by
  unfold correctedSlabSpinNetworkFactors
    exactCorrectedSlabSpinNetworkIntegrand
  exact factorProduct_map
    (correctedSlabPlaquetteSpinFactor extent faceLabel)
    (boundaryCompleteSlabPlaquettes extent)

/-- Executable factorized value of one literal embedded closed surface. -/
def embeddedSurfaceFactorizedHaar (compactMask : Nat) : Q' :=
  compactFactorizedHaar (boundaryCompleteSlabLinks 1).length
    (correctedSlabSpinNetworkFactors 1
      (embeddedSurfaceLabelling compactMask))

theorem exactCorrectedSlabHaarCoefficient_eq_factorized
    (extent : Nat)
    (faceLabel :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    exactCorrectedSlabHaarCoefficient extent faceLabel ≈
      compactFactorizedHaar (boundaryCompleteSlabLinks extent).length
        (correctedSlabSpinNetworkFactors extent faceLabel) := by
  unfold exactCorrectedSlabHaarCoefficient
  rw [← factorProduct_correctedSlabSpinNetworkFactors]
  exact quaternionHaar_eq_compactFactorizedHaar
    (boundaryCompleteSlabLinks extent).length _

/-- The factorized evaluator is exactly the original 116-link coefficient. -/
theorem exactEmbeddedSurfaceHaarCoefficient_eq_factorized
    (compactMask : Nat) :
    exactCorrectedSlabHaarCoefficient 1
        (embeddedSurfaceLabelling compactMask) ≈
      embeddedSurfaceFactorizedHaar compactMask := by
  exact exactCorrectedSlabHaarCoefficient_eq_factorized 1
    (embeddedSurfaceLabelling compactMask)

/-- Consequently the actual five-based-cycle marginal and the factorized
116-link evaluation are the same exact rational number. -/
theorem embeddedSurfaceBasedCycleFive_eq_factorized
    (compactMask : Nat) :
    quaternionHaar 5
        (embeddedSurfaceBasedCycleFivePolynomial compactMask) ≈
      embeddedSurfaceFactorizedHaar compactMask := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (exactEmbeddedSurfaceHaarCoefficient_eq_basedCycleFive compactMask))
    (exactEmbeddedSurfaceHaarCoefficient_eq_factorized compactMask)

/-- Exact reduction of the original surface-amplitude bridge to the 128
factorized values.  Each premise is now an evaluator statement, with no
remaining 116-link product expansion. -/
theorem cutoffOneClosedSurfaceTopologicalAmplitude_of_factorized
    (hfactorized : ∀ compactMask : Nat,
      compactMask ∈ binarySurfaceMasks →
      embeddedSurfaceFactorizedHaar compactMask ≈
        surfaceTopologicalHaarAmplitude compactMask) :
    CutoffOneClosedSurfaceTopologicalAmplitude := by
  apply cutoffOneClosedSurfaceTopologicalAmplitude_of_basedCycleFive
  intro compactMask hmem
  exact Q'.eqv_trans _ _ _
    (embeddedSurfaceBasedCycleFive_eq_factorized compactMask)
    (hfactorized compactMask hmem)

/-! ### Checked six-face regression on the five actual chord variables -/

def sixFaceSphereFiveChordFactors : List RatPoly :=
  sixFaceSphereFiveChordWords.map compactFundamentalWordFactor

theorem factorProduct_sixFaceSphereFiveChordFactors :
    factorProduct sixFaceSphereFiveChordFactors =
      sixFaceSphereFiveChordPolynomial := by
  unfold sixFaceSphereFiveChordFactors sixFaceSphereFiveChordPolynomial
  exact factorProduct_map compactFundamentalWordFactor
    sixFaceSphereFiveChordWords

theorem sixFaceSphereFactorizedHaar_exact :
    factorizedHaar 5 sixFaceSphereFiveChordFactors ≈
      surfaceTopologicalHaarAmplitude 2167232 := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (quaternionHaar_eq_factorizedHaar 5
        sixFaceSphereFiveChordFactors))
    (by
      rw [factorProduct_sixFaceSphereFiveChordFactors]
      exact sixFaceSphereFiveChordHaar_exact)

theorem sixFaceSphereFiveChordHaar_factorized_exact :
    quaternionHaar 5 sixFaceSphereFiveChordPolynomial ≈
      surfaceTopologicalHaarAmplitude 2167232 := by
  rw [← factorProduct_sixFaceSphereFiveChordFactors]
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_eq_factorizedHaar 5
      sixFaceSphereFiveChordFactors)
    sixFaceSphereFactorizedHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar.exactEmbeddedSurfaceHaarCoefficient_eq_factorized
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar.embeddedSurfaceBasedCycleFive_eq_factorized
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar.cutoffOneClosedSurfaceTopologicalAmplitude_of_factorized
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar.sixFaceSphereFiveChordHaar_factorized_exact
