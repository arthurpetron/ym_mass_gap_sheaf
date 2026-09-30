/-
# The actual conditional division preserves polynomial gauge invariance

The existing vertex-gauge predicate is closed under physical conditional
Haar integration. Hence the ORIGINAL incident normalizer, inserted
numerator and every polynomial inverse iterate retain that predicate.
No substitute weight, inverse or gauge-fixed measure is introduced.

This supplies the dense approximants needed for a completed invariant-sector
join. It does not define that completed sector or prove a useful signed
covariance estimate, scaling bound, OS transfer or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionGaugeFamilyProjection
import YMGap.Continuum.SU2QuaternionLiftedFamilyProjection
import YMGap.Continuum.BF4ExactSlabVertexGaugeAction
import YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
import YMGap.Continuum.BF4ExactSlabBlockOriginalConditional

namespace YMGap.Continuum.BF4ExactSlabGaugeConditionalApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
open YMGap.Continuum.BF4ExactSlabVertexGaugeAction
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarCarrierProjection
open YMGap.Continuum.SU2QuaternionGaugeFamilyProjection
open YMGap.Continuum.SU2QuaternionLiftedFamilyProjection

/-- The EXISTING original-polynomial predicate, not a new augmented sector. -/
theorem familyProject_invariant {extent : Nat} {tags : Z4Vertex → Option (Fin 3)}
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < linkCount extent)
    {p : RatPoly} (hp : Invariant extent tags p) :
    Invariant extent tags (familyProject ids p) := by
  refine ⟨familyProject_supported ids hp.support, ?_⟩
  change SupportedHaarEqv (linkCount extent+3)
    (slabGaugePolynomial extent tags (liftBoundary 3 (familyProject ids p)))
    (liftBoundary 3 (familyProject ids p))
  rw [← familyProject_lift 3 ids p]
  have hv : ∀ j, j ∈ ids.map (fun i => i+3) → j < linkCount extent+3 := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have := hids i hi
    omega
  exact (SupportedHaarEqv.of_carrier
    (slabGauge_familyProject extent tags ids hids (liftBoundary 3 p) hp.lifted_support).symm).trans
    (familyProject_preserves_supportedHaarEqv _ _ hv hp.image)

theorem collarHeat_invariant (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (w : Q') (K : Nat) (links : List Z4Link) :
    Invariant extent tags (collarHeat w K extent links) :=
  heatProduct_invariant tags w K _ (fun _ hi => collar_physical hi)

theorem background_invariant (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (w : Q') (K : Nat) (links : List Z4Link) :
    Invariant extent tags (background w K extent links) :=
  heatProduct_invariant tags w K _ (fun _ hi => detached_physical hi)

/-- The actual collar normalizer; no scalar floor replaces it. -/
theorem normalizer_invariant (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (w : Q') (K : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) :
    Invariant extent tags (normalizer w K extent links) :=
  familyProject_invariant _ (slots_valid extent links hl)
    (collarHeat_invariant extent tags w K links)

/-- Invariance of the original inserted numerator follows from that of p. -/
theorem insertedNormalizer_invariant {extent : Nat} {tags : Z4Vertex → Option (Fin 3)}
    (w : Q') (K : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    {p : RatPoly} (hp : Invariant extent tags p) :
    Invariant extent tags (insertedNormalizer w K extent links p) :=
  familyProject_invariant _ (slots_valid extent links hl)
    (hp.mul (collarHeat_invariant extent tags w K links))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
  (tags : Z4Vertex → Option (Fin 3))

local notation "D" => backgroundData hw0 hw1 K extent hK links
local notation "A" => approximateInverse hw0 hw1 K extent hK links

include hl in
/-- Every actual inverse iterate preserves the original gauge predicate. -/
theorem approximateInverse_invariant (r : (D).V) (hr : Invariant extent tags r.val) :
    ∀ n : Nat, Invariant extent tags (A r n).val
  | 0 => (Invariant.one extent tags).smul 0
  | n+1 => by
      have ha := approximateInverse_invariant r hr n
      exact ha.add ((hr.add ((ha.mul
        (normalizer_invariant extent tags w K links hl)).smul (-1))).smul _)

include hl in
/-- No symmetry is assumed of the output: it is proved for every constructed
polynomial approximant to the original N_p/D. -/
theorem conditionalApproximation_invariant (p : RatPoly)
    (hp : SupportedQuaternionBlocks (linkCount extent) p)
    (hpin : Invariant extent tags p) (n : Nat) :
    Invariant extent tags
      (conditionalApproximation hw0 hw1 K extent hK links p hp n).val :=
  approximateInverse_invariant hw0 hw1 K extent hK links hl tags
    (numeratorVector hw0 hw1 K extent hK links p hp)
    (insertedNormalizer_invariant w K links hl hpin) n

/-- The SAME explicit Cauchy representative already consumed by the full-action
completed conditional projection consists entirely of invariant polynomials. -/
theorem conditionalRep_invariant (p : (fullData hw0 hw1 K extent hK).V)
    (hpin : Invariant extent tags p.val) (n : Nat) :
    Invariant extent tags
      ((conditionalRep hw0 hw1 K extent hK links hl p).seq n).val :=
  conditionalApproximation_invariant hw0 hw1 K extent hK links hl tags
    p.val p.property hpin n

#print axioms familyProject_invariant
#print axioms collarHeat_invariant
#print axioms background_invariant
#print axioms normalizer_invariant
#print axioms insertedNormalizer_invariant
#print axioms approximateInverse_invariant
#print axioms conditionalApproximation_invariant
#print axioms conditionalRep_invariant

end YMGap.Continuum.BF4ExactSlabGaugeConditionalApproximation
