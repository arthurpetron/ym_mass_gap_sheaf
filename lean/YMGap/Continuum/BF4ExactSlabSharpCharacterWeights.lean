/-
# Dimension-sharp weights for the original signed slab moments

Apply the polynomial character certificates to the actual plaquette
holonomies and every original spin-network factor. The connected pair
keeps its four original moments. Including the heat coefficients costs
the SQUARE of the dimension product and the exact Casimir power, not
an exponential character envelope. No sign or summability is inferred.
-/

import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison

namespace YMGap.Continuum.BF4ExactSlabSharpCharacterWeights

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def faceCharacterInterval (extent : Nat) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    Interval (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) (dimQ spin) :=
  sharpCharacterInterval (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette hf)) spin

def spinFactor (extent : Nat) (state : EdgeLabelling) (id : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar (state id)

theorem spin_product_pin (extent : Nat) (state : EdgeLabelling) :
    polynomialProduct (spinFactor extent state) (slabPhysicalFaceEdges extent) =
      exactCorrectedSlabSpinNetworkIntegrand extent state := by
  rw [polynomialProduct_congr (spinFactor extent state)
    (fun id => correctedSlabPlaquetteSpinFactor extent state (slabPlaquetteAt extent id))
    (slabPhysicalFaceEdges extent) (fun id hi => by
      unfold correctedSlabPlaquetteSpinFactor spinFactor
      dsimp only
      rw [idxOf_slabPlaquetteAt hi])]
  unfold polynomialProduct exactCorrectedSlabSpinNetworkIntegrand
  rw [← slabFaceIds_map extent, List.foldr_map]

def spinListInterval (extent : Nat) (state : EdgeLabelling) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    Interval (boundaryCompleteSlabLinks extent).length (polynomialProduct (spinFactor extent state) ids)
      (dimensionProduct state ids)
  | [], _ => .one _
  | id::ids, hi =>
    (faceCharacterInterval extent _ (slabPlaquetteAt_mem (hi id List.mem_cons_self)) (state id)).mul
      (spinListInterval extent state ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def spinNetworkInterval (extent : Nat) (state : EdgeLabelling) :
    Interval (boundaryCompleteSlabLinks extent).length (exactCorrectedSlabSpinNetworkIntegrand extent state)
      (dimensionProduct state (slabPhysicalFaceEdges extent)) := by
  rw [← spin_product_pin]
  exact spinListInterval extent state _ (fun _ hi => hi)

def lowerProbeInterval (margin : Nat) :
    Interval (boundaryCompleteSlabLinks (responseExtent margin)).length (lower (enlarge margin shiftedProbe)) 2 := by
  rw [lower_shifted_probe_pin]
  exact faceCharacterInterval _ _ (slice_physical margin ⟨0,by decide⟩) 1

def upperProbeInterval (margin : Nat) :
    Interval (boundaryCompleteSlabLinks (responseExtent margin)).length (upper (enlarge margin shiftedProbe)) 2 := by
  rw [upper_shifted_probe_pin]
  exact faceCharacterInterval _ _ (slice_physical margin ⟨3,by decide⟩) 1

def insertionCap (lo hi : Bool) : Q' := (if lo then 2 else 1) * (if hi then 2 else 1)

def insertionInterval (margin : Nat) (lo hi : Bool) :
    Interval (boundaryCompleteSlabLinks (responseExtent margin)).length (insertion margin lo hi) (insertionCap lo hi) := by
  cases lo <;> cases hi
  · exact (Interval.one _).mul (Interval.one _)
  · exact (Interval.one _).mul (upperProbeInterval margin)
  · exact (lowerProbeInterval margin).mul (Interval.one _)
  · exact (lowerProbeInterval margin).mul (upperProbeInterval margin)

theorem moment_bound (margin : Nat) (lo hi : Bool) (state : EdgeLabelling) :
    Q'.abs (moment margin lo hi state) ≤
      insertionCap lo hi * dimensionProduct state (slabPhysicalFaceEdges (responseExtent margin)) :=
  ((insertionInterval margin lo hi).mul (spinNetworkInterval (responseExtent margin) state)).haar_bound

theorem pairTerm_bound (margin : Nat) (left right : EdgeLabelling) :
    Q'.abs (pairTerm margin left right) ≤
      (8 * dimensionProduct left (slabPhysicalFaceEdges (responseExtent margin))) *
        dimensionProduct right (slabPhysicalFaceEdges (responseExtent margin)) :=
  connected_bound (lowerProbeInterval margin) (upperProbeInterval margin)
    (spinNetworkInterval (responseExtent margin) left) (spinNetworkInterval (responseExtent margin) right)

def pairDimension (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  dimensionProduct pair.1 (slabPhysicalFaceEdges (responseExtent margin)) *
    dimensionProduct pair.2 (slabPhysicalFaceEdges (responseExtent margin))

theorem pairDimension_nonnegative (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ pairDimension margin pair :=
  Q'.mul_nonneg _ _ (spinNetworkInterval (responseExtent margin) pair.1).nonnegative
    (spinNetworkInterval (responseExtent margin) pair.2).nonnegative

/-- All original signed Haar terms are retained; no character-envelope factor remains. -/
theorem signedAmplitude_bound (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    Q'.abs (signedAmplitude margin pair) ≤ 8 * (pairDimension margin pair * pairDimension margin pair) := by
  have hd : Q'.abs (pairDimension margin pair) ≤ pairDimension margin pair := by
    rw [Q'.abs, if_pos (pairDimension_nonnegative margin pair)]
    exact Q'.le_refl' _
  exact Q'.le_trans' _ _ _ (abs_product_bound hd (pairTerm_bound margin pair.1 pair.2))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.const 8) (.var 0)) (.var 1)))
      (.mul (.const 8) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))) (by decide)
      (fun i => if i = 0 then dimensionProduct pair.1 (slabPhysicalFaceEdges (responseExtent margin))
        else dimensionProduct pair.2 (slabPhysicalFaceEdges (responseExtent margin)))))

/-- The original heat-weighted pair, all cutoff labels, with its exact Casimir power. -/
theorem weightedPairTerm_bound (w : Q') (hw : (0 : Q') ≤ w) (K margin : Nat)
    (pair : EdgeLabelling × EdgeLabelling)
    (hb : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → pair.1 id ≤ K ∧ pair.2 id ≤ K) :
    Q'.abs (weightedPairTerm w K margin pair) ≤
      (8 * (pairDimension margin pair * pairDimension margin pair)) * qpow w (pairPower margin pair) := by
  have hp : Q'.abs (qpow w (pairPower margin pair)) ≤ qpow w (pairPower margin pair) := by
    rw [Q'.abs, if_pos (qpow_nonneg w hw _)]
    exact Q'.le_refl' _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (original_pair_power w K margin pair hb)))
    (abs_product_bound (signedAmplitude_bound margin pair) hp)

end YMGap.Continuum.BF4ExactSlabSharpCharacterWeights

#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.faceCharacterInterval
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.spin_product_pin
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.spinListInterval
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.spinNetworkInterval
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.lowerProbeInterval
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.upperProbeInterval
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.insertionCap
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.insertionInterval
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.moment_bound
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.pairTerm_bound
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.pairDimension
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.pairDimension_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.signedAmplitude_bound
#print axioms YMGap.Continuum.BF4ExactSlabSharpCharacterWeights.weightedPairTerm_bound
