/-
# Positive temporal-gauge crossing interfaces on every odd slab

The actual central crossing faces, original heat coefficients, and literal
spatial-link representation columns construct local square expansions at
every odd extent. Any supported lower-half polynomial may multiply their
channels, so its full spatial interaction and overlapping links remain.

The crossing interface after the existing temporal link assignment is pinned
to this Gram product under every Haar insertion. Its reflected pairing is
therefore an explicit nonnegative sum of squares, for every cutoff and w >= 0.
At extent one the result is pinned to the ORIGINAL signed slab quadratic.

The all-extent change-of-variables pin for the COMPLETE original observable
and law is not proved here. Neither larger-slab consistency, time evolution,
vacuum stationarity, a strict gap nor any limit is asserted.
-/

import YMGap.Continuum.BF4ExactSlabLocalSquareExpansion

namespace YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep

/-- All-degree actual spatial Gram channels on a physical lower link. -/
def spatialLinkExpansion {half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks (centralExtent half))
    (hs : linkHalfSide half link = .lower) (hd : link.2 ≠ .x3) (spin : Nat) :
    LocalSquareExpansion half (reflectedSpatialLinkGram (centralExtent half) link spin).1 where
  tree := gramSquares (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half) link)) spin
  image := spatial_gram_reflected_squares hl hd spin
  polynomialSupported := (spatialGram_support (centralExtent half) link spin).1
  treeSupported := spatialGramSquares_support (centralExtent half) link spin
  treeLower := lower_gram_tree hl hs spin
  weightsNonnegative := gramSquares_nonnegative _ spin

def faceHeatPolynomial (w : Q') (K half id : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (reflectedSpatialLinkGram (centralExtent half)
      (faceLinkA (slabPlaquetteAt (centralExtent half) id)) spin).1) (List.range (K + 1))

def faceExpansion {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) : LocalSquareExpansion half (faceHeatPolynomial w K half id) :=
  LocalSquareExpansion.finiteSum _ _ (fun spin hspin =>
    (spatialLinkExpansion
      (faceLinkA_physical (slabPlaquetteAt_mem (mem_centralFixedFaceIds.mp hi).1))
      (crossing_face_path_sides (mem_centralFixedFaceIds.mp hi).2).1
      (faceLinkA_spatial _) spin).scale (coeffAt (heatKernelPacket K w) spin) (by
        rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]
        exact coeffW_nonneg hw spin))

/-- Product over the actual central fixed-face enumeration, not a list of
independent replacement kernels. -/
def interfacePolynomial (w : Q') (K half : Nat) : RatPoly :=
  (centralFixedFaceIds half).foldr (fun id p => polyMul (faceHeatPolynomial w K half id) p) polyOne

def interfaceExpansion {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) :
    LocalSquareExpansion half (interfacePolynomial w K half) :=
  LocalSquareExpansion.finiteProduct _ _ (fun _ hi => faceExpansion hw K hi)

def reflectedInterfacePolynomial (w : Q') (K half : Nat) (p : RatPoly) : RatPoly :=
  polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p) (interfacePolynomial w K half)

/-- No restriction on the degree or sign of the lower observable, and no
factorization of its internal or shared spatial links. -/
def reflectedInterfaceExpansion {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) : LocalSquareExpansion half (reflectedInterfacePolynomial w K half p) :=
  (LocalSquareExpansion.reflectedSquare half p hp hl).product (interfaceExpansion hw K half)

theorem reflectedInterface_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    (0 : Q') ≤ quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (reflectedInterfacePolynomial w K half p) :=
  (reflectedInterfaceExpansion hw K half p hp hl).haar_nonnegative

/-- The ORIGINAL character evaluated after the existing temporal link
assignment, before replacing that character by its proved Gram image. -/
def temporalFaceHeatPolynomial (w : Q') (K half id : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (characterPolynomial (temporalFaceWord (centralExtent half) half
      (slabPlaquetteAt (centralExtent half) id)).scalar spin)) (List.range (K + 1))

def temporalInterfacePolynomial (w : Q') (K half : Nat) : RatPoly :=
  (centralFixedFaceIds half).foldr (fun id p => polyMul (temporalFaceHeatPolynomial w K half id) p) polyOne

private theorem sum_row {A : Type} {blocks : Nat} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionHaarCarrierEqv blocks (f a) (g a)) →
      QuaternionHaarCarrierEqv blocks (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => QuaternionHaarCarrierEqv.refl _ _
  | a :: xs, h => QuaternionHaarCarrierEqv.add (h a List.mem_cons_self)
      (sum_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem fold_row {A : Type} {blocks : Nat} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionHaarCarrierEqv blocks (f a) (g a)) →
      QuaternionHaarCarrierEqv blocks
        (xs.foldr (fun a p => polyMul (f a) p) polyOne)
        (xs.foldr (fun a p => polyMul (g a) p) polyOne)
  | [], _ => QuaternionHaarCarrierEqv.refl _ _
  | a :: xs, h => QuaternionHaarCarrierEqv.mul (h a List.mem_cons_self)
      (fold_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Complete central crossing interface, every odd extent and cutoff,
with every additional polynomial insertion retained on the same Haar carrier. -/
theorem temporalInterface_haar_gram (w : Q') (K half : Nat) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length
      (temporalInterfacePolynomial w K half) (interfacePolynomial w K half) := by
  apply fold_row
  intro id hi
  apply sum_row
  intro spin _
  apply QuaternionHaarCarrierEqv.smul
  exact (crossing_face_reflected_gram half _ (mem_centralFixedFaceIds.mp hi).2 spin).1

/-- The temporal-gauge reflected form is pinned to its explicit rational
square value. This does not assume positivity of the finite heat polynomial. -/
theorem temporalInterface_eq_squareValue {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p)
        (temporalInterfacePolynomial w K half))).eqv
      (reflectedInterfaceExpansion hw K half p hp hl).squareValue :=
  Q'.eqv_trans _ _ _ (temporalInterface_haar_gram w K half _)
    (reflectedInterfaceExpansion hw K half p hp hl).haar_eq_squareValue

theorem temporalInterface_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    (0 : Q') ≤ quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p)
        (temporalInterfacePolynomial w K half)) :=
  Q'.le_trans' _ _ _ (reflectedInterface_nonnegative hw K half p hp hl)
    (Q'.le_of_eqv (Q'.eqv_symm (temporalInterface_haar_gram w K half _)))

theorem interface_extent_one (w : Q') (K : Nat) :
    interfacePolynomial w K 0 = spatialGramInterface w K := rfl

/-- At the already constructed original extent-one law, the general
polynomial form is the SAME signed quadratic, not a surrogate comparison. -/
theorem original_quadratic_pin (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    (exactSlabAllCutoffQuadratic w K c).eqv
      (quaternionHaar 116 (reflectedInterfacePolynomial w K 0 (lowerObservable w K c))) := by
  refine Q'.eqv_trans _ _ _ (exact_quadratic_eq_spatialGramHaar w K c) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc 116 _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm 116 _ _) ?_
  exact Q'.eqv_symm (quaternionHaar_polyMul_assoc 116 _ _ _)

end YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.spatialLinkExpansion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.faceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.faceExpansion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.interfacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.interfaceExpansion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.reflectedInterfacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.reflectedInterfaceExpansion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.reflectedInterface_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.temporalFaceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.temporalInterfacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.temporalInterface_haar_gram
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.temporalInterface_eq_squareValue
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.temporalInterface_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.interface_extent_one
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity.original_quadratic_pin
