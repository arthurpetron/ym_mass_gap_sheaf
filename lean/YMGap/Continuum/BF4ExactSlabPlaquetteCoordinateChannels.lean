/-
# Concrete plaquette-boundary coordinate channels in the original interface

This module selects the four crossing faces above the boundary links of an
actual lower plaquette at extent one. The resulting channel polynomials are
products of coordinates on that closed boundary, with the original positive
heat weights. No interacting amplitude or positive minor is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
import YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.ReflectedSquareTreeRealizedLeaf
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem probeId_lower : 0 ∈ centralLowerFaceIds 0 := by decide

def probe : PlaquetteExpression 0 := .character 0 probeId_lower 1

/-- Original crossing-face order is A,D,C,B around this lower plaquette. -/
theorem crossing_links :
    faceLinkA (slabPlaquetteAt 1 2) = faceLinkA (slabPlaquetteAt 1 0) ∧
    faceLinkA (slabPlaquetteAt 1 4) = faceLinkD (slabPlaquetteAt 1 0) ∧
    faceLinkA (slabPlaquetteAt 1 20) = faceLinkC (slabPlaquetteAt 1 0) ∧
    faceLinkA (slabPlaquetteAt 1 40) = faceLinkB (slabPlaquetteAt 1 0) := by decide

theorem crossing_ids : (centralFixedFaceIds 0).filter (fun id =>
    let link := faceLinkA (slabPlaquetteAt 1 id)
    let p := slabPlaquetteAt 1 0
    decide (link = faceLinkA p ∨ link = faceLinkB p ∨ link = faceLinkC p ∨ link = faceLinkD p)) =
    [2, 4, 20, 40] := by decide

/-- Coordinate indices 0,1,2,3 refer to A,B,C,D in the oriented word. -/
def loopChoice (coordinates : Nat → Bool × Bool) (id : Nat) : CoordinateChoice :=
  if id = 2 then some (coordinates 0)
  else if id = 4 then some (coordinates 3)
  else if id = 20 then some (coordinates 2)
  else if id = 40 then some (coordinates 1)
  else none

def selectedTags (choice : Nat → CoordinateChoice) (ids : List Nat) : List (Nat × (Bool × Bool)) :=
  ids.filterMap (fun id => (choice id).map (fun c => (id, c)))

def coordinateProduct (half : Nat) : List (Nat × (Bool × Bool)) → RatPoly
  | [] => polyOne
  | (id, (column, imaginary)) :: rest => polyMul (faceCoordinatePolynomial half id column imaginary)
      (coordinateProduct half rest)

/-- Removing unit factors changes no polynomial coefficient. -/
theorem selectedPolynomial_tagged (half : Nat) (choice : Nat → CoordinateChoice) :
    (ids : List Nat) → RatPolyCoeffEqv (selectedPolynomial half choice ids)
      (coordinateProduct half (selectedTags choice ids))
  | [] => .refl _
  | id :: ids => by
      cases h : choice id with
      | none =>
          simp only [selectedPolynomial, h, choicePolynomial, selectedTags, List.filterMap_cons, Option.map_none]
          exact (RatPolyCoeffEqv.one_mul _).trans (selectedPolynomial_tagged half choice ids)
      | some c =>
          rcases c with ⟨column, imaginary⟩
          simp only [selectedPolynomial, h, choicePolynomial, selectedTags, List.filterMap_cons, Option.map_some,
            coordinateProduct]
          exact (RatPolyCoeffEqv.refl _).mul (selectedPolynomial_tagged half choice ids)

def channelWeightPower (w : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => coeffW w 1 * channelWeightPower w n

theorem selectedWeight_tagged (w : Q') (choice : Nat → CoordinateChoice) :
    (ids : List Nat) → (selectedWeight w choice ids).eqv (channelWeightPower w (selectedTags choice ids).length)
  | [] => Q'.eqv_refl _
  | id :: ids => by
      cases h : choice id with
      | none =>
          simp only [selectedWeight, h, choiceWeight, selectedTags, List.filterMap_cons, Option.map_none]
          exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (selectedWeight_tagged w choice ids)
      | some c =>
          simp only [selectedWeight, h, choiceWeight, selectedTags, List.filterMap_cons, Option.map_some,
            List.length_cons, channelWeightPower]
          exact Q'.mul_eqv_congr_left _ _ _ (selectedWeight_tagged w choice ids)

/-- Checked literal selection, with all four coordinate choices still free. -/
theorem loop_tags (coordinates : Nat → Bool × Bool) :
    selectedTags (loopChoice coordinates) (centralFixedFaceIds 0) =
      [(2, coordinates 0), (4, coordinates 3), (20, coordinates 2), (40, coordinates 1)] := by rfl

def loopPolynomial (coordinates : Nat → Bool × Bool) : RatPoly :=
  coordinateProduct 0 [(2, coordinates 0), (4, coordinates 3), (20, coordinates 2), (40, coordinates 1)]

/-- A genuine original interface channel on the closed plaquette boundary;
the SAME polynomial and heat weight are retained at every cutoff K>=1. -/
def loopChannel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K)
    (coordinates : Nat → Bool × Bool) :
    RealizedLeaf (interfaceExpansion hw K 0).tree (loopPolynomial coordinates) (channelWeightPower w 4) := by
  have hp := selectedPolynomial_tagged 0 (loopChoice coordinates) (centralFixedFaceIds 0)
  rw [loop_tags] at hp
  have hwc := selectedWeight_tagged w (loopChoice coordinates) (centralFixedFaceIds 0)
  rw [loop_tags] at hwc
  exact ((interfaceChoice hw K hK 0 (loopChoice coordinates)).recode hp).reweight hwc

theorem loopChannel_weight_positive {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (coordinates : Nat → Bool × Bool) : (0 : Q') < (loopChannel (Q'.le_of_lt hw) K hK coordinates).leaf.weight :=
  interfaceChoice_weight_positive hw K hK 0 (loopChoice coordinates)

/-- The product of the four scalar coordinates is one explicit candidate. -/
def scalarLoopChannel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) :
    RealizedLeaf (interfaceExpansion hw K 0).tree (loopPolynomial (fun _ => (false, false)))
      (channelWeightPower w 4) := loopChannel hw K hK (fun _ => (false, false))

end YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.probeId_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.probe
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.crossing_links
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.crossing_ids
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.loopChoice
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.selectedTags
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.coordinateProduct
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.selectedPolynomial_tagged
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.channelWeightPower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.selectedWeight_tagged
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.loop_tags
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.loopPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.loopChannel
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.loopChannel_weight_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels.scalarLoopChannel
