/-
# Original recentered chart means in different spatial boxes

The face, action, partition, cutoff stage and time buffer are literal
original objects in each box. Exact selected-action transport and the
signed boundary estimate give a geometric cross-width comparison for
every representation label, under the displayed small-nome guards.

The coefficient depends only on nome and representation, not on cutoff,
time buffer, base width, face position or further outer padding. This is
a one-plaquette state comparison, not a correlation-decay, completed-gap,
thermodynamic QFT or continuum theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteBoundary

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue expectation)
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (original_character_support)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

local infix:50 " ≈ " => Q'.eqv

def chartFace (base r t : Nat) (p : Z4Plaq) : Z4Plaq :=
  shiftFace (r+1) (paddedWidth base r+1+t) p

def chartCharacter (base r t : Nat) (p : Z4Plaq) (spin : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial (chartExtent base r 0 t)
    (chartFace base r t p)).scalar spin

theorem chartFace_physical (base r t : Nat) {p : Z4Plaq} (hp : p ∈ spatialFaces base) :
    chartFace base r t p ∈ boundaryCompleteSlabPlaquettes (chartExtent base r 0 t) := by
  have hbase : p ∈ boundaryCompleteSlabPlaquettes (base+1) := by
    have h := spatialFaces_shift_physical (extent := base+1) (time := 0)
      (by omega) (by omega) hp
    obtain ⟨⟨a, b, c, z⟩, plane⟩ := p
    simpa only [timeShiftPlaquette, timeShiftVertex, Nat.add_zero] using h
  apply shiftFace_mem (source := base+1) ?_ ?_ hbase
  all_goals unfold chartExtent adjacentEvenExtent centralExtent paddedWidth; omega

theorem chartFace_translate (base r d t : Nat) (p : Z4Plaq) :
    shiftFace d (2*d) (chartFace base r t p) = chartFace base (r+d) t p := by
  unfold chartFace
  rw [shiftFace_comp]
  have hspace : r+1+d = r+d+1 := by omega
  have htime : paddedWidth base r+1+t+2*d = paddedWidth base (r+d)+1+t := by
    have h := chart_start_shift base r d
    omega
  rw [hspace, htime]

theorem chartCharacter_translate (base r d t : Nat) {p : Z4Plaq}
    (hp : p ∈ spatialFaces base) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (chartExtent base (r+d) 0 t)).length
      ((placement base r d 0 t).embedding.polynomial (chartCharacter base r t p spin))
      (chartCharacter base (r+d) t p spin) := by
  have h := (placement base r d 0 t).character_pin (chartFace_physical base r t hp) spin
  change QuaternionPrefixPolynomialEqv _ _
    (characterPolynomial (correctedSlabPlaquettePolynomial (chartExtent base (r+d) 0 t)
      (shiftFace d (2*d) (chartFace base r t p))).scalar spin) at h
  rw [chartFace_translate] at h
  exact h

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

def finiteMean (base r t : Nat) (p : Z4Plaq) (spin stage : Nat) : Q' :=
  finiteValue w hw0 hw1 (chartExtent base r 0 t) (chartIds base r 0 t)
    (fun _ hi => chartIds_physical hi) (chartCharacter base r t p spin) stage

def cutoffMean (base r t : Nat) (p : Z4Plaq) (spin : Nat) : CReal :=
  expectation w hw0 hw1 (chartExtent base r 0 t) (chartIds base r 0 t)
    (fun _ hi => chartIds_physical hi) (chartCharacter base r t p spin)

section SmallNome

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
include hsmall

/-- Actual smaller/larger box means at the SAME cutoff and time depth. -/
theorem finiteMean_difference_bound (base r d t : Nat) (p : Z4Plaq)
    (hp : p ∈ spatialFaces base) (spin stage : Nat) :
    Q'.abs (finiteMean w hw0 hw1 base (r+d) t p spin stage +
      -(finiteMean w hw0 hw1 base r t p spin stage)) ≤
      BF4ExactSlabFixedSpatialPlaquetteBoundary.characterAmplitude w hd hs spin *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1) := by
  have hpin := BF4ExactSlabFixedSpatialAlignedAction.finiteValue_pin hw0 hw1 base r d 0 t
    (chartCharacter base r t p spin) (original_character_support _ _ spin)
    (chartCharacter base (r+d) t p spin) (original_character_support _ _ spin)
    (chartCharacter_translate base r d t hp spin) stage
  have hb := BF4ExactSlabFixedSpatialPlaquetteBoundary.finiteValue_bound hw0 hw1 hsmall hd hs
    base r d 0 t (paddedWidth base (r+d)+1+t) p hp
    (chartFace_physical base (r+d) t hp) spin stage
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hpin)))) hb

/-- The identical coefficient survives heat-cutoff removal at fixed t. -/
theorem cutoffMean_difference_bound (base r d t : Nat) (p : Z4Plaq)
    (hp : p ∈ spatialFaces base) (spin : Nat) :
    leEv (CReal.abs (CReal.sub (cutoffMean w hw0 hw1 base (r+d) t p spin)
      (cutoffMean w hw0 hw1 base r t p spin)))
      (ofQ' (BF4ExactSlabFixedSpatialPlaquetteBoundary.characterAmplitude w hd hs spin *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1))) := by
  have hpin := BF4ExactSlabFixedSpatialAlignedAction.expectation_pin hw0 hw1 base r d 0 t
    (chartCharacter base r t p spin) (original_character_support _ _ spin)
    (chartCharacter base (r+d) t p spin) (original_character_support _ _ spin)
    (chartCharacter_translate base r d t hp spin)
  have hb := BF4ExactSlabFixedSpatialPlaquetteBoundary.expectation_bound hw0 hw1 hsmall hd hs
    base r d 0 t (paddedWidth base (r+d)+1+t) p hp
    (chartFace_physical base (r+d) t hp) spin
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr (CReal.sub_congr_right hpin.symm))) hb

end SmallNome

/-- At the existing w=1/1024 pilot every analytic coupling guard is supplied. -/
theorem existingNome_cutoffMean_difference_bound (base r d t : Nat) (p : Z4Plaq)
    (hp : p ∈ spatialFaces base) (spin : Nat) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hw0 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    let hw1 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    leEv (CReal.abs (CReal.sub (cutoffMean w hw0 hw1 base (r+d) t p spin)
      (cutoffMean w hw0 hw1 base r t p spin)))
      (ofQ' (BF4ExactSlabFixedSpatialPlaquetteBoundary.characterAmplitude w hd hs spin *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1))) :=
  cutoffMean_difference_bound _ BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2 base r d t p hp spin

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.chartFace
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.chartCharacter
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.chartFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.chartFace_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.chartCharacter_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.finiteMean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.cutoffMean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.finiteMean_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.cutoffMean_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteComparison.existingNome_cutoffMean_difference_bound
