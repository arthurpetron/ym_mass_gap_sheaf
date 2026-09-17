/-
# Actual time-zero Wilson chart locality and square certificates

An arbitrary supplied source loop at offset H is recentered and placed on
the reflection-fixed slice of the ORIGINAL spatial chart. Its literal
character polynomial is supported and fixed-local on that same carrier.
Ordered Haar-unit norm and the character recurrence construct an explicit
SquareBound with cap characterBound spin; no interval estimate is promoted
to a reflected operator bound here.

These finite certificates feed the separate selected-action multiplier
estimate. No extra loop hypothesis, physical mass or continuum claim is
introduced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
import YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.BF4WilsonTimeZeroChart

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (centeredExpression chartInsertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent)
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl (character_local word_unit)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabVacuumReflection (correctedSlabLinkAt)
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization (blockCount blockSide Local)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

private theorem spatial_fixed {radius : Nat} {edge : Z4Link}
    (hsp : edge.2 ≠ .x3) (ht : edge.1.2.2.2 = radius+1) :
    adjacentEvenLinkSide radius edge = .fixed := by
  rcases edge with ⟨⟨x,y,z,time⟩,dir⟩
  change time = radius+1 at ht
  cases dir <;> try exact False.elim (hsp rfl)
  all_goals simp [adjacentEvenLinkSide, adjacentEvenSpatialSide, adjacentEvenCenter, ht]

/-- Every source of locality is an actual oriented edge on the fixed slice. -/
theorem fixedLoop_local (radius : Nat)
    (L : SpatialLoop (adjacentEvenExtent radius) (radius+1)) (spin : Nat) :
    Local radius .fixed (character (adjacentEvenExtent radius) L.edges spin) := by
  have hl := character_local (adjacentEvenExtent radius) (L.edges.map (fun e => e.link))
    L.edges (fun e he => List.mem_map.mpr ⟨e, he, rfl⟩) spin
  intro term hterm block hb hn
  apply hl term hterm block hb
  intro hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  apply hn
  change adjacentEvenLinkSide radius
    (correctedSlabLinkAt (adjacentEvenExtent radius) block) = .fixed
  rw [← heq]
  exact spatial_fixed (L.spatial e he).1 (L.spatial e he).2

/-- Computed square cap for the literal ordered Wilson word on this Haar carrier. -/
def fixedLoop_squareBound (radius : Nat)
    (L : SpatialLoop (adjacentEvenExtent radius) (radius+1)) (spin : Nat) :
    SquareBound (blockCount radius)
      (character (adjacentEvenExtent radius) L.edges spin) (characterBound spin) := by
  have hp := word_supported (adjacentEvenExtent radius) L.edges
  exact character_squareBound (SquareBound.scalar
    ⟨hp.scalar, hp.iPart, hp.jPart, hp.kPart⟩
    (word_unit (adjacentEvenExtent radius) L.edges L.physical)) spin

/-- Recenter the actual source loop, then place it on the original chart's fixed slice. -/
def chartLoop {base : Nat} (r H t : Nat) (L : SourceLoop base) :
    SpatialLoop (adjacentEvenExtent (paddedWidth base r+t+H))
      (paddedWidth base r+t+H+1) :=
  placeLoop (width := paddedWidth base r)
    (by unfold adjacentEvenExtent centralExtent; omega)
    (by unfold adjacentEvenExtent centralExtent; omega)
    (recenterLoop (space := r+1) (by unfold paddedWidth; omega) L)

/-- Literal polynomial equality: the insertion's time is exactly radius+1. -/
theorem chartInsertion_loop {base : Nat} (r H t : Nat) (L : SourceLoop base) (spin : Nat) :
    chartInsertion r H t (.loop H L spin) =
      character (adjacentEvenExtent (paddedWidth base r+t+H)) (chartLoop r H t L).edges spin := by
  simp only [chartInsertion, placedPolynomial, centeredExpression, recenterExpression,
    chartLoop, placeLoop, chartExtent]
  rw [show paddedWidth base r+1+t+H = paddedWidth base r+t+H+1 by omega]

theorem chart_fixed_local {base : Nat} (r H t : Nat) (L : SourceLoop base) (spin : Nat) :
    Local (paddedWidth base r+t+H) .fixed (chartInsertion r H t (.loop H L spin)) := by
  rw [chartInsertion_loop]
  exact fixedLoop_local (paddedWidth base r+t+H) (chartLoop r H t L) spin

/-- Type-valued square certificate, independent in its cap of placement and regulators. -/
def chart_squareBound {base : Nat} (r H t : Nat) (L : SourceLoop base) (spin : Nat) :
    SquareBound (blockCount (paddedWidth base r+t+H))
      (chartInsertion r H t (.loop H L spin)) (characterBound spin) := by
  rw [chartInsertion_loop]
  exact fixedLoop_squareBound (paddedWidth base r+t+H) (chartLoop r H t L) spin

theorem chart_supported {base : Nat} (r H t : Nat) (L : SourceLoop base) (spin : Nat) :
    SupportedQuaternionBlocks (blockCount (paddedWidth base r+t+H))
      (chartInsertion r H t (.loop H L spin)) :=
  (chart_squareBound r H t L spin).support

end YMGap.Continuum.BF4WilsonTimeZeroChart

#print axioms YMGap.Continuum.BF4WilsonTimeZeroChart.fixedLoop_local
#print axioms YMGap.Continuum.BF4WilsonTimeZeroChart.fixedLoop_squareBound
#print axioms YMGap.Continuum.BF4WilsonTimeZeroChart.chartLoop
#print axioms YMGap.Continuum.BF4WilsonTimeZeroChart.chartInsertion_loop
#print axioms YMGap.Continuum.BF4WilsonTimeZeroChart.chart_fixed_local
#print axioms YMGap.Continuum.BF4WilsonTimeZeroChart.chart_squareBound
#print axioms YMGap.Continuum.BF4WilsonTimeZeroChart.chart_supported
