/-
# Reflection invariance of the original full Wilson window

An ambient observable may span both sides of the reflection plane. Literal
reflection is valid on the full window, although one-sided positivity is not.
The offset bound below prevents truncated subtraction from identifying
distinct times. Every ordered loop, spin, signed coefficient and operation
is retained.

Reflection preserves the SAME selected-chain action and reciprocal partition
at each finite cutoff. The resulting identity passes to the already constructed
spatial limit with its existing explicit moduli and small-nome guards. This
supplies the reflection-invariant expectation input for an ambient observable
construction; it does not construct that quotient or identify the canonical
reflected OS carrier, nor assert a spacing or continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (OrientedBF4Link)
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSpatialWilsonReflection (reflectEntry spatial_character_reflection)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection (symmetric_window_contained)
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization (blockCount)
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction (selectedHeat selectedHeat_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection (selectedIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry (originalChain_reflection)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent chartIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio heatRemainderBound)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "E" radius:arg => adjacentEvenExtent radius

/-- Full-window support makes offset reflection an actual involution. -/
theorem mirror_involutive {width : Nat} (H : Nat) :
    ∀ e : WindowExpression width, Within (2*H) e → mirror H (mirror H e) = e
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have ho : offset ≤ 2*H := he
      change WindowExpression.loop (2*H-(2*H-offset)) value spin = .loop offset value spin
      rw [show 2*H-(2*H-offset) = offset by omega]
  | .add e f, he => by
      change WindowExpression.add (mirror H (mirror H e)) (mirror H (mirror H f)) = .add e f
      rw [mirror_involutive H e he.1, mirror_involutive H f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (mirror H (mirror H e)) (mirror H (mirror H f)) = .mul e f
      rw [mirror_involutive H e he.1, mirror_involutive H f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mirror H (mirror H e)) = .smul c e
      rw [mirror_involutive H e he]

/-- Reflection commutes with centered enlargement for the full ambient window. -/
theorem mirror_shift_full {width : Nat} (H d : Nat) :
    ∀ e : WindowExpression width, Within (2*H) e →
    mirror (H+d) (shift d e) = shift d (mirror H e)
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have ho : offset ≤ 2*H := he
      change WindowExpression.loop (2*(H+d)-(offset+d)) value spin =
        .loop ((2*H-offset)+d) value spin
      rw [show 2*(H+d)-(offset+d) = (2*H-offset)+d by omega]
  | .add e f, he => by
      change WindowExpression.add (mirror (H+d) (shift d e)) (mirror (H+d) (shift d f)) =
        .add (shift d (mirror H e)) (shift d (mirror H f))
      rw [mirror_shift_full H d e he.1, mirror_shift_full H d f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (mirror (H+d) (shift d e)) (mirror (H+d) (shift d f)) =
        .mul (shift d (mirror H e)) (shift d (mirror H f))
      rw [mirror_shift_full H d e he.1, mirror_shift_full H d f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mirror (H+d) (shift d e)) = .smul c (shift d (mirror H e))
      rw [mirror_shift_full H d e he]

private theorem shifted_entry_reflection {width radius A H j : Nat}
    (hcenter : A+H=radius+1) (hj : j ≤ 2*H) {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    reflectEntry (E radius) (shiftEntry (A+j) e) = shiftEntry (A+(2*H-j)) e := by
  have hd := (baseLinks_mem_iff width e.link).mp he
  have hsp := hd.1
  have hz := hd.2.2.2.2
  rcases e with ⟨⟨⟨x,y,z,t⟩,dir⟩,reverse⟩
  change t = 0 at hz
  subst t
  have ht : E radius - (A+j) = A+(2*H-j) := by
    unfold adjacentEvenExtent centralExtent
    omega
  cases dir <;> try exact False.elim (hsp rfl)
  all_goals simp only [reflectEntry, shiftEntry, timeShiftLink, timeShiftVertex,
    timeReflectLink, Nat.zero_add, ht]

/-- Literal spatial loop reflection needs full-window, not half-window, support. -/
theorem loop_placed_reflection {width radius A H j : Nat}
    (hw : width ≤ E radius) (hcenter : A+H=radius+1) (hj : j ≤ 2*H)
    (loop : SourceLoop width) (spin : Nat) :
    ReflectionImage (E radius)
      (character (E radius) (loop.edges.map (shiftEntry (A+j))) spin)
      (character (E radius) (loop.edges.map (shiftEntry (A+(2*H-j)))) spin) := by
  have ht : A+j ≤ E radius := by have := symmetric_window_contained hcenter; omega
  let placed := placeLoop hw ht loop
  have hr := spatial_character_reflection (E radius) placed.edges placed.physical
    (fun e he => (placed.spatial e he).1) spin
  have he : (loop.edges.map (shiftEntry (A+j))).map (reflectEntry (E radius)) =
      loop.edges.map (shiftEntry (A+(2*H-j))) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    exact shifted_entry_reflection hcenter hj (loop.physical e he)
  change ReflectionImage (E radius)
    (character (E radius) (loop.edges.map (shiftEntry (A+j))) spin)
    (character (E radius) ((loop.edges.map (shiftEntry (A+j))).map (reflectEntry (E radius))) spin) at hr
  rw [he] at hr
  exact hr

/-- Full signed ambient expressions retain their literal original reflection. -/
theorem placed_reflection_full {width radius A H : Nat}
    (hw : width ≤ E radius) (hcenter : A+H=radius+1) :
    ∀ e : WindowExpression width, Within (2*H) e →
    ReflectionImage (E radius) (placedPolynomial (E radius) A e)
      (placedPolynomial (E radius) A (mirror H e))
  | .one, _ => ReflectionImage.one _
  | .loop _offset value spin, he => loop_placed_reflection hw hcenter he value spin
  | .add e f, he =>
      (placed_reflection_full hw hcenter e he.1).add (placed_reflection_full hw hcenter f he.2)
  | .mul e f, he =>
      (placed_reflection_full hw hcenter e he.1).mul (placed_reflection_full hw hcenter f he.2)
  | .smul c e, he => (placed_reflection_full hw hcenter e he).smul c

/-- A literal reflected insertion has the same finite expectation, including
the original action and its unchanged reciprocal partition. -/
theorem originalChain_finiteValue_reflection {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (hcenter : start+depth=radius+1)
    (p p' : RatPoly) (hp : SupportedQuaternionBlocks (blockCount radius) p)
    (hp' : SupportedQuaternionBlocks (blockCount radius) p')
    (hr : ReflectionImage (E radius) p p') (stage : Nat) :
    finiteValue w hw0 hw1 (E radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi) p stage ≈
    finiteValue w hw0 hw1 (E radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi) p' stage := by
  let action := selectedHeat w (headCutoff w+stage) radius (selectedIds radius width start depth)
  have ha := selectedHeat_supported w (headCutoff w+stage) radius (selectedIds radius width start depth)
  have hra := originalChain_reflection w (headCutoff w+stage) radius width start depth hcenter
  apply Q'.mul_eqv_congr_right
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_reflectCorrectedSlabPolynomial (E radius)
      (polyMul p action) (supported_polyMul hp ha)))
    ((hr.mul hra).haar (reflectCorrectedSlabPolynomial_support _ _)
      (supported_polyMul hp' ha))

/-- The SAME chart action is invariant under full-window reflection at every
spatial padding, retained heat stage and symmetric temporal boundary distance. -/
theorem chartScalar_mirror {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)
    (r stage t : Nat) :
    chartScalar hw0 hw1 H e r stage t ≈ chartScalar hw0 hw1 H (mirror H e) r stage t := by
  let width := paddedWidth base r
  let radius := width+t+H
  let start := width+1
  have hw : width ≤ E radius := by unfold adjacentEvenExtent centralExtent radius; omega
  have hcenter : start+t+H=radius+1 := by unfold start radius; omega
  have hcount : t+(2*H+t)=2*(t+H) := by omega
  let p := placedPolynomial (E radius) (start+t) (centeredExpression r e)
  let rp := placedPolynomial (E radius) (start+t) (mirror H (centeredExpression r e))
  have hp := placed_supported (E radius) (start+t) (centeredExpression r e)
  have hrp := placed_supported (E radius) (start+t) (mirror H (centeredExpression r e))
  have hr := placed_reflection_full hw hcenter (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)
  have h := originalChain_finiteValue_reflection hw0 hw1 radius width start (t+H)
    (by omega) p rp hp hrp hr stage
  simpa only [p, rp, radius, start, width, chartScalar, chartInsertion,
    chartExtent, chartIds, selectedIds, hcount, centeredExpression, recenterExpression,
    mirror, recenter_mapOffsets] using h

attribute [local irreducible] chartScalar spatialLimit

/-- Reflection invariance of the existing explicit-modulus expectation for
every full-window expression. Spatial small-nome hypotheses remain explicit. -/
theorem spatialLimit_mirror {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base) :
    Equiv (spatialLimit hw0 hw1 H e he hsmall hd hs hb)
      (spatialLimit hw0 hw1 H (mirror H e) (mirror_within H e) hsmall hd hs hb) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv (fun _ => chartScalar_mirror hw0 hw1 H e he n n n))
    (spatial_diagonal_converges hw0 hw1 H e he hsmall hd hs hb)
    (spatial_diagonal_converges hw0 hw1 H (mirror H e) (mirror_within H e) hsmall hd hs hb)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection.mirror_involutive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection.mirror_shift_full
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection.loop_placed_reflection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection.placed_reflection_full
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection.originalChain_finiteValue_reflection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection.chartScalar_mirror
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection.spatialLimit_mirror
