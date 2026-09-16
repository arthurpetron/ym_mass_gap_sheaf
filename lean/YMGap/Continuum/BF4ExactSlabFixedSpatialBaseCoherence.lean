/-
# Base inclusion preserves the actual spatial-limit reflected pairing

The same signed physical face words may be presented in any larger base
box. At a common margin their original selected actions differ only outside
the translated smaller selection. The actual signed boundary determinant
estimate cancels both original partitions. Its fixed support is computed
from the SOURCE base and observation radius, not the larger ambient box.

The resulting geometric bound is uniform in the cutoff stage, temporal
buffer and larger base. Explicit late-margin control identifies the two
already constructed spatial limits. The same small-nome assumptions remain
visible. No finite-width state identity, width-uniform temporal gap, or
spacing/continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseAlignedBoxes
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBaseCoherence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion (activeAnchors)
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
  (chartExtent chartIds chartIds_physical chartIds_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (Span Within Physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe
  (encodeChart_translate mirrorSpan_translate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
  (spatialPairing spatialPairing_chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary
  (carrierSize boxAmplitude shifted_budget_factor)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem finiteValue_perm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
    (xs ys : List Nat)
    (hx : ∀ id, id ∈ xs → id ∈ slabPhysicalFaceEdges extent)
    (hy : ∀ id, id ∈ ys → id ∈ slabPhysicalFaceEdges extent)
    (hperm : xs.Perm ys) (p : RatPoly) (stage : Nat) :
    finiteValue w hw0 hw1 extent xs hx p stage ≈
      finiteValue w hw0 hw1 extent ys hy p stage := by
  unfold finiteValue
  apply qmul (BF4ExactSlabMixedAction.moment_perm w _ extent p hperm)
  unfold reciprocalTerm PositiveRationalCauchyReciprocal.term partitionSample
  exact Q'.recipPos_eqv_congr _ _ _ _
    (BF4ExactSlabMixedAction.partition_perm w _ extent hperm)

/-- Exact normalization of the masked target law by its own partition.
Only this masked action, not the full target action, equals the source law. -/
theorem inside_finiteValue_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base larger : Nat} (h : base ≤ larger) (r H t : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks (chartExtent base r H t)) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks (chartExtent larger r H t)) q)
    (he : QuaternionPrefixPolynomialEqv (blocks (chartExtent larger r H t))
      ((placement h r H t).embedding.polynomial p) q) (stage : Nat) :
    finiteValue w hw0 hw1 (chartExtent larger r H t) (insideIds h r H t)
      (insideIds_physical h r H t) q stage ≈
      finiteValue w hw0 hw1 (chartExtent base r H t) (chartIds base r H t)
        (fun _ hi => chartIds_physical hi) p stage := by
  exact Q'.eqv_trans _ _ _
    (finiteValue_perm hw0 hw1 (chartExtent larger r H t)
      (insideIds h r H t) (translatedChartIds h r H t)
      (insideIds_physical h r H t)
      (BF4ExactSlabTranslatedSelectedAction.selectedIds_physical
        (placement h r H t) (chartIds base r H t) (fun _ hi => chartIds_physical hi))
      (insideIds_perm h r H t) q stage)
    (BF4ExactSlabTranslatedSelectedAction.finiteValue_pin_of_prefix
      (placement h r H t) hw0 hw1 (chartIds base r H t)
      (fun _ hi => chartIds_physical hi) p hp q hq he stage)

private theorem origin_spatial {base : Nat} (hb : 0<base) : originFace ∈ spatialFaces base := by
  apply (spatialFaces_mem_iff base originFace).mpr
  exact ⟨hb, hb, hb, rfl, by decide⟩

private theorem active_core_size_floor {base larger : Nat} (h : base ≤ larger)
    (r H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) {anchor : List Nat}
    (ha : anchor ∈ activeAnchors (chartExtent larger r H t)
      ((boxLinks n).map (shiftLink (r+1) timeOrigin)) (keep h r H t)
      (chartIds larger r H t)) : r+1-carrierSize n ≤ anchor.length := by
  have hf := active_core_linf_floor (distance := r+1)
    (shiftedBoxProbe n (r+1) timeOrigin hn)
    (chartIds_nodup larger r H t) (fun _ hi => chartIds_physical hi) ha (by
      intro id hi ho
      exact omitted_separation h r H t timeOrigin (origin_spatial hb) hi
        ((keep_eq_false h r H t id).mp ho))
  rw [shiftedBoxProbe_size] at hf
  unfold carrierSize
  omega

private theorem determinant_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger)
    (K r H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) (p : RatPoly) (c : Q')
    (P : Interval (blocks (chartExtent larger r H t)) p c)
    (hl : LinkLocal (chartExtent larger r H t)
      ((boxLinks n).map (shiftLink (r+1) timeOrigin)) p) :
    Q'.abs (mixedNumerator w K (chartExtent larger r H t) (keep h r H t) p
      (chartIds larger r H t)) ≤
      (((c+c)*boxAmplitude w hd hs n) *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize n)) *
        mixedPartition w K (chartExtent larger r H t) (keep h r H t)
          (chartIds larger r H t) := by
  have hbnd := mixedNumerator_tail_bound hw0 hw1 hsmall hd hs K (chartExtent larger r H t)
    (keep h r H t) p c P _ (shiftedBoxProbe n (r+1) timeOrigin hn) hl
    (chartIds larger r H t) (r+1-carrierSize n) (chartIds_nodup larger r H t)
    (fun _ hi => chartIds_physical hi)
    (fun _ ha => active_core_size_floor h r H t timeOrigin n hb hn ha)
  exact Q'.le_trans' _ _ _ hbnd
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c+c) _ _ (shifted_budget_factor w hd hs n _ _ _ hn))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

private theorem finiteValue_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger)
    (r H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) (p : RatPoly) (c : Q')
    (P : Interval (blocks (chartExtent larger r H t)) p c)
    (hl : LinkLocal (chartExtent larger r H t)
      ((boxLinks n).map (shiftLink (r+1) timeOrigin)) p) (stage : Nat) :
    Q'.abs (finiteValue w hw0 hw1 (chartExtent larger r H t)
      (chartIds larger r H t) (fun _ hi => chartIds_physical hi) p stage +
      -(finiteValue w hw0 hw1 (chartExtent larger r H t) (insideIds h r H t)
        (insideIds_physical h r H t) p stage)) ≤
      ((c+c)*boxAmplitude w hd hs n) *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize n) := by
  apply finite_comparison_bound w hw0 hw1 (chartExtent larger r H t)
    (chartIds larger r H t) (fun _ hi => chartIds_physical hi)
    (insideIds h r H t) (insideIds_physical h r H t) p _ stage
  exact determinant_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs h
    (headCutoff w+stage) r H t timeOrigin n hb hn p c P hl

private theorem mirror_within (H : Nat) (xs : Span) : Within (2*H) (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_within H y.2

private theorem mirror_physical {width : Nat} (H : Nat) (xs : Span)
    (hx : Physical width xs) : Physical width (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces H y.2 (hx y hy)

/-- The target observable still uses the SOURCE fixed support box. -/
theorem included_chartProbe_local {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) (x y : PhysicalSpan base) (hy : radius y.val ≤ H) :
    LinkLocal (chartExtent larger r H t)
      ((boxLinks (boxSize base H)).map (shiftLink (r+1) (paddedWidth larger r+1+t)))
      (chartProbe larger r H t (inclusion h x) (inclusion h y)) := by
  have hywithin : Within (2*H) (encodeChart H y.val) := by
    intro a ha e he
    have ho := encodeChart_within H y.val hy a ha e he
    omega
  have Px := placedSpan_translated_local base (2*H) (r+1)
    (chartExtent larger r H t) (paddedWidth larger r+1+t)
    (mirrorSpan H (encodeChart H x.val))
    (mirror_physical H _ (encodeChart_physical H _ x.property)) (mirror_within H _)
  have Py := placedSpan_translated_local base (2*H) (r+1)
    (chartExtent larger r H t) (paddedWidth larger r+1+t)
    (encodeChart H y.val) (encodeChart_physical H _ y.property) hywithin
  have P := BlockLocal.mul Px Py
  simpa only [chartProbe, boxSize, inclusion, recenter,
    encodeChart_translate, mirrorSpan_translate] using P

/-- Same original reflected insertion and two actual partitions, with no
caller-supplied interval, locality, or spatial-decay premise. The bound does
not depend on the larger base, stage, or boundary-time buffer. -/
theorem chartScalar_inclusion_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger) (r H t stage : Nat) (hb : 0<base)
    (x y : PhysicalSpan base) (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    Q'.abs (chartScalar hw0 hw1 (paddedWidth larger r) stage H
      (recenter r (inclusion h x)) (recenter r (inclusion h y)) t +
      -(chartScalar hw0 hw1 (paddedWidth base r) stage H (recenter r x) (recenter r y) t)) ≤
      spatialAmplitude w hd hs base H x y *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize (boxSize base H)) := by
  have hpin := inside_finiteValue_pin hw0 hw1 h r H t
    (chartProbe base r H t x y) (chartProbe_interval base r H t x y hx hy).support
    (chartProbe larger r H t (inclusion h x) (inclusion h y))
    (chartProbe_interval larger r H t (inclusion h x) (inclusion h y) hx hy).support
    (aligned_chartInsertion_pin h r H t x y hx hy) stage
  have hbnd := finiteValue_bound hw0 hw1 hsmall hd hs h r H t
    (paddedWidth larger r+1+t) (boxSize base H) hb (boxSize_pos base H)
    (chartProbe larger r H t (inclusion h x) (inclusion h y)) (pairCap x.val y.val)
    (chartProbe_interval larger r H t (inclusion h x) (inclusion h y) hx hy)
    (included_chartProbe_local h r H t x y hy) stage
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hpin)))) hbnd

/-- Computed tolerance threshold independent of the larger base and both
inner regulators. It also covers zero geometric rate. -/
def inclusionModulus (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base H : Nat) (x y : PhysicalSpan base) (epsilon : Q') : Nat :=
  carrierSize (boxSize base H) + geometricCutoff
    (entropyRate 625 (adjustedCoreRate w hd)) (spatialAmplitude w hd hs base H x y) epsilon

theorem chartScalar_inclusion_close {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger) (H : Nat) (hb : 0<base)
    (x y : PhysicalSpan base) (hx : radius x.val ≤ H) (hy : radius y.val ≤ H)
    (epsilon : Q') (he : (0 : Q') < epsilon) (r stage t : Nat)
    (hr : inclusionModulus w hd hs base H x y epsilon ≤ r) :
    chartScalar hw0 hw1 (paddedWidth base r) stage H (recenter r x) (recenter r y) t ≤
        chartScalar hw0 hw1 (paddedWidth larger r) stage H
          (recenter r (inclusion h x)) (recenter r (inclusion h y)) t + epsilon ∧
      chartScalar hw0 hw1 (paddedWidth larger r) stage H
          (recenter r (inclusion h x)) (recenter r (inclusion h y)) t ≤
        chartScalar hw0 hw1 (paddedWidth base r) stage H (recenter r x) (recenter r y) t + epsilon := by
  have hn : geometricCutoff (entropyRate 625 (adjustedCoreRate w hd))
      (spatialAmplitude w hd hs base H x y) epsilon ≤ r+1-carrierSize (boxSize base H) := by
    unfold inclusionModulus at hr
    omega
  have hgeo := geometric_bound (rate_nonnegative hw0 hd) hs
    (spatialAmplitude_nonnegative w hd hs base H x y hx hy) he _ hn
  have hsmall' := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hgeo
  have habs := Q'.le_trans' _ _ _
    (chartScalar_inclusion_bound hw0 hw1 hsmall hd hs h r H t stage hb x y hx hy) hsmall'
  have hpair := Q'.two_sided_of_abs_sub_le habs
  exact ⟨hpair.2, hpair.1⟩

/-- Uniqueness of the actual three-regulator diagonal limits. The two
existing Cauchy moduli remain intact; no width-uniform time modulus is used. -/
theorem spatialLimit_inclusion {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger) (H : Nat) (hb : 0<base)
    (x y : PhysicalSpan base) (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    Equiv (spatialLimit hw0 hw1 base H x y hx hy hsmall hd hs hb)
      (spatialLimit hw0 hw1 larger H (inclusion h x) (inclusion h y) hx hy
        hsmall hd hs (Nat.lt_of_lt_of_le hb h)) := by
  apply Equiv_of_ofQ'_limit_close
    (spatial_diagonal_converges hw0 hw1 base H x y hx hy hsmall hd hs hb)
    (spatial_diagonal_converges hw0 hw1 larger H (inclusion h x) (inclusion h y)
      hx hy hsmall hd hs (Nat.lt_of_lt_of_le hb h))
  intro epsilon he
  exact ⟨inclusionModulus w hd hs base H x y epsilon, fun n hn =>
    chartScalar_inclusion_close hw0 hw1 hsmall hd hs h H hb x y hx hy epsilon he n n n hn⟩

/-- The limiting reflected form, not a finite-box form, is independent of
enlarging the base guard around the unchanged original physical face words. -/
theorem spatialPairing_inclusion {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger) (hb : 0<base) (x y : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 base hsmall hd hs hb x y)
      (spatialPairing hw0 hw1 larger hsmall hd hs (Nat.lt_of_lt_of_le hb h)
        (inclusion h x) (inclusion h y)) := by
  let H := max (radius x.val) (radius y.val)
  have hx : radius x.val ≤ H := Nat.le_max_left _ _
  have hy : radius y.val ≤ H := Nat.le_max_right _ _
  exact Equiv.trans (spatialPairing_chart hw0 hw1 base hsmall hd hs hb x y H hx hy)
    (Equiv.trans (spatialLimit_inclusion hw0 hw1 hsmall hd hs h H hb x y hx hy)
      (Equiv.symm (spatialPairing_chart hw0 hw1 larger hsmall hd hs (Nat.lt_of_lt_of_le hb h)
        (inclusion h x) (inclusion h y) H hx hy)))

#print axioms inside_finiteValue_pin
#print axioms included_chartProbe_local
#print axioms chartScalar_inclusion_bound
#print axioms inclusionModulus
#print axioms chartScalar_inclusion_close
#print axioms spatialLimit_inclusion
#print axioms spatialPairing_inclusion

end YMGap.Continuum.BF4ExactSlabFixedSpatialBaseCoherence
