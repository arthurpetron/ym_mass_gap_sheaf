/-
# Original growing Wilson-square curvature and Ward moments

The literal loop has L=4*side distinct links. Every selected block contributes
4-f^2 to its angular square; spectators contribute zero. The COMPLETE
original odd marginal, its OWN mean and partition therefore give
Var=1+m2-m1^2, Angular=L*(3-m2), Ward=L*(4*m2-3*m1^2).
Here m2 is the label-two CHARACTER moment, not the second scalar moment.

The produced relative scores also give a positive nome-dependent OWN
variance floor, uniform in square size, width and depth after the explicit
cutoff. Its limit is the SAME original completed centered norm. The complete
Taylor remainder is retained; no response survival or physical trajectory follows.
-/

import YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare
import YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor
import YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
import YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo
import YMGap.Continuum.QuaternionHaarGeneralizedLinearWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare

namespace YMGap.Continuum.BF4DyadicWilsonSquareWardMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor (ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSquareLocality
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma blockGamma)
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard
open YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion orientedCoordinateQuaternion_blockDegree)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt word_independent)
open YMGap.Continuum.QuaternionHaarWordDifference (word_unit)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six angularSquare)
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_sum_indexed)
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_add supported_one)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceWord sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor (varianceRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_normalized_ward)
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarAngularCarrier (carrierOfPrefix)
open YMGap.Continuum.QuaternionHaarGeneralizedLinearWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound (frameRelativeBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound (endpointRelativeCutoff)
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks

private theorem blockSquare_coeff (block : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularSquare block p) (blockAngularSquare block q) := by
  have hd (i j : Nat) := angularDerivative_congr (4*block+i) (4*block+j) h
  unfold blockAngularSquare six
  exact ((hd 0 1).mul (hd 0 1)).add
    (((hd 0 2).mul (hd 0 2)).add
      (((hd 0 3).mul (hd 0 3)).add
        (((hd 1 2).mul (hd 1 2)).add
          (((hd 1 3).mul (hd 1 3)).add ((hd 2 3).mul (hd 2 3))))))

private theorem angular_of_recode {blocks block : Nat} {f g : RatPoly}
    (h : RatPolyCoeffEqv f g)
    (hg : HaarCarrierEqv blocks (blockAngularSquare block g)
      (polyAdd (cap 4) (polyNeg (polyMul g g)))) :
    HaarCarrierEqv blocks (blockAngularSquare block f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) :=
  (RatPolyCoeffEqv.haarCarrier (blockSquare_coeff block h)).trans
    (hg.trans (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (h.symm.mul h.symm)))))

private theorem scalar_conj_comm (p q : PolyQuaternion) :
    RatPolyCoeffEqv (p ⋄ PolyQuaternion.conj q).scalar
      (q ⋄ PolyQuaternion.conj p).scalar := by
  let env : Nat → RatPoly := fun
    | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
    | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart
  simpa only [PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
    PolyQuaternionExpr.coordinate, coeffEvalExpr, env,
    PolyQuaternion.mul, PolyQuaternion.conj] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))).scalar
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
      (by decide) env)

private theorem oriented_prefix_angular {blocks block : Nat} (hb : block < blocks)
    (p q : PolyQuaternion) (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hq : HasPolyQuaternionBlockDegree block 0 q)
    (hnp : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (hnq : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) (reverse : Bool) :
    let f := characterPolynomial
      (p ⋄ (orientedCoordinateQuaternion block reverse ⋄ q)).scalar 1
    HaarCarrierEqv blocks (blockAngularSquare block f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
  dsimp only
  let tail := q ⋄ p
  have hd : HasPolyQuaternionBlockDegree block 0 tail := by simpa using hq.mul hp
  have hn : HaarCarrierEqv blocks (polyQuaternionNorm tail) polyOne := haarNorm_mul hnq hnp
  have cyclic (r : Bool) : RatPolyCoeffEqv
      (characterPolynomial (p ⋄ (orientedCoordinateQuaternion block r ⋄ q)).scalar 1)
      (characterPolynomial (orientedCoordinateQuaternion block r ⋄ tail).scalar 1) :=
    characterPolynomial_coeffEqv
      ((polyQuaternion_mul_scalar_cyclic p (orientedCoordinateQuaternion block r ⋄ q)).trans
        (PolyQuaternionCoeffEqv.mul_assoc (orientedCoordinateQuaternion block r) q p).scalar) 1
  cases reverse with
  | false =>
      exact angular_of_recode (cyclic false)
        (fundamental_angularSquare hb tail hd hn)
  | true =>
      have hconj : RatPolyCoeffEqv
          (characterPolynomial (orientedCoordinateQuaternion block true ⋄ tail).scalar 1)
          (characterPolynomial (PolyQuaternion.coordinateVariable block ⋄ PolyQuaternion.conj tail).scalar 1) :=
        characterPolynomial_coeffEqv
          ((polyQuaternion_mul_scalar_cyclic (PolyQuaternion.conj (PolyQuaternion.coordinateVariable block)) tail).trans
            (scalar_conj_comm tail (PolyQuaternion.coordinateVariable block))) 1
      have hn' := (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj tail)).trans hn
      exact angular_of_recode ((cyclic true).trans hconj)
        (fundamental_angularSquare hb (PolyQuaternion.conj tail) hd.conj hn')

private theorem letter_unit {blocks block : Nat} (hb : block < blocks) (r : Bool) :
    HaarCarrierEqv blocks (polyQuaternionNorm (orientedCoordinateQuaternion block r)) polyOne := by
  cases r
  · exact haarNorm_coordinate hb
  · exact (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans (haarNorm_coordinate hb)

private theorem word_selected_angular {blocks block : Nat} (hb : block < blocks)
    (index : OrientedBF4Link → Nat) : ∀ (es : List OrientedBF4Link),
    (es.map index).Nodup → (∀ e, e ∈ es → index e < blocks) → block ∈ es.map index →
    ∀ (p : PolyQuaternion), HasPolyQuaternionBlockDegree block 0 p →
    HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne →
    let f := characterPolynomial (p ⋄ wordAt index es).scalar 1
    HaarCarrierEqv blocks (blockAngularSquare block f)
      (polyAdd (cap 4) (polyNeg (polyMul f f)))
  | [], _, _, hm, _, _, _ => False.elim (List.not_mem_nil hm)
  | e::es, hnd, hrange, hm, p, hp, hnp => by
      have hn := List.nodup_cons.mp hnd
      let c := orientedCoordinateQuaternion (index e) e.reverse
      by_cases hi : block = index e
      · have hd : HasPolyQuaternionBlockDegree block 0 (wordAt index es) :=
          word_independent block index es (fun f hf he =>
            hn.1 (List.mem_map.mpr ⟨f,hf,he.symm.trans hi⟩))
        have hunit : HaarCarrierEqv blocks (polyQuaternionNorm (wordAt index es)) polyOne :=
          word_unit (fun f => orientedCoordinateQuaternion (index f) f.reverse) es
            (fun f hf => letter_unit (hrange f (List.mem_cons_of_mem e hf)) f.reverse)
        simpa only [wordAt, hi] using
          oriented_prefix_angular (hi ▸ hb) p (wordAt index es) (hi ▸ hp) (hi ▸ hd)
            hnp hunit e.reverse
      · have hc := orientedCoordinateQuaternion_blockDegree (index e) block e.reverse
        rw [if_neg hi] at hc
        have hp' : HasPolyQuaternionBlockDegree block 0 (p ⋄ c) := by simpa using hp.mul hc
        have hn' := haarNorm_mul hnp (letter_unit (hrange e List.mem_cons_self) e.reverse)
        have ht := word_selected_angular hb index es hn.2
          (fun f hf => hrange f (List.mem_cons_of_mem e hf))
          ((List.mem_cons.mp hm).resolve_left hi) (p ⋄ c) hp' hn'
        exact angular_of_recode
          (characterPolynomial_coeffEqv (PolyQuaternionCoeffEqv.mul_assoc p c (wordAt index es)).scalar.symm 1) ht

private theorem wordAt_sourceWord (width : Nat) : ∀ es : List OrientedBF4Link,
    (∀ e, e ∈ es → e.link ∈ baseLinks width) →
    wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e::es, hp => by
      have he := hp e List.mem_cons_self
      change orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse ⋄
          wordAt (fun f => (baseLinks width).idxOf f.link) es =
        orientedLink width e ⋄ sourceWord width es
      rw [wordAt_sourceWord width es (fun f hf => hp f (List.mem_cons_of_mem e hf))]
      unfold orientedLink link
      rw [if_pos he]
      rfl

/-- Exact angular square of every ACTUAL selected link of the growing loop. -/
theorem paddedSquare_block_gamma (scale width : Nat) (hwidth : side scale < width)
    (block : Nat) (hb : block ∈ observableBlocks scale width hwidth) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    HaarCarrierEqv (N width) (blockAngularSquare block f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
  dsimp only
  let es := (paddedSquare scale width hwidth).edges
  let index := fun e : OrientedBF4Link => (baseLinks width).idxOf e.link
  have hrange : ∀ e, e ∈ es → index e < N width := fun e he =>
    List.idxOf_lt_length_of_mem ((paddedSquare scale width hwidth).physical e he)
  have hmem : block ∈ es.map index := of_decide_eq_true (List.mem_filter.mp hb).2
  have hp : HasPolyQuaternionBlockDegree block 0 PolyQuaternion.one :=
    ⟨hasQuaternionBlockDegree_one block, hasQuaternionBlockDegree_zero block 0,
      hasQuaternionBlockDegree_zero block 0, hasQuaternionBlockDegree_zero block 0⟩
  have ht := word_selected_angular (observableBlocks_lt scale width hwidth block hb)
    index es (paddedSquare_indices_nodup scale width hwidth) hrange hmem
    PolyQuaternion.one hp (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one)
  have hout := angular_of_recode
    (characterPolynomial_coeffEqv (PolyQuaternionCoeffEqv.one_mul (wordAt index es)).scalar.symm 1) ht
  rw [wordAt_sourceWord width es (paddedSquare scale width hwidth).physical] at hout
  exact hout

attribute [local irreducible] terminalMessage spatialWeight sourceWord sourceCharacter
  marginalWeight oddMass oddVariance
  BF4WilsonAllNomeMarginalVarianceLimit.varianceCauchy
  BF4WilsonAllNomeMarginalVarianceLimit.varianceLimit

private theorem gap_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyAdd (cap 4) (polyNeg (polyMul p p))) := by
  apply supported_add
  · intro t ht
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
    exact supported_one blocks r hr
  · intro t ht
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
    exact supported_polyMul hp hp r hr

/-- Selected-link transport at the full carrier level, permitting every
original density insertion. Unweighted Haar equality alone would not suffice. -/
theorem paddedSquare_head_gamma (scale width : Nat) (hwidth : side scale < width)
    (block : Nat) (hb : block ∈ observableBlocks scale width hwidth) :
    let swap := headSwapBlockInvolution (N width) block
      (observableBlocks_lt scale width hwidth block hb)
    let f := reindexQuaternionPolynomial swap
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
    HaarCarrierEqv (N width) (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
  dsimp only
  let p := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let swap := headSwapBlockInvolution (N width) block
    (observableBlocks_lt scale width hwidth block hb)
  have hp := BF4ExactSlabFixedSpatialWilsonProbe.sourceCharacter_supported width
    (paddedSquare scale width hwidth).edges 1
  have h0 : 0 < N width := Nat.lt_of_le_of_lt (Nat.zero_le block)
    (observableBlocks_lt scale width hwidth block hb)
  have hmap : swap.map 0 = block := headSwapBlockInvolution_map_zero _ _ _
  have hd := BF4ExactSlabFixedSpatialPlaquetteAngularSquare.reindex_blockAngularSquare_carrier
    swap h0 p hp
  rw [hmap] at hd
  have hg := reindex_carrier swap
    (blockAngularSquare_supported (observableBlocks_lt scale width hwidth block hb) hp)
    (gap_supported hp) (paddedSquare_block_gamma scale width hwidth block hb)
  have hone : QuaternionPrefixPolynomialEqv (N width)
      (reindexQuaternionPolynomial swap polyOne) polyOne := by
    change QuaternionPrefixPolynomialEqv (N width)
      [(reindexQuaternionExponents swap [], 1)] [([], 1)]
    apply QuaternionPrefixPolynomialEqv.cons
    · constructor
      · exact Q'.eqv_refl 1
      · intro coordinate hc
        rw [exponentAt_reindexQuaternionExponents swap [] hc]
        simp [exponentAt]
    · exact .nil
  have hgap : QuaternionPrefixPolynomialEqv (N width)
      (reindexQuaternionPolynomial swap (polyAdd (cap 4) (polyNeg (polyMul p p))))
      (polyAdd (cap 4) (polyNeg (polyMul (reindexQuaternionPolynomial swap p)
        (reindexQuaternionPolynomial swap p)))) := by
    unfold cap
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg,
      reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_smul]
    exact (hone.smul 4).append (.refl _ _)
  have hc := carrierOfPrefix (reindex_supported swap _)
    (gap_supported (reindex_supported swap p)) hgap
  simpa only [blockAngularSquare, blockAngularDerivative, Nat.mul_zero, Nat.zero_add,
    angularSquare] using hd.symm.trans (hg.trans hc)

private theorem selected_variance_score_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width n scale : Nat) (hK : endpointRelativeCutoff w ≤ K)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    scoreVarianceFloor (marginalScoreCap w) ≤
      oddVariance hw0 hw1 K width hhead n
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  dsimp only
  let p := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have hp := BF4ExactSlabFixedSpatialWilsonProbe.sourceCharacter_supported width
    (paddedSquare scale width hwidth).edges 1
  have hidx := observableBlocks_lt scale width hwidth block hb
  have h0 : 0 < N width := Nat.lt_of_le_of_lt (Nat.zero_le block) hidx
  have hlen : N width-1+1 = N width := Nat.sub_add_cancel h0
  let swap := headSwapBlockInvolution (N width) block hidx
  let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
  let W := frameWeight w K width n swap
  have hmem := of_decide_eq_true (List.mem_filter.mp hb).2
  obtain ⟨edge,he,hblock⟩ := List.mem_map.mp hmem
  have hl := (paddedSquare scale width hwidth).physical edge he
  have hactive : (baseLinks width).idxOf edge.link ∈
      BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks width := by
    apply BF4ExactSlabFixedSpatialWilsonActivePadding.source_edges_active_after_padding
      hwidth (square scale) edge
    rw [← paddedSquare_edges scale width hwidth]
    exact he
  have hrel (i j : Nat) (hi : i < 4) (hj : j < 4) :
      QuaternionHaarRelativeAngularBound.RelativeBound (N width-1+1) i j W
        (marginalScoreCap w) := by
    rw [hlen]
    simpa only [marginalScoreCap, W, swap, hblock] using
      frameRelativeBound hw0 hw1 K width n hK edge.link hl hactive hi hj
  have hlinear : HasQuaternionBlockDegree 0 1 (reindexQuaternionPolynomial swap p) :=
    blockDegree_reindex swap h0 (headSwapBlockInvolution_map_zero _ _ _)
      (BF4DyadicWilsonSquareVarianceTaylor.paddedSquare_character_degree
        scale width hwidth block hb)
  have hfloor := original_score_variance_floor (tail := N width-1)
    (marginalScoreCap_positive hw0) hrel
    (by rw [hlen]; exact reindex_supported swap p)
    hlinear (by rw [hlen]; exact paddedSquare_head_gamma scale width hwidth block hb)
    (by rw [hlen]; exact frameMass_positive hw0 hw1 K width hhead n swap)
  simp only [hlen] at hfloor
  exact Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv
    (by simpa only [oddVariance] using
      (frameVariance_pin hw0 hw1 K width hhead n swap p hp)))

private theorem gamma_perm (p q : RatPoly) {first second : List Nat} (h : first.Perm second) :
    RatPolyCoeffEqv (activeGamma first p q) (activeGamma second p q) := by
  unfold activeGamma
  induction h with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons x _ ih => exact (RatPolyCoeffEqv.refl (blockGamma x p q)).add ih
  | swap x y rest =>
      exact (RatPolyCoeffEqv.add_assoc _ _ _).symm.trans
        (((RatPolyCoeffEqv.add_comm (blockGamma y p q) (blockGamma x p q)).add
          (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.add_assoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem gamma_passive : ∀ (rest : List Nat) (p : RatPoly),
    (∀ i, i ∈ rest → QuaternionBlockIndependent i p) →
    RatPolyCoeffEqv (activeGamma rest p p) polyZero
  | [], _, _ => RatPolyCoeffEqv.refl polyZero
  | i::rest, p, h => ((blockAngularSquare_zero (h i List.mem_cons_self)).add
      (gamma_passive rest p (fun j hj => h j (List.mem_cons_of_mem i hj)))).trans
        (RatPolyCoeffEqv.add_zero polyZero)

private theorem gamma_active {blocks : Nat} (f gap : RatPoly) : ∀ active : List Nat,
    (∀ i, i ∈ active → HaarCarrierEqv blocks (blockAngularSquare i f) gap) →
    HaarCarrierEqv blocks (activeGamma active f f) (polySmul (Q'.ofNat active.length) gap)
  | [], _ => (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.smul_coefficient Q'.ofNat_zero_eqv gap).trans
        (RatPolyCoeffEqv.zero_smul gap))).symm
  | i::rest, h => by
      have hs := (h i List.mem_cons_self).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_smul gap).symm)
      have ht := gamma_active f gap rest (fun j hj => h j (List.mem_cons_of_mem i hj))
      have hc : (1 : Q')+Q'.ofNat rest.length ≈ Q'.ofNat (i::rest).length :=
        Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
          (.add (.const 1) (.var 0)) (.add (.var 0) (.const 1))
          (by decide) (fun _ => Q'.ofNat rest.length))
          (Q'.eqv_symm (Q'.ofNat_add_eqv rest.length 1))
      exact (HaarCarrierEqv.add hs ht).trans (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.add_smul_same 1 (Q'.ofNat rest.length) gap).trans
          (RatPolyCoeffEqv.smul_coefficient hc gap)))

private theorem observable_length (scale width : Nat) (hwidth : side scale < width) :
    (observableBlocks scale width hwidth).length = 4*side scale := by
  have hp := Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
    (observableBlocks scale width hwidth) (loopSlots scale width hwidth)
    (observableBlocks_nodup scale width hwidth) (loopSlots_nodup scale width hwidth)
    (fun i => by
      constructor
      · intro hi
        exact of_decide_eq_true (List.mem_filter.mp hi).2
      · intro hi
        obtain ⟨e, he, hidx⟩ := List.mem_map.mp hi
        exact List.mem_filter.mpr ⟨List.mem_range.mpr (hidx ▸
          List.idxOf_lt_length_of_mem ((paddedSquare scale width hwidth).physical e he)), by simp [hi]⟩)
  exact hp.length_eq.trans (loopSlots_length scale width hwidth)

/-- Literal amplitude-four original OWN variance floor. The selected active
link is produced from the nonempty square, not an additional geometry input. -/
theorem paddedSquare_variance_score_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width n scale : Nat) (hK : endpointRelativeCutoff w ≤ K)
    (hwidth : side scale < width) :
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK
    scoreVarianceFloor (marginalScoreCap w) ≤
      oddVariance hw0 hw1 K width hhead n
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  cases hs : observableBlocks scale width hwidth with
  | nil =>
      have h := observable_length scale width hwidth
      rw [hs] at h
      have hp := side_positive scale
      simp only [List.length_nil] at h
      omega
  | cons block rest =>
      exact selected_variance_score_floor hw0 hw1 K width n scale hK hwidth block
        (by rw [hs]; exact List.mem_cons_self)

/-- The finite odd-marginal floor passes through its existing variance
modulus to the SAME completed time-zero centered norm. No odd/even finite
partition equality or changing-family convergence is assumed. -/
theorem paddedSquare_centeredNorm_score_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (scale width : Nat) (hwidth : side scale < width) :
    CReal.leEv (CReal.ofQ' (scoreVarianceFloor (marginalScoreCap w)))
      (BF4WilsonAllNomeCenteredMoments.centeredTimeMoment hw0 hw1 0
        (BF4WilsonAllNomeLoopTimePin.loopState (paddedSquare scale width hwidth))
        (BF4WilsonAllNomeLoopTimePin.loopState (paddedSquare scale width hwidth))) := by
  let e : BF4ExactSlabFixedSpatialWilsonWindow.WindowExpression width :=
    .loop 0 (paddedSquare scale width hwidth) 1
  let he : BF4ExactSlabFixedSpatialWilsonWindow.Within 0 e := Nat.le_refl 0
  let L := BF4WilsonAllNomeMarginalVarianceLimit.varianceLimit hw0 hw1 e he
  have hlimit : CReal.leEv (CReal.ofQ' (scoreVarianceFloor (marginalScoreCap w))) L := by
    intro epsilon hepsilon
    refine ⟨(BF4WilsonAllNomeMarginalVarianceLimit.varianceCauchy hw0 hw1 e he).M
      epsilon, ?_⟩
    intro p hp
    let k := max
      (BF4WilsonAllNomeMarginalVarianceLimit.varianceCutoffThreshold hw0 hw1 e he epsilon)
      (endpointRelativeCutoff w)
    let t := BF4WilsonAllNomeMarginalVarianceLimit.varianceTimeThreshold hw0 hw1 e he epsilon
    have hK : endpointRelativeCutoff w ≤ headCutoff w+k :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_left _ _)
    have hfloor := paddedSquare_variance_score_floor hw0 hw1 (headCutoff w+k)
      width t scale hK hwidth
    have hclose := (BF4WilsonAllNomeMarginalVarianceLimit.varianceLimit_approx
      hw0 hw1 e he epsilon hepsilon k t p (Nat.le_max_left _ _) (Nat.le_refl _) hp).1
    have hfinite : scoreVarianceFloor (marginalScoreCap w) ≤
        BF4WilsonAllNomeMarginalVarianceLimit.finiteVariance hw0 hw1 e k t := by
      simpa only [BF4WilsonAllNomeMarginalVarianceLimit.finiteVariance,
        BF4ExactSlabFixedSpatialWilsonWindow.sourcePolynomial, e, Nat.zero_mul,
        SU2QuaternionPartialFactorizedHaar.liftBoundary] using hfloor
    exact Q'.le_trans' _ _ _ hfinite hclose
  have hpin := BF4WilsonAllNomeMarginalVarianceLimit.varianceLimit_completed_pin
    hw0 hw1 e he
  have heq : CReal.Equiv L
      (BF4WilsonAllNomeCenteredMoments.centeredTimeMoment hw0 hw1 0
        (BF4WilsonAllNomeLoopTimePin.loopState (paddedSquare scale width hwidth))
        (BF4WilsonAllNomeLoopTimePin.loopState (paddedSquare scale width hwidth))) :=
    Quotient.exact (hpin.trans
      (BF4WilsonAllNomeCenteredVector.centeredVector_diagonal hw0 hw1
        (BF4WilsonAllNomeCenteredTransferBondLimit.singleSlice e he)))
  exact CReal.leEv_trans hlimit (CReal.leEv_of_equiv heq)

/-- Full ORIGINAL slice curvature, retaining every spectator insertion. -/
theorem paddedSquare_gamma (scale width : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    HaarCarrierEqv (N width) (activeGamma (List.range (N width)) f f)
      (polySmul (4*Q'.ofNat (side scale)) (polyAdd (cap 4) (polyNeg (polyMul f f)))) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let gap := polyAdd (cap 4) (polyNeg (polyMul f f))
  have hperm := gamma_perm f f (spectator_observable_cover scale width hwidth).symm
  have happ : RatPolyCoeffEqv
      (activeGamma (spectatorBlocks scale width hwidth ++ observableBlocks scale width hwidth) f f)
      (polyAdd (activeGamma (spectatorBlocks scale width hwidth) f f)
        (activeGamma (observableBlocks scale width hwidth) f f)) := by
    unfold activeGamma
    rw [List.map_append]
    exact (RatPolyCoeffEqv.polySum_append _ _).symm
  have hp := gamma_passive (spectatorBlocks scale width hwidth) f
    (sourceCharacter_spectator_independent scale width hwidth)
  have ha := gamma_active f gap (observableBlocks scale width hwidth)
    (paddedSquare_block_gamma scale width hwidth)
  have hc : Q'.ofNat (observableBlocks scale width hwidth).length ≈ 4*Q'.ofNat (side scale) := by
    rw [observable_length]
    exact ofNat_mul_eqv 4 (side scale)
  exact (RatPolyCoeffEqv.haarCarrier (hperm.trans (happ.trans
    ((hp.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _))))).trans
      (ha.trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_coefficient hc gap)))

/-- Actual original odd-marginal character moment. Every parameter remains explicit. -/
def squareMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) (label : Nat) : Q' :=
  middleRatio hw0 hw1 K width hK (n+1) n
    (sourceCharacter width (paddedSquare scale width hwidth).edges label)

private theorem square_fusion (width : Nat) (es : List OrientedBF4Link) :
    RatPolyCoeffEqv (polyMul (sourceCharacter width es 1) (sourceCharacter width es 1))
      (polyAdd polyOne (sourceCharacter width es 2)) := by
  unfold sourceCharacter
  exact first_character_square (sourceWord width es).scalar

private theorem moment_neg {blocks : Nat} {W p : RatPoly} (hZ : (0 : Q') < H blocks W) :
    normalizedMoment blocks W (polyNeg p) hZ ≈ -(normalizedMoment blocks W p hZ) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (haar_of_coeff ((neg_smul p).mul_left W)))
    (Q'.eqv_trans _ _ _ (normalizedMoment_smul hZ)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => normalizedMoment blocks W p hZ)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "m1" => squareMoment hw0 hw1 K width hK n scale hwidth 1
local notation "m2" => squareMoment hw0 hw1 K width hK n scale hwidth 2
local notation "L" => (4 : Q')*Q'.ofNat (side scale)

private theorem second_moment :
    normalizedMoment (N width) (marginalWeight w K width n) (polyMul f f)
      (marginalMass_positive hw0 hw1 K width hK n) ≈ 1+m2 := by
  let W := marginalWeight w K width n
  let hZ := marginalMass_positive hw0 hw1 K width hK n
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (haar_of_coeff ((square_fusion width (paddedSquare scale width hwidth).edges).mul_left W)))
    (Q'.eqv_trans _ _ _ (normalizedMoment_add hZ)
      (Q'.add_eqv_congr' (normalizedMoment_one hZ)
        (marginalMoment_pin hw0 hw1 K width hK n _)))

/-- OWN variance, with m2 the actual label-two moment, not E[f^2]. -/
theorem paddedSquare_variance : oddVariance hw0 hw1 K width hK n f ≈ 1+m2+ -(m1*m1) := by
  have hm := marginalMoment_pin hw0 hw1 K width hK n f
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (marginalVariance_pin hw0 hw1 K width hK n f))
    (Q'.add_eqv_congr' (second_moment hw0 hw1 K width hK n scale hwidth)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
        (Q'.mul_eqv_congr_left _ _ _ hm))))

/-- Original angular energy is perimeter times the label-two deficit. -/
theorem paddedSquare_angular : normalizedAngular hw0 hw1 K width hK n f ≈ L*(3-m2) := by
  let W := marginalWeight w K width n
  let hZ := marginalMass_positive hw0 hw1 K width hK n
  have hcap : normalizedMoment (N width) W (cap 4) hZ ≈ 4 :=
    Q'.eqv_trans _ _ _ (normalizedMoment_smul hZ)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _ (normalizedMoment_one hZ)) (Q'.mul_one_eqv 4))
  have hr : normalizedMoment (N width) W (activeGamma (List.range (N width)) f f) hZ ≈ L*(3-m2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (paddedSquare_gamma scale width hwidth W))
      (Q'.eqv_trans _ _ _ (normalizedMoment_smul hZ)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left L _ _
          (Q'.eqv_trans _ _ _ (normalizedMoment_add hZ)
            (Q'.add_eqv_congr' hcap (Q'.eqv_trans _ _ _ (moment_neg hZ)
              (Q'.neg_eqv_congr _ _ (second_moment hw0 hw1 K width hK n scale hwidth))))))
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.add (.const 4) (.neg (.add (.const 1) (.var 1)))))
            (.mul (.var 0) (.add (.const 3) (.neg (.var 1))))
            (by decide) (fun | 0 => L | _ => m2))))
  have ha : marginalAngular w K width n f ≈ H (N width) (polyMul W (activeGamma (List.range (N width)) f f)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (totalEnergy_finSum (N width) W f))
      (Q'.eqv_symm (haar_weighted_sum_indexed (N width) W (fun i => blockGamma i f f) (List.range (N width))))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.recipPos_eqv_congr _ _ (oddMass_positive hw0 hw1 K width hK n) hZ
        (marginalMass_pin w K width n).symm)) hr)

/-- COMPLETE differentiated-weight Ward term as two OWN moments. No sign is assigned. -/
theorem paddedSquare_ward : normalizedWardResidual hw0 hw1 K width hK n f ≈ L*(4*m2-3*(m1*m1)) := by
  have hj := paddedSquare_normalized_ward hw0 hw1 K width hK n scale hwidth
  have ha := paddedSquare_angular hw0 hw1 K width hK n scale hwidth
  have hv := paddedSquare_variance hw0 hw1 K width hK n scale hwidth
  have hright : (12*Q'.ofNat (side scale))*oddVariance hw0 hw1 K width hK n f ≈
      L*(3*(1+m2+ -(m1*m1))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hv)
      (poly_identity_of_normal_eq (.mul (.mul (.const 12) (.var 0)) (.var 1))
        (.mul (.mul (.const 4) (.var 0)) (.mul (.const 3) (.var 1)))
        (by decide) (fun | 0 => Q'.ofNat (side scale) | _ => 1+m2+ -(m1*m1)))
  have hsum : L*(3-m2)+normalizedWardResidual hw0 hw1 K width hK n f ≈
      L*(3*(1+m2+ -(m1*m1))) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_symm ha) (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ hj hright)
  have hcancel : (L*(3-m2)+normalizedWardResidual hw0 hw1 K width hK n f)+ -(L*(3-m2)) ≈
      normalizedWardResidual hw0 hw1 K width hK n f :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => L*(3-m2) | _ => normalizedWardResidual hw0 hw1 K width hK n f)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hsum (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.const 3) (.add (.add (.const 1) (.var 1)) (.neg (.mul (.var 2) (.var 2))))))
          (.neg (.mul (.var 0) (.add (.const 3) (.neg (.var 1))))))
        (.mul (.var 0) (.add (.mul (.const 4) (.var 1)) (.neg (.mul (.const 3) (.mul (.var 2) (.var 2))))))
        (by decide) (fun | 0 => L | 1 => m2 | _ => m1)))

/-- The existing COMPLETE remainder, with its Ward contribution now an exact
original two-character expression. This is not an error bound. -/
theorem paddedSquare_varianceRemainder : varianceRemainder hw0 hw1 K width hK n f ≈
    normalizedRemainder hw0 hw1 K width hK n f - ((1 : Q')-w)*(L*(4*m2-3*(m1*m1))) :=
  Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
      (paddedSquare_ward hw0 hw1 K width hK n scale hwidth)))

#print axioms paddedSquare_block_gamma
#print axioms paddedSquare_head_gamma
#print axioms paddedSquare_variance_score_floor
#print axioms paddedSquare_centeredNorm_score_floor
#print axioms paddedSquare_gamma
#print axioms squareMoment
#print axioms paddedSquare_variance
#print axioms paddedSquare_angular
#print axioms paddedSquare_ward
#print axioms paddedSquare_varianceRemainder

end YMGap.Continuum.BF4DyadicWilsonSquareWardMoments
