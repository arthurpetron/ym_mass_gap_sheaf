/-
# An actual Wilson-word mode retained in the ORIGINAL transfer reserve

The literal padded square has bare Haar moments zero and one and the actual
active product heat multiplier w^(12*side). Apply the two-mode kinetic floor
to V*h, with every original spatial factor retained. This gives a genuine
additional squared tested overlap for arbitrary supported signed h.

For the chronological OWN-centered filtered block source it bounds the
COMPLETE cleared Rayleigh cost, preserving both distinct partitions. The
magnitude of this reserve relative to the filtered norm on a justified
changing family remains open; no interacting eigenpin or survival is claimed.
-/

import YMGap.Continuum.SU2QuaternionProductHeatTwoModeFloor
import YMGap.Continuum.SU2QuaternionProductHeatSpectatorWilsonWord
import YMGap.Continuum.QuaternionHaarWordDifference
import YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit

namespace YMGap.Continuum.BF4DyadicWilsonSquareLoopModeReserve

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
  (wordAt word_independent productMap_fundamental_word)
open YMGap.Continuum.SU2QuaternionProductHeatSpectatorWilsonWord (fundamental_word_first_moment)
open YMGap.Continuum.SU2QuaternionIndependentTailMoments (fundamental_second_moment)
open YMGap.Continuum.SU2QuaternionProductHeatTwoModeFloor (kineticPair_two_mode_floor)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm (kineticPair)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
  (haarNorm_coordinate polyQuaternionNorm_conj)
open YMGap.Continuum.QuaternionHaarWordDifference (word_unit)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate supported_one haar_of_coeff)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (link orientedLink spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceWord sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_nodup activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (source_edges_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (original_quadratic_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare (side square square_length paddedSquare paddedSquare_edges)
open YMGap.Continuum.BF4DyadicWilsonSquareNodup (paddedSquare_indices_nodup)
open YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge
  (selectedEdge dyadicTail paddedSquare_edges_split selectedEdge_mem_paddedSquare)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter weightedMass
  originalBlockTransfer middleRatio transferStep clearedRayleighCost

private theorem wordAt_sourceWord (width : Nat) :
    ∀ es : List OrientedBF4Link,
      (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e::es, h => by
      have he := h e List.mem_cons_self
      change PolyQuaternion.mul
          (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
          (wordAt (fun d => (baseLinks width).idxOf d.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es (fun d hd => h d (List.mem_cons_of_mem e hd))]
      unfold orientedLink link
      rw [if_pos he]
      rfl

private theorem wordAt_unit (n : Nat) (block : OrientedBF4Link → Nat)
    (es : List OrientedBF4Link) (h : ∀ e, e ∈ es → block e < n) :
    HaarCarrierEqv n (polyQuaternionNorm (wordAt block es)) polyOne := by
  unfold wordAt
  apply word_unit
  intro e he
  cases e.reverse with
  | false => exact haarNorm_coordinate (h e he)
  | true =>
      exact (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans
        (haarNorm_coordinate (h e he))

private theorem bare_square_moments (scale width : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    quaternionHaar (N width) f ≈ 0 ∧ quaternionHaar (N width) (polyMul f f) ≈ 1 := by
  dsimp only
  let block : OrientedBF4Link → Nat := fun e => (baseLinks width).idxOf e.link
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let i := block selectedEdge
  have hphysical := (paddedSquare scale width hwidth).physical
  have hi : i < N width := List.idxOf_lt_length_of_mem
    (hphysical selectedEdge (selectedEdge_mem_paddedSquare scale width hwidth))
  have htail : ∀ d, d ∈ dyadicTail scale → block d < N width := by
    intro d hd
    apply List.idxOf_lt_length_of_mem
    apply hphysical d
    rw [paddedSquare_edges_split]
    exact List.mem_cons_of_mem selectedEdge hd
  have hnd := paddedSquare_indices_nodup scale width hwidth
  rw [paddedSquare_edges_split, List.map_cons, List.nodup_cons] at hnd
  have habsent : ∀ d, d ∈ dyadicTail scale → i ≠ block d := by
    intro d hd heq
    exact hnd.1 (List.mem_map.mpr ⟨d,hd,heq.symm⟩)
  have hone : QuaternionBlockIndependent i polyOne := by
    intro term ht
    simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst term
    rfl
  have hfpin : characterPolynomial (wordAt block (selectedEdge::dyadicTail scale)).scalar 1 = f := by
    rw [← paddedSquare_edges_split scale width hwidth]
    rw [wordAt_sourceWord width _ hphysical]
    unfold f sourceCharacter
    rfl
  have hzero := fundamental_word_first_moment (N width) block selectedEdge (dyadicTail scale)
    hi (by rfl) habsent polyOne hone
  rw [hfpin] at hzero
  have hhead : characterPolynomial
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable i) (wordAt block (dyadicTail scale))).scalar 1 = f := by
    simpa only [wordAt, wordWith, selectedEdge, orientedCoordinateQuaternion,
      Bool.false_eq_true, if_false] using hfpin
  have hsecond := fundamental_second_moment (N width) i hi (wordAt block (dyadicTail scale))
    polyOne (word_independent i block (dyadicTail scale) habsent) hone
    (wordAt_unit (N width) block (dyadicTail scale) htail)
  rw [hhead] at hsecond
  exact ⟨Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (blocks := N width)
      (RatPolyCoeffEqv.mul_one f))) hzero,
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (blocks := N width)
      (RatPolyCoeffEqv.mul_one (polyMul f f))))
      (Q'.eqv_trans _ _ _ hsecond (haar_one (N width)))⟩

/-- A genuine two-mode ORIGINAL transfer floor, for every supported signed
source h. The original V*h is not assumed positive or independent of f. -/
theorem paddedSquare_transfer_loop_mode_floor (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (hK1 : 1 ≤ K) (scale width : Nat) (hwidth : side scale < width)
    (h : RatPoly) (hh : SupportedQuaternionBlocks (N width) h) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    weightedMass w K width h * weightedMass w K width h +
        qpow w (12*side scale)*(weightedMass w K width (polyMul h f)*
          weightedMass w K width (polyMul h f)) ≤
      weightedMass w K width (polyMul h (transferStep w K width h)) := by
  dsimp only
  let es := (paddedSquare scale width hwidth).edges
  let block : OrientedBF4Link → Nat := fun e => (baseLinks width).idxOf e.link
  let f := sourceCharacter width es 1
  let p := polyMul (spatialWeight w K width) h
  have hp := supported_polyMul (spatialWeight_supported w K width) hh
  have hf := sourceCharacter_supported width es 1
  have hactive : ∀ e, e ∈ es → block e ∈ activeBlocks width := by
    intro e he
    apply source_edges_active_after_padding hwidth (square scale) e
    rw [← paddedSquare_edges scale width hwidth]
    exact he
  have hword := wordAt_sourceWord width es (paddedSquare scale width hwidth).physical
  have htrace : characterPolynomial (sourceWord width es).scalar 1 = f := by
    unfold f sourceCharacter
    rfl
  have hlen : 3*es.length = 12*side scale := by
    dsimp only [es]
    rw [paddedSquare_edges, square_length]
    omega
  have heigen := productMap_fundamental_word (N width) w K hK1 block es
    (activeBlocks width) (activeBlocks_nodup width) (activeBlocks_lt width)
    (paddedSquare_indices_nodup scale width hwidth) hactive
  dsimp only at heigen
  rw [hword, htrace, hlen] at heigen
  have hmom := bare_square_moments scale width hwidth
  have hfloor := kineticPair_two_mode_floor (N width) w hw K (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) f hf (qpow w (12*side scale))
    heigen hmom.1 hmom.2 p hp
  have htested : quaternionHaar (N width) (polyMul p f) ≈
      weightedMass w K width (polyMul h f) := by
    unfold weightedMass
    exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) h f)
  have hmean : weightedMass w K width h ≈ quaternionHaar (N width) p := by
    unfold weightedMass
    exact Q'.eqv_refl _
  have hleft : weightedMass w K width h * weightedMass w K width h +
      qpow w (12*side scale)*(weightedMass w K width (polyMul h f)*weightedMass w K width (polyMul h f)) ≈
      quaternionHaar (N width) p * quaternionHaar (N width) p +
        qpow w (12*side scale)*(quaternionHaar (N width) (polyMul p f)*quaternionHaar (N width) (polyMul p f)) :=
    Q'.add_eqv_congr' (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hmean) (Q'.mul_eqv_congr_left _ _ _ hmean))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm htested))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm htested))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hfloor (Q'.ge_of_eqv (original_quadratic_pin w K width h)))

/-- Complete cleared cost of the SAME half-smoothed OWN-centered source.
Both partitions and the additional squared tested overlap stay literal. -/
theorem paddedSquare_own_block_cost_loop_reserve {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hhead : headCutoff w ≤ K) (hK1 : 1 ≤ K)
    (n t scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let c := middleRatio hw0 hw1 K width hhead (n+1) n f
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) (shifted f c))
    let Z0 := weightedMass w K width (polyMul A A)
    let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
    clearedRayleighCost w K width A b + Z0*(weightedMass w K width b*weightedMass w K width b +
        qpow w (12*side scale)*(weightedMass w K width (polyMul b f)*weightedMass w K width (polyMul b f))) ≤
      Z1*weightedMass w K width (polyMul b b) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let c := middleRatio hw0 hw1 K width hhead (n+1) n f
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) (shifted f c))
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let S := weightedMass w K width (polyMul b b)
  let J := weightedMass w K width (polyMul b (transferStep w K width b))
  let reserve := weightedMass w K width b*weightedMass w K width b +
    qpow w (12*side scale)*(weightedMass w K width (polyMul b f)*weightedMass w K width (polyMul b f))
  have hb : SupportedQuaternionBlocks (N width) b := by
    unfold b originalBlockTransfer
    exact iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width) t
      (supported_polyMul (terminalMessage_supported w K width n)
        (shifted_supported (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1) c))
  have hZ0 : (0 : Q') ≤ Z0 := weightedMass_nonnegative hw0 hw1 K width hhead
    (Certificate.square A (terminalMessage_supported w K width (n+t)))
  have hreserve : reserve ≤ J :=
    paddedSquare_transfer_loop_mode_floor w (Q'.le_of_lt hw0) K hK1 scale width hwidth b hb
  have hscaled := Q'.mul_le_mul_of_nonneg_left reserve J Z0 hreserve hZ0
  have hsum := Q'.add_le_add_left (clearedRayleighCost w K width A b) _ _ hscaled
  have hcancel : clearedRayleighCost w K width A b+Z0*J ≈ Z1*S := by
    unfold clearedRayleighCost
    change (Z1*S + -(Z0*J))+Z0*J ≈ Z1*S
    exact poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
        (.mul (.var 2) (.var 3))) (.mul (.var 0) (.var 1)) (by decide)
      (fun
        | 0 => Z1
        | 1 => S
        | 2 => Z0
        | _ => J)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcancel)

#print axioms paddedSquare_transfer_loop_mode_floor
#print axioms paddedSquare_own_block_cost_loop_reserve

end YMGap.Continuum.BF4DyadicWilsonSquareLoopModeReserve
