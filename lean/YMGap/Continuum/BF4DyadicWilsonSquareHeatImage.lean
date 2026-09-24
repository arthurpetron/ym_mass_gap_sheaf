/-
# Full-range fundamental heat image of a literal dyadic Wilson square

The generic distinct-link Wilson-word transmission applies to the actual
fixed-spatial source word of the padded dyadic square.  Its perimeter is
`4 * side scale`, so the fundamental kinetic multiplier is exactly
`w^(12 * side scale)`.  The final theorem retains an arbitrary supported
source in the Haar pairing.  Nothing here identifies an interacting
eigenmode or supplies the label-two square channel.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareNodup
import YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding

namespace YMGap.Continuum.BF4DyadicWilsonSquareHeatImage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding
  (source_edges_active_after_padding)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

private theorem wordAt_sourceWord (width : Nat) :
    ∀ (es : List OrientedBF4Link),
      (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e :: es, hphysical => by
      have he := hphysical e List.mem_cons_self
      have ht : ∀ f, f ∈ es → f.link ∈ baseLinks width :=
        fun f hf => hphysical f (List.mem_cons_of_mem e hf)
      change PolyQuaternion.mul
          (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
          (wordAt (fun f => (baseLinks width).idxOf f.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es ht]
      unfold orientedLink link
      rw [if_pos he]
      rfl

private theorem padded_wordAt_sourceWord (scale width : Nat)
    (hwidth : side scale < width) :
    wordAt (fun e => (baseLinks width).idxOf e.link)
        (paddedSquare scale width hwidth).edges =
      sourceWord width (paddedSquare scale width hwidth).edges := by
  apply wordAt_sourceWord
  exact (paddedSquare scale width hwidth).physical

/-- Strict padding makes the literal square character independent of every
uncoupled fringe block. This is the premise needed by the original signed
source-energy identity, not an assumed independence of its source. -/
theorem paddedSquare_fringe_independent (scale width : Nat)
    (hwidth : side scale < width) (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  have hd := word_independent i (fun e => (baseLinks width).idxOf e.link)
    (paddedSquare scale width hwidth).edges (by
      intro e he heq
      have he' : e ∈ (square scale).edges := by
        rw [← paddedSquare_edges scale width hwidth]
        exact he
      have ha := source_edges_active_after_padding hwidth (square scale) e he'
      exact ((fringeBlocks_mem_iff width i).mp hi).2 (heq.symm ▸ ha))
  rw [padded_wordAt_sourceWord scale width hwidth] at hd
  exact degree_zero_independent (hd.scalar.smul 2)

/-- The literal original fundamental square character is an exact eigenvector
of the full product heat alone, with one `w^3` factor per boundary link. -/
theorem paddedSquare_fundamental_fullRange
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 1 ≤ K) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    SupportedHaarEqv (N width)
      (productMap (N width) w K (List.range (N width)) f)
      (polySmul (qpow w (12 * side scale)) f) := by
  dsimp only
  let es := (paddedSquare scale width hwidth).edges
  let block : OrientedBF4Link → Nat := fun e => (baseLinks width).idxOf e.link
  have hgeneric := productMap_fundamental_word (N width) w K hK block es
    (List.range (N width)) (CayleyParentInj.range_nodup (N width))
    (fun i hi => List.mem_range.mp hi)
    (paddedSquare_indices_nodup scale width hwidth)
    (fun e he => List.mem_range.mpr (List.idxOf_lt_length_of_mem
      ((paddedSquare scale width hwidth).physical e he)))
  have hw : PolyQuaternionCoeffEqv (wordAt block es) (sourceWord width es) := by
    rw [padded_wordAt_sourceWord scale width hwidth]
    exact PolyQuaternionCoeffEqv.refl _
  have hf : RatPolyCoeffEqv
      (characterPolynomial (wordAt block es).scalar 1)
      (sourceCharacter width es 1) := by
    exact characterPolynomial_coeffEqv hw.scalar 1
  have hlen : 3 * es.length = 12 * side scale := by
    dsimp only [es]
    rw [paddedSquare_edges]
    rw [square_length]
    omega
  rw [hlen] at hgeneric
  exact (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        (productMap_congr (N width) w K (List.range (N width)) hf.symm))).trans
    (hgeneric.trans (SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier (hf.smul (qpow w (12 * side scale))))))

/-- The same exact heat image inside the mixed source moment used by the
single-ended cost expansion.  The supported source `q` is otherwise arbitrary. -/
theorem paddedSquare_fundamental_mixed_moment
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 1 ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    H width (polyMul (polyMul (polyMul q q) f)
      (productMap (N width) w K (List.range (N width)) f)) ≈
      qpow w (12 * side scale) *
        H width (polyMul (polyMul q q) (polyMul f f)) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have hf := sourceCharacter_supported width
    (paddedSquare scale width hwidth).edges 1
  have htest : SupportedQuaternionBlocks (N width) (polyMul (polyMul q q) f) :=
    supported_polyMul (supported_polyMul hq hq) hf
  have himage := paddedSquare_fundamental_fullRange scale width hwidth w K hK
    (polyMul (polyMul q q) f) htest
  have hsmul := quaternionHaar_polyMul_smul_right (N width)
    (qpow w (12 * side scale)) (polyMul (polyMul q q) f) f
  have hassoc := haar_of_coeff (blocks := N width)
    (RatPolyCoeffEqv.mul_assoc (polyMul q q) f f)
  exact Q'.eqv_trans _ _ _ himage
    (Q'.eqv_trans _ _ _ hsmul
      (Q'.mul_eqv_congr_left _ _ _ hassoc))

#print axioms paddedSquare_fringe_independent
#print axioms paddedSquare_fundamental_fullRange
#print axioms paddedSquare_fundamental_mixed_moment

end YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
