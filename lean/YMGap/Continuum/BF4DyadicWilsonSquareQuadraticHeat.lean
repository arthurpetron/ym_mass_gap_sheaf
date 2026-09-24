/-
# Quadratic full-range heat image of a literal dyadic Wilson square

The generic distinct-word label-two transmission is specialized to the actual
fixed-spatial source word.  The fundamental square therefore has its vacuum
channel plus the exact `w^(32 * side)` label-two channel.  A tested moment
form keeps the complete supported source and uses no pointwise replacement.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
import YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo
import YMGap.Continuum.BF4DyadicWilsonSquareSignedCost

namespace YMGap.Continuum.BF4DyadicWilsonSquareQuadraticHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4DyadicWilsonSquareSignedCost
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
  (first_character_square)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup

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

/-- Exact square image of the literal padded dyadic Wilson character. -/
theorem paddedSquare_square_fullRange
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 2 ≤ K) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let c := sourceCharacter width (paddedSquare scale width hwidth).edges 2
    SupportedHaarEqv (N width)
      (productMap (N width) w K (List.range (N width)) (polyMul f f))
      (polyAdd polyOne (polySmul (qpow w (32 * side scale)) c)) := by
  dsimp only
  let es := (paddedSquare scale width hwidth).edges
  let block : OrientedBF4Link → Nat := fun e => (baseLinks width).idxOf e.link
  have hgeneric := productMap_fundamental_square (N width) w K hK block es
    (List.range (N width)) (CayleyParentInj.range_nodup (N width))
    (fun i hi => List.mem_range.mp hi)
    (paddedSquare_indices_nodup scale width hwidth)
    (fun e he => List.mem_range.mpr (List.idxOf_lt_length_of_mem
      ((paddedSquare scale width hwidth).physical e he)))
  have hw : PolyQuaternionCoeffEqv (wordAt block es) (sourceWord width es) := by
    rw [padded_wordAt_sourceWord scale width hwidth]
    exact PolyQuaternionCoeffEqv.refl _
  have hf := characterPolynomial_coeffEqv hw.scalar 1
  have hc := characterPolynomial_coeffEqv hw.scalar 2
  have hlen : 8 * es.length = 32 * side scale := by
    dsimp only [es]
    rw [paddedSquare_edges, square_length]
    omega
  rw [hlen] at hgeneric
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (productMap_congr (N width) w K (List.range (N width))
        (hf.symm.mul hf.symm)))).trans
    (hgeneric.trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.refl polyOne).add
        (hc.smul (qpow w (32 * side scale)))))))

/-- Tested square image with the complete arbitrary supported source retained.
The right side is a convex-looking algebraic split only; no sign premise on
`w` is used. -/
theorem paddedSquare_square_moment
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 2 ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let P := productMap (N width) w K (List.range (N width))
    let M := H width (polyMul (polyMul q q) (polyMul f f))
    let N0 := H width (polyMul q q)
    H width (polyMul (polyMul q q) (P (polyMul f f))) ≈
      qpow w (32 * side scale) * M +
        (1 + -(qpow w (32 * side scale))) * N0 := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let c := sourceCharacter width (paddedSquare scale width hwidth).edges 2
  let b := qpow w (32 * side scale)
  let q2 := polyMul q q
  have hq2 := supported_polyMul hq hq
  have himage := paddedSquare_square_fullRange scale width hwidth w K hK q2 hq2
  have hout := Q'.eqv_trans _ _ _ himage
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right (N width) q2 polyOne (polySmul b c))
      (Q'.add_eqv_congr'
        (haar_of_coeff (blocks := N width) (RatPolyCoeffEqv.mul_one q2))
        (quaternionHaar_polyMul_smul_right (N width) b q2 c)))
  have hsq : RatPolyCoeffEqv (polyMul f f) (polyAdd polyOne c) := by
    exact first_character_square (sourceWord width
      (paddedSquare scale width hwidth).edges).scalar
  have hM := Q'.eqv_trans _ _ _
    (haar_of_coeff (blocks := N width) (hsq.mul_left q2))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (N width) q2 polyOne c)
      (Q'.add_eqv_congr_right _ _ _
        (haar_of_coeff (blocks := N width) (RatPolyCoeffEqv.mul_one q2))))
  refine Q'.eqv_trans _ _ _ hout ?_
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.var 2) (.var 1)))
      (.add (.mul (.var 2) (.add (.var 0) (.var 1)))
        (.mul (.add (.const 1) (.neg (.var 2))) (.var 0)))
      (by decide)
      (fun | 0 => H width q2 | 1 => H width (polyMul q2 c) | _ => b))
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left b _ _ (Q'.eqv_symm hM)))

private theorem collect_moments (a b M N0 S : Q')
    (hS : S ≈ b*M+(1 + -b)*N0) :
    (1 + -((2 : Q')*a))*M+S ≈
      (1 + -((2 : Q')*a)+b)*M+(1 + -b)*N0 := by
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hS) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (.var 2))
      (.add (.mul (.var 1) (.var 2))
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 3))))
    (.add (.mul (.add (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (.var 1)) (.var 2))
      (.mul (.add (.const 1) (.neg (.var 1))) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => M | _ => N0)

/-- The complete original terminal energy identity with BOTH kinetic images
evaluated. The signed coefficient and source-increment correction remain;
neither source normalization nor a scaling variance bound is assumed. -/
theorem paddedSquare_terminal_quadratic_identity
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (n : Nat) :
    let g := terminalMessage w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let q := projectedEndpointSource w K width g
    let a := qpow w (12 * side scale)
    let b := qpow w (32 * side scale)
    (4 : Q') * energy w K width g f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≈
      (2 : Q') *
        ((1 + -((2 : Q') * a) + b) * H width (polyMul (polyMul q q) (polyMul f f)) +
          (1 + -b) * H width (polyMul q q)) := by
  dsimp only
  let g := terminalMessage w K width n
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let q := projectedEndpointSource w K width g
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width n))
  have hy := paddedSquare_terminal_young_identity scale width hwidth w K (by omega) n
  have hs := paddedSquare_square_moment scale width hwidth w K hK q hq
  exact Q'.eqv_trans _ _ _ hy (Q'.mul_eqv_congr_left 2 _ _
    (collect_moments (qpow w (12 * side scale)) (qpow w (32 * side scale)) _ _ _ hs))

#print axioms paddedSquare_square_fullRange
#print axioms paddedSquare_square_moment
#print axioms paddedSquare_terminal_quadratic_identity

end YMGap.Continuum.BF4DyadicWilsonSquareQuadraticHeat
