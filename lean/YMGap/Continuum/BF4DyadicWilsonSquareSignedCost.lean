/-
# Signed source cost for a literal dyadic Wilson square

Only the fundamental full-range heat image is evaluated.  The square image is
left as the actual `productMap` term, while the signed cross term acquires the
exact perimeter multiplier.  The terminal theorem inserts this identity into
the existing projected-source Young equality.  These are algebraic identities,
not positivity, variance, interacting-eigenvalue, or scaling statements.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (singleEndedCost sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
  (singleEndedCost_eq_moments)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

/-- The exact one-ended cost after evaluating only its signed fundamental
cross term.  The full square image remains untouched. -/
theorem paddedSquare_singleEndedCost
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 1 ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let P := productMap (N width) w K (List.range (N width))
    singleEndedCost (N width) w K (List.range (N width)) q f ≈
      (1 + -((2 : Q') * qpow w (12 * side scale))) *
          H width (polyMul (polyMul q q) (polyMul f f)) +
        H width (polyMul (polyMul q q) (P (polyMul f f))) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let P := productMap (N width) w K (List.range (N width))
  have hf := sourceCharacter_supported width
    (paddedSquare scale width hwidth).edges 1
  have hm := singleEndedCost_eq_moments (N width) w K (List.range (N width))
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi) hq hf
  have hcross := paddedSquare_fundamental_mixed_moment
    scale width hwidth w K hK q hq
  have hrewrite := Q'.add_eqv_congr' (Q'.eqv_refl
      (H width (polyMul (polyMul q q) (polyMul f f))))
    (Q'.add_eqv_congr' (Q'.eqv_refl
      (H width (polyMul (polyMul q q) (P (polyMul f f)))))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hcross)))
  refine Q'.eqv_trans _ _ _ hm (Q'.eqv_trans _ _ _ hrewrite ?_)
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 1)
      (.neg (.mul (.const 2) (.mul (.var 2) (.var 0))))))
    (.add (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 2)))) (.var 0))
      (.var 1))
    (by decide)
    (fun | 0 => H width (polyMul (polyMul q q) (polyMul f f))
         | 1 => H width (polyMul (polyMul q q) (P (polyMul f f)))
         | _ => qpow w (12 * side scale))

/-- The original terminal source and its full fringe projection satisfy the
same signed identity.  The source-increment correction is retained. -/
theorem paddedSquare_terminal_young_identity
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (n : Nat) :
    let g := terminalMessage w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let q := projectedEndpointSource w K width g
    let P := productMap (N width) w K (List.range (N width))
    (4 : Q') * energy w K width g f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≈
      (2 : Q') *
        ((1 + -((2 : Q') * qpow w (12 * side scale))) *
            H width (polyMul (polyMul q q) (polyMul f f)) +
          H width (polyMul (polyMul q q) (P (polyMul f f)))) := by
  dsimp only
  let g := terminalMessage w K width n
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let q := projectedEndpointSource w K width g
  have hg : SupportedQuaternionBlocks (N width) g :=
    terminalMessage_supported w K width n
  have hf : SupportedQuaternionBlocks (N width) f :=
    sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width) hg)
  have hyoung := projected_young_identity w K width g f hg hf
    (paddedSquare_fringe_independent scale width hwidth)
  exact Q'.eqv_trans _ _ _ hyoung
    (Q'.mul_eqv_congr_left 2 _ _
      (paddedSquare_singleEndedCost scale width hwidth w K hK q hq))

#print axioms paddedSquare_singleEndedCost
#print axioms paddedSquare_terminal_young_identity

end YMGap.Continuum.BF4DyadicWilsonSquareSignedCost
