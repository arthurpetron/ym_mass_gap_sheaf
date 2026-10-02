/-
# Actual retained-spectator overlap gain for the original Wilson square

The source is q=V*u_(n+1); its spectator R retains the full predecessor n
and exterior. U=H[q*(P R)*OWNpsi^2] and the exact dual moment D are computed
on the SAME active heat. Sharp kinetic Cauchy--Schwarz gives
a*U^2 <= (G+a*Z*OWNVar)*D, retaining the actual signed defect G.

No pointwise local band, source independence, variance/source inverse or
assumed overlap estimate enters. Useful changing-family control of these
actual overlaps remains open; this finite gain alone proves no survival.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect
import YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedOverlapGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatBandResponse (dual_image shifted_pair_zero)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment sourceEnergy)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment shifted shifted_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (energy_source_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (centered_unprojected_square energy_shifted)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareSpectator squareSpectator_supported paddedSquare_spectator_kinetic paddedSquare_spectator_zero)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage sourceCharacter energy
attribute [local irreducible] spatialWeight productMap normalizedMoment marginalWeight
attribute [local irreducible] squareSpectator oddMass oddVariance squareSignedHeatDefect

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (qpow_positive hw n) hw

/-- Actual source/exterior overlap at original depth n+1 and OWN center. -/
def squareSpectatorOverlap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let q := endpointSource w K width (terminalMessage w K width (n+1))
  let R := squareSpectator w K scale width hwidth n
  let psi := oddCentered hw0 hw1 K width hK (n+1) f
  H width (polyMul (polyMul q (productMap (N width) w K (activeBlocks width) R))
    (polyMul psi psi))

/-- Exact dual moment, including the affine correction from the OWN mean.
This is not replaced by a mean-zero or bare-source moment. -/
def squareSpectatorDualMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let R := squareSpectator w K scale width hwidth n
  let W := polyMul R (productMap (N width) w K (activeBlocks width) R)
  let mu := normalizedMoment (N width) (marginalWeight w K width (n+1)) f
    (marginalMass_positive hw0 hw1 K width hK (n+1))
  H width (polyMul W (polyMul f f))+
    (qpow w (12*side scale)*(mu*mu))*H width W

/-- The actual original kinetic diagonal equals signed defect plus a*S. -/
theorem paddedSquare_kinetic_signedHeatDefect_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let q := endpointSource w K width (terminalMessage w K width (n+1))
    let psi := oddCentered hw0 hw1 K width hK (n+1) f
    kineticPair (N width) w K (activeBlocks width) (polyMul q psi) (polyMul q psi) ≈
      squareSignedHeatDefect hw0 hw1 K width hK (n+1) scale hwidth+
      qpow w (12*side scale)*(oddMass w K width (n+1)*
        oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let g := terminalMessage w K width (n+1)
  let q := endpointSource w K width g
  let mu := normalizedMoment (N width) (marginalWeight w K width (n+1)) f
    (marginalMass_positive hw0 hw1 K width hK (n+1))
  let psi := shifted f mu
  let S := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
  let B := kineticPair (N width) w K (activeBlocks width) (polyMul q psi) (polyMul q psi)
  let G := squareSignedHeatDefect hw0 hw1 K width hK (n+1) scale hwidth
  let a := qpow w (12*side scale)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hE : energy w K width g f ≈ S-B :=
    Q'.eqv_trans _ _ _ (energy_shifted w K width (terminalMessage_supported w K width (n+1)) hf mu).symm
      (Q'.eqv_trans _ _ _ (energy_source_pin w K width g psi)
        (Q'.add_eqv_congr' (centered_unprojected_square hw0 hw1 K width hK (n+1) hf)
          (Q'.eqv_refl _)))
  have hp : S-B ≈ (1-a)*S-G := Q'.eqv_trans _ _ _ hE.symm
    (paddedSquare_energy_signedHeatDefect_identity hw0 hw1 K width hK (n+1) scale hwidth)
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq (.var 0)
    (.add (.var 1) (.neg (.add (.var 1) (.neg (.var 0)))))
    (by decide) (fun | 0 => B | _ => S))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hp))
      (poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)) (.neg (.var 2)))))
        (.add (.var 2) (.mul (.var 1) (.var 0)))
        (by decide) (fun | 0 => S | 1 => a | _ => G)))

attribute [local irreducible] squareSpectatorOverlap squareSpectatorDualMoment

/-- Sharp actual overlap inequality, without coarse l/u replacement or
division by any source, dual moment or interacting variance. -/
theorem paddedSquare_signed_overlap_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let U := squareSpectatorOverlap hw0 hw1 K width hK n scale hwidth
    let D := squareSpectatorDualMoment hw0 hw1 K width hK n scale hwidth
    let S := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
    let G := squareSignedHeatDefect hw0 hw1 K width hK (n+1) scale hwidth
    a*(U*U) ≤ (G+a*S)*D := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let q := endpointSource w K width (terminalMessage w K width (n+1))
  let R := squareSpectator w K scale width hwidth n
  let PR := productMap (N width) w K (activeBlocks width) R
  let W := polyMul R PR
  let a := qpow w (12*side scale)
  let mu := normalizedMoment (N width) (marginalWeight w K width (n+1)) f
    (marginalMass_positive hw0 hw1 K width hK (n+1))
  let psi := shifted f mu
  let tau := shifted f (a*mu)
  let x := polyMul q psi
  let t := polyMul R tau
  let U := squareSpectatorOverlap hw0 hw1 K width hK n scale hwidth
  let D := squareSpectatorDualMoment hw0 hw1 K width hK n scale hwidth
  let S := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
  let G := squareSignedHeatDefect hw0 hw1 K width hK (n+1) scale hwidth
  let B := kineticPair (N width) w K (activeBlocks width) x x
  have hUdef : U = H width (polyMul (polyMul q PR) (polyMul psi psi)) := by
    unfold U squareSpectatorOverlap
    rfl
  have hDdef : D = H width (polyMul W (polyMul f f))+
      (a*(mu*mu))*H width W := by
    unfold D squareSpectatorDualMoment
    rfl
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hq := supported_polyMul (spatialWeight_supported w K width)
    (terminalMessage_supported w K width (n+1))
  have hR := squareSpectator_supported w K scale width hwidth n
  have hx := supported_polyMul hq (shifted_supported hf mu)
  have ht := supported_polyMul hR (shifted_supported hf (a*mu))
  have hi := dual_image (N width) w K (activeBlocks width) R f a mu
    (paddedSquare_spectator_kinetic scale width hwidth w K hK1 n)
  have hC : kineticPair (N width) w K (activeBlocks width) x t ≈ a*U :=
    Q'.eqv_trans _ _ _ (hi x hx)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (N width) a x (polyMul PR psi))
        (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _ (haar_of_coeff
          (blocks := N width) (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 1)))
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
            (by decide) (fun | 0 => q | 1 => psi | _ => PR)))
          (Q'.eqv_of_eq hUdef.symm))))
  have hD : kineticPair (N width) w K (activeBlocks width) t t ≈ a*D := by
    have hp : H width (polyMul W (polyMul tau psi)) ≈ D :=
      Q'.eqv_trans _ _ _ (shifted_pair_zero (N width) W f (a*mu) mu
        (paddedSquare_spectator_zero scale width hwidth w K n))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_right _ _ (H width W)
            (Q'.mul_assoc_eqv a mu mu))) (Q'.eqv_of_eq hDdef.symm))
    exact Q'.eqv_trans _ _ _ (hi t ht)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (N width) a t (polyMul PR psi))
        (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _ (haar_of_coeff
          (blocks := N width) (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
            (by decide) (fun | 0 => R | 1 => tau | 2 => PR | _ => psi))) hp)))
  have hCS := kineticPair_cauchySchwarz (N width) w (Q'.le_of_lt hw0) K
    (activeBlocks width) (activeBlocks_lt width) x t hx ht
  have hscaled : a*(a*(U*U)) ≤ a*(B*D) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
        (by decide) (fun | 0 => a | _ => U))))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hC)
          (Q'.mul_eqv_congr_left (a*U) _ _ hC)))
        (Q'.le_trans' _ _ _ hCS (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left B _ _ hD)
          (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.mul (.var 0) (.var 2)))
            (by decide) (fun | 0 => B | 1 => a | _ => D))))))
  have hbound : a*(U*U) ≤ B*D :=
    Q'.le_of_mul_le_mul_left hscaled (qpow_positive hw0 _)
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
    (Q'.mul_eqv_congr_right _ _ D
      (paddedSquare_kinetic_signedHeatDefect_pin hw0 hw1 K width hK n scale hwidth)))

/-- Explicit lower estimate for the computed SIGNED defect times its dual
moment. All original source and mean terms remain in U,D,S,G. -/
theorem paddedSquare_signed_overlap_gain {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let U := squareSpectatorOverlap hw0 hw1 K width hK n scale hwidth
    let D := squareSpectatorDualMoment hw0 hw1 K width hK n scale hwidth
    let S := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
    let G := squareSignedHeatDefect hw0 hw1 K width hK (n+1) scale hwidth
    a*(U*U-S*D) ≤ G*D := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let a := qpow w (12*side scale)
  let U := squareSpectatorOverlap hw0 hw1 K width hK n scale hwidth
  let D := squareSpectatorDualMoment hw0 hw1 K width hK n scale hwidth
  let S := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
  let G := squareSignedHeatDefect hw0 hw1 K width hK (n+1) scale hwidth
  have h := Q'.sub_nonneg_of_le
    (paddedSquare_signed_overlap_cleared hw0 hw1 K width hK hK1 n scale hwidth)
  have he : (G+a*S)*D-a*(U*U) ≈ G*D-a*(U*U-S*D) :=
    poly_identity_of_normal_eq
      (.add (.mul (.add (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
        (.neg (.mul (.var 1) (.mul (.var 4) (.var 4)))))
      (.add (.mul (.var 0) (.var 3))
        (.neg (.mul (.var 1) (.add (.mul (.var 4) (.var 4))
          (.neg (.mul (.var 2) (.var 3)))))))
      (by decide) (fun | 0 => G | 1 => a | 2 => S | 3 => D | _ => U)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))

#print axioms squareSpectatorOverlap
#print axioms squareSpectatorDualMoment
#print axioms paddedSquare_kinetic_signedHeatDefect_pin
#print axioms paddedSquare_signed_overlap_cleared
#print axioms paddedSquare_signed_overlap_gain

end YMGap.Continuum.BF4DyadicWilsonSquareSignedOverlapGain
