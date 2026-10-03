/-
# Connected dual overlap for the ORIGINAL Wilson square

Project the retained-spectator dual off the actual source q in the SAME
kinetic form. OWN centering makes the mixed numerator unchanged. The dual
denominator loses an explicit nonnegative mean-mismatch square, with only
the original positive odd partition used for cancellation. No norm inverse,
stationary ground pin, useful scaling estimate or survival is asserted.
-/

import YMGap.Continuum.GNSOrthogonalDualProjection
import YMGap.Continuum.BF4DyadicWilsonSquareSignedOverlapGain
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualOverlap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatBandResponse (dual_image shifted_pair_zero)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment shifted shifted_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive marginalMass_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (oddMoment_unprojected_source)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect
open YMGap.Continuum.BF4DyadicWilsonSquareSignedOverlapGain
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareSpectator squareSpectator_supported paddedSquare_spectator_kinetic
    paddedSquare_spectator_zero)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage spatialWeight sourceCharacter energy

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (qpow_positive hw n) hw

/-- The actual source norm is the ORIGINAL positive odd partition, with
the SAME chronological depth and no fringe projection. -/
theorem original_kinetic_mass_pin (w : Q') (K width depth : Nat) :
    let q := endpointSource w K width (terminalMessage w K width depth)
    kineticPair (N width) w K (activeBlocks width) q q ≈ oddMass w K width depth := by
  dsimp only
  let q := endpointSource w K width (terminalMessage w K width depth)
  have hs : sourceMoment (N width) w K (activeBlocks width) q polyOne ≈
      kineticPair (N width) w K (activeBlocks width) q q :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_one q).mul_right
      (productMap (N width) w K (activeBlocks width) q))
  exact Q'.eqv_trans _ _ _ hs.symm
    (Q'.eqv_trans _ _ _ (oddMoment_unprojected_source w K width depth polyOne).symm
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _))
        (marginalMass_pin w K width depth)))

/-- A SIGNED mean mismatch against the retained exterior, with the original
OWN center. It is computed, not assumed to vanish. -/
def squareSpectatorMeanMismatch {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let q := endpointSource w K width (terminalMessage w K width (n+1))
  let R := squareSpectator w K scale width hwidth n
  let psi := oddCentered hw0 hw1 K width hK (n+1) f
  H width (polyMul (polyMul q (productMap (N width) w K (activeBlocks width) R)) psi)

/-- The projected dual denominator; no reciprocal of this quantity is formed. -/
def squareConnectedDualMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) : Q' :=
  oddMass w K width (n+1)*squareSpectatorDualMoment hw0 hw1 K width hK n scale hwidth -
    qpow w (12*side scale)*
      (squareSpectatorMeanMismatch hw0 hw1 K width hK n scale hwidth *
        squareSpectatorMeanMismatch hw0 hw1 K width hK n scale hwidth)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
  (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "q" => endpointSource w K width (terminalMessage w K width (n+1))
local notation "R" => squareSpectator w K scale width hwidth n
local notation "PR" => productMap (N width) w K (activeBlocks width) R
local notation "mu" => normalizedMoment (N width) (marginalWeight w K width (n+1)) f
  (marginalMass_positive hw0 hw1 K width hK (n+1))
local notation "psi" => oddCentered hw0 hw1 K width hK (n+1) f
local notation "a" => qpow w (12*side scale)
local notation "t" => polyMul R (shifted f (a*mu))
local notation "x" => polyMul q psi
local notation "B" => kineticPair (N width) w K (activeBlocks width)
local notation "Z" => oddMass w K width (n+1)
local notation "U" => squareSpectatorOverlap hw0 hw1 K width hK n scale hwidth
local notation "D" => squareSpectatorDualMoment hw0 hw1 K width hK n scale hwidth
local notation "m" => squareSpectatorMeanMismatch hw0 hw1 K width hK n scale hwidth
local notation "D0" => squareConnectedDualMoment hw0 hw1 K width hK n scale hwidth
local notation "S" => Z*oddVariance hw0 hw1 K width hK (n+1) f
local notation "G" => squareSignedHeatDefect hw0 hw1 K width hK (n+1) scale hwidth

private theorem q_supported : SupportedQuaternionBlocks (N width) q :=
  supported_polyMul (spatialWeight_supported w K width)
    (terminalMessage_supported w K width (n+1))

private theorem x_supported : SupportedQuaternionBlocks (N width) x :=
  supported_polyMul (q_supported K width n)
    (oddCentered_supported hw0 hw1 K width hK (n+1)
      (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1))

private theorem t_supported : SupportedQuaternionBlocks (N width) t :=
  supported_polyMul (squareSpectator_supported w K scale width hwidth n)
    (shifted_supported
      (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1) (a*mu))

/-- OWN centering is exactly orthogonality to q in this original kinetic form. -/
theorem paddedSquare_centered_kinetic_source_zero : B x q ≈ 0 :=
  paddedSquare_centered_source_firstMoment_zero hw0 hw1 K width hK (n+1) scale hwidth

private theorem dual_kinetic_pins (hK1 : 1 ≤ K) :
    (B x t ≈ a*U) ∧ (B q t ≈ a*m) ∧ (B t t ≈ a*D) := by
  let tau := shifted f (a*mu)
  let W := polyMul R PR
  have hx := x_supported hw0 hw1 K width hK n scale hwidth
  have hq := q_supported (w := w) K width n
  have ht := t_supported hw0 hw1 K width hK n scale hwidth
  have hi := dual_image (N width) w K (activeBlocks width) R f a mu
    (paddedSquare_spectator_kinetic scale width hwidth w K hK1 n)
  have hUdef : U = H width (polyMul (polyMul q PR) (polyMul psi psi)) := rfl
  have hmdef : m = H width (polyMul (polyMul q PR) psi) := rfl
  have hDdef : D = H width (polyMul W (polyMul f f))+
      (a*(mu*mu))*H width W := rfl
  constructor
  · exact Q'.eqv_trans _ _ _ (hi x hx)
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_smul_right (N width) a x (polyMul PR psi))
        (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _
          (haar_of_coeff (blocks := N width) (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 1)))
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
            (by decide) (fun | 0 => q | 1 => psi | _ => PR)))
          (Q'.eqv_of_eq hUdef.symm))))
  constructor
  · exact Q'.eqv_trans _ _ _ (hi q hq)
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_smul_right (N width) a q (polyMul PR psi))
        (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_assoc q PR psi).symm)
          (Q'.eqv_of_eq hmdef.symm))))
  · have hp : H width (polyMul W (polyMul tau psi)) ≈ D :=
      Q'.eqv_trans _ _ _ (shifted_pair_zero (N width) W f (a*mu) mu
        (paddedSquare_spectator_zero scale width hwidth w K n))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_right _ _ (H width W) (Q'.mul_assoc_eqv a mu mu)))
          (Q'.eqv_of_eq hDdef.symm))
    exact Q'.eqv_trans _ _ _ (hi t ht)
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_smul_right (N width) a t (polyMul PR psi))
        (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _
          (haar_of_coeff (blocks := N width) (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
            (by decide) (fun | 0 => R | 1 => tau | 2 => PR | _ => psi))) hp)))

attribute [local irreducible] productMap normalizedMoment marginalWeight squareSpectator
attribute [local irreducible] oddMass oddVariance squareSignedHeatDefect
attribute [local irreducible] squareSpectatorOverlap squareSpectatorDualMoment
attribute [local irreducible] squareSpectatorMeanMismatch squareConnectedDualMoment

private theorem connected_schur_pin (hK1 : 1 ≤ K) :
    B q q * B t t - B q t * B q t ≈ a*D0 := by
  have hp := dual_kinetic_pins hw0 hw1 K width hK n scale hwidth hK1
  have hz := original_kinetic_mass_pin w K width (n+1)
  have hs : B q q * B t t - B q t * B q t ≈ Z*(a*D)-(a*m)*(a*m) :=
    Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz)
        (Q'.mul_eqv_congr_left _ _ _ hp.2.2))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hp.2.1)
        (Q'.mul_eqv_congr_left _ _ _ hp.2.1)))
  unfold squareConnectedDualMoment
  exact Q'.eqv_trans _ _ _ hs
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3)))))
      (.mul (.var 1) (.add (.mul (.var 0) (.var 2))
        (.neg (.mul (.var 1) (.mul (.var 3) (.var 3))))))
      (by decide) (fun | 0 => Z | 1 => a | 2 => D | _ => m))

/-- The computed projected dual denominator is nonnegative; it may be zero. -/
theorem paddedSquare_connectedDualMoment_nonnegative (hK1 : 1 ≤ K) :
    (0 : Q') ≤ D0 := by
  let F := kineticGNSData (N width) w (Q'.le_of_lt hw0) K (activeBlocks width)
    (activeBlocks_lt width)
  let qv : F.V := ⟨q, q_supported (w := w) K width n⟩
  let tv : F.V := ⟨t, t_supported hw0 hw1 K width hK n scale hwidth⟩
  have h := GNSOrthogonalDualProjection.schur_nonnegative F qv tv
  have h0 : (0 : Q') ≤ a*D0 := Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (connected_schur_pin hw0 hw1 K width hK n scale hwidth hK1))
  exact Q'.nonneg_of_mul_pos (qpow_positive hw0 _) h0

/-- The ORIGINAL connected test removes a computed square from the dual
denominator, without inverting a variance or dropping the OWN mean. -/
theorem paddedSquare_connected_overlap_cleared (hK1 : 1 ≤ K) :
    a*Z*(U*U) ≤ (G+a*S)*D0 := by
  let F := kineticGNSData (N width) w (Q'.le_of_lt hw0) K (activeBlocks width)
    (activeBlocks_lt width)
  let qv : F.V := ⟨q, q_supported (w := w) K width n⟩
  let xv : F.V := ⟨x, x_supported hw0 hw1 K width hK n scale hwidth⟩
  let tv : F.V := ⟨t, t_supported hw0 hw1 K width hK n scale hwidth⟩
  have hz := original_kinetic_mass_pin w K width (n+1)
  have hZ : (0 : Q') < F.B qv qv :=
    Q'.pos_of_lt_of_le (oddMass_positive hw0 hw1 K width hK (n+1))
      (Q'.ge_of_eqv hz)
  have hp := dual_kinetic_pins hw0 hw1 K width hK n scale hwidth hK1
  have h := GNSOrthogonalDualProjection.cleared_bound F xv qv tv
    (paddedSquare_centered_kinetic_source_zero hw0 hw1 K width hK n scale hwidth) hZ
  have hl : B q q*(B x t*B x t) ≈ a*(a*Z*(U*U)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz)
        (Q'.mul_eqv_congr_left Z _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hp.1)
          (Q'.mul_eqv_congr_left _ _ _ hp.1))))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.var 1) (.mul (.mul (.var 1) (.var 0)) (.mul (.var 2) (.var 2))))
        (by decide) (fun | 0 => Z | 1 => a | _ => U))
  have hr : B x x*(B q q*B t t-B q t*B q t) ≈ a*((G+a*S)*D0) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (paddedSquare_kinetic_signedHeatDefect_pin hw0 hw1 K width hK n scale hwidth))
        (Q'.mul_eqv_congr_left _ _ _
          (connected_schur_pin hw0 hw1 K width hK n scale hwidth hK1)))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => G+a*S | 1 => a | _ => D0))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))) (qpow_positive hw0 _)

/-- This is a genuinely no-larger denominator than the previous unprojected
test, for ALL original parameters. The mismatch is not declared zero. -/
theorem connectedDualMoment_le_unprojected : D0 ≤ Z*D := by
  have hn : (0 : Q') ≤ a*(m*m) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (qpow_positive hw0 _))
      (SumOfSquares.q_mul_self_nonneg m)
  have he : Z*D-D0 ≈ a*(m*m) := by
    unfold squareConnectedDualMoment
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1)))))
      (.var 1) (by decide) (fun | 0 => Z*D | _ => a*(m*m))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hn (Q'.ge_of_eqv he))

/-- COMPLETE original energy and OWN variance consume the sharper overlap.
No positivity of D0 is assumed and no dual moment is inverted. -/
theorem paddedSquare_energy_connected_overlap_cleared (hK1 : 1 ≤ K) :
    energy w K width (terminalMessage w K width (n+1)) f * D0 + a*Z*(U*U) ≤ S*D0 := by
  have h := Q'.add_le_add_left
    (energy w K width (terminalMessage w K width (n+1)) f * D0) _ _
    (paddedSquare_connected_overlap_cleared hw0 hw1 K width hK n scale hwidth hK1)
  have he := paddedSquare_energy_signedHeatDefect_identity hw0 hw1 K width hK
    (n+1) scale hwidth
  have hp : energy w K width (terminalMessage w K width (n+1)) f * D0 +
      (G+a*S)*D0 ≈ S*D0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ D0 he) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.mul (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
            (.neg (.var 2))) (.var 3))
          (.mul (.add (.var 2) (.mul (.var 0) (.var 1))) (.var 3)))
        (.mul (.var 1) (.var 3))
        (by decide) (fun | 0 => a | 1 => S | 2 => G | _ => D0))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hp)

#print axioms original_kinetic_mass_pin
#print axioms squareSpectatorMeanMismatch
#print axioms squareConnectedDualMoment
#print axioms paddedSquare_centered_kinetic_source_zero
#print axioms paddedSquare_connectedDualMoment_nonnegative
#print axioms paddedSquare_connected_overlap_cleared
#print axioms connectedDualMoment_le_unprojected
#print axioms paddedSquare_energy_connected_overlap_cleared

end YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualOverlap
