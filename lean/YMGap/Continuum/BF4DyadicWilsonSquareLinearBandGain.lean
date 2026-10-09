/-
The connected retained-spectator test gives a linear, rather than squared,
local-band fraction for the COMPLETE original padded Wilson-square energy.
The comparison retains the actual endpoint source, OWN center, exterior,
and all connected cross terms. It is finite at fixed nome and scale; it is
not a changing-family survival or physical mass estimate.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain
import YMGap.Continuum.SU2QuaternionProductHeatBandResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand

namespace YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand (erasedCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatBandResponse
  (square_moment_order shifted_pair_zero)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (SourceLoop sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
  (spectator_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
  (localLower localLower_positive localUpper localUpper_positive
    endpoint_localLowerCertificate)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareSpectator squareSpectator_supported paddedSquare_spectator_zero)
open YMGap.Continuum.BF4DyadicWilsonSquareSignedOverlapGain
  (squareSpectatorOverlap squareSpectatorDualMoment)
open YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualOverlap
  (squareConnectedDualMoment connectedDualMoment_le_unprojected
    paddedSquare_energy_connected_overlap_cleared)
open YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain
  (paddedSquare_original_upper_overlap paddedSquare_connectedDualMoment_positive)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ k : Nat, (0 : Q') < qpow w k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos (qpow_positive hw k) hw

private theorem qpow_rg (w : Q') : ∀ k : Nat, qpow w k = RGTransport.qpow w k
  | 0 => rfl
  | k+1 => congrArg (fun x : Q' => x*w) (qpow_rg w k)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
  (hwidth : side scale < width)

local notation "f" => sourceCharacter width (SourceLoop.edges (paddedSquare scale width hwidth)) 1
local notation "q" => endpointSource w K width (terminalMessage w K width (n+1))
local notation "R" => squareSpectator w K scale width hwidth n
local notation "PR" => productMap (N width) w K (activeBlocks width) R
local notation "W" => polyMul R PR
local notation "mu" => normalizedMoment (N width) (marginalWeight w K width (n+1)) f
  (marginalMass_positive hw0 hw1 K width hK (n+1))
local notation "psi" => oddCentered hw0 hw1 K width hK (n+1) f
local notation "l" => localLower w (4*side scale)
local notation "u" => localUpper w (4*side scale)
local notation "a" => qpow w (12*side scale)
local notation "Z" => oddMass w K width (n+1)
local notation "S" => Z*oddVariance hw0 hw1 K width hK (n+1) f
local notation "U" => squareSpectatorOverlap hw0 hw1 K width hK n scale hwidth
local notation "D" => squareSpectatorDualMoment hw0 hw1 K width hK n scale hwidth
local notation "D0" => squareConnectedDualMoment hw0 hw1 K width hK n scale hwidth
local notation "E" => energy w K width (terminalMessage w K width (n+1)) f
local notation "F" => H width (polyMul W (polyMul psi psi))

/-- The lower local certificate is inserted against the actual heat image of
the retained exterior. The OWN centered square is kept as the insertion. -/
theorem paddedSquare_original_lower_overlap : l*F ≤ U := by
  have hf := sourceCharacter_supported width
    (SourceLoop.edges (paddedSquare scale width hwidth)) 1
  have hR := squareSpectator_supported w K scale width hwidth n
  have CR := spectator_certificate hw0 hw1 K width hK n
    ((SourceLoop.edges (paddedSquare scale width hwidth)).map (fun e => e.link))
  have CPR := erasedCertificate (N width) hw0 hw1 K hK (activeBlocks width)
    (activeBlocks_lt width) hR CR
  have hsize : ((SourceLoop.edges (paddedSquare scale width hwidth)).map
      (fun e => e.link)).length ≤
      4*side scale := by
    exact Nat.le_of_eq (by rw [List.length_map, paddedSquare_edges, square_length])
  have CL : Certificate (N width)
      (polyAdd (polyMul q PR) (polyNeg (polySmul l W))) := by
    have he : RatPolyCoeffEqv
        (polyAdd (polyMul q PR) (polyNeg (polySmul l W)))
        (polyMul (polyAdd q (polyNeg (polySmul l R))) PR) :=
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left l W).symm)).trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 1))
            (.neg (.mul (.var 2) (.mul (.var 3) (.var 1)))))
          (.mul (.add (.var 0) (.neg (.mul (.var 2) (.var 3)))) (.var 1))
          (by decide) (fun | 0 => q | 1 => PR | 2 => cap l | _ => R)).trans
          (((RatPolyCoeffEqv.refl q).add
            (RatPolyCoeffEqv.neg (cap_mul_left l R))).mul_right PR))
    exact .ofCoeff he
      ((endpoint_localLowerCertificate hw0 hw1 K width hK n _ _ hsize).mul CPR)
  have hpsi := oddCentered_supported hw0 hw1 K width hK (n+1) hf
  have hFpin : H width (polyMul (polySmul l W) (polyMul psi psi)) ≈ l*F :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left l W _))
      (quaternionHaar_polySmul (N width) l _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hFpin)
    (square_moment_order CL hpsi)

/-- The unprojected dual diagonal is no larger than the SAME exterior
centered square. The affine correction and all nonzero OWN-mean terms remain. -/
theorem paddedSquare_dual_le_centered_exterior : D ≤ F := by
  have hR := squareSpectator_supported w K scale width hwidth n
  have CR := spectator_certificate hw0 hw1 K width hK n
    ((SourceLoop.edges (paddedSquare scale width hwidth)).map (fun e => e.link))
  have CPR := erasedCertificate (N width) hw0 hw1 K hK (activeBlocks width)
    (activeBlocks_lt width) hR CR
  have hW0 : (0 : Q') ≤ H width W := (CR.mul CPR).haar_nonnegative
  have ha : a ≤ 1 := by
    rw [qpow_rg]
    exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _
  have hc : (a*mu)*mu ≤ mu*mu := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv a mu mu))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (mu*mu) ha
        (SumOfSquares.q_mul_self_nonneg mu))
      (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  have haff : H width (polyMul W (polyMul f f))+
      ((a*mu)*mu)*H width W ≤ F :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ (H width W) hc hW0))
      (Q'.ge_of_eqv (shifted_pair_zero (N width) W f mu mu
        (paddedSquare_spectator_zero scale width hwidth w K n)))
  have hDdef : D = H width (polyMul W (polyMul f f))+
      (a*(mu*mu))*H width W := rfl
  have hrearrange : (a*(mu*mu))*H width W ≈ ((a*mu)*mu)*H width W :=
    Q'.mul_eqv_congr_right _ _ (H width W) (Q'.eqv_symm (Q'.mul_assoc_eqv a mu mu))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) hrearrange)) haff

attribute [local irreducible] productMap normalizedMoment marginalWeight squareSpectator
attribute [local irreducible] oddMass oddVariance squareSpectatorOverlap
attribute [local irreducible] squareSpectatorDualMoment squareConnectedDualMoment

/-- One lower band factor suffices for the computed connected denominator. -/
theorem paddedSquare_connected_dual_linear_overlap : l*D0 ≤ Z*U := by
  have hD0 := connectedDualMoment_le_unprojected hw0 hw1 K width hK n scale hwidth
  have hD := paddedSquare_dual_le_centered_exterior hw0 hw1 K width hK n scale hwidth
  have hF := paddedSquare_original_lower_overlap hw0 hw1 K width hK n scale hwidth
  have hl := Q'.le_of_lt (localLower_positive hw0 hw1 (4*side scale))
  have hZ := Q'.le_of_lt (oddMass_positive hw0 hw1 K width hK (n+1))
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ l hD0 hl
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (l*Z) hD
    (Q'.mul_nonneg _ _ hl hZ)
  have h3 := Q'.mul_le_mul_of_nonneg_left _ _ Z hF hZ
  have he1 : l*(Z*D) ≈ (l*Z)*D := Q'.eqv_symm (Q'.mul_assoc_eqv l Z D)
  have he2 : (l*Z)*F ≈ Z*(l*F) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => l | 1 => Z | _ => F)
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he1)
      (Q'.le_trans' _ _ _ h2
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv he2) h3)))

/-- The positive connected denominator can be cancelled only after its
strict positivity has been produced from original overlap and variance. -/
theorem paddedSquare_energy_linear_overlap (hK1 : 1 ≤ K) : E+a*l*U ≤ S := by
  have hlinear := paddedSquare_connected_dual_linear_overlap
    hw0 hw1 K width hK n scale hwidth
  have hAU : (0 : Q') ≤ a*U :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (qpow_positive hw0 _))
      (Q'.le_of_lt (BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_overlap_positive
        hw0 hw1 K width hK n scale hwidth))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (a*U) hlinear hAU
  have hscaled' : (a*l*U)*D0 ≤ a*Z*(U*U) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => a | 1 => l | 2 => U | _ => D0)))
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 1)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => a | 1 => U | _ => Z))))
  have hclear := paddedSquare_energy_connected_overlap_cleared
    hw0 hw1 K width hK n scale hwidth hK1
  have hsum := Q'.add_le_add_left (E*D0) _ _ hscaled'
  have hfact : (E+a*l*U)*D0 ≤ S*D0 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (.var 4))
      (.add (.mul (.var 0) (.var 4))
        (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.var 4)))
      (by decide) (fun | 0 => E | 1 => a | 2 => l | 3 => U | _ => D0)))
      (Q'.le_trans' _ _ _ hsum hclear)
  have hD0 := paddedSquare_connectedDualMoment_positive
    hw0 hw1 K width hK n scale hwidth hK1
  have hcomm : D0*(E+a*l*U) ≤ D0*S :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hfact (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact Q'.le_of_mul_le_mul_left hcomm hD0

/-- Cleared complete-energy bound with only ONE lower and upper band factor. -/
theorem paddedSquare_energy_linear_band_cleared (hK1 : 1 ≤ K) :
    u*E+(a*l)*S ≤ u*S := by
  have hEU := paddedSquare_energy_linear_overlap
    hw0 hw1 K width hK n scale hwidth hK1
  have hSU := paddedSquare_original_upper_overlap
    hw0 hw1 K width hK n scale hwidth
  have hu := Q'.le_of_lt (localUpper_positive hw0 hw1 (4*side scale))
  have hal : (0 : Q') ≤ a*l :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (qpow_positive hw0 (12*side scale)))
    (Q'.le_of_lt (localLower_positive hw0 hw1 (4*side scale)))
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ u hEU hu
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (a*l) hSU hal
  have he1 : u*(E+a*l*U) ≈ u*E+(a*l)*(u*U) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.mul (.mul (.var 2) (.var 3)) (.var 4))))
      (.add (.mul (.var 0) (.var 1))
        (.mul (.mul (.var 2) (.var 3)) (.mul (.var 0) (.var 4))))
      (by decide) (fun | 0 => u | 1 => E | 2 => a | 3 => l | _ => U)
  have hsum := Q'.add_le_add_left (u*E) _ _ h2
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he1.symm) h1)

/-- Computed fixed-nome, fixed-scale fraction. No global cutoff, width, or
depth enters its definition. -/
def linearBandFraction {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (scale : Nat) : Q' :=
  (qpow w (12*side scale)*localLower w (4*side scale))*
    Q'.recipPos (localUpper w (4*side scale))
      (localUpper_positive hw0 hw1 _)

theorem linearBandFraction_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (scale : Nat) :
    (0 : Q') < linearBandFraction hw0 hw1 scale :=
  Q'.mul_pos
    (Q'.mul_pos (qpow_positive hw0 _)
      (localLower_positive hw0 hw1 _))
    (Q'.recipPos_pos _ _)

/-- Original complete energy, with the explicit linear band factor. -/
theorem paddedSquare_energy_linear_band_raw (hK1 : 1 ≤ K) :
    E ≤ (1-linearBandFraction hw0 hw1 scale)*S := by
  let A := a*l
  let hu := localUpper_positive hw0 hw1 (4*side scale)
  let r := Q'.recipPos u hu
  let delta := A*r
  have hur : r*u ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv r u) (Q'.mul_recipPos_eqv u hu)
  have hclear := paddedSquare_energy_linear_band_cleared
    hw0 hw1 K width hK n scale hwidth hK1
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ r hclear
    (Q'.le_of_lt (Q'.recipPos_pos u hu))
  have hleft : r*(u*E+A*S) ≈ E+delta*S :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 3) (.var 0)) (.var 4)))
      (by decide) (fun | 0 => r | 1 => u | 2 => E | 3 => A | _ => S))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ E hur) (Q'.one_mul_eqv E))
        (Q'.eqv_refl _))
  have hright : r*(u*S) ≈ S := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv r u S))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ S hur) (Q'.one_mul_eqv S))
  have hbudget : E+delta*S ≤ S := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  have he : S + -(E+delta*S) ≈ (1-delta)*S + -E :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.mul (.var 2) (.var 0)))))
      (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0)) (.neg (.var 1)))
      (by decide) (fun | 0 => S | 1 => E | _ => delta)
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hbudget) (Q'.le_of_eqv he))

/-- Same positive original odd partition on both sides. -/
theorem paddedSquare_energy_linear_band (hK1 : 1 ≤ K) :
    normalizedEnergy hw0 hw1 K width hK (n+1) f ≤
      (1-linearBandFraction hw0 hw1 scale)*
        oddVariance hw0 hw1 K width hK (n+1) f := by
  let z := oddMass w K width (n+1)
  let hz := oddMass_positive hw0 hw1 K width hK (n+1)
  let r := Q'.recipPos z hz
  let v := oddVariance hw0 hw1 K width hK (n+1) f
  let c := 1-linearBandFraction hw0 hw1 scale
  have h := Q'.mul_le_mul_of_nonneg_right _ _ r
    (paddedSquare_energy_linear_band_raw hw0 hw1 K width hK n scale hwidth hK1)
    (Q'.le_of_lt (Q'.recipPos_pos z hz))
  have hright : (c*(z*v))*r ≈ c*v :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => c | 1 => z | 2 => v | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (c*v) (Q'.mul_recipPos_eqv z hz))
        (Q'.one_mul_eqv (c*v)))
  unfold normalizedEnergy
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright)

end YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.paddedSquare_original_lower_overlap
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.paddedSquare_dual_le_centered_exterior
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.paddedSquare_connected_dual_linear_overlap
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.paddedSquare_energy_linear_overlap
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.paddedSquare_energy_linear_band_cleared
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.linearBandFraction
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.linearBandFraction_positive
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.paddedSquare_energy_linear_band_raw
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain.paddedSquare_energy_linear_band
