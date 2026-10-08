/-
# Necessary ORIGINAL signed cancellation at cofinal AF square scales

The literal AF schedule has a computed cofinal probe at which the bare
square transmission a=w^(12*side) is smaller than any positive rational eta.
The existing SAME-action identity E=(1-a)*S-D, with S=Z*OWN variance,
then makes a useful INITIAL energy fraction E<=c*S require

  (1-eta-c)*S <= D.

S is proved nonnegative from the actual original marginal certificate; it
is never inverted. For S>0, this rules out simultaneously paying that
initial fraction and treating D as a small perturbative credit when
eta+c+delta<1. It does not produce either bound, refute the interacting
theory, or replace a filtered variance by this unfiltered source square.
The probes are cofinal, not an eventual all-index modulus. The AF schedule
has no proved physical-spacing calibration here.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory

namespace YMGap.Continuum.BF4DyadicWilsonSquareAFSignedCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (oddMoment_unprojected_source centered_unprojected_square)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage sourceCharacter energy
  oddMass oddVariance squareSignedHeatDefect

private theorem original_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    (0 : Q') ≤ oddMass w K width depth *
      oddVariance hw0 hw1 K width hK depth
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let psi := oddCentered hw0 hw1 K width hK depth f
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hp := oddCentered_supported hw0 hw1 K width hK depth hf
  have hpos := ((marginalCertificate hw0 hw1 K width hK depth).mul
    (Certificate.square psi hp)).haar_nonnegative
  have hpin := Q'.eqv_trans _ _ _
    (oddMoment_unprojected_source w K width depth (polyMul psi psi))
    (centered_unprojected_square hw0 hw1 K width hK depth hf)
  exact Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv hpin)

private theorem signed_credit_required {E S D a eta c : Q'}
    (hS : (0 : Q') ≤ S) (ha : a ≤ eta)
    (hidentity : E ≈ (1-a)*S-D) (henergy : E ≤ c*S) :
    (1-eta-c)*S ≤ D := by
  have he : (1-a)*S-D ≤ c*S :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hidentity) henergy
  have hcredit : (1-a-c)*S ≤ D := Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le he) (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.mul (.var 4) (.var 1))
          (.neg (.add (.mul (.add (.const 1) (.neg (.var 3))) (.var 1))
            (.neg (.var 2)))))
        (.add (.var 2)
          (.neg (.mul (.add (.add (.const 1) (.neg (.var 3)))
            (.neg (.var 4))) (.var 1))))
        (by decide) (fun | 0 => E | 1 => S | 2 => D | 3 => a | _ => c))))
  have hcoefficient : 1-eta-c ≤ 1-a-c :=
    Q'.add_le_add_right _ _ (-c)
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg ha))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ S hcoefficient hS) hcredit

/-- SAME original marginal, source, OWN center, and unnormalized energy.
The reference ceiling is explicit; it is produced on the AF probes below.
No small energy fraction is assumed to have been proved. -/
theorem paddedSquare_signedCredit_necessary {w eta c : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width)
    (hreference : qpow w (12*side scale) ≤ eta)
    (henergy : energy w K width (terminalMessage w K width depth)
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) ≤
      c*(oddMass w K width depth * oddVariance hw0 hw1 K width hK depth
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1))) :
    (1-eta-c)*(oddMass w K width depth * oddVariance hw0 hw1 K width hK depth
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1)) ≤
      squareSignedHeatDefect hw0 hw1 K width hK depth scale hwidth :=
  signed_credit_required (original_square_nonnegative hw0 hw1 K width hK depth scale hwidth)
    hreference (paddedSquare_energy_signedHeatDefect_identity
      hw0 hw1 K width hK depth scale hwidth) henergy

/-- At a computed scale beyond EVERY supplied start, a useful original
initial fraction requires an order-S signed credit when eta+c<1.
Widths, cutoff and depth remain independent parameters with literal guards. -/
theorem af_signedCredit_necessary_at_probe {eta c : Q'}
    (heta : (0 : Q') < eta) (start K width depth : Nat)
    (hK : headCutoff (afNomeSchedule.nome
      (afSquareTransmissionProbeScale eta start)) ≤ K)
    (hwidth : side (afSquareTransmissionProbeScale eta start) < width)
    (henergy : energy (afNomeSchedule.nome (afSquareTransmissionProbeScale eta start))
        K width (terminalMessage
          (afNomeSchedule.nome (afSquareTransmissionProbeScale eta start)) K width depth)
        (sourceCharacter width
          (paddedSquare (afSquareTransmissionProbeScale eta start) width hwidth).edges 1) ≤
      c*(oddMass (afNomeSchedule.nome (afSquareTransmissionProbeScale eta start))
        K width depth * oddVariance
          (afNomeSchedule.nome_pos (afSquareTransmissionProbeScale eta start))
          (afNomeSchedule.nome_lt_one (afSquareTransmissionProbeScale eta start))
          K width hK depth (sourceCharacter width
            (paddedSquare (afSquareTransmissionProbeScale eta start) width hwidth).edges 1))) :
    (1-eta-c)*(oddMass (afNomeSchedule.nome (afSquareTransmissionProbeScale eta start))
      K width depth * oddVariance
        (afNomeSchedule.nome_pos (afSquareTransmissionProbeScale eta start))
        (afNomeSchedule.nome_lt_one (afSquareTransmissionProbeScale eta start))
        K width hK depth (sourceCharacter width
          (paddedSquare (afSquareTransmissionProbeScale eta start) width hwidth).edges 1)) ≤
      squareSignedHeatDefect
        (afNomeSchedule.nome_pos (afSquareTransmissionProbeScale eta start))
        (afNomeSchedule.nome_lt_one (afSquareTransmissionProbeScale eta start))
        K width hK depth (afSquareTransmissionProbeScale eta start) hwidth :=
  paddedSquare_signedCredit_necessary
    (afNomeSchedule.nome_pos (afSquareTransmissionProbeScale eta start))
    (afNomeSchedule.nome_lt_one (afSquareTransmissionProbeScale eta start))
    K width hK depth (afSquareTransmissionProbeScale eta start) hwidth
    (Q'.le_of_lt (afSquareTransmission_lt_at_probe heta start)) henergy

/-- With a nonzero SAME original square, the useful initial fraction and a
small signed-credit cap cannot both hold below the displayed coefficient
threshold. This prunes that perturbative proof shortcut, not Yang--Mills. -/
theorem paddedSquare_smallCredit_incompatible {w eta c delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width)
    (hreference : qpow w (12*side scale) ≤ eta)
    (hvariance : (0 : Q') < oddMass w K width depth *
      oddVariance hw0 hw1 K width hK depth
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1))
    (hbudget : eta+c+delta < (1 : Q'))
    (henergy : energy w K width (terminalMessage w K width depth)
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) ≤
      c*(oddMass w K width depth * oddVariance hw0 hw1 K width hK depth
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1)))
    (hcredit : squareSignedHeatDefect hw0 hw1 K width hK depth scale hwidth ≤
      delta*(oddMass w K width depth * oddVariance hw0 hw1 K width hK depth
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1))) : False := by
  have hneed := paddedSquare_signedCredit_necessary hw0 hw1 K width hK depth scale
    hwidth hreference henergy
  let S := oddMass w K width depth * oddVariance hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  have hboth : (1-eta-c)*S ≤ delta*S := Q'.le_trans' _ _ _ hneed hcredit
  have hleft : S*(1-eta-c) ≤ S*delta := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv S (1-eta-c)))
    (Q'.le_trans' _ _ _ hboth (Q'.le_of_eqv (Q'.mul_comm_eqv delta S)))
  have hcoeff : 1-eta-c ≤ delta :=
    Q'.le_of_mul_le_mul_left hleft hvariance
  have hone : (1 : Q') ≤ eta+c+delta := Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hcoeff) (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.var 2)
          (.neg (.add (.add (.const 1) (.neg (.var 0))) (.neg (.var 1)))))
        (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.const 1)))
        (by decide) (fun | 0 => eta | 1 => c | _ => delta))))
  exact ClusteringImpliesGap.lt_irrefl' 1 (Q'.lt_of_le_of_lt hone hbudget)

end YMGap.Continuum.BF4DyadicWilsonSquareAFSignedCancellation

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareAFSignedCancellation.paddedSquare_signedCredit_necessary
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareAFSignedCancellation.af_signedCredit_necessary_at_probe
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareAFSignedCancellation.paddedSquare_smallCredit_incompatible
