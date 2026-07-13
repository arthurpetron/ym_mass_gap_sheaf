/-
`FusedSchurSpacingBridge` turns the genuine two-mode shell coupling into an
explicit Schur-complement erosion and a varying-spacing mass inequality.

For a head mass `h`, positive shell mass `d`, and coupling `g`, eliminating the
shell gives `h - g^2/d`.  If `g^2 <= eps*d`, then the Schur loss is at most
`eps`.  Combined with a Schur-level spacing cross inequality and a contracting
spacing schedule, this implies the physical additive cross law

  h*aOut <= (eps + mOut)*aIn.

The theorem is then instantiated on the exact 3-4-5 rotated endpoint operator,
the consecutive quadratic cutoffs, and the independently defined reciprocal-
cutoff spacings.  The coupling-size and Schur-cross conditions both reduce in
the kernel; no fitted constant or scalar spectrum pin is used.
-/

import YMGap.Continuum.FusedOffDiagonalCompression
import YMGap.Continuum.SpectralMarginBridge

namespace YMGap.Continuum.FusedSchurSpacingBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic constructive Schur-complement bound -/

/-- Shell loss `g^2/d` at positive shell mass `d`. -/
def shellLoss (g d : Q') (hd : (0 : Q') < d) : Q' :=
  Q'.divPos (g * g) d hd

/-- Scalar Schur complement of the shell block in the mass matrix. -/
def schurMass (head d g : Q') (hd : (0 : Q') < d) : Q' :=
  head - shellLoss g d hd

/-- A quadratic coupling-size estimate bounds the exact resolvent loss. -/
theorem shellLoss_le_of_coupling_size
    {g d eps : Q'} (hd : (0 : Q') < d)
    (hsize : g * g <= eps * d) :
    shellLoss g d hd <= eps := by
  unfold shellLoss
  exact Q'.divPos_le_of_le_mul (g * g) d hd hsize

/-- Therefore the head mass is bounded by erosion plus its Schur complement. -/
theorem head_le_erosion_add_schur
    {head d g eps : Q'} (hd : (0 : Q') < d)
    (hsize : g * g <= eps * d) :
    head <= eps + schurMass head d g hd := by
  have hloss : shellLoss g d hd <= eps :=
    shellLoss_le_of_coupling_size hd hsize
  have hneg : -eps <= -(shellLoss g d hd) := Q'.neg_le_neg hloss
  have hsub : head - eps <= schurMass head d g hd := by
    unfold schurMass
    exact Q'.add_le_add_left head _ _ hneg
  have hadd : head <= schurMass head d g hd + eps :=
    le_add_of_sub_le hsub
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.add_comm_eqv _ _))

/-- **Schur-to-spacing cross law.**  If the shell-eliminated mass already obeys
the cross inequality and the spacing contracts, the coupling-size estimate
adds exactly `eps` to the outgoing numerator. -/
theorem spacing_cross_of_schur
    {head d g eps mOut aIn aOut : Q'}
    (hd : (0 : Q') < d) (heps : (0 : Q') <= eps)
    (haOut : (0 : Q') <= aOut) (hcontract : aOut <= aIn)
    (hsize : g * g <= eps * d)
    (hschur : schurMass head d g hd * aOut <= mOut * aIn) :
    head * aOut <= (eps + mOut) * aIn := by
  have hhead : head <= eps + schurMass head d g hd :=
    head_le_erosion_add_schur hd hsize
  have hscale : head * aOut <= (eps + schurMass head d g hd) * aOut :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hhead haOut
  have hepsScale : eps * aOut <= eps * aIn :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcontract heps
  have hsum :
      eps * aOut + schurMass head d g hd * aOut <=
        eps * aIn + mOut * aIn :=
    BulkModeCrux.qadd_le_add hepsScale hschur
  have hleft : (eps + schurMass head d g hd) * aOut ≈
      eps * aOut + schurMass head d g hd * aOut :=
    Q'.add_mul_eqv eps (schurMass head d g hd) aOut
  have hright : eps * aIn + mOut * aIn ≈ (eps + mOut) * aIn :=
    Q'.eqv_symm (Q'.add_mul_eqv eps mOut aIn)
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hright)))

/-! ## 2. Exact endpoint rotated-operator instance -/

def endpointOldLam : Q' := lamPW (1 : Q') (Ncut 0) 1
def endpointNewLam : Q' := lamPW (1 : Q') (Ncut 1) 1

/-- Head coordinate mass of `I - rotatedFusedOp`. -/
def endpointHeadMass : Q' := (1 : Q') - rot00 endpointOldLam endpointNewLam

/-- Shell coordinate mass of `I - rotatedFusedOp`. -/
def endpointShellMass : Q' := (1 : Q') - rot11 endpointOldLam endpointNewLam

/-- Exact off-diagonal coupling.  Its sign is irrelevant to the Schur loss. -/
def endpointCoupling : Q' := rot01 endpointOldLam endpointNewLam

/-- Outgoing physical eigenmass of the new fused shell. -/
def endpointOutgoingMass : Q' := (1 : Q') - endpointNewLam

theorem endpointShellMass_pos : (0 : Q') < endpointShellMass := by decide

/-- The derived Schur erosion is the exact quotient `g^2/d`. -/
def endpointErosion : Q' :=
  shellLoss endpointCoupling endpointShellMass endpointShellMass_pos

def endpointSchurMass : Q' :=
  schurMass endpointHeadMass endpointShellMass endpointCoupling endpointShellMass_pos

/-- Reciprocal-cutoff spacing, independent of the spectral mass. -/
def cutoffSpacing (k : Nat) : Q' := unit (Ncut k) (Ncut_pos k)

theorem cutoffSpacing_pos (k : Nat) : (0 : Q') < cutoffSpacing k :=
  unit_pos (Ncut k) (Ncut_pos k)

/-- The first quadratic-cutoff spacing step contracts. -/
theorem endpoint_spacing_contracts : cutoffSpacing 1 <= cutoffSpacing 0 := by decide

/-- Exact coupling-size discharge: `g^2 = endpointErosion*d`. -/
theorem endpoint_coupling_size :
    endpointCoupling * endpointCoupling <=
      endpointErosion * endpointShellMass := by
  decide

/-- Exact resolvent/Schur spacing inequality at the coupled endpoint step. -/
theorem endpoint_schur_spacing_cross :
    endpointSchurMass * cutoffSpacing 1 <=
      endpointOutgoingMass * cutoffSpacing 0 := by
  decide

/-- **Constructed operator mass/spacing cross law.**  The head coordinate mass
of the genuinely coupled operator, at the contracted reciprocal-cutoff spacing,
is controlled by the new fused eigenmass plus the exactly derived Schur erosion. -/
theorem endpoint_operator_mass_spacing_cross :
    endpointHeadMass * cutoffSpacing 1 <=
      (endpointErosion + endpointOutgoingMass) * cutoffSpacing 0 := by
  exact spacing_cross_of_schur endpointShellMass_pos
    (by decide : (0 : Q') <= endpointErosion)
    (Q'.le_of_lt (cutoffSpacing_pos 1)) endpoint_spacing_contracts
    endpoint_coupling_size endpoint_schur_spacing_cross

/-- Division by the two positive spacings gives the corresponding physical
additive-margin step. -/
theorem endpoint_operator_physical_margin_step :
    Q'.divPos endpointHeadMass (cutoffSpacing 0) (cutoffSpacing_pos 0) -
        Q'.divPos endpointErosion (cutoffSpacing 1) (cutoffSpacing_pos 1) <=
      Q'.divPos endpointOutgoingMass (cutoffSpacing 1) (cutoffSpacing_pos 1) := by
  exact SpectralMarginBridge.hadd_of_hlat_varying
    endpointHeadMass endpointOutgoingMass endpointErosion
    (cutoffSpacing 0) (cutoffSpacing 1)
    (cutoffSpacing_pos 0) (cutoffSpacing_pos 1)
    endpoint_operator_mass_spacing_cross

end YMGap.Continuum.FusedSchurSpacingBridge

#print axioms YMGap.Continuum.FusedSchurSpacingBridge.shellLoss_le_of_coupling_size
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.head_le_erosion_add_schur
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.spacing_cross_of_schur
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.endpointShellMass_pos
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.endpoint_spacing_contracts
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.endpoint_coupling_size
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.endpoint_schur_spacing_cross
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.endpoint_operator_mass_spacing_cross
#print axioms YMGap.Continuum.FusedSchurSpacingBridge.endpoint_operator_physical_margin_step
