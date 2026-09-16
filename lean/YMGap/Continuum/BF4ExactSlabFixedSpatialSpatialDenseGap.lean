/-
# Strict dense reflected form bound after spatial exhaustion

The actual two-probe selected-action bound has a temporal rate depending
only on the nome. It passes through the same original connected diagonal
to the spatial centered moment. An explicit positive prefactor absorbs
the fixed support-size loss, including its truncated initial segment.
The actual even-moment inequalities then remove this prefactor entirely.

The resulting two-step form rate is common to all positive base sizes and
physical signed presentations, under the displayed small-nome guards.
This is a dense reflected form inequality, not yet a theorem about every
completed vector or a physical continuum Hamiltonian. The nome dependence
and fixed lattice spacing have not been removed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay
import YMGap.Continuum.RationalShiftedGeometric
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
  (face_joint_variance_floor recenter_faceSpan)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime physicalTime_zero unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift (radius_advance_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound (pairedHeatRate)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (dyadic_geometric_first_le)

/-- The actual connected-core temporal rate, with no volume or support argument. -/
def timeRate (w : Q') (hd : heatRemainderBound w < 1) : Q' :=
  entropyRate 625 (adjustedCoreRate w hd)

theorem timeRate_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) : (0 : Q') < timeRate w hd := by
  have hdelta : (0 : Q') < heatRemainderBound w :=
    Q'.pos_of_lt_of_le
      (Q'.mul_pos (by decide : (0 : Q') < 128) (BondMovingScaledNorm.qpow_pos hw0 3))
      (Q'.ge_of_eqv (heatRemainderBound_eq w))
  have hpaired : (0 : Q') < pairedHeatRate w :=
    TuranPositivity.q_pos_add_nonneg
      (TuranPositivity.q_pos_add_nonneg hdelta (Q'.le_of_lt hdelta))
      (Q'.le_of_lt (Q'.mul_pos hdelta hdelta))
  exact Q'.mul_pos (by decide : (0 : Q') < 625)
    (Q'.mul_pos hpaired (ClusteringImpliesGap.pow_pos (inverseFaceFloor_pos w hd) 48))

/-- Two physical lattice steps; this is not a calibrated continuum mass. -/
def twoStepRate (w : Q') (hd : heatRemainderBound w < 1) : Q' :=
  timeRate w hd * timeRate w hd

theorem twoStepRate_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) : (0 : Q') < twoStepRate w hd :=
  Q'.mul_pos (timeRate_positive hw0 hd) (timeRate_positive hw0 hd)

theorem twoStepRate_lt_one {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    twoStepRate w hd < (1 : Q') :=
  Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hs)
        (Q'.le_of_lt (timeRate_positive hw0 hd))) (Q'.le_of_eqv (Q'.one_mul_eqv _))) hs

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

private theorem radius_time_le (R n : Nat) (y : PhysicalSpan base)
    (hy : radius y.val ≤ R) : radius (physicalTime n y).val ≤ R+n :=
  Nat.le_trans (radius_advance_le n y.val) (Nat.add_le_add_right hy n)

/-- Original connected moments, not an unrelated full-slab covariance,
pass to the spatial limit with the same temporal coefficient. -/
theorem spatialCenteredMoment_bound (R n : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) :
    leEv (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y)
      (ofQ' (decayAmplitude w hd hs base R x y * timeRate w hd^(R+n+1-sizeLoss base R))) :=
  leEv_of_convergesTo_le
    (originalConnected_diagonal_converges hw0 hw1 base hsmall hd hs hb n (R+n) x y
      (Nat.le_trans hx (Nat.le_add_right _ _)) (radius_time_le base R n y hy))
    (convergesTo_const _)
    (fun r => leEv_ofQ'_of_approx_ge (fun _ => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (connectedScalar_uniform_bound hw0 hw1 hsmall hd hs base r R n r r x y hx hy)))

/-- A computed positive coefficient, independent of physical lag and regulators. -/
def positivePrefactor (R : Nat) (x y : PhysicalSpan base) : Q' :=
  RationalShiftedGeometric.amplitude (timeRate w hd) (decayAmplitude w hd hs base R x y)
    (timeRate_positive hw0 hd) (sizeLoss base R)

theorem positivePrefactor_pos (R : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) :
    (0 : Q') < positivePrefactor hw0 base hd hs R x y :=
  RationalShiftedGeometric.amplitude_pos _ _ (timeRate_positive hw0 hd)
    (decayAmplitude_nonnegative w hd hs base R x y hx hy) _

theorem spatialCenteredMoment_le_geometric (R n : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) :
    leEv (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y)
      (ofQ' (positivePrefactor hw0 base hd hs R x y * timeRate w hd^n)) := by
  have h := RationalShiftedGeometric.shifted_bound (timeRate_positive hw0 hd) hs
    (decayAmplitude_nonnegative w hd hs base R x y hx hy) (sizeLoss base R) R n
  have hindex : n+R = R+n := Nat.add_comm _ _
  rw [hindex] at h
  exact leEv_trans (spatialCenteredMoment_bound hw0 hw1 base hsmall hd hs hb R n x y hx hy)
    (leEv_ofQ'_of_approx_ge (fun _ => h))

theorem spatialEvenMoment_le_geometric (x : PhysicalSpan base) (k : Nat) :
    leEv (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x k)
      (ofQ' (positivePrefactor hw0 base hd hs (radius x.val) x x * twoStepRate w hd^k)) :=
  leEv_trans
    (spatialCenteredMoment_le_geometric hw0 hw1 base hsmall hd hs hb (radius x.val) (2*k) x x
      (Nat.le_refl _) (Nat.le_refl _))
    (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_eqv_congr_left _ _ _ (RationalShiftedGeometric.even_power (timeRate w hd) k))))

/-- Prefactor-free, SAME spatial centered form; no positive norm is assumed. -/
theorem spatialEvenMoment_first_le (x : PhysicalSpan base) :
    leEv (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x 1)
      (mul (ofQ' (twoStepRate w hd)) (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x 0)) :=
  dyadic_geometric_first_le (spatialEvenMoment hw0 hw1 base hsmall hd hs hb x)
    (twoStepRate w hd) (positivePrefactor hw0 base hd hs (radius x.val) x x)
    (twoStepRate_positive hw0 hd)
    (positivePrefactor_pos hw0 base hd hs (radius x.val) x x (Nat.le_refl _) (Nat.le_refl _))
    (spatialEvenMoment_nonnegative hw0 hw1 base hsmall hd hs hb x)
    (spatialEvenMoment_le_zero hw0 hw1 base hsmall hd hs hb x)
    (spatialEvenMoment_dyadic hw0 hw1 base hsmall hd hs hb x)
    (spatialEvenMoment_le_geometric hw0 hw1 base hsmall hd hs hb x)

local notation "B" => spatialPairing hw0 hw1 base hsmall hd hs hb

private theorem centered_of_orthogonal (n : Nat) (x : PhysicalSpan base)
    (hx : Equiv (B x (unit base)) czero) :
    Equiv (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x x) (B x (physicalTime n x)) := by
  have hz : Equiv (mul (B x (unit base)) (B (unit base) x)) czero :=
    (CReal.mul_congr_left hx).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.zero_mul_eqv _))
  exact (Equiv_add (Equiv.refl _) (neg_congr hz)).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_of_eq (Q'.add_zero' _)))

/-- One common nome-dependent strict rate for every positive base and every
dense physical presentation orthogonal to the actual normalized unit. -/
theorem dense_vacuumComplement_twoStep_bound (x : PhysicalSpan base)
    (hx : Equiv (B x (unit base)) czero) :
    leEv (B x (physicalTime 2 x)) (mul (ofQ' (twoStepRate w hd)) (B x x)) := by
  have hzero := centered_of_orthogonal hw0 hw1 base hsmall hd hs hb 0 x hx
  rw [physicalTime_zero] at hzero
  exact leEv_trans
    (leEv_of_equiv (centered_of_orthogonal hw0 hw1 base hsmall hd hs hb 2 x hx).symm)
    (leEv_trans (spatialEvenMoment_first_le hw0 hw1 base hsmall hd hs hb x)
      (leEv_of_equiv (TrigSignedAdd.mul_congr_right hzero)))

/-- The same centered moments have a concrete nonzero-norm scalar witness.
This is not yet a constructed centered vector in the spatial completion. -/
theorem spatialCenteredFace_floor (p : Z4Plaq) (hp : p ∈ spatialFaces base) :
    leEv (ofQ' (starRatio w))
      (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb 0 (faceSpan base p hp) (faceSpan base p hp)) :=
  leEv_of_convergesTo_le (convergesTo_const _)
    (jointCenteredMoment_spatial_converges hw0 hw1 base hsmall hd hs hb 0
      (faceSpan base p hp) (faceSpan base p hp))
    (fun r => by rw [recenter_faceSpan]; exact face_joint_variance_floor hw0 hw1 _ _ _)

#print axioms timeRate
#print axioms timeRate_positive
#print axioms twoStepRate
#print axioms twoStepRate_positive
#print axioms twoStepRate_lt_one
#print axioms spatialCenteredMoment_bound
#print axioms positivePrefactor
#print axioms positivePrefactor_pos
#print axioms spatialCenteredMoment_le_geometric
#print axioms spatialEvenMoment_le_geometric
#print axioms spatialEvenMoment_first_le
#print axioms dense_vacuumComplement_twoStep_bound
#print axioms spatialCenteredFace_floor

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
