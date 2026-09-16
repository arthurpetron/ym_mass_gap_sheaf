/-
# Actual centered spatial vectors realize the original connected moments

The explicit rational centering streams live in the existing spatial
completion. Their completed pairing with the original unit is zero.
Their correlations under the SAME completed physical time are exactly the
spatialCenteredMoment already pinned to the original connected scalar
diagonal. No representative choice or completed real scalar action is used.

The small-nome guards and fixed lattice spacing remain explicit. These
are identities on the actual Cauchy quotient, not metric completeness,
a continuum Hilbert/OS reconstruction, or physical mass calibration.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredStream
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (unit zero physicalTime physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra
  (centerApprox physicalTime_centerApprox)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenterAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredStream
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb
local notation "P" => spatialPairing hw0 hw1 base hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 base hsmall hd hs hb
local notation "C" => centeredStream hw0 hw1 base hsmall hd hs hb
local notation "v" => centeredVector hw0 hw1 base hsmall hd hs hb

attribute [local irreducible] spatialPairing

/-- The explicit spatial mean approximations center the SAME unit coefficient. -/
theorem centered_unit_representative (x : PhysicalSpan base) :
    Equiv (representativeInner hw0 hw1 base hsmall hd hs hb (C x) ((D).constant (unit base)))
      czero := by
  have hc : ConvergesTo
      (fun k => sub (mean hw0 hw1 base hsmall hd hs hb x)
        (ofQ' ((mean hw0 hw1 base hsmall hd hs hb x).approx k)))
      (sub (mean hw0 hw1 base hsmall hd hs hb x) (mean hw0 hw1 base hsmall hd hs hb x)) :=
    TrigAddCReal.convergesTo_add (convergesTo_const _)
      (TrigAddCReal.convergesTo_neg (mean_approximations_converge hw0 hw1 base hsmall hd hs hb x))
  exact (Equiv_of_limit_of_equal
    (fun k => centerApprox_unit hw0 hw1 base hsmall hd hs hb x
      ((mean hw0 hw1 base hsmall hd hs hb x).approx k))
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb (C x) ((D).constant (unit base))) hc).trans
      (sub_self_eqv_zero _)

theorem centeredVector_orthogonal (x : PhysicalSpan base) :
    B (v x) (spatialCompletedUnit hw0 hw1 base hsmall hd hs hb) = RCzero :=
  Quotient.sound (centered_unit_representative hw0 hw1 base hsmall hd hs hb x)

private theorem unit_time_pairing (n : Nat) (y : PhysicalSpan base) :
    Equiv (P (unit base) (physicalTime n y)) (P (unit base) y) := by
  simpa only [physicalTime_unit] using
    (spatialPairing_time_balance hw0 hw1 base hsmall hd hs hb n (unit base) y).symm

/-- Rational centering, scalar limit and physical time retain the same
spatial form. The disappearing cross term is an actual scalar identity. -/
theorem centered_time_representative (n : Nat) (x y : PhysicalSpan base) :
    Equiv (representativeInner hw0 hw1 base hsmall hd hs hb (C x)
      ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy (C y)))
      (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y) := by
  let mu := mean hw0 hw1 base hsmall hd hs hb x
  let nu := mean hw0 hw1 base hsmall hd hs hb y
  let A := P x (physicalTime n y)
  let E := P (unit base) (physicalTime n y)
  let F (k : Nat) :=
    sub (sub A (mul (ofQ' (mu.approx k)) E))
      (sub (mul (ofQ' (nu.approx k)) mu)
        (mul (ofQ' (mu.approx k)) (ofQ' (nu.approx k))))
  have hmu := mean_approximations_converge hw0 hw1 base hsmall hd hs hb x
  have hnu := mean_approximations_converge hw0 hw1 base hsmall hd hs hb y
  have hc : ConvergesTo F
      (sub (sub A (mul mu E)) (sub (mul nu mu) (mul mu nu))) :=
    TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (convergesTo_const A)
        (TrigAddCReal.convergesTo_neg
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hmu (convergesTo_const E))))
      (TrigAddCReal.convergesTo_neg
        (TrigAddCReal.convergesTo_add
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hnu (convergesTo_const mu))
          (TrigAddCReal.convergesTo_neg
            (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
              hmu hnu))))
  have h := Equiv_of_limit_of_equal
    (aSeq := pairSequence hw0 hw1 base hsmall hd hs hb (C x)
      ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy (C y)))
    (bSeq := F)
    (fun k => by
      change Equiv (P (centerApprox x (mu.approx k))
        (physicalTime n (centerApprox y (nu.approx k)))) _
      rw [physicalTime_centerApprox]
      exact (centerApprox_pairing hw0 hw1 base hsmall hd hs hb x (physicalTime n y)
        (mu.approx k) (nu.approx k)).trans
          (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)))
    (pairSequence_converges hw0 hw1 base hsmall hd hs hb (C x)
      ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy (C y))) hc
  have hcancel : Equiv (sub (mul nu mu) (mul mu nu)) czero :=
    (Equiv_add (CRealAlg.cmul_comm nu mu) (Equiv.refl _)).trans (sub_self_eqv_zero _)
  have hclean : Equiv (sub (sub A (mul mu E)) (sub (mul nu mu) (mul mu nu)))
      (sub A (mul mu E)) :=
    (Equiv_add (Equiv.refl _) (neg_congr hcancel)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-(0 : Q')) 0))
          (QPoly.q_add_zero_eqv _)))
  exact h.trans (hclean.trans (Equiv_add (Equiv.refl _) (neg_congr
    (TrigSignedAdd.mul_congr_right (unit_time_pairing hw0 hw1 base hsmall hd hs hb n y)))))

/-- The completed correlation is exactly the existing original connected
spatial limit at the displayed discrete physical lag. -/
theorem centeredVector_time_pairing (n : Nat) (x y : PhysicalSpan base) :
    B (v x) (spatialCompletedTime hw0 hw1 base hsmall hd hs hb n (v y)) =
      Quotient.mk crealSetoid (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y) :=
  Quotient.sound (centered_time_representative hw0 hw1 base hsmall hd hs hb n x y)

theorem centeredVector_pairing (x y : PhysicalSpan base) :
    B (v x) (v y) =
      Quotient.mk crealSetoid (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb 0 x y) := by
  simpa only [spatialCompletedTime_zero] using
    centeredVector_time_pairing hw0 hw1 base hsmall hd hs hb 0 x y

theorem spatialCompletedZero_norm :
    B (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (zero base))
      (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (zero base)) = RCzero := by
  rw [completedInner_embedSpan]
  exact Quotient.sound (spatialDistSq_refl hw0 hw1 base hsmall hd hs hb (zero base))

#print axioms centered_unit_representative
#print axioms centeredVector_orthogonal
#print axioms centered_time_representative
#print axioms centeredVector_time_pairing
#print axioms centeredVector_pairing
#print axioms spatialCompletedZero_norm

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredPairing
