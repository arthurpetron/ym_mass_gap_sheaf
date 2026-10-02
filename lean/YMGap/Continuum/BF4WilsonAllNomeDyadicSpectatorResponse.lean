/-
# Retained-spectator response at every integer lag of the SAME growing Wilson square

The actual positive-depth finite energy/OWN-variance band is passed through
the already constructed original variance and transfer limits. This gives a
one-step response fraction for the EXISTING centered dyadic excitation.
Existing positive-form propagation gives a strictly positive floor at every
integer lag, including side(scale). No new state, source, center, partition,
operator or convergence input is substituted.

The fraction depends on nome and perimeter, not cutoff, width or terminal
depth. It can deteriorate for growing loops or changing nome. The result is
not a uniform changing-family survival estimate, changing-spacing calibration, nonzero
continuum excitation, physical mass statement or continuum QFT.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
import YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
import YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
import YMGap.Continuum.BF4WilsonAllNomeResponseLower
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicSpectatorResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareResponseFraction squareResponseFraction_positive paddedSquare_energy_band)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit (finiteEnergy)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
  (finiteVariance finiteVariance_budget_pin varianceCauchy varianceLimit
    varianceLimit_completed_pin bond_connected_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
  (singleSlice finiteScalar transferCauchy transferLimit transferLimit_completed_pin)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredExcitation)
open YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
  (dyadicExcitation dyadicExcitation_norm_floor)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)

local infix:50 " ≈ " => Q'.eqv
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

attribute [local irreducible] finiteEnergy finiteVariance finiteScalar
  varianceCauchy varianceLimit transferCauchy transferLimit

private theorem retained_fraction {E V B r : Q'}
    (hV : V ≈ E+B) (hE : E ≤ (1-r)*V) : r*V ≤ B := by
  have h1 : V ≤ (1-r)*V+B := Q'.le_trans' _ _ _ (Q'.le_of_eqv hV)
    (Q'.add_le_add_right _ _ B hE)
  have h2 := Q'.add_le_add_right _ _ (-((1-r)*V)) h1
  have hleft : r*V ≈ V + -((1-r)*V) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.var 1))
      (.add (.var 1) (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))))
      (by decide) (fun | 0 => r | _ => V)
  have hright : ((1-r)*V+B) + -((1-r)*V) ≈ B :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => (1-r)*V | _ => B)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hright))

private theorem scaled_stream_converges (r : Q') (f : Nat → Q') (c : QCauchy f) :
    ConvergesTo (fun n => ofQ' (r*f n)) (mul (ofQ' r) (ofQ'CauchySeq f c)) :=
  TrigAddCReal.convergesTo_congr_seq
    (fun n => (CRealAlg.ofQ'_mul r (f n)).symm)
    (convergesTo_const_mul (ofQ' r) (convergesTo_ofQ'CauchySeq f c))

private theorem scale_rational (r q : Q') : RCscale r (Rq q) = Rq (r*q) :=
  Quotient.sound (CRealAlg.ofQ'_mul r q).symm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "e" => WindowExpression.loop 0 (paddedSquare scale width hwidth) 1
local notation "he" => (Nat.le_refl 0 : Within 0 e)
local notation "rho" => squareResponseFraction hw0 hw1 scale
local notation "v" => Subtype.val (dyadicExcitation hw0 hw1 scale width hwidth)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- The finite completed-limit regulator uses the literal square, its OWN
center and original partition. Positive depth and label one remain explicit. -/
theorem finite_dyadic_energy_band (k n : Nat) (hk : 1 ≤ k) :
    finiteEnergy hw0 hw1 e k (n+1) ≤ (1-rho)*finiteVariance hw0 hw1 e k (n+1) := by
  have hK1 : 1 ≤ headCutoff w+k := Nat.le_trans hk (Nat.le_add_left _ _)
  have h := paddedSquare_energy_band hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) hK1 n scale hwidth
  simpa only [finiteEnergy, finiteVariance, sourcePolynomial, Nat.zero_mul,
    liftBoundary] using h

/-- The actual finite adjacent reserve retains the fraction of SAME OWN
variance. No raw/channel variance or mean is substituted. -/
theorem finite_dyadic_transfer_fraction (k n : Nat) (hk : 1 ≤ k) :
    rho*finiteVariance hw0 hw1 e k (n+1) ≤ finiteScalar hw0 hw1 e k (n+1) :=
  retained_fraction (finiteVariance_budget_pin hw0 hw1 e he k (n+1))
    (finite_dyadic_energy_band hw0 hw1 scale width hwidth k n hk)

/-- Original regulator limits give the response of the EXISTING centered
dyadic excitation under its SAME completed one-step time operator. -/
theorem dyadicExcitation_oneStep_fraction :
    RCle (RCscale rho (B v v)) (B v (T 1 v)) := by
  have hv : ConvergesTo (fun s => ofQ' (rho*finiteVariance hw0 hw1 e s s))
      (mul (ofQ' rho) (varianceLimit hw0 hw1 e he)) := by
    unfold varianceLimit
    exact scaled_stream_converges rho _ (varianceCauchy hw0 hw1 e he)
  have hb : ConvergesTo (fun s => ofQ' (finiteScalar hw0 hw1 e s s))
      (transferLimit hw0 hw1 e he) := by
    unfold transferLimit
    exact convergesTo_ofQ'CauchySeq _ (transferCauchy hw0 hw1 e he)
  have hlim := leEv_of_ofQ'_limit_le hv hb (fun epsilon hp =>
    ⟨1, fun s hs => by
      have h := finite_dyadic_transfer_fraction hw0 hw1 scale width hwidth s (s-1) hs
      rw [Nat.sub_add_cancel hs] at h
      exact Q'.le_trans' _ _ _ h (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hp))⟩)
  have hRC : RCle (RCscale rho (Quotient.mk crealSetoid (varianceLimit hw0 hw1 e he)))
      (Quotient.mk crealSetoid (transferLimit hw0 hw1 e he)) := hlim
  rw [varianceLimit_completed_pin, transferLimit_completed_pin,
    bond_connected_time_pairing] at hRC
  simpa only [singleSlice, loopState, dyadicExcitation, centeredExcitation] using hRC

/-- The existing positive norm floor is consumed on this SAME excitation.
Only nome and square perimeter enter the response coefficient. -/
theorem dyadicExcitation_oneStep_floor :
    RCle (Rq (rho*starRatio w)) (B v (T 1 v)) := by
  have h := RCscale_mono (Q'.le_of_lt (squareResponseFraction_positive hw0 hw1 scale))
    (dyadicExcitation_norm_floor hw0 hw1 scale width hwidth)
  rw [scale_rational] at h
  exact RCle_trans h (dyadicExcitation_oneStep_fraction hw0 hw1 scale width hwidth)

/-- Positive fixed-nome one-step response, not a continuum survival claim. -/
theorem dyadicExcitation_oneStep_ne_zero : B v (T 1 v) ≠ RCzero := by
  intro hz
  have h := dyadicExcitation_oneStep_floor hw0 hw1 scale width hwidth
  rw [hz] at h
  have hle : rho*starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hp
    obtain ⟨N, hN⟩ := h epsilon hp
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le
      (Q'.mul_pos (squareResponseFraction_positive hw0 hw1 scale)
        (starRatio_positive hw0 hw1)) hle)

#print axioms finite_dyadic_energy_band
#print axioms finite_dyadic_transfer_fraction
#print axioms dyadicExcitation_oneStep_fraction
#print axioms dyadicExcitation_oneStep_floor
#print axioms dyadicExcitation_oneStep_ne_zero

private theorem power_positive (a : Q') (ha : (0 : Q') < a) :
    ∀ n : Nat, (0 : Q') < a^n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos ha (power_positive a ha n)

/-- Every integer power of the SAME completed time map retains the computed
fraction on the existing excitation; lag may in particular be `side scale`.
This is not a fraction uniform in lag, perimeter or changing nome. -/
theorem dyadicExcitation_time_geometric_fraction (lag : Nat) :
    RCle (RCscale (rho^lag) (B v v)) (B v (T lag v)) :=
  BF4WilsonAllNomeResponseLower.response_geometric_lower hw0 hw1 v rho
    (Q'.le_of_lt (squareResponseFraction_positive hw0 hw1 scale))
    (dyadicExcitation_oneStep_fraction hw0 hw1 scale width hwidth) lag

/-- The SAME original norm floor gives a positive response floor at every
integer lag. The explicit power may decay with the growing loop and lag. -/
theorem dyadicExcitation_time_geometric_floor (lag : Nat) :
    RCle (Rq (rho^lag*starRatio w)) (B v (T lag v)) := by
  have h := RCscale_mono (Q'.le_of_lt
    (power_positive rho (squareResponseFraction_positive hw0 hw1 scale) lag))
    (dyadicExcitation_norm_floor hw0 hw1 scale width hwidth)
  rw [scale_rational] at h
  exact RCle_trans h
    (dyadicExcitation_time_geometric_fraction hw0 hw1 scale width hwidth lag)

/-- Nonzero response at each integer lag on the actual centered excitation.
No nonzero continuum limit or changing-family survival is inferred. -/
theorem dyadicExcitation_time_response_ne_zero (lag : Nat) :
    B v (T lag v) ≠ RCzero := by
  intro hz
  have h := dyadicExcitation_time_geometric_floor hw0 hw1 scale width hwidth lag
  rw [hz] at h
  have hle : rho^lag*starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hp
    obtain ⟨N, hN⟩ := h epsilon hp
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le
      (Q'.mul_pos
        (power_positive rho (squareResponseFraction_positive hw0 hw1 scale) lag)
        (starRatio_positive hw0 hw1)) hle)

#print axioms dyadicExcitation_time_geometric_fraction
#print axioms dyadicExcitation_time_geometric_floor
#print axioms dyadicExcitation_time_response_ne_zero

end YMGap.Continuum.BF4WilsonAllNomeDyadicSpectatorResponse
