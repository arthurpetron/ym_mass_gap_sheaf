/-
# Explicit original dyadic-time continuity moduli

The original preimage's supplied Cauchy stream computes a norm ceiling.
The denominator of epsilon/(ceiling+1) is a sufficient dyadic depth for
ALL small increments on T(1)x, and for increments relative to any positive
dyadic anchor. Only carrier-free scalar tolerance lemmas are reused from
the legacy thermodynamic file; its carrier and time operator are not used.

The same result extends to an existing represented Cauchy limit of original
time images with SUPPLIED preimage representatives. Neither boundedness nor
convergence of those preimages is required, and none is selected by choice.
This is not full-carrier continuity, a range-density claim, a real-time
extension, a generator identity, or physical/scaling calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- An explicit sufficient depth, computed from the ORIGINAL representative. -/
def rangeModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  (linearTolerance (normCeiling PD X) (normCeiling_nonnegative PD X) epsilon).den

theorem scaled_norm_small (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : rangeModulus hw0 hw1 X epsilon ≤ k) :
    RCle (RCscale (half^k) (B (Class X) (Class X))) (rat epsilon) := by
  let cap := normCeiling PD X
  have hc : (0 : Q') ≤ cap := normCeiling_nonnegative PD X
  let delta := linearTolerance cap hc epsilon
  have hp : half^k ≤ delta := Q'.le_trans' _ _ _ (HalfPow.pow_half_le_invSucc k)
    (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hk)
      (HalfPow.invSucc_den_le delta (linearTolerance_pos cap hc he)))
  have hb : (half^k)*cap ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ cap hp hc)
      (linearTolerance_budget cap hc he))
  have h := RCscale_mono (Q'.pow_nonneg half half_nonneg k)
    (completedInner_diagonal_le_normCeiling PD X)
  have hs : RCscale (half^k) (rat cap) = rat ((half^k)*cap) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hs] at h
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ => hb))

/-- The threshold controls every supplied dyadic presentation, not just roots. -/
theorem range_smallTime (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (depth steps : Nat) (hsmall : steps*2^(rangeModulus hw0 hw1 X epsilon) ≤ 2^depth) :
    RCle (d (S depth steps (T 1 (Class X))) (T 1 (Class X))) (rat epsilon) :=
  RCle_trans (range_small_bound hw0 hw1 depth steps (rangeModulus hw0 hw1 X epsilon) hsmall (Class X))
    (scaled_norm_small hw0 hw1 X epsilon he _ (Nat.le_refl _))

/-- The computed threshold is retained as Type-level data. -/
def rangeContinuityCertificate (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    {k : Nat // ∀ depth steps, steps*2^k ≤ 2^depth →
      RCle (d (S depth steps (T 1 (Class X))) (T 1 (Class X))) (rat epsilon)} :=
  ⟨rangeModulus hw0 hw1 X epsilon,range_smallTime hw0 hw1 X epsilon he⟩

/-- Relative to an arbitrary anchor. A zero anchor permits only zero increments. -/
theorem anchored_smallTime (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (anchorDepth anchorSteps depth steps : Nat)
    (hsmall : (steps*2^anchorDepth)*2^(rangeModulus hw0 hw1 X epsilon) ≤ anchorSteps*2^depth) :
    RCle (d (S depth steps (S anchorDepth anchorSteps (Class X)))
      (S anchorDepth anchorSteps (Class X))) (rat epsilon) :=
  RCle_trans (anchored_small_bound hw0 hw1 anchorDepth anchorSteps depth steps
    (rangeModulus hw0 hw1 X epsilon) hsmall (Class X))
    (scaled_norm_small hw0 hw1 X epsilon he _ (Nat.le_refl _))

private def tenth (e : Q') : Q' := Q'.invSucc 9 * e

private theorem ten_tenths (e : Q') :
    RCadd (RCadd (rat (tenth e)) (rat (tenth e)))
      (RCadd
        (RCadd (RCadd (rat (tenth e)) (rat (tenth e))) (RCadd (rat (tenth e)) (rat (tenth e))))
        (RCadd (RCadd (rat (tenth e)) (rat (tenth e))) (RCadd (rat (tenth e)) (rat (tenth e))))) = rat e := by
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv
    ((tenth e+tenth e)+(((tenth e+tenth e)+(tenth e+tenth e))+((tenth e+tenth e)+(tenth e+tenth e)))) e
  have hsum : Q'.eqv
      ((tenth e+tenth e)+(((tenth e+tenth e)+(tenth e+tenth e))+((tenth e+tenth e)+(tenth e+tenth e))))
      (10*tenth e) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0))
        (.add (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
          (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))))
      (.mul (.const 10) (.var 0)) (by decide) (fun _ => tenth e)
  exact Q'.eqv_trans _ _ _ hsum (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (10*Q'.invSucc 9) (1 : Q')))
      (Q'.one_mul_eqv e)))

/-- A represented limit supplies the index; only that supplied preimage's norm
ceiling is used. Preimages need not be a Cauchy or uniformly bounded sequence. -/
def closureModulus (R : RepresentedCauchy hw0 hw1 (width := width))
    (preimages : Nat → (D).Cauchy) (epsilon : Q') : Nat :=
  rangeModulus hw0 hw1 (preimages (limitRate hw0 hw1 R (tenth epsilon))) (tenth epsilon)

theorem closure_smallTime (R : RepresentedCauchy hw0 hw1 (width := width))
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, rowPoint hw0 hw1 R n = T 1 (Class (preimages n)))
    (epsilon : Q') (he : (0 : Q') < epsilon) (depth steps : Nat)
    (hsmall : steps*2^(closureModulus hw0 hw1 R preimages epsilon) ≤ 2^depth) :
    RCle (d (S depth steps (limit hw0 hw1 R)) (limit hw0 hw1 R)) (rat epsilon) := by
  let delta := tenth epsilon
  have hd : (0 : Q') < delta := Q'.mul_pos (Q'.invSucc_pos 9) he
  let n := limitRate hw0 hw1 R delta
  let a := T 1 (Class (preimages n))
  let z := limit hw0 hw1 R
  have hclose : RCle (d a z) (rat delta) := by
    have h := limit_bound hw0 hw1 R delta hd n (Nat.le_refl _)
    rwa [hpin] at h
  have hleft : RCle (d (S depth steps z) (S depth steps a)) (rat delta) :=
    RCle_trans (mesh_distance_bound hw0 hw1 depth steps z a)
      (by rw [completedDist_symm]; exact hclose)
  have hmiddle : RCle (d (S depth steps a) a) (rat delta) :=
    range_smallTime hw0 hw1 (preimages n) delta hd depth steps hsmall
  have hright := RCle_trans (completedDist_triangle hw0 hw1 (S depth steps a) a z)
    (RCadd_le_add (RCadd_le_add hmiddle hmiddle) (RCadd_le_add hclose hclose))
  have h := RCle_trans (completedDist_triangle hw0 hw1 (S depth steps z) (S depth steps a) z)
    (RCadd_le_add (RCadd_le_add hleft hleft) (RCadd_le_add hright hright))
  rwa [ten_tenths] at h

/-- Continuity data for the existing represented positive-time range closure. -/
def closureContinuityCertificate (R : RepresentedCauchy hw0 hw1 (width := width))
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, rowPoint hw0 hw1 R n = T 1 (Class (preimages n)))
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    {k : Nat // ∀ depth steps, steps*2^k ≤ 2^depth →
      RCle (d (S depth steps (limit hw0 hw1 R)) (limit hw0 hw1 R)) (rat epsilon)} :=
  ⟨closureModulus hw0 hw1 R preimages epsilon,
    closure_smallTime hw0 hw1 R preimages hpin epsilon he⟩

#print axioms rangeModulus
#print axioms scaled_norm_small
#print axioms range_smallTime
#print axioms rangeContinuityCertificate
#print axioms anchored_smallTime
#print axioms closureModulus
#print axioms closure_smallTime
#print axioms closureContinuityCertificate

end YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
