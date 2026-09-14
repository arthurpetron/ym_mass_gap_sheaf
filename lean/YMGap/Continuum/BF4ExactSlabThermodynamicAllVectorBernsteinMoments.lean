/-
# Bernstein moment bounds for EVERY original completed vector

The existing all-vector positive mixed moments give finite Bernstein rows
with total mass ||x||^2, without normalizing x or choosing a cyclic probe.
The existing all-order falling-factorial identity gives the two-sided
moment error C(r)/(n+1) * ||x||^2 on the SAME original transfer.

For a supplied original Cauchy representative the existing computed norm
cap gives a rational error bound. Zero vectors are included. No density,
spectral-model or normalization premise is supplied. Nome and spacing
remain fixed; this is not a continuum or physical-scale gap conclusion.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows (node)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence (wordSum_mono)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BernsteinFallingProductError

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def average (x : Completion) (n : Nat) (f : Word (n+1) → Q') : RC :=
  wordSum (n+1) (fun p => RCscale (f p) (wordMoment x 0 0 p))

theorem average_mono (x : Completion) (n : Nat) (f g : Word (n+1) → Q') (h : ∀ p,f p≤g p) :
    RCle (average x n f) (average x n g) :=
  wordSum_mono _ _ _ (fun p => RCscale_scalar_mono (h p) (weight_nonnegative x p))

theorem average_const (x : Completion) (n : Nat) (a : Q') :
    average x n (fun _ => a)=RCscale a (completedInner x x) := by
  unfold average
  rw [wordSum_scale,weights_total]

theorem average_add (x : Completion) (n : Nat) (f g : Word (n+1) → Q') :
    average x n (fun p => f p+g p)=RCadd (average x n f) (average x n g) := by
  unfold average
  simp only [scale_add,wordSum_add]

theorem average_scale (x : Completion) (n : Nat) (c : Q') (f : Word (n+1) → Q') :
    average x n (fun p => c*f p)=RCscale c (average x n f) := by
  unfold average
  simp only [← RCscale_RCscale,wordSum_scale]

theorem average_congr (x : Completion) (n : Nat) (f g : Word (n+1) → Q') (h : ∀ p,Q'.eqv (f p) (g p)) :
    average x n f=average x n g := by
  unfold average
  congr 1
  funext p
  exact scale_congr (h p) _

def powerMoment (x : Completion) (n r : Nat) : RC := average x n (fun p => node n p^r)

def moment (x : Completion) (r : Nat) : RC := mixedMoment x r 0

theorem moment_pin (x : Completion) (r : Nat) : moment x r=completedInner x (completedTime (r+r) x) := rfl

theorem moment_nonnegative (x : Completion) (r : Nat) : RCnonneg (moment x r) :=
  mixedMoment_nonnegative x r 0

theorem moment_le_norm (x : Completion) (r : Nat) : RCle (moment x r) (completedInner x x) := by
  rw [moment,mixedMoment_halfTime]
  exact completedTime_contraction r x

theorem falling_average (x : Completion) (n r : Nat) :
    average x n (fun p => product n (timeCount p) r)=RCscale (product n (n+1) r) (moment x r) := by
  unfold average
  have hterms :
      (fun p : Word (n+1) => RCscale (product n (timeCount p) r) (wordMoment x 0 0 p))=
      (fun p : Word (n+1) => RCscale (Q'.invSucc n^r)
        (RCscale (Q'.ofNat (SU2TransvectantFactorialRecurrence.tvFallingNat (timeCount p) r))
          (wordMoment x 0 0 p))) := by
    funext p
    exact (scale_congr (product_falling n (timeCount p) r) _).trans (RCscale_RCscale _ _ _).symm
  rw [hterms,wordSum_scale,weighted_falling,RCscale_RCscale,Nat.zero_add,
    ← scale_congr (product_falling n (n+1) r)]
  rfl

theorem powerMoment_lower (x : Completion) (n r : Nat) :
    RCle (RCscale (product n (n+1) r) (moment x r)) (powerMoment x n r) := by
  rw [← falling_average]
  exact average_mono x n _ _ (fun p => product_le_power n (timeCount p) r)

theorem powerMoment_upper (x : Completion) (n r : Nat) :
    RCle (powerMoment x n r)
      (RCadd (RCscale (product n (n+1) r) (moment x r)) (RCscale (error n r) (completedInner x x))) := by
  have h := average_mono x n _ _ (fun p : Word (n+1) =>
    power_le_product_error n (timeCount p) (by have hc := counts_sum p; omega) r)
  rw [average_add,average_const,falling_average] at h
  exact h

theorem scaled_moment_le (x : Completion) (n r : Nat) :
    RCle (RCscale (product n (n+1) r) (moment x r)) (moment x r) := by
  have h := RCscale_scalar_mono (product_le_one n (n+1) r (Nat.le_refl _)) (moment_nonnegative x r)
  rw [RCscale_one] at h
  exact h

theorem moment_scaled_budget (x : Completion) (n r : Nat) :
    RCle (moment x r)
      (RCadd (RCscale (product n (n+1) r) (moment x r)) (RCscale (error n r) (completedInner x x))) := by
  have h := RCscale_scalar_mono (top_product_budget n r) (moment_nonnegative x r)
  rw [RCscale_one,scale_add] at h
  exact RCle_trans h (RCadd_le_add (RCle_refl _) (RCscale_mono (error_nonnegative n r) (moment_le_norm x r)))

theorem powerMoment_error (x : Completion) (n r : Nat) :
    RCle (powerMoment x n r) (RCadd (moment x r) (RCscale (error n r) (completedInner x x))) ∧
    RCle (moment x r) (RCadd (powerMoment x n r) (RCscale (error n r) (completedInner x x))) :=
  ⟨RCle_trans (powerMoment_upper x n r) (RCadd_le_add (scaled_moment_le x n r) (RCle_refl _)),
    RCle_trans (moment_scaled_budget x n r) (RCadd_le_add (powerMoment_lower x n r) (RCle_refl _))⟩

/-- The exact rational fold keeps computed norm caps opaque to elaboration. -/
theorem scale_rational (a b : Q') : RCscale a (rat b)=rat (a*b) := by
  rw [RCscale_mk]
  exact Quotient.sound (CReal.Equiv.symm (CRealAlg.ofQ'_mul a b))

/-- The cap is computed from supplied original Cauchy data, never selected from a quotient. -/
theorem powerMoment_error_cap (X : seminorm.Cauchy) (n r : Nat) :
    RCle (powerMoment (Quotient.mk seminorm.completionSetoid X) n r)
      (RCadd (moment (Quotient.mk seminorm.completionSetoid X) r) (rat (error n r*normCap X))) ∧
    RCle (moment (Quotient.mk seminorm.completionSetoid X) r)
      (RCadd (powerMoment (Quotient.mk seminorm.completionSetoid X) n r) (rat (error n r*normCap X))) := by
  have h := powerMoment_error (Quotient.mk seminorm.completionSetoid X) n r
  have hb := RCscale_mono (error_nonnegative n r) (norm_le_cap X)
  rw [scale_rational] at hb
  exact ⟨RCle_trans h.1 (RCadd_le_add (RCle_refl _) hb),RCle_trans h.2 (RCadd_le_add (RCle_refl _) hb)⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.average
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.average_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.average_const
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.average_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.average_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.average_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.powerMoment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.moment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.moment_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.moment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.moment_le_norm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.falling_average
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.powerMoment_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.powerMoment_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.scaled_moment_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.moment_scaled_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.powerMoment_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.scale_rational
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments.powerMoment_error_cap
