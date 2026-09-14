/-
# Quantitative convergence of ALL original Bernstein probe moments

The finite probability rows already constructed from the SAME original
operator converge on every monomial to <v,T2^r v>. The two-sided error is
at most C(r)/(n+1), with C(0)=0, C(r+1)=C(r)+r, and a computed modulus.
The row moments and limiting original moments retain CReal/QCauchy data.

This is moment convergence at fixed SU(2) nome and spacing. It neither
postulates a spectral decomposition nor constructs the full spectral
functional calculus, continuous-time generator, continuum QFT or Clay result.
-/

import YMGap.Continuum.BernsteinFallingProductError
import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarAddCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar (rationalCauchy)
open YMGap.Continuum.BernsteinFallingProductError

local notation "one" => Quotient.mk crealSetoid cone
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem rat_mono {a b : Q'} (h : a≤b) : RCle (rat a) (rat b) := by
  intro epsilon he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt he))⟩

theorem scale_one_real (a : Q') : RCscale a one=rat a :=
  Quotient.sound (CRealAlg.cmul_cone (ofQ' a))

theorem wordSum_mono (N : Nat) (f g : Word N → RC) (h : ∀ p,RCle (f p) (g p)) :
    RCle (wordSum N f) (wordSum N g) := by
  induction N with
  | zero => exact h ()
  | succ N ih => exact RCadd_le_add (ih _ _ (fun p => h (true,p))) (ih _ _ (fun p => h (false,p)))

def rowAverage (n : Nat) (f : Word (n+1) → Q') : RC :=
  wordSum (n+1) (fun p => RCscale (f p) (Quotient.mk crealSetoid (weight n p)))

theorem rowAverage_mono (n : Nat) (f g : Word (n+1) → Q') (h : ∀ p,f p≤g p) :
    RCle (rowAverage n f) (rowAverage n g) :=
  wordSum_mono _ _ _ (fun p => RCscale_scalar_mono (h p)
    (BF4ExactSlabThermodynamicBernsteinProbeRows.weight_nonnegative n p))

theorem rowAverage_const (n : Nat) (a : Q') : rowAverage n (fun _ => a)=rat a := by
  unfold rowAverage
  rw [wordSum_scale,weight_total,scale_one_real]

theorem rowAverage_add (n : Nat) (f g : Word (n+1) → Q') :
    rowAverage n (fun p => f p+g p)=RCadd (rowAverage n f) (rowAverage n g) := by
  unfold rowAverage
  simp only [scale_add,wordSum_add]

def powerMoment (n r : Nat) : RC := rowAverage n (fun p => node n p^r)

def limitRepresentative (r : Nat) : CReal := momentRepresentative probeCauchy r 0

def limitCauchy (r : Nat) : QCauchy (limitRepresentative r).approx := momentCauchy probeCauchy r 0

def limitMoment (r : Nat) : RC := Quotient.mk crealSetoid (limitRepresentative r)

theorem limitMoment_pin (r : Nat) : limitMoment r=mixedMoment unitProbe.val r 0 := by
  rw [← probeCauchy_pin]
  exact (moment_pin probeCauchy r 0).symm

theorem limitMoment_nonnegative (r : Nat) : RCnonneg (limitMoment r) := by
  rw [limitMoment_pin]
  exact mixedMoment_nonnegative _ _ _

theorem limitMoment_le_one (r : Nat) : RCle (limitMoment r) one := by
  rw [limitMoment_pin,mixedMoment_halfTime]
  have h := completedTime_contraction r unitProbe.val
  rw [unitProbe_norm] at h
  exact h

theorem falling_average (n r : Nat) :
    rowAverage n (fun p => product n (timeCount p) r)=RCscale (product n (n+1) r) (limitMoment r) := by
  unfold rowAverage
  simp only [weight_pin]
  have hterms :
      (fun p : Word (n+1) => RCscale (product n (timeCount p) r) (wordMoment unitProbe.val 0 0 p))=
      (fun p : Word (n+1) => RCscale (Q'.invSucc n^r)
        (RCscale (Q'.ofNat (SU2TransvectantFactorialRecurrence.tvFallingNat (timeCount p) r))
          (wordMoment unitProbe.val 0 0 p))) := by
    funext p
    exact (scale_congr (product_falling n (timeCount p) r) _).trans (RCscale_RCscale _ _ _).symm
  rw [hterms,wordSum_scale,weighted_falling,RCscale_RCscale,Nat.zero_add,
    ← scale_congr (product_falling n (n+1) r),← limitMoment_pin]

theorem powerMoment_lower (n r : Nat) :
    RCle (RCscale (product n (n+1) r) (limitMoment r)) (powerMoment n r) := by
  rw [← falling_average]
  exact rowAverage_mono n _ _ (fun p => product_le_power n (timeCount p) r)

theorem powerMoment_upper (n r : Nat) :
    RCle (powerMoment n r) (RCadd (RCscale (product n (n+1) r) (limitMoment r)) (rat (error n r))) := by
  have h := rowAverage_mono n _ _ (fun p : Word (n+1) =>
    power_le_product_error n (timeCount p) (by have hc := counts_sum p; omega) r)
  rw [rowAverage_add,rowAverage_const,falling_average] at h
  exact h

theorem scaled_limit_le (n r : Nat) : RCle (RCscale (product n (n+1) r) (limitMoment r)) (limitMoment r) := by
  have h := RCscale_scalar_mono (product_le_one n (n+1) r (Nat.le_refl _)) (limitMoment_nonnegative r)
  rw [RCscale_one] at h
  exact h

theorem limit_scaled_budget (n r : Nat) :
    RCle (limitMoment r) (RCadd (RCscale (product n (n+1) r) (limitMoment r)) (rat (error n r))) := by
  have h := RCscale_scalar_mono (top_product_budget n r) (limitMoment_nonnegative r)
  rw [RCscale_one,scale_add] at h
  have he := RCscale_mono (error_nonnegative n r) (limitMoment_le_one r)
  rw [scale_one_real] at he
  exact RCle_trans h (RCadd_le_add (RCle_refl _) he)

/-- The same triangular error controls BOTH directions, at every order. -/
theorem powerMoment_error (n r : Nat) :
    RCle (powerMoment n r) (RCadd (limitMoment r) (rat (error n r))) ∧
    RCle (limitMoment r) (RCadd (powerMoment n r) (rat (error n r))) :=
  ⟨RCle_trans (powerMoment_upper n r) (RCadd_le_add (scaled_limit_le n r) (RCle_refl _)),
    RCle_trans (limit_scaled_budget n r) (RCadd_le_add (powerMoment_lower n r) (RCle_refl _))⟩

def wordRealSum : (N : Nat) → (Word N → CReal) → CReal
  | 0,f => f ()
  | N+1,f => CReal.add (wordRealSum N (fun p => f (true,p))) (wordRealSum N (fun p => f (false,p)))

def wordRealSumCauchy (N : Nat) (f : Word N → CReal) (h : ∀ p,QCauchy (f p).approx) :
    QCauchy (wordRealSum N f).approx := by
  induction N with
  | zero => exact h ()
  | succ N ih => exact scalarAddCauchy _ _ (ih _ (fun p => h (true,p))) (ih _ (fun p => h (false,p)))

theorem wordRealSum_pin (N : Nat) (f : Word N → CReal) :
    Quotient.mk crealSetoid (wordRealSum N f)=wordSum N (fun p => Quotient.mk crealSetoid (f p)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change RCadd (Quotient.mk crealSetoid (wordRealSum N (fun p => f (true,p))))
        (Quotient.mk crealSetoid (wordRealSum N (fun p => f (false,p))))=_
      rw [ih,ih]
      rfl

def powerRepresentative (n r : Nat) : CReal :=
  wordRealSum (n+1) (fun p => CReal.mul (ofQ' (node n p^r)) (weight n p))

def powerCauchy (n r : Nat) : QCauchy (powerRepresentative n r).approx :=
  wordRealSumCauchy _ _ (fun p => scalarMulCauchy _ _ (rationalCauchy _) (weightCauchy n p))

theorem powerRepresentative_pin (n r : Nat) :
    Quotient.mk crealSetoid (powerRepresentative n r)=powerMoment n r := wordRealSum_pin _ _

def momentModulus (r : Nat) (epsilon : Q') : Nat := modulus r epsilon

theorem moment_error_le (r : Nat) (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : momentModulus r epsilon≤n) :
    leEv (powerRepresentative n r) (CReal.add (limitRepresentative r) (ofQ' epsilon)) ∧
    leEv (limitRepresentative r) (CReal.add (powerRepresentative n r) (ofQ' epsilon)) := by
  have hh := rat_mono (error_small r epsilon he n hn)
  have h := powerMoment_error n r
  have h1 := RCle_trans h.1 (RCadd_le_add (RCle_refl _) hh)
  have h2 := RCle_trans h.2 (RCadd_le_add (RCle_refl _) hh)
  rw [← powerRepresentative_pin] at h1 h2
  exact ⟨h1,h2⟩

/-- The limit, its Cauchy data, the actual-operator pin and the rate are returned. -/
def momentConvergenceCertificate (r : Nat) :
    Σ' a : CReal, QCauchy a.approx ×'
      (Quotient.mk crealSetoid a=completedInner unitProbe.val (completedTime (r+r) unitProbe.val)) ×'
      {M : Q' → Nat // ∀ epsilon,(0 : Q')<epsilon → ∀ n,M epsilon≤n →
        leEv (powerRepresentative n r) (CReal.add a (ofQ' epsilon)) ∧
        leEv a (CReal.add (powerRepresentative n r) (ofQ' epsilon))} :=
  ⟨limitRepresentative r,limitCauchy r,limitMoment_pin r,⟨momentModulus r,moment_error_le r⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.rat_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.scale_one_real
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.wordSum_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.rowAverage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.rowAverage_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.rowAverage_const
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.rowAverage_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.powerMoment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.limitRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.limitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.limitMoment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.limitMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.limitMoment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.limitMoment_le_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.falling_average
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.powerMoment_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.powerMoment_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.scaled_limit_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.limit_scaled_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.powerMoment_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.wordRealSum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.wordRealSumCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.wordRealSum_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.powerRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.powerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.powerRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.momentModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.moment_error_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence.momentConvergenceCertificate
