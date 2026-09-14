/-
# All factorial moments of the ORIGINAL finite Bernstein rows

Pascal induction on the existing binary words proves
sum C(count,r)*weight = C(N,r)*<x,T^(k+r) D^l x>.
The existing constructive factorial/Pascal bridge then gives the exact
falling-factorial identity at EVERY order and degree, including r>N.
Only finite combinatorial identities are reused from the transvectant
modules; no spectral or group-theoretic premise is introduced.

All moments concern the SAME original completion and transfer. This is
not yet convergence of ordinary grid moments or a spectral measure.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
import YMGap.Continuum.SU2TransvectantFactorialRecurrence

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.SU2TransvectantMixedPentagon (tvFact)
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
  (tvFallingNat tvFact_mul_choose_eq_falling choose_zero_of_lt)
open YMGap.Continuum.PNPaths (choose)

theorem scale_zero (a : RC) : RCscale 0 a=RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

theorem scale_add (a b : Q') (v : RC) :
    RCscale (a+b) v=RCadd (RCscale a v) (RCscale b v) := by
  refine Quotient.inductionOn v ?_
  intro V
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_mul_eqv a b (V.approx n)))

theorem scale_nat_add (a b : Nat) (v : RC) :
    RCscale (Q'.ofNat (a+b)) v=RCadd (RCscale (Q'.ofNat a) v) (RCscale (Q'.ofNat b) v) :=
  (scale_congr (Q'.ofNat_add_eqv a b) v).trans (scale_add _ _ _)

theorem scale_nat_mul (a b : Nat) (v : RC) :
    RCscale (Q'.ofNat (a*b)) v=RCscale (Q'.ofNat a) (RCscale (Q'.ofNat b) v) :=
  (scale_congr (SU3CharFactor.ofNat_mul_eqv a b) v).trans (RCscale_RCscale _ _ _).symm

theorem weighted_choose (x : Completion) (N r k l : Nat) :
    wordSum N (fun p => RCscale (Q'.ofNat (choose (timeCount p) r)) (wordMoment x k l p))=
      RCscale (Q'.ofNat (choose N r)) (mixedMoment x (k+r) l) := by
  induction N generalizing r k l with
  | zero =>
      cases r with
      | zero => rfl
      | succ r =>
          change RCscale 0 (mixedMoment x k l)=RCscale 0 (mixedMoment x (k+(r+1)) l)
          rw [scale_zero,scale_zero]
  | succ N ih =>
      cases r with
      | zero =>
          simp only [choose,Nat.add_zero,wordSum_scale,wordMoment_mass]
      | succ r =>
          change RCadd
            (wordSum N (fun p => RCscale (Q'.ofNat (choose (timeCount p+1) (r+1)))
              (wordMoment x k l (n:=N+1) (true,p))))
            (wordSum N (fun p => RCscale (Q'.ofNat (choose (timeCount p) (r+1)))
              (wordMoment x k l (n:=N+1) (false,p))))=_
          simp only [wordMoment_time,wordMoment_defect,
            show ∀ c, choose (c+1) (r+1)=choose c r+choose c (r+1) from fun _ => rfl,
            scale_nat_add,wordSum_add,ih]
          rw [show (k+1)+r=k+(r+1) by omega,
            show (k+1)+(r+1)=(k+(r+1))+1 by omega,
            add_assoc,← RCscale_RCadd,← mixedMoment_split,← scale_nat_add]

theorem falling_zero_of_lt (n : Nat) : ∀ r, n<r → tvFallingNat n r=0
  | 0,h => by omega
  | r+1,h => by
      by_cases hr : n<r
      · rw [tvFallingNat,falling_zero_of_lt n r hr,Nat.zero_mul]
      · have he : n=r := by omega
        subst n
        rw [tvFallingNat,Nat.sub_self,Nat.mul_zero]

theorem factorial_choose_all (r n : Nat) : tvFact r*choose n r=tvFallingNat n r := by
  by_cases h : r≤n
  · exact tvFact_mul_choose_eq_falling r n h
  · have hn : n<r := by omega
    rw [choose_zero_of_lt n r hn,falling_zero_of_lt n r hn,Nat.mul_zero]

theorem weighted_falling (x : Completion) (N r k l : Nat) :
    wordSum N (fun p => RCscale (Q'.ofNat (tvFallingNat (timeCount p) r)) (wordMoment x k l p))=
      RCscale (Q'.ofNat (tvFallingNat N r)) (mixedMoment x (k+r) l) := by
  simp only [← factorial_choose_all,scale_nat_mul,wordSum_scale,weighted_choose]

end YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.scale_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.scale_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.scale_nat_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.scale_nat_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.weighted_choose
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.falling_zero_of_lt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.factorial_choose_all
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments.weighted_falling
