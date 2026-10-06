/-
# Even-lag Jensen bound and the relative-energy route to the macroscopic ratio

The even responses `E_k = R(2k) = B x (T(2k) x)` of ANY completed vector form
a nonnegative log-convex sequence (`response_log_convex`). A positive rational
norm floor and one relative two-step floor `rho*R(0) <= R(2)` therefore give,
without division or case splits on vanishing,

  rho*R(2n) <= R(2n+2)   and   rho^n * R(0) <= R(2n)   for every n,

i.e. `R(2n)*R(0)^(n-1) >= R(2)^n` in cleared form. Combined with the survival
compiler this yields `rho^u * R(2u) <= R(4u)`.

The block compiler converts a SMALL relative two-step energy into a macro
ratio: if `1 - t` is the two-step floor, `L*t <= 1/2` and `u = L*k`, then
`(1/2)^k * R(2u) <= R(4u)`. With `t <= c/u` one takes `L ~ u/(2c)`, `k ~ 2c`,
so kappa is about `4^(-c)`, uniform in the side.

Scope: these are compilers. The relative-energy floor itself (eps <= c/side
for a smoothed/coherent state on a justified changing family) is NOT supplied.
The odd-lag version (`R(n)R(0)^(n-1) >= R(1)^n`) needs Cauchy--Schwarz for the
one-step form `B(y, T z)` and is left open here.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
import YMGap.Continuum.BondMovingRetuneFix
import YMGap.Continuum.FiveHolonomyPerronCutoff
import YMGap.Continuum.ReconstructionCapstone
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.BF4WilsonAllNomeEvenResponseJensen

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
  (rc_ratio_step response_log_convex response_even_nonnegative macro_ratio_of_survival_floor)

/-! ## Scalar bookkeeping -/

private theorem czero_le_ofQ' {r : Q'} (hr : (0 : Q') ≤ r) : leEv czero (ofQ' r) := by
  intro epsilon hepsilon
  exact ⟨0, fun _ _ => Q'.le_trans' _ _ _ hr
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))⟩

/-- `r*a <= b`, `rho*b <= c`, `rho >= 0` give `(rho*r)*a <= c`. -/
theorem creal_scale_chain (a b c : CReal) (r rho : Q') (hrho : (0 : Q') ≤ rho)
    (hab : leEv (mul (ofQ' r) a) b) (hbc : leEv (mul (ofQ' rho) b) c) :
    leEv (mul (ofQ' (rho*r)) a) c := by
  have hm := leEv_mul_nonneg_left (czero_le_ofQ' hrho) hab
  have e : Equiv (mul (ofQ' (rho*r)) a) (mul (ofQ' rho) (mul (ofQ' r) a)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => rho | 1 => r | _ => a.approx n))
  exact leEv_trans (leEv_of_equiv e) (leEv_trans hm hbc)

theorem rc_scale_chain (a b c : RC) (r rho : Q') (hrho : (0 : Q') ≤ rho)
    (hab : RCle (RCscale r a) b) (hbc : RCle (RCscale rho b) c) :
    RCle (RCscale (rho*r) a) c := by
  revert hab hbc
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C hab hbc
  exact creal_scale_chain A B' C r rho hrho hab hbc

/-! ## Log-convex sequences -/

/-- A nonnegative log-convex RC sequence with a positive rational floor at 0
and a ratio floor at 0 keeps the ratio floor and a geometric positive floor
at every index. Positivity is propagated, never assumed at later indices. -/
theorem rc_logconvex_ratio_floor (E : Nat → RC) (rho p : Q')
    (hrho : (0 : Q') < rho) (hp : (0 : Q') < p)
    (h0 : RCle (RCscale 1 (Quotient.mk crealSetoid (ofQ' p))) (E 0))
    (hnn : ∀ k, RCnonneg (E k))
    (hcs : ∀ k, RCle (RCmul (E (k+1)) (E (k+1))) (RCmul (E k) (E (k+2))))
    (h1 : RCle (RCscale rho (E 0)) (E 1)) :
    ∀ n, RCle (RCscale rho (E n)) (E (n+1)) ∧
      RCle (RCscale (rho^n) (Quotient.mk crealSetoid (ofQ' p))) (E n)
  | 0 => ⟨h1, h0⟩
  | n+1 =>
      let ih := rc_logconvex_ratio_floor E rho p hrho hp h0 hnn hcs h1 n
      ⟨rc_ratio_step (E n) (E (n+1)) (E (n+2)) rho (rho^n) p
          (HKPos.pow_pos hrho n) hp ih.2 (hnn (n+1)) (hcs n) ih.1,
        rc_scale_chain _ (E n) (E (n+1)) (rho^n) rho (Q'.le_of_lt hrho) ih.2 ih.1⟩

/-- Cleared Jensen bound on the even grid: `rho^n * E_0 <= E_n`. -/
theorem rc_logconvex_geometric (E : Nat → RC) (rho p : Q')
    (hrho : (0 : Q') < rho) (hp : (0 : Q') < p)
    (h0 : RCle (RCscale 1 (Quotient.mk crealSetoid (ofQ' p))) (E 0))
    (hnn : ∀ k, RCnonneg (E k))
    (hcs : ∀ k, RCle (RCmul (E (k+1)) (E (k+1))) (RCmul (E k) (E (k+2))))
    (h1 : RCle (RCscale rho (E 0)) (E 1)) :
    ∀ n, RCle (RCscale (rho^n) (E 0)) (E n)
  | 0 => by
      show RCle (RCscale 1 (E 0)) (E 0)
      rw [RCscale_one]; exact RCle_refl _
  | n+1 => rc_scale_chain (E 0) (E n) (E (n+1)) (rho^n) rho (Q'.le_of_lt hrho)
      (rc_logconvex_geometric E rho p hrho hp h0 hnn hcs h1 n)
      (rc_logconvex_ratio_floor E rho p hrho hp h0 hnn hcs h1 n).1

section Completed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- EVEN-LAG JENSEN. A positive rational norm floor and a relative two-step
floor `rho*R(0) <= R(2)` give `rho^n * R(0) <= R(2n)` for every n. -/
theorem response_even_jensen (x : V) (rho q : Q')
    (hrho : (0 : Q') < rho) (hq : (0 : Q') < q)
    (hnorm : RCle (Quotient.mk crealSetoid (ofQ' q)) (B x x))
    (h2 : RCle (RCscale rho (B x x)) (B x (T 2 x))) :
    ∀ n, RCle (RCscale (rho^n) (B x x)) (B x (T (2*n) x)) := by
  let E : Nat → RC := fun k => B x (T (2*k) x)
  have e0 : E 0 = B x x := by
    show B x (T (2*0) x) = B x x
    rw [Nat.mul_zero, completedTime_zero]
  have hcs : ∀ k, RCle (RCmul (E (k+1)) (E (k+1))) (RCmul (E k) (E (k+2))) := by
    intro k
    have h := response_log_convex hw0 hw1 width x k (k+2)
    rw [show k + (k+2) = 2*(k+1) by omega] at h
    exact h
  have h0 : RCle (RCscale 1 (Quotient.mk crealSetoid (ofQ' q))) (E 0) := by
    rw [RCscale_one, e0]; exact hnorm
  have h1 : RCle (RCscale rho (E 0)) (E 1) := by
    rw [e0]; exact h2
  intro n
  have h := rc_logconvex_geometric E rho q hrho hq h0
    (fun k => response_even_nonnegative hw0 hw1 width x k) hcs h1 n
  rw [e0] at h
  exact h

/-- Relative two-step floor => macroscopic ratio with kappa = rho^u. -/
theorem macro_ratio_of_twoStep_floor (x : V) (u : Nat) (rho q : Q')
    (hrho : (0 : Q') < rho) (hq : (0 : Q') < q)
    (hnorm : RCle (Quotient.mk crealSetoid (ofQ' q)) (B x x))
    (h2 : RCle (RCscale rho (B x x)) (B x (T 2 x))) :
    RCle (RCscale (rho^u) (B x (T (2*u) x))) (B x (T (4*u) x)) :=
  macro_ratio_of_survival_floor hw0 hw1 width x u (rho^u) q hq hnorm
    (response_even_jensen hw0 hw1 width x rho q hrho hq hnorm h2 u)

private theorem qpow_eqv_pow (y : Q') : ∀ n, (RGTransport.qpow y n).eqv (y^n)
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ y (qpow_eqv_pow y n))
      (Q'.mul_comm_eqv (y^n) y)

/-- BLOCK COMPILER. Relative two-step energy at most `t` (`(1-t)R(0) <= R(2)`),
`L*t` at most one half and `u = L*k` give `(1/2)^k * R(2u) <= R(4u)`. -/
theorem macro_ratio_of_block_energy (x : V) (u L k : Nat) (hu : u = L*k)
    (t q : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t < (1 : Q')) (hq : (0 : Q') < q)
    (hL : HalfPow.half ≤ (1 : Q') - Q'.ofNat L * t)
    (hnorm : RCle (Quotient.mk crealSetoid (ofQ' q)) (B x x))
    (h2 : RCle (RCscale ((1 : Q') - t) (B x x)) (B x (T 2 x))) :
    RCle (RCscale (HalfPow.half^k) (B x (T (2*u) x))) (B x (T (4*u) x)) := by
  have hrho : (0 : Q') < (1 : Q') - t := HKPos.one_sub_pos ht1
  have hbern := BondMovingRetuneFix.bernoulli_oneSub t ht0 (Q'.le_of_lt ht1) L
  have hblock : HalfPow.half ≤ ((1 : Q') - t)^L :=
    Q'.le_trans' _ _ _ hL (Q'.le_trans' _ _ _ hbern (Q'.le_of_eqv (qpow_eqv_pow _ L)))
  have hhalf : (0 : Q') ≤ HalfPow.half := by decide
  have hpow : HalfPow.half^k ≤ ((1 : Q') - t)^u := by
    rw [hu]
    exact Q'.le_trans' _ _ _
      (CRealLog.pow_le_pow_base _ _ hhalf hblock k)
      (Q'.le_of_eqv (FiveHolonomyPerronCutoff.pow_mul_eqv _ L k))
  have hj := response_even_jensen hw0 hw1 width x ((1 : Q') - t) q hrho hq hnorm h2 u
  have hfloor : RCle (RCscale (HalfPow.half^k) (B x x)) (B x (T (2*u) x)) :=
    RCle_trans (RCscale_mono_scalar hpow (completedInner_nonnegative hw0 hw1 x)) hj
  exact macro_ratio_of_survival_floor hw0 hw1 width x u (HalfPow.half^k) q hq hnorm hfloor

end Completed

#print axioms creal_scale_chain
#print axioms rc_scale_chain
#print axioms rc_logconvex_ratio_floor
#print axioms rc_logconvex_geometric
#print axioms response_even_jensen
#print axioms macro_ratio_of_twoStep_floor
#print axioms macro_ratio_of_block_energy

end YMGap.Continuum.BF4WilsonAllNomeEvenResponseJensen
