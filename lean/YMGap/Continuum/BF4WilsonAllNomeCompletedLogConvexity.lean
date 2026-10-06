/-
# Completed Cauchy--Schwarz, response log-convexity and the survival compiler

On the SAME literal-width all-nome completion, the existing intrinsic-form
Cauchy--Schwarz passes through the actual pairing limits. With time balance it
gives log-convexity of the response `R(n) = B x (T n x)` on the even grid:
`R(m+n)^2 <= R(2m) R(2n)`, in particular `R(2u)^2 <= R(0) R(4u)`.

Consequently ONE survival floor `kappa*R(0) <= R(2u)` with a positive rational
norm floor already yields the macroscopic ratio `kappa*R(2u) <= R(4u)`. For
the literal norm-one dyadic unit excitation this is exactly the `hratio`
input of `BF4WilsonAllNomeDyadicNormalizedMacroRatio`. This is the A03
direct-response alternative; it replaces no hypothesis by a weaker one and
supplies no survival floor, changing family, scaling or continuum claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz
import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation

namespace YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap (completedInner_even_diagonal)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
  (dyadicUnitExcitation dyadicUnitResponse dyadicUnitResponse_pin dyadicUnitExcitation_norm)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.TuranPositivity (PosEv)

/-! ## Scalar ratio step (no division; only a positive rational floor is cancelled) -/

/-- `kappa*a <= b`, `b >= 0`, `b^2 <= a*c` and an explicit positive rational
floor `s*p <= a` give `kappa*b <= c`. The sign of `kappa` is not used. -/
theorem creal_ratio_step (a b c : CReal) (kappa s p : Q')
    (hs : (0 : Q') < s) (hp : (0 : Q') < p)
    (ha : leEv (mul (ofQ' s) (ofQ' p)) a) (hb : leEv czero b)
    (hcs : leEv (mul b b) (mul a c)) (hf : leEv (mul (ofQ' kappa) a) b) :
    leEv (mul (ofQ' kappa) b) c := by
  have hpos : PosEv a := ⟨s*p, Q'.mul_pos hs hp,
    leEv_trans (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))) ha⟩
  have h1 := leEv_trans (leEv_mul_nonneg_left hb hf) hcs
  have el : Equiv (mul (mul (ofQ' kappa) b) a) (mul b (mul (ofQ' kappa) a)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => kappa | 1 => b.approx n | _ => a.approx n))
  have er : Equiv (mul a c) (mul c a) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0))
        (by decide) (fun | 0 => a.approx n | _ => c.approx n))
  exact leEv_cancel_mul_right_posEv hpos
    (leEv_trans (leEv_of_equiv el) (leEv_trans h1 (leEv_of_equiv er)))

/-- Quotient form of `creal_ratio_step`. -/
theorem rc_ratio_step (a b c : RC) (kappa s p : Q')
    (hs : (0 : Q') < s) (hp : (0 : Q') < p)
    (ha : RCle (RCscale s (Quotient.mk crealSetoid (ofQ' p))) a) (hb : RCnonneg b)
    (hcs : RCle (RCmul b b) (RCmul a c)) (hf : RCle (RCscale kappa a) b) :
    RCle (RCscale kappa b) c := by
  revert ha hb hcs hf
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C ha hb hcs hf
  exact creal_ratio_step A B' C kappa s p hs hp ha hb hcs hf

section Completed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Cauchy--Schwarz for actual representative pairings, by passing the
intrinsic-form inequality through the three pairing limits. -/
theorem representativeInner_cauchySchwarz (X Y : (D).Cauchy) :
    leEv (mul (CRealSeminormPairingCompletion.representativeInner PD X Y)
              (CRealSeminormPairingCompletion.representativeInner PD X Y))
      (mul (CRealSeminormPairingCompletion.representativeInner PD X X)
           (CRealSeminormPairingCompletion.representativeInner PD Y Y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CRealSeminormPairingCompletion.pairSequence_converges PD X Y)
      (CRealSeminormPairingCompletion.pairSequence_converges PD X Y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CRealSeminormPairingCompletion.pairSequence_converges PD X X)
      (CRealSeminormPairingCompletion.pairSequence_converges PD Y Y))
    (fun n => BF4WilsonAllNomeCauchySchwarz.intrinsicForm_cauchySchwarz hw0 hw1
      (X.seq n) (Y.seq n))

/-- Cauchy--Schwarz on the SAME all-nome completion. -/
theorem completedInner_cauchySchwarz (x y : V) :
    RCle (RCmul (B x y) (B x y)) (RCmul (B x x) (B y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeInner_cauchySchwarz hw0 hw1 width

/-- Even-grid log-convexity of the actual response: `R(m+n)^2 <= R(2m)R(2n)`. -/
theorem response_log_convex (x : V) (m n : Nat) :
    RCle (RCmul (B x (T (m+n) x)) (B x (T (m+n) x)))
      (RCmul (B x (T (2*m) x)) (B x (T (2*n) x))) := by
  have h := completedInner_cauchySchwarz hw0 hw1 width (T m x) (T n x)
  rw [completedInner_time_sum, completedInner_time_sum, completedInner_time_sum,
    ← Nat.two_mul, ← Nat.two_mul] at h
  exact h

/-- `R(2u)^2 <= R(0) R(4u)`. -/
theorem response_square_le_zero_mul_four (x : V) (u : Nat) :
    RCle (RCmul (B x (T (2*u) x)) (B x (T (2*u) x)))
      (RCmul (B x x) (B x (T (4*u) x))) := by
  have h := response_log_convex hw0 hw1 width x 0 (2*u)
  rw [Nat.zero_add, Nat.mul_zero, completedTime_zero,
    show 2*(2*u) = 4*u by omega] at h
  exact h

/-- Every even response is a squared norm, hence nonnegative. -/
theorem response_even_nonnegative (x : V) (n : Nat) :
    RCnonneg (B x (T (2*n) x)) := by
  rw [completedInner_even_diagonal hw0 hw1 width n x]
  exact completedInner_nonnegative hw0 hw1 (T n x)

/-- SURVIVAL-FLOOR COMPILER. A positive rational norm floor `q <= R(0)` and
one survival floor `kappa*R(0) <= R(2u)` give the macroscopic ratio
`kappa*R(2u) <= R(4u)`. No window budget, signed cost or nome window is used. -/
theorem macro_ratio_of_survival_floor (x : V) (u : Nat) (kappa q : Q')
    (hq : (0 : Q') < q)
    (hnorm : RCle (Quotient.mk crealSetoid (ofQ' q)) (B x x))
    (hfloor : RCle (RCscale kappa (B x x)) (B x (T (2*u) x))) :
    RCle (RCscale kappa (B x (T (2*u) x))) (B x (T (4*u) x)) := by
  have hnorm1 : RCle (RCscale 1 (Quotient.mk crealSetoid (ofQ' q))) (B x x) := by
    rw [RCscale_one]; exact hnorm
  exact rc_ratio_step _ _ _ kappa 1 q (by decide) hq hnorm1
    (response_even_nonnegative hw0 hw1 width x u)
    (response_square_le_zero_mul_four hw0 hw1 width x u) hfloor

/-- The literal norm-one dyadic unit excitation: a survival floor
`kappa <= R(side)` at even side gives EXACTLY the `hratio` input consumed by
`BF4WilsonAllNomeDyadicNormalizedMacroRatio.normalizedAnchorResponse_block_floor`. -/
theorem dyadic_macro_ratio_of_survival_floor (scale : Nat) (hwidth : side scale < width)
    (u : Nat) (hs : side scale = 2*u) (kappa : Q')
    (hfloor : leEv (ofQ' kappa) (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale))) :
    leEv (mul (ofQ' kappa) (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale)) := by
  let x := (dyadicUnitExcitation hw0 hw1 scale width hwidth).val
  have hn := dyadicUnitExcitation_norm hw0 hw1 scale width hwidth
  have hnorm : RCle (Quotient.mk crealSetoid (ofQ' 1)) (B x x) := by
    change RCle _ (B x x)
    rw [show B x x = Quotient.mk crealSetoid (ofQ' 1) from hn]
    exact RCle_refl _
  have hfl : RCle (RCscale kappa (B x x)) (B x (T (2*u) x)) := by
    rw [show B x x = Quotient.mk crealSetoid (ofQ' 1) from hn, ← hs,
      dyadicUnitResponse_pin, RCscale_mk]
    have e : Equiv (mul (ofQ' kappa) (ofQ' 1)) (ofQ' kappa) :=
      SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv kappa)
    exact leEv_trans (leEv_of_equiv e) hfloor
  have h := macro_ratio_of_survival_floor hw0 hw1 width x u kappa 1 (by decide) hnorm hfl
  rw [dyadicUnitResponse_pin, show 4*u = 2*side scale by omega,
    dyadicUnitResponse_pin, ← hs, RCscale_mk] at h
  exact h

end Completed

#print axioms creal_ratio_step
#print axioms rc_ratio_step
#print axioms representativeInner_cauchySchwarz
#print axioms completedInner_cauchySchwarz
#print axioms response_log_convex
#print axioms response_square_le_zero_mul_four
#print axioms response_even_nonnegative
#print axioms macro_ratio_of_survival_floor
#print axioms dyadic_macro_ratio_of_survival_floor

end YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
