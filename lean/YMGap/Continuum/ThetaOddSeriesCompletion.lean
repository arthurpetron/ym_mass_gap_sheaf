/-
# Actual unbalanced odd theta series completions

The signed interval is not a balanced odd rectangle: its prefix is
2 H_N minus the actual last term. Both value and endpoint-frequency
prefixes retain their literal N-th approximants. Their explicit cutoff
is the existing shell cutoff at epsilon/4. The omitted last term tends
to zero, so each completion equals twice its separately constructed
one-sided series. No finite factor four or differentiation of a limit
is used. These are fixed-nome scalar joins, not physical estimates.
-/

import YMGap.Continuum.ThetaOddBoundaryPin
import YMGap.Continuum.ThetaOneSidedSeriesCompletion
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.ThetaOddSeriesCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.ThetaOddBoundaryPin
open YMGap.Continuum.ThetaOneSidedSeriesCompletion
open YMGap.Continuum.ThetaAlternatingMixedRectangle (oddTerm oddPartial)
open YMGap.Continuum.ThetaAlternatingEndpointRectangle (oddEndpointTerm oddEndpointJet)
open YMGap.Continuum.ThetaAngularShellTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Explicit Cauchy cutoff; uniform in the coordinate at each named nome. -/
def oddSignedCutoff (w epsilon : Q') : Nat :=
  oneSidedCutoff w (quarter*epsilon)

private theorem quarter_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < quarter*epsilon := Q'.mul_pos (by decide) he

private theorem shell_single_close {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (he : (0 : Q') < epsilon) (N : Nat)
    (hN : oneSidedCutoff w epsilon ≤ N) : shellTerm w N ≤ epsilon := by
  have h := shellTail_le_epsilon hw0 hw1 he N 1 hN
  change (0 : Q') + shellTerm w (N+0) ≤ epsilon at h
  simpa only [Nat.add_zero, Q'.zero_add'] using h

private theorem cutoff_positive {w epsilon : Q'} {N : Nat}
    (hN : oneSidedCutoff w epsilon ≤ N) : 1 ≤ N := by
  have h1 : 1 ≤ shellOnset w := Nat.le_max_left _ _
  unfold oneSidedCutoff shellTailCutoff at hN
  omega

/-- The actual odd value boundary vanishes with the original shell cutoff. -/
theorem odd_boundary_close {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (he : (0 : Q') < epsilon) (N : Nat)
    (hN : oneSidedCutoff w epsilon ≤ N) :
    Q'.abs (oddTerm w x N) ≤ epsilon :=
  Q'.le_trans' _ _ _ (oddTerm_shell_abs_le hw0 hw1 hx0 hx1 N (cutoff_positive hN))
    (shell_single_close hw0 hw1 he N hN)

/-- The actual squared-frequency boundary uses the SAME cutoff, not a
derivative inferred from the value completion. -/
theorem odd_endpoint_boundary_close {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (he : (0 : Q') < epsilon) (N : Nat)
    (hN : oneSidedCutoff w epsilon ≤ N) :
    Q'.abs (oddEndpointTerm w N) ≤ epsilon :=
  Q'.le_trans' _ _ _ (oddEndpointTerm_shell_abs_le hw0 hw1 N (cutoff_positive hN))
    (shell_single_close hw0 hw1 he N hN)

private theorem le_add_of_sub_le {a b e : Q'} (h : a + -b ≤ e) : a ≤ b+e := by
  have hsum := Q'.add_le_add_right _ _ b h
  have hleft : a ≈ (a + -b)+b :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (by decide) (fun | 0 => a | _ => b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.add_comm_eqv e b)))

private theorem boundary_cauchy_step (Sm Sn Pm Pn rm rn epsilon : Q')
    (hm : Sm ≈ 2*Pm + -rm) (hn : Sn ≈ 2*Pn + -rn)
    (hP : Pm ≤ Pn+quarter*epsilon)
    (hrm : Q'.abs rm ≤ quarter*epsilon) (hrn : Q'.abs rn ≤ quarter*epsilon) :
    Sm ≤ Sn+epsilon := by
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ 2 (Q'.sub_le_of_le_add hP) (by decide)
  have hr := Q'.add_le_add
    (Q'.le_trans' _ _ _ (Q'.neg_le_abs rm) hrm)
    (Q'.le_trans' _ _ _ (Q'.le_abs_self rn) hrn)
  have hbound := Q'.add_le_add hp hr
  have hpin : Sm + -Sn ≈ 2*(Pm + -Pn) + (-rm+rn) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hm (Q'.neg_eqv_congr _ _ hn))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.const 2) (.var 0)) (.neg (.var 2)))
          (.neg (.add (.mul (.const 2) (.var 1)) (.neg (.var 3)))))
        (.add (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
          (.add (.neg (.var 2)) (.var 3))) (by decide)
        (fun | 0 => Pm | 1 => Pn | 2 => rm | _ => rn))
  have hpay : 2*(quarter*epsilon)+(quarter*epsilon+quarter*epsilon) ≈ epsilon :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)))
        (.mul (.const 4) (.var 0)) (by decide) (fun _ => quarter*epsilon))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 4 quarter epsilon))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ epsilon
          (by decide : (4 : Q')*quarter ≈ 1)) (Q'.one_mul_eqv epsilon)))
  exact le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hpay)))

/-- Literal unbalanced value prefixes are Cauchy, with a named modulus. -/
theorem odd_signed_cauchy {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oddSignedCutoff w epsilon ≤ m) (hn : oddSignedCutoff w epsilon ≤ n) :
    oddSignedPrefix w x m ≤ oddSignedPrefix w x n+epsilon ∧
      oddSignedPrefix w x n ≤ oddSignedPrefix w x m+epsilon := by
  have hp := odd_cauchy hw0 hw1 hx0 hx1 (quarter*epsilon) (quarter_pos he) m n hm hn
  have hrm := odd_boundary_close hw0 hw1 hx0 hx1 (quarter_pos he) m hm
  have hrn := odd_boundary_close hw0 hw1 hx0 hx1 (quarter_pos he) n hn
  exact ⟨boundary_cauchy_step _ _ _ _ _ _ _
      (odd_signed_boundary_pin w x m) (odd_signed_boundary_pin w x n) hp.1 hrm hrn,
    boundary_cauchy_step _ _ _ _ _ _ _
      (odd_signed_boundary_pin w x n) (odd_signed_boundary_pin w x m) hp.2 hrn hrm⟩

/-- Literal endpoint-frequency prefixes are completed independently. -/
theorem odd_signed_endpoint_cauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oddSignedCutoff w epsilon ≤ m) (hn : oddSignedCutoff w epsilon ≤ n) :
    oddSignedEndpointPrefix w m ≤ oddSignedEndpointPrefix w n+epsilon ∧
      oddSignedEndpointPrefix w n ≤ oddSignedEndpointPrefix w m+epsilon := by
  have hp := oddEndpoint_cauchy hw0 hw1 (quarter*epsilon) (quarter_pos he) m n hm hn
  have hrm := odd_endpoint_boundary_close hw0 hw1 (quarter_pos he) m hm
  have hrn := odd_endpoint_boundary_close hw0 hw1 (quarter_pos he) n hn
  exact ⟨boundary_cauchy_step _ _ _ _ _ _ _
      (odd_signed_endpoint_boundary_pin w m) (odd_signed_endpoint_boundary_pin w n) hp.1 hrm hrn,
    boundary_cauchy_step _ _ _ _ _ _ _
      (odd_signed_endpoint_boundary_pin w n) (odd_signed_endpoint_boundary_pin w m) hp.2 hrn hrm⟩

def oddSignedCReal {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal where
  approx := oddSignedPrefix w x
  cauchy := fun epsilon he => ⟨oddSignedCutoff w epsilon,
    odd_signed_cauchy hw0 hw1 hx0 hx1 epsilon he⟩

def oddSignedEndpointCReal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : CReal where
  approx := oddSignedEndpointPrefix w
  cauchy := fun epsilon he => ⟨oddSignedCutoff w epsilon,
    odd_signed_endpoint_cauchy hw0 hw1 epsilon he⟩

@[simp] theorem oddSignedCReal_approx {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (oddSignedCReal hw0 hw1 hx0 hx1).approx N = oddSignedPrefix w x N := rfl

@[simp] theorem oddSignedEndpointCReal_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    (oddSignedEndpointCReal hw0 hw1).approx N = oddSignedEndpointPrefix w N := rfl

private theorem boundary_difference_pin (S P r : Q') (h : S ≈ 2*P + -r) :
    Q'.abs (S + -(2*P)) ≈ Q'.abs r :=
  Q'.eqv_trans _ _ _
    (TsumDeriv.Q'.abs_eqv_congr (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ h)
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.const 2) (.var 0)) (.neg (.var 1)))
          (.neg (.mul (.const 2) (.var 0))))
        (.neg (.var 1)) (by decide) (fun | 0 => P | _ => r))))
    (TsumDeriv.Q'.abs_neg r)

/-- Completed signed odd value equals twice the ORIGINAL one-sided H. -/
theorem oddSignedCReal_eq_twice {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (oddSignedCReal hw0 hw1 hx0 hx1)
      (CReal.mul (CReal.ofQ' 2) (oddCReal hw0 hw1 hx0 hx1)) := by
  apply CReal.Equiv_of_abs_sub_le_all_pos
  intro epsilon he
  apply CReal.leRat_of_eventually
  refine ⟨oneSidedCutoff w epsilon, fun N hN => ?_⟩
  change Q'.abs (oddSignedPrefix w x N + -(2*oddPartial w x N)) ≤ epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (boundary_difference_pin _ _ _ (odd_signed_boundary_pin w x N)))
    (odd_boundary_close hw0 hw1 hx0 hx1 he N hN)

/-- Separately completed signed odd endpoint jet equals twice H_endpoint. -/
theorem oddSignedEndpointCReal_eq_twice {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.Equiv (oddSignedEndpointCReal hw0 hw1)
      (CReal.mul (CReal.ofQ' 2) (oddEndpointCReal hw0 hw1)) := by
  apply CReal.Equiv_of_abs_sub_le_all_pos
  intro epsilon he
  apply CReal.leRat_of_eventually
  refine ⟨oneSidedCutoff w epsilon, fun N hN => ?_⟩
  change Q'.abs (oddSignedEndpointPrefix w N + -(2*oddEndpointJet w N)) ≤ epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (boundary_difference_pin _ _ _ (odd_signed_endpoint_boundary_pin w N)))
    (odd_endpoint_boundary_close hw0 hw1 he N hN)

end YMGap.Continuum.ThetaOddSeriesCompletion

#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.oddSignedCutoff
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.odd_boundary_close
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.odd_endpoint_boundary_close
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.odd_signed_cauchy
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.odd_signed_endpoint_cauchy
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.oddSignedCReal
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.oddSignedEndpointCReal
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.oddSignedCReal_approx
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.oddSignedEndpointCReal_approx
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.oddSignedCReal_eq_twice
#print axioms YMGap.Continuum.ThetaOddSeriesCompletion.oddSignedEndpointCReal_eq_twice
