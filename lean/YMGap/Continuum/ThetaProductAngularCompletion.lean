/-
# The SAME finite product angular jets as a constructive real

The N-th approximation remains the actual productAngularJet w x N.
Its checked comparison to the literal bare angular prefix and that
prefix's checked Cauchy modulus construct a coordinate-uniform cutoff
at each fixed nome. Two approximation errors and one prefix error each
pay epsilon/3. The actual product completion is then Equiv to the
separately constructed bare angular completion, using derivativeCutoff.

No finite Euler product is identified with a finite bare prefix. No
value limit is differentiated, and no angular pin is supplied as an
analytic hypothesis. The actual numerator/radial-cost consumer is separate;
no completed addition, curvature ceiling or original-action bound is claimed.
-/

import YMGap.Continuum.ThetaBareAngularCompletion
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealLe

namespace YMGap.Continuum.ThetaProductAngularCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteJacobiAngularComparison
  (productAngularJet angularSum productAngularJet_sub_bare_close)
open YMGap.Continuum.FiniteJacobiDerivativeComparison (derivativeCutoff)
open YMGap.Continuum.ThetaOneSidedSeriesCompletion (oneSidedCutoff)
open YMGap.Continuum.ThetaBareAngularCompletion (bareAngular_cauchy bareAngularCReal)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private def third : Q' := Q'.mkPos 1 3 (by decide)

private theorem third_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < third*epsilon := Q'.mul_pos (by decide) he

/-- Named cutoff for the actual product jet: two finite comparison errors
and one original bare-prefix error, with the same epsilon/3 budget. -/
def productAngularCutoff (w epsilon : Q') : Nat :=
  max (derivativeCutoff w (third*epsilon)) (oneSidedCutoff w (third*epsilon))

/-- Named SAME-index equivalence cutoff, with no extra tolerance rescaling. -/
def productAngularEquivCutoff (w epsilon : Q') : Nat := derivativeCutoff w epsilon

private theorem le_add_of_sub_le {a b e : Q'} (h : a + -b ≤ e) : a ≤ b+e := by
  have hsum := Q'.add_le_add_right _ _ b h
  have hleft : a ≈ (a + -b)+b :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (by decide) (fun
        | 0 => a
        | _ => b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.add_comm_eqv e b)))

private theorem comparison_cauchy_step (Pm Pn Bm Bn epsilon : Q')
    (hm : Q'.abs (Pm + -Bm) ≤ third*epsilon)
    (hn : Q'.abs (Pn + -Bn) ≤ third*epsilon)
    (hB : Bm ≤ Bn+third*epsilon) : Pm ≤ Pn+epsilon := by
  have hbound := Q'.add_le_add
    (Q'.add_le_add (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hm)
      (Q'.sub_le_of_le_add hB))
    (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) hn)
  have hpin : Pm + -Pn ≈ ((Pm + -Bm)+(Bm + -Bn)) + -(Pn + -Bn) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.add
        (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 2) (.neg (.var 3))))
        (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun
        | 0 => Pm
        | 1 => Pn
        | 2 => Bm
        | _ => Bn)
  have hpay : (third*epsilon+third*epsilon)+third*epsilon ≈ epsilon :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0)) (.var 0))
        (.mul (.const 3) (.var 0)) (by decide) (fun _ => third*epsilon))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 3 third epsilon))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ epsilon
          (by decide : (3 : Q')*third ≈ 1)) (Q'.one_mul_eqv epsilon)))
  exact le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hpay)))

/-- Actual product angular approximants are Cauchy at the named cutoff,
uniformly in x on the entire scalar interval for each fixed 0<w<1. -/
theorem productAngular_cauchy {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : productAngularCutoff w epsilon ≤ m) (hn : productAngularCutoff w epsilon ≤ n) :
    productAngularJet w x m ≤ productAngularJet w x n+epsilon ∧
      productAngularJet w x n ≤ productAngularJet w x m+epsilon := by
  have hmD : derivativeCutoff w (third*epsilon) ≤ m :=
    Nat.le_trans (Nat.le_max_left _ _) hm
  have hnD : derivativeCutoff w (third*epsilon) ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hmB : oneSidedCutoff w (third*epsilon) ≤ m :=
    Nat.le_trans (Nat.le_max_right _ _) hm
  have hnB : oneSidedCutoff w (third*epsilon) ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hb := bareAngular_cauchy hw0 hw1 hx0 hx1
    (third*epsilon) (third_pos he) m n hmB hnB
  have hem := productAngularJet_sub_bare_close hw0 hw1 hx1 hx0 (third_pos he) m hmD
  have hen := productAngularJet_sub_bare_close hw0 hw1 hx1 hx0 (third_pos he) n hnD
  exact ⟨comparison_cauchy_step _ _ _ _ _ hem hen hb.1,
    comparison_cauchy_step _ _ _ _ _ hen hem hb.2⟩

/-- Direct completion of the actual original product angular jet sequence. -/
def productAngularCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal where
  approx := productAngularJet w x
  cauchy := fun epsilon he => ⟨productAngularCutoff w epsilon,
    productAngular_cauchy hw0 hw1 hx0 hx1 epsilon he⟩

@[simp] theorem productAngularCReal_approx {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (productAngularCReal hw0 hw1 hx0 hx1).approx N = productAngularJet w x N := rfl

/-- The named finite-comparison cutoff pays the actual SAME-index completed
angular difference. It is independent of x at each fixed nome. -/
theorem productAngularCReal_equiv_close {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (he : (0 : Q') < epsilon) (N : Nat) (hN : productAngularEquivCutoff w epsilon ≤ N) :
    Q'.abs ((productAngularCReal hw0 hw1 hx0 hx1).approx N +
      -(bareAngularCReal hw0 hw1 hx0 hx1).approx N) ≤ epsilon :=
  productAngularJet_sub_bare_close hw0 hw1 hx1 hx0 he N hN

/-- The actual product angular completion equals the separately constructed
bare angular completion. This uses finite comparison, not limit differentiation. -/
theorem productAngularCReal_eq_bare {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (productAngularCReal hw0 hw1 hx0 hx1)
      (bareAngularCReal hw0 hw1 hx0 hx1) := by
  apply CReal.Equiv_of_abs_sub_le_all_pos
  intro epsilon he
  apply CReal.leRat_of_eventually
  refine ⟨productAngularEquivCutoff w epsilon, fun N hN => ?_⟩
  exact productAngularCReal_equiv_close hw0 hw1 hx0 hx1 he N hN

end YMGap.Continuum.ThetaProductAngularCompletion

#print axioms YMGap.Continuum.ThetaProductAngularCompletion.productAngularCutoff
#print axioms YMGap.Continuum.ThetaProductAngularCompletion.productAngularEquivCutoff
#print axioms YMGap.Continuum.ThetaProductAngularCompletion.productAngular_cauchy
#print axioms YMGap.Continuum.ThetaProductAngularCompletion.productAngularCReal
#print axioms YMGap.Continuum.ThetaProductAngularCompletion.productAngularCReal_approx
#print axioms YMGap.Continuum.ThetaProductAngularCompletion.productAngularCReal_equiv_close
#print axioms YMGap.Continuum.ThetaProductAngularCompletion.productAngularCReal_eq_bare
