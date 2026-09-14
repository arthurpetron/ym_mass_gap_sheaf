/-
# Symmetry, order and positivity of ORIGINAL continuous cyclic actions

Bernstein sampling stays in [0,1], including degree zero. Its nonnegative
weights preserve pointwise symbol order and positivity. The original
polynomial form order passes through represented pairing limits; likewise
polynomial symmetry gives symmetry of the constructed continuous action.

For a represented square symbol H=F*F, its quadratic form is exactly the
original squared norm of F(T2)x. The capped-cusp square supplies a closed
instance. These results use no spectral model or supplied form-order axiom.
They are fixed-nome/spacing cyclic results, not full-carrier identification
or a strictly positive physical mass gap or continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder
import YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum finSum_zero_seq)
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicFormOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication
open YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicCuspMultiplication

theorem finSum_le_on (f g : Nat → Q') : ∀ N,
    (∀ k,k<N → f k≤g k) → finSum f N≤finSum g N
  | 0,_ => Q'.le_refl' _
  | N+1,h => Q'.add_le_add (finSum_le_on f g N (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self N))))
      (h N (Nat.lt_succ_self N))

theorem finSum_nonnegative_on (f : Nat → Q') (N : Nat) (h : ∀ k,k<N → (0 : Q')≤f k) :
    (0 : Q')≤finSum f N := by
  have hs := finSum_le_on (fun _ => 0) f N h
  rw [finSum_zero_seq] at hs
  exact hs

theorem smp_nonnegative (n k : Nat) : (0 : Q')≤smp n k :=
  Q'.mul_nonneg _ _ (Q'.ofNat_nonneg k) (Q'.le_of_lt (Q'.recip_pos _))

theorem smp_le_one (n k : Nat) (hk : k≤n) : smp n k≤(1 : Q') := by
  cases n with
  | zero =>
      have h : k=0 := Nat.eq_zero_of_le_zero hk
      subst k
      decide
  | succ n =>
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hk) (Q'.le_of_lt (Q'.recip_pos _)))
        (Q'.le_of_eqv (Q'.mul_recip_eqv _ (Q'.ofNat_succ_pos n)))

theorem bernsteinPoly_mono (F G : CtsMod)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → F.f t≤G.f t)
    (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (bernsteinPoly F n) t≤QPoly.eval (bernsteinPoly G n) t := by
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_bernsteinPoly F n t))
  apply Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (eval_bernsteinPoly G n t))
  apply finSum_le_on
  intro k hk
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (h _ (smp_nonnegative n k) (smp_le_one n k (Nat.le_of_lt_succ hk))) (bmono_nonneg n t ht h1 k)

theorem bernsteinPoly_nonnegative (F : CtsMod)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤F.f t)
    (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    (0 : Q')≤QPoly.eval (bernsteinPoly F n) t := by
  apply Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (eval_bernsteinPoly F n t))
  apply finSum_nonnegative_on
  intro k hk
  exact Q'.mul_nonneg _ _ (h _ (smp_nonnegative n k) (smp_le_one n k (Nat.le_of_lt_succ hk)))
    (bmono_nonneg n t ht h1 k)

theorem symbolAction_symmetric (F : CtsMod) (V : MonotoneOmegaVanishing F) (X Y : CyclicPresentation) :
    completedInner (symbolAction F V X) (state Y)=completedInner (state X) (symbolAction F V Y) := by
  have h := rowLimit_pairing_eq (symbolRows F V X) (constantRows (diagonalCauchy Y.rows))
    (constantRows (diagonalCauchy X.rows)) (symbolRows F V Y) (by
      intro n
      rw [symbolRows_pin,symbolRows_pin,constantRows_pin,constantRows_pin]
      exact operator_symmetric _ _ _)
  rw [rowLimit_constant,rowLimit_constant] at h
  exact h

theorem symbolAction_form_mono (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G)
    (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → F.f t≤G.f t) (X : CyclicPresentation) :
    RCle (completedInner (symbolAction F V X) (state X))
      (completedInner (symbolAction G W X) (state X)) := by
  have h := rowLimit_pairing_le (symbolRows F V X) (constantRows (diagonalCauchy X.rows))
    (symbolRows G W X) (constantRows (diagonalCauchy X.rows)) (by
      intro n
      rw [symbolRows_pin,symbolRows_pin,constantRows_pin]
      exact polynomial_form_mono X _ _ (bernsteinPoly_mono F G hfg n))
  rw [rowLimit_constant] at h
  exact h

theorem symbolAction_form_nonnegative (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (hF : ∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤F.f t) (X : CyclicPresentation) :
    RCnonneg (completedInner (symbolAction F V X) (state X)) := by
  have h := rowLimit_pairing_nonnegative (symbolRows F V X) (constantRows (diagonalCauchy X.rows)) (by
    intro n
    rw [symbolRows_pin,constantRows_pin]
    exact polynomial_form_nonnegative X _ (bernsteinPoly_nonnegative F hF n))
  rw [rowLimit_constant] at h
  exact h

theorem square_form_identity (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (hH : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (H.f t) (F.f t*F.f t)) (X : CyclicPresentation) :
    completedInner (symbolAction H U X) (state X)=
      completedInner (symbolAction F V X) (symbolAction F V X) := by
  rw [symbolAction_mul F V F V H U hH X,symbolAction_symmetric,state_actionPresentation]

theorem cuspSquare_form_identity (X : CyclicPresentation) :
    completedInner (symbolAction cuspSquareSymbol cuspSquareVanishing X) (state X)=
      completedInner (symbolAction cuspSymbol cuspVanishing X) (symbolAction cuspSymbol cuspVanishing X) :=
  square_form_identity cuspSymbol cuspVanishing cuspSquareSymbol cuspSquareVanishing
    (fun t _ _ => Q'.eqv_refl (cuspSquare t)) X

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.finSum_le_on
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.finSum_nonnegative_on
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.smp_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.smp_le_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.bernsteinPoly_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.bernsteinPoly_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.symbolAction_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.symbolAction_form_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.symbolAction_form_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.square_form_identity
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousFormOrder.cuspSquare_form_identity
