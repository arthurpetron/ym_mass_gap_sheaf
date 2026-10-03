/-
# Constructive order of the ORIGINAL rational function

Finite signed numerator and denominator polynomials are evaluated literally.
The cleared FORMAL quotient derivative supplies each mesh cell's sign; two
computed Taylor budgets supply a quadratic error. A supplied positive
denominator floor is retained explicitly. Finite rational mesh closure gives
endpoint order of p/q itself, not order of a denominator-multiplied surrogate.
No analytic derivative, integration theorem, or endpoint order is assumed.
-/

import YMGap.Continuum.RationalPolynomialTaylorCell
import YMGap.Constructive.QPolyWeightedL1

namespace YMGap.Continuum.RationalFunctionIntervalOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Continuum.RationalPolynomialIntervalOrder
open YMGap.Continuum.RationalPolynomialTaylorCell
open YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann (invSucc_nonnegative)
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Total computable evaluation; on the positive-denominator domain this is
the literal ratio, as certified below. No inverse of the numerator is used. -/
def quotient (p q : Poly) (x : Q') : Q' := eval p x * Q'.recip (eval q x)

/-- Cleared literal formal quotient-rule numerator q*p' - p*q'. -/
def derivativeNumerator (p q : Poly) : Poly :=
  psub (pmul q (pderiv p)) (pmul p (pderiv q))

theorem derivativeNumerator_eval (p q : Poly) (x : Q') :
    eval (derivativeNumerator p q) x ≈
      eval q x * eval (pderiv p) x + -(eval p x * eval (pderiv q) x) :=
  Q'.eqv_trans _ _ _ (eval_psub _ _ x)
    (Q'.add_eqv_congr' (eval_pmul q (pderiv p) x)
      (Q'.neg_eqv_congr _ _ (eval_pmul p (pderiv q) x)))

theorem quotient_denominator_pin (p q : Poly) (x : Q')
    (hq : (0 : Q') < eval q x) : quotient p q x * eval q x ≈ eval p x := by
  unfold quotient
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recip_eqv _ hq)))
      (Q'.mul_one_eqv _))

/-- Actual coefficient and Taylor budgets of BOTH polynomials. -/
def cellBudget (p q : Poly) : Q' :=
  weightedL1 1 q * taylorCellBudget p + weightedL1 1 p * taylorCellBudget q

theorem cellBudget_nonnegative (p q : Poly) : (0 : Q') ≤ cellBudget p q :=
  Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (weightedL1_nonnegative 1 Q'.zero_le_one q) (taylorCellBudget_nonnegative p))
    (Q'.mul_nonneg _ _ (weightedL1_nonnegative 1 Q'.zero_le_one p) (taylorCellBudget_nonnegative q))

/-- Computed quotient error constant. Its denominator floor is visible data. -/
def cellConstant (p q : Poly) (d : Q') : Q' := cellBudget p q * Q'.recip (d*d)

theorem cellConstant_nonnegative (p q : Poly) (d : Q') : (0 : Q') ≤ cellConstant p q d :=
  Q'.mul_nonneg _ _ (cellBudget_nonnegative p q) (Q'.le_of_lt (Q'.recip_pos _))

private theorem cellConstant_pin (p q : Poly) (d : Q') (hd : (0 : Q') < d) :
    cellConstant p q d * (d*d) ≈ cellBudget p q := by
  unfold cellConstant
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recip_eqv _ (Q'.mul_pos hd hd))))
      (Q'.mul_one_eqv _))

private theorem le_add_of_sub_le {p q ε : Q'} (h : q + -p ≤ ε) : q ≤ p + ε := by
  have hs := Q'.add_le_add_right _ _ p h
  have he : ((q + -p) + p) ≈ q := poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
    (fun | 0 => q | _ => p)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.add_comm_eqv ε p)))

private theorem eval_cap (p : Poly) (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Q'.abs (eval p x) ≤ weightedL1 1 p :=
  abs_eval_le_weightedL1 Q'.zero_le_one (by simpa only [ExpNeg.abs_of_nonneg hx] using hx1) p

private def cellIdentityL : PolyExpr :=
  .add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))

private def cellIdentityR : PolyExpr :=
  .add
    (.mul (.var 4) (.add (.mul (.var 0) (.var 5)) (.neg (.mul (.var 2) (.var 6)))))
    (.add
      (.mul (.var 0) (.add (.add (.var 3) (.neg (.var 2))) (.neg (.mul (.var 4) (.var 5)))))
      (.neg (.mul (.var 2) (.add (.add (.var 1) (.neg (.var 0))) (.neg (.mul (.var 4) (.var 6)))))))

private theorem cell_identity (dx dy px py δ dp dq : Q') :
    dx*py + -(dy*px) ≈
      δ*(dx*dp + -(px*dq)) +
        (dx*((py + -px) + -(δ*dp)) + -(px*((dy + -dx) + -(δ*dq)))) := by
  have h := poly_identity_of_normal_eq cellIdentityL cellIdentityR (by decide)
    (fun | 0 => dx | 1 => dy | 2 => px | 3 => py | 4 => δ | 5 => dp | _ => dq)
  simpa only [cellIdentityL, cellIdentityR, RingNormaliser.eval] using h

/-- A signed original quotient cell is increasing up to its explicit
quadratic error. The hypothesis is a derivative sign, never endpoint order. -/
theorem quotient_cell_le (p q : Poly) (x y d : Q')
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) (hy : y ≤ (1 : Q'))
    (hd : (0 : Q') < d) (hdx : d ≤ eval q x) (hdy : d ≤ eval q y)
    (hder : (0 : Q') ≤ eval (derivativeNumerator p q) x) :
    quotient p q x ≤ quotient p q y + ((y + -x)*(y + -x))*cellConstant p q d := by
  let δ := y + -x
  let dx := eval q x
  let dy := eval q y
  let px := eval p x
  let py := eval p y
  let Rp := (py + -px) + -(δ * eval (pderiv p) x)
  let Rq := (dy + -dx) + -(δ * eval (pderiv q) x)
  let R := dx*Rp + -(px*Rq)
  let I := dx*py + -(dy*px)
  let M := δ*(dx*eval (pderiv p) x + -(px*eval (pderiv q) x))
  have hδ : (0 : Q') ≤ δ := Q'.sub_nonneg_of_le hxy
  have hδ2 : (0 : Q') ≤ δ*δ := Q'.mul_nonneg _ _ hδ hδ
  have hx1 : x ≤ (1 : Q') := Q'.le_trans' _ _ _ hxy hy
  have hdxpos : (0 : Q') < dx := HeatKernelRGStep.lt_of_lt_of_le hd hdx
  have hdypos : (0 : Q') < dy := HeatKernelRGStep.lt_of_lt_of_le hd hdy
  have hM : (0 : Q') ≤ M := Q'.mul_nonneg _ _ hδ
    (Q'.le_trans' _ _ _ hder (Q'.le_of_eqv (derivativeNumerator_eval p q x)))
  have hI : I ≈ M + R := cell_identity dx dy px py δ (eval (pderiv p) x) (eval (pderiv q) x)
  have hRp := polynomial_taylor_cell_error p x y hx hxy hy
  have hRq := polynomial_taylor_cell_error q x y hx hxy hy
  have hRcap : Q'.abs R ≤ (δ*δ)*cellBudget p q := by
    have hp : Q'.abs (dx*Rp) ≤ weightedL1 1 q * ((δ*δ)*taylorCellBudget p) :=
      Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ (eval_cap q x hx hx1) (Q'.abs_nonneg Rp))
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hRp (weightedL1_nonnegative 1 Q'.zero_le_one q)))
    have hq : Q'.abs (-(px*Rq)) ≤ weightedL1 1 p * ((δ*δ)*taylorCellBudget q) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right _ _ _ (eval_cap p x hx hx1) (Q'.abs_nonneg Rq))
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hRq (weightedL1_nonnegative 1 Q'.zero_le_one p))))
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hp hq) (Q'.le_of_eqv ?_)
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 2) (.var 3))) (.mul (.var 1) (.mul (.var 2) (.var 4))))
      (.mul (.var 2) (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4)))) (by decide)
      (fun | 0 => weightedL1 1 q | 1 => weightedL1 1 p | 2 => δ*δ
           | 3 => taylorCellBudget p | _ => taylorCellBudget q)
  have hnegI : -I ≤ (δ*δ)*cellBudget p q := by
    have hh : -M + -R ≤ Q'.abs R := Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.neg_le_neg hM) (Q'.neg_le_abs R))
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hI) (Q'.neg_add_eqv M R)))
      (Q'.le_trans' _ _ _ hh hRcap)
  have hden : d*d ≤ dx*dy := Q'.mul_le_mul_of_nonneg hdx hdy
    (Q'.le_of_lt hdxpos) (Q'.le_of_lt hd)
  have hB : cellBudget p q ≤ cellConstant p q d * (dx*dy) := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (cellConstant_pin p q d hd))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hden (cellConstant_nonnegative p q d))
  have hQx : (dx*dy)*quotient p q x ≈ dy*px := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
      (fun | 0 => dx | 1 => dy | _ => quotient p q x))
    (Q'.mul_eqv_congr_left dy _ _ (quotient_denominator_pin p q x hdxpos))
  have hQy : (dx*dy)*quotient p q y ≈ dx*py := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
      (fun | 0 => dx | 1 => dy | _ => quotient p q y))
    (Q'.mul_eqv_congr_left dx _ _ (quotient_denominator_pin p q y hdypos))
  have hdiff : (dx*dy)*(quotient p q x + -quotient p q y) ≈ -I :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hQx
        (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv _ _) (Q'.neg_eqv_congr _ _ hQy)))
        (poly_identity_of_normal_eq (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
          (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))
          (by decide) (fun | 0 => dx | 1 => dy | 2 => px | _ => py)))
  have hc : (dx*dy)*(quotient p q x + -quotient p q y) ≤
      (dx*dy)*((δ*δ)*cellConstant p q d) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdiff) ?_
    refine Q'.le_trans' _ _ _ hnegI ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hB hδ2) (Q'.le_of_eqv ?_)
    exact poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => δ*δ | 1 => cellConstant p q d | _ => dx*dy)
  exact le_add_of_sub_le (Q'.le_of_mul_le_mul_left hc (Q'.mul_pos hdxpos hdypos))

private theorem quotient_congr_argument (p q : Poly) {x y : Q'} (h : x ≈ y)
    (hx : (0 : Q') < eval q x) (hy : (0 : Q') < eval q y) : quotient p q x ≈ quotient p q y := by
  have hev : ∀ r : Poly, eval r x ≈ eval r y := by
    intro r
    induction r with
    | nil => exact Q'.eqv_refl _
    | cons c cs ih =>
        exact Q'.add_eqv_congr_left c _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ ih))
  have heq : eval q x ≈ eval q y := hev q
  have hp : eval p x ≈ eval p y := hev p
  have hxpin := quotient_denominator_pin p q x hx
  have hypin := quotient_denominator_pin p q y hy
  have hscaled : quotient p q x * eval q x ≈ quotient p q y * eval q x :=
    Q'.eqv_trans _ _ _ hxpin (Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hypin)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm heq))))
  apply Int.le_antisymm
  · apply Q'.le_of_mul_le_mul_left _ hx
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled) (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  · apply Q'.le_of_mul_le_mul_left _ hx
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hscaled) (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

/-- Genuine endpoint order of p/q from its cleared FORMAL derivative sign.
The positive floor is explicit; numerator sign and endpoint order are absent. -/
theorem quotient_monotone (p q : Poly) (a b d : Q')
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hb : b ≤ (1 : Q')) (hd : (0 : Q') < d)
    (hq : ∀ x : Q', a ≤ x → x ≤ b → d ≤ eval q x)
    (hder : ∀ x : Q', a ≤ x → x ≤ b → (0 : Q') ≤ eval (derivativeNumerator p q) x) :
    quotient p q a ≤ quotient p q b := by
  let C := cellConstant p q d
  let B := C.num.toNat
  have hC : C ≤ Q'.ofNat B := RatNat.le_ofNat_toNat _ (cellConstant_nonnegative p q d)
  apply Q'.le_of_le_add_mul_invSucc _ _ B
  intro N
  let x := intervalNode a b N
  let δ := intervalMesh a b N
  have hx : ∀ j, j ≤ N+1 → a ≤ x j ∧ x j ≤ b := fun j hj => node_in_interval hab N j hj
  have hδ : (0 : Q') ≤ δ := mesh_nonnegative hab N
  have hcell : ∀ j, j < N+1 →
      quotient p q (x j) ≤ quotient p q (x (j+1)) + (δ*δ)*C := by
    intro j hj
    have hjn := Nat.le_of_lt hj
    have hj1 : j+1 ≤ N+1 := hj
    have hs := quotient_cell_le p q (x j) (x (j+1)) d
      (Q'.le_trans' _ _ _ ha (hx j hjn).1) (node_mono hab N (Nat.le_succ j))
      (Q'.le_trans' _ _ _ (hx (j+1) hj1).2 hb) hd
      (hq _ (hx j hjn).1 (hx j hjn).2) (hq _ (hx (j+1) hj1).1 (hx (j+1) hj1).2)
      (hder _ (hx j hjn).1 (hx j hjn).2)
    refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ ?_))
    exact Q'.mul_eqv_congr_right _ _ C (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (node_step a b N j))
      (Q'.mul_eqv_congr_left δ _ _ (node_step a b N j)))
  have ht : ∀ j, j ≤ N+1 → quotient p q (x 0) ≤
      quotient p q (x j) + Q'.ofNat j * ((δ*δ)*C) := by
    intro j
    induction j with
    | zero => intro _; exact Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) (Q'.eqv_of_eq (Q'.add_zero' _))))
    | succ j ih =>
        intro hj
        have ih' := ih (Nat.le_trans (Nat.le_succ j) hj)
        have hs := hcell j hj
        refine Q'.le_trans' _ _ _ ih' ?_
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hs) (Q'.le_of_eqv ?_)
        refine Q'.eqv_trans _
          (quotient p q (x (j+1)) + (Q'.ofNat j+1)*((δ*δ)*C)) _ ?_ ?_
        · exact poly_identity_of_normal_eq
            (.add (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 1)))
            (.add (.var 0) (.mul (.add (.var 2) (.const 1)) (.var 1))) (by decide)
            (fun | 0 => quotient p q (x (j+1)) | 1 => (δ*δ)*C | _ => Q'.ofNat j)
        · exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (Q'.ofNat_add_eqv j 1)))
  have hcount : Q'.ofNat (N+1)*δ ≈ b + -a := by
    change Q'.ofNat (N+1)*((b + -a)*Q'.invSucc N) ≈ b + -a
    refine Q'.eqv_trans _ ((Q'.ofNat (N+1)*Q'.invSucc N)*(b + -a)) _ ?_ ?_
    · exact poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => Q'.ofNat (N+1) | 1 => b + -a | _ => Q'.invSucc N)
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_succ_mul_invSucc N)) (Q'.one_mul_eqv _)
  have hwidth : b + -a ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add hb (Q'.neg_le_neg ha)) (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))
  have herr : Q'.ofNat (N+1)*((δ*δ)*C) ≤ Q'.ofNat B * Q'.invSucc N := by
    have he : Q'.ofNat (N+1)*((δ*δ)*C) ≈ (b + -a)*(δ*C) :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 2))) (by decide)
          (fun | 0 => Q'.ofNat (N+1) | 1 => δ | _ => C))
        (Q'.mul_eqv_congr_right _ _ _ hcount)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
    refine Q'.le_trans' _ (δ*C) _ ?_ ?_
    · exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hwidth
        (Q'.mul_nonneg _ _ hδ (cellConstant_nonnegative p q d))) (Q'.le_of_eqv (Q'.one_mul_eqv _))
    · exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (mesh_le_inverse ha hb N) (cellConstant_nonnegative p q d))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hC (invSucc_nonnegative N))
          (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  have hp0 : quotient p q (x 0) ≈ quotient p q a := quotient_congr_argument p q (node_zero a b N)
    (HeatKernelRGStep.lt_of_lt_of_le hd (hq _ (hx 0 (Nat.zero_le _)).1 (hx 0 (Nat.zero_le _)).2))
    (HeatKernelRGStep.lt_of_lt_of_le hd (hq a (Q'.le_refl' _) hab))
  have hp1 : quotient p q (x (N+1)) ≈ quotient p q b := quotient_congr_argument p q (node_endpoint a b N)
    (HeatKernelRGStep.lt_of_lt_of_le hd (hq _ (hx (N+1) (Nat.le_refl _)).1 (hx (N+1) (Nat.le_refl _)).2))
    (HeatKernelRGStep.lt_of_lt_of_le hd (hq b hab (Q'.le_refl' _)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp0)
    (Q'.le_trans' _ _ _ (ht (N+1) (Nat.le_refl _))
      (Q'.add_le_add (Q'.le_of_eqv hp1) herr))

end YMGap.Continuum.RationalFunctionIntervalOrder

#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.quotient
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.derivativeNumerator
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.derivativeNumerator_eval
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.quotient_denominator_pin
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.cellBudget
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.cellBudget_nonnegative
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.cellConstant
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.cellConstant_nonnegative
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.quotient_cell_le
#print axioms YMGap.Continuum.RationalFunctionIntervalOrder.quotient_monotone
