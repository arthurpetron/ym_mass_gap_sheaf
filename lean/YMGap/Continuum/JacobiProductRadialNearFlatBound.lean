/-
# A finite positive-hemisphere Jacobi product radial ceiling

An exact rational potential telescopes the literal logarithmic-factor
increments. On 0 <= x <= 1 this gives (1-w*w)*D_N <= 2-w*w, including
the empty prefix. No limit, density inverse, heat substitution, Haar
promotion or source-weighted concentration estimate is used.
-/

import YMGap.Continuum.JacobiProductRadialSignedTail
import YMGap.Continuum.JacobiHeatNearFlatLogHessian

namespace YMGap.Continuum.JacobiProductRadialNearFlatBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation (productRadialCost)
open YMGap.Continuum.JacobiProductRadialSignedTail (radialSummand radialSummand_sum_pin)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ g)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ g)

private theorem nonneg_of_eqv {a b : Q'} (h : a ≈ b) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a := Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv h)

private theorem eval_congr (p : PolyExpr) (f g : Nat → Q')
    (h : ∀ i, f i ≈ g i) : eval f p ≈ eval g p := by
  induction p with
  | const c => exact Q'.eqv_refl _
  | var i => exact h i
  | add p q hp hq => exact add_congr hp hq
  | mul p q hp hq => exact mul_congr hp hq
  | neg p hp => exact Q'.neg_eqv_congr _ _ hp
  | pow p n hp => exact qpow_eqv_congr hp n

/-- The actual rational finite-difference potential, not a supplied bound. -/
def radialPotential (c x : Q') : Q' :=
  HKConv.divPos ((c+c)*(c+x)) (HKPos.factor c x)

private theorem potential_pin {c x : Q'} (hc0 : (0 : Q') ≤ c)
    (hc1 : c < (1 : Q')) (hx0 : (0 : Q') ≤ x) :
    radialPotential c x*HKPos.factor c x ≈ (c+c)*(c+x) :=
  HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (HKPos.factor_pos hc0 hc1
    (Q'.le_trans' _ _ _ (by decide) hx0)))

theorem radialPotential_nonnegative {c x : Q'}
    (hc0 : (0 : Q') ≤ c) (hx0 : (0 : Q') ≤ x) :
    (0 : Q') ≤ radialPotential c x :=
  HKConv.divPos_nonneg (Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ hc0 hc0) (Q'.zero_le_add _ _ hc0 hx0))

theorem radialPotential_le_one {c x : Q'} (hc0 : (0 : Q') ≤ c)
    (hc1 : c < (1 : Q')) (hx0 : (0 : Q') ≤ x) :
    radialPotential c x ≤ (1 : Q') := by
  apply HKConv.divPos_le_of_le
    (CReal.num_pos_of_pos (HKPos.factor_pos hc0 hc1
      (Q'.le_trans' _ _ _ (by decide) hx0)))
  have hsq : c*c ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right c 1 c (Q'.le_of_lt hc1) hc0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv c)) (Q'.le_of_lt hc1))
  have hg : (0 : Q') ≤ HKPos.factor c x + -((c+c)*(c+x)) :=
    nonneg_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.var 1))
        (.mul (.var 0) (.var 0))))
        (.neg (.mul (.add (.var 0) (.var 0)) (.add (.var 0) (.var 1)))))
      (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
      (by decide) (fun | 0 => c | _ => x)) (Q'.sub_nonneg_of_le hsq)
  exact Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg hg)
    (Q'.ge_of_eqv (Q'.one_mul_eqv _))

private theorem geoAmp_step (w : Q') (i : Nat) :
    HKPos.geoAmp w (i+1) ≈ (w*w)*HKPos.geoAmp w i := by
  have hi : 2*(i+1)+1 = (2*i+1)+2 := by omega
  unfold HKPos.geoAmp
  rw [hi]
  exact Q'.eqv_symm (Q'.mul_assoc_eqv w w (w^(2*i+1)))

private def factorExpr (c x : PolyExpr) : PolyExpr :=
  .add (.const 1) (.add (.mul (.add c c) x) (.mul c c))

private def potentialNumeratorExpr (c x : PolyExpr) : PolyExpr :=
  .mul (.add c c) (.add c x)

private def radialNumeratorExpr (c x : PolyExpr) : PolyExpr :=
  .add (.mul (.add (.const 1) (.neg (.mul x x)))
    (.mul (.add c c) (.add c c)))
    (.mul (.mul x (.add c c)) (factorExpr c x))

private def clearedExpr (c e x r : PolyExpr) : PolyExpr :=
  .add (.add
    (.mul (potentialNumeratorExpr c x)
      (.mul (factorExpr e x) (factorExpr e x)))
    (.neg (.mul (potentialNumeratorExpr e x)
      (.mul (factorExpr c x) (factorExpr e x)))))
    (.neg (.mul (.mul (.add (.const 1) (.neg r))
      (radialNumeratorExpr e x)) (factorExpr c x)))

private def positiveExpr : PolyExpr :=
  let c := PolyExpr.var 0; let x := PolyExpr.var 2; let r := PolyExpr.var 3
  let gap := PolyExpr.add (.const 1) (.neg r)
  .mul (.mul (.mul (.const 2) (.mul gap gap)) c)
    (.add (.add
      (.mul c (.add (.add (.const 1) (.mul (.const 2) r))
        (.neg (.mul (.mul r r) (.mul c c)))))
      (.mul x (.add (.const 1) (.mul (.mul r (.add r (.const 2))) (.mul c c)))))
      (.mul (.mul (.mul (.const 2) (.mul x x)) (.mul r r)) (.mul (.mul c c) c)))

/-- Exact telescope for the literal next logarithmic-factor radial increment.
All signs and denominators are retained; no recurrence is assumed. -/
theorem radialSummand_telescope {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (0 : Q') ≤ x) (i : Nat) :
    (1 + -(w*w))*radialSummand w x (i+1) ≤
      radialPotential (HKPos.geoAmp w i) x +
        -(radialPotential (HKPos.geoAmp w (i+1)) x) := by
  let c := HKPos.geoAmp w i
  let e := HKPos.geoAmp w (i+1)
  let r := w*w
  let D := HKPos.factor c x
  let E := HKPos.factor e x
  let F := radialPotential c x
  let G := radialPotential e x
  let s := HKConv.sTerm w x (i+1)
  let H := radialSummand w x (i+1)
  have hc := HKPos.pow_succ_pos_lt_one hw0 hw1 (2*i)
  have he := HKPos.pow_succ_pos_lt_one hw0 hw1 (2*(i+1))
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx0
  have hD : (0 : Q') < D := HKPos.factor_pos (Q'.le_of_lt hc.1) hc.2 hx
  have hE : (0 : Q') < E := HKPos.factor_pos (Q'.le_of_lt he.1) he.2 hx
  have hF : F*D ≈ (c+c)*(c+x) := potential_pin (Q'.le_of_lt hc.1) hc.2 hx0
  have hG : G*E ≈ (e+e)*(e+x) := potential_pin (Q'.le_of_lt he.1) he.2 hx0
  have hs : s*E ≈ e+e := HKConv.divPos_mul_eqv
    (HKConv.factor_num_pos hw0 hw1 hx (i+1))
  have hH : H*(E*E) ≈ (1 + -(x*x))*((e+e)*(e+e))+x*(e+e)*E := by
    have hp : H*(E*E) ≈ (1 + -(x*x))*((s*E)*(s*E))+x*(s*E)*E :=
      poly_identity_of_normal_eq
        (.mul (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
          (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 1)))
          (.mul (.var 2) (.var 2)))
        (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
          (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
          (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 2)))
        (by decide) (fun | 0 => x | 1 => s | _ => E)
    exact Q'.eqv_trans _ _ _ hp (add_congr
      (mul_congr (Q'.eqv_refl _) (mul_congr hs hs))
      (mul_congr (mul_congr (Q'.eqv_refl _) hs) (Q'.eqv_refl _)))
  have hgroup : ((F + -G) + -((1 + -r)*H))*(D*(E*E)) ≈
      (F*D)*(E*E) + -((G*E)*(D*E)) + -((1 + -r)*(H*(E*E))*D) :=
    poly_identity_of_normal_eq
      (.mul (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.mul (.add (.const 1) (.neg (.var 5))) (.var 2))))
        (.mul (.var 3) (.mul (.var 4) (.var 4))))
      (.add (.add (.mul (.mul (.var 0) (.var 3)) (.mul (.var 4) (.var 4)))
        (.neg (.mul (.mul (.var 1) (.var 4)) (.mul (.var 3) (.var 4)))))
        (.neg (.mul (.mul (.add (.const 1) (.neg (.var 5)))
          (.mul (.var 2) (.mul (.var 4) (.var 4)))) (.var 3))))
      (by decide) (fun | 0 => F | 1 => G | 2 => H | 3 => D | 4 => E | _ => r)
  let env : Nat → Q' := fun | 0 => c | 1 => e | 2 => x | _ => r
  let next : Nat → Q' := fun | 0 => c | 1 => r*c | 2 => x | _ => r
  have hclear : ((F + -G) + -((1 + -r)*H))*(D*(E*E)) ≈
      eval env (clearedExpr (.var 0) (.var 1) (.var 2) (.var 3)) :=
    Q'.eqv_trans _ _ _ hgroup (add_congr (add_congr
      (mul_congr hF (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (mul_congr hG (Q'.eqv_refl _))))
      (Q'.neg_eqv_congr _ _ (mul_congr
        (mul_congr (Q'.eqv_refl _) hH) (Q'.eqv_refl _))))
  have hnext : eval env (clearedExpr (.var 0) (.var 1) (.var 2) (.var 3)) ≈
      eval next (clearedExpr (.var 0) (.var 1) (.var 2) (.var 3)) :=
    eval_congr _ env next (by
      intro j
      cases j with
      | zero => exact Q'.eqv_refl _
      | succ j => cases j with
        | zero => exact geoAmp_step w i
        | succ j => cases j <;> exact Q'.eqv_refl _)
  have hpositive : eval next (clearedExpr (.var 0) (.var 1) (.var 2) (.var 3)) ≈
      eval env positiveExpr :=
    poly_identity_of_normal_eq
      (clearedExpr (.var 0) (.mul (.var 3) (.var 0)) (.var 2) (.var 3))
      positiveExpr (by decide +kernel) env
  have hr0 : (0 : Q') ≤ r := SumOfSquares.q_mul_self_nonneg w
  have hr1 : r ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv w)) (Q'.le_of_lt hw1))
  have hcc : c*c ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right c 1 c (Q'.le_of_lt hc.2) (Q'.le_of_lt hc.1))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv c)) (Q'.le_of_lt hc.2))
  have hrr : r*r ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right r 1 r hr1 hr0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv r)) hr1)
  have hprod : (r*r)*(c*c) ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcc (SumOfSquares.q_mul_self_nonneg r))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hrr)
  have hfirst : (0 : Q') ≤ (1+2*r) + -((r*r)*(c*c)) :=
    nonneg_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.const 1) (.mul (.const 2) (.var 0))) (.neg (.var 1)))
      (.add (.add (.const 1) (.neg (.var 1))) (.mul (.const 2) (.var 0)))
      (by decide) (fun | 0 => r | _ => (r*r)*(c*c)))
      (Q'.zero_le_add _ _ (Q'.sub_nonneg_of_le hprod)
        (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hr0))
  have hp : (0 : Q') ≤ eval env positiveExpr :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
        (SumOfSquares.q_mul_self_nonneg (1 + -r))) (Q'.le_of_lt hc.1))
      (Q'.zero_le_add _ _ (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (Q'.le_of_lt hc.1) hfirst)
        (Q'.mul_nonneg _ _ hx0 (Q'.zero_le_add _ _ Q'.zero_le_one
          (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hr0
            (Q'.zero_le_add _ _ hr0 (by decide : (0 : Q') ≤ 2))) (SumOfSquares.q_mul_self_nonneg c)))))
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
            (SumOfSquares.q_mul_self_nonneg x)) (SumOfSquares.q_mul_self_nonneg r))
          (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg c) (Q'.le_of_lt hc.1))))
  have hgap := nonneg_of_eqv (Q'.eqv_trans _ _ _ hclear
    (Q'.eqv_trans _ _ _ hnext hpositive)) hp
  have hden : (0 : Q') < D*(E*E) := HKPos.q_mul_pos hD (HKPos.q_mul_pos hE hE)
  have hg : (0 : Q') ≤ (F + -G) + -((1 + -r)*H) := by
    apply HKConvGen.mul_le_mul_left_cancel hden
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _))
      (Q'.le_trans' _ _ _ hgap (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact Q'.le_of_sub_nonneg hg

private theorem sum_with_potential {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) :
    ∀ N, (1 + -(w*w))*finSum (radialSummand w x) (N+1) +
      radialPotential (HKPos.geoAmp w N) x ≤
      (1 + -(w*w))*radialSummand w x 0 + radialPotential (HKPos.geoAmp w 0) x
  | 0 => Q'.le_of_eqv (add_congr (mul_congr (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 _) (QPoly.q_add_zero_eqv _))) (Q'.eqv_refl _))
  | N+1 => by
      let g := 1 + -(w*w)
      let S := finSum (radialSummand w x) (N+1)
      let H := radialSummand w x (N+1)
      let F := radialPotential (HKPos.geoAmp w N) x
      let G := radialPotential (HKPos.geoAmp w (N+1)) x
      have ht : g*H+G ≤ F := by
        have h := Q'.add_le_add_right _ _ G (radialSummand_telescope hw0 hw1 hx0 N)
        exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
          (by decide) (fun | 0 => F | _ => G)))
      have hp : g*(S+H)+G ≈ g*S+(g*H+G) :=
        poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
          (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 0) (.var 2)) (.var 3)))
          (by decide) (fun | 0 => g | 1 => S | 2 => H | _ => G)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
        (Q'.le_trans' _ _ _ (Q'.add_le_add_left (g*S) _ _ ht)
          (sum_with_potential hw0 hw1 hx0 N))

/-- Explicit denominator-cleared ceiling for the ACTUAL finite product cost.
Every N, including zero, is retained. -/
theorem productRadialCost_cleared_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (1 + -(w*w))*productRadialCost (HKConv.sTerm w x) N x ≤ 2 + -(w*w) := by
  have hr : w*w ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv w)) (Q'.le_of_lt hw1))
  have hg : (0 : Q') ≤ 1 + -(w*w) := Q'.sub_nonneg_of_le hr
  have hh : radialSummand w x 0 ≤ (1 : Q') := Q'.le_trans' _ _ _
    (JacobiProductRadialSignedTail.radialSummand_bounds hw0 hw1
      (Q'.le_trans' _ _ _ (by decide) hx0) hx1 0).2
    (JacobiHeatNearFlatLogHessian.sTerm_le_one hw0 hw1 hx0 0)
  have hc := HKPos.pow_succ_pos_lt_one hw0 hw1 0
  have hF := radialPotential_le_one (Q'.le_of_lt hc.1) hc.2 hx0
  have hbudget : (1 + -(w*w))*radialSummand w x 0 +
      radialPotential (HKPos.geoAmp w 0) x ≤ 2 + -(w*w) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hh hg) hF)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const 1)) (.const 1))
        (.add (.const 2) (.neg (.var 0))) (by decide) (fun _ => w*w)))
  cases N with
  | zero =>
      have hz : productRadialCost (HKConv.sTerm w x) 0 x ≈ (0 : Q') :=
        Q'.eqv_trans _ _ _ (add_congr (Q'.mul_zero_eqv _) (Q'.mul_zero_eqv _))
          (QPoly.q_add_zero_eqv 0)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (mul_congr (Q'.eqv_refl _) hz) (Q'.mul_zero_eqv _)))
        (nonneg_of_eqv (poly_identity_of_normal_eq
          (.add (.const 2) (.neg (.var 0)))
          (.add (.const 1) (.add (.const 1) (.neg (.var 0))))
          (by decide) (fun _ => w*w)) (Q'.zero_le_add _ _ Q'.zero_le_one hg))
  | succ N =>
      have hp := radialPotential_nonnegative
        (Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*N)).1) hx0
      have hs : (1 + -(w*w))*finSum (radialSummand w x) (N+1) ≤ 2 + -(w*w) :=
        Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hp)
          (Q'.le_trans' _ _ _ (sum_with_potential hw0 hw1 hx0 N) hbudget)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
        (Q'.mul_eqv_congr_left _ _ _ (radialSummand_sum_pin w x (N+1)))) hs

/-- Computed positive-hemisphere allowance, with leading coefficient one half
in nome-defect units. No source-dependent coefficient is supplied. -/
def nearFlatCap (w : Q') : Q' := 1 + HKConv.divPos 1 (1 + -(w*w))

theorem nearFlatCap_nonnegative (w : Q') : (0 : Q') ≤ nearFlatCap w :=
  Q'.zero_le_add _ _ Q'.zero_le_one (HKConv.divPos_nonneg Q'.zero_le_one)

theorem productRadialCost_le_nearFlatCap {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    productRadialCost (HKConv.sTerm w x) N x ≤ nearFlatCap w := by
  have hww : w*w < (1 : Q') := HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
      (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1
  have hg := HKPos.one_sub_pos hww
  have hi : HKConv.divPos 1 (1 + -(w*w))*(1 + -(w*w)) ≈ (1 : Q') :=
    HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hg)
  apply HKConvGen.mul_le_mul_left_cancel hg
  have hp : (1 + -(w*w))*nearFlatCap w ≈ 2 + -(w*w) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 1)))
      (.add (.add (.const 1) (.neg (.var 0)))
        (.mul (.var 1) (.add (.const 1) (.neg (.var 0)))))
      (by decide) (fun | 0 => w*w | _ => HKConv.divPos 1 (1 + -(w*w))))
      (Q'.eqv_trans _ _ _ (add_congr (Q'.eqv_refl _) hi)
        (poly_identity_of_normal_eq
          (.add (.add (.const 1) (.neg (.var 0))) (.const 1))
          (.add (.const 2) (.neg (.var 0))) (by decide) (fun _ => w*w)))
  exact Q'.le_trans' _ _ _ (productRadialCost_cleared_le hw0 hw1 hx0 hx1 N)
    (Q'.ge_of_eqv hp)

/-- Actual finite heat-jet consumer of the produced positive-hemisphere
ceiling. No product-cost hypothesis or heat inverse is supplied. This is
not an original-character-prefix or source-weighted marginal certificate. -/
theorem heat_radial_nonnegative_nearFlat {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (0 : Q') ≤ JacobiHeatRadialMomentJets.heatRadialExpression w x (nearFlatCap w) N := by
  have hxx : x*x ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right x 1 x hx1 hx0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv x)) hx1)
  exact JacobiHeatRadialMomentJets.heat_radial_nonnegative_of_productCost hw0 hw1
    (Q'.le_trans' _ _ _ (by decide) hx0) (nearFlatCap w) N
    (nearFlatCap_nonnegative w) hxx
    (productRadialCost_le_nearFlatCap hw0 hw1 hx0 hx1 N)

end YMGap.Continuum.JacobiProductRadialNearFlatBound

#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.radialPotential
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.radialPotential_nonnegative
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.radialPotential_le_one
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.radialSummand_telescope
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.sum_with_potential
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.productRadialCost_cleared_le
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.nearFlatCap
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.nearFlatCap_nonnegative
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.productRadialCost_le_nearFlatCap
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.heat_radial_nonnegative_nearFlat
