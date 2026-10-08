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

/-! ## Endpoint cancellation: all estimates remain denominator-cleared. -/

private theorem nome_gap_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) : (0 : Q') < 1 + -(w*w) :=
  HKPos.one_sub_pos (HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
      (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1)

/-- The computed endpoint form of the rational telescoping potential. -/
def endpointPotential (c : Q') : Q' := HKConv.divPos (c+c) (1+c)

private theorem endpointPotential_pin {c : Q'} (hc : (0 : Q') ≤ c) :
    endpointPotential c*(1+c) ≈ c+c :=
  HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1) (Q'.add_le_self_of_nonneg 1 c hc)))

private theorem endpointPotential_le_two {c : Q'} (hc : (0 : Q') ≤ c) :
    endpointPotential c ≤ c+c := by
  apply HKConv.divPos_le_of_le (CReal.num_pos_of_pos (Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1) (Q'.add_le_self_of_nonneg 1 c hc)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (c+c)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg 1 c hc)
      (Q'.zero_le_add _ _ hc hc))

private def endpointClearedExpr (c e q : PolyExpr) : PolyExpr :=
  let A := PolyExpr.add (.const 1) c
  let B := PolyExpr.add (.const 1) e
  .add (.mul (.mul (.add (.const 1) (.neg q)) (.add c c)) B)
    (.neg (.mul q (.add (.mul (.mul (.add c c) A) B)
      (.neg (.mul (.add e e) (.mul A A))))))

/-- Actual endpoint factor telescope, in inverse-free form. -/
theorem endpoint_sTerm_telescope {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (i : Nat) :
    (w*w)*(endpointPotential (HKPos.geoAmp w i) +
      -(endpointPotential (HKPos.geoAmp w (i+1)))) ≤
      (1 + -(w*w))*HKConv.sTerm w 1 i := by
  let c := HKPos.geoAmp w i
  let e := HKPos.geoAmp w (i+1)
  let q := w*w
  let A := 1+c
  let B := 1+e
  let F := endpointPotential c
  let G := endpointPotential e
  let s := HKConv.sTerm w 1 i
  have hc := Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*i)).1
  have he := Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*(i+1))).1
  have hA : (0 : Q') < A := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 c hc)
  have hB : (0 : Q') < B := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 e he)
  have hD : HKPos.factor c 1 ≈ A*A := poly_identity_of_normal_eq
    (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.const 1))
      (.mul (.var 0) (.var 0))))
    (.mul (.add (.const 1) (.var 0)) (.add (.const 1) (.var 0)))
    (by decide) (fun _ => c)
  have hs : s*(A*A) ≈ c+c := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _ (Q'.eqv_symm hD))
    (HKConv.divPos_mul_eqv (HKConv.factor_num_pos hw0 hw1 (by decide) i))
  have hF : F*A ≈ c+c := endpointPotential_pin hc
  have hG : G*B ≈ e+e := endpointPotential_pin he
  have hgroup : ((1 + -q)*s + -(q*(F + -G)))*((A*A)*B) ≈
      (1 + -q)*(s*(A*A))*B + -(q*((F*A)*A*B + -((G*B)*(A*A)))) :=
    poly_identity_of_normal_eq
      (.mul (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
        (.neg (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))))
        (.mul (.mul (.var 4) (.var 4)) (.var 5)))
      (.add (.mul (.mul (.add (.const 1) (.neg (.var 0)))
        (.mul (.var 1) (.mul (.var 4) (.var 4)))) (.var 5))
        (.neg (.mul (.var 0) (.add
          (.mul (.mul (.mul (.var 2) (.var 4)) (.var 4)) (.var 5))
          (.neg (.mul (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 4))))))))
      (by decide) (fun | 0 => q | 1 => s | 2 => F | 3 => G | 4 => A | _ => B)
  let env : Nat → Q' := fun | 0 => c | 1 => e | _ => q
  let next : Nat → Q' := fun | 0 => c | 1 => q*c | _ => q
  have hclear : ((1 + -q)*s + -(q*(F + -G)))*((A*A)*B) ≈
      eval env (endpointClearedExpr (.var 0) (.var 1) (.var 2)) :=
    Q'.eqv_trans _ _ _ hgroup (add_congr
      (mul_congr (mul_congr (Q'.eqv_refl _) hs) (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (mul_congr (Q'.eqv_refl _) (add_congr
        (mul_congr (mul_congr hF (Q'.eqv_refl _)) (Q'.eqv_refl _))
        (Q'.neg_eqv_congr _ _ (mul_congr hG (Q'.eqv_refl _)))))))
  have hnext := eval_congr (endpointClearedExpr (.var 0) (.var 1) (.var 2)) env next
    (by
      intro j
      cases j with
      | zero => exact Q'.eqv_refl _
      | succ j =>
          cases j with
          | zero => exact geoAmp_step w i
          | succ j => exact Q'.eqv_refl _)
  have hpos : eval next (endpointClearedExpr (.var 0) (.var 1) (.var 2)) ≈
      (c+c)*((1 + -q)*(1 + -q)) :=
    poly_identity_of_normal_eq
      (endpointClearedExpr (.var 0) (.mul (.var 2) (.var 0)) (.var 2))
      (.mul (.add (.var 0) (.var 0))
        (.mul (.add (.const 1) (.neg (.var 2))) (.add (.const 1) (.neg (.var 2)))))
      (by decide +kernel) env
  have hg := nonneg_of_eqv (Q'.eqv_trans _ _ _ hclear
    (Q'.eqv_trans _ _ _ hnext hpos))
    (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ hc hc)
      (SumOfSquares.q_mul_self_nonneg (1 + -q)))
  have hden := HKPos.q_mul_pos (HKPos.q_mul_pos hA hA) hB
  have hh : (0 : Q') ≤ (1 + -q)*s + -(q*(F + -G)) := by
    apply HKConvGen.mul_le_mul_left_cancel hden
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _))
      (Q'.le_trans' _ _ _ hg (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact Q'.le_of_sub_nonneg hh

private theorem endpoint_moment_telescope {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ∀ N, (w*w)*endpointPotential (HKPos.geoAmp w 0) ≤
      (1 + -(w*w))*JacobiHeatRadialMomentJets.firstMoment w 1 N +
        (w*w)*endpointPotential (HKPos.geoAmp w N)
  | 0 => Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (add_congr (Q'.mul_zero_eqv _) (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 _) (QPoly.q_add_zero_eqv _)))
  | N+1 => by
      let q := w*w
      let g := 1 + -q
      let M := JacobiHeatRadialMomentJets.firstMoment w 1 N
      let s := HKConv.sTerm w 1 N
      let F := endpointPotential (HKPos.geoAmp w N)
      let G := endpointPotential (HKPos.geoAmp w (N+1))
      have h : q*F ≤ g*s+q*G := by
        have ht := Q'.add_le_add_right _ _ (q*G) (endpoint_sTerm_telescope hw0 hw1 N)
        have hp : q*(F + -G)+q*G ≈ q*F := poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
            (.mul (.var 0) (.var 2))) (.mul (.var 0) (.var 1))
          (by decide) (fun | 0 => q | 1 => F | _ => G)
        exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp) ht
      have hp : g*M+(g*s+q*G) ≈ g*(M+s)+q*G := poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1))
          (.add (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 4))))
        (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
        (by decide) (fun | 0 => g | 1 => M | 2 => s | 3 => q | _ => G)
      exact Q'.le_trans' _ _ _ (endpoint_moment_telescope hw0 hw1 N)
        (Q'.le_trans' _ _ _ (Q'.add_le_add_left (g*M) _ _ h) (Q'.le_of_eqv hp))

private theorem nearFlatCap_gap_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) :
    (1 + -(w*w))*nearFlatCap w ≈ 2 + -(w*w) := by
  have hi : HKConv.divPos 1 (1 + -(w*w))*(1 + -(w*w)) ≈ (1 : Q') :=
    HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (nome_gap_positive hw0 hw1))
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 1)))
    (.add (.add (.const 1) (.neg (.var 0)))
      (.mul (.var 1) (.add (.const 1) (.neg (.var 0)))))
    (by decide) (fun | 0 => w*w | _ => HKConv.divPos 1 (1 + -(w*w))))
    (Q'.eqv_trans _ _ _ (add_congr (Q'.eqv_refl _) hi)
      (poly_identity_of_normal_eq
        (.add (.add (.const 1) (.neg (.var 0))) (.const 1))
        (.add (.const 2) (.neg (.var 0))) (by decide) (fun _ => w*w)))

/-- Actual first-moment lower payment, with no moment or heat inverse. -/
theorem endpoint_firstMoment_payment {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (N : Nat)
    (htail : HKPos.geoAmp w N ≤ 1 + -w) :
    4*nearFlatCap w ≤ 4*JacobiHeatRadialMomentJets.firstMoment w 1 N+13 := by
  let q := w*w
  let g := 1 + -q
  let d := 1 + -w
  let M := JacobiHeatRadialMomentJets.firstMoment w 1 N
  let F := endpointPotential (HKPos.geoAmp w 0)
  let G := endpointPotential (HKPos.geoAmp w N)
  have hq := SumOfSquares.q_mul_self_nonneg w
  have hc := Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*N)).1
  have hG : G ≤ d+d := Q'.le_trans' _ _ _ (endpointPotential_le_two hc)
    (Q'.add_le_add htail htail)
  have ht : q*F ≤ g*M+q*(d+d) := Q'.le_trans' _ _ _
    (endpoint_moment_telescope hw0 hw1 N)
    (Q'.add_le_add_left (g*M) _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hG hq))
  have hc0 : HKPos.geoAmp w 0 ≈ w := Q'.mul_one_eqv w
  have hF : F*(1+w) ≈ w+w := Q'.eqv_trans _ _ _
    (mul_congr (Q'.eqv_refl _) (Q'.eqv_symm (add_congr (Q'.eqv_refl 1) hc0)))
    (Q'.eqv_trans _ _ _
      (endpointPotential_pin (Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 0).1))
      (add_congr hc0 hc0))
  have hplus : (0 : Q') < 1+w := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 w (Q'.le_of_lt hw0))
  have hm : 4*q*(w+w) ≤ 4*(1+w)*(g*M+q*(d+d)) := by
    have ht' := Q'.mul_le_mul_of_nonneg_left _ _ _ ht
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 4) (Q'.le_of_lt hplus))
    have hp : 4*(1+w)*(q*F) ≈ 4*q*(w+w) := Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 4) (.add (.const 1) (.var 0))) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.const 4) (.var 1)) (.mul (.var 2) (.add (.const 1) (.var 0))))
        (by decide) (fun | 0 => w | 1 => q | _ => F))
      (mul_congr (Q'.eqv_refl _) hF)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp) ht'
  have hrem : (0 : Q') ≤ d*d*(8*q+15*w+5) := Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg d) (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 8) hq)
        (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 15) (Q'.le_of_lt hw0)))
      (by decide : (0 : Q') ≤ 5))
  have hp : (1+w)*((4*M+13)*g + -(4*(2 + -q))) ≈
      (4*(1+w)*(g*M+q*(d+d)) + -(4*q*(w+w))) + d*d*(8*q+15*w+5) :=
    poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.var 0)) (.add
        (.mul (.add (.mul (.const 4) (.var 1)) (.const 13))
          (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))))
        (.neg (.mul (.const 4) (.add (.const 2) (.neg (.mul (.var 0) (.var 0))))))))
      (.add (.add
        (.mul (.mul (.const 4) (.add (.const 1) (.var 0)))
          (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))) (.var 1))
            (.mul (.mul (.var 0) (.var 0))
              (.add (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0)))))))
        (.neg (.mul (.mul (.const 4) (.mul (.var 0) (.var 0))) (.add (.var 0) (.var 0)))))
        (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
          (.add (.add (.mul (.const 8) (.mul (.var 0) (.var 0))) (.mul (.const 15) (.var 0))) (.const 5))))
      (by decide +kernel) (fun | 0 => w | _ => M)
  have hpaid : (0 : Q') ≤ (4*M+13)*g + -(4*(2 + -q)) := by
    apply HKConvGen.mul_le_mul_left_cancel hplus
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _))
      (nonneg_of_eqv hp (Q'.zero_le_add _ _ (Q'.sub_nonneg_of_le hm) hrem))
  apply HKConvGen.mul_le_mul_left_cancel (nome_gap_positive hw0 hw1)
  have hC : g*(4*nearFlatCap w) ≈ 4*(2 + -q) := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 4) (.var 1)))
      (.mul (.const 4) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => g | _ => nearFlatCap w))
    (mul_congr (Q'.eqv_refl _) (nearFlatCap_gap_pin hw0 hw1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hC)
    (Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg hpaid)
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

/-- The literal endpoint logarithmic factor is at most one half. -/
theorem endpoint_sTerm_twice_le_one {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (i : Nat) : 2*HKConv.sTerm w 1 i ≤ (1 : Q') := by
  let c := HKPos.geoAmp w i
  let D := HKPos.factor c 1
  let s := HKConv.sTerm w 1 i
  have hc := HKPos.pow_succ_pos_lt_one hw0 hw1 (2*i)
  have hD := HKPos.factor_pos (Q'.le_of_lt hc.1) hc.2 (by decide : (-1 : Q') ≤ 1)
  have hs : s*D ≈ c+c := HKConv.divPos_mul_eqv (HKConv.factor_num_pos hw0 hw1 (by decide) i)
  have hg : 2*(c+c) ≤ D := Q'.le_of_sub_nonneg (nonneg_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.const 1))
        (.mul (.var 0) (.var 0)))) (.neg (.mul (.const 2) (.add (.var 0) (.var 0)))))
      (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
      (by decide) (fun _ => c)) (SumOfSquares.q_mul_self_nonneg (1 + -c)))
  apply HKConvGen.mul_le_mul_left_cancel hD
  have hp : D*(2*s) ≈ 2*(c+c) := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 2) (.var 1)))
      (.mul (.const 2) (.mul (.var 1) (.var 0)))
      (by decide) (fun | 0 => D | _ => s)) (mul_congr (Q'.eqv_refl _) hs)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.le_trans' _ _ _ hg (Q'.ge_of_eqv (Q'.mul_one_eqv D)))

private theorem sum_mono (f g : Nat → Q') (h : ∀ i, f i ≤ g i) :
    ∀ N, finSum f N ≤ finSum g N
  | 0 => Q'.le_refl' 0
  | N+1 => Q'.add_le_add (sum_mono f g h N) (h N)

theorem endpoint_secondMoment_twice_le_first {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    2*JacobiHeatRadialMomentJets.secondMoment w 1 N ≤
      JacobiHeatRadialMomentJets.firstMoment w 1 N := by
  have hp := const_mul_finSum (fun i => HKConv.sTerm w 1 i*HKConv.sTerm w 1 i) 2 N
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
  apply sum_mono _ _ (fun i => ?_) N
  have hs := HKConv.sTerm_nonneg hw0 hw1 (by decide : (-1 : Q') ≤ 1) i
  have h := Q'.mul_le_mul_of_nonneg_right _ _ _ (endpoint_sTerm_twice_le_one hw0 hw1 i) hs
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv 2 _ _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _)))

/-- Fixed rational endpoint slack; it contains no heat floor or source norm. -/
def endpointSlack : Q' := Q'.mkPos 15 4 (by decide)

/-- Actual normalized finite Jacobi heat cancellation at x=1. The heat is
multiplied, never inverted; N=0/1 remain in scope whenever the tail holds. -/
theorem heat_endpoint_cancellation {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (N : Nat) (htail : HKPos.geoAmp w N ≤ 1 + -w) :
    let h := QPoly.eval (JacobiShiftedPositiveCoefficients.heat w N) (1+(1 : Q'))
    let h1 := QPoly.eval (QPolyFormalDerivative.pderiv (JacobiShiftedPositiveCoefficients.heat w N))
      (1+(1 : Q'))
    nearFlatCap w*h + -h1 ≤ endpointSlack*h := by
  dsimp only
  let M := JacobiHeatRadialMomentJets.firstMoment w 1 N
  let V := JacobiHeatRadialMomentJets.secondMoment w 1 N
  let P := JacobiHeatRadialMomentJets.normalizedProduct w 1 N
  let C := nearFlatCap w
  let h := QPoly.eval (JacobiShiftedPositiveCoefficients.heat w N) (1+(1 : Q'))
  let h1 := QPoly.eval (QPolyFormalDerivative.pderiv (JacobiShiftedPositiveCoefficients.heat w N))
    (1+(1 : Q'))
  have hM : (0 : Q') ≤ M := JacobiHeatRadialMixtureCancellation.M1_nonneg _ N
    (fun i _ => HKConv.sTerm_nonneg hw0 hw1 (by decide : (-1 : Q') ≤ 1) i)
  have hP : (0 : Q') ≤ P := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (SU2PointwiseHeatPositiveCompletion.inverseNome_nonnegative w)
      (by decide : (0 : Q') ≤ HalfPow.half))
    (ThetaConv.Ppart_nonneg hw0 hw1 (by decide : (-1 : Q') ≤ 1) N)
  have hC := Q'.mul_le_mul_of_nonneg_right _ _ _ (endpoint_firstMoment_payment hw0 hw1 N htail) hM
  have hV := Q'.mul_le_mul_of_nonneg_left _ _ _ (endpoint_secondMoment_twice_le_first hw0 hw1 N)
    (by decide : (0 : Q') ≤ 2)
  have hm : 4*(C*M + -(M*M + -V)) ≤ 15*M := by
    have hp := Q'.add_le_add hC hV
    have hh := Q'.add_le_add_right _ _ (-(4*(M*M))) hp
    have hl : (4*C)*M+2*(2*V)+-(4*(M*M)) ≈ 4*(C*M + -(M*M + -V)) :=
      poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.const 4) (.var 0)) (.var 1))
          (.mul (.const 2) (.mul (.const 2) (.var 2))))
          (.neg (.mul (.const 4) (.mul (.var 1) (.var 1)))))
        (.mul (.const 4) (.add (.mul (.var 0) (.var 1))
          (.neg (.add (.mul (.var 1) (.var 1)) (.neg (.var 2))))))
        (by decide) (fun | 0 => C | 1 => M | _ => V)
    have hr : (4*M+13)*M+2*M+-(4*(M*M)) ≈ 15*M := poly_identity_of_normal_eq
      (.add (.add (.mul (.add (.mul (.const 4) (.var 0)) (.const 13)) (.var 0))
        (.mul (.const 2) (.var 0))) (.neg (.mul (.const 4) (.mul (.var 0) (.var 0)))))
      (.mul (.const 15) (.var 0)) (by decide) (fun _ => M)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv hr))
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ _ hm hP
  have hv : h ≈ P*M := JacobiHeatRadialMomentJets.heat_eval_moment_pin hw0 hw1 (by decide) N
  have hd : h1 ≈ P*(M*M + -V) := JacobiHeatRadialMomentJets.heat_first_moment_pin hw0 hw1 (by decide) N
  have hleft : 4*(C*h + -h1) ≈ P*(4*(C*M + -(M*M + -V))) :=
    Q'.eqv_trans _ _ _
      (mul_congr (Q'.eqv_refl _) (add_congr (mul_congr (Q'.eqv_refl _) hv)
        (Q'.neg_eqv_congr _ _ hd)))
      (poly_identity_of_normal_eq
        (.mul (.const 4) (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.neg (.mul (.var 1) (.var 3)))))
        (.mul (.var 1) (.mul (.const 4) (.add (.mul (.var 0) (.var 2)) (.neg (.var 3)))))
        (by decide) (fun | 0 => C | 1 => P | 2 => M | _ => M*M + -V))
  have hright : P*(15*M) ≈ 15*h := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 15) (.var 1)))
      (.mul (.const 15) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => P | _ => M))
    (mul_congr (Q'.eqv_refl _) (Q'.eqv_symm hv))
  have hpaid : 4*(C*h + -h1) ≤ 15*h := Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv hright))
  apply HKConvGen.mul_le_mul_left_cancel (by decide : (0 : Q') < 4)
  have hs : (4 : Q')*endpointSlack ≈ 15 := by decide
  have hr : 4*(endpointSlack*h) ≈ 15*h := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv 4 endpointSlack h))
    (mul_congr hs (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _ hpaid (Q'.ge_of_eqv hr)

/-- Computed sufficient endpoint onset, independent of the heat or source. -/
def endpointCancellationOnset (w : Q') : Nat := HKConvGen.powBaseCutoff w (1 + -w)

theorem endpointCancellationOnset_tail {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (N : Nat) (hN : endpointCancellationOnset w ≤ N) :
    HKPos.geoAmp w N ≤ 1 + -w :=
  Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (m := N) (n := 2*N+1) (by omega))
    (Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hN)
      (HKConvGen.pow_base_le_cutoff hw0 hw1 (HKPos.one_sub_pos hw1)))

theorem heat_endpoint_cancellation_at_onset {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (N : Nat) (hN : endpointCancellationOnset w ≤ N) :
    let h := QPoly.eval (JacobiShiftedPositiveCoefficients.heat w N) (1+(1 : Q'))
    let h1 := QPoly.eval (QPolyFormalDerivative.pderiv (JacobiShiftedPositiveCoefficients.heat w N))
      (1+(1 : Q'))
    nearFlatCap w*h + -h1 ≤ endpointSlack*h :=
  heat_endpoint_cancellation hw0 hw1 N (endpointCancellationOnset_tail hw0 hw1 N hN)

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
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpointPotential
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpoint_sTerm_telescope
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpoint_moment_telescope
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpoint_firstMoment_payment
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpoint_sTerm_twice_le_one
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpoint_secondMoment_twice_le_first
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpointSlack
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.heat_endpoint_cancellation
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpointCancellationOnset
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.endpointCancellationOnset_tail
#print axioms YMGap.Continuum.JacobiProductRadialNearFlatBound.heat_endpoint_cancellation_at_onset
