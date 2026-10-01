/-
# A floor for the even-detector Young UPPER budget

The scalar correction obtained by testing the favorable source increment
against the even plaquette test still leaves a quadratic nome defect.  This
is a floor on that computed upper budget, not a lower bound on the actual
original temporal energy or a claim about the projected terminal source.
-/

import YMGap.Continuum.SU2HeatProductFirstMomentFloor
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.SU2PlaquetteEvenBudgetFloor

set_option autoImplicit false
set_option maxRecDepth 2048

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2HeatProductFirstMomentFloor (qpow_antitone_exponent)

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def subE (a b : PE) : PE := .add a (.neg b)

private def aE : PE := subE (.const 1) (.pow (.var 0) 8)
private def bE : PE :=
  subE (.add (.const 1) (.pow (.var 0) 8))
    (.mul (.const 2) (.pow (.var 0) 3))

private def coreE (a b x : PE) : PE :=
  let d := subE x (.const 1)
  subE (.mul (.const 32) (.add a (.mul b x)))
    (.mul (.mul a a) (.mul d d))

private def budgetE (x : PE) : PE := coreE aE bE x

private def env (u x : Q') : Nat → Q'
  | 0 => u
  | _ => x

/-- Sixty-four times the even-corrected Young upper budget, expressed using
`u=w^4`. Its linear heat factors are `u^3=w^12` and `u^8=w^32`. -/
def evenBudget64 (w x : Q') : Q' :=
  eval (env (RingNormaliser.qpow w 4) x) (budgetE (.var 1))

private def composedE : PE := Id.run do
  let u : PE := .pow (.var 0) 4
  let a := subE (.const 1) (.pow u 8)
  let b := subE (.add (.const 1) (.pow u 8))
    (.mul (.const 2) (.pow u 3))
  return coreE a b (.var 1)

private def nativeE : PE := Id.run do
  let a := subE (.const 1) (.pow (.var 0) 32)
  let b := subE (.add (.const 1) (.pow (.var 0) 32))
    (.mul (.const 2) (.pow (.var 0) 12))
  return coreE a b (.var 1)

/-- The encoded budget is exactly the proposed original scalar expression;
`64*B` is used to keep every coefficient integral. -/
theorem evenBudget64_formula (w x : Q') :
    evenBudget64 w x ≈
      32*((1 + -RingNormaliser.qpow w 32) +
        (1 + RingNormaliser.qpow w 32 +
          -(2*RingNormaliser.qpow w 12))*x) +
      -(((1 + -RingNormaliser.qpow w 32)*
          (1 + -RingNormaliser.qpow w 32))*
        ((x + -1)*(x + -1))) := by
  change eval (env w x) composedE ≈ eval (env w x) nativeE
  exact poly_identity_of_normal_eq composedE nativeE (by decide) (env w x)

private theorem power_nonnegative {u : Q'} (hu : (0 : Q') ≤ u) :
    ∀ n, (0 : Q') ≤ RingNormaliser.qpow u n
  | 0 => by change (0 : Q') ≤ 1; decide
  | n+1 => Q'.mul_nonneg _ _ (power_nonnegative hu n) hu

private theorem ring_power_eq_source (u : Q') : ∀ n,
    RingNormaliser.qpow u n = YMGap.Continuum.RGTransport.qpow u n
  | 0 => rfl
  | n+1 => congrArg (fun z : Q' => z*u) (ring_power_eq_source u n)

private theorem power_antitone {u : Q'} (hu0 : (0 : Q') ≤ u)
    (hu1 : u ≤ (1 : Q')) {i j : Nat} (hij : i ≤ j) :
    RingNormaliser.qpow u j ≤ RingNormaliser.qpow u i := by
  rw [ring_power_eq_source u j, ring_power_eq_source u i]
  exact qpow_antitone_exponent hu0 hu1 hij

private theorem power_le_one {u : Q'} (hu0 : (0 : Q') ≤ u)
    (hu1 : u ≤ (1 : Q')) (n : Nat) :
    RingNormaliser.qpow u n ≤ (1 : Q') := by
  have h := power_antitone hu0 hu1 (i := 0) (j := n) (Nat.zero_le n)
  simpa only [RingNormaliser.qpow_zero] using h

/- The eight negative coefficients of Q are paid by `348*u^3`; the
coefficient sum is 324, leaving `24*u^3`. -/
private def tailE : Nat → PE
  | 0 => .const 0
  | n+1 => .add (tailE n)
      (.mul (.const (Int.ofNat (9*(8-n))))
        (subE (.pow (.var 0) 3) (.pow (.var 0) (7+n))))

private theorem tail_nonnegative {u x : Q'} (hu0 : (0 : Q') ≤ u)
    (hu1 : u ≤ (1 : Q')) : ∀ n, n ≤ 8 →
    (0 : Q') ≤ eval (env u x) (tailE n)
  | 0, _ => by change (0 : Q') ≤ 0; decide
  | n+1, hn => by
      have hn8 : n ≤ 8 := Nat.le_trans (Nat.le_succ n) hn
      have hp : RingNormaliser.qpow u (7+n) ≤ RingNormaliser.qpow u 3 :=
        power_antitone hu0 hu1 (by omega : 3 ≤ 7+n)
      have hd : (0 : Q') ≤
          RingNormaliser.qpow u 3 + -RingNormaliser.qpow u (7+n) :=
        Q'.sub_nonneg_of_le hp
      have hc : (0 : Q') ≤ Q'.ofNat (9*(8-n)) := by
        rw [Q'.zero_le_iff_num_nonneg]
        exact Int.natCast_nonneg _
      change (0 : Q') ≤ eval (env u x) (tailE n) +
        Q'.ofNat (9*(8-n)) *
          (RingNormaliser.qpow u 3 + -RingNormaliser.qpow u (7+n))
      exact Q'.zero_le_add _ _ (tail_nonnegative hu0 hu1 n hn8)
        (Q'.mul_nonneg _ _ hc hd)

private def residualE : PE := Id.run do
  let u : PE := .var 0
  return .add
    (.add
      (.add
        (.add
          (.add
            (.add (.mul (.const 302) u)
              (.mul (.const 453) (.pow u 2)))
            (.mul (.const 24) (.pow u 3)))
          (.mul (.const 243) (.pow u 4)))
        (.mul (.const 138) (.pow u 5)))
      (.mul (.const 33) (.pow u 6)))
    (tailE 8)

private theorem residual_nonnegative {u x : Q'} (hu0 : (0 : Q') ≤ u)
    (hu1 : u ≤ (1 : Q')) :
    (0 : Q') ≤ eval (env u x) residualE := by
  have hp2 := power_nonnegative hu0 2
  have hp3 := power_nonnegative hu0 3
  have hp4 := power_nonnegative hu0 4
  have hp5 := power_nonnegative hu0 5
  have hp6 := power_nonnegative hu0 6
  have ht := tail_nonnegative (x := x) hu0 hu1 8 (Nat.le_refl 8)
  change (0 : Q') ≤
    (((((302*u + 453*RingNormaliser.qpow u 2) +
      24*RingNormaliser.qpow u 3) +
      243*RingNormaliser.qpow u 4) +
      138*RingNormaliser.qpow u 5) +
      33*RingNormaliser.qpow u 6) + eval (env u x) (tailE 8)
  have hbase : (0 : Q') ≤
    (((((302*u + 453*RingNormaliser.qpow u 2) +
      24*RingNormaliser.qpow u 3) +
      243*RingNormaliser.qpow u 4) +
      138*RingNormaliser.qpow u 5) +
      33*RingNormaliser.qpow u 6) := Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ (by decide) hu0)
            (Q'.mul_nonneg _ _ (by decide) hp2))
          (Q'.mul_nonneg _ _ (by decide) hp3))
        (Q'.mul_nonneg _ _ (by decide) hp4))
      (Q'.mul_nonneg _ _ (by decide) hp5))
    (Q'.mul_nonneg _ _ (by decide) hp6)
  exact Q'.zero_le_add _ _ hbase ht

/-- The endpoint `x=4` has an exact double nome-defect factor. The finite
tail in `residualE` is manifestly nonnegative on the unit interval. -/
private theorem four_factor (u : Q') :
    eval (env u 4) (budgetE (.var 1)) ≈
      ((1 + -u)*(1 + -u)) * (151 + eval (env u 4) residualE) := by
  exact poly_identity_of_normal_eq
    (budgetE (.const 4))
    (.mul (.mul (subE (.const 1) (.var 0)) (subE (.const 1) (.var 0)))
      (.add (.const 151) residualE))
    (by decide) (env u 4)

private theorem zero_factor (u : Q') :
    eval (env u 0) (budgetE (.var 1)) ≈
      (1 + -RingNormaliser.qpow u 8) *
        (32 + -(1 + -RingNormaliser.qpow u 8)) := by
  exact poly_identity_of_normal_eq
    (budgetE (.const 0))
    (.mul aE (subE (.const 32) aE))
    (by decide) (env u 0)

private def env3 (a b x : Q') : Nat → Q'
  | 0 => a
  | 1 => b
  | _ => x

private theorem core_chord (a b x : Q') :
    4*eval (env3 a b x) (coreE (.var 0) (.var 1) (.var 2)) ≈
      ((4 + -x)*eval (env3 a b 0) (coreE (.var 0) (.var 1) (.var 2)) +
        x*eval (env3 a b 4) (coreE (.var 0) (.var 1) (.var 2))) +
      4*(a*a)*(x*(4 + -x)) := by
  exact poly_identity_of_normal_eq
    (.mul (.const 4) (coreE (.var 0) (.var 1) (.var 2)))
    (.add
      (.add
        (.mul (subE (.const 4) (.var 2)) (coreE (.var 0) (.var 1) (.const 0)))
        (.mul (.var 2) (coreE (.var 0) (.var 1) (.const 4))))
      (.mul (.mul (.const 4) (.mul (.var 0) (.var 0)))
        (.mul (.var 2) (subE (.const 4) (.var 2)))))
    (by decide) (env3 a b x)

private theorem chord_identity (u x : Q') :
    4 * eval (env u x) (budgetE (.var 1)) ≈
      ((4 + -x) * eval (env u 0) (budgetE (.var 1)) +
        x * eval (env u 4) (budgetE (.var 1))) +
      4 * ((1 + -RingNormaliser.qpow u 8) *
        (1 + -RingNormaliser.qpow u 8)) * (x*(4 + -x)) := by
  let a := (1 : Q') + -RingNormaliser.qpow u 8
  let b := (1 : Q') + RingNormaliser.qpow u 8 +
    -(2*RingNormaliser.qpow u 3)
  change 4*eval (env3 a b x) (coreE (.var 0) (.var 1) (.var 2)) ≈
    ((4 + -x)*eval (env3 a b 0) (coreE (.var 0) (.var 1) (.var 2)) +
      x*eval (env3 a b 4) (coreE (.var 0) (.var 1) (.var 2))) +
      4*(a*a)*(x*(4 + -x))
  exact core_chord a b x

private theorem nome_power_gap {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (n : Nat) (hn : 1 ≤ n) :
    (1 : Q') + -w ≤ (1 : Q') + -RingNormaliser.qpow w n := by
  have hp : RingNormaliser.qpow w n ≤ w := by
    have h := power_antitone hw0 hw1 hn
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv w))
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hp)

private theorem gap_square_mono {a b : Q'}
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) : a*a ≤ b*b := by
  have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ a hab ha)
    (Q'.mul_le_mul_of_nonneg_left _ _ b hab hb)

private theorem endpoint_zero_floor {u h : Q'}
    (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q'))
    (hh0 : (0 : Q') ≤ h)
    (hha : h ≤ 1 + -RingNormaliser.qpow u 8)
    (hh1 : h ≤ (1 : Q')) :
    31*(h*h) ≤ eval (env u 0) (budgetE (.var 1)) := by
  let a := (1 : Q') + -RingNormaliser.qpow u 8
  have ha0 : (0 : Q') ≤ a := Q'.sub_nonneg_of_le
    (power_le_one hu0 hu1 8)
  have ha1 : a ≤ (1 : Q') := by
    have hp := power_nonnegative hu0 8
    have hn := Q'.neg_le_neg hp
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ hn)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))
  have hh2 : h*h ≤ h := by
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ h hh1 hh0
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_one_eqv h))
  have hsq : h*h ≤ a := Q'.le_trans' _ _ _ hh2 hha
  have hprod : 31*a ≤ a*(32 + -a) := by
    have hdiff : (0 : Q') ≤ (1 : Q') + -a := Q'.sub_nonneg_of_le ha1
    have hp := Q'.mul_nonneg _ _ ha0 hdiff
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (31*a) (a*((1 : Q') + -a)) hp)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.mul (.const 31) (.var 0))
          (.mul (.var 0) (subE (.const 1) (.var 0))))
        (.mul (.var 0) (subE (.const 32) (.var 0)))
        (by decide) (fun _ => a)))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (31 : Q') hsq (by decide)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv (zero_factor u).symm))

private theorem endpoint_four_floor {u h : Q'}
    (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q'))
    (hh0 : (0 : Q') ≤ h)
    (hhd : h ≤ (1 : Q') + -u) :
    31*(h*h) ≤ eval (env u 4) (budgetE (.var 1)) := by
  let d := (1 : Q') + -u
  have hd0 : (0 : Q') ≤ d := Q'.sub_nonneg_of_le hu1
  have hsq := gap_square_mono hh0 hhd
  have hr := residual_nonnegative (x := 4) hu0 hu1
  have hs : (0 : Q') ≤ 151 + eval (env u 4) residualE :=
    Q'.zero_le_add _ _ (by decide) hr
  have h31 : 31 ≤ 151 + eval (env u 4) residualE :=
    Q'.le_trans' _ _ _ (by decide : (31 : Q') ≤ 151)
      (Q'.add_le_self_of_nonneg 151 _ hr)
  have hleft := Q'.mul_le_mul_of_nonneg_left _ _ (31 : Q') hsq (by decide)
  have hright := Q'.mul_le_mul_of_nonneg_left _ _ (d*d) h31
    (Q'.mul_nonneg _ _ hd0 hd0)
  have hp : 31*(d*d) ≈ (d*d)*31 := Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _ hleft
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (Q'.le_trans' _ _ _ hright (Q'.le_of_eqv (four_factor u).symm)))

/-- Every allowed raw moment ratio `0≤x≤4` leaves at least a quadratic
nome defect in THIS computed upper budget. This does not bound actual energy
from below. -/
theorem even_budget_floor {w x : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hx0 : (0 : Q') ≤ x) (hx4 : x ≤ (4 : Q')) :
    31*((1 + -w)*(1 + -w)) ≤ evenBudget64 w x := by
  let h := (1 : Q') + -w
  let u := RingNormaliser.qpow w 4
  let a := (1 : Q') + -RingNormaliser.qpow u 8
  have hh0 : (0 : Q') ≤ h := Q'.sub_nonneg_of_le hw1
  have hh1 : h ≤ (1 : Q') := by
    have hn := Q'.neg_le_neg hw0
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ hn)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))
  have hu0 : (0 : Q') ≤ u := power_nonnegative hw0 4
  have hu1 : u ≤ (1 : Q') := by
    exact power_le_one hw0 hw1 4
  have hha : h ≤ a := by
    have hp : RingNormaliser.qpow u 8 ≈ RingNormaliser.qpow w 32 := by
      exact poly_identity_of_normal_eq
        (.pow (.pow (.var 0) 4) 8) (.pow (.var 0) 32)
        (by decide) (fun _ => w)
    have hg := nome_power_gap hw0 hw1 32 (by decide)
    exact Q'.le_trans' _ _ _ hg
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hp))))
  have hhd : h ≤ (1 : Q') + -u := nome_power_gap hw0 hw1 4 (by decide)
  have hz := endpoint_zero_floor hu0 hu1 hh0 hha hh1
  have hf := endpoint_four_floor hu0 hu1 hh0 hhd
  have hxgap : (0 : Q') ≤ (4 : Q') + -x := Q'.sub_nonneg_of_le hx4
  have ha0 : (0 : Q') ≤ a := Q'.sub_nonneg_of_le
    (power_le_one hu0 hu1 8)
  have hterm : (0 : Q') ≤ 4*(a*a)*(x*((4 : Q') + -x)) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ ha0 ha0))
      (Q'.mul_nonneg _ _ hx0 hxgap)
  have hchord := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ ((4 : Q') + -x) hz hxgap)
    (Q'.mul_le_mul_of_nonneg_left _ _ x hf hx0)
  have hsum : ((4 + -x)* (31*(h*h)) + x*(31*(h*h))) ≈
      4*(31*(h*h)) :=
    poly_identity_of_normal_eq
      (.add (.mul (subE (.const 4) (.var 0)) (.var 1))
        (.mul (.var 0) (.var 1)))
      (.mul (.const 4) (.var 1)) (by decide)
      (fun | 0 => x | _ => 31*(h*h))
  have hfour : 4*(31*(h*h)) ≤ 4*evenBudget64 w x := by
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsum)
      (Q'.le_trans' _ _ _ hchord
        (Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg _ _ hterm)
          (Q'.le_of_eqv (chord_identity u x).symm)))
  exact Q'.le_of_mul_le_mul_left hfour (by decide : (0 : Q') < 4)

/-- A coefficient `C*h^3` with `C*h<31/64` cannot dominate this budget.
This says nothing about whether actual original energy might be cubic. -/
theorem even_budget_not_cubic {w x C : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hx0 : (0 : Q') ≤ x) (hx4 : x ≤ (4 : Q'))
    (hh : (0 : Q') < (1 : Q') + -w)
    (hC : 64*(C*((1 : Q') + -w)) < (31 : Q')) :
    ¬ evenBudget64 w x ≤ 64*(C*(((1 + -w)*(1 + -w))*(1 + -w))) := by
  let h := (1 : Q') + -w
  have hp : (0 : Q') < h*h := Q'.mul_pos hh hh
  have hs : 64*(C*((h*h)*h)) < (h*h)*31 := by
    have hm := Q'.mul_lt_mul_of_pos_left hp hC
    exact Q'.lt_of_le_of_lt
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.const 64) (.mul (.var 0)
          (.mul (.mul (.var 1) (.var 1)) (.var 1))))
        (.mul (.mul (.var 1) (.var 1))
          (.mul (.const 64) (.mul (.var 0) (.var 1))))
        (by decide) (fun | 0 => C | _ => h))) hm
  intro hb
  have hf := even_budget_floor hw0 hw1 hx0 hx4
  have hf' : (h*h)*31 ≤ evenBudget64 w x :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hf
  exact Int.lt_irrefl _ (Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _ hf' hb) hs)

#print axioms evenBudget64
#print axioms evenBudget64_formula
#print axioms even_budget_floor
#print axioms even_budget_not_cubic

end YMGap.Continuum.SU2PlaquetteEvenBudgetFloor
