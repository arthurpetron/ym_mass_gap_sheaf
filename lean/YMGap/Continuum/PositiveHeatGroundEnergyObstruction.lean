/-
# A bounded positive action defeats a generic near-identity relative-energy inference

This is an explicit TWO-STATE diagnostic, not a BF4 or Yang--Mills model.
Its literal transfer is T=K_e M_V, K_e is symmetric, row-Markov and PSD,
V lies between 1/2 and 2, and the constructed positive g satisfies Tg=lambda*g.
Nevertheless the original edge-law OWN variance determinant is positive and
2*Z*energy exceeds it for every 0<e<1/2. The bare heat defect tends to zero
with e; the action does NOT tend to the constant action. No continuum,
spectral theorem, BF4-terminal counterexample or physical gap claim is made.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Sqrt
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.PositiveHeatGroundEnergyObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem add_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a+b ≈ a'+b' :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ha)
    (Q'.add_eqv_congr_left _ _ _ hb)

abbrev TwoValue := Q' × Q'

def pointwiseMul (a b : TwoValue) : TwoValue := (a.1*b.1, a.2*b.2)
def scale (a : Q') (h : TwoValue) : TwoValue := (a*h.1, a*h.2)
def unit : TwoValue := (1, 1)
def pairing (a b : TwoValue) : Q' := a.1*b.1+a.2*b.2

/-- Actual symmetric row-Markov heat, applied after spatial multiplication. -/
def heat (e : Q') (h : TwoValue) : TwoValue :=
  ((1-e)*h.1+e*h.2, e*h.1+(1-e)*h.2)

def action (e : Q') : TwoValue := (1-e+e*e, 2-e)
def transfer (e : Q') (h : TwoValue) : TwoValue := heat e (pointwiseMul (action e) h)
def ground (e : Q') : TwoValue := (e*(2-e), 1-e+e*e)
def groundEigenvalue (e : Q') : Q' := (2-e)*(1-e+e*e)
def weightedMass (e : Q') (h : TwoValue) : Q' := pairing (action e) h
def source : TwoValue := (1, 0)
def excitation (e : Q') : TwoValue := (1, -e)

def edgePartition (e : Q') : Q' :=
  weightedMass e (pointwiseMul (ground e) (transfer e (ground e)))

def sourceMomentOne (e : Q') : Q' := weightedMass e
  (pointwiseMul (pointwiseMul (ground e) (transfer e (ground e))) source)

def sourceMomentTwo (e : Q') : Q' := weightedMass e
  (pointwiseMul (pointwiseMul (ground e) (transfer e (ground e)))
    (pointwiseMul source source))

/-- The OWN centered variance cleared only by the edge partition squared. -/
def determinantVariance (e : Q') : Q' :=
  edgePartition e*sourceMomentTwo e-sourceMomentOne e*sourceMomentOne e

def groundEnergy (e : Q') : Q' := sourceMomentTwo e-
  weightedMass e (pointwiseMul (pointwiseMul (ground e) source)
    (transfer e (pointwiseMul (ground e) source)))

def muZero (e : Q') : Q' := (e*e)*(2-e)
def muOne (e : Q') : Q' := 1-e+e*e

private theorem positive_equivalent {a b : Q'} (h : a ≈ b) (ha : (0 : Q') < a) :
    (0 : Q') < b := Q'.pos_of_lt_of_le ha (Q'.le_of_eqv h)

private theorem power_positive (a : Q') (ha : (0 : Q') < a) :
    (n : Nat) → (0 : Q') < qpow a n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_positive a ha n) ha

private theorem lt_of_difference_positive {a b : Q'} (h : (0 : Q') < b-a) : a < b := by
  have hn := Q'.num_pos_of_pos h
  change (0 : Int) < b.num*(a.den : Int)+(-a.num)*(b.den : Int) at hn
  change a.num*(b.den : Int) < b.num*(a.den : Int)
  rw [Int.neg_mul] at hn
  omega

private theorem one_minus_lower {e : Q'} (hehalf : e < HalfPow.half) :
    HalfPow.half ≤ 1-e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : HalfPow.half ≈ 1-HalfPow.half))
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hehalf)))

/-- Literal unit preservation, including arbitrary signed e. -/
theorem heat_unit (e : Q') : (heat e unit).1 ≈ 1 ∧ (heat e unit).2 ≈ 1 := by
  constructor
  · exact poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const 1))
        (.mul (.var 0) (.const 1))) (.const 1) (by decide) (fun _ => e)
  · exact poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.const 1))
        (.mul (.add (.const 1) (.neg (.var 0))) (.const 1)))
      (.const 1) (by decide) (fun _ => e)

theorem heat_symmetric (e : Q') (a b : TwoValue) :
    pairing a (heat e b) ≈ pairing (heat e a) b :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 1) (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 3))
      (.mul (.var 0) (.var 4))))
      (.mul (.var 2) (.add (.mul (.var 0) (.var 3))
        (.mul (.add (.const 1) (.neg (.var 0))) (.var 4)))))
    (.add (.mul (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
      (.mul (.var 0) (.var 2))) (.var 3))
      (.mul (.add (.mul (.var 0) (.var 1))
        (.mul (.add (.const 1) (.neg (.var 0))) (.var 2))) (.var 4)))
    (by decide) (fun | 0 => e | 1 => a.1 | 2 => a.2 | 3 => b.1 | _ => b.2)

theorem heat_nonnegative {e : Q'} (he0 : (0 : Q') < e)
    (hehalf : e < HalfPow.half) {h : TwoValue}
    (hh : (0 : Q') ≤ h.1 ∧ (0 : Q') ≤ h.2) :
    (0 : Q') ≤ (heat e h).1 ∧ (0 : Q') ≤ (heat e h).2 := by
  have hmargin : (0 : Q') ≤ 1-e := Q'.le_trans' _ _ _
    HalfPow.half_nonneg (one_minus_lower hehalf)
  exact ⟨Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hmargin hh.1)
      (Q'.mul_nonneg _ _ (Q'.le_of_lt he0) hh.2),
    Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (Q'.le_of_lt he0) hh.1)
      (Q'.mul_nonneg _ _ hmargin hh.2)⟩

/-- Positive-semidefinite heat, not just entrywise positivity. -/
theorem heat_psd {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < HalfPow.half)
    (h : TwoValue) : (0 : Q') ≤ pairing h (heat e h) := by
  have htwo : 2*e ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 (Q'.le_of_lt hehalf) (by decide))
    (Q'.le_of_eqv (by decide : 2*HalfPow.half ≈ (1 : Q')))
  have hdiag := Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le htwo)
    (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg h.1)
      (SumOfSquares.q_mul_self_nonneg h.2))
  have hsum := Q'.mul_nonneg _ _ (Q'.le_of_lt he0)
    (SumOfSquares.q_mul_self_nonneg (h.1+h.2))
  have hp := Q'.zero_le_add _ _ hdiag hsum
  have hid : pairing h (heat e h) ≈
      (1-2*e)*(h.1*h.1+h.2*h.2)+e*((h.1+h.2)*(h.1+h.2)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 1) (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
        (.mul (.var 0) (.var 2))))
        (.mul (.var 2) (.add (.mul (.var 0) (.var 1))
          (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)))))
      (.add (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 0))))
        (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))))
        (.mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.add (.var 1) (.var 2)))))
      (by decide) (fun | 0 => e | 1 => h.1 | _ => h.2)
  exact Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv hid)

/-- Explicit bare near-identity defect on every signed vector. -/
theorem heat_bare_defect (e : Q') (h : TwoValue) :
    pairing h h-pairing h (heat e h) ≈ e*((h.1-h.2)*(h.1-h.2)) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))
      (.neg (.add (.mul (.var 1) (.add
        (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)) (.mul (.var 0) (.var 2))))
        (.mul (.var 2) (.add (.mul (.var 0) (.var 1))
          (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)))))))
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2)))
      (.add (.var 1) (.neg (.var 2)))))
    (by decide) (fun | 0 => e | 1 => h.1 | _ => h.2)

theorem action_bounds {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < HalfPow.half) :
    HalfPow.half ≤ (action e).1 ∧ (action e).1 ≤ 2 ∧
    HalfPow.half ≤ (action e).2 ∧ (action e).2 ≤ 2 := by
  have he1 : e ≤ (1 : Q') := Q'.le_trans' _ _ _ (Q'.le_of_lt hehalf) (by decide)
  have he : (0 : Q') ≤ e := Q'.le_of_lt he0
  have hlo := one_minus_lower hehalf
  have hv0lo : HalfPow.half ≤ (action e).1 := Q'.le_trans' _ _ _ hlo
    (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg e))
  have hsq : e*e ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ e he1 he) (Q'.le_of_eqv (Q'.mul_one_eqv e))
  have hv0 : (action e).1 ≤ 1 := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _
    (Q'.sub_nonneg_of_le hsq) (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 0) (.var 0))))
      (.add (.const 1) (.neg (.add (.add (.const 1) (.neg (.var 0)))
        (.mul (.var 0) (.var 0))))) (by decide) (fun _ => e))))
  have hv1lo : (1 : Q') ≤ (action e).2 := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _
    (Q'.sub_nonneg_of_le he1) (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.var 0)))
      (.add (.add (.const 2) (.neg (.var 0))) (.neg (.const 1)))
      (by decide) (fun _ => e))))
  have hv1hi : (action e).2 ≤ 2 := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ he
    (Q'.le_of_eqv (poly_identity_of_normal_eq (.var 0)
      (.add (.const 2) (.neg (.add (.const 2) (.neg (.var 0)))))
      (by decide) (fun _ => e))))
  exact ⟨hv0lo, Q'.le_trans' _ _ _ hv0 (by decide),
    Q'.le_trans' _ _ _ (by decide : HalfPow.half ≤ 1) hv1lo, hv1hi⟩

/-- The actual spatially weighted ground vector, not an assumed eigenpin. -/
theorem weightedGround_pin (e : Q') :
    (pointwiseMul (action e) (ground e)).1 ≈ groundEigenvalue e*e ∧
    (pointwiseMul (action e) (ground e)).2 ≈ groundEigenvalue e := by
  constructor
  · exact poly_identity_of_normal_eq (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (.mul (.mul (.var 2) (.var 1)) (.var 0)) (by decide)
      (fun | 0 => e | 1 => 1-e+e*e | _ => 2-e)
  · exact Q'.eqv_refl _

theorem transferGround_pin (e : Q') :
    (transfer e (ground e)).1 ≈ groundEigenvalue e*(ground e).1 ∧
    (transfer e (ground e)).2 ≈ groundEigenvalue e*(ground e).2 := by
  have h := weightedGround_pin e
  constructor
  · have hx : (transfer e (ground e)).1 ≈
        (1-e)*(groundEigenvalue e*e)+e*groundEigenvalue e :=
      add_congr (Q'.mul_eqv_congr_left _ _ _ h.1)
        (Q'.mul_eqv_congr_left _ _ _ h.2)
    exact Q'.eqv_trans _ _ _ hx (poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 1) (.var 0)))
        (.mul (.var 0) (.var 1)))
      (.mul (.var 1) (.mul (.var 0) (.add (.const 2) (.neg (.var 0)))))
      (by decide) (fun | 0 => e | _ => groundEigenvalue e))
  · have hx : (transfer e (ground e)).2 ≈
        e*(groundEigenvalue e*e)+(1-e)*groundEigenvalue e :=
      add_congr (Q'.mul_eqv_congr_left _ _ _ h.1)
        (Q'.mul_eqv_congr_left _ _ _ h.2)
    exact Q'.eqv_trans _ _ _ hx (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)))
      (.mul (.var 1) (.add (.add (.const 1) (.neg (.var 0))) (.mul (.var 0) (.var 0))))
      (by decide) (fun | 0 => e | _ => groundEigenvalue e))

theorem ground_positive {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < HalfPow.half) :
    (0 : Q') < (ground e).1 ∧ (0 : Q') < (ground e).2 ∧
      (0 : Q') < groundEigenvalue e := by
  have hb := action_bounds he0 hehalf
  have hv0 := Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half) hb.1
  have hv1 := Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half) hb.2.2.1
  exact ⟨Q'.mul_pos he0 hv1, hv0, Q'.mul_pos hv1 hv0⟩

private theorem mass_ground_product (e : Q') (h : TwoValue) :
    weightedMass e (pointwiseMul (ground e) h) ≈ groundEigenvalue e*(e*h.1+h.2) := by
  have h0 := weightedGround_pin e
  have h1 : weightedMass e (pointwiseMul (ground e) h) ≈
      ((action e).1*(ground e).1)*h.1+((action e).2*(ground e).2)*h.2 :=
    add_congr (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  have h2 : ((action e).1*(ground e).1)*h.1+((action e).2*(ground e).2)*h.2 ≈
      (groundEigenvalue e*e)*h.1+groundEigenvalue e*h.2 :=
    add_congr (Q'.mul_eqv_congr_right _ _ _ h0.1)
      (Q'.mul_eqv_congr_right _ _ _ h0.2)
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.var 3)))
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => groundEigenvalue e | 1 => e | 2 => h.1 | _ => h.2)))

/-- An actual signed transfer eigenvector orthogonal to the actual ground. -/
theorem excitation_transfer_pin (e : Q') :
    (transfer e (excitation e)).1 ≈ 1-2*e ∧
    (transfer e (excitation e)).2 ≈ (1-2*e)*(-e) := by
  constructor
  · exact poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.var 0)))
        (.mul (.add (.add (.const 1) (.neg (.var 0))) (.mul (.var 0) (.var 0))) (.const 1)))
        (.mul (.var 0) (.mul (.add (.const 2) (.neg (.var 0))) (.neg (.var 0)))))
      (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (by decide) (fun _ => e)
  · exact poly_identity_of_normal_eq
      (.add (.mul (.var 0)
        (.mul (.add (.add (.const 1) (.neg (.var 0))) (.mul (.var 0) (.var 0))) (.const 1)))
        (.mul (.add (.const 1) (.neg (.var 0)))
          (.mul (.add (.const 2) (.neg (.var 0))) (.neg (.var 0)))))
      (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (.neg (.var 0)))
      (by decide) (fun _ => e)

theorem excitation_ground_orthogonal (e : Q') :
    weightedMass e (pointwiseMul (ground e) (excitation e)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (mass_ground_product e (excitation e))
    (poly_identity_of_normal_eq (.mul (.var 0) (.add (.mul (.var 1) (.const 1)) (.neg (.var 1))))
      (.const 0) (by decide) (fun | 0 => groundEigenvalue e | _ => e))

/-- Exact edge partition and source moments under the SAME original edge law. -/
theorem moment_pins (e : Q') :
    edgePartition e ≈ qpow (groundEigenvalue e) 2*(muZero e+muOne e) ∧
    sourceMomentOne e ≈ qpow (groundEigenvalue e) 2*muZero e ∧
    sourceMomentTwo e ≈ qpow (groundEigenvalue e) 2*muZero e := by
  have hT := transferGround_pin e
  have hp : edgePartition e ≈ groundEigenvalue e*
      (e*(groundEigenvalue e*(ground e).1)+groundEigenvalue e*(ground e).2) :=
    Q'.eqv_trans _ _ _ (mass_ground_product e (transfer e (ground e)))
      (Q'.mul_eqv_congr_left _ _ _ (add_congr
        (Q'.mul_eqv_congr_left _ _ _ hT.1) hT.2))
  have hpart : edgePartition e ≈ qpow (groundEigenvalue e) 2*(muZero e+muOne e) :=
    Q'.eqv_trans _ _ _ hp (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.mul (.var 0) (.var 3))))
      (.mul (.pow (.var 0) 2) (.add (.mul (.mul (.var 1) (.var 1)) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => groundEigenvalue e | 1 => e | 2 => 2-e | _ => 1-e+e*e))
  have hmoment (f : TwoValue) : weightedMass e
      (pointwiseMul (pointwiseMul (ground e) (transfer e (ground e))) f) ≈
        qpow (groundEigenvalue e) 2*(muZero e*f.1+muOne e*f.2) := by
    have ha : weightedMass e
        (pointwiseMul (pointwiseMul (ground e) (transfer e (ground e))) f) ≈
        weightedMass e (pointwiseMul (ground e) (pointwiseMul (transfer e (ground e)) f)) :=
      add_congr (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _))
    have hb : groundEigenvalue e*(e*((transfer e (ground e)).1*f.1)+
        (transfer e (ground e)).2*f.2) ≈ groundEigenvalue e*
        (e*((groundEigenvalue e*(ground e).1)*f.1)+
          (groundEigenvalue e*(ground e).2)*f.2) :=
      Q'.mul_eqv_congr_left _ _ _ (add_congr
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ hT.1))
        (Q'.mul_eqv_congr_right _ _ _ hT.2))
    exact Q'.eqv_trans _ _ _ ha (Q'.eqv_trans _ _ _
      (mass_ground_product e (pointwiseMul (transfer e (ground e)) f))
      (Q'.eqv_trans _ _ _ hb (poly_identity_of_normal_eq
        (.mul (.var 0) (.add
          (.mul (.var 1) (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 4)))
          (.mul (.mul (.var 0) (.var 3)) (.var 5))))
        (.mul (.pow (.var 0) 2) (.add
          (.mul (.mul (.mul (.var 1) (.var 1)) (.var 2)) (.var 4))
          (.mul (.var 3) (.var 5))))
        (by decide) (fun
          | 0 => groundEigenvalue e
          | 1 => e
          | 2 => 2-e
          | 3 => 1-e+e*e
          | 4 => f.1
          | _ => f.2))))
  have hsource : sourceMomentOne e ≈ qpow (groundEigenvalue e) 2*muZero e :=
    Q'.eqv_trans _ _ _ (hmoment source) (poly_identity_of_normal_eq
      (.mul (.pow (.var 0) 2) (.add (.mul (.var 1) (.const 1)) (.mul (.var 2) (.const 0))))
      (.mul (.pow (.var 0) 2) (.var 1)) (by decide)
      (fun | 0 => groundEigenvalue e | 1 => muZero e | _ => muOne e))
  have hsquare : sourceMomentTwo e ≈ qpow (groundEigenvalue e) 2*muZero e :=
    Q'.eqv_trans _ _ _ (hmoment (pointwiseMul source source)) (poly_identity_of_normal_eq
      (.mul (.pow (.var 0) 2) (.add (.mul (.var 1) (.mul (.const 1) (.const 1)))
        (.mul (.var 2) (.mul (.const 0) (.const 0)))))
      (.mul (.pow (.var 0) 2) (.var 1)) (by decide)
      (fun | 0 => groundEigenvalue e | 1 => muZero e | _ => muOne e))
  exact ⟨hpart, hsource, hsquare⟩

theorem determinant_pin (e : Q') :
    determinantVariance e ≈ qpow (groundEigenvalue e) 4*(muZero e*muOne e) := by
  have h := moment_pins e
  have hx : determinantVariance e ≈
      (qpow (groundEigenvalue e) 2*(muZero e+muOne e))*(qpow (groundEigenvalue e) 2*muZero e)-
        (qpow (groundEigenvalue e) 2*muZero e)*(qpow (groundEigenvalue e) 2*muZero e) :=
    add_congr (mul_congr h.1 h.2.2)
      (Q'.neg_eqv_congr _ _ (mul_congr h.2.1 h.2.1))
  exact Q'.eqv_trans _ _ _ hx (poly_identity_of_normal_eq
    (.add (.mul (.mul (.pow (.var 0) 2) (.add (.var 1) (.var 2)))
      (.mul (.pow (.var 0) 2) (.var 1)))
      (.neg (.mul (.mul (.pow (.var 0) 2) (.var 1)) (.mul (.pow (.var 0) 2) (.var 1)))))
    (.mul (.pow (.var 0) 4) (.mul (.var 1) (.var 2)))
    (by decide) (fun | 0 => groundEigenvalue e | 1 => muZero e | _ => muOne e))

/-- Original energy of f=(1,0), not the bare heat energy. -/
theorem energy_pin (e : Q') : groundEnergy e ≈ qpow (groundEigenvalue e) 2*(e*e) := by
  have h := weightedGround_pin e
  have hnorm : weightedMass e (pointwiseMul (pointwiseMul (ground e) source)
        (transfer e (pointwiseMul (ground e) source))) ≈
      (1-e)*((groundEigenvalue e*e)*(groundEigenvalue e*e)) := by
    let y0 : PolyExpr := .mul (.var 1) (.const 1)
    let y1 : PolyExpr := .mul (.var 3) (.const 0)
    let z0 : PolyExpr := .add
      (.mul (.add (.const 1) (.neg (.var 4))) (.mul (.var 0) y0))
      (.mul (.var 4) (.mul (.var 2) y1))
    let z1 : PolyExpr := .add
      (.mul (.var 4) (.mul (.var 0) y0))
      (.mul (.add (.const 1) (.neg (.var 4))) (.mul (.var 2) y1))
    have hraw : weightedMass e (pointwiseMul (pointwiseMul (ground e) source)
        (transfer e (pointwiseMul (ground e) source))) ≈
        (1-e)*(((action e).1*(ground e).1)*((action e).1*(ground e).1)) :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul y0 z0)) (.mul (.var 2) (.mul y1 z1)))
        (.mul (.add (.const 1) (.neg (.var 4)))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
        (by decide) (fun
          | 0 => (action e).1
          | 1 => (ground e).1
          | 2 => (action e).2
          | 3 => (ground e).2
          | _ => e)
    exact Q'.eqv_trans _ _ _ hraw
      (Q'.mul_eqv_congr_left _ _ _ (mul_congr h.1 h.1))
  have hx : groundEnergy e ≈ qpow (groundEigenvalue e) 2*muZero e-
      (1-e)*((groundEigenvalue e*e)*(groundEigenvalue e*e)) :=
    add_congr (moment_pins e).2.2 (Q'.neg_eqv_congr _ _ hnorm)
  exact Q'.eqv_trans _ _ _ hx (poly_identity_of_normal_eq
    (.add (.mul (.pow (.var 0) 2) (.mul (.mul (.var 1) (.var 1))
      (.add (.const 2) (.neg (.var 1)))))
      (.neg (.mul (.add (.const 1) (.neg (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))))
    (.mul (.pow (.var 0) 2) (.mul (.var 1) (.var 1)))
    (by decide) (fun | 0 => groundEigenvalue e | _ => e))

private theorem mu_positive {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < HalfPow.half) :
    (0 : Q') < muZero e ∧ (0 : Q') < muOne e := by
  have hb := action_bounds he0 hehalf
  have hv1 := Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half) hb.2.2.1
  exact ⟨Q'.mul_pos (Q'.mul_pos he0 he0) hv1, (ground_positive he0 hehalf).2.1⟩

theorem edgePartition_positive {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < HalfPow.half) :
    (0 : Q') < edgePartition e := by
  have hm := mu_positive he0 hehalf
  have hp := Q'.mul_pos (power_positive _ (ground_positive he0 hehalf).2.2 2)
    (Q'.add_pos hm.1 hm.2)
  exact positive_equivalent (Q'.eqv_symm (moment_pins e).1) hp

theorem determinant_positive {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < HalfPow.half) :
    (0 : Q') < determinantVariance e := by
  have hm := mu_positive he0 hehalf
  have hp := Q'.mul_pos (power_positive _ (ground_positive he0 hehalf).2.2 4)
    (Q'.mul_pos hm.1 hm.2)
  exact positive_equivalent (Q'.eqv_symm (determinant_pin e)) hp

/-- Cleared OWN energy/variance exceeds 1/2 for every arbitrarily small e.
No division by the variance and no BF4 specialization is used. -/
theorem energy_relative_obstruction {e : Q'} (he0 : (0 : Q') < e)
    (hehalf : e < HalfPow.half) : determinantVariance e < 2*edgePartition e*groundEnergy e := by
  have hm := mu_positive he0 hehalf
  have hv1 := Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half)
    (action_bounds he0 hehalf).2.2.1
  have hgap : 2*edgePartition e*groundEnergy e-determinantVariance e ≈
      qpow (groundEigenvalue e) 4*(e*(e*e))*(2*e*(2-e)+muOne e) := by
    have hx : 2*edgePartition e*groundEnergy e-determinantVariance e ≈
        2*(qpow (groundEigenvalue e) 2*(muZero e+muOne e))*
          (qpow (groundEigenvalue e) 2*(e*e))-
            qpow (groundEigenvalue e) 4*(muZero e*muOne e) :=
      add_congr
        (mul_congr (Q'.mul_eqv_congr_left 2 _ _ (moment_pins e).1) (energy_pin e))
        (Q'.neg_eqv_congr _ _ (determinant_pin e))
    let x : PolyExpr := .var 1
    let b : PolyExpr := .add (.const 2) (.neg x)
    let x2 : PolyExpr := .mul x x
    let m0 : PolyExpr := .mul x2 b
    let m1 : PolyExpr := .var 2
    let l2 : PolyExpr := .pow (.var 0) 2
    let l4 : PolyExpr := .pow (.var 0) 4
    let left : PolyExpr := .add
      (.mul (.mul (.const 2) (.mul l2 (.add m0 m1))) (.mul l2 x2))
      (.neg (.mul l4 (.mul m0 m1)))
    let right : PolyExpr := .mul (.mul l4 (.mul x x2))
      (.add (.mul (.mul (.const 2) x) b) m1)
    exact Q'.eqv_trans _ _ _ hx (poly_identity_of_normal_eq left right
      (by decide) (fun | 0 => groundEigenvalue e | 1 => e | _ => muOne e))
  have hlast := Q'.add_pos (Q'.mul_pos (Q'.mul_pos (by decide : (0 : Q') < 2) he0) hv1) hm.2
  have hp := Q'.mul_pos
    (Q'.mul_pos (power_positive _ (ground_positive he0 hehalf).2.2 4)
      (Q'.mul_pos he0 (Q'.mul_pos he0 he0))) hlast
  exact lt_of_difference_positive (positive_equivalent (Q'.eqv_symm hgap) hp)

end YMGap.Continuum.PositiveHeatGroundEnergyObstruction

#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.heat_unit
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.heat_symmetric
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.heat_nonnegative
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.heat_psd
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.heat_bare_defect
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.action_bounds
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.weightedGround_pin
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.transferGround_pin
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.ground_positive
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.excitation_transfer_pin
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.excitation_ground_orthogonal
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.moment_pins
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.determinant_pin
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.energy_pin
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.edgePartition_positive
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.determinant_positive
#print axioms YMGap.Continuum.PositiveHeatGroundEnergyObstruction.energy_relative_obstruction
