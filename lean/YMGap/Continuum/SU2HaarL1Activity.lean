/-
# R1 commit 2: ℓ¹ bound for the multi-link Haar, and the true-activity envelope

ADDITIVE.  Honest route with no positivity beyond what is proved.

* `sm4_bounds`: `0 ≤ sphereMoment4 e₀ e₁ e₂ e₃ ≤ 1`.  This is the Nat inequality
  `Π (2kᵢ−1)!! ≤ 4·6⋯(2+2Σkᵢ)`.
* `mono_bounds`: `0 ≤ H_n(m) ≤ 1`, so `haar_abs`: `|∫_n p| ≤ ‖p‖₁` (sum of `|coeff|`).
* `l1_mul`, `l1_add_le`, `l1_smul`: the norm is submultiplicative and subadditive.
* `L1q_mul`: the four-component quaternion ℓ¹ norm is submultiplicative.  Each coordinate
  variable has norm 4, so `‖scalar(plaqWord)‖₁ ≤ 256`.
* `char_l1`: `‖χ_s(x)‖₁ ≤ (2X+1)^s` when `‖x‖₁ ≤ X`.  At X = 256 this is `513^s`.
* `fPoly w … M = Σ_{1≤s≤M} coeffW w s · χ_s(U_p)`, the excited part of the plaquette weight.
* `fPoly_l1`: `‖fPoly‖₁ ≤ charEnv (513·w) M`.
* `fPoly_pass`: at `w₀ = 1/10⁸`, `‖fPoly‖₁ ≤ ε_L = 1/10¹⁵` for every M and p.
* `prod_l1`: `‖Π_{p∈γ} f_p‖₁ ≤ ε_L^{|γ|}`, so `|∫ Π_{p∈γ} f_p| ≤ ε_L^{|γ|}`.
-/

import YMGap.Continuum.SU2HaarDisjointSupport
import YMGap.Continuum.HeatKernelPolymerActivityR1

namespace YMGap.Continuum.SU2HaarL1Activity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.HeatKernelPolymerActivityR1 (charEnv envTerm charEnv_inv charEnv_nonneg)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## 1. Sphere moments lie in [0, 1] -/

theorem odf_sfd : ∀ a b : Nat, oddDoubleFactorial a * sphereFourDenominator b ≤
    sphereFourDenominator (a + b)
  | 0, b => by
    show 1 * sphereFourDenominator b ≤ _
    rw [Nat.one_mul, Nat.zero_add]; exact Nat.le_refl _
  | a + 1, b => by
    show (2 * a + 1) * oddDoubleFactorial a * sphereFourDenominator b ≤ _
    rw [Nat.succ_add, Nat.mul_assoc]
    show _ ≤ (4 + 2 * (a + b)) * sphereFourDenominator (a + b)
    exact Nat.mul_le_mul (by omega) (odf_sfd a b)

theorem odf4 (k0 k1 k2 k3 : Nat) :
    oddDoubleFactorial k0 * oddDoubleFactorial k1 * oddDoubleFactorial k2 * oddDoubleFactorial k3 ≤
      sphereFourDenominator (k0 + k1 + k2 + k3) := by
  have h3 := odf_sfd k3 0
  have h2 := odf_sfd k2 k3
  have h1 := odf_sfd k1 (k2 + k3)
  have h0 := odf_sfd k0 (k1 + (k2 + k3))
  have e : k0 + k1 + k2 + k3 = k0 + (k1 + (k2 + k3)) := by omega
  rw [e, Nat.mul_assoc, Nat.mul_assoc]
  refine Nat.le_trans (Nat.mul_le_mul_left _ ?_) h0
  refine Nat.le_trans (Nat.mul_le_mul_left _ ?_) h1
  refine Nat.le_trans (Nat.mul_le_mul_left _ ?_) h2
  have : sphereFourDenominator 0 = 1 := rfl
  rw [this, Nat.mul_one, Nat.add_zero] at h3
  exact h3

theorem sm4_bounds (e0 e1 e2 e3 : Nat) :
    (0 : Q') ≤ sphereMoment4 e0 e1 e2 e3 ∧ sphereMoment4 e0 e1 e2 e3 ≤ 1 := by
  unfold sphereMoment4
  split
  · refine ⟨(Q'.zero_le_iff_num_nonneg _).mpr (by rw [Q'.mkPos_num]; exact Int.natCast_nonneg _), ?_⟩
    have hN := odf4 (e0 / 2) (e1 / 2) (e2 / 2) (e3 / 2)
    show (Q'.mkPos _ _ _).num * ((1 : Q').den : Int) ≤ (1 : Q').num * ((Q'.mkPos _ _ _).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    show Int.ofNat _ * 1 ≤ 1 * ((sphereFourDenominator _ : Nat) : Int)
    rw [Int.mul_one, Int.one_mul]
    exact Int.ofNat_le.mpr hN
  · exact ⟨Q'.le_refl' _, by decide⟩

theorem unit_mul {a b : Q'} (ha : (0 : Q') ≤ a ∧ a ≤ 1) (hb : (0 : Q') ≤ b ∧ b ≤ 1) :
    (0 : Q') ≤ a * b ∧ a * b ≤ 1 :=
  ⟨Q'.mul_nonneg _ _ ha.1 hb.1, Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hb.2 ha.1)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv a)) ha.2)⟩

theorem prefix_bounds : ∀ (n : Nat) (m : List Nat),
    (0 : Q') ≤ quaternionHaarPrefix n m ∧ quaternionHaarPrefix n m ≤ 1
  | 0, _ => ⟨show (0 : Q') ≤ 1 from by decide, Q'.le_refl' _⟩
  | n + 1, m => unit_mul (sm4_bounds _ _ _ _) (prefix_bounds n (m.drop 4))

theorem mono_bounds (n : Nat) (m : List Nat) :
    (0 : Q') ≤ quaternionHaarMono n m ∧ quaternionHaarMono n m ≤ 1 := by
  unfold quaternionHaarMono
  split
  · exact prefix_bounds n m
  · exact ⟨Q'.le_refl' _, by decide⟩

/-! ## 2. The ℓ¹ norm -/

def l1 : RatPoly → Q'
  | [] => 0
  | t :: p => Q'.abs t.2 + l1 p

theorem l1_nonneg : ∀ p, (0 : Q') ≤ l1 p
  | [] => Q'.le_refl' _
  | _ :: p => Q'.zero_le_add _ _ (Q'.abs_nonneg _) (l1_nonneg p)

/-- **ℓ¹ Haar bound (PROVED):** `|∫_n p| ≤ ‖p‖₁`. -/
theorem haar_abs (n : Nat) : ∀ p : RatPoly, Q'.abs (quaternionHaar n p) ≤ l1 p
  | [] => show Q'.abs 0 ≤ 0 from by decide
  | t :: p => by
    show Q'.abs (t.2 * quaternionHaarMono n t.1 + quaternionHaar n p) ≤ Q'.abs t.2 + l1 p
    have hb := mono_bounds n t.1
    refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add ?_ (haar_abs n p))
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_
    rw [ExpNeg.abs_of_nonneg hb.1]
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hb.2 (Q'.abs_nonneg _))
      (Q'.le_of_eqv (Q'.mul_one_eqv _))

theorem l1_append : ∀ p q : RatPoly, (l1 (p ++ q)).eqv (l1 p + l1 q)
  | [], q => by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0) (PolyExpr.const 0 + V 0) (by decide) (fun _ => l1 q)
  | t :: p, q => by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl (Q'.abs t.2)) (l1_append p q)) ?_
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + (V 1 + V 2)) ((V 0 + V 1) + V 2) (by decide)
      (fun | 0 => Q'.abs t.2 | 1 => l1 p | _ => l1 q)

theorem l1_add_le (p q : RatPoly) : l1 (polyAdd p q) ≤ l1 p + l1 q := Q'.le_of_eqv (l1_append p q)

theorem l1_neg_le : ∀ p : RatPoly, l1 (polyNeg p) ≤ l1 p
  | [] => Q'.le_refl' _
  | t :: p => Q'.add_le_add (Q'.le_of_eqv (Q'.abs_neg' t.2)) (l1_neg_le p)

theorem l1_map_mul (c : Q') (f : List Nat → List Nat) : ∀ q : RatPoly,
    l1 (q.map fun t => (f t.1, c * t.2)) ≤ Q'.abs c * l1 q
  | [] => Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | t :: q => by
    show Q'.abs (c * t.2) + l1 (q.map fun t => (f t.1, c * t.2)) ≤ Q'.abs c * (Q'.abs t.2 + l1 q)
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (ExpNeg.abs_mul_le _ _) (l1_map_mul c f q)) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

theorem l1_smul (c : Q') (p : RatPoly) : l1 (polySmul c p) ≤ Q'.abs c * l1 p :=
  l1_map_mul c id p

/-- **Submultiplicativity (PROVED).** -/
theorem l1_mul : ∀ p q : RatPoly, l1 (polyMul p q) ≤ l1 p * l1 q
  | [], q => Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | s :: p, q => by
    show l1 ((q.map fun t => (monoMul s.1 t.1, s.2 * t.2)) ++ polyMul p q) ≤ (Q'.abs s.2 + l1 p) * l1 q
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (l1_append _ _)) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (l1_map_mul s.2 (monoMul s.1) q) (l1_mul p q)) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))

/-! ## 3. Quaternion words -/

def L1q (q : PolyQuaternion) : Q' := l1 q.scalar + l1 q.iPart + l1 q.jPart + l1 q.kPart

theorem L1q_nonneg (q : PolyQuaternion) : (0 : Q') ≤ L1q q :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (l1_nonneg _) (l1_nonneg _))
    (l1_nonneg _)) (l1_nonneg _)

theorem comb4 {A B C D a b c d : Q'} (hA : A ≤ a) (hB : B ≤ b) (hC : C ≤ c) (hD : D ≤ d) :
    A + (B + (C + D)) ≤ a + (b + (c + d)) :=
  Q'.add_le_add hA (Q'.add_le_add hB (Q'.add_le_add hC hD))

theorem L1q_mul (q r : PolyQuaternion) : L1q (PolyQuaternion.mul q r) ≤ L1q q * L1q r := by
  let a0 := l1 q.scalar; let a1 := l1 q.iPart; let a2 := l1 q.jPart; let a3 := l1 q.kPart
  let b0 := l1 r.scalar; let b1 := l1 r.iPart; let b2 := l1 r.jPart; let b3 := l1 r.kPart
  have hs : l1 (PolyQuaternion.mul q r).scalar ≤ a0 * b0 + (a1 * b1 + (a2 * b2 + a3 * b3)) := by
    refine Q'.le_trans' _ _ _ (l1_add_le _ _) (Q'.add_le_add (l1_mul _ _) ?_)
    refine Q'.le_trans' _ _ _ (l1_neg_le _) (Q'.le_trans' _ _ _ (l1_add_le _ _)
      (Q'.add_le_add (l1_mul _ _) ?_))
    exact Q'.le_trans' _ _ _ (l1_add_le _ _) (Q'.add_le_add (l1_mul _ _) (l1_mul _ _))
  have hv : ∀ A B C D : RatPoly,
      l1 (polyAdd A (polyAdd B (polyAdd C (polyNeg D)))) ≤ l1 A + (l1 B + (l1 C + l1 D)) :=
    fun A B C D => Q'.le_trans' _ _ _ (l1_add_le _ _) (Q'.add_le_add (Q'.le_refl' _)
      (Q'.le_trans' _ _ _ (l1_add_le _ _) (Q'.add_le_add (Q'.le_refl' _)
        (Q'.le_trans' _ _ _ (l1_add_le _ _) (Q'.add_le_add (Q'.le_refl' _) (l1_neg_le _))))))
  have hi : l1 (PolyQuaternion.mul q r).iPart ≤ a0 * b1 + (a1 * b0 + (a2 * b3 + a3 * b2)) :=
    Q'.le_trans' _ _ _ (hv _ _ _ _) (comb4 (l1_mul _ _) (l1_mul _ _) (l1_mul _ _) (l1_mul _ _))
  have hj : l1 (PolyQuaternion.mul q r).jPart ≤ a0 * b2 + (a2 * b0 + (a3 * b1 + a1 * b3)) :=
    Q'.le_trans' _ _ _ (hv _ _ _ _) (comb4 (l1_mul _ _) (l1_mul _ _) (l1_mul _ _) (l1_mul _ _))
  have hk : l1 (PolyQuaternion.mul q r).kPart ≤ a0 * b3 + (a3 * b0 + (a1 * b2 + a2 * b1)) :=
    Q'.le_trans' _ _ _ (hv _ _ _ _) (comb4 (l1_mul _ _) (l1_mul _ _) (l1_mul _ _) (l1_mul _ _))
  refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add (Q'.add_le_add hs hi) hj) hk)
    (Q'.le_of_eqv ?_)
  show (_ : Q').eqv ((a0 + a1 + a2 + a3) * (b0 + b1 + b2 + b3))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    ((V 0 * V 4 + (V 1 * V 5 + (V 2 * V 6 + V 3 * V 7))) +
      (V 0 * V 5 + (V 1 * V 4 + (V 2 * V 7 + V 3 * V 6))) +
      (V 0 * V 6 + (V 2 * V 4 + (V 3 * V 5 + V 1 * V 7))) +
      (V 0 * V 7 + (V 3 * V 4 + (V 1 * V 6 + V 2 * V 5))))
    ((V 0 + V 1 + V 2 + V 3) * (V 4 + V 5 + V 6 + V 7)) (by decide)
    (fun | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => b0 | 5 => b1 | 6 => b2 | _ => b3)

theorem L1q_conj (q : PolyQuaternion) : L1q (PolyQuaternion.conj q) ≤ L1q q :=
  Q'.add_le_add (Q'.add_le_add (Q'.add_le_add (Q'.le_refl' _) (l1_neg_le _)) (l1_neg_le _))
    (l1_neg_le _)

theorem L1q_var (links : List Z4Link) (ℓ : Z4Link) : L1q (linkVar links ℓ) ≤ Q'.ofNat 4 := by
  show (Q'.abs 1 + 0) + (Q'.abs 1 + 0) + (Q'.abs 1 + 0) + (Q'.abs 1 + 0) ≤ Q'.ofNat 4
  decide

theorem L1q_mul_le {q r : PolyQuaternion} {X Y : Q'} (hq : L1q q ≤ X) (hr : L1q r ≤ Y)
    (hX : (0 : Q') ≤ X) : L1q (PolyQuaternion.mul q r) ≤ X * Y :=
  Q'.le_trans' _ _ _ (L1q_mul q r) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hq (L1q_nonneg r))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hr hX))

/-- `‖scalar(plaqWord)‖₁ ≤ 256`. -/
theorem word_l1 (links : List Z4Link) (N : Nat) (p : Z4Plaq) :
    l1 (plaqWord links N p).scalar ≤ Q'.ofNat 256 := by
  have h4 : (0 : Q') ≤ Q'.ofNat 4 := by decide
  have h16 : (0 : Q') ≤ Q'.ofNat 4 * Q'.ofNat 4 := by decide
  have hw : L1q (plaqWord links N p) ≤ (Q'.ofNat 4 * Q'.ofNat 4) * (Q'.ofNat 4 * Q'.ofNat 4) :=
    L1q_mul_le (L1q_mul_le (L1q_var _ _) (L1q_var _ _) h4)
      (L1q_mul_le (Q'.le_trans' _ _ _ (L1q_conj _) (L1q_var _ _))
        (Q'.le_trans' _ _ _ (L1q_conj _) (L1q_var _ _)) h4) h16
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hw (by decide))
  let q := plaqWord links N p
  show l1 q.scalar ≤ l1 q.scalar + l1 q.iPart + l1 q.jPart + l1 q.kPart
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (l1_nonneg _)) (Q'.add_le_self_of_nonneg _ _ (l1_nonneg _)))
    (Q'.add_le_self_of_nonneg _ _ (l1_nonneg _))

/-! ## 4. Characters -/

theorem pow_le_succ {B : Q'} (hB : (1 : Q') ≤ B) (n : Nat) : B ^ n ≤ B ^ (n + 1) := by
  show B ^ n ≤ B * B ^ n
  have h0 : (0 : Q') ≤ B ^ n := Q'.pow_nonneg _ (Q'.le_trans' _ _ _ (by decide) hB) _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hB h0)

/-- **Character ℓ¹ bound (PROVED).** -/
theorem char_l1 (x : RatPoly) (X : Q') (hX : (0 : Q') ≤ X) (hx : l1 x ≤ X) :
    ∀ n, l1 (characterPolynomial x n) ≤ (2 * X + 1) ^ n ∧
      l1 (characterPolynomial x (n + 1)) ≤ (2 * X + 1) ^ (n + 1) := by
  let B := 2 * X + 1
  have hB1 : (1 : Q') ≤ B := Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) hX)) (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have h2x : l1 (polySmul 2 x) ≤ 2 * X :=
    Q'.le_trans' _ _ _ (l1_smul 2 x) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hx (by decide)) (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
        (by decide : (Q'.abs 2).eqv 2))))
  intro n
  induction n with
  | zero =>
    refine ⟨by show Q'.abs 1 + 0 ≤ 1; decide, ?_⟩
    show l1 (polySmul 2 x) ≤ B * 1
    exact Q'.le_trans' _ _ _ h2x (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (by decide))
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))))
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hBn : (0 : Q') ≤ B ^ (n + 1) := Q'.pow_nonneg _ (Q'.le_trans' _ _ _ (by decide) hB1) _
    show l1 (polyAdd (polyMul (polySmul 2 x) (characterPolynomial x (n + 1)))
      (polySmul (-1) (characterPolynomial x n))) ≤ B * B ^ (n + 1)
    refine Q'.le_trans' _ _ _ (l1_add_le _ _) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_trans' _ _ _ (l1_mul _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h2x (l1_nonneg _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ih.2 (Q'.mul_nonneg _ _ (by decide) hX))))
      (Q'.le_trans' _ _ _ (l1_smul _ _) (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ih.1 (Q'.abs_nonneg _))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
          (by decide : (Q'.abs (-1)).eqv 1))) (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.one_mul_eqv _)) (pow_le_succ hB1 n)))))) ?_
    refine Q'.le_of_eqv ?_
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (PolyExpr.const 2 * V 0 * V 1 + V 1)
      ((PolyExpr.const 2 * V 0 + PolyExpr.const 1) * V 1) (by decide)
      (fun | 0 => X | _ => B ^ (n + 1))

/-! ## 5. The excited plaquette polynomial and its envelope -/

abbrev B513 : Q' := 2 * Q'.ofNat 256 + 1

def fPoly (w : Q') (links : List Z4Link) (N : Nat) (p : Z4Plaq) : Nat → RatPoly
  | 0 => []
  | M + 1 => polyAdd (fPoly w links N p M)
      (polySmul (coeffW w (M + 1)) (plaqCharacter links N p (M + 1)))

theorem qpow_eqv (w : Q') : ∀ n, (YMGap.Continuum.RGTransport.qpow w n).eqv (w ^ n)
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (qpow_eqv w n)) (Q'.mul_comm_eqv _ _)

theorem pow_ge {b : Q'} (hb : (1 : Q') ≤ b) : ∀ {s k : Nat}, s ≤ k → b ^ s ≤ b ^ k
  | s, k, h => by
    induction k with
    | zero => rw [Nat.le_zero.mp h]; exact Q'.le_refl' _
    | succ k ih =>
      rcases Nat.lt_or_ge s (k + 1) with hl | hl
      · exact Q'.le_trans' _ _ _ (ih (Nat.le_of_lt_succ hl)) (pow_le_succ hb k)
      · rw [Nat.le_antisymm h hl]; exact Q'.le_refl' _

theorem term_le {w : Q'} (h0 : (0 : Q') ≤ w) (s : Nat) :
    coeffW w s * B513 ^ s ≤ envTerm (B513 * w) s := by
  have hB : (1 : Q') ≤ B513 := by decide
  have hk : s ≤ s * (s + 2) := by
    have := Nat.mul_le_mul_left s (show 1 ≤ s + 2 by omega); rwa [Nat.mul_one] at this
  have hw : (0 : Q') ≤ w ^ (s * (s + 2)) := Q'.pow_nonneg _ h0 _
  show YMGap.Continuum.RGTransport.dimQ s * YMGap.Continuum.RGTransport.qpow w (s * (s + 2)) *
    B513 ^ s ≤ Q'.ofNat ((s + 1) * (s + 1)) * (B513 * w) ^ (s * (s + 2))
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_eqv
    (Q'.mul_eqv_congr_left _ _ _ (qpow_eqv w _))) (Q'.pow_nonneg _ (by decide) _)) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_ge hB hk)
    (Q'.mul_nonneg _ _ (YMGap.Continuum.ClusterCount.ofNat_nonneg _) hw)) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (YMGap.Continuum.Z4PolymerKP.ofNat_le' (by
      have := Nat.mul_le_mul_left (s + 1) (show 1 ≤ s + 1 by omega); rwa [Nat.mul_one] at this)) hw)
    (Q'.pow_nonneg _ (by decide) _)) (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _
    (YMGap.Continuum.Z4PolymerKP.mul_pow' B513 w _))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * V 1 * V 2) (V 0 * (V 2 * V 1)) (by decide)
    (fun | 0 => Q'.ofNat ((s + 1) * (s + 1)) | 1 => w ^ (s * (s + 2)) | _ => B513 ^ (s * (s + 2)))

/-- **Envelope (PROVED):** `‖Σ_{1≤s≤M} coeffW w s χ_s(U_p)‖₁ ≤ charEnv (513w) M`. -/
theorem fPoly_l1 {w : Q'} (h0 : (0 : Q') ≤ w) (links : List Z4Link) (N : Nat) (p : Z4Plaq) :
    ∀ M, l1 (fPoly w links N p M) ≤ charEnv (B513 * w) M
  | 0 => Q'.le_refl' _
  | M + 1 => by
    have hc := (char_l1 _ _ (by decide) (word_l1 links N p) (M + 1)).1
    refine Q'.le_trans' _ _ _ (l1_add_le _ _) (Q'.add_le_add (fPoly_l1 h0 links N p M) ?_)
    refine Q'.le_trans' _ _ _ (l1_smul _ _) ?_
    rw [ExpNeg.abs_of_nonneg (YMGap.Continuum.BondMovingStep.coeffW_nonneg h0 _)]
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hc
      (YMGap.Continuum.BondMovingStep.coeffW_nonneg h0 _)) (term_le h0 (M + 1))

def w0 : Q' := Q'.mkPos 1 100000000 (by decide)
def epsL : Q' := Q'.mkPos 1 1000000000000000 (by decide)

/-- **Pass (PROVED):** at `w₀ = 10⁻⁸`, `‖f_p‖₁ ≤ ε_L = 10⁻¹⁵` for every cutoff M. -/
theorem fPoly_pass (links : List Z4Link) (N : Nat) (p : Z4Plaq) (M : Nat) :
    l1 (fPoly w0 links N p M) ≤ epsL := by
  have h0 : (0 : Q') ≤ B513 * w0 := by decide
  have h1 : B513 * w0 ≤ 1 := by decide
  refine Q'.le_trans' _ _ _ (fPoly_l1 (by decide) links N p M) ?_
  refine Q'.le_trans' _ _ _ (charEnv_inv (c := epsL) h0 h1 (by decide) M) ?_
  have hr0 : (0 : Q') ≤ epsL * (Q'.ofNat 4 * (B513 * w0) ^ 3) ^ M :=
    Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) _)
  refine YMGap.Continuum.SignedPolymerKP.le_of_eqv_add (S := epsL * (Q'.ofNat 4 * (B513 * w0) ^ 3) ^ M) ?_ hr0
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0) ((V 0 + -(V 1)) + V 1) (by decide)
    (fun | 0 => epsL | _ => epsL * (Q'.ofNat 4 * (B513 * w0) ^ 3) ^ M)

/-! ## 6. Polymer products -/

def prodPoly (F : Z4Plaq → RatPoly) : List Z4Plaq → RatPoly
  | [] => polyOne
  | p :: ps => polyMul (F p) (prodPoly F ps)

theorem prod_l1 (F : Z4Plaq → RatPoly) (c : Q') (hc0 : (0 : Q') ≤ c) (hF : ∀ p, l1 (F p) ≤ c) :
    ∀ γ : List Z4Plaq, l1 (prodPoly F γ) ≤ c ^ γ.length
  | [] => by show Q'.abs 1 + 0 ≤ 1; decide
  | p :: ps => Q'.le_trans' _ _ _ (l1_mul _ _) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hF p) (l1_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (prod_l1 F c hc0 hF ps) hc0))

/-- **True-activity bound (PROVED):** `|∫ Π_{p∈γ} f_p| ≤ ε_L^{|γ|}` at `w₀`. -/
theorem activity_bound (n : Nat) (links : List Z4Link) (N M : Nat) (γ : List Z4Plaq) :
    Q'.abs (quaternionHaar n (prodPoly (fun p => fPoly w0 links N p M) γ)) ≤ epsL ^ γ.length :=
  Q'.le_trans' _ _ _ (haar_abs n _) (prod_l1 _ epsL (by decide) (fun p => fPoly_pass links N p M) γ)

end YMGap.Continuum.SU2HaarL1Activity
