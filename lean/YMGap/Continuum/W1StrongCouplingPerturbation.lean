/-
# V2 finite check: W = 1 single-plaquette transfer, electric diagonal plus magnetic
# perturbation, certified operator-norm bound `‖T x‖ ≤ (λ_lead + ε(w)) ‖x‖`

ADDITIVE.  **MODEL, not the true slab.**

Model.  Gauge-invariant sector of a single spatial plaquette (W = 1): class functions
of the plaquette holonomy, character basis `χ_s` (`s = 2j`).  Electric (heat-kernel on
the 4 links) transfer: `E χ_s = w^{4 c4(s)} χ_s`, with `c4 s = s(s+2)`.  Magnetic factor
LINEARIZED: `M = 1 + κ·(mult. by χ₁)`, and `χ₁ χ_s = χ_{s-1} + χ_{s+1}`.  Symmetrized
transfer `T = E^{1/2} M E^{1/2}`:
`T_ss = w^{4c4(s)}`, `T_{s,s±1} = κ w^{2c4(s)+2c4(s±1)}` (all exact rationals).

Truncation.  `T` is COMPRESSED to the excited span `{χ₁, χ₂, χ₃}`.  This drops the
vacuum coupling `T_{01} = κ w^{6}` (so it is the compression to `span{χ₁..χ₃}`, not the
`vac⊥` block of the perturbed operator) and drops all modes `s ≥ 4`.  The tail is NOT
formalized here (see the scope note).

* `cs3` (PROVED): weighted Cauchy–Schwarz `(ax+by+cz)² ≤ (a+b+c)(ax²+by²+cz²)`.
* `schur3` (PROVED): Schur/row-sum test for a symmetric nonnegative 3×3 matrix,
  `‖Tx‖² ≤ ρ²‖x‖²` for EVERY rational `x`, a genuine operator-norm bound.
* `lambdaLead w = w^{12}` (spin-½ electric eigenvalue), `eps κ w = κ·w^{22}`.
* `w1_norm_bound_1024` and `w1_norm_bound_half` (PROVED, exact): at `κ = 1` and
  `w = 1/1024` (resp. `w = 1/2`), `‖T x‖² ≤ (w^{12} + w^{22})² ‖x‖²` on the truncation.

PLUMBING (group-blind): `cs3`, `schur3`.  SU(2) content: `c4` and `χ₁χ_s` fusion.
Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.W1StrongCouplingPerturbation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Constructive.SumOfSquares (q_mul_self_nonneg)

theorem cs3 (a b c x y z : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) (hc : (0 : Q') ≤ c) :
    (a * x + b * y + c * z) * (a * x + b * y + c * z) ≤
      (a + b + c) * (a * (x * x) + b * (y * y) + c * (z * z)) := by
  have hid : ((a + b + c) * (a * (x * x) + b * (y * y) + c * (z * z))).eqv
      ((a * x + b * y + c * z) * (a * x + b * y + c * z) +
        ((a * b) * ((x + -y) * (x + -y)) + (a * c) * ((x + -z) * (x + -z)) +
          (b * c) * ((y + -z) * (y + -z)))) :=
    poly_identity_of_normal_eq
      (.mul (.add (.add (.var 0) (.var 1)) (.var 2))
        (.add (.add (.mul (.var 0) (.mul (.var 3) (.var 3))) (.mul (.var 1) (.mul (.var 4) (.var 4))))
          (.mul (.var 2) (.mul (.var 5) (.var 5)))))
      (.add (.mul (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 5)))
          (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 5))))
        (.add (.add
          (.mul (.mul (.var 0) (.var 1)) (.mul (.add (.var 3) (.neg (.var 4))) (.add (.var 3) (.neg (.var 4)))))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.add (.var 3) (.neg (.var 5))) (.add (.var 3) (.neg (.var 5))))))
          (.mul (.mul (.var 1) (.var 2)) (.mul (.add (.var 4) (.neg (.var 5))) (.add (.var 4) (.neg (.var 5)))))))
      (by decide)
      (fun | 0 => a | 1 => b | 2 => c | 3 => x | 4 => y | _ => z)
  have hnn : (0 : Q') ≤ (a * b) * ((x + -y) * (x + -y)) + (a * c) * ((x + -z) * (x + -z)) +
      (b * c) * ((y + -z) * (y + -z)) :=
    Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha hb) (q_mul_self_nonneg _))
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha hc) (q_mul_self_nonneg _)))
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hb hc) (q_mul_self_nonneg _))
  have hle : (a * x + b * y + c * z) * (a * x + b * y + c * z) ≤
      (a * x + b * y + c * z) * (a * x + b * y + c * z) +
        ((a * b) * ((x + -y) * (x + -y)) + (a * c) * ((x + -z) * (x + -z)) +
          (b * c) * ((y + -z) * (y + -z))) := by
    have h := Q'.add_le_add
      (Q'.le_refl' ((a * x + b * y + c * z) * (a * x + b * y + c * z))) hnn
    rwa [Q'.add_zero'] at h
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (Q'.eqv_symm hid))

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

/-- Schur / row-sum test for a symmetric nonnegative 3×3 matrix
`[[a,d,e],[d,b,f],[e,f,c]]`: `‖Tx‖² ≤ ρ²‖x‖²` for every rational `x`. -/
theorem schur3 (a b c d e f ρ x y z : Q')
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) (hc : (0 : Q') ≤ c)
    (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e) (hf : (0 : Q') ≤ f) (hρ : (0 : Q') ≤ ρ)
    (h1 : a + d + e ≤ ρ) (h2 : d + b + f ≤ ρ) (h3 : e + f + c ≤ ρ) :
    (a * x + d * y + e * z) * (a * x + d * y + e * z) +
      (d * x + b * y + f * z) * (d * x + b * y + f * z) +
      (e * x + f * y + c * z) * (e * x + f * y + c * z) ≤
    ρ * ρ * (x * x + y * y + z * z) := by
  have hx := q_mul_self_nonneg x
  have hy := q_mul_self_nonneg y
  have hz := q_mul_self_nonneg z
  have wnn : ∀ p q r : Q', (0 : Q') ≤ p → (0 : Q') ≤ q → (0 : Q') ≤ r →
      (0 : Q') ≤ p * (x * x) + q * (y * y) + r * (z * z) := fun p q r hp hq hr =>
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hp hx) (Q'.mul_nonneg _ _ hq hy))
      (Q'.mul_nonneg _ _ hr hz)
  have s1 := Q'.le_trans' _ _ _ (cs3 a d e x y z ha hd he)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h1 (wnn a d e ha hd he))
  have s2 := Q'.le_trans' _ _ _ (cs3 d b f x y z hd hb hf)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h2 (wnn d b f hd hb hf))
  have s3 := Q'.le_trans' _ _ _ (cs3 e f c x y z he hf hc)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h3 (wnn e f c he hf hc))
  have hsum := Q'.add_le_add (Q'.add_le_add s1 s2) s3
  let V := PolyExpr.var
  let env : Nat → Q' := fun
    | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f
    | 6 => x | 7 => y | 8 => z | _ => ρ
  have hid1 : (ρ * (a * (x * x) + d * (y * y) + e * (z * z)) +
      ρ * (d * (x * x) + b * (y * y) + f * (z * z)) +
      ρ * (e * (x * x) + f * (y * y) + c * (z * z))).eqv
      (ρ * ((a + d + e) * (x * x) + (d + b + f) * (y * y) + (e + f + c) * (z * z))) :=
    poly_identity_of_normal_eq
      (V 9 * (V 0 * (V 6 * V 6) + V 3 * (V 7 * V 7) + V 4 * (V 8 * V 8)) +
        V 9 * (V 3 * (V 6 * V 6) + V 1 * (V 7 * V 7) + V 5 * (V 8 * V 8)) +
        V 9 * (V 4 * (V 6 * V 6) + V 5 * (V 7 * V 7) + V 2 * (V 8 * V 8)))
      (V 9 * ((V 0 + V 3 + V 4) * (V 6 * V 6) + (V 3 + V 1 + V 5) * (V 7 * V 7) +
        (V 4 + V 5 + V 2) * (V 8 * V 8)))
      (by decide) env
  have hcol : (a + d + e) * (x * x) + (d + b + f) * (y * y) + (e + f + c) * (z * z) ≤
      ρ * (x * x) + ρ * (y * y) + ρ * (z * z) :=
    Q'.add_le_add (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_right _ _ _ h1 hx)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h2 hy)) (Q'.mul_le_mul_of_nonneg_right _ _ _ h3 hz)
  have hid2 : (ρ * (ρ * (x * x) + ρ * (y * y) + ρ * (z * z))).eqv
      (ρ * ρ * (x * x + y * y + z * z)) :=
    poly_identity_of_normal_eq
      (V 9 * (V 9 * (V 6 * V 6) + V 9 * (V 7 * V 7) + V 9 * (V 8 * V 8)))
      (V 9 * V 9 * (V 6 * V 6 + V 7 * V 7 + V 8 * V 8))
      (by decide) env
  refine Q'.le_trans' _ _ _ hsum ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hid1) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ ρ hcol hρ) ?_
  exact Q'.le_of_eqv hid2

/-! ## The W = 1 model, truncated to `{χ₁, χ₂, χ₃}`, magnetic weight `κ = 1` -/

def lambdaLead (w : Q') : Q' := w ^ 12
def eps (κ w : Q') : Q' := κ * w ^ 22

/-- Truncated transfer entries (κ = 1): diag `w^{4c4(s)}`, `s = 1,2,3` → `w^12, w^32, w^60`;
off-diagonal `w^{2c4(s)+2c4(s+1)}` → `w^22` (1–2), `w^46` (2–3); no 1–3 coupling. -/
def normSqTx (w x y z : Q') : Q' :=
  (w ^ 12 * x + w ^ 22 * y + 0 * z) * (w ^ 12 * x + w ^ 22 * y + 0 * z) +
  (w ^ 22 * x + w ^ 32 * y + w ^ 46 * z) * (w ^ 22 * x + w ^ 32 * y + w ^ 46 * z) +
  (0 * x + w ^ 46 * y + w ^ 60 * z) * (0 * x + w ^ 46 * y + w ^ 60 * z)

theorem w1_norm_bound_of_rows (w : Q') (hw : (0 : Q') ≤ w ^ 12 ∧ (0 : Q') ≤ w ^ 22 ∧
      (0 : Q') ≤ w ^ 32 ∧ (0 : Q') ≤ w ^ 46 ∧ (0 : Q') ≤ w ^ 60)
    (h2 : w ^ 22 + w ^ 32 + w ^ 46 ≤ lambdaLead w + eps 1 w)
    (h3 : 0 + w ^ 46 + w ^ 60 ≤ lambdaLead w + eps 1 w)
    (h1 : w ^ 12 + w ^ 22 + 0 ≤ lambdaLead w + eps 1 w)
    (x y z : Q') :
    normSqTx w x y z ≤
      (lambdaLead w + eps 1 w) * (lambdaLead w + eps 1 w) * (x * x + y * y + z * z) :=
  schur3 (w ^ 12) (w ^ 32) (w ^ 60) (w ^ 22) 0 (w ^ 46) _ x y z hw.1 hw.2.2.1 hw.2.2.2.2
    hw.2.1 (Q'.le_refl' 0) hw.2.2.2.1
    (Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hw.1 hw.2.1) (Q'.le_refl' 0)) h1)
    h1 h2 h3

def w1024 : Q' := Q'.mkPos 1 1024 (by decide)
def wHalf : Q' := Q'.mkPos 1 2 (by decide)

set_option maxRecDepth 100000 in
/-- **Certified (exact), w = 1/1024, κ = 1**: `‖Tx‖ ≤ (w^12 + w^22)‖x‖` on the truncation. -/
theorem w1_norm_bound_1024 (x y z : Q') :
    normSqTx w1024 x y z ≤ (lambdaLead w1024 + eps 1 w1024) *
      (lambdaLead w1024 + eps 1 w1024) * (x * x + y * y + z * z) :=
  w1_norm_bound_of_rows w1024 (by decide) (by decide) (by decide) (by decide) x y z

set_option maxRecDepth 100000 in
/-- **Certified (exact), w = 1/2, κ = 1**. -/
theorem w1_norm_bound_half (x y z : Q') :
    normSqTx wHalf x y z ≤ (lambdaLead wHalf + eps 1 wHalf) *
      (lambdaLead wHalf + eps 1 wHalf) * (x * x + y * y + z * z) :=
  w1_norm_bound_of_rows wHalf (by decide) (by decide) (by decide) (by decide) x y z

end YMGap.Continuum.W1StrongCouplingPerturbation

#print axioms YMGap.Continuum.W1StrongCouplingPerturbation.cs3
#print axioms YMGap.Continuum.W1StrongCouplingPerturbation.schur3
#print axioms YMGap.Continuum.W1StrongCouplingPerturbation.w1_norm_bound_1024
#print axioms YMGap.Continuum.W1StrongCouplingPerturbation.w1_norm_bound_half
