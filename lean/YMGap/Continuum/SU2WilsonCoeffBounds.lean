/-
# Wilson action, commit 2: rational bounds on the truncated Wilson character coefficients

**STRONG COUPLING ONLY (β ≲ 1e-4).** This is a volume-uniform strong-coupling cluster-expansion
input for the actual Wilson action, and it is equally true for U(1). It is NOT mass-gap or
continuum evidence.

For any coefficient sequence `a` (Wilson: `a_k = λ^k/k!`, `λ = β/2`), with
`c_s = wCoeff a K s` the exact character coefficients of `T_K = Σ_{k≤K} a_k χ_1^k`:

* `dim_identity` : `Σ_{s≤K} (s+1) c_s ≈ Σ_{k≤K} a_k 2^k`. This is evaluation at the identity, `x = 1`,
  via the coefficient-sum functional `V`, so it needs no combinatorics.
* `bSum_wList`   : `bSum [(c_s, s) | s = 1..K] + c_0 ≈ Σ_{s≤K}(s+1)c_s` for `c ≥ 0`.
* `centred_envelope` : the two combined, `B_K + c_0 ≈ Σ_{k≤K} a_k 2^k`.
* `mult_nonneg`, `mult_diag`, `wCoeff_nonneg`, `wCoeff_ge_diag`: give `c_s ≥ a_s` and `c_0 ≥ a_0`.
No reciprocals are used.
-/

import YMGap.Continuum.SU2WilsonCharacterPower
import YMGap.Continuum.SU2PolymerActivityBound

namespace YMGap.Continuum.SU2WilsonCoeffBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2CharacterSquareIdentity (U)
open YMGap.Continuum.SU2WilsonCharacterPower
open YMGap.Continuum.SU2PolymerActivityBound (bSum)
open YMGap.Continuum.SU2PlaqWeightedCharacterBound (ofInt_add')

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≅ " => RatPolyCoeffEqv

theorem add_nonneg' {a b : Q'} (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) : (0 : Q') ≤ a + b := by
  rw [Q'.zero_le_iff_num_nonneg] at ha hb ⊢
  show 0 ≤ a.num * (b.den : Int) + b.num * (a.den : Int)
  exact Int.add_nonneg (Int.mul_nonneg ha (Int.natCast_nonneg _)) (Int.mul_nonneg hb (Int.natCast_nonneg _))

theorem ofInt_mul' (a b : Int) : Q'.ofInt a * Q'.ofInt b ≈ Q'.ofInt (a * b) := by
  show (a * b) * ((0 + 1 : Nat) : Int) = (a * b) * (((0 + 1) * (0 + 1) - 1 + 1 : Nat) : Int)
  simp only [Nat.zero_add, Nat.mul_one, Nat.sub_self, Int.natCast_one, Int.mul_one]

theorem zero_add_q (a : Q') : (0 + a) ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (YMGap.Constructive.QPoly.q_add_zero_eqv a)

/-! ## The coefficient-sum functional (evaluation at the identity) -/

def V (p : RatPoly) : Q' := ratWeightedSum (fun _ => (1 : Q')) p

theorem V_congr {p q : RatPoly} (h : p ≅ q) : V p ≈ V q := h _

theorem V_one : V polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (YMGap.Constructive.QPoly.q_add_zero_eqv _) (Q'.mul_one_eqv _)

theorem V_two_mul (p : RatPoly) : V (polyMul (polySmul 2 polyOne) p) ≈ 2 * V p :=
  Q'.eqv_trans _ _ _ (V_congr ((RatPolyCoeffEqv.polyMul_smul_left 2 polyOne p).trans
    (RatPolyCoeffEqv.smul 2 (RatPolyCoeffEqv.one_mul p)))) (ratWeightedSum_smul _ 2 p)

/-- `dim χ_s = s+1`, as `bSum` writes it. -/
def dQ (s : Nat) : Q' := Q'.ofInt ((s : Int) + 1)

theorem lin (n : Nat) : 2 * dQ (n + 1) + (-1) * dQ n ≈ dQ (n + 2) := by
  show Q'.ofInt 2 * Q'.ofInt (((n + 1 : Nat) : Int) + 1) + Q'.ofInt (-1) * Q'.ofInt ((n : Int) + 1) ≈ _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (ofInt_mul' _ _) (ofInt_mul' _ _))
    (Q'.eqv_trans _ _ _ (ofInt_add' _ _) ?_)
  have e : 2 * (((n + 1 : Nat) : Int) + 1) + -1 * ((n : Int) + 1) = ((n + 2 : Nat) : Int) + 1 := by omega
  rw [e]; exact Q'.eqv_refl _

theorem V_U : ∀ n, V (U polyOne n) ≈ dQ n
  | 0 => V_one
  | 1 => Q'.eqv_trans _ _ _ (ratWeightedSum_smul _ 2 polyOne)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ V_one) (Q'.eqv_refl _))
  | n + 2 => by
    show V (polyAdd (polyMul (polySmul 2 polyOne) (U polyOne (n + 1))) (polySmul (-1) (U polyOne n))) ≈ _
    exact Q'.eqv_trans _ _ _ (ratWeightedSum_add _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (V_two_mul _) (ratWeightedSum_smul _ (-1) _))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (V_U (n + 1)))
          (Q'.mul_eqv_congr_left _ _ _ (V_U n))) (lin n)))

/-- `Σ_{s≤D} c_s (s+1)`. -/
def dsum (c : Nat → Q') : Nat → Q'
  | 0 => c 0 * dQ 0
  | D + 1 => dsum c D + c (D + 1) * dQ (D + 1)

theorem V_cc (c : Nat → Q') : ∀ D, V (cc polyOne c D) ≈ dsum c D
  | 0 => Q'.eqv_trans _ _ _ (ratWeightedSum_smul _ _ _) (Q'.mul_eqv_congr_left _ _ _ (V_U 0))
  | D + 1 => Q'.eqv_trans _ _ _ (ratWeightedSum_add _ _ _) (Q'.add_eqv_congr' (V_cc c D)
      (Q'.eqv_trans _ _ _ (ratWeightedSum_smul _ _ _) (Q'.mul_eqv_congr_left _ _ _ (V_U _))))

def pow2 : Nat → Q'
  | 0 => 1
  | k + 1 => 2 * pow2 k

theorem V_chiPow : ∀ k, V (chiPow polyOne k) ≈ pow2 k
  | 0 => V_one
  | k + 1 => Q'.eqv_trans _ _ _ (V_two_mul _) (Q'.mul_eqv_congr_left _ _ _ (V_chiPow k))

/-- `Σ_{k≤K} a_k 2^k`. -/
def wsum (a : Nat → Q') : Nat → Q'
  | 0 => a 0 * pow2 0
  | K + 1 => wsum a K + a (K + 1) * pow2 (K + 1)

theorem V_wilson (a : Nat → Q') : ∀ K, V (wilsonPoly polyOne a K) ≈ wsum a K
  | 0 => Q'.eqv_trans _ _ _ (ratWeightedSum_smul _ _ _) (Q'.mul_eqv_congr_left _ _ _ (V_chiPow 0))
  | K + 1 => Q'.eqv_trans _ _ _ (ratWeightedSum_add _ _ _) (Q'.add_eqv_congr' (V_wilson a K)
      (Q'.eqv_trans _ _ _ (ratWeightedSum_smul _ _ _) (Q'.mul_eqv_congr_left _ _ _ (V_chiPow _))))

/-- **Dimension identity**: `Σ_{s≤K} (s+1) c_s^{(K)} ≈ Σ_{k≤K} a_k 2^k`. -/
theorem dim_identity (a : Nat → Q') (K : Nat) : dsum (wCoeff a K) K ≈ wsum a K :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (V_cc _ K))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (V_congr (wilsonPoly_expand polyOne a K))) (V_wilson a K))

/-! ## Centred list and its `bSum` -/

/-- `[(c_j, j), …, (c_1, 1)]`: the centred character list (s = 0 dropped). -/
def wList (c : Nat → Q') : Nat → List (Q' × Nat)
  | 0 => []
  | j + 1 => (c (j + 1), j + 1) :: wList c j

private theorem abs_nn {q : Q'} (h : (0 : Q') ≤ q) : Q'.abs q = q := if_pos h

theorem bSum_wList (c : Nat → Q') (hc : ∀ s, (0 : Q') ≤ c s) :
    ∀ j, bSum (wList c j) + c 0 * dQ 0 ≈ dsum c j
  | 0 => zero_add_q _
  | j + 1 => by
    show (Q'.abs (c (j + 1)) * dQ (j + 1) + bSum (wList c j)) + c 0 * dQ 0 ≈
      dsum c j + c (j + 1) * dQ (j + 1)
    rw [abs_nn (hc (j + 1))]
    exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (bSum_wList c hc j)) (Q'.add_comm_eqv _ _))

/-! ## Positivity -/

theorem mult_nonneg : ∀ k s, (0 : Q') ≤ mult k s
  | 0, 0 => by decide
  | 0, _ + 1 => Q'.le_refl' _
  | k + 1, 0 => add_nonneg' (Q'.le_refl' _) (mult_nonneg k 1)
  | k + 1, s + 1 => add_nonneg' (mult_nonneg k s) (mult_nonneg k (s + 2))

theorem mult_diag : ∀ s, mult s s ≈ 1
  | 0 => Q'.eqv_refl _
  | s + 1 => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (mult_diag s) (mult_vanish s (s + 2) (by omega)))
      (YMGap.Constructive.QPoly.q_add_zero_eqv _)

theorem wCoeff_nonneg (a : Nat → Q') (ha : ∀ k, (0 : Q') ≤ a k) : ∀ K s, (0 : Q') ≤ wCoeff a K s
  | 0, s => Q'.mul_nonneg _ _ (ha 0) (mult_nonneg 0 s)
  | K + 1, s => add_nonneg' (wCoeff_nonneg a ha K s) (Q'.mul_nonneg _ _ (ha _) (mult_nonneg _ s))

/-- `a_s ≤ c_s^{(K)}` for `s ≤ K` (the diagonal term `a_s · mult s s`). -/
theorem wCoeff_ge_diag (a : Nat → Q') (ha : ∀ k, (0 : Q') ≤ a k) (s : Nat) :
    ∀ K, s ≤ K → a s ≤ wCoeff a K s
  | 0, h => by
    have : s = 0 := by omega
    subst this
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mult_diag 0))
      (Q'.mul_one_eqv _)))
  | K + 1, h => by
    by_cases hs : s = K + 1
    · subst hs
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (zero_add_q _))) ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (wCoeff_nonneg a ha K (K + 1))) ?_
      exact Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mult_diag _)) (Q'.mul_one_eqv _))))
    · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (YMGap.Constructive.QPoly.q_add_zero_eqv _))) ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (wCoeff_ge_diag a ha s K (by omega))) ?_
      exact Q'.add_le_add_left _ _ _ (Q'.mul_nonneg _ _ (ha _) (mult_nonneg _ s))

/-- **Centred envelope identity** (unnormalised, no reciprocal):
`bSum [(c_s, s) | s = 1..K] + c_0 ≈ Σ_{k≤K} a_k 2^k`. STRONG COUPLING ONLY input. -/
theorem centred_envelope (a : Nat → Q') (ha : ∀ k, (0 : Q') ≤ a k) (K : Nat) :
    bSum (wList (wCoeff a K) K) + wCoeff a K 0 * dQ 0 ≈ wsum a K :=
  Q'.eqv_trans _ _ _ (bSum_wList _ (wCoeff_nonneg a ha K) K) (dim_identity a K)

end YMGap.Continuum.SU2WilsonCoeffBounds

#print axioms YMGap.Continuum.SU2WilsonCoeffBounds.dim_identity
#print axioms YMGap.Continuum.SU2WilsonCoeffBounds.centred_envelope
#print axioms YMGap.Continuum.SU2WilsonCoeffBounds.wCoeff_ge_diag
