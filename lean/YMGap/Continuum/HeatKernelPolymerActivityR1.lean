/-
# R1 wall, activity side: an explicit heat-kernel polymer activity obeying `|z| ≤ ε^{|γ|}`

ADDITIVE.  **GROUP-BLIND PLUMBING** for the KP use (U(1) rule).  The activity
envelope is SU(2) heat-kernel arithmetic.

* Envelope (corrected 2026-10-07): `charEnv w M = Σ_{s=1}^{M} (s+1)²·w^{s(s+2)}`.  Each
  term is the repo weight `coeffW w s = (s+1)w^{s(s+2)}` times the character sup bound
  `|χ_s| ≤ s+1`.  That bound is a second factor of `(s+1)`; it is NOT absorbed in
  `coeffW`.
* `charEnv_pass`: at `w = 1/40`, `0 ≤ charEnv ≤ ε = 1/10000` for every M.  The proof uses a
  geometric bound with ratio `4w³` (`(s+1)² ≤ 4^s`, `s(s+2) ≥ 3s`).
* `charEnv_fail`: at `w = 1/20`, `charEnv > ε` for every M ≥ 1, because the s=1 term is
  `4w³ = 1/2000`.  So the KP threshold `w*` is certified to lie in `[1/40, 1/20)`.
* `zHeat M γ := (charEnv (1/40) M)^{|γ|}`.  `zHeat_bounds` gives `0 ≤ zHeat ≤ ε^{|γ|}`, the
  two-sided bound.
* `heat_kp`: the KP bound, which needs only the lower bound `z ≥ −ε^{|X|}`, together with the
  one-polymer ratio-Lipschitz bound, which needs the two-sided `|z| ≤ ε^{|X|}`.  Both hold on
  any degree-24 gas.

**OPEN (the actual R1 wall):** this does not prove that the Wilson heat-kernel partition
function equals `Ξ` of a gas with activity `zHeat`, or one bounded by it.  The minimal missing
identity is:

  `∫ Π_p (Σ_{s≤M} coeffW w s · χ_s(U_p)) dU  =  Σ_{compatible families}  Π_γ z_true(γ)`,

where `z_true(γ)` is the Haar integral of the connected character products over `γ`.  It
must come with the bound `|z_true(γ)| ≤ zHeat M γ`.  That bound uses `|χ_s| ≤ s+1`, which
`charEnv` accounts for explicitly.  No file proves the Haar/character expansion to a polymer
gas.  HKPS was not imported.
-/

import YMGap.Continuum.PolymerRatioLipschitz
import YMGap.Continuum.ClusterCount

namespace YMGap.Continuum.HeatKernelPolymerActivityR1

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.BddLatticeAnimal (BddLattice)
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerRatioLipschitz

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

def wR1 : Q' := Q'.mkPos 1 40 (by decide)
def wFail : Q' := Q'.mkPos 1 20 (by decide)

/-- Character-bounded excited term `(s+1)²·w^{s(s+2)}`: the `coeffW` weight `(s+1)w^{C₄}` times
the sup bound `|χ_s| ≤ s+1`. -/
def envTerm (w : Q') (s : Nat) : Q' := Q'.ofNat ((s + 1) * (s + 1)) * w ^ (s * (s + 2))

/-- `charEnv w M = Σ_{s=1}^{M} (s+1)² w^{s(s+2)}`. -/
def charEnv (w : Q') : Nat → Q'
  | 0 => 0
  | M + 1 => charEnv w M + envTerm w (M + 1)

theorem pow_add' (w : Q') (a : Nat) : ∀ b : Nat, (w ^ (a + b)).eqv (w ^ a * w ^ b)
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv _)
  | b + 1 => by
    show (w * w ^ (a + b)).eqv (w ^ a * (w * w ^ b))
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (pow_add' w a b)) ?_
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 1 * (V 0 * V 2)) (by decide)
      (fun | 0 => w | 1 => w ^ a | _ => w ^ b)

theorem pow_anti {w : Q'} (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) (a : Nat) :
    ∀ k : Nat, w ^ (a + k) ≤ w ^ a
  | 0 => Q'.le_refl' _
  | k + 1 => by
    show w * w ^ (a + k) ≤ w ^ a
    have hp : (0 : Q') ≤ w ^ (a + k) := Q'.pow_nonneg _ h0 _
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h1 hp)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) (pow_anti h0 h1 a k))

theorem exp_le (s : Nat) : s * (s + 2) + 3 ≤ (s + 1) * (s + 1 + 2) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
  omega

theorem pow_c4_le {w : Q'} (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) :
    ∀ s : Nat, w ^ (s * (s + 2)) ≤ (w ^ 3) ^ s
  | 0 => Q'.le_refl' _
  | s + 1 => by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (exp_le s)
    rw [hk]
    show w ^ (s * (s + 2) + 3 + k) ≤ w ^ 3 * (w ^ 3) ^ s
    refine Q'.le_trans' _ _ _ (pow_anti h0 h1 _ k) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (pow_add' w _ 3)) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (pow_c4_le h0 h1 s)
      (Q'.pow_nonneg _ h0 _)) (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

theorem sq_le_four_pow : ∀ s : Nat, (s + 1) * (s + 1) ≤ 4 ^ s
  | 0 => Nat.le_refl _
  | s + 1 => by
    have h2 : s + 1 + 1 ≤ 2 * (s + 1) := by
      rw [Nat.two_mul]; exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le s)) _
    refine Nat.le_trans (Nat.mul_le_mul h2 h2) ?_
    rw [Nat.mul_mul_mul_comm, Nat.pow_succ, Nat.mul_comm (4 ^ s) 4]
    exact Nat.mul_le_mul_left 4 (sq_le_four_pow s)

theorem ofNat_pow4 : ∀ s : Nat, (Q'.ofNat (4 ^ s)).eqv (Q'.ofNat 4 ^ s)
  | 0 => Q'.eqv_refl _
  | s + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm]
    refine Q'.eqv_trans _ _ _ (YMGap.Continuum.ClusterCount.ofNat_mul_eqv 4 (4 ^ s)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (ofNat_pow4 s)

theorem envTerm_le {w : Q'} (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) (s : Nat) :
    envTerm w s ≤ (Q'.ofNat 4 * w ^ 3) ^ s := by
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (ofNat_le' (sq_le_four_pow s)) (Q'.pow_nonneg _ h0 _)) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_c4_le h0 h1 s)
    (YMGap.Continuum.ClusterCount.ofNat_nonneg _)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (ofNat_pow4 s))) ?_
  exact Q'.le_of_eqv (mul_pow' _ _ s)

theorem envTerm_nonneg {w : Q'} (h0 : (0 : Q') ≤ w) (s : Nat) : (0 : Q') ≤ envTerm w s :=
  Q'.mul_nonneg _ _ (YMGap.Continuum.ClusterCount.ofNat_nonneg _) (Q'.pow_nonneg _ h0 _)

theorem charEnv_nonneg {w : Q'} (h0 : (0 : Q') ≤ w) : ∀ M, (0 : Q') ≤ charEnv w M
  | 0 => Q'.le_refl' _
  | M + 1 => Q'.zero_le_add _ _ (charEnv_nonneg h0 M) (envTerm_nonneg h0 _)

/-- Geometric invariant: `charEnv w M ≤ c − c·r^M` when `r(1+c) ≤ c`, `r = 4w³`. -/
theorem charEnv_inv {w c : Q'} (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1)
    (hr : Q'.ofNat 4 * w ^ 3 * (1 + c) ≤ c) :
    ∀ M, charEnv w M ≤ c + -(c * (Q'.ofNat 4 * w ^ 3) ^ M)
  | 0 => by
    show (0 : Q') ≤ c + -(c * 1)
    let V := PolyExpr.var
    exact Q'.le_of_eqv (Q'.eqv_symm (poly_identity_of_normal_eq (V 0 + -(V 0 * PolyExpr.const 1))
      (PolyExpr.const 0) (by decide) (fun _ => c)))
  | M + 1 => by
    let r := Q'.ofNat 4 * w ^ 3
    have hrM : (0 : Q') ≤ r ^ M :=
      Q'.pow_nonneg _ (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ h0 _)) _
    have hS : (0 : Q') ≤ (c + -(r * (1 + c))) * r ^ M :=
      Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hr) hrM
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (charEnv_inv h0 h1 hr M) (envTerm_le h0 h1 (M + 1))) ?_
    refine le_of_eqv_add (S := (c + -(r * (1 + c))) * r ^ M) ?_ hS
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + -(V 0 * (V 1 * V 2)))
      ((V 0 + -(V 0 * V 2) + V 1 * V 2) + (V 0 + -(V 1 * (PolyExpr.const 1 + V 0))) * V 2)
      (by decide) (fun | 0 => c | 1 => r | _ => r ^ M)

/-- **Passing nome (PROVED):** at `w = 1/40`, `0 ≤ charEnv w M ≤ 1/10000` for every `M`. -/
theorem charEnv_pass (M : Nat) : (0 : Q') ≤ charEnv wR1 M ∧ charEnv wR1 M ≤ epsZ := by
  have h0 : (0 : Q') ≤ wR1 := by decide
  have h1 : wR1 ≤ 1 := by decide
  refine ⟨charEnv_nonneg h0 M, Q'.le_trans' _ _ _ (charEnv_inv (c := epsZ) h0 h1 (by decide) M) ?_⟩
  have hr0 : (0 : Q') ≤ epsZ * (Q'.ofNat 4 * wR1 ^ 3) ^ M :=
    Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) _)
  refine le_of_eqv_add (S := epsZ * (Q'.ofNat 4 * wR1 ^ 3) ^ M) ?_ hr0
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0) ((V 0 + -(V 1)) + V 1) (by decide)
    (fun | 0 => epsZ | _ => epsZ * (Q'.ofNat 4 * wR1 ^ 3) ^ M)

theorem charEnv_mono {w : Q'} (h0 : (0 : Q') ≤ w) (M : Nat) : charEnv w 1 ≤ charEnv w (M + 1) := by
  induction M with
  | zero => exact Q'.le_refl' _
  | succ k ih => exact Q'.le_trans' _ _ _ ih (Q'.add_le_self_of_nonneg _ _ (envTerm_nonneg h0 _))

/-- **Failing nome (PROVED):** at `w = 1/20` the `s = 1` term alone is `4w³ = 1/2000 > ε`, so
`charEnv w M ≤ 1/10000` fails for every `M ≥ 1`.  The certified threshold interval is
`1/40 ≤ w* < 1/20`. -/
theorem charEnv_fail (M : Nat) : ¬ (charEnv wFail (M + 1) ≤ epsZ) := fun h =>
  (by decide : ¬ (charEnv wFail 1 ≤ epsZ))
    (Q'.le_trans' _ _ _ (charEnv_mono (by decide) M) h)

variable {BL : BddLattice}

def zHeat (M : Nat) (γ : Poly BL) : Q' := charEnv wR1 M ^ sz γ

theorem zHeat_bounds (M : Nat) (γ : Poly BL) :
    (0 : Q') ≤ zHeat M γ ∧ zHeat M γ ≤ epsZ ^ sz γ :=
  ⟨Q'.pow_nonneg _ (charEnv_pass M).1 _,
    pow_le_pow_base' (charEnv_pass M).1 (charEnv_pass M).2 _⟩

/-- **KP and ratio-Lipschitz for the explicit heat-kernel activity (PROVED).** -/
theorem heat_kp (hD : BL.D = 24) (d : PL BL) (B : Z4BoxGas BL) (M : Nat) :
    (((0 : Q') ≤ Xi (zHeat M) shareB B.polys ∧
      ∀ p b r, B.polys = p ++ b :: r →
        Xi (zHeat M) shareB (p ++ r) ≤ (1 + etaZ ^ sz b) * Xi (zHeat M) shareB B.polys) ∧
      (1 : Q') ≤ prodm (fun x => 1 + etaZ ^ sz x) B.polys * Xi (zHeat M) shareB B.polys) ∧
    ∀ (y : Poly BL) (S₀ T₀ : List (Poly BL)), S₀.Sublist B.polys → T₀.Sublist B.polys →
      Xi (zHeat M) shareB (y :: S₀) * Xi (zHeat M) shareB T₀ +
          -(Xi (zHeat M) shareB (y :: T₀) * Xi (zHeat M) shareB S₀) ≤
        (epsZ ^ sz y * (five3 ^ sz y + five3 ^ sz y)) *
          (Xi (zHeat M) shareB S₀ * Xi (zHeat M) shareB T₀) ∧
      (0 : Q') ≤ Xi (zHeat M) shareB (y :: S₀) * Xi (zHeat M) shareB T₀ +
          -(Xi (zHeat M) shareB (y :: T₀) * Xi (zHeat M) shareB S₀) +
        (epsZ ^ sz y * (five3 ^ sz y + five3 ^ sz y)) *
          (Xi (zHeat M) shareB S₀ * Xi (zHeat M) shareB T₀) := by
  have hz1 : ∀ X : Poly BL, (0 : Q') ≤ zHeat M X + epsZ ^ sz X :=
    fun X => Q'.zero_le_add _ _ (zHeat_bounds M X).1 (Q'.pow_nonneg _ (by decide) _)
  have hz2 : ∀ X : Poly BL, zHeat M X ≤ epsZ ^ sz X := fun X => (zHeat_bounds M X).2
  exact ⟨deg24_kp hD d B (zHeat M) hz1,
    fun y S₀ T₀ hS hT => deg24_ratio_lip hD d B (zHeat M) hz1 hz2 y S₀ T₀ hS hT⟩

end YMGap.Continuum.HeatKernelPolymerActivityR1

#print axioms YMGap.Continuum.HeatKernelPolymerActivityR1.charEnv_pass
#print axioms YMGap.Continuum.HeatKernelPolymerActivityR1.charEnv_fail
#print axioms YMGap.Continuum.HeatKernelPolymerActivityR1.zHeat_bounds
#print axioms YMGap.Continuum.HeatKernelPolymerActivityR1.heat_kp
