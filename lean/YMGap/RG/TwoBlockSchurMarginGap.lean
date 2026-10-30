/-
# Two-Block Schur-Margin Gap Assembly (Hayakawa `2609.39802`, Lemma 9 + Proposition 8)

**Label: linear-algebraic gap-assembly INFRASTRUCTURE. NOT gap evidence. NOT a proof of the
Yang–Mills mass gap.**

**U(1) / abelian rule.** Every statement in this file holds verbatim for *any* finite group,
including abelian ones (Z2, U(1) truncations, …): Hayakawa applies the same assembly to Kitaev
quantum-double vertex terms for every nontrivial finite group. The file converts an OPEN Schur
margin into a gap; it never produces the margin. It is therefore infrastructure, not evidence
for a non-abelian mass gap.

Source: Hayakawa `2609.39802` (*Double Localization for Quantum Gibbs Sampler Gaps*), read in
full. (The 2026-10-28 HP note mis-titles this paper as a 3D lattice YM decimation paper; it is a
quantum-double Davies-gap paper with no YM Hamiltonian.)
* Lemma 9: `K = [[A, -B†],[-B, T]] ⪰ 0`, `A ⪰ aΠ`, `T ⪰ τΠ⊥`, `S_Π(K) ⪰ ηA`, `0<η≤1`
  ⟹ `K ⪰ (1 - √(1-η)) · min(a,τ) · I`.
* Proposition 8 (first half): `K_p ⪰ g_loc E_p⊥`, `Σ E_p⊥ ⪰ κ`, `Σ K_p ⪯ r_K K`
  ⟹ `g_loc κ ⪯ r_K T` on `ran Π⊥`.

**Mathlib-free reformulation.** No square roots: `s ∈ [0,1]` plays `√(1-η)`. The cross-term
hypothesis is the AM-GM'd Cauchy–Schwarz `2·B(x,y) ≤ s·(A(x)+T(y))`, derived from the squared
form `B² ≤ s²·A·T` in `hcross_of_sq_bound` (PROVED).

PROVED: `absorb_cross`, `diag_floor`, `twoBlock_gap`, `interface_complement_floor`,
`hcross_of_sq_bound`, `relative_of_twoBlock`, `schurShape_of_twoBlock`.

OPEN (explicit hypotheses, never discharged here):
* `hA_OPEN` — the interface gap `a` (`A ⪰ a`);
* `hcross` / margin `s < 1` — the Schur margin `η > 0`; this IS the r46/r49 `hschur_OPEN`
  content in quadratic-form shape;
* `hT` / local gaps `hloc_OPEN`, cover `hcov_OPEN`, overlap `hG2_OPEN`;
* the bridge additionally needs the coarse upper bound `hupper_OPEN` (`A - C ≤ Kmax·N`), and the
  identification of these rational quadratic forms with the completed-carrier energies of
  `RelativeDissipationScaleChain.SchurDecomposition` is NOT formalized here (OPEN).
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.AbsQ
import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.RG.TwoBlockSchurMarginGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Rational helpers -/

private theorem sub_nonneg_of_le' {a b : Q'} (h : b ≤ a) : (0 : Q') ≤ a - b := by
  have h1 : b + -b ≤ a + -b := Q'.add_le_add_right b a (-b) h
  have h0 : (0 : Q') ≈ b + -b :=
    poly_identity_of_normal_eq (.const 0) (.add (.var 0) (.neg (.var 0))) (by decide) (fun _ => b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h0) h1

/-- `(1 - s)·u ≈ u + -(s·u)`. -/
private theorem one_sub_mul_eqv (s u : Q') : ((1 : Q') - s) * u ≈ u + -(s * u) :=
  poly_identity_of_normal_eq
    (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
    (.add (.var 1) (.neg (.mul (.var 0) (.var 1)))) (by decide)
    (fun | 0 => s | _ => u)

/-! ## 1. Two-block assembly (Hayakawa Lemma 9), quadratic-form level -/

/-- Quadratic-form data of `K = [[A,-B†],[-B,T]]` on `ran Π ⊕ ran Π⊥`, evaluated on
`z = x + y`: `K(x,y) = A(x) + T(y) - 2·B(x,y)` with `B(x,y) = Re⟨y, B x⟩`.
`nx`, `ny` are the squared norms. -/
structure TwoBlockForm (X Y : Type) where
  A : X → Q'
  T : Y → Q'
  B : X → Y → Q'
  K : X → Y → Q'
  nx : X → Q'
  ny : Y → Q'
  nx_nonneg : ∀ x, (0 : Q') ≤ nx x
  ny_nonneg : ∀ y, (0 : Q') ≤ ny y
  K_decomp : ∀ x y, K x y ≈ (A x + T y) + -((2 : Q') * B x y)

namespace TwoBlockForm
variable {X Y : Type} (F : TwoBlockForm X Y)

/-- **Cross-term absorption (PROVED):** `hcross` ⟹ `(1-s)(A+T) ≤ K`. -/
theorem absorb_cross (s : Q')
    (hcross : ∀ x y, (2 : Q') * F.B x y ≤ s * (F.A x + F.T y)) (x : X) (y : Y) :
    ((1 : Q') - s) * (F.A x + F.T y) ≤ F.K x y := by
  have h1 : -(s * (F.A x + F.T y)) ≤ -((2 : Q') * F.B x y) := Q'.neg_le_neg (hcross x y)
  have h2 : (F.A x + F.T y) + -(s * (F.A x + F.T y)) ≤ (F.A x + F.T y) + -((2 : Q') * F.B x y) :=
    Q'.add_le_add_left _ _ _ h1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_mul_eqv s _))
    (Q'.le_trans' _ _ _ h2 (Q'.ge_of_eqv (F.K_decomp x y)))

/-- **Diagonal floor (PROVED):** `A ⪰ a`, `T ⪰ τ` ⟹ `min(a,τ)(‖x‖²+‖y‖²) ≤ A(x)+T(y)`. -/
theorem diag_floor (a τ : Q')
    (hA : ∀ x, a * F.nx x ≤ F.A x) (hT : ∀ y, τ * F.ny y ≤ F.T y) (x : X) (y : Y) :
    Q'.min' a τ * (F.nx x + F.ny y) ≤ F.A x + F.T y := by
  have hx : Q'.min' a τ * F.nx x ≤ a * F.nx x :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.min_le_left' a τ) (F.nx_nonneg x)
  have hy : Q'.min' a τ * F.ny y ≤ τ * F.ny y :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.min_le_right' a τ) (F.ny_nonneg y)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
    (Q'.add_le_add (Q'.le_trans' _ _ _ hx (hA x)) (Q'.le_trans' _ _ _ hy (hT y)))

/-- **Hayakawa Lemma 9, rational form (PROVED from OPEN inputs `hA_OPEN hT hcross`).**
`K ⪰ (1 - s) · min(a,τ)`, with `s` standing for `√(1-η)`. -/
theorem twoBlock_gap (a τ s : Q') (hs1 : s ≤ (1 : Q'))
    (hA_OPEN : ∀ x, a * F.nx x ≤ F.A x) (hT : ∀ y, τ * F.ny y ≤ F.T y)
    (hcross : ∀ x y, (2 : Q') * F.B x y ≤ s * (F.A x + F.T y)) (x : X) (y : Y) :
    ((1 : Q') - s) * (Q'.min' a τ * (F.nx x + F.ny y)) ≤ F.K x y :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (F.diag_floor a τ hA_OPEN hT x y) (sub_nonneg_of_le' hs1))
    (F.absorb_cross s hcross x y)

end TwoBlockForm

/-! ## 2. Complement floor from local pieces (Hayakawa Prop. 8, `T ⪰ τ Π⊥`) -/

/-- Finite list sum. -/
def lsum {α : Type} (f : α → Q') : List α → Q'
  | [] => 0
  | p :: ps => f p + lsum f ps

theorem lsum_le {α : Type} (f g : α → Q') (h : ∀ p, f p ≤ g p) :
    ∀ ps : List α, lsum f ps ≤ lsum g ps
  | [] => Q'.le_refl' 0
  | p :: ps => Q'.add_le_add (h p) (lsum_le f g h ps)

/-- `Σ c·f ≈ c·Σ f`. -/
theorem lsum_smul {α : Type} (c : Q') (f : α → Q') :
    ∀ ps : List α, lsum (fun p => c * f p) ps ≈ c * lsum f ps
  | [] => poly_identity_of_normal_eq (.const 0) (.mul (.var 0) (.const 0)) (by decide) (fun _ => c)
  | p :: ps =>
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (lsum_smul c f ps))
        (poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
          (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide)
          (fun | 0 => c | 1 => f p | _ => lsum f ps))

/-- **Prop. 8, first half (PROVED from OPEN `hloc_OPEN hcov_OPEN hG2_OPEN`).**
`Tp y` = `⟨y, K_p y⟩` on `ran Π⊥`, `cov p y` = `⟨y, E_p⊥ y⟩`.
Conclusion: `g_loc · κ · ‖y‖² ≤ r_K · T(y)`. -/
theorem interface_complement_floor {α Y : Type} (ps : List α)
    (Tp : α → Y → Q') (cov : α → Y → Q') (T ny : Y → Q') (gloc κ rK : Q')
    (hg : (0 : Q') ≤ gloc)
    (hloc_OPEN : ∀ p y, gloc * cov p y ≤ Tp p y)
    (hcov_OPEN : ∀ y, κ * ny y ≤ lsum (fun p => cov p y) ps)
    (hG2_OPEN : ∀ y, lsum (fun p => Tp p y) ps ≤ rK * T y)
    (y : Y) : gloc * (κ * ny y) ≤ rK * T y := by
  have h1 : gloc * (κ * ny y) ≤ gloc * lsum (fun p => cov p y) ps :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (hcov_OPEN y) hg
  have h2 : gloc * lsum (fun p => cov p y) ps ≤ lsum (fun p => Tp p y) ps :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (lsum_smul gloc (fun p => cov p y) ps))
      (lsum_le _ _ (fun p => hloc_OPEN p y) ps)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (hG2_OPEN y))

/-! ## 3. Cross term from the squared Cauchy–Schwarz bound -/

private theorem sq_nonneg' (q : Q') : (0 : Q') ≤ q * q :=
  SumOfSquares.q_mul_self_nonneg q

/-- Degenerate case of square-root monotonicity: `0 ≤ e`, `¬ 0 < e`, `t·t ≤ e·e` ⟹ `t ≤ e`. -/
private theorem le_of_sq_le_sq_zero {t e : Q'} (he0 : (0 : Q') ≤ e) (hne : ¬ (0 : Q') < e)
    (h : t * t ≤ e * e) : t ≤ e := by
  have hel : e ≤ 0 := Int.not_lt.mp hne
  have hee : e * e ≤ 0 :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right e 0 e hel he0)
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.const 0) (.var 0)) (.const 0) (by decide)
        (fun _ => e)))
  have htt : t * t ≤ 0 := Q'.le_trans' _ _ _ h hee
  have ht : t ≤ 0 := Int.not_lt.mp (fun hlt => (Int.not_le.mpr (Q'.mul_pos hlt hlt)) htt)
  exact Q'.le_trans' _ _ _ ht he0

/-- **Squared Cauchy–Schwarz ⟹ AM-GM cross bound (PROVED).**
`B² ≤ s²·A·T`, `s, A, T ≥ 0` ⟹ `2B ≤ s(A+T)`. Uses `s²(A+T)² = 4s²AT + (s(A-T))²`. -/
theorem hcross_of_sq_bound (s Ax Ty Bxy : Q') (hs : (0 : Q') ≤ s) (hA : (0 : Q') ≤ Ax)
    (hT : (0 : Q') ≤ Ty) (hsq : Bxy * Bxy ≤ (s * s) * (Ax * Ty)) :
    (2 : Q') * Bxy ≤ s * (Ax + Ty) := by
  have he0 : (0 : Q') ≤ s * (Ax + Ty) := Q'.mul_nonneg _ _ hs (Q'.zero_le_add _ _ hA hT)
  have h4 : (4 : Q') * (Bxy * Bxy) ≤ (4 : Q') * ((s * s) * (Ax * Ty)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsq (by decide)
  have hadd : (4 : Q') * ((s * s) * (Ax * Ty)) + 0 ≤
      (4 : Q') * ((s * s) * (Ax * Ty)) + (s * (Ax + -Ty)) * (s * (Ax + -Ty)) :=
    Q'.add_le_add_left _ _ _ (sq_nonneg' _)
  have hsq2 : ((2 : Q') * Bxy) * ((2 : Q') * Bxy) ≤ (s * (Ax + Ty)) * (s * (Ax + Ty)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
        (.mul (.const 4) (.mul (.var 0) (.var 0))) (by decide) (fun _ => Bxy)))
      (Q'.le_trans' _ _ _ h4 (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.const 4) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))))
          (.add (.mul (.const 4) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))) (.const 0))
          (by decide) (fun | 0 => s | 1 => Ax | _ => Ty)))
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.mul (.const 4) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))))
            (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
              (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))))
          (.mul (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.var 0) (.add (.var 1) (.var 2))))
          (by decide) (fun | 0 => s | 1 => Ax | _ => Ty))))))
  exact if hpos : (0 : Q') < s * (Ax + Ty) then
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.abs_le_of_sq_le_sq hpos hsq2)
  else le_of_sq_le_sq_zero he0 hpos hsq2

/-! ## 4. Bridge to the r49 Schur-decomposition shape (quadratic-form level) -/

/-- **Relative comparison from the two-block gap (PROVED from OPEN inputs).**
`K ⪰ g·N` (e.g. `g = (1-s)·min(a,τ)` from `twoBlock_gap`), the coarse dissipation bound
`Ec ≤ Kmax·N` (`hupper_OPEN`), and `γ·Kmax ≤ g`, `0 ≤ γ` ⟹ `γ·Ec ≤ K`.
With `δ := 1 - γ` this is the r49 relative-comparison shape `(1-δ)(A-C) ≤ A-F`. -/
theorem relative_of_twoBlock {Z : Type} (K Ec N : Z → Q') (g Kmax γ : Q')
    (hγ : (0 : Q') ≤ γ) (hgap : ∀ z, g * N z ≤ K z)
    (hupper_OPEN : ∀ z, Ec z ≤ Kmax * N z) (hN : ∀ z, (0 : Q') ≤ N z)
    (hγK : γ * Kmax ≤ g) (z : Z) : γ * Ec z ≤ K z :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hupper_OPEN z) hγ)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hγK (hN z)) (hgap z)))

/-- **Schur shape `K ≈ (1-δ)·Ec + D`, `D ≥ 0` with `δ := 1-γ` (PROVED).** Rational analogue of
`RelativeDissipationScaleChain.SchurDecomposition`, with `D := K - γ·Ec`. -/
theorem schurShape_of_twoBlock {Z : Type} (K Ec N : Z → Q') (g Kmax γ : Q')
    (hγ : (0 : Q') ≤ γ) (hgap : ∀ z, g * N z ≤ K z)
    (hupper_OPEN : ∀ z, Ec z ≤ Kmax * N z) (hN : ∀ z, (0 : Q') ≤ N z)
    (hγK : γ * Kmax ≤ g) (z : Z) :
    (0 : Q') ≤ K z - γ * Ec z ∧ K z ≈ ((1 : Q') - ((1 : Q') - γ)) * Ec z + (K z - γ * Ec z) :=
  ⟨sub_nonneg_of_le' (relative_of_twoBlock K Ec N g Kmax γ hγ hgap hupper_OPEN hN hγK z),
   poly_identity_of_normal_eq (.var 0)
     (.add (.mul (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 1))))) (.var 2))
       (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))) (by decide)
     (fun | 0 => K z | 1 => γ | _ => Ec z)⟩

end YMGap.RG.TwoBlockSchurMarginGap
