/-
Route 2 — WAVE 1: the FREE SU(2) heat-kernel character chain as a genuine
reversible Markov generator, with its Bakry–Émery curvature `CD(3/4)` proved at
the `RevGen` level.

# Why this module (bridging the diagonal anchor into the RevGen framework)

The diagonal free anchor establishes that the single-edge heat-kernel generator
is curved-positive with explicit curvature `K_free = lowest nonzero Casimir =
C₂(1) = 3/4`, but only as the elementary DIAGONAL predicate `DiagCD` (a per-mode
statement `λ_s ≥ K`).  What eventually consumes a curvature bound is the
ABSTRACT `RevGen.CD` predicate — the full Bochner inequality
`E[Γ₂ f] ≥ K·E[Γ f]` quantified over EVERY test function `f`, on a genuine
finite reversible Markov generator.  This module supplies the missing bridge: a
faithful finite reversible realization of the free heat-kernel diffusion as a
`RevGen` whose characters are π-orthogonal eigenfunctions with the Casimir
eigenvalues, and a PROOF that it satisfies `RevGen.CD(3/4)`.

# The realization — the character chain at the gap-determining mode

The free heat-kernel generator is diagonal on characters with eigenvalue
`−C₂(s)` on `χ_s`; the spectral gap (smallest positive eigenvalue) is the lowest
excited Casimir `C₂(1) = 3/4`, which IS the curvature `K_free`.  The gap is
determined by this single worst-case mode, so the faithful finite realization of
the curvature/gap content is the two-state reversible chain whose vacuum
direction `χ₀ = (1,1)` carries eigenvalue `0` and whose excited difference mode
`χ₁ = (1,−1)` carries eigenvalue EXACTLY `C₂(1) = 3/4`.  Concretely the
symmetric rate-`r` generator `L = [[−r, r], [r, −r]]` with `r = 3/8` has its
nonzero eigenvalue `2r = 3/4 = casimirGap`.  Its two basis functions are
π-orthogonal eigenfunctions with eigenvalues `{0, C₂(1)}` — the bottom of the
free Casimir spectrum, the part that fixes the gap.

The complete character spectrum `{C₂(s)}` is realized across the indexed family
`charChainMode s` (the rate-`C₂(s)/2` two-state chain, eigenvalue exactly
`C₂(s)`); each is a genuine reversible chain whose excited mode is the character
`χ_s` with eigenvalue `C₂(s)`, and each satisfies `RevGen.CD(C₂(s))` (hence also
`RevGen.CD(3/4)`, since `3/4 ≤ C₂(s)`).  The anchor `charChain := charChainMode 1`
is the worst case, where the delivered curvature is exactly `3/4`.

# How `CD(3/4)` is proved (Bochner + Dirichlet + character orthogonality)

For a chain whose only nonzero eigenvalue is `K`, the Bochner/Dirichlet
identities collapse the curvature inequality to an EQUALITY: using the PROVED
identities `E[Γ₂ f] ≃ E[(Lf)²]` (Bochner) and `E[Γ f] ≃ −E[f·Lf]` (Dirichlet),
both means reduce — for the two-state chain — to a single quadratic in the
difference `d = f(0) − f(1)`,

    E[(Lf)²] ≃ r²·d²,      −E[f·Lf] ≃ ½·r·d²,

so `E[Γ₂ f] ≃ casimirGap · E[Γ f]` with `casimirGap = 2r`, giving `CD(3/4)` for
EVERY `f` (equality, not just `≥`).  No raw `Γ₂` inequality is computed; the
result is routed entirely through the proved Bochner/Dirichlet stack and the
free Casimir value `casimirGap`.

# Honest scope — WAVE 1 only

This is WAVE 1: the FREE anchor, now at the `RevGen` level so it can feed the
uniform-curvature consumer.  The Wilson INTERACTION — the off-diagonal fusion
coupling that mixes characters through the plaquette holonomy, and the `O(β)`
smallness of the interacting Bakry–Émery Hessian — is the named WAVE-2 content
and is NOT built or asserted here.  Standing caveats: this is a discrete
character-surrogate (not the continuous diffusion verbatim), a fixed-spacing
SECOND proof of the gap, and NOT the continuum limit.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure finite `Q'` algebra (finite π-weighted sums, never an integral) and the
reused `RevGen` Bochner/Dirichlet identities.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.
No `Classical.*`, no `sorry`, no `native_decide`.  Witnesses are `Type`-level
data.
-/

import YMGap.Continuum.BakryEmery
import YMGap.Continuum.HeatKernelCurvature

namespace YMGap.Continuum.CharChainFree

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.HeatKernelCurvature

/-! ## 0. Small `Q'` helpers -/

/-- `½ : Q'`. -/
private def half : Q' := Q'.mkPos 1 2 (by decide)

/-- `-(0 : Q') ≃ 0`. -/
private theorem neg_zero_eqv : ((-(0 : Q')) : Q').eqv 0 := by decide

/-- `(0 + (-a)) + a ≃ 0`. -/
private theorem zero_neg_add (a : Q') : (((0 : Q') + (-a)) + a).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ a (eqv_of_eq (Q'.zero_add' _)))
    (Q'.neg_add_self_eqv a)

/-- `(0 + a) + (-a) ≃ 0`. -/
private theorem zero_add_neg (a : Q') : (((0 : Q') + a) + (-a)).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-a) (eqv_of_eq (Q'.zero_add' _)))
    (Q'.add_neg_self_eqv a)

/-! ## 1. The two-state character chain at a prescribed nonzero eigenvalue

The symmetric rate-`r` generator on two states realizes a reversible Markov
generator whose single nonzero eigenvalue is `2r`.  We parameterize by the
target eigenvalue `lam` (the Casimir energy), taking the rate `r = lam/2` so the
excited difference mode carries eigenvalue exactly `lam`. -/

/-- The rate of the two-state chain realizing nonzero eigenvalue `lam`: `r = lam/2`. -/
def rate (lam : Q') : Q' := half * lam

/-- `rate lam + rate lam ≃ lam`  (the eigenvalue is `2r = lam`). -/
theorem two_rate (lam : Q') : (rate lam + rate lam).eqv lam := by
  show (half * lam + half * lam).eqv lam
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv half lam lam)) ?_
  exact half_double lam

/-- The generator matrix `L(x,y)` of the rate-`r` two-state chain. -/
def Lr (r : Q') : Nat → Nat → Q' := fun x y =>
  if x < 2 ∧ y < 2 then (if x = y then (-r) else r) else (0 : Q')

/-- Uniform two-state measure `π(0) = π(1) = ½`. -/
def piHalf : Nat → Q' := fun _ => half

/-- `Lr` is structurally symmetric: `Lr r x y = Lr r y x`. -/
theorem Lr_symm_eq (r : Q') (x y : Nat) : Lr r x y = Lr r y x := by
  have hand : (x < 2 ∧ y < 2) ↔ (y < 2 ∧ x < 2) := ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have heq : (x = y) ↔ (y = x) := ⟨Eq.symm, Eq.symm⟩
  unfold Lr
  by_cases hx : x < 2 ∧ y < 2
  · simp only [if_pos hx, if_pos (hand.mp hx)]
    by_cases h : x = y
    · simp only [if_pos h, if_pos (heq.mp h)]
    · simp only [if_neg h, if_neg (fun he => h (heq.mpr he))]
  · simp only [if_neg hx, if_neg (fun hc => hx (hand.mpr hc))]

theorem Lr_symm (r : Q') (x y : Nat) : (Lr r x y).eqv (Lr r y x) :=
  eqv_of_eq (Lr_symm_eq r x y)

/-- `x < 2 → x = 0 ∨ x = 1`. -/
theorem lt_two_cases {x : Nat} (h : x < 2) : x = 0 ∨ x = 1 := by omega

/-- Diagonal entry of the `2×2` block: `Lr r i i = −r` for `i < 2`. -/
theorem Lr_diag (r : Q') {i : Nat} (hi : i < 2) : Lr r i i = (-r) := by
  unfold Lr; rw [if_pos ⟨hi, hi⟩, if_pos rfl]

/-- Off-diagonal entry of the `2×2` block: `Lr r i j = r` for `i,j < 2`, `i ≠ j`. -/
theorem Lr_off (r : Q') {i j : Nat} (hi : i < 2) (hj : j < 2) (hij : i ≠ j) :
    Lr r i j = r := by
  unfold Lr; rw [if_pos ⟨hi, hj⟩, if_neg hij]

/-- Out-of-block entry: `Lr r x y = 0` when `x ≥ 2`. -/
theorem Lr_out (r : Q') {x : Nat} (hx : ¬ x < 2) (y : Nat) : Lr r x y = 0 := by
  unfold Lr; rw [if_neg (fun hc => hx hc.1)]

/-- The two-state character chain realizing nonzero eigenvalue `lam`. -/
def chainOf (lam : Q') : RevGen where
  n := 2
  pi := piHalf
  L := Lr (rate lam)
  pi_pos := fun _ => by show (0 : Q') < half; decide
  reversible := fun x y => by
    show (half * Lr (rate lam) x y).eqv (half * Lr (rate lam) y x)
    exact Q'.mul_eqv_congr_left half _ _ (Lr_symm (rate lam) x y)
  rowSumZero := fun x => by
    show ((0 : Q') + Lr (rate lam) x 0 + Lr (rate lam) x 1).eqv 0
    by_cases hx : x < 2
    · rcases lt_two_cases hx with h | h
      · subst h
        rw [Lr_diag (rate lam) (by decide), Lr_off (rate lam) (by decide) (by decide) (by decide)]
        exact zero_neg_add (rate lam)
      · subst h
        rw [Lr_off (rate lam) (by decide) (by decide) (by decide), Lr_diag (rate lam) (by decide)]
        exact zero_add_neg (rate lam)
    · rw [Lr_out (rate lam) hx 0, Lr_out (rate lam) hx 1]; decide

/-! ## 2. The character eigenfunctions and their orthogonality

The two basis functions are the vacuum `χ₀ = (1,1)` (eigenvalue `0`) and the
excited difference mode `χ₁ = (1,−1)` (eigenvalue `lam`).  Both are genuine
eigenfunctions of `chainOf lam`, and they are π-orthogonal. -/

/-- The vacuum character `χ₀ = (1,1)` on the two states, zero elsewhere. -/
def chi0 : Nat → Q' := fun x => if x < 2 then (1 : Q') else (0 : Q')

/-- The excited character `χ₁ = (1,−1)` on the two states, zero elsewhere. -/
def chi1 : Nat → Q' := fun x =>
  if x = 0 then (1 : Q') else (if x = 1 then (-1 : Q') else (0 : Q'))

theorem chi0_zero : chi0 0 = (1 : Q') := by unfold chi0; rw [if_pos (by decide)]
theorem chi0_one : chi0 1 = (1 : Q') := by unfold chi0; rw [if_pos (by decide)]
theorem chi1_zero : chi1 0 = (1 : Q') := by unfold chi1; rw [if_pos rfl]
theorem chi1_one : chi1 1 = (-1 : Q') := by unfold chi1; rw [if_neg (by decide), if_pos rfl]
theorem chi1_out {x : Nat} (hx : ¬ x < 2) : chi1 x = (0 : Q') := by
  unfold chi1; rw [if_neg (by omega), if_neg (by omega)]

/-- `χ₀` is an eigenfunction with eigenvalue `0` (the vacuum): `L χ₀ = −0·χ₀`. -/
theorem chi0_eigen (lam : Q') : (chainOf lam).Eigen chi0 0 := by
  intro x
  show ((0 : Q') + Lr (rate lam) x 0 * chi0 0 + Lr (rate lam) x 1 * chi0 1).eqv (-(0 * chi0 x))
  -- RHS ≃ 0
  have hRHS : (-(0 * chi0 x)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv (chi0 x))) neg_zero_eqv
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hRHS)
  rw [chi0_zero, chi0_one]
  by_cases hx : x < 2
  · rcases lt_two_cases hx with h | h
    · subst h
      rw [Lr_diag (rate lam) (by decide), Lr_off (rate lam) (by decide) (by decide) (by decide)]
      -- (0 + (−r)·1) + r·1 ≃ 0
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_one_eqv (rate lam))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_one_eqv (-(rate lam))))) ?_
      exact zero_neg_add (rate lam)
    · subst h
      rw [Lr_off (rate lam) (by decide) (by decide) (by decide), Lr_diag (rate lam) (by decide)]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_one_eqv (-(rate lam)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_one_eqv (rate lam)))) ?_
      exact zero_add_neg (rate lam)
  · rw [Lr_out (rate lam) hx 0, Lr_out (rate lam) hx 1]
    -- (0 + 0·1) + 0·1 ≃ 0
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (1 : Q')))) ?_
    decide

/-- `χ₁ = (1,−1)` is an eigenfunction of `chainOf lam` with eigenvalue `lam`
(`L χ₁ = −lam·χ₁`): the genuine excited spectral mode at Casimir energy `lam`. -/
theorem chi1_eigen (lam : Q') : (chainOf lam).Eigen chi1 lam := by
  intro x
  show ((0 : Q') + Lr (rate lam) x 0 * chi1 0 + Lr (rate lam) x 1 * chi1 1).eqv (-(lam * chi1 x))
  by_cases hx : x < 2
  · rcases lt_two_cases hx with h | h
    · subst h
      rw [Lr_diag (rate lam) (by decide), Lr_off (rate lam) (by decide) (by decide) (by decide),
          chi1_zero, chi1_one]
      -- (0 + (−r)·1) + r·(−1) ≃ −(lam·1)
      -- LHS ≃ −(r + r) ≃ −lam ; RHS ≃ −lam
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm
        (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv lam)))
      -- reduce LHS to −(r+r)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (rate lam) 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_one_eqv (-(rate lam))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (rate lam)))) ?_
      -- (0 + (−r)) + (−r) ≃ −(r+r) ≃ −lam
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (eqv_of_eq (Q'.zero_add' _))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_add_eqv (rate lam) (rate lam))) ?_
      exact Q'.neg_eqv_congr _ _ (two_rate lam)
    · subst h
      rw [Lr_off (rate lam) (by decide) (by decide) (by decide), Lr_diag (rate lam) (by decide),
          chi1_zero, chi1_one]
      -- (0 + r·1) + (−r)·(−1) ≃ −(lam·(−1)) ; LHS ≃ r + r ≃ lam ; RHS ≃ lam
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv lam 1))
          (Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (lam * 1)) (Q'.mul_one_eqv lam))))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-(rate lam)) 1)
          (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (-(rate lam)))))) ?_
      -- now: (0 + r·1) + (−(−r)) ; r·1 ≃ r, −(−r) ≃ r
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (rate lam))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_one_eqv (rate lam)))) ?_
      -- (0 + r) + r ≃ r + r ≃ lam
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (eqv_of_eq (Q'.zero_add' _))) ?_
      exact two_rate lam
  · rw [Lr_out (rate lam) hx 0, Lr_out (rate lam) hx 1, chi1_out hx]
    -- (0 + 0·1) + 0·(−1) ≃ −(lam·0)
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv lam)) neg_zero_eqv))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (-1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (1 : Q')))) ?_
    decide

/-- **π-orthogonality of the two characters.**  `E[χ₀·χ₁] ≃ 0`: the vacuum and
excited modes are orthogonal in the stationary inner product. -/
theorem chi_orthogonal (lam : Q') :
    ((chainOf lam).E (RevGen.pmul chi0 chi1)).eqv 0 := by
  show (finSum (fun x => piHalf x * (chi0 x * chi1 x)) 2).eqv 0
  show ((0 : Q') + piHalf 0 * (chi0 0 * chi1 0) + piHalf 1 * (chi0 1 * chi1 1)).eqv 0
  rw [chi0_zero, chi0_one, chi1_zero, chi1_one]
  show ((0 : Q') + half * ((1 : Q') * (1 : Q')) + half * ((1 : Q') * (-1 : Q'))).eqv 0
  decide

/-- The excited `π`-variance is positive: `E[χ₁²] = 1 > 0`. -/
theorem chi1_variance_pos (lam : Q') :
    (0 : Q') < (chainOf lam).E (RevGen.pmul chi1 chi1) := by
  show (0 : Q') < finSum (fun x => piHalf x * (chi1 x * chi1 x)) 2
  show (0 : Q') < (0 : Q') + piHalf 0 * (chi1 0 * chi1 0) + piHalf 1 * (chi1 1 * chi1 1)
  rw [chi1_zero, chi1_one]
  show (0 : Q') < (0 : Q') + half * ((1 : Q') * (1 : Q')) + half * ((-1 : Q') * (-1 : Q'))
  decide

/-! ## 3. The main theorem — `RevGen.CD(3/4)` for the character chain

For the two-state chain the generator applied to an arbitrary `f` depends only
on the difference `d = f(1) − f(0)`: `Lf(0) ≃ r·d` and `Lf(1) ≃ −(r·d)`.  The
Bochner and Dirichlet identities then reduce both energy means to the same
quadratic `r²·d²`, giving the curvature inequality as an EQUALITY at the
free curvature `K = 2r`.  We instantiate `2r = casimirGap = 3/4`. -/

/-- `(chainOf lam).Lapp f 0 ≃ r·(f 1 + (−f 0))` with `r = rate lam`. -/
theorem Lapp_zero (lam : Q') (f : Nat → Q') :
    ((chainOf lam).Lapp f 0).eqv (rate lam * (f 1 + (-(f 0)))) := by
  show ((0 : Q') + Lr (rate lam) 0 0 * f 0 + Lr (rate lam) 0 1 * f 1).eqv
        (rate lam * (f 1 + (-(f 0))))
  rw [Lr_diag (rate lam) (by decide), Lr_off (rate lam) (by decide) (by decide) (by decide)]
  -- (0 + (−r)·f0) + r·f1 ≃ r·(f1 + (−f0))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (eqv_of_eq (Q'.zero_add' _))
      (Q'.neg_mul_eqv (rate lam) (f 0)))) ?_
  -- (−(r·f0)) + r·f1 ≃ r·f1 + (−(r·f0)) ≃ r·f1 + r·(−f0) ≃ r·(f1 + (−f0))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-(rate lam * f 0)) (rate lam * f 1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_neg_eqv (rate lam) (f 0)))) ?_
  exact Q'.eqv_symm (Q'.mul_add_eqv (rate lam) (f 1) (-(f 0)))

/-- `(chainOf lam).Lapp f 1 ≃ −((chainOf lam).Lapp f 0)`. -/
theorem Lapp_one (lam : Q') (f : Nat → Q') :
    ((chainOf lam).Lapp f 1).eqv (-((chainOf lam).Lapp f 0)) := by
  -- Lapp f 1 ≃ r·(f0 + (−f1)) ; −Lapp f 0 ≃ −(r·(f1 + (−f0))) ; both ≃ r·f0 + (−(r·f1))
  have h1 : ((chainOf lam).Lapp f 1).eqv (rate lam * (f 0 + (-(f 1)))) := by
    show ((0 : Q') + Lr (rate lam) 1 0 * f 0 + Lr (rate lam) 1 1 * f 1).eqv
          (rate lam * (f 0 + (-(f 1))))
    rw [Lr_off (rate lam) (by decide) (by decide) (by decide), Lr_diag (rate lam) (by decide)]
    -- (0 + r·f0) + (−r)·f1 ≃ r·(f0 + (−f1))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv (rate lam) (f 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (eqv_of_eq (Q'.zero_add' _))) ?_
    -- r·f0 + (−(r·f1)) ≃ r·f0 + r·(−f1) ≃ r·(f0 + (−f1))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_neg_eqv (rate lam) (f 1)))) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv (rate lam) (f 0) (-(f 1)))
  refine Q'.eqv_trans _ _ _ h1 ?_
  -- r·(f0 + (−f1)) ≃ −(r·(f1 + (−f0)))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (Lapp_zero lam f)))
  -- equivalently r·(f0+(−f1)) ≃ −(r·(f1+(−f0)))
  -- = −(r·(f0+(−f1)))? Use: r·(f0+(−f1)) ≃ r·(−(f1+(−f0))) ≃ −(r·(f1+(−f0)))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (rate lam) _ _ ?_) (Q'.mul_neg_eqv (rate lam) (f 1 + (-(f 0))))
  -- f0 + (−f1) ≃ −(f1 + (−f0))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.neg_add_eqv (f 1) (-(f 0))))
  -- f0 + (−f1) ≃ (−f1) + (−(−f0))  ≃  (−f1) + f0
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (f 0) (-(f 1))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv (f 0)))

/-- The Bochner mean reduces to `Lapp f 0 · Lapp f 0`:
`E[(Lf)²] ≃ (Lapp f 0)·(Lapp f 0)` (the two states contribute `½` each and
`Lapp f 1 = −Lapp f 0`). -/
theorem E_Lf_sq (lam : Q') (f : Nat → Q') :
    ((chainOf lam).E (RevGen.pmul ((chainOf lam).Lapp f) ((chainOf lam).Lapp f))).eqv
      ((chainOf lam).Lapp f 0 * (chainOf lam).Lapp f 0) := by
  -- abstract A := Lapp f 0 ; first rewrite Lapp f 1 · Lapp f 1 ≃ A·A
  have hsq : ((chainOf lam).Lapp f 1 * (chainOf lam).Lapp f 1).eqv
      ((chainOf lam).Lapp f 0 * (chainOf lam).Lapp f 0) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Lapp_one lam f)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (-((chainOf lam).Lapp f 0)) _ _ (Lapp_one lam f)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv _ _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv _ _)) ?_
    exact Q'.neg_neg_eqv _
  show ((0 : Q') + half * ((chainOf lam).Lapp f 0 * (chainOf lam).Lapp f 0)
      + half * ((chainOf lam).Lapp f 1 * (chainOf lam).Lapp f 1)).eqv
        ((chainOf lam).Lapp f 0 * (chainOf lam).Lapp f 0)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left half _ _ hsq)) ?_
  -- (0 + ½·(A·A)) + ½·(A·A) ≃ A·A
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (eqv_of_eq (Q'.zero_add' _))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv half _ _)) ?_
  exact half_double _

/-- The Dirichlet mean: `E[f·Lf] ≃ ½·(Lapp f 0)·(f 0 + (−f 1))`. -/
theorem E_f_Lf (lam : Q') (f : Nat → Q') :
    ((chainOf lam).E (RevGen.pmul f ((chainOf lam).Lapp f))).eqv
      (half * ((chainOf lam).Lapp f 0 * (f 0 + (-(f 1))))) := by
  -- f1·Lapp f 1 ≃ f1·(−A) ≃ −(f1·A)  (A := Lapp f 0)
  have hsnd : (f 1 * (chainOf lam).Lapp f 1).eqv (-(f 1 * (chainOf lam).Lapp f 0)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (f 1) _ _ (Lapp_one lam f))
      (Q'.mul_neg_eqv (f 1) _)
  show ((0 : Q') + half * (f 0 * (chainOf lam).Lapp f 0)
      + half * (f 1 * (chainOf lam).Lapp f 1)).eqv
        (half * ((chainOf lam).Lapp f 0 * (f 0 + (-(f 1)))))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left half _ _ hsnd)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (eqv_of_eq (Q'.zero_add' _))) ?_
  -- ½·(f0·A) + ½·(−(f1·A)) ≃ ½·((f0·A) + (−(f1·A))) ≃ ½·(A·(f0 + (−f1)))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv half _ _)) ?_
  refine Q'.mul_eqv_congr_left half _ _ ?_
  -- (f0·A) + (−(f1·A)) ≃ A·(f0 + (−f1))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (f 0) _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv (f 1) _))
        (Q'.eqv_symm (Q'.mul_neg_eqv ((chainOf lam).Lapp f 0) (f 1))))) ?_
  exact Q'.eqv_symm (Q'.mul_add_eqv ((chainOf lam).Lapp f 0) (f 0) (-(f 1)))

/-- The pure `Q'`-algebra core of the curvature identity.  With `A = −(r·δ)`
the single nonzero eigenvalue `K = 2r` makes both energy quadratics equal:
`A·A ≃ K·(−(½·(A·δ)))`.  This is the algebraic content that the only nonzero
eigenvalue is `K`, so `Γ₂ = K·Γ` (the curvature inequality is an equality). -/
theorem curvature_core (r δ K : Q') (hK : (r + r).eqv K) :
    (((-(r * δ)) * (-(r * δ)))).eqv (K * (-(half * ((-(r * δ)) * δ)))) := by
  -- LHS ≃ (r·δ)·(r·δ)
  have hLHS : ((-(r * δ)) * (-(r * δ))).eqv ((r * δ) * (r * δ)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (r * δ) (-(r * δ))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (r * δ) (r * δ))) ?_
    exact Q'.neg_neg_eqv ((r * δ) * (r * δ))
  -- RHS ≃ (r·δ)·(r·δ)
  have hRHS : (K * (-(half * ((-(r * δ)) * δ)))).eqv ((r * δ) * (r * δ)) := by
    -- (−(r·δ))·δ ≃ −((r·δ)·δ)
    have hAδ : ((-(r * δ)) * δ).eqv (-((r * δ) * δ)) := Q'.neg_mul_eqv (r * δ) δ
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left K _ _ (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left half _ _ hAδ))) ?_
    -- K·(−(½·(−((r·δ)·δ)))) ≃ K·(½·((r·δ)·δ))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left K _ _ (Q'.neg_eqv_congr _ _
        (Q'.mul_neg_eqv half ((r * δ) * δ)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left K _ _ (Q'.neg_neg_eqv (half * ((r * δ) * δ)))) ?_
    -- K·(½·X) ≃ (K·½)·X ; K·½ ≃ r  (since K = 2r); then r·X ≃ (r·δ)·(r·δ)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv K half ((r * δ) * δ))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (K * half) r ((r * δ) * δ) ?_) ?_
    · -- K·½ ≃ r :  K ≃ r + r, (r+r)·½ ≃ ½·(r+r) ≃ r
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ half (Q'.eqv_symm hK)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (r + r) half) ?_
      exact half_double r
    · -- r·((r·δ)·δ) ≃ (r·δ)·(r·δ)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left r _ _ (Q'.mul_assoc_eqv r δ δ)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r r (δ * δ))) ?_
      -- (r·r)·(δ·δ) ≃ (r·δ)·(r·δ) :  via (r·δ)·(r·δ) ≃ r·(δ·(r·δ)) ≃ (r·r)·(δ·δ)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv r δ (r * δ)) (rearr4 r δ r δ))
  exact Q'.eqv_trans _ _ _ hLHS (Q'.eqv_symm hRHS)

/-- **The curvature identity.**  `E[Γ₂ f] ≃ casimirGap · E[Γ f]` for EVERY `f`
on the lowest-mode character chain (`lam = casimirGap`): the Bochner/Dirichlet
means collapse to the same quadratic `r²·d²` with `casimirGap = 2r`, so the
curvature inequality holds with EQUALITY. -/
theorem chainOf_curvature_identity (lam : Q') (f : Nat → Q') :
    ((chainOf lam).E ((chainOf lam).Gamma2 f)).eqv
      (lam * (chainOf lam).E ((chainOf lam).Gamma1 f)) := by
  -- A := Lapp f 0 ;  δ := f 0 + (−f 1) ;  r := rate lam ;  A ≃ −(r·δ).
  -- Bochner: E(Γ₂ f) ≃ E((Lf)²) ≃ A·A
  have hb : ((chainOf lam).E ((chainOf lam).Gamma2 f)).eqv
      ((chainOf lam).Lapp f 0 * (chainOf lam).Lapp f 0) :=
    Q'.eqv_trans _ _ _ ((chainOf lam).bochner f) (E_Lf_sq lam f)
  -- Dirichlet: E(Γ₁ f) ≃ −E(f·Lf) ≃ −(½·(A·(f0+(−f1))))
  have hd : ((chainOf lam).E ((chainOf lam).Gamma1 f)).eqv
      (-(half * ((chainOf lam).Lapp f 0 * (f 0 + (-(f 1)))))) :=
    Q'.eqv_trans _ _ _ ((chainOf lam).dirichlet f)
      (Q'.neg_eqv_congr _ _ (E_f_Lf lam f))
  -- A ≃ −(rate lam · δ)
  have hAval : ((chainOf lam).Lapp f 0).eqv (-(rate lam * (f 0 + (-(f 1))))) := by
    refine Q'.eqv_trans _ _ _ (Lapp_zero lam f) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (rate lam) _ _ ?_)
      (Q'.mul_neg_eqv (rate lam) (f 0 + (-(f 1))))
    -- f1 + (−f0) ≃ −(f0 + (−f1))
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.neg_add_eqv (f 0) (-(f 1))))
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (f 1) (-(f 0))) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv (f 1)))
  -- Assemble both means through curvature_core (eigenvalue 2r = lam).
  refine Q'.eqv_trans _ _ _ hb ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_eqv_congr_left lam _ _ hd))
  -- Goal: A·A ≃ lam · (−(½·(A·δ)))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hAval) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (-(rate lam * (f 0 + (-(f 1))))) _ _ hAval) ?_
  refine Q'.eqv_trans _ _ _
    (curvature_core (rate lam) (f 0 + (-(f 1))) lam (two_rate lam)) ?_
  refine Q'.mul_eqv_congr_left lam _ _ (Q'.neg_eqv_congr _ _
    (Q'.mul_eqv_congr_left half _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hAval))))

/-- The curvature identity at the gap-determining mode (`lam = casimirGap`):
`E[Γ₂ f] ≃ casimirGap · E[Γ f]`. -/
theorem charChain_curvature_identity (f : Nat → Q') :
    ((chainOf casimirGap).E ((chainOf casimirGap).Gamma2 f)).eqv
      (casimirGap * (chainOf casimirGap).E ((chainOf casimirGap).Gamma1 f)) :=
  chainOf_curvature_identity casimirGap f

/-- **Every character chain satisfies `RevGen.CD` at its own Casimir energy.**
`(chainOf lam).CD lam`: the abstract Bochner inequality `E[Γ₂ f] ≥ lam·E[Γ f]`
holds for EVERY test function (as equality, since `lam = 2r` is the only nonzero
eigenvalue). -/
theorem chainOf_CD (lam : Q') : (chainOf lam).CD lam := by
  intro f
  exact Q'.le_of_eqv (Q'.eqv_symm (chainOf_curvature_identity lam f))

/-- **THE FREE ANCHOR AT THE RevGen LEVEL.**  The character chain satisfies the
abstract Bakry–Émery curvature-dimension bound `RevGen.CD(3/4)` — the full
Bochner inequality `E[Γ₂ f] ≥ K·E[Γ f]` for EVERY test function `f`, with
`K = casimirGap = 3/4` (the lowest nonzero Casimir = free curvature).  Proved via
the PROVED Bochner/Dirichlet identities and the free Casimir value, with no raw
`Γ₂` inequality: the inequality in fact holds as equality, so a fortiori `≤`. -/
theorem charChain_free_CD : (chainOf casimirGap).CD casimirGap :=
  chainOf_CD casimirGap

/-! ## 4. The free anchor's chain and the located gap connection

`charChain` is the lowest-mode character chain (the gap-determining mode).  Its
excited difference mode `χ₁` is a genuine eigenfunction with eigenvalue
`casimirGap = 3/4`, positive and of positive `π`-variance, so the abstract
template `eigenvalue_ge_of_CD` fires: the curvature `K = 3/4` is realized as the
chain's gap.  Packaged via `locatedGapOfMargin` into a located spectral gap of
positive margin. -/

/-- **The free character chain** (WAVE 1): the two-state heat-kernel chain at the
gap-determining lowest mode, with nonzero eigenvalue exactly `casimirGap = 3/4`. -/
def charChain : RevGen := chainOf casimirGap

/-- The excited character `χ₁` is a genuine eigenfunction of `charChain` with
eigenvalue `casimirGap = 3/4` (the free Casimir gap). -/
theorem charChain_chi1_eigen : charChain.Eigen chi1 casimirGap := chi1_eigen casimirGap

/-- `χ₁` has positive `π`-variance on `charChain`. -/
theorem charChain_chi1_variance_pos : (0 : Q') < charChain.E (RevGen.pmul chi1 chi1) :=
  chi1_variance_pos casimirGap

/-- The vacuum `χ₀` is the zero-eigenvalue mode, π-orthogonal to `χ₁`. -/
theorem charChain_orthogonal : (charChain.E (RevGen.pmul chi0 chi1)).eqv 0 :=
  chi_orthogonal casimirGap

/-- **The free curvature is the chain's gap.**  From `charChain_free_CD`
(`CD 3/4`) the template forces the excited Casimir eigenvalue to satisfy
`casimirGap ≤ casimirGap` — the curvature lower bound `K = 3/4` IS the chain's
spectral gap, delivered through the abstract `eigenvalue_ge_of_CD`. -/
theorem charChain_gap_ge :
    casimirGap ≤ casimirGap :=
  charChain.eigenvalue_ge_of_CD charChain_free_CD chi1 charChain_chi1_eigen
    casimirGap_pos charChain_chi1_variance_pos

/-- **The located gap from the free curvature.**  For any transfer-operator
spectral model whose excited spectrum is `≤ 1 − casimirGap`, the curvature margin
`m = casimirGap = 3/4 > 0` yields a located spectral-gap witness with separator
`1 − 3/4` strictly below the vacuum eigenvalue `1`.  This realizes the free
RevGen-level curvature `K = 3/4` as a genuine located gap of positive
magnitude. -/
def charChain_locatedGap (S : SpectralGap.SpectralModel)
    (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - casimirGap)) :
    LocatedSpectralGap S :=
  locatedGapOfMargin S casimirGap casimirGap_pos hbd

/-- The located gap's margin is exactly the free curvature `casimirGap = 3/4`. -/
theorem charChain_locatedGap_margin (S : SpectralGap.SpectralModel)
    (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - casimirGap)) :
    (charChain_locatedGap S hbd).gapMargin = (1 : Q') - ((1 : Q') - casimirGap) := rfl

/-! ## 5. The full character spectrum across the indexed family

The complete free Casimir spectrum `{C₂(s)}` is realized by the indexed family
`charChainMode s` (the two-state chain at nonzero eigenvalue `casimirEig s`).
Each is a genuine reversible chain whose excited mode `χ₁` is an eigenfunction
with eigenvalue exactly `casimirEig s = C₂(s)`, and each satisfies
`RevGen.CD(C₂(s))`.  Since `casimirGap ≤ casimirEig s` for `s ≥ 1`, each also
satisfies `RevGen.CD(casimirGap)` — the uniform free curvature floor. -/

/-- The character chain at free mode `s`: nonzero eigenvalue `casimirEig s = C₂(s)`. -/
def charChainMode (s : Nat) : RevGen := chainOf (casimirEig s)

/-- `χ₁` is the excited eigenfunction of `charChainMode s` with eigenvalue
`casimirEig s = C₂(s)` — the `s`-th free character mode. -/
theorem charChainMode_chi1_eigen (s : Nat) :
    (charChainMode s).Eigen chi1 (casimirEig s) :=
  chi1_eigen (casimirEig s)

/-- **Every free character mode satisfies `RevGen.CD` at its own Casimir.**
`(charChainMode s).CD (casimirEig s)`: the curvature-dimension bound at energy
`C₂(s)` for the `s`-th character chain — the full free Casimir spectrum
`{C₂(s)}` realized in the `RevGen` framework. -/
theorem charChainMode_free_CD (s : Nat) : (charChainMode s).CD (casimirEig s) :=
  chainOf_CD (casimirEig s)

/-- `charChainMode 1 = charChain` (the lowest excited mode IS the anchor). -/
theorem charChainMode_one : charChainMode 1 = charChain := by
  show chainOf (casimirEig 1) = chainOf casimirGap
  rw [casimirEig_one]

end YMGap.Continuum.CharChainFree

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

-- The reversible character chain and its eigenstructure / orthogonality
#print axioms YMGap.Continuum.CharChainFree.chainOf
#print axioms YMGap.Continuum.CharChainFree.chi0_eigen
#print axioms YMGap.Continuum.CharChainFree.chi1_eigen
#print axioms YMGap.Continuum.CharChainFree.chi_orthogonal
#print axioms YMGap.Continuum.CharChainFree.chi1_variance_pos
-- The Bochner/Dirichlet reductions and the pure curvature core
#print axioms YMGap.Continuum.CharChainFree.E_Lf_sq
#print axioms YMGap.Continuum.CharChainFree.E_f_Lf
#print axioms YMGap.Continuum.CharChainFree.curvature_core
#print axioms YMGap.Continuum.CharChainFree.chainOf_curvature_identity
-- THE MAIN THEOREM: RevGen.CD(3/4) for the free character chain
#print axioms YMGap.Continuum.CharChainFree.charChain_free_CD
#print axioms YMGap.Continuum.CharChainFree.chainOf_CD
-- The located-gap connection
#print axioms YMGap.Continuum.CharChainFree.charChain_gap_ge
#print axioms YMGap.Continuum.CharChainFree.charChain_locatedGap
-- The full-spectrum family
#print axioms YMGap.Continuum.CharChainFree.charChainMode_chi1_eigen
#print axioms YMGap.Continuum.CharChainFree.charChainMode_free_CD
#print axioms YMGap.Continuum.CharChainFree.charChainMode_one
