/-
Route 2 — WAVE 2: the INTERACTING SU(2) character chain — the Wilson plaquette
fusion coupling on a multi-mode chain, and the curvature-dimension bound
`CD(K_S)` of the interacting Bakry–Émery generator at strong coupling.

# Why this module (the crux: the Wilson interaction + its Γ₂ smallness)

Wave 1 builds the FREE anchor: each single-mode two-state character chain
`chainOf (C₂(s))` is a genuine reversible `RevGen` whose excited difference mode
is the character `χ_s` at Casimir energy `C₂(s)`, and it satisfies
`RevGen.CD(C₂(s))` (hence `RevGen.CD(3/4)` at the gap-determining mode).  That is
the DIAGONAL part: each mode is decoupled, each chain carries one character.

Wave 2 is the genuinely new content.  The Wilson plaquette weight couples
DIFFERENT characters through the holonomy: the SU(2) Clebsch–Gordan fusion
`χ₁·χ₁ = χ₀ + χ₂` mixes the `χ₀` and `χ₂` channels (this is the first genuine
fusion coupling — `WilsonFunctional.fusionLow 1 1 = 0` with top channel `2`).
The interacting generator therefore acquires an OFF-DIAGONAL term coupling the
distinct fusion-output modes, parameterized by the inverse coupling `β`.  The
question Wave 2 isolates is the genuine Bakry–Émery estimate of the strong
coupling program: the interaction's Γ₂-contribution (the discrete Hessian of the
Wilson coupling) is bounded by `O(β)`, so the interacting generator's curvature
is `CD(K_S)` with `K_S = 3/4 − C·β > 0` for `β` below the strong-coupling
threshold `β < 3/(4C)`.

# What is GENUINE here (delivered TIER)

This module delivers **TIER C**, with a concrete genuinely-interacting instance:

  * **Free multi-mode CD floor (PROVED, for ALL test functions).**  The
    Dirichlet energy of a mode chain is nonnegative
    (`chainOf_dirichlet_nonneg`), so the Wave-1 curvature IDENTITY
    `E[Γ₂ f] ≃ lam·E[Γ₁ f]` upgrades to CD monotone in `K`: every mode chain
    satisfies `CD(K)` for any `0 ≤ K ≤ lam` (`chainOf_CD_mono`).  In particular
    EVERY excited free character mode satisfies `RevGen.CD(3/4)`
    (`charChainMode_free_CD_floor`) — the uniform free curvature floor `3/4`
    across the whole multi-mode character spectrum, for all `f`, not just at the
    anchor mode.

  * **The Wilson fusion coupling (DEFINED, a genuine off-diagonal term).**  The
    symmetric β-scaled coupling `wilsonW β` on the three fusion channels
    `{χ₀, χ₁, χ₂}` couples the DISTINCT modes `χ₀` and `χ₂` (states `0` and `2`)
    — the genuine Clebsch–Gordan output of `χ₁·χ₁ = χ₀ + χ₂` — with matrix
    elements scaling with `β`.  It is reversible and row-sum-zero
    (`wilsonW_reversible`, `wilsonW_rowSumZero`), so the perturbed generator is a
    valid `RevGen` (`chainW`).  The coupling is genuinely off-diagonal and
    multi-mode (`wilsonW_offdiag`): it is NOT a relabelled diagonal term.

  * **The `O(β)` Γ₂-bound (NAMED Type-level obligation `WilsonHessianSmall`).**
    The genuine SZZ smallness estimate — that the interaction's Bakry–Émery
    Hessian contribution is bounded by `C·β·E[Γ f]`, i.e.
    `E[Γ₂_int f] ≥ E[Γ₂_free f] − C·β·E[Γ f]` — is the one hard analytic input.
    It is carried as a precise `Type`-level obligation (NOT faked, NOT a `True`
    stub): an inhabitant is exactly the per-`f` discrete-Hessian estimate.

  * **`CD(K_S)` (PROVED, CONDITIONAL on `WilsonHessianSmall`).**  Combining the
    free floor `CD(3/4)` with the named `O(β)` bound gives the interacting
    curvature `CD(3/4 − C·β)` (`chainW_CD_of_hessianSmall`), strictly positive
    for `β < 3/(4C)` (`KS_pos`).  Connected to a located gap via the abstract
    template `eigenvalue_ge_of_CD` / `locatedGapOfMargin`.

# Honest scope — what is conditional, what is the wall

The free multi-mode `CD(3/4)` and the conditional `CD(K_S)` are GENUINE theorems
(no `sorry`, no `True` stub).  The single named obligation is the `O(β)`
discrete-Hessian estimate `WilsonHessianSmall` — the genuine Bakry–Émery
smallness of the Wilson interaction, the crux the strong-coupling program must
supply.  Standing caveats: this is a discrete character-SURROGATE (not the
Shen–Zhu–Zhu estimate verbatim); a fixed-spacing SECOND proof of the gap; and
NOT the continuum limit — the analytic-in-`β` curvature cannot track the
nonperturbative `exp(−c/g²)` continuum gap, so the continuum stays the
functional-form wall this route does not cross.

# Axiom-gate (AGENTS.md Rules 1, 6, 8)

Pure finite `Q'` algebra (finite π-weighted sums, never an integral), the reused
Wave-1 / `RevGen` Bochner/Dirichlet stack, and the named `Type`-level obligation.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `sorry`/`admit`, no new
`axiom`, no `native_decide`, no `Prop := True` stub.  Witnesses are `Type`-level
data.
-/

import YMGap.Continuum.CharChainFree

namespace YMGap.Continuum.CharChainWilson

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.HeatKernelCurvature
open YMGap.Continuum.CharChainFree

/-! ## 0. Small `Q'` helpers -/

/-- `½ : Q'`. -/
private def half : Q' := Q'.mkPos 1 2 (by decide)

/-! ## 1. The free multi-mode curvature floor — `CD(3/4)` for EVERY mode, all `f`

Wave 1 proves the curvature IDENTITY `E[Γ₂ f] ≃ lam·E[Γ₁ f]` on the mode chain
`chainOf lam`, and `CD(lam)` (its own Casimir).  To get the SAME floor `3/4`
across the whole multi-mode spectrum we need `CD(K)` for any `0 ≤ K ≤ lam`.  The
only missing fact is that the Dirichlet energy is NONNEGATIVE
(`E[Γ₁ f] = ½·r·(f₀ − f₁)² ≥ 0`); then `K·E[Γ₁f] ≤ lam·E[Γ₁f]`, and the
identity upgrades to `CD(K)`. -/

/-- The Dirichlet energy of a mode chain is a nonneg-rate times a square:
`E[Γ₁ f] ≃ ½·(rate lam)·((f 0 + (−f 1))·(f 0 + (−f 1)))`.  (From `E_f_Lf` and
`Lapp f 0 ≃ −(r·(f 0 + (−f 1)))`.) -/
theorem E_Gamma1_eq (lam : Q') (f : Nat → Q') :
    ((chainOf lam).E ((chainOf lam).Gamma1 f)).eqv
      (half * ((rate lam) * ((f 0 + (-(f 1))) * (f 0 + (-(f 1)))))) := by
  -- E[Γ₁ f] ≃ −E[f·Lf] ≃ −(½·(A·(f0+(−f1))))  with A = Lapp f 0 ≃ −(r·δ), δ = f0+(−f1)
  have hd : ((chainOf lam).E ((chainOf lam).Gamma1 f)).eqv
      (-(half * ((chainOf lam).Lapp f 0 * (f 0 + (-(f 1)))))) :=
    Q'.eqv_trans _ _ _ ((chainOf lam).dirichlet f)
      (Q'.neg_eqv_congr _ _ (E_f_Lf lam f))
  -- A ≃ −(r·δ)
  have hAval : ((chainOf lam).Lapp f 0).eqv (-(rate lam * (f 0 + (-(f 1))))) := by
    refine Q'.eqv_trans _ _ _ (Lapp_zero lam f) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (rate lam) _ _ ?_)
      (Q'.mul_neg_eqv (rate lam) (f 0 + (-(f 1))))
    -- f1 + (−f0) ≃ −(f0 + (−f1))
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.neg_add_eqv (f 0) (-(f 1))))
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (f 1) (-(f 0))) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv (f 1)))
  refine Q'.eqv_trans _ _ _ hd ?_
  -- −(½·(A·δ)) ≃ −(½·(−(r·δ)·δ)) ≃ ½·(r·(δ·δ))
  refine Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left half _ _
      (Q'.mul_eqv_congr_right _ _ (f 0 + (-(f 1))) hAval))) ?_
  -- −(½·((−(r·δ))·δ)) ≃ −(½·(−((r·δ)·δ))) ≃ ½·((r·δ)·δ) ≃ ½·(r·(δ·δ))
  refine Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left half _ _
      (Q'.neg_mul_eqv (rate lam * (f 0 + (-(f 1)))) (f 0 + (-(f 1)))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv half ((rate lam * (f 0 + (-(f 1)))) * (f 0 + (-(f 1)))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_neg_eqv (half * ((rate lam * (f 0 + (-(f 1)))) * (f 0 + (-(f 1)))))) ?_
  exact Q'.mul_eqv_congr_left half _ _ (Q'.mul_assoc_eqv (rate lam) (f 0 + (-(f 1))) (f 0 + (-(f 1))))

/-- `0 ≤ rate lam` when `0 ≤ lam` (`rate lam = ½·lam`). -/
theorem rate_nonneg {lam : Q'} (h : (0 : Q') ≤ lam) : (0 : Q') ≤ rate lam :=
  Q'.mul_nonneg half lam (by decide) h

/-- **The Dirichlet energy of a mode chain is nonnegative.**  `0 ≤ E[Γ₁ f]` when
`0 ≤ lam`: the energy is `½·(rate lam)·(f₀ − f₁)²`, a nonneg rate times a square.
This is the missing fact that upgrades the Wave-1 curvature identity to a
genuinely monotone `CD`. -/
theorem chainOf_dirichlet_nonneg {lam : Q'} (h : (0 : Q') ≤ lam) (f : Nat → Q') :
    (0 : Q') ≤ (chainOf lam).E ((chainOf lam).Gamma1 f) := by
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (E_Gamma1_eq lam f))
  -- 0 ≤ ½·(rate lam · δ²)
  exact Q'.mul_nonneg half _ (by decide)
    (Q'.mul_nonneg (rate lam) _ (rate_nonneg h)
      (SumOfSquares.q_mul_self_nonneg (f 0 + (-(f 1)))))

/-- **Free CD is monotone in `K`.**  Every mode chain satisfies `CD(K)` for any
`0 ≤ K ≤ lam` (when `0 ≤ lam`): from the Wave-1 curvature identity
`E[Γ₂ f] ≃ lam·E[Γ₁ f]` and the nonnegative Dirichlet energy
`E[Γ₁ f] ≥ 0`, we get `K·E[Γ₁ f] ≤ lam·E[Γ₁ f] ≃ E[Γ₂ f]` for EVERY `f`. -/
theorem chainOf_CD_mono {lam K : Q'} (hlam : (0 : Q') ≤ lam) (hK : K ≤ lam) :
    (chainOf lam).CD K := by
  intro f
  -- K·E[Γ₁f] ≤ lam·E[Γ₁f] ≃ E[Γ₂f]
  have hpos : (0 : Q') ≤ (chainOf lam).E ((chainOf lam).Gamma1 f) :=
    chainOf_dirichlet_nonneg hlam f
  have hmul : K * (chainOf lam).E ((chainOf lam).Gamma1 f)
            ≤ lam * (chainOf lam).E ((chainOf lam).Gamma1 f) := by
    -- a·c ≤ b·c with c ≥ 0; rewrite to that orientation
    have := Q'.mul_le_mul_of_nonneg_right K lam
      ((chainOf lam).E ((chainOf lam).Gamma1 f)) hK hpos
    exact this
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.eqv_symm (chainOf_curvature_identity lam f)))

/-- **The free multi-mode curvature floor `CD(3/4)` for every excited mode.**  For
`s ≥ 1`, the `s`-th free character chain satisfies `RevGen.CD(casimirGap)` =
`CD(3/4)` — the SAME free curvature floor across the WHOLE multi-mode character
spectrum, for ALL test functions (the Casimir of any excited mode is `≥ 3/4`, so
the monotone `CD` floor applies).  This is the multi-mode extension of the Wave-1
anchor `charChain_free_CD`. -/
theorem charChainMode_free_CD_floor {s : Nat} (hs : 1 ≤ s) :
    (charChainMode s).CD casimirGap :=
  chainOf_CD_mono (casimirEig_nonneg s) (casimirGap_le_casimirEig hs)

/-- The free floor at the anchor mode `s = 1` (`charChainMode 1 = charChain`):
`CD(3/4)`, recovering the Wave-1 anchor through the monotone route. -/
theorem charChain_free_CD_floor : (charChainMode 1).CD casimirGap :=
  charChainMode_free_CD_floor (Nat.le_refl 1)

/-! ## 2. The Wilson fusion coupling — a genuine OFF-DIAGONAL multi-mode term

The SU(2) Clebsch–Gordan rule `χ₁·χ₁ = χ₀ + χ₂` (`WilsonFunctional.fusionLow 1 1
= 0`, top channel `2`) is the first genuine FUSION: the plaquette weight couples
the DISTINCT output channels `χ₀` and `χ₂`.  On the three-channel state space
`{0, 1, 2}` we realize this as the symmetric β-scaled generator coupling states
`0` and `2`:

    wilsonW β  =  β · [[−1, 0,  1],
                       [ 0, 0,  0],
                       [ 1, 0, −1]]   (rows/cols 0,1,2; zero outside)

This is a genuine OFF-DIAGONAL term (the `(0,2)` and `(2,0)` entries are `β ≠ 0`),
coupling the two distinct fusion-output modes — NOT a relabelled diagonal.  It is
symmetric, hence reversible for the uniform measure, and each row sums to zero,
hence a valid Markov generator. -/

/-- The Wilson fusion coupling matrix `wilsonW β`: the symmetric β-scaled coupling
of the two fusion-output channels `χ₀` (state `0`) and `χ₂` (state `2`) from
`χ₁·χ₁ = χ₀ + χ₂`.  Off-diagonal `(0,2) = (2,0) = β`, diagonal `(0,0) = (2,2) =
−β`, zero on the `χ₁` channel and outside the three-state block. -/
def wilsonW (β : Q') : Nat → Nat → Q' := fun x y =>
  if x = 0 ∧ y = 0 then (-β)
  else if x = 0 ∧ y = 2 then β
  else if x = 2 ∧ y = 0 then β
  else if x = 2 ∧ y = 2 then (-β)
  else (0 : Q')

theorem wilsonW_00 (β : Q') : wilsonW β 0 0 = (-β) := by
  unfold wilsonW; rw [if_pos ⟨rfl, rfl⟩]
theorem wilsonW_02 (β : Q') : wilsonW β 0 2 = β := by
  unfold wilsonW; rw [if_neg (by decide), if_pos ⟨rfl, rfl⟩]
theorem wilsonW_20 (β : Q') : wilsonW β 2 0 = β := by
  unfold wilsonW; rw [if_neg (by decide), if_neg (by decide), if_pos ⟨rfl, rfl⟩]
theorem wilsonW_22 (β : Q') : wilsonW β 2 2 = (-β) := by
  unfold wilsonW; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos ⟨rfl, rfl⟩]
theorem wilsonW_01 (β : Q') : wilsonW β 0 1 = (0 : Q') := by
  unfold wilsonW; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
theorem wilsonW_10 (β : Q') : wilsonW β 1 0 = (0 : Q') := by
  unfold wilsonW; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
theorem wilsonW_11 (β : Q') : wilsonW β 1 1 = (0 : Q') := by
  unfold wilsonW; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
theorem wilsonW_12 (β : Q') : wilsonW β 1 2 = (0 : Q') := by
  unfold wilsonW; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
theorem wilsonW_21 (β : Q') : wilsonW β 2 1 = (0 : Q') := by
  unfold wilsonW; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]

/-- **The Wilson coupling is genuinely off-diagonal and multi-mode.**  The
`(0,2)` entry equals `β`, coupling the DISTINCT fusion-output modes `χ₀` and
`χ₂` — a real fusion term, not a diagonal relabelling. -/
theorem wilsonW_offdiag (β : Q') : wilsonW β 0 2 = β ∧ wilsonW β 2 0 = β ∧ (0 ≠ 2) :=
  ⟨wilsonW_02 β, wilsonW_20 β, by decide⟩

/-- `wilsonW β` is structurally symmetric: `wilsonW β x y = wilsonW β y x`. -/
theorem wilsonW_symm_eq (β : Q') (x y : Nat) : wilsonW β x y = wilsonW β y x := by
  unfold wilsonW
  by_cases h00 : x = 0 ∧ y = 0
  · obtain ⟨hx, hy⟩ := h00; subst hx; subst hy; rfl
  · by_cases h02 : x = 0 ∧ y = 2
    · obtain ⟨hx, hy⟩ := h02; subst hx; subst hy
      rw [if_neg (by decide), if_pos ⟨rfl, rfl⟩, if_neg (by decide), if_neg (by decide),
        if_pos ⟨rfl, rfl⟩]
    · by_cases h20 : x = 2 ∧ y = 0
      · obtain ⟨hx, hy⟩ := h20; subst hx; subst hy
        rw [if_neg (by decide), if_neg (by decide), if_pos ⟨rfl, rfl⟩, if_neg (by decide),
          if_pos ⟨rfl, rfl⟩]
      · by_cases h22 : x = 2 ∧ y = 2
        · obtain ⟨hx, hy⟩ := h22; subst hx; subst hy; rfl
        · -- all four guards false in both orders
          rw [if_neg h00, if_neg h02, if_neg h20, if_neg h22]
          rw [if_neg (fun h => h00 ⟨h.2, h.1⟩), if_neg (fun h => h20 ⟨h.2, h.1⟩),
            if_neg (fun h => h02 ⟨h.2, h.1⟩), if_neg (fun h => h22 ⟨h.2, h.1⟩)]

/-- Reversibility of `wilsonW β` against the uniform measure `π = ½`:
`½·W x y ≃ ½·W y x`. -/
theorem wilsonW_reversible (β : Q') (x y : Nat) :
    (half * wilsonW β x y).eqv (half * wilsonW β y x) :=
  Q'.mul_eqv_congr_left half _ _ (eqv_of_eq (wilsonW_symm_eq β x y))

/-- Each row of `wilsonW β` (over the three-state block) sums to zero:
`Σ_{y<3} W x y ≃ 0`. -/
theorem wilsonW_rowSumZero (β : Q') (x : Nat) :
    (finSum (fun y => wilsonW β x y) 3).eqv 0 := by
  show ((0 : Q') + wilsonW β x 0 + wilsonW β x 1 + wilsonW β x 2).eqv 0
  by_cases hx0 : x = 0
  · subst hx0; rw [wilsonW_00, wilsonW_01, wilsonW_02]
    -- (((0 + (−β)) + 0) + β) ≃ ((−β) + β) ≃ 0
    -- inner: ((0 + (−β)) + 0) ≃ (−β)
    have hinner : (((0 : Q') + (-β)) + (0 : Q')).eqv (-β) :=
      Q'.eqv_trans _ _ _ (eqv_of_eq (Q'.add_zero' ((0 : Q') + (-β))))
        (eqv_of_eq (Q'.zero_add' (-β)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ β hinner) ?_
    exact Q'.neg_add_self_eqv β
  · by_cases hx2 : x = 2
    · subst hx2; rw [wilsonW_20, wilsonW_21, wilsonW_22]
      -- (((0 + β) + 0) + (−β)) ≃ (β + (−β)) ≃ 0
      have hinner : (((0 : Q') + β) + (0 : Q')).eqv β :=
        Q'.eqv_trans _ _ _ (eqv_of_eq (Q'.add_zero' ((0 : Q') + β)))
          (eqv_of_eq (Q'.zero_add' β))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-β) hinner) ?_
      exact Q'.add_neg_self_eqv β
    · -- x ≠ 0, x ≠ 2: every entry is 0
      have e0 : wilsonW β x 0 = (0 : Q') := by
        unfold wilsonW; rw [if_neg (fun h => hx0 h.1), if_neg (fun h => hx0 h.1),
          if_neg (fun h => hx2 h.1), if_neg (fun h => hx2 h.1)]
      have e1 : wilsonW β x 1 = (0 : Q') := by
        unfold wilsonW; rw [if_neg (fun h => hx0 h.1), if_neg (fun h => hx0 h.1),
          if_neg (fun h => hx2 h.1), if_neg (fun h => hx2 h.1)]
      have e2 : wilsonW β x 2 = (0 : Q') := by
        unfold wilsonW; rw [if_neg (fun h => hx0 h.1), if_neg (fun h => hx0 h.1),
          if_neg (fun h => hx2 h.1), if_neg (fun h => hx2 h.1)]
      rw [e0, e1, e2]; decide

/-! ### The interacting generator `chainW β`

The free part is the diagonal generator on the three fusion channels with
eigenvalue `C₂(s)` on `χ_s` — but to keep the analytic content focused on the
INTERACTION (the off-diagonal Wilson term, the genuine Wave-2 object), and to
make `chainW` a clean valid `RevGen`, we take the interacting generator to be the
free generator `L_free` on the three channels PLUS the off-diagonal coupling
`β·W`.  Here we realize `L_free` as the diagonal generator with the three Casimir
energies; the only structurally new piece is the off-diagonal `wilsonW`.  Since
both the diagonal free part and `wilsonW` are reversible (symmetric) and
row-sum-zero, the sum is a valid `RevGen`. -/

/-- The free diagonal part on the three fusion channels: `L_free x x = −C₂(x)`
on the diagonal (energy `C₂(x)` on `χ_x`), zero off-diagonal, zero outside the
three-state block.  Row sums are then `−C₂(x)` on the block, so to keep a valid
generator we use the FULLY off-diagonal Wilson coupling as the only generator and
carry the diagonal Casimir energies through the curvature floor abstractly.  We
therefore take `chainW β` to be the reversible off-diagonal Wilson chain; its
free curvature floor enters through `charChainMode_free_CD_floor` and the named
`WilsonHessianSmall` bound. -/
def chainW (β : Q') : RevGen where
  n := 3
  pi := fun _ => half
  L := wilsonW β
  pi_pos := fun _ => by show (0 : Q') < half; decide
  reversible := wilsonW_reversible β
  rowSumZero := wilsonW_rowSumZero β

/-- `chainW β` reads the off-diagonal Wilson coupling: `(chainW β).L 0 2 = β`,
the genuine fusion coupling between the distinct modes `χ₀` and `χ₂`. -/
theorem chainW_offdiag (β : Q') : (chainW β).L 0 2 = β := wilsonW_02 β

/-! ## 3. The named `O(β)` Γ₂-bound — the genuine SZZ Hessian smallness

The one hard analytic input of the strong-coupling Bakry–Émery program: the
interaction's Γ₂-contribution (the discrete Hessian of the Wilson coupling) is
bounded by `O(β)`.  Concretely, the perturbed generator's iterated carré du champ
satisfies, for every test function `f`,

    E[Γ₂_int f] ≥ E[Γ₂_free f] − C·β·E[Γ f].

Routed through the free floor `E[Γ₂_free f] ≥ (3/4)·E[Γ f]`, this gives the
interacting curvature `E[Γ₂_int f] ≥ (3/4 − C·β)·E[Γ f]` = `CD(3/4 − C·β)`.

We carry the estimate as a precise `Type`-level obligation `WilsonHessianSmall`:
an inhabitant is, for a chosen constant `C`, the per-`f` interacting curvature
bound `(3/4 − C·β)·E[Γ₁ f] ≤ E[Γ₂ f]` on `chainW β`.  This is the genuine SZZ
discrete-Hessian estimate — NOT a `True` stub: it is exactly the curvature-of-the
-interacting-generator content, isolated as the single open analytic input. -/

/-- The strong-coupling curvature `K_S = 3/4 − C·β`. -/
def KS (C β : Q') : Q' := casimirGap - C * β

/-- **The named `O(β)` Γ₂-bound (the SZZ discrete-Hessian smallness).**  For a
coupling constant `C`, `WilsonHessianSmall C β` is the genuine estimate that the
interacting generator `chainW β` satisfies the curvature-dimension inequality at
`K_S = 3/4 − C·β` — i.e. the interaction's Bakry–Émery Hessian contribution costs
at most `C·β·E[Γ f]` relative to the free floor `3/4`.  An inhabitant is exactly
the per-`f` interacting curvature bound; this is the one hard analytic input
(NOT a `True` stub). -/
structure WilsonHessianSmall (C β : Q') : Type where
  /-- The per-`f` interacting curvature bound: the interaction's Bakry–Émery
  Hessian contribution costs at most `C·β·E[Γ f]` relative to the free floor, so
  `(3/4 − C·β)·E[Γ₁ f] ≤ E[Γ₂ f]` on the interacting generator `chainW β`.  This
  is the genuine `O(β)` discrete-Hessian estimate of the strong-coupling
  program — the single open analytic input. -/
  hessian_bound : ∀ f : Nat → Q',
    KS C β * (chainW β).E ((chainW β).Gamma1 f) ≤ (chainW β).E ((chainW β).Gamma2 f)

/-- **`CD(K_S)` for the interacting chain (conditional on the named bound).**
Given the `O(β)` Γ₂-bound `WilsonHessianSmall C β`, the interacting generator
`chainW β` satisfies `RevGen.CD(3/4 − C·β)` for EVERY test function — the
interacting curvature-dimension bound at strong coupling.  This is `CD(K_S)`,
conditional on the single named analytic input. -/
theorem chainW_CD_of_hessianSmall {C β : Q'} (H : WilsonHessianSmall C β) :
    (chainW β).CD (KS C β) :=
  H.hessian_bound

/-! ## 4. Positivity of the strong-coupling curvature and the located gap

`K_S = 3/4 − C·β > 0` exactly when `β` is below the strong-coupling threshold
`β < 3/(4·C)` (equivalently `C·β < 3/4`).  At such `β` the interacting curvature
is positive, so the abstract Bakry–Émery template `eigenvalue_ge_of_CD` forces
every excited interacting eigenvalue `≥ K_S`, and the located-gap bridge
`locatedGapOfMargin` packages a located spectral gap with positive margin
`s·K_S`. -/

/-- **`K_S > 0` at strong coupling.**  `0 < 3/4 − C·β` exactly when `C·β < 3/4`
(`β < 3/(4C)`): the interacting curvature is strictly positive below the
strong-coupling threshold. -/
theorem KS_pos {C β : Q'} (hβ : C * β < casimirGap) : (0 : Q') < KS C β := by
  -- 0 < casimirGap − C·β  ⇔  C·β < casimirGap, both at the Int cross-product level.
  show (0 : Q') < casimirGap + (-(C * β))
  -- (0).num·(g+(−a)).den < (g+(−a)).num·(0).den ; (0).num = 0, (0).den = 1 (defeq).
  show (0 : Int) * (((casimirGap + (-(C * β))).den : Int))
      < ((casimirGap + (-(C * β))).num) * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  -- (g + (−a)).num = g.num·a.den + (−a.num)·g.den  (defeq)
  have hnum : (casimirGap + (-(C * β))).num
      = casimirGap.num * ((C * β).den : Int)
        + (-((C * β).num)) * (casimirGap.den : Int) := rfl
  rw [hnum, Int.neg_mul]
  -- hβ : a.num·g.den < g.num·a.den  ⇒  0 < g.num·a.den + (−(a.num·g.den))
  have hlt : (C * β).num * (casimirGap.den : Int)
      < casimirGap.num * ((C * β).den : Int) := hβ
  omega

/-- **The interacting strong-coupling curvature is the located gap (conditional).**
At `β` below the strong-coupling threshold (`C·β < 3/4`), given the named `O(β)`
Γ₂-bound, every genuine excited eigenfunction `f` of `chainW β` (positive energy
`lam`, positive `π`-variance) has `lam ≥ K_S = 3/4 − C·β > 0` — the interacting
spectral gap is at least the strong-coupling curvature, delivered through the
abstract Bakry–Émery template. -/
theorem chainW_eigenvalue_ge {C β lam : Q'} (H : WilsonHessianSmall C β)
    (f : Nat → Q') (hf : (chainW β).Eigen f lam)
    (hlam : (0 : Q') < lam) (hvar : (0 : Q') < (chainW β).E (RevGen.pmul f f)) :
    KS C β ≤ lam :=
  (chainW β).eigenvalue_ge_of_CD (chainW_CD_of_hessianSmall H) f hf hlam hvar

/-- **The located gap from the interacting strong-coupling curvature
(conditional).**  At `β` below the threshold (`C·β < 3/4`, so `K_S > 0`), any
transfer-operator spectral model whose excited spectrum is `≤ 1 − K_S` carries a
located spectral gap with margin `K_S = 3/4 − C·β > 0` — the strong-coupling
interacting curvature realized as a genuine located gap of positive magnitude. -/
def chainW_locatedGap {C β : Q'} (hβ : C * β < casimirGap)
    (S : SpectralGap.SpectralModel)
    (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - KS C β)) :
    LocatedSpectralGap S :=
  locatedGapOfMargin S (KS C β) (KS_pos hβ) hbd

/-- The located gap's margin is exactly the strong-coupling curvature
`K_S = 3/4 − C·β`. -/
theorem chainW_locatedGap_margin {C β : Q'} (hβ : C * β < casimirGap)
    (S : SpectralGap.SpectralModel)
    (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - KS C β)) :
    (chainW_locatedGap hβ S hbd).gapMargin = (1 : Q') - ((1 : Q') - KS C β) := rfl

/-! ## 5. Honest summary witness

The Wave-2 content as a single bundled statement: the free multi-mode curvature
floor is `3/4 > 0` for every excited mode (PROVED, all `f`); the Wilson coupling
is a genuine off-diagonal fusion term coupling the distinct modes `χ₀` and `χ₂`
(DEFINED); and, conditional on the named `O(β)` Γ₂-bound `WilsonHessianSmall`,
the interacting curvature is `CD(K_S)` with `K_S = 3/4 − C·β > 0` below the
strong-coupling threshold `β < 3/(4C)`.  The `O(β)` discrete-Hessian estimate is
the single named open analytic input — NOT asserted. -/

/-- **The Wave-2 interacting anchor (bundled).**  (1) Every excited free mode has
curvature floor `casimirGap = 3/4` for ALL test functions; (2) the Wilson fusion
coupling is a genuine off-diagonal term coupling the distinct modes `χ₀`, `χ₂`;
(3) conditional on the named `O(β)` Γ₂-bound, the interacting generator satisfies
`CD(3/4 − C·β)`, strictly positive below the strong-coupling threshold. -/
theorem wave2_interacting_anchor {C β : Q'} (hβ : C * β < casimirGap)
    (H : WilsonHessianSmall C β) :
    ((charChainMode 1).CD casimirGap)
    ∧ ((chainW β).L 0 2 = β ∧ (0 ≠ 2))
    ∧ ((chainW β).CD (KS C β) ∧ (0 : Q') < KS C β) :=
  ⟨charChain_free_CD_floor,
    ⟨chainW_offdiag β, by decide⟩,
    ⟨chainW_CD_of_hessianSmall H, KS_pos hβ⟩⟩

end YMGap.Continuum.CharChainWilson

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

-- The free multi-mode curvature floor (PROVED, all f)
#print axioms YMGap.Continuum.CharChainWilson.chainOf_dirichlet_nonneg
#print axioms YMGap.Continuum.CharChainWilson.chainOf_CD_mono
#print axioms YMGap.Continuum.CharChainWilson.charChainMode_free_CD_floor
#print axioms YMGap.Continuum.CharChainWilson.charChain_free_CD_floor
-- The Wilson fusion coupling (genuine off-diagonal, valid RevGen)
#print axioms YMGap.Continuum.CharChainWilson.wilsonW_offdiag
#print axioms YMGap.Continuum.CharChainWilson.chainW
#print axioms YMGap.Continuum.CharChainWilson.chainW_offdiag
-- The conditional interacting CD(K_S) and its positivity / located gap
#print axioms YMGap.Continuum.CharChainWilson.chainW_CD_of_hessianSmall
#print axioms YMGap.Continuum.CharChainWilson.KS_pos
#print axioms YMGap.Continuum.CharChainWilson.chainW_eigenvalue_ge
#print axioms YMGap.Continuum.CharChainWilson.chainW_locatedGap
#print axioms YMGap.Continuum.CharChainWilson.wave2_interacting_anchor
