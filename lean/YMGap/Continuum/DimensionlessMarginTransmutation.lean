/-
Track B / R2 — **DIMENSIONAL TRANSMUTATION assembled: the dimensionless physical
margin, its multiplicative recursion, and the uniform continuum floor.**

# What this module does (read first)

`BlockSpinMarginConstruction` machine-REFUTED the naive identification: the
fixed-spacing eigenvalue margin `1 − w_k³` (in LATTICE units) erodes to `0` as
`w_k → 1`, so it CANNOT satisfy the multiplicative single-step recursion with a
positive floor.  The missing ingredient is the **dimensionful spacing rescaling**
`b^k` (the accumulated block factor) that turns the eroding lattice gap into the
RG-invariant DIMENSIONLESS margin `m_lat(a_k)/a_k`.

`CodynamicTransmutation` / `CodynamicCRealFlow` supplied exactly that rescaling as
the conserved-margin invariant along a self-similar flow, and — crucially — built
the genuine constructive-real inhabitant of the flow law (`concreteSelfSimilarFlow`,
`concreteCRealFlowE`) that no rational flow can inhabit (the `(b+1)`-th-root flow is
IRRATIONAL).  The exp-on-CReal residual (Λ = exp) is therefore ALREADY discharged
downstream: the separators `sep k = e^{−(e^{−1})/(b+1)^k}` are honest irrational
`CReal`s and `marginInvariantC` proves the rescaled margin is conserved.

This module ASSEMBLES those pieces into the named object the construction wanted:

  * **`dimMargin b s N`** — the DIMENSIONLESS margin `(1 − sep N)·∏_{j≤N} geomSumC`,
    the eroding lattice margin `1 − sep N → 0` TIMES the spacing rescaling
    `∏ geomSumC ≈ (b+1)^N` (`= 1/a_N`).  Its transmutation value is the CONSERVED
    constant `1 − sep 0 > 0` (`dimMargin_conserved`, from `marginInvariantC`).

  * **`dimMargin_multiplicative_recursion`** — the transmuted margin SATISFIES the
    multiplicative single-step recursion `(1 − δ_N)·dimMargin N ≤ dimMargin (N+1)`
    (in the eventual `CReal` order `leEv`) for EVERY defect sequence `0 ≤ δ ≤ 1` —
    the recursion the eroding lattice margin FAILED (`eigMargin_fails_singleStep`),
    now HOLDS for the dimensionless margin.

  * **`uniformContinuumFloor`** — a single positive rational `c > 0` bounds
    `dimMargin b s N` from below at EVERY scale `N` simultaneously (the uniform
    positive continuum floor), because the margin is conserved.

  * The concrete `*_concreteE` versions are UNCONDITIONAL along the genuinely
    IRRATIONAL `e^{−1}`-seeded self-similar flow (`concreteCRealFlowE 1`).

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9) — the crux of the whole problem

The dimensional transmutation KINEMATICS are now genuinely constructed: the
dimensionless margin `(1 − sep N)·(b+1)^N → m_phys = 1 − sep 0 > 0` along a REAL
irrational constructive-real self-similar flow, the spacing rescaling `∏ geomSumC`
being tied to the block factor `b` (NOT a free parameter), and the multiplicative
recursion — impossible for the eroding lattice margin — HOLDS.

**BUT this is the ZERO-DEFECT idealization.**  `dimMargin` is PERFECTLY conserved
(`dimMargin N ≃ dimMargin (N+1)`), so the multiplicative recursion
`(1 − δ_N)·dimMargin N ≤ dimMargin (N+1)` holds for ANY `0 ≤ δ_N ≤ 1` — INCLUDING
`δ ≡ 0`.  That universality is precisely the "multiplicative surrogate (`ε ≡ 0`)"
that `TrueMarginRecursionPhysical` flags as EVADING the real physics: the ideal
self-similar flow has NO block-spin defect, whereas the real 4D SU(2) flow deviates
from self-similarity, and that deviation is the ADDITIVE erosion `ε_k`.  So this
module constructs the transmutation MECHANISM and proves the multiplicative
recursion is now satisfiable by the RIGHT (dimensionless, conserved) object — it
does NOT close the mass gap, because the genuine residual is the REAL flow's
deviation from the ideal (the summable additive block-spin defect `ε_k` of
`TrueMarginRecursionPhysical`), untouched here.

**No guarded bundle is inhabited.**  `dimMargin` is `CReal`-valued (the ideal
irrational flow), NOT the rational `SingleStepDefectBound.trueMargin`, NOT tied to
`afDefectSeq`, and NOT a `TrueMarginRecursion` / `UniformSpacingFloor` / `FrontierDAG`
inhabitant.  A rational constant surrogate `trueMargin := fun _ => c` (c below the
irrational `1 − sep 0`) WOULD trivially inhabit the multiplicative
`SingleStepDefectBound` — that is exactly the `ε ≡ 0` fake, and it is DELIBERATELY
NOT written here (Rule 9(1)).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `CodynamicCRealFlow` / `TuranPositivity` backbone plus one
elementary `Q'` scalar inequality.  Every load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data (Rule 8).
-/

import YMGap.Continuum.CodynamicCRealFlow

namespace YMGap.Continuum.DimensionlessMarginTransmutation

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicCRealFlow

/-! ## 1. The elementary `Q'` scalar inequality (the recursion engine)

For `0 ≤ c ≤ 1` and `0 ≤ a + ε`, `c·a ≤ a + ε`.  This is the scalar core of
"degrading a nonnegative quantity by a factor `c ≤ 1` keeps it below the original
(up to the same eventual slack)".  Pure additive/multiplicative `Q'` algebra. -/

/-- **The scalar contraction inequality.**  `c·a ≤ a + ε` for `0 ≤ c ≤ 1` and
`0 ≤ a + ε`.  Proof: `c·a ≤ c·a + (1−c)·(a+ε)` (the added term is `≥ 0`), and
`c·a + (1−c)·(a+ε) ≃ a + (1−c)·ε ≤ a + ε` (since `(1−c)·ε ≤ ε`). -/
theorem scalarMul_le_add {a c ε : Q'} (hε : (0 : Q') < ε) (hae : (0 : Q') ≤ a + ε)
    (hc0 : (0 : Q') ≤ c) (hc1 : c ≤ (1 : Q')) : c * a ≤ a + ε := by
  have hmc0 : (0 : Q') ≤ (1 : Q') - c := Q'.sub_nonneg_of_le hc1
  have hprod : (0 : Q') ≤ ((1 : Q') - c) * (a + ε) := Q'.mul_nonneg _ _ hmc0 hae
  have hI : c * a ≤ c * a + ((1 : Q') - c) * (a + ε) :=
    Q'.add_le_self_of_nonneg (c * a) _ hprod
  -- chain: c*a + (1-c)*(a+ε) ≃ a + (1-c)*ε
  have hexp : (((1 : Q') - c) * (a + ε)).eqv (((1 : Q') - c) * a + ((1 : Q') - c) * ε) :=
    Q'.mul_add_eqv ((1 : Q') - c) a ε
  have hstep1 : (c * a + ((1 : Q') - c) * (a + ε)).eqv
      (c * a + (((1 : Q') - c) * a + ((1 : Q') - c) * ε)) :=
    Q'.add_eqv_congr_left (c * a) _ _ hexp
  have hstep2 : (c * a + (((1 : Q') - c) * a + ((1 : Q') - c) * ε)).eqv
      ((c * a + ((1 : Q') - c) * a) + ((1 : Q') - c) * ε) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (c * a) (((1 : Q') - c) * a) (((1 : Q') - c) * ε))
  have hsum : (c * a + ((1 : Q') - c) * a).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ExpNeg.add_mul_eqv c ((1 : Q') - c) a)) ?_
    have hone : (c + ((1 : Q') - c)).eqv (1 : Q') := by
      show (c + ((1 : Q') + -c)).eqv (1 : Q')
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left c _ _ (Q'.add_comm_eqv (1 : Q') (-c))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv c (-c) (1 : Q'))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (1 : Q') (Q'.add_neg_self_eqv c)) ?_
      exact QPoly.q_zero_add_eqv (1 : Q')
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a hone) ?_
    exact Q'.one_mul_eqv a
  have hstep3 : ((c * a + ((1 : Q') - c) * a) + ((1 : Q') - c) * ε).eqv
      (a + ((1 : Q') - c) * ε) :=
    Q'.add_eqv_congr_right _ _ (((1 : Q') - c) * ε) hsum
  have hchain : (c * a + ((1 : Q') - c) * (a + ε)).eqv (a + ((1 : Q') - c) * ε) :=
    Q'.eqv_trans _ _ _ hstep1 (Q'.eqv_trans _ _ _ hstep2 hstep3)
  -- (1-c) ≤ 1  and hence (1-c)*ε ≤ ε
  have hnegc : -c ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hc0) (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0))
  have hmc1 : (1 : Q') - c ≤ (1 : Q') := by
    show (1 : Q') + -c ≤ (1 : Q')
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_left (1 : Q') (-c) 0 hnegc)
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv (1 : Q')))
  have hcε : ((1 : Q') - c) * ε ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right ((1 : Q') - c) 1 ε hmc1 (Q'.le_of_lt hε))
      (Q'.le_of_eqv (Q'.one_mul_eqv ε))
  have hII : a + ((1 : Q') - c) * ε ≤ a + ε := Q'.add_le_add_left a _ _ hcε
  exact Q'.le_trans' _ _ _ hI (Q'.le_trans' _ _ _ (Q'.le_of_eqv hchain) hII)

/-! ## 2. The dimensionless margin -/

/-- **THE DIMENSIONLESS PHYSICAL MARGIN** at RG scale `N`:

    dimMargin b s N  =  (1 − sep N) · ∏_{j=1}^{N} geomSumC (sep j, b+1) ,

the eroding lattice margin `1 − sep N` (→ 0 as `sep N → 1`, deep UV) TIMES the
accumulated spacing rescaling `∏ geomSumC ≈ (b+1)^N = 1/a_N`.  Along a self-similar
flow this is the RG-INVARIANT `m_lat(a_N)/a_N`, conserved to `1 − sep 0 > 0`
(§3) — the dimensional-transmutation object the eroding lattice margin was NOT. -/
def dimMargin (b : Nat) (s : Nat → CReal) (N : Nat) : CReal :=
  CReal.mul (CReal.sub CReal.cone (s N))
    (cprodTail (fun j => geomSumC (s j) (b + 1)) N)

/-! ## 3. Transmutation: the dimensionless margin is CONSERVED -/

/-- **THE TRANSMUTATION IDENTITY.**  Under the CReal flow law the dimensionless
margin is conserved: `dimMargin b s N ≃ 1 − sep 0` at every scale.  This IS
dimensional transmutation — the eroding lattice margin `1 − sep N → 0` times the
diverging spacing rescaling `∏ geomSumC → ∞` stays at the fixed positive constant
`1 − sep 0`.  Directly `marginInvariantC`. -/
theorem dimMargin_conserved {b : Nat} {s : Nat → CReal}
    (hss : selfSimilarC b s) (N : Nat) :
    CReal.Equiv (dimMargin b s N) (CReal.sub CReal.cone (s 0)) :=
  marginInvariantC hss N

/-- Eventual order from limit-equality: `Equiv A B → leEv A B` (the `.1` projection
of the two-sided `Equiv` bound). -/
theorem leEv_of_equiv {A B : CReal} (h : CReal.Equiv A B) : CReal.leEv A B := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => (hN n hn).1⟩

/-- **The margin is scale-invariant** (both consecutive values equal `1 − sep 0`):
`dimMargin b s N ≃ dimMargin b s (N+1)`. -/
theorem dimMargin_step_equiv {b : Nat} {s : Nat → CReal}
    (hss : selfSimilarC b s) (N : Nat) :
    CReal.Equiv (dimMargin b s N) (dimMargin b s (N + 1)) :=
  CReal.Equiv.trans (dimMargin_conserved hss N)
    (CReal.Equiv.symm (dimMargin_conserved hss (N + 1)))

/-! ## 4. The multiplicative single-step recursion — the recursion the lattice
margin FAILED, now HELD by the dimensionless margin -/

/-- **The scalar contraction on a nonnegative `CReal`.**  For `0 ≤ c ≤ 1` and a
`CReal` `A` with `A ≥ 0` (`geRat A 0`), `c·A ≤ A` in the eventual order `leEv`. -/
theorem scalar_le_self {A : CReal} (hA : ExpPos.geRat A 0) {c : Q'}
    (hc0 : (0 : Q') ≤ c) (hc1 : c ≤ (1 : Q')) :
    CReal.leEv (CReal.mul (CReal.ofQ' c) A) A := by
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨N, fun n hn => ?_⟩
  show c * A.approx n ≤ A.approx n + ε
  exact scalarMul_le_add hε (hN n hn) hc0 hc1

/-- **THE MULTIPLICATIVE SINGLE-STEP RECURSION FOR THE DIMENSIONLESS MARGIN.**  For
EVERY defect sequence `0 ≤ δ ≤ 1`,

    (1 − δ_N) · dimMargin b s N  ≤  dimMargin b s (N+1)     (eventual order `leEv`),

along any self-similar CReal flow with a nonnegative margin.  This is EXACTLY the
recursion the eroding fixed-spacing eigenvalue margin `1 − w_k³` machine-FAILED
(`BlockSpinMarginConstruction.eigMargin_fails_singleStep`): the dimensionless margin
degrades by the per-step defect factor `(1 − δ_N)` and stays above the next scale,
because it is conserved.  (That it holds for ANY `δ`, including `δ ≡ 0`, is the
honest signal that the multiplicative form is the `ε ≡ 0` surrogate — see the module
docstring / §6.) -/
theorem dimMargin_multiplicative_recursion {b : Nat} {s : Nat → CReal}
    (hss : selfSimilarC b s) (hpos : ∀ N, ExpPos.geRat (dimMargin b s N) 0)
    {δ : Nat → Q'} (hδ0 : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ (1 : Q')) (N : Nat) :
    CReal.leEv (CReal.mul (CReal.ofQ' ((1 : Q') - δ N)) (dimMargin b s N))
      (dimMargin b s (N + 1)) := by
  have hc0 : (0 : Q') ≤ (1 : Q') - δ N := Q'.sub_nonneg_of_le (hδ1 N)
  have hc1 : (1 : Q') - δ N ≤ (1 : Q') := by
    have hnegc : -(δ N) ≤ (0 : Q') :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg (hδ0 N))
        (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0))
    show (1 : Q') + -(δ N) ≤ (1 : Q')
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_left (1 : Q') (-(δ N)) 0 hnegc)
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv (1 : Q')))
  exact CReal.leEv_trans (scalar_le_self (hpos N) hc0 hc1)
    (leEv_of_equiv (dimMargin_step_equiv hss N))

/-! ## 5. The uniform continuum floor -/

/-- **THE UNIFORM POSITIVE CONTINUUM FLOOR.**  A single positive rational `c` bounds
the dimensionless margin from below at EVERY scale `N` simultaneously:

    ∃ c > 0, ∀ N,  c ≤ dimMargin b s N     (eventual order `leEv (ofQ' c) …`).

The uniformity (one `c` for all `N`) is precisely dimensional transmutation: the
margin is conserved to the fixed `1 − sep 0`, so its floor does not degrade with the
scale.  The floor's existence is genuinely propositional (it is extracted from
`PosEv`, itself an `∃`), so it is stated as `∃` (Rule 2), given the base UV margin
`PosEv (1 − sep 0)`. -/
theorem uniformContinuumFloor {b : Nat} {s : Nat → CReal}
    (hss : selfSimilarC b s) (hM : PosEv (CReal.sub CReal.cone (s 0))) :
    ∃ c : Q', (0 : Q') < c ∧ ∀ N, CReal.leEv (CReal.ofQ' c) (dimMargin b s N) := by
  obtain ⟨ε, hε, Nε, hNε⟩ := eventually_ge_of_posEv hM
  refine ⟨ε, hε, fun N => ?_⟩
  intro δ hδ
  obtain ⟨N1, hN1⟩ := dimMargin_conserved hss N δ hδ
  refine ⟨max Nε N1, fun n hn => ?_⟩
  have hnε : Nε ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show ε ≤ (dimMargin b s N).approx n + δ
  exact Q'.le_trans' _ _ _ (hNε n hnε) (hN1 n hn1).2

/-! ## 6. UNCONDITIONAL instances along the genuinely IRRATIONAL `e^{−1}` flow

`concreteCRealFlowE 1` is the `e^{−1}`-seeded self-similar CReal flow (block factor
`b = 1`) — separators `e^{−(e^{−1})/2^k}`, genuinely irrational, satisfying the flow
law the rational `polyFlow` provably fails.  Its base UV margin
`baseMargin_posC_concreteE` and per-scale positivity `marginBudget_posC_concreteE`
are UNCONDITIONAL, so the transmutation, recursion, and floor below are too. -/

/-- The dimensionless margin along the concrete irrational flow is `≥ 0` at every
scale (from `marginBudget_posC_concreteE`). -/
theorem geRat_dimMargin_concreteE (N : Nat) :
    ExpPos.geRat (dimMargin 1 (concreteCRealFlowE 1).s N) 0 :=
  geRat_zero_of_posEv (marginBudget_posC_concreteE N)

/-- **TRANSMUTATION, UNCONDITIONAL.**  The dimensionless margin along the irrational
`e^{−1}` self-similar flow is conserved to `1 − sep 0` at every scale. -/
theorem dimMargin_conserved_concreteE (N : Nat) :
    CReal.Equiv (dimMargin 1 (concreteCRealFlowE 1).s N)
      (CReal.sub CReal.cone ((concreteCRealFlowE 1).s 0)) :=
  dimMargin_conserved (concreteCRealFlowE 1).ss N

/-- **MULTIPLICATIVE RECURSION, UNCONDITIONAL.**  For every defect `0 ≤ δ ≤ 1`, the
dimensionless margin along the irrational `e^{−1}` flow satisfies the multiplicative
single-step recursion — the recursion the eroding lattice margin failed. -/
theorem multiplicativeRecursion_concreteE {δ : Nat → Q'}
    (hδ0 : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ (1 : Q')) (N : Nat) :
    CReal.leEv (CReal.mul (CReal.ofQ' ((1 : Q') - δ N))
        (dimMargin 1 (concreteCRealFlowE 1).s N))
      (dimMargin 1 (concreteCRealFlowE 1).s (N + 1)) :=
  dimMargin_multiplicative_recursion (concreteCRealFlowE 1).ss
    geRat_dimMargin_concreteE hδ0 hδ1 N

/-- **UNIFORM CONTINUUM FLOOR, UNCONDITIONAL.**  A single positive rational bounds
the dimensionless margin below at every scale along the irrational `e^{−1}`
self-similar flow — the transmuted continuum floor, with NO open hypothesis. -/
theorem uniformContinuumFloor_concreteE :
    ∃ c : Q', (0 : Q') < c ∧
      ∀ N, CReal.leEv (CReal.ofQ' c) (dimMargin 1 (concreteCRealFlowE 1).s N) :=
  uniformContinuumFloor (concreteCRealFlowE 1).ss baseMargin_posC_concreteE

/-! ## 7. Honest verdict (documentation carrier) -/

/-- **HONEST VERDICT.**  This module ASSEMBLES the dimensional-transmutation
kinematics: `dimMargin` is the genuine dimensionless margin `(1 − sep N)·(b+1)^N`,
CONSERVED to `1 − sep 0 > 0` along a REAL irrational constructive-real self-similar
flow (`dimMargin_conserved_concreteE`), satisfying the multiplicative single-step
recursion the eroding lattice margin machine-FAILED
(`multiplicativeRecursion_concreteE`) with a uniform positive continuum floor
(`uniformContinuumFloor_concreteE`).  The spacing rescaling `∏ geomSumC ≈ (b+1)^N`
is TIED to the block factor `b`, NOT a free parameter — the transmutation is genuine,
not a relabeling, and the exp-on-CReal residual is discharged (irrational `e^{−1}`
separators).

It does NOT close the 4D Yang–Mills mass gap.  `dimMargin` is the ZERO-DEFECT
idealization: it is PERFECTLY conserved, so the multiplicative recursion holds for
ANY `0 ≤ δ ≤ 1` (`multiplicativeRecursion_concreteE` is parametric in `δ`) — the
`ε ≡ 0` multiplicative surrogate `TrueMarginRecursionPhysical` flags.  The genuine
open residual is the REAL 4D SU(2) block-spin flow's DEVIATION from self-similarity —
the ADDITIVE erosion `ε_k` — and its summability + anchor-dominance, untouched here.
No guarded bundle (`SingleStepDefectBound`, `TrueMarginRecursion`,
`UniformSpacingFloor`, `FrontierDAG`, `ClayTarget`) is inhabited; the rational
constant surrogate that WOULD inhabit the multiplicative `SingleStepDefectBound` is
the `ε ≡ 0` fake, deliberately refused.  The 4D Yang–Mills mass gap remains OPEN;
nothing is faked. -/
theorem dimensionlessMargin_honesty : True := trivial

end YMGap.Continuum.DimensionlessMarginTransmutation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.scalarMul_le_add
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.dimMargin_conserved
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.leEv_of_equiv
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.dimMargin_step_equiv
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.scalar_le_self
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.dimMargin_multiplicative_recursion
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.uniformContinuumFloor
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.geRat_dimMargin_concreteE
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.dimMargin_conserved_concreteE
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.multiplicativeRecursion_concreteE
#print axioms YMGap.Continuum.DimensionlessMarginTransmutation.uniformContinuumFloor_concreteE
