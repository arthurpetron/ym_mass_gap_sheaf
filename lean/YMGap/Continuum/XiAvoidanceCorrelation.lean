/-
`XiAvoidanceCorrelation` — Milestone 13.1, D1-loopy step 7: the AVOIDANCE-
CORRELATION INEQUALITY — the one remaining sign-layer piece after
`XiSignLayer` — PROVED, and the truncated two-point numerator pinned to its
EXACT four-cell normal form.

# The two identities and the inequality

In the four-cell notation of `XiSignLayer` (`B := XiB2` both-covered,
`D := cellD`, `E := cellE` single-cross cells, `A := cellA = A₁₂`
double-avoidance, `Ξ = B + D + E + A`):

  * **`avoidance_mayer` (exact, subtraction-free):**
        A·Ξ + E·D  ≃  Av(b₁)·Av(b₂) + A·B
    — i.e. `A₁₂·Ξ − Av(b₁)·Av(b₂) = A·B − E·D`: the avoidance-correlation
    defect IS the cell-product cross difference.
  * **`avoidance_correlation` (the inequality, PROVED):**
        A₁₂·Ξ  ≤  Av(b₁)·Av(b₂) + A₁₂·XiB2
    (drop `E·D ≥ 0`).  The double-avoidance correlation exceeds the product
    of single avoidances by AT MOST the (small, chain-majorized) both-covered
    cell times the avoidance itself.
  * **`truncated_numerator_mayer` (exact):**
        XiB2·Ξ + E·D  ≃  XiB(b₁)·XiB(b₂) + A·B
    — the truncated two-point numerator in PURE cell form:
    `T·Ξ² = A·B − E·D`.  The Ursell-sign content of the two-point function
    is EXACTLY "double-avoidance × double-cover minus the two single-cross
    cells".
  * **`truncated_numerator_le_chain` (the grand corollary, PROVED):**
        XiB2·Ξ  ≤  XiB(b₁)·XiB(b₂)
                    + Ξ·(actSum(br₁∧br₂)·Ξ + actSum(br₁)·XiB(b₂)
                        + actSum(br₂)·XiB(b₁))
    — chaining `A ≤ Ξ` and the two-marker chain majorant
    (`XiChainBound.XiB2_le_chain`) through `A·B`: the truncated numerator is
    dominated by the product term plus `Ξ` times the chain envelope, whose
    diagonal (`actSum(br₁∧br₂)`) is exactly the bridging-activity sum with
    the (D2) size floor and KP domination of `LoopyPinnedPenroseUrsell`.

# What remains open (AGENTS.md Rule 6 — the sharpness front)

The identities are EXACT and the bounds PROVED.  The remaining Ursell
content is now a SHARPNESS question, not a sign question: in
`T·Ξ² = A·B − E·D`, the non-decaying parts of `A·B` cancel against `E·D`
(connectedness cancellation), and extracting a SEPARATION-DECAYING envelope
for the difference (rather than for `A·B` alone) is the remaining
cluster-expansion content.  Not closed here; no frontier type is touched;
the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.XiSignLayer

namespace YMGap.Continuum.XiAvoidanceCorrelation

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPinnedBridge
open YMGap.Continuum.XiChainBound
open YMGap.Continuum.XiSignLayer
open YMGap.Continuum.RingNormaliser

variable {L : Lattice}

/-! ## 1. The two 4-variable polynomial cores (ring-normaliser payloads) -/

/-- `x₀ = B`, `x₁ = D`, `x₂ = E`, `x₃ = A`; the shared 4-sum. -/
private def sum4 : PolyExpr :=
  .add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)

/-- LHS: `A·(B+D+E+A) + E·D`. -/
def avLHS : PolyExpr :=
  .add (.mul (.var 3) sum4) (.mul (.var 2) (.var 1))

/-- RHS: `(E+A)·(D+A) + A·B`. -/
def avRHS : PolyExpr :=
  .add
    (.mul (.add (.var 2) (.var 3)) (.add (.var 1) (.var 3)))
    (.mul (.var 3) (.var 0))

theorem av_normal_eq : normalize avLHS = normalize avRHS := by decide

/-- **`avoid_expand` (PROVED by the reflective normaliser).**
`A(B+D+E+A) + ED ≃ (E+A)(D+A) + AB`. -/
theorem avoid_expand (B D E A : Q') :
    (A * (B + D + E + A) + E * D).eqv ((E + A) * (D + A) + A * B) := by
  have h := poly_identity_of_normal_eq avLHS avRHS av_normal_eq
    (fun i => if i = 0 then B else if i = 1 then D else if i = 2 then E else A)
  simpa [eval, avLHS, avRHS, sum4] using h

/-- LHS: `B·(B+D+E+A) + E·D`. -/
def tnLHS : PolyExpr :=
  .add (.mul (.var 0) sum4) (.mul (.var 2) (.var 1))

/-- RHS: `(B+D)·(B+E) + A·B`. -/
def tnRHS : PolyExpr :=
  .add
    (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 2)))
    (.mul (.var 3) (.var 0))

theorem tn_normal_eq : normalize tnLHS = normalize tnRHS := by decide

/-- **`truncated_expand` (PROVED by the reflective normaliser).**
`B(B+D+E+A) + ED ≃ (B+D)(B+E) + AB`. -/
theorem truncated_expand (B D E A : Q') :
    (B * (B + D + E + A) + E * D).eqv ((B + D) * (B + E) + A * B) := by
  have h := poly_identity_of_normal_eq tnLHS tnRHS tn_normal_eq
    (fun i => if i = 0 then B else if i = 1 then D else if i = 2 then E else A)
  simpa [eval, tnLHS, tnRHS, sum4] using h

/-! ## 2. Cell monotonicity: `A₁₂ ≤ Ξ` -/

variable [DecidableEq L.Plaquette]

/-- The double-avoidance cell is dominated by the full restricted sum. -/
theorem cellA_le_XiR {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    cellA w qP b1 b2 Γ label ≤ XiR w qP Γ label := by
  unfold cellA XiR
  refine polySum_filter_mono hw label _ _ ?_ _
  intro S h
  obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨h2, _⟩ := (Bool.and_eq_true _ _).mp h1
  exact h2

/-! ## 3. The exact identities (four-cell congruence chaining) -/

/-- **`avoidance_mayer` (PROVED — the exact avoidance-correlation identity).**

    A₁₂·Ξ + E·D  ≃  Av(b₁)·Av(b₂) + A₁₂·XiB2. -/
theorem avoidance_mayer (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (cellA w qP b1 b2 Γ label * XiR w qP Γ label
        + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label).eqv
      (XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label) := by
  have hXi : (XiR w qP Γ label).eqv
      (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label
        + cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label) := by
    refine Q'.eqv_trans _ _ _ (xi_partition_b1 w qP b1 Γ label) ?_
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_both _ _ _ _ (xib1_partition w qP b1 b2 Γ label)
        (xiavoid1_partition w qP b1 b2 Γ label)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  have hcore := avoid_expand (XiB2 w qP b1 b2 Γ label)
    (cellD w qP b1 b2 Γ label) (cellE w qP b1 b2 Γ label)
    (cellA w qP b1 b2 Γ label)
  have hL : (cellA w qP b1 b2 Γ label * XiR w qP Γ label
      + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label).eqv
      (cellA w qP b1 b2 Γ label
          * (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label
            + cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)
        + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label) :=
    add_eqv_congr_both _ _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hXi) (Q'.eqv_refl _)
  have hR : ((cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)
        * (cellD w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)
      + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label).eqv
      (XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label) :=
    add_eqv_congr_both _ _ _ _
      (mul_eqv_congr_both
        (Q'.eqv_symm (xiavoid1_partition w qP b1 b2 Γ label))
        (Q'.eqv_symm (xiavoid2_partition w qP b1 b2 Γ label)))
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ hcore hR)

/-- **`truncated_numerator_mayer` (PROVED — `T·Ξ² = A·B − E·D`, stated
subtraction-free).**

    XiB2·Ξ + E·D  ≃  XiB(b₁)·XiB(b₂) + A₁₂·XiB2. -/
theorem truncated_numerator_mayer (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
        + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label).eqv
      (XiB w qP b1 Γ label * XiB w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label) := by
  have hXi : (XiR w qP Γ label).eqv
      (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label
        + cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label) := by
    refine Q'.eqv_trans _ _ _ (xi_partition_b1 w qP b1 Γ label) ?_
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_both _ _ _ _ (xib1_partition w qP b1 b2 Γ label)
        (xiavoid1_partition w qP b1 b2 Γ label)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  have hcore := truncated_expand (XiB2 w qP b1 b2 Γ label)
    (cellD w qP b1 b2 Γ label) (cellE w qP b1 b2 Γ label)
    (cellA w qP b1 b2 Γ label)
  have hL : (XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
      + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label).eqv
      (XiB2 w qP b1 b2 Γ label
          * (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label
            + cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)
        + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label) :=
    add_eqv_congr_both _ _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hXi) (Q'.eqv_refl _)
  have hR : ((XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label)
        * (XiB2 w qP b1 b2 Γ label + cellE w qP b1 b2 Γ label)
      + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label).eqv
      (XiB w qP b1 Γ label * XiB w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label) :=
    add_eqv_congr_both _ _ _ _
      (mul_eqv_congr_both
        (Q'.eqv_symm (xib1_partition w qP b1 b2 Γ label))
        (Q'.eqv_symm (xib2_partition w qP b1 b2 Γ label)))
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ hcore hR)

/-! ## 4. The inequalities -/

/-- **`avoidance_correlation` (PROVED — THE remaining sign-layer piece).**

    A₁₂·Ξ  ≤  Av(b₁)·Av(b₂) + A₁₂·XiB2. -/
theorem avoidance_correlation {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    cellA w qP b1 b2 Γ label * XiR w qP Γ label
      ≤ XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label := by
  have h1 : cellA w qP b1 b2 Γ label * XiR w qP Γ label
      ≤ cellA w qP b1 b2 Γ label * XiR w qP Γ label
        + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label :=
    Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (polySum_nonneg hw label _)
        (polySum_nonneg hw label _))
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_of_eqv (avoidance_mayer w qP b1 b2 Γ label))

/-- **`truncated_numerator_le_chain` (PROVED — the grand corollary).**  The
truncated two-point numerator is dominated by the product term plus `Ξ`
times the two-marker chain majorant:

    XiB2·Ξ ≤ XiB(b₁)·XiB(b₂)
              + Ξ·(actSum(br₁∧br₂)·Ξ + actSum(br₁)·XiB(b₂)
                  + actSum(br₂)·XiB(b₁)). -/
theorem truncated_numerator_le_chain {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
      ≤ XiB w qP b1 Γ label * XiB w qP b2 Γ label
        + XiR w qP Γ label
            * (actSum w (Γ.filter (fun X => b1 X && b2 X)) label
                  * XiR w qP Γ label
                + actSum w (Γ.filter b1) label * XiB w qP b2 Γ label
                + actSum w (Γ.filter b2) label * XiB w qP b1 Γ label) := by
  -- step 1: drop E·D through the exact identity
  have h1 : XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
      ≤ XiB w qP b1 Γ label * XiB w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label := by
    have h0 : XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
        ≤ XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
          + cellE w qP b1 b2 Γ label * cellD w qP b1 b2 Γ label :=
      Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (polySum_nonneg hw label _)
          (polySum_nonneg hw label _))
    exact Q'.le_trans' _ _ _ h0
      (Q'.le_of_eqv (truncated_numerator_mayer w qP b1 b2 Γ label))
  -- step 2: A·B ≤ Ξ·B ≤ Ξ·(chain majorant)
  have h2 : cellA w qP b1 b2 Γ label * XiB2 w qP b1 b2 Γ label
      ≤ XiR w qP Γ label
          * (actSum w (Γ.filter (fun X => b1 X && b2 X)) label
                * XiR w qP Γ label
              + actSum w (Γ.filter b1) label * XiB w qP b2 Γ label
              + actSum w (Γ.filter b2) label * XiB w qP b1 Γ label) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (cellA_le_XiR hw qP b1 b2 Γ label)
        (polySum_nonneg hw label _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (XiB2_le_chain hw b1 b2 label Γ qP)
      (polySum_nonneg hw label _)
  exact Q'.le_trans' _ _ _ h1
    (Q'.add_le_add (Q'.le_refl' _) h2)

end YMGap.Continuum.XiAvoidanceCorrelation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.XiAvoidanceCorrelation.av_normal_eq
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.avoid_expand
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.tn_normal_eq
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.truncated_expand
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.cellA_le_XiR
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.avoidance_mayer
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.truncated_numerator_mayer
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.avoidance_correlation
#print axioms YMGap.Continuum.XiAvoidanceCorrelation.truncated_numerator_le_chain
