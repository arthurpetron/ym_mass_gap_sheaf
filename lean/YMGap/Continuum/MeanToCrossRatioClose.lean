/-
# The constructive FTC / increasing-function skeleton for `MeanToCrossRatio`

`FusionMarginMonotone.MeanToCrossRatio w` is the sole analytic bridge between the
POINTWISE first-moment gap `AsMsFirstMomentGap w'` (holding for every rational
`w' ∈ [0, wH]`) and the TWO-POINT cross-ratio inequality `CrossRatioMonotone w`.
Per mode `s`, writing

    A_s(w) := acN w (s+1) s · acN w (s+1) (s+2)          (`Asf`)
    M_s(w) := acN w (s+1) (s+1) · acN w (s+1) (s+1)      (`Msf`)

the target `CrossRatioMonotone.cross s` is `A_s(w)·M_s(wH) ≤ A_s(wH)·M_s(w)`, i.e.
`R_s := A_s/M_s` nondecreasing on `[0, wH]` in cross-multiplied (division-free)
form.  This IS the constructive increasing-function theorem: `R_s' ≥ 0` pointwise
(the premise) ⟹ `R_s` nondecreasing.

## What this module ADDS (all axiom-clean, GENUINE new content)

The postulate splits the bridge into a FREE algebraic half (telescoping /
chaining) and an IRREDUCIBLE analytic atom (the per-cell derivative-to-difference
estimate).  Here the FREE half is built FOR REAL as reusable, division-free
machinery, and the wall is relocated onto ONE precisely-named Type-level residual:

  * `acN_pos_diag` — the diagonal `0 < acN w (s+1) (s+1)` for EVERY `0 < w`
    (generalising `acN_pos_diag_wH`; the `p=0` term dominates the nonneg tail).
  * `Msf_pos` — hence `0 < M_s(w)` for `0 < w`.
  * `mul_right_comm_eqv` — the `(a·b)·c ≃ (a·c)·b` reassociation primitive.
  * `crossTrans` — **DIVISION-FREE TRANSITIVITY of the cross-ratio order**: from
    `R_0 ≤ R_1` and `R_1 ≤ R_2` (cross form, `M_1 > 0`) conclude `R_0 ≤ R_2`
    (cross form).  This is the constructive statement that the ratio order is a
    preorder WITHOUT forming the quotient `A/M` (the substrate has no `Q'`
    division): three positive multiplications plus one strictly-positive cancel.
  * `crossChain` — the `n`-cell iterate: given a partition `t_0, …, t_n` with all
    `M(t_k) > 0` and per-cell cross-signs `R(t_k) ≤ R(t_{k+1})`, the ENDPOINT
    cross inequality `A(t_0)·M(t_n) ≤ A(t_n)·M(t_0)` follows.  This IS the
    telescoping/FTC skeleton (`ChebOrthoEvenFTC.telescope_sum`'s cross-ratio
    analogue), fully proved.
  * `meanToCrossRatio_of_refinement` — **THE REDUCTION**: a signed-refinement
    certificate inhabits `MeanToCrossRatio w`.  For each mode the certificate
    supplies a positive cross-signed partition of `[w, wH]`; `crossChain` chains
    it to the endpoints `t_0 = w`, `t_n = wH`, i.e. exactly `cross s`.
  * `signedRefinement_of_crossRatio` — the ROUND-TRIP (non-vacuity guard): a
    `CrossRatioMonotone w` witness (with `0 < w`) inhabits the residual via the
    trivial one-cell partition.  So the residual Type is inhabitable EXACTLY when
    the target holds — it is not a provably-empty (vacuous-truth) hole.

## The single named-open residual

  * `RsSignedRefinement w` — for each mode `s`, GIVEN the pointwise first-moment
    gap on all of `[0, wH]`, a positive cross-signed refining partition of
    `[w, wH]`.  This is the honest FTC content: producing the per-cell signs from
    the pointwise derivative sample is the per-`s` derivative-to-difference
    estimate — self-similar, MLR-refuted at every scale (the coefficient/PF₂ route
    is FALSE, `noArrayMLR_A1M1`), hence a genuine analytic atom, NOT the free
    chaining.  NAMED-OPEN (never `sorry`).

## Honest verdict

This is a REDUCTION + reusable machinery, NOT a closure.  The division-free
cross-ratio chaining (`crossTrans`/`crossChain`) — the algebraic half of the
constructive increasing-function theorem — is PROVED and reusable; the analytic
half (signing each cell from the pointwise gap) is relocated onto the single
named residual `RsSignedRefinement`.  The Clay Yang–Mills mass gap remains OPEN.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide`/`omega` only
on closed `Nat`/`Q'` goals.  Axiom-gate at the foot: `[propext]` /
`[propext, Quot.sound]`.
-/

import YMGap.Continuum.FusionMarginMonotone

namespace YMGap.Continuum.MeanToCrossRatioClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FiniteSMarginWorstcase
open YMGap.Continuum.FusionMarginMonotone

/-! ## 1. The per-mode numerator `A_s` and denominator `M_s`. -/

/-- **`Asf w s`** — the off-diagonal antidiagonal product `acN_s·acN_{s+2}` (the
numerator `A_s(w)` of the margin ratio). -/
def Asf (w : Q') (s : Nat) : Q' := acN w (s + 1) s * acN w (s + 1) (s + 2)

/-- **`Msf w s`** — the diagonal square `(acN_{s+1})²` (the denominator `M_s(w)`
of the margin ratio). -/
def Msf (w : Q') (s : Nat) : Q' := acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)

/-! ## 2. Positivity of the diagonal denominator for every `0 < w`. -/

/-- **`acN_pos_diag`** — the diagonal autoconvolution is strictly positive for
EVERY `0 < w`.  `acN w (s+1) (s+1) = Σ_{p<s+1} c_p·c_{(s+1)−p}` with all summands
`≥ 0` and the `p=0` summand `c_0·c_{s+1} > 0` (`coeffW_pos` twice), so the fsum
dominates a strictly positive term.  Generalises `acN_pos_diag_wH` off `w = wH`. -/
theorem acN_pos_diag {w : Q'} (hw : (0 : Q') < w) (s : Nat) :
    (0 : Q') < acN w (s + 1) (s + 1) := by
  have hnn : ∀ t, (0 : Q') ≤ coeffW w t * coeffW w ((s + 1) - t) := fun t =>
    Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hw) t)
      (coeffW_nonneg (Q'.le_of_lt hw) ((s + 1) - t))
  have hterm : (coeffW w 0 * coeffW w ((s + 1) - 0))
      ≤ fsum (fun p => coeffW w p * coeffW w ((s + 1) - p)) (s + 1) :=
    BondMovingMoment.fsum_term_le_of_nonneg hnn 0 (s + 1) (Nat.succ_pos s)
  have h0 : (0 : Q') < coeffW w 0 * coeffW w ((s + 1) - 0) :=
    BakryEmery.mul_pos (coeffW_pos hw 0) (coeffW_pos hw ((s + 1) - 0))
  exact HeatKernelRGStep.lt_of_lt_of_le h0 hterm

/-- **`Msf_pos`** — the denominator `M_s(w)` is strictly positive for `0 < w`. -/
theorem Msf_pos {w : Q'} (hw : (0 : Q') < w) (s : Nat) : (0 : Q') < Msf w s :=
  BakryEmery.mul_pos (acN_pos_diag hw s) (acN_pos_diag hw s)

/-! ## 3. The division-free cross-ratio order machinery. -/

/-- **`mul_right_comm_eqv`** — `(a·b)·c ≃ (a·c)·b`.  A reassociation primitive
used to move the pivot denominator through the cross-ratio products. -/
theorem mul_right_comm_eqv (a b c : Q') : ((a * b) * c).eqv ((a * c) * b) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b c)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a (b * c) (c * b) (Q'.mul_comm_eqv b c))
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c b)))

/-- **`crossTrans` — DIVISION-FREE TRANSITIVITY of the cross-ratio order.**  From
`A_0·M_1 ≤ A_1·M_0` (i.e. `R_0 ≤ R_1`) and `A_1·M_2 ≤ A_2·M_1` (i.e. `R_1 ≤ R_2`),
with `0 ≤ M_0`, `0 < M_1`, `0 ≤ M_2`, conclude `A_0·M_2 ≤ A_2·M_0` (i.e.
`R_0 ≤ R_2`).  No `Q'` division is formed: multiply the first cross-inequality by
`M_2`, the second by `M_0`, chain through `(A_1·M_0)·M_2 ≃ (A_1·M_2)·M_0`, and
cancel the strictly-positive pivot `M_1`. -/
theorem crossTrans {A0 A1 A2 M0 M1 M2 : Q'}
    (h1 : A0 * M1 ≤ A1 * M0) (h2 : A1 * M2 ≤ A2 * M1)
    (hM0 : (0 : Q') ≤ M0) (hM1 : (0 : Q') < M1) (hM2 : (0 : Q') ≤ M2) :
    A0 * M2 ≤ A2 * M0 := by
  -- (A0·M2)·M1 ≃ (A0·M1)·M2 ≤ (A1·M0)·M2 ≃ (A1·M2)·M0 ≤ (A2·M1)·M0 ≃ (A2·M0)·M1
  have s1 : (A0 * M1) * M2 ≤ (A1 * M0) * M2 :=
    Q'.mul_le_mul_of_nonneg_right (A0 * M1) (A1 * M0) M2 h1 hM2
  have s2 : (A1 * M2) * M0 ≤ (A2 * M1) * M0 :=
    Q'.mul_le_mul_of_nonneg_right (A1 * M2) (A2 * M1) M0 h2 hM0
  have e_lhs : ((A0 * M2) * M1).eqv ((A0 * M1) * M2) := mul_right_comm_eqv A0 M2 M1
  have e_mid : ((A1 * M0) * M2).eqv ((A1 * M2) * M0) := mul_right_comm_eqv A1 M0 M2
  have e_rhs : ((A2 * M1) * M0).eqv ((A2 * M0) * M1) := mul_right_comm_eqv A2 M1 M0
  have chain : (A0 * M2) * M1 ≤ (A2 * M0) * M1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv e_lhs)
      (Q'.le_trans' _ _ _ s1
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv e_mid)
          (Q'.le_trans' _ _ _ s2 (Q'.le_of_eqv e_rhs))))
  exact BakryEmery.le_of_mul_le_mul_right_pos hM1 chain

/-- **`crossChain` — the `n`-cell iterate (the cross-ratio FTC skeleton).**  For
sequences `A, M : Nat → Q'`, if every node `M k` (`k ≤ n`) is strictly positive
and every cell is cross-signed `A k·M(k+1) ≤ A(k+1)·M k` (`k < n`), then the
ENDPOINT cross inequality `A 0·M n ≤ A n·M 0` holds.  Proved by induction on `n`,
`crossTrans` fusing the running head-to-`n` inequality with the `n`-th cell.  This
is the division-free analogue of the discrete telescoping identity. -/
theorem crossChain (A M : Nat → Q') :
    ∀ n, (∀ k, k ≤ n → (0 : Q') < M k) →
      (∀ k, k < n → A k * M (k + 1) ≤ A (k + 1) * M k) →
      A 0 * M n ≤ A n * M 0
  | 0, _, _ => Q'.le_refl' (A 0 * M 0)
  | n + 1, hpos, hcell => by
    have IH : A 0 * M n ≤ A n * M 0 :=
      crossChain A M n
        (fun k hk => hpos k (Nat.le_trans hk (Nat.le_succ n)))
        (fun k hk => hcell k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    have hcelln : A n * M (n + 1) ≤ A (n + 1) * M n := hcell n (Nat.lt_succ_self n)
    exact crossTrans IH hcelln
      (Q'.le_of_lt (hpos 0 (Nat.zero_le _)))
      (hpos n (Nat.le_succ n))
      (Q'.le_of_lt (hpos (n + 1) (Nat.le_refl _)))

/-! ## 4. The single named-open residual: a signed refining partition. -/

/-- **`RsSignedRefinement w`** — the NAMED-OPEN analytic atom.  For each mode `s`,
GIVEN the pointwise first-moment gap on all of `[0, wH]`, a natural `n`, a
partition `t_0, …, t_n` of `[w, wH]` (`t 0 = w`, `t n = wH`) with every denominator
`M_s(t_k) > 0` and every cell cross-signed `A_s(t_k)·M_s(t_{k+1}) ≤
A_s(t_{k+1})·M_s(t_k)`.

Producing these per-cell signs from the pointwise derivative sample is exactly the
per-`s` derivative-to-difference estimate — self-similar and MLR-refuted at every
scale (the per-coefficient PF₂/MLR route is FALSE, `noArrayMLR_A1M1`), so it is a
genuine analytic atom, NOT the free chaining discharged by `crossChain`.
NAMED-OPEN (never `sorry`; Type-level data, AGENTS.md Rule 8). -/
structure RsSignedRefinement (w : Q') : Type where
  refine :
    (∀ w', (0 : Q') ≤ w' → w' ≤ wH → AsMsFirstMomentGap w') → ∀ s,
      Σ' (n : Nat), Σ' (t : Nat → Q'),
        (t 0 = w) ×' (t n = wH) ×'
          (∀ k, k ≤ n → (0 : Q') < Msf (t k) s) ×'
          (∀ k, k < n → Asf (t k) s * Msf (t (k + 1)) s
            ≤ Asf (t (k + 1)) s * Msf (t k) s)

/-! ## 5. THE REDUCTION: `RsSignedRefinement w ⟹ MeanToCrossRatio w`. -/

/-- **`meanToCrossRatio_of_refinement` — THE REDUCTION.**  A signed-refinement
certificate inhabits `MeanToCrossRatio w`.  For each mode `s`, `crossChain` fuses
the certificate's per-cell cross-signs along its positive partition to the
endpoint cross inequality; rewriting `t 0 = w` and `t n = wH` yields exactly the
`CrossRatioMonotone.cross s` statement.  The premise `∀ w' ∈ [0, wH],
AsMsFirstMomentGap w'` is threaded to the certificate (it is genuinely required —
the two-point sign is NOT termwise-definite). -/
def meanToCrossRatio_of_refinement {w : Q'} (H : RsSignedRefinement w) :
    MeanToCrossRatio w where
  integrate := fun premise =>
    { cross := fun s => by
        obtain ⟨n, t, h0, hn, hpos, hcell⟩ := H.refine premise s
        have hchain : Asf (t 0) s * Msf (t n) s ≤ Asf (t n) s * Msf (t 0) s :=
          crossChain (fun k => Asf (t k) s) (fun k => Msf (t k) s) n hpos hcell
        rw [h0, hn] at hchain
        exact hchain }

/-! ## 6. ROUND-TRIP (non-vacuity guard): `CrossRatioMonotone w ⟹
`RsSignedRefinement w` for `0 < w`, via the trivial one-cell partition. -/

/-- **`signedRefinement_of_crossRatio` — the ROUND-TRIP.**  A `CrossRatioMonotone
w` witness (with `0 < w`) inhabits `RsSignedRefinement w`: take the trivial
one-cell partition `t 0 = w`, `t 1 = wH`; positivity is `Msf_pos` at `w` and `wH`,
and the sole cell is exactly `star.cross s`.  This certifies the residual Type is
inhabitable EXACTLY when the target holds — it is not a provably-empty
(vacuous-truth) hole. -/
def signedRefinement_of_crossRatio {w : Q'} (hw : (0 : Q') < w)
    (star : CrossRatioMonotone w) : RsSignedRefinement w where
  refine := fun _premise s =>
    ⟨1, (fun k => if k = 0 then w else wH),
      rfl, rfl,
      (by
        intro k hk
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl
        · show (0 : Q') < Msf w s
          exact Msf_pos hw s
        · show (0 : Q') < Msf wH s
          exact Msf_pos (by decide) s),
      (by
        intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        show Asf w s * Msf wH s ≤ Asf wH s * Msf w s
        exact star.cross s)⟩

end YMGap.Continuum.MeanToCrossRatioClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MeanToCrossRatioClose.acN_pos_diag
#print axioms YMGap.Continuum.MeanToCrossRatioClose.Msf_pos
#print axioms YMGap.Continuum.MeanToCrossRatioClose.mul_right_comm_eqv
#print axioms YMGap.Continuum.MeanToCrossRatioClose.crossTrans
#print axioms YMGap.Continuum.MeanToCrossRatioClose.crossChain
#print axioms YMGap.Continuum.MeanToCrossRatioClose.meanToCrossRatio_of_refinement
#print axioms YMGap.Continuum.MeanToCrossRatioClose.signedRefinement_of_crossRatio
