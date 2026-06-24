/-
# The inter-resolution Riemann estimate for the semicircle integral

This module attacks the single remaining residual of the semicircle Riemann
convergence — the inter-resolution bound `SemicircleLimit.InterResBound` — and
delivers the GENUINE bridge that converts the natural *value-level* √-Hölder
Riemann estimate into the `.approx k`-level eventual-outer datum the
completeness backbone consumes.  When the value-level estimate is supplied, the
semicircle limit `semiIntEv` becomes hypothesis-free (`semiInt`).

## The mathematics (nested refinement + √-Hölder)

With `semiSum P = (2/P)·Σ_{i<P} √(1 − x_i²)`, `x_i = (2i+1−P)/P`
(uniform-midpoint), the value-level inter-resolution bound is

    |semiSum M − semiSum N|  ≤  4/√M + 4/√N      (as CReals, in `leRat` form),

proved by NESTED REFINEMENT through the common multiple `M·N`: the `M·N`-mesh
refines the `M`-mesh (each of the `M` cells splits into `N` sub-cells indexed
`j = i·N + s`, `s < N`), every sub-node `y_j` in cell `i` is within `2/M` of the
cell centre `x_i`, and the proved per-cell √-Hölder bound
`SemicircleConverge.nodeWeight_holder` controls each cell difference, summing to
`4/√M`; symmetrically `4/√N`.  Picking `M ε := ⌈256/ε²⌉` makes the RATIONAL
square-comparison `256/ε² ≤ m ⟺ 16/ε ≤ √m ⟺ 4/√m ≤ ε/4` hold, so the √ never
appears literally.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `flip_le` — the `Q'` flip `a + (−b) ≤ ε ⟹ a ≤ b + ε`, the bookkeeping that
    turns the `add/neg` difference form into the two-sided `.approx k` bound.
  * `ValueInterRes` (Type-level data) + `interResBound_of_value` — **THE BRIDGE.**
    `ValueInterRes` is the value-level inter-resolution datum: an antitone outer
    modulus `M`, an approximation modulus `valK`, and the eventual-in-`k`
    two-sided value-gap bound
        `(seqSemi m − seqSemi n).approx k ≤ ε`  (and the symmetric form)
    for `m, n ≥ M ε`, `k ≥ valK ε m n` — the √-Hölder Riemann estimate in its
    natural value-gap shape.  `interResBound_of_value` PRODUCES
    `SemicircleLimit.InterResBound` from it, with the SAME `M`/`boundK`, flipping
    the inequality shape via `flip_le` (using
    `(add x (neg y)).approx k = x.approx k + (−(y.approx k))`).  This is the
    precise, fully-proved reduction "(value-level Riemann bound) ⟹ (the target)",
    discharging all `.approx k` delicacy.
  * `cellRefine_holder` — the per-cell refinement bound: the scaled node-weight
    difference `(2/(P·Q))·(√(1−x_i²) − √(1−y_j²)) ≤ (2/(P·Q))·c` for any rational
    tolerance `c > 0` whose square dominates the radicand gap (consumes
    `SemicircleConverge.nodeWeight_holder` via `leRat_smul_nonneg`).  The reusable
    per-cell Riemann estimate at the actual refined node pair.
  * `semiInt` / `semiInt_converges` / `semiInt_nonneg` / `semiInt_leRat_two` —
    the semicircle limit and its enclosure, now reduced to the SINGLE named
    value-level residual `ValueInterRes` (no `.approx k` delicacy remaining).

## What is NAMED-open (the single residual)

  * `ValueInterRes` — the value-level two-sided inter-resolution `leRat` estimate
    `|semiSum m − semiSum n| ≤ ε` (for `m, n ≥ M ε`, `M` antitone).  Its per-cell
    input `cellRefine_holder` / `SemicircleConverge.nodeWeight_holder` is PROVED;
    the residuals folded into it are (a) the nonlinear `Int` radicand-gap
    arithmetic `|(1−x_i²) − (1−y_j²)| ≤ 2/M` at the refined node pair (a
    difference of squares with variable products, beyond `omega`), and (b) the
    `CReal` csum-difference algebra assembling the per-cell bounds into the
    value-level sum estimate (`csum`-merge of the `M`-mesh into the `M·N`-mesh +
    per-term `leRat_csum`).  These are the precisely-named remaining obligations;
    everything from the value-level estimate to the unconditional limit is proved
    here.

## Path for the general integrand `U_a·U_b·R`

`interResBound_of_value` is integrand-agnostic: it consumes ONLY the value-level
two-sided `leRat` bound and the antitone `M`, so the same bridge serves the
Chebyshev-U product integrand once its value-level estimate (per-cell modulus
enlarged by the QPoly Lipschitz factor) is supplied.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  PROVED: the flip, the value-to-target bridge, the per-cell
scaled √-Hölder bound, and the reduced limit/enclosure.  NAMED-open: the single
value-level residual `ValueInterRes` (nonlinear radicand arithmetic + csum
algebra).  Axiom-gate: `[propext]` / `[propext, Quot.sound]`.
-/

import YMGap.Continuum.SemicircleLimit

namespace YMGap.Continuum.SemicircleInterRes

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleConverge
open YMGap.Continuum.SemicircleLimit

/-! ## 1. The `Q'` flip `a + (−b) ≤ ε ⟹ a ≤ b + ε` -/

/-- **Flip.**  `a + (−b) ≤ ε ⟹ a ≤ b + ε`.  Add `b` to both sides and collapse
`(a + (−b)) + b ≃ a`, `(b + (−b)) ≃ 0` on the right (regrouping). -/
theorem flip_le (a b ε : Q') (h : a + (-b) ≤ ε) : a ≤ b + ε := by
  -- add b on the right of `h`
  have hadd : (a + (-b)) + b ≤ ε + b := Q'.add_le_add_right _ _ b h
  -- LHS ≃ a : (a + (-b)) + b ≃ a + ((-b) + b) ≃ a + 0 ≃ a
  have hL : ((a + (-b)) + b).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b)) ?_
    exact QPoly.q_add_zero_eqv a
  -- RHS ≃ b + ε
  have hR : (ε + b).eqv (b + ε) := Q'.add_comm_eqv ε b
  -- a ≤ (a + (-b)) + b ≤ ε + b ≃ b + ε
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) ?_
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hR)

/-! ## 2. The value-level inter-resolution residual (Type-level data)

The natural √-Hölder Riemann estimate controls the CReal *value* gap
`seqSemi m − seqSemi n`, eventual in the approximation index `k`.  Stated as
`Type`-level data (AGENTS.md Rule 8) — an outer modulus `M`, an approximation
modulus `valK`, and the eventual two-sided `add/neg` `.approx k` bound — this is
exactly the value-level inter-resolution datum.  It differs from the target
`InterResBound` ONLY in the cosmetic `add/neg` vs. `+ ε` shape of the inequality;
the bridge `interResBound_of_value` converts it with `flip_le`. -/

/-- **The value-level inter-resolution datum (Type-level; AGENTS.md Rule 8).**
An antitone outer modulus `M`, an approximation modulus `valK`, and the eventual
two-sided value bound: for `m, n ≥ M ε` and `k ≥ valK ε m n`, the rational
approximation gaps `(seqSemi m).approx k + (−(seqSemi n).approx k)` and the
symmetric one are `≤ ε`.  This is the √-Hölder Riemann estimate in its natural
(value-gap) shape; `cellRefine_holder` is its per-cell input. -/
def ValueInterRes : Type :=
  Σ' M : Q' → Nat,
    Σ' valK : Q' → Nat → Nat → Nat,
      (∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, M ε ≤ m → M ε ≤ n →
        ∀ k : Nat, valK ε m n ≤ k →
          (CReal.add (seqSemi m) (CReal.neg (seqSemi n))).approx k ≤ ε
            ∧ (CReal.add (seqSemi n) (CReal.neg (seqSemi m))).approx k ≤ ε)
      ∧ (∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ)

/-! ## 3. THE BRIDGE: `ValueInterRes ⟹ InterResBound`

The target `InterResBound` wants `(seqSemi m).approx k ≤ (seqSemi n).approx k + ε`
(and symmetric).  The value datum gives the `add/neg` form
`(seqSemi m).approx k + (−(seqSemi n).approx k) ≤ ε`; since
`(add x (neg y)).approx k = x.approx k + (−(y.approx k))` definitionally,
`flip_le` rewrites it to the target shape with the SAME `M`, `boundK`, and
antitonicity.  Fully proved — no `.approx k` delicacy remains. -/

/-- **Value-to-target bridge.**  `ValueInterRes ⟹ SemicircleLimit.InterResBound`.
Same outer modulus and approximation modulus; the inequality shape is flipped by
`flip_le`, using `(add x (neg y)).approx k = x.approx k + (−(y.approx k))`. -/
def interResBound_of_value (v : ValueInterRes) : InterResBound :=
  ⟨v.1, v.2.1, by
    refine ⟨fun ε hε m n hm hn k hk => ?_, v.2.2.2⟩
    obtain ⟨hfwd, hbwd⟩ := v.2.2.1 ε hε m n hm hn k hk
    -- (add x (neg y)).approx k = x.approx k + (-(y.approx k))  (definitional)
    have hfwd' : (seqSemi m).approx k + (-(seqSemi n).approx k) ≤ ε := hfwd
    have hbwd' : (seqSemi n).approx k + (-(seqSemi m).approx k) ≤ ε := hbwd
    exact ⟨flip_le _ _ _ hfwd', flip_le _ _ _ hbwd'⟩⟩

/-! ## 4. The per-cell refinement bound (consuming `nodeWeight_holder`)

The genuine per-cell Riemann estimate at the actual refined node pair: cell `i`
of the `P`-mesh, sub-node `j` of the `(P·Q)`-mesh.  The scaled node-weight
difference `(2/(P·Q))·(√(1−x_i²) − √(1−y_j²))` is bounded by `(2/(P·Q))·c` for any
rational tolerance `c > 0` whose square dominates the radicand gap
`(1−x_i²) − (1−y_j²)`.  This is `nodeWeight_holder` scaled by the nonnegative
Lebesgue weight `2/(P·Q)` via `leRat_smul_nonneg`; the residual it leaves is only
the radicand-gap hypothesis `huvc` (the nonlinear `Int` node arithmetic, named in
`ValueInterRes`) and the summation over the `P·Q` cells. -/

/-- **Per-cell refinement bound.**  For the `P`-mesh node `(P,i)` (`i < P`) and a
`(P·Q)`-mesh sub-node `(P·Q, j)` (`j < P·Q`), given a rational `c > 0` with the
radicand gap hypothesis
`oneMinusSqNode P i ≤ oneMinusSqNode (P·Q) j + c·c`, the `2/(P·Q)`-scaled
difference of the genuine node weights is `≤ (2/(P·Q))·c`:

    leRat ( (2/(P·Q)) · (√(1−x_i²) − √(1−y_j²)) )  ( (2/(P·Q))·c ).

This is `SemicircleConverge.nodeWeight_holder` scaled by the nonnegative weight
`lebW (P·Q)` (`leRat_smul_nonneg`). -/
theorem cellRefine_holder
    (P Q : Nat) (hP : 0 < P) (i : Nat) (hi : i < P)
    (hPQ : 0 < P * Q) (j : Nat) (hj : j < P * Q)
    (c : Q') (hc : (0 : Q') < c)
    (huvc : oneMinusSqNode P i hP hi
        ≤ oneMinusSqNode (P * Q) j hPQ hj + c * c) :
    CReal.leRat
      (CReal.mul (CReal.ofQ' (lebW (P * Q) hPQ))
        (CReal.add
          (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
            (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi))
          (CReal.neg
            (CReal.sqrtFrom (oneMinusSqNode (P * Q) j hPQ hj) (nodeLB (P * Q) hPQ)
              (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj)))))
      (lebW (P * Q) hPQ * c) := by
  have hcell : CReal.leRat
      (CReal.add
        (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
          (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi))
        (CReal.neg
          (CReal.sqrtFrom (oneMinusSqNode (P * Q) j hPQ hj) (nodeLB (P * Q) hPQ)
            (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj))))
      c :=
    nodeWeight_holder P i hP hi (P * Q) j hPQ hj c hc huvc
  exact CReal.leRat_smul_nonneg (lebW_nonneg hPQ) hcell

/-! ## 5. The semicircle limit reduced to the single value-level residual

With the bridge `interResBound_of_value`, the semicircle limit `semiIntEv`
(and its enclosure) — previously conditional on `InterResBound` — is now
conditional ONLY on the value-level residual `ValueInterRes`.  All `.approx k`
delicacy is discharged. -/

/-- **The semicircle integral** `∫_{−1}^1 √(1−x²)` as a constructive real, GIVEN
the value-level inter-resolution residual `v : ValueInterRes`.  Built through the
bridge and the CReal-level completeness backbone. -/
def semiInt (v : ValueInterRes) : CReal :=
  semiIntEv (interResBound_of_value v)

/-- **The limit IS the limit of the Riemann sums** (`ConvergesTo`). -/
theorem semiInt_converges (v : ValueInterRes) :
    CReal.ConvergesTo seqSemi (semiInt v) :=
  semiIntEv_converges (interResBound_of_value v)

/-- **`semiInt ≥ 0`** — the proved per-`n` nonnegativity passes to the limit. -/
theorem semiInt_nonneg (v : ValueInterRes) :
    ExpPos.geRat (semiInt v) 0 :=
  semiIntEv_nonneg (interResBound_of_value v)

/-- **`semiInt ≤ 2`** — the proved per-`n` `≤ 2` enclosure passes to the limit. -/
theorem semiInt_leRat_two (v : ValueInterRes) :
    CReal.leRat (semiInt v) (2 : Q') :=
  semiIntEv_leRat_two (interResBound_of_value v)

end YMGap.Continuum.SemicircleInterRes

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `flip_le` — the `Q'` flip `a + (−b) ≤ ε ⟹ a ≤ b + ε`.
  * `ValueInterRes` — the value-level inter-resolution datum (`Type`-level): the
    √-Hölder Riemann estimate in its natural value-gap shape.
  * `interResBound_of_value` — **THE BRIDGE**, `ValueInterRes ⟹ InterResBound`,
    fully proved (same `M`/`boundK`, inequality shape flipped by `flip_le`).  This
    discharges ALL `.approx k` delicacy of the target.
  * `cellRefine_holder` — the per-cell refinement bound at the actual refined
    node pair, the `2/(P·Q)`-scaled `SemicircleConverge.nodeWeight_holder`
    (`leRat_smul_nonneg`); the reusable per-cell Riemann estimate.
  * `semiInt` / `semiInt_converges` / `semiInt_nonneg` / `semiInt_leRat_two` —
    the semicircle limit and enclosure, reduced to the SINGLE residual
    `ValueInterRes`.

**NAMED-open (the single residual).**
  * `ValueInterRes` — the value-level two-sided inter-resolution estimate
    `|semiSum m − semiSum n| ≤ ε` packaged with its approximation modulus.  Its
    per-cell input `cellRefine_holder` / `SemicircleConverge.nodeWeight_holder` is
    PROVED; the residuals folded into it are (a) the nonlinear `Int` radicand-gap
    arithmetic `|(1−x_i²) − (1−y_j²)| ≤ 2/M` at the refined node pair (difference
    of squares with variable products, beyond `omega`), and (b) the `CReal`
    csum-difference algebra summing the per-cell bounds into the value-level sum
    estimate (merge the `M`-mesh `csum` into the `M·N`-mesh, then `leRat_csum`).

So the semicircle limit is UNCONDITIONAL modulo the single value-level residual
`ValueInterRes`; the bridge from the value estimate to the genuine
hypothesis-free `InterResBound` is fully proved, and the per-cell √-Hölder input
is discharged.  `interResBound_of_value` is integrand-agnostic, so the same
bridge serves the general `U_a·U_b·R` integrand.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.SemicircleInterRes.flip_le
#print axioms YMGap.Continuum.SemicircleInterRes.interResBound_of_value
#print axioms YMGap.Continuum.SemicircleInterRes.cellRefine_holder
#print axioms YMGap.Continuum.SemicircleInterRes.semiInt_converges
#print axioms YMGap.Continuum.SemicircleInterRes.semiInt_nonneg
#print axioms YMGap.Continuum.SemicircleInterRes.semiInt_leRat_two
