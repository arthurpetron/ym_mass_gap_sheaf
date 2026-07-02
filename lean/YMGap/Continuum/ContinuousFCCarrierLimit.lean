/-
The CARRIER-side limit of the continuous functional calculus — the object
`f(T)x := lim_n pₙ(T)x` on the completed GNS Hilbert space, together with the
polynomial-LINEARITY of the formed operator `polyApply` that the limit rests on.

# What this module adds (all axiom-clean)

`Continuum/ContinuousFunctionalCalculusForm.lean` FORMED the transfer polynomial
operator `polyApply p x = p(T)x = Σ_k cₖ·Tᵏx` as a genuine
`GNSCompletionSpace → GNSCompletionSpace` map and proved it self-adjoint.
`Continuum/ContinuousTransferCalculus.lean` proved the diagonal norm bound
`polyNormBound` and the pointwise operator limit `symbolLimit`.  The residual for
a CONTINUOUS `f` was: take the CARRIER limit of `polyApply pₙ x` for a
uniformly-Cauchy polynomial sequence `pₙ`.  This module delivers the two genuine
mechanisms for that limit and isolates — sharply and honestly — the exact
remaining analytic inputs.

  * **PART 1 — the completion additive algebra** (`cAdd_embedZero_left` /
    `cAdd_embedZero_right` / `cAdd_add_add_comm`).  The embedded zero is a two-sided
    unit for the completion addition, and `cAdd` satisfies the middle-four
    interchange.  Descended from the carrier laws `zero_add` / `add_zero` /
    `add_add_add_comm` through `rad_of_veq` and `Quotient.sound`.

  * **PART 2 — scalar additivity of `cSmul`** (`LinearSmulGNSData`,
    `cSmul_add_scalar`).  Forming `p(T)` linearly in `p` needs
    `(s+t)·x = s·x + t·x` on the completion.  This is a genuine module law NOT
    implied by `SmulGNSData`'s `smul_sub`; we add it as the wrapper
    `LinearSmulGNSData` (inhabited by the `Q'`-weighted module `qLinearSmulGNS`,
    where it is `Q'` right-distributivity) and descend it to the completion scalar
    action.

  * **PART 3 — polynomial linearity of the formed operator** (`polyApply_padd`).
    `polyApply (p + q) x = polyApply p x + polyApply q x` — the formed operator is
    ADDITIVE in the polynomial.  Induction along `padd`, using the operator
    additivity `T_add`, the scalar additivity `cSmul_add_scalar`, and the
    completion interchange `cAdd_add_add_comm`.  This is the polynomial-side
    linearity the Bernstein limit runs through.

  * **PART 4 — the carrier limit** (`carrierLimit`, `carrierLimit_converges`,
    `PolyImageCauchy`, `fcApply`).  Given a Cauchy sequence of carrier points
    presented `Type`-level by representatives with a modulus (a
    `GeneralCompletionCauchy`, the honest choice-free reading — extracting a
    representative from an arbitrary quotient point is `Quotient.out`, i.e.
    choice), the metric completeness already proved (`GeneralCompletionCauchy.lim`
    / `.converges`) yields the limit point `carrierLimit` with genuine
    convergence.  `PolyImageCauchy` records that the represented points ARE the
    polynomial images `polyApply pₙ x`, so `fcApply := carrierLimit` is genuinely
    `lim_n pₙ(T)x`.

# Honest scope — the sharply-named remaining inputs

`fcApply` is the genuine limit ONCE the sequence `n ↦ polyApply pₙ x` is presented
as a `PolyImageCauchy` (represented + distance-Cauchy).  Producing that datum, and
the self-adjointness / norm bound of the limit, need exactly three inputs, none of
which the current interfaces expose — named here, not faked:

  1. **A representative-level transfer lift.**  `AdditiveTransferOperator` exposes
     `T` only as a map on the quotient `GNSCompletionSpace`.  `cAdd` / `cSmul` have
     representative-level lifts (`cAddCauchy` / `cSmulCauchy`), but `T` does not, so
     `polyApply pₙ x` cannot be presented via representatives (as
     `GeneralCompletionCauchy` requires) without one.

  2. **Transfer scalar-homogeneity `T (c·x) = c·(T x)`.**  Needed to identify the
     operator DIFFERENCE `polyApply pₙ x ⊖ polyApply pₘ x` with `polyApply (pₙ⊖pₘ) x`
     (only `T_add` — additivity — is available), hence to run the distance-Cauchy
     estimate off `polyNormBound`.

  3. **`RC` Cauchy–Schwarz** (`|⟨u,z⟩| ≤ ‖u‖·‖z‖`).  Needed to pass
     self-adjointness and the norm bound of each `polyApply pₙ` to the limit
     (inner-product continuity).  The `RC` product is deliberately undeveloped in
     this branch (see `Continuum/BoundedTransferCalculus.lean`).

The single remaining Bernstein input (the general-`n` variance identity) supplies
the uniformly-Cauchy polynomial sequence; it is orthogonal to (1)–(3).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.ContinuousFunctionalCalculusForm

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.ContinuousFunctionalCalculusForm

/-! ## Part 1 — the completion additive algebra -/

namespace YMGap.Continuum.GNSQuotient.GNSData

variable (D : GNSData)

/-- **The embedded zero is a left unit for `cAdd`.**  `0 + u = u`, descended from
the carrier law `zero_add` through `rad_of_veq`. -/
theorem cAdd_embedZero_left (u : GNSCompletionSpace D) :
    D.cAdd (embedV D D.zero) u = u := by
  refine Quotient.inductionOn u ?_
  intro a
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : D.veq (D.add D.zero (a.seq n)) (a.seq n) := D.zero_add (a.seq n)
  exact le_of_eqv_le (rad_of_veq D hva) (Q'.le_of_lt hε)

/-- **The embedded zero is a right unit for `cAdd`.**  `u + 0 = u`, via `add_zero`. -/
theorem cAdd_embedZero_right (u : GNSCompletionSpace D) :
    D.cAdd u (embedV D D.zero) = u := by
  refine Quotient.inductionOn u ?_
  intro a
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : D.veq (D.add (a.seq n) D.zero) (a.seq n) := D.add_zero (a.seq n)
  exact le_of_eqv_le (rad_of_veq D hva) (Q'.le_of_lt hε)

/-- **Middle-four interchange for `cAdd`.**  `(a+b)+(c+d) = (a+c)+(b+d)`, descended
from the carrier interchange `add_add_add_comm`. -/
theorem cAdd_add_add_comm (a b c d : GNSCompletionSpace D) :
    D.cAdd (D.cAdd a b) (D.cAdd c d) = D.cAdd (D.cAdd a c) (D.cAdd b d) := by
  refine Quotient.inductionOn a (fun A => Quotient.inductionOn b (fun B =>
    Quotient.inductionOn c (fun C => Quotient.inductionOn d (fun Dd => ?_))))
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : D.veq
      (D.add (D.add (A.seq n) (B.seq n)) (D.add (C.seq n) (Dd.seq n)))
      (D.add (D.add (A.seq n) (C.seq n)) (D.add (B.seq n) (Dd.seq n))) :=
    D.add_add_add_comm (A.seq n) (B.seq n) (C.seq n) (Dd.seq n)
  exact le_of_eqv_le (rad_of_veq D hva) (Q'.le_of_lt hε)

end YMGap.Continuum.GNSQuotient.GNSData

/-! ## Part 2 — scalar additivity of the completion scalar action -/

namespace YMGap.Continuum.HamiltonianScalar

/-- **A `SmulGNSData` whose scalar action is additive in the scalar.**  The one
module law `(s+t)·a ≈ s·a + t·a` NOT implied by `smul_sub`, added as a wrapper so
no existing inhabitant has to re-discharge it.  Needed for the polynomial-linearity
of the formed transfer operator. -/
structure LinearSmulGNSData extends SmulGNSData where
  /-- **Scalar additivity** `(s+t)·a ≈ s·a + t·a`. -/
  smul_add_scalar : ∀ (s t : Q') (a : toGNSData.V),
    toGNSData.veq (toGNSData.smul (s + t) a)
      (toGNSData.add (toGNSData.smul s a) (toGNSData.smul t a))

namespace LinearSmulGNSData

variable (SL : LinearSmulGNSData)

/-- **Scalar additivity of the completion scalar action.**
`(s+t)·x = s·x + t·x` on `GNSCompletionSpace`, descended from `smul_add_scalar`
through `rad_of_veq`. -/
theorem cSmul_add_scalar (s t : Q') (x : GNSCompletionSpace SL.toGNSData) :
    SL.toSmulGNSData.cSmul (s + t) x
      = SL.toGNSData.cAdd (SL.toSmulGNSData.cSmul s x) (SL.toSmulGNSData.cSmul t x) := by
  refine Quotient.inductionOn x ?_
  intro a
  apply Quotient.sound
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hva : SL.toGNSData.veq
      (SL.toGNSData.smul (s + t) (a.seq n))
      (SL.toGNSData.add (SL.toGNSData.smul s (a.seq n)) (SL.toGNSData.smul t (a.seq n))) :=
    SL.smul_add_scalar s t (a.seq n)
  exact le_of_eqv_le (rad_of_veq SL.toGNSData hva) (Q'.le_of_lt hε)

end LinearSmulGNSData

/-- **Non-vacuity: the `Q'`-weighted module is a `LinearSmulGNSData`.**  Its scalar
action is `Q'` multiplication, so scalar additivity is `Q'` right-distributivity. -/
def qLinearSmulGNS (w : Q') (hw : (0 : Q') ≤ w) : LinearSmulGNSData where
  toSmulGNSData := qSmulGNS w hw
  smul_add_scalar := fun (s t : Q') (a : Q') => by
    show Q'.eqv ((s + t) * a) ((s * a) + (t * a))
    exact QPoly.q_add_mul s t a

end YMGap.Continuum.HamiltonianScalar

/-! ## Part 3 — polynomial linearity of the formed operator `polyApply` -/

namespace YMGap.Continuum.ContinuousFCCarrierLimit

open YMGap.Continuum.GNSQuotient.GNSData
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.HamiltonianScalar.LinearSmulGNSData

variable (SL : LinearSmulGNSData) (L : AdditiveTransferOperator SL.toGNSData)

/-- **The formed operator is additive in the polynomial.**
`polyApply (p + q) x = polyApply p x + polyApply q x`.  Induction along `padd`:
the base cases use the embedded-zero unit laws, and the step uses the operator
additivity `T_add`, the scalar additivity `cSmul_add_scalar`, and the completion
interchange `cAdd_add_add_comm`.  (`polyApply` needs `SL.toSmulGNSData`.) -/
theorem polyApply_padd (x : GNSCompletionSpace SL.toGNSData) :
    ∀ p q : QPoly.Poly,
      polyApply SL.toSmulGNSData L (QPoly.padd p q) x
        = SL.toGNSData.cAdd (polyApply SL.toSmulGNSData L p x)
            (polyApply SL.toSmulGNSData L q x) := by
  intro p
  induction p with
  | nil =>
      intro q
      show polyApply SL.toSmulGNSData L q x
        = SL.toGNSData.cAdd (embedV SL.toGNSData SL.toGNSData.zero)
            (polyApply SL.toSmulGNSData L q x)
      exact (SL.toGNSData.cAdd_embedZero_left _).symm
  | cons a p ih =>
      intro q
      cases q with
      | nil =>
          show polyApply SL.toSmulGNSData L (a :: p) x
            = SL.toGNSData.cAdd (polyApply SL.toSmulGNSData L (a :: p) x)
                (embedV SL.toGNSData SL.toGNSData.zero)
          exact (SL.toGNSData.cAdd_embedZero_right _).symm
      | cons b q =>
          show SL.toGNSData.cAdd (SL.toSmulGNSData.cSmul (a + b) x)
                 (L.T (polyApply SL.toSmulGNSData L (QPoly.padd p q) x))
            = SL.toGNSData.cAdd
                (SL.toGNSData.cAdd (SL.toSmulGNSData.cSmul a x)
                  (L.T (polyApply SL.toSmulGNSData L p x)))
                (SL.toGNSData.cAdd (SL.toSmulGNSData.cSmul b x)
                  (L.T (polyApply SL.toSmulGNSData L q x)))
          rw [ih q, L.T_add, SL.cSmul_add_scalar a b x,
              SL.toGNSData.cAdd_add_add_comm]

/-- **The formed operator is additive in the polynomial — the paired difference
form.**  A convenience restatement: for the sum polynomial the operator splits. -/
theorem polyApply_padd_apply (x : GNSCompletionSpace SL.toGNSData) (p q : QPoly.Poly) :
    polyApply SL.toSmulGNSData L (QPoly.padd p q) x
      = SL.toGNSData.cAdd (polyApply SL.toSmulGNSData L p x)
          (polyApply SL.toSmulGNSData L q x) :=
  polyApply_padd SL L x p q

/-! ## Part 4 — the carrier limit `f(T)x = lim_n pₙ(T)x` -/

variable {D : GNSData}

/-- **The carrier limit of a represented Cauchy sequence of completion points.**
Given a `Type`-level Cauchy sequence of carrier points (representatives + modulus),
its limit point in the completion — the genuine metric-completeness diagonal
`GeneralCompletionCauchy.lim`. -/
def carrierLimit (X : GeneralCompletionCauchy D) : GNSCompletionSpace D :=
  Quotient.mk (cauchySetoid D) X.lim

/-- **The represented sequence converges to `carrierLimit`.**  For every tolerance
`ε > 0`, eventually (in the sequence index `p`, then in the representative index
`n`) the representative squared distance to the limit representative is `≤ ε`.
This is exactly `GeneralCompletionCauchy.converges`. -/
theorem carrierLimit_converges (X : GeneralCompletionCauchy D) :
    ∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        D.distSqQ ((X.pt p).seq n) (X.lim.seq n) ≤ ε :=
  X.converges

/-- **A represented Cauchy sequence whose points ARE the polynomial images.**
`pt n` (via the underlying `GeneralCompletionCauchy`) represents `pₙ(T)x`:
`⟦pt n⟧ = polyApply pₙ x`.  This is the honest `Type`-level supplier for the
continuous functional calculus — its existence is exactly the residual named in
the module header (representative-level transfer lift + distance-Cauchy control). -/
structure PolyImageCauchy (SL : LinearSmulGNSData)
    (L : AdditiveTransferOperator SL.toGNSData) (pseq : Nat → QPoly.Poly)
    (x : GNSCompletionSpace SL.toGNSData) extends GeneralCompletionCauchy SL.toGNSData where
  /-- The `n`-th represented point IS `pₙ(T)x`. -/
  represents : ∀ n : Nat,
    Quotient.mk (cauchySetoid SL.toGNSData) (toGeneralCompletionCauchy.pt n)
      = polyApply SL.toSmulGNSData L (pseq n) x

/-- **`f(T)x := lim_n pₙ(T)x`.**  The carrier limit of the polynomial images —
a genuine `GNSCompletionSpace` point, constructed (no choice) from the represented
Cauchy sequence. -/
def fcApply {SL : LinearSmulGNSData} {L : AdditiveTransferOperator SL.toGNSData}
    {pseq : Nat → QPoly.Poly} {x : GNSCompletionSpace SL.toGNSData}
    (X : PolyImageCauchy SL L pseq x) : GNSCompletionSpace SL.toGNSData :=
  carrierLimit X.toGeneralCompletionCauchy

/-- **`fcApply` is the limit of the polynomial images.**  The represented points
— which ARE `pₙ(T)x` by `represents` — converge (in the representative squared
distance) to the limit representative of `fcApply`.  Hence `fcApply` genuinely
realizes `lim_n pₙ(T)x` on the carrier. -/
theorem fcApply_converges {SL : LinearSmulGNSData}
    {L : AdditiveTransferOperator SL.toGNSData} {pseq : Nat → QPoly.Poly}
    {x : GNSCompletionSpace SL.toGNSData} (X : PolyImageCauchy SL L pseq x) :
    (∀ ε : Q', (0 : Q') < ε → ∃ P : Nat, ∀ p : Nat, P ≤ p →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        SL.toGNSData.distSqQ ((X.toGeneralCompletionCauchy.pt p).seq n)
          (X.toGeneralCompletionCauchy.lim.seq n) ≤ ε)
    ∧ (∀ n : Nat, Quotient.mk (cauchySetoid SL.toGNSData)
        (X.toGeneralCompletionCauchy.pt n) = polyApply SL.toSmulGNSData L (pseq n) x) :=
  ⟨carrierLimit_converges X.toGeneralCompletionCauchy, X.represents⟩

end YMGap.Continuum.ContinuousFCCarrierLimit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GNSQuotient.GNSData.cAdd_embedZero_left
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cAdd_embedZero_right
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cAdd_add_add_comm
#print axioms YMGap.Continuum.HamiltonianScalar.LinearSmulGNSData.cSmul_add_scalar
#print axioms YMGap.Continuum.HamiltonianScalar.qLinearSmulGNS
#print axioms YMGap.Continuum.ContinuousFCCarrierLimit.polyApply_padd
#print axioms YMGap.Continuum.ContinuousFCCarrierLimit.carrierLimit
#print axioms YMGap.Continuum.ContinuousFCCarrierLimit.carrierLimit_converges
#print axioms YMGap.Continuum.ContinuousFCCarrierLimit.fcApply
#print axioms YMGap.Continuum.ContinuousFCCarrierLimit.fcApply_converges
