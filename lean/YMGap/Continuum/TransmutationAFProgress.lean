/-
Track B3 (transmutation) — **Closing the "one honest gap": the
Cauchy-tail ⇒ bounded-partial-sums bridge that discharges
`SummableDescentTower.summable` from the standard EFT quadratic-defect datum.**

# What this module does (read first)

The continuum-gap program factors `physGap = margin / spacing`.  The natural
candidate — "the physical AF separators are EXACTLY self-similar
(`selfSimilarC b physSep`), grounded in `afBlocked_ratio_ge` + the transmutation
limit" — is REFUTED elsewhere as a category error (spacing vs. margin) compounded
by a finite-step mismatch (`R = 1+M·L ≠ b+1`; the AF spacing ratio is only
ASYMPTOTICALLY geometric).  On ℝ⁴ the exact `δ=0` descent is false; the correct
node is the RELAXED `SummableDescentTower` whose per-step defect `δ_k` is
summable.

`AFDeltaDecay.SummableDescentTower.summable` demands BOUNDED PARTIAL SUMS
`∀ n, lossSum δ n ≤ R`.  The proved AF endpoint
`AFTrajectoryCertificate.quadratic_defect_summable` instead yields a dyadic
CAUCHY-TAIL modulus `∀ r M', tailSum δ (N r) M' ≤ (½)^r` from the standard
Symanzik/HNS majorant `δ_k ≤ M · 1/(k+B)²` (itself the majorization of
`δ_k = O(a_k²)` through the proved reciprocal AF rate).  The bridge between these
two shapes was the SINGLE not-yet-in-Lean gap — "pure `Q'` bookkeeping over the
existing `tailSum`, no analysis."  This module writes it.

Contents:

  * **(§1) `lossSum_split`** — the split identity
    `lossSum δ (N+M) ≃ lossSum δ N + tailSum δ N M` bridging `ProductFloor.lossSum`
    and `SummableInverseSquare.tailSum`.
  * **(§1) `lossSum_le_add`** — monotonicity of the (nonnegative) partial sum.
  * **(§2) `partial_sum_bound_of_tail_bound`** — THE BRIDGE: a single uniform tail
    bound `tailSum δ N M ≤ C` (any window) yields
    `∀ n, lossSum δ n ≤ lossSum δ N + C`.
  * **(§2) `partial_sum_bound_of_cauchy_modulus`** — feed the Cauchy modulus at
    `r=0` (`R := lossSum δ (N 0) + (½)^0`).
  * **(§3) `quadratic_defect_partial_sum_bound`** — compose with the proved
    `quadratic_defect_summable`: from `δ_k ≤ M·1/(k+B)²` obtain a concrete `R`
    with `∀ n, lossSum δ n ≤ R`.  This is EXACTLY the `summable` shape.
  * **(§4) `SummableDescentTower.ofCore_quadratic`** — THE PAYOFF: a
    `DescentTowerCore` (all exponent-tower fields except `R`/`summable`) plus a
    quadratic-defect majorant on `δ` produces a full `SummableDescentTower`, with
    `summable` DISCHARGED by the bridge.  So `summable` is NOT open; the genuine
    residual re-localizes entirely onto `AsymptoticDescentInput.recursion`
    (the `s=1` spectral-margin obligation, uninhabited on ℝ⁴).
  * **(§4) `quadratic_defect_partial_sum_bound_demo`** — a non-vacuous firing on
    `δ_k = 1/(k+2)²`.

# Honest scope

Every declaration here is genuine axiom-clean `Q'` plumbing composing three
already-green machines (`ProductFloor.lossSum`, `SummableInverseSquare.tailSum`,
`AFTrajectoryCertificate.quadratic_defect_summable`).  Nothing fabricates the
physical exponent tower or the margin recursion; `DescentTowerCore` bundles the
tower data as HONEST named inputs.  The reduction claim is precise: the
`summable` field of the relaxed self-similar node is dischargeable from the
standard EFT scaling datum, so it is off the critical path.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition; every carrier is `Type`-level data.  Each load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.AFDeltaDecay
import YMGap.Continuum.AFTrajectoryCertificate
import YMGap.Continuum.SummableInverseSquare

namespace YMGap.Continuum.TransmutationAFProgress

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum

/-! ## 1. Splitting a partial sum into a prefix + a tail window

`ProductFloor.lossSum δ n = ∑_{k<n} δ k` (prefix) and
`SummableInverseSquare.tailSum δ N M = ∑_{j<M} δ (N+j)` (window).  They compose
by the elementary split `∑_{k<N+M} = ∑_{k<N} + ∑_{j<M} δ (N+j)`. -/

/-- **The split identity.**  `lossSum δ (N+M) ≃ lossSum δ N + tailSum δ N M`.
Induction on the window length `M`; the step reassociates the newly-added term
`δ (N+M)` (shared by both `lossSum (…+1)` and `tailSum (…+1)`). -/
theorem lossSum_split (δ : Nat → Q') (N : Nat) :
    ∀ M, (ProductFloor.lossSum δ (N + M)).eqv
      (ProductFloor.lossSum δ N + SummableInverseSquare.tailSum δ N M)
  | 0 =>
      -- `N + 0 = N` and `tailSum δ N 0 = 0`, so this is `x ≃ x + 0`.
      Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (ProductFloor.lossSum δ N)))
  | M + 1 => by
      -- LHS = lossSum δ (N+M) + δ (N+M); RHS = lossSum δ N + (tailSum δ N M + δ (N+M)).
      show (ProductFloor.lossSum δ (N + M) + δ (N + M)).eqv
          (ProductFloor.lossSum δ N
            + (SummableInverseSquare.tailSum δ N M + δ (N + M)))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (δ (N + M)) (lossSum_split δ N M)) ?_
      -- (lossSum N + tailSum N M) + δ(N+M) ≃ lossSum N + (tailSum N M + δ(N+M)).
      exact Q'.add_assoc_eqv _ _ _

/-- **Monotonicity of the (nonnegative) partial sum.**
`lossSum δ n ≤ lossSum δ (n + d)`; induction on `d` adds the nonnegative
`δ (n+d)`. -/
theorem lossSum_le_add (δ : Nat → Q') (hδ0 : ∀ k, (0 : Q') ≤ δ k) (n : Nat) :
    ∀ d, ProductFloor.lossSum δ n ≤ ProductFloor.lossSum δ (n + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      -- lossSum δ (n+(d+1)) = lossSum δ (n+d) + δ (n+d).
      show ProductFloor.lossSum δ n
          ≤ ProductFloor.lossSum δ (n + d) + δ (n + d)
      exact Q'.le_trans' _ _ _ (lossSum_le_add δ hδ0 n d)
        (Q'.add_le_self_of_nonneg _ _ (hδ0 (n + d)))

/-! ## 2. The bridge: uniform tail bound ⇒ bounded partial sums -/

/-- **THE BRIDGE.**  For a nonnegative `δ`, a SINGLE uniform window bound
`tailSum δ N M ≤ C` (for every window length `M`) forces EVERY partial sum to be
bounded: `∀ n, lossSum δ n ≤ lossSum δ N + C`.

Proof: `lossSum δ n ≤ lossSum δ (n+N)` (monotonicity), `n+N = N+n`,
`lossSum δ (N+n) ≃ lossSum δ N + tailSum δ N n` (split), and
`tailSum δ N n ≤ C` (the hypothesis).  No analysis — pure `Q'` bookkeeping. -/
theorem partial_sum_bound_of_tail_bound (δ : Nat → Q')
    (hδ0 : ∀ k, (0 : Q') ≤ δ k) (N : Nat) (C : Q')
    (htail : ∀ M, SummableInverseSquare.tailSum δ N M ≤ C) :
    ∀ n, ProductFloor.lossSum δ n ≤ ProductFloor.lossSum δ N + C := by
  intro n
  have h1 : ProductFloor.lossSum δ n ≤ ProductFloor.lossSum δ (n + N) :=
    lossSum_le_add δ hδ0 n N
  have h2 : ProductFloor.lossSum δ (n + N) = ProductFloor.lossSum δ (N + n) :=
    congrArg (ProductFloor.lossSum δ) (Nat.add_comm n N)
  have h3 : (ProductFloor.lossSum δ (N + n)).eqv
      (ProductFloor.lossSum δ N + SummableInverseSquare.tailSum δ N n) :=
    lossSum_split δ N n
  have h4 : ProductFloor.lossSum δ N + SummableInverseSquare.tailSum δ N n
      ≤ ProductFloor.lossSum δ N + C :=
    Q'.add_le_add_left _ _ _ (htail n)
  refine Q'.le_trans' _ _ _ h1 ?_
  rw [h2]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h3) h4

/-- **The Cauchy-modulus corollary.**  A dyadic Cauchy-tail modulus
`∀ r M', tailSum δ (Nf r) M' ≤ (½)^r` (the shape `quadratic_defect_summable`
emits) yields a concrete uniform bound `R := lossSum δ (Nf 0) + (½)^0` on all
partial sums, by feeding the bridge the `r = 0` slice. -/
def partial_sum_bound_of_cauchy_modulus (δ : Nat → Q')
    (hδ0 : ∀ k, (0 : Q') ≤ δ k) (Nf : Nat → Nat)
    (hmod : ∀ r M', SummableInverseSquare.tailSum δ (Nf r) M'
      ≤ HalfPow.half ^ r) :
    Σ' R : Q', ∀ n, ProductFloor.lossSum δ n ≤ R :=
  ⟨ProductFloor.lossSum δ (Nf 0) + HalfPow.half ^ 0,
   partial_sum_bound_of_tail_bound δ hδ0 (Nf 0) (HalfPow.half ^ 0)
     (fun M => hmod 0 M)⟩

/-! ## 3. Composing with the proved quadratic-defect summability -/

/-- **THE SUMMABILITY-FIELD DISCHARGE.**  From the standard EFT majorant
`δ_k ≤ M · 1/(k+B)²` (`M > 0`, integer `B ≥ 2`) — the Symanzik/HNS
`δ_k = O(a_k²)` after majorization through the proved reciprocal AF rate — the
proved `quadratic_defect_summable` gives the Cauchy modulus, and the bridge turns
it into a concrete `R` with `∀ n, lossSum δ n ≤ R`.  This is EXACTLY the
`SummableDescentTower.summable` shape, produced with no new summability
assumption. -/
def quadratic_defect_partial_sum_bound
    (M : Q') (B : Nat) (hM : (0 : Q') < M) (hB : 2 ≤ B) (δ : Nat → Q')
    (hδ0 : ∀ k, (0 : Q') ≤ δ k)
    (hδmaj : ∀ k, δ k ≤ M * SummableInverseSquare.invSqTerm B hB k) :
    Σ' R : Q', ∀ n, ProductFloor.lossSum δ n ≤ R :=
  let mod :=
    AFTrajectoryCertificate.quadratic_defect_summable M B hM hB δ hδ0 hδmaj
  partial_sum_bound_of_cauchy_modulus δ hδ0 mod.1 mod.2

/-! ## 4. The payoff — discharging `SummableDescentTower.summable` -/

/-- **The exponent-tower data of a summable-descent tower MINUS `R`/`summable`.**
All fields of `AFDeltaDecay.SummableDescentTower` except the summability witness;
these are the honest physical-tower inputs (the exponent flow with its
per-step defect `δ`), carried verbatim.  Bundling them separately makes the
summability discharge (below) precise: `R`/`summable` are the ONLY fields the
bridge supplies. -/
structure DescentTowerCore (b : Nat) : Type where
  /-- The exponent at scale `k`. -/
  w : Nat → CReal
  /-- Its modulus data. -/
  dw : ∀ k, ExpNegCData (w k)
  /-- The `(b+1)`-fold sub-unit bound at level `k+1`. -/
  bnd : ∀ k j, (scaleN (b + 1) (w (k + 1))).approx j ≤ 1
  /-- The per-step rational defect majorant `δ_k`. -/
  δ : Nat → Q'
  /-- The defect is nonnegative. -/
  δ_nonneg : ∀ k, (0 : Q') ≤ δ k
  /-- The defect is `≤ ½`. -/
  δ_le_half : ∀ k, δ k ≤ HalfPow.half
  /-- The sub-unit bound on the approximate exponent `(b+1)·w_{k+1} + δ_k`. -/
  sumbnd : ∀ k j, (scaleN (b + 1) (w (k + 1))).approx j + δ k ≤ 1
  /-- **APPROXIMATE descent** (pointwise): `w_k ≃ (b+1)·w_{k+1} + δ_k`. -/
  descent : ∀ k j,
    ((w k).approx j).eqv ((scaleN (b + 1) (w (k + 1))).approx j + δ k)

/-- **THE RELAXED-NODE REDUCTION.**  A `DescentTowerCore b` together with a
quadratic-defect majorant `δ_k ≤ M·1/(k+B)²` on its defect PRODUCES a full
`AFDeltaDecay.SummableDescentTower b`: the `R` and `summable` fields are
discharged by `quadratic_defect_partial_sum_bound` (no separate summability
input).  Hence `SummableDescentTower.summable` is NOT an open obligation — the
genuine open content re-localizes onto `AsymptoticDescentInput.recursion`, the
`s=1` spectral-margin statement (uninhabited on ℝ⁴). -/
def SummableDescentTower.ofCore_quadratic {b : Nat}
    (core : DescentTowerCore b)
    (M : Q') (B : Nat) (hM : (0 : Q') < M) (hB : 2 ≤ B)
    (hmaj : ∀ k, core.δ k ≤ M * SummableInverseSquare.invSqTerm B hB k) :
    AFDeltaDecay.SummableDescentTower b :=
  let sb :=
    quadratic_defect_partial_sum_bound M B hM hB core.δ core.δ_nonneg hmaj
  { w := core.w
    dw := core.dw
    bnd := core.bnd
    δ := core.δ
    δ_nonneg := core.δ_nonneg
    δ_le_half := core.δ_le_half
    sumbnd := core.sumbnd
    descent := core.descent
    R := sb.1
    summable := sb.2 }

/-- **A non-vacuous firing.**  With `M = 1`, `B = 2`, and the concrete defect
`δ_k = 1/(k+2)²`, the composed pipeline produces an explicit uniform partial-sum
bound `R` for the summable series.  (This exercises only the summability
machinery; it does NOT fabricate a physical exponent tower.) -/
def quadratic_defect_partial_sum_bound_demo :
    Σ' R : Q', ∀ n, ProductFloor.lossSum
      (fun k => SummableInverseSquare.invSqTerm 2 (by decide) k) n ≤ R :=
  quadratic_defect_partial_sum_bound 1 2 (by decide) (by decide)
    (fun k => SummableInverseSquare.invSqTerm 2 (by decide) k)
    (fun k => SummableInverseSquare.invSqTerm_nonneg 2 (by decide) k)
    (fun k => Q'.ge_of_eqv
      (Q'.one_mul_eqv (SummableInverseSquare.invSqTerm 2 (by decide) k)))

end YMGap.Continuum.TransmutationAFProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TransmutationAFProgress.lossSum_split
#print axioms YMGap.Continuum.TransmutationAFProgress.lossSum_le_add
#print axioms YMGap.Continuum.TransmutationAFProgress.partial_sum_bound_of_tail_bound
#print axioms YMGap.Continuum.TransmutationAFProgress.partial_sum_bound_of_cauchy_modulus
#print axioms YMGap.Continuum.TransmutationAFProgress.quadratic_defect_partial_sum_bound
#print axioms YMGap.Continuum.TransmutationAFProgress.SummableDescentTower.ofCore_quadratic
#print axioms YMGap.Continuum.TransmutationAFProgress.quadratic_defect_partial_sum_bound_demo
