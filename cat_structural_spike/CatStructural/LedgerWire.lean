/-
CatStructural/LedgerWire.lean

The generic wiring layer: from a positive ledger to the categorical
spine, with zero substrate arithmetic beyond `GapSubstrate`.

The main tree's actual per-scale certificates
(`YMGap.RG.SigmaHatPilot`, backed by
`YMGap.Constructive.RationalTail`) are SUBTRACTIVE: an η-budget
sequence with closure `∀ N, Σ_{k<N} η_k ≤ σ̂₀`, inducing the ledger
`σ̂_N = σ̂₀ − Σ_{k<N} η_k`.  The bridge to the MULTIPLICATIVE
categorical layer is the observation that once the closure certificate
delivers ledger POSITIVITY, everything category-side is generic:

  * `selfRatioStep` — the canonical domination `M k ⟶ M (k+1)` with
    ratio `σ_{k+1}/σ_k`; its `bound` is commutativity, its positivity
    fields are the ledger's.  The analytic content enters ONLY through
    the positivity hypothesis — exactly what the budget closure
    provides.
  * Telescoping collapse — the chain composite of self-ratio steps is
    hom-setoid EQUAL to the direct comparison `σ_n/σ_0`
    (`selfRatio_chain_collapse`).  The telescoping product identity is
    a theorem about composition: one associativity + one congruence
    per inductive step.
  * `UniformGapG.ofPointwise` — a pointwise lower bound
    `∀ L, apex ≤ σ_L` (the shape the budget-closure theorem outputs)
    assembles into the uniform-gap cone with unit-ratio legs.  The
    Clay uniformity clause consumes the closure certificate directly.
  * `selfRatio_squares_commute` — the naturality square between two
    self-ratio ledgers along their canonical comparison commutes,
    generically.  This is the POSITIVE control for the standing audit
    guard (`SquareGuard.lean`); ledgers that are NOT honest self-ratio
    presentations of their own values (the `EigShiftOrder` class) fail
    it, kernel-detectably.

Mathlib-free, Classical-free, sorry-free.  The generic layer stays
axiom-free (see `#print axioms` gates).
-/

import CatStructural.Substrate
import CatStructural.DomOver

namespace CatStructural

variable {S : GapSubstrate}

/-! ## Self-ratio steps and their chain -/

/-- The canonical self-ratio domination step of a positive ledger:
    `num = σ_{k+1}`, `den = σ_k`, bound by commutativity.  All analytic
    content is the positivity hypothesis. -/
def selfRatioStep (M : Nat → MassG S)
    (pos : ∀ k, S.lt S.zero (M k).val) (k : Nat) :
    DomG (M k) (M (k + 1)) where
  num := (M (k + 1)).val
  den := (M k).val
  num_nonneg := (M (k + 1)).nonneg
  den_pos := pos k
  bound := S.le_of_eqv (S.mul_comm_eqv (M (k + 1)).val (M k).val)

/-- The direct end-to-end comparison `σ_n/σ_0` as a single morphism. -/
def directHom (M : Nat → MassG S)
    (pos : ∀ k, S.lt S.zero (M k).val) (n : Nat) :
    DomG (M 0) (M n) where
  num := (M n).val
  den := (M 0).val
  num_nonneg := (M n).nonneg
  den_pos := pos 0
  bound := S.le_of_eqv (S.mul_comm_eqv (M n).val (M 0).val)

/-- **Telescoping collapse**: the chain composite of self-ratio steps is
    hom-setoid equal to the direct comparison `σ_n/σ_0`.  The inductive
    step costs exactly one associativity and one congruence — the
    telescoping product identity has become a statement about
    composition. -/
theorem selfRatio_chain_collapse (M : Nat → MassG S)
    (pos : ∀ k, S.lt S.zero (M k).val) (n : Nat) :
    DomG.eqv (chainG M (selfRatioStep M pos) n) (directHom M pos n) := by
  induction n with
  | zero =>
    -- ident vs σ₀/σ₀ : 1·σ₀ ≈ σ₀·1
    show S.eqv (S.mul S.one (M 0).val) (S.mul (M 0).val S.one)
    exact S.eqv_trans (S.one_mul_eqv (M 0).val)
      (S.eqv_symm (S.mul_one_eqv (M 0).val))
  | succ n ih =>
    -- (σ_{n+1}·chainNum)·σ₀ ≈ σ_{n+1}·(σ_n·chainDen),
    -- from ih : chainNum·σ₀ ≈ σ_n·chainDen.
    show S.eqv
      (S.mul (S.mul (M (n + 1)).val
        (chainG M (selfRatioStep M pos) n).num) (M 0).val)
      (S.mul (M (n + 1)).val
        (S.mul (M n).val (chainG M (selfRatioStep M pos) n).den))
    exact S.eqv_trans
      (S.mul_assoc_eqv (M (n + 1)).val
        (chainG M (selfRatioStep M pos) n).num (M 0).val)
      (S.mul_congr (S.eqv_refl (M (n + 1)).val) ih)

/-! ## The cone from a pointwise closure certificate -/

/-- A unit-ratio leg from a pointwise bound `a ≤ b`. -/
def unitLeg {a b : MassG S} (h : S.le a.val b.val) : DomG a b where
  num := S.one
  den := S.one
  num_nonneg := S.zero_le_one
  den_pos := S.zero_lt_one
  bound :=
    S.le_trans (S.le_of_eqv (S.one_mul_eqv a.val))
      (S.le_trans h (S.ge_of_eqv (S.one_mul_eqv b.val)))

/-- **The cone from a closure certificate**: a strictly positive apex
    with a pointwise lower bound at every volume assembles into a
    `UniformGapG`.  This is the exact shape of the σ̂-budget closure
    output (`∀ N, Σ η ≤ total < σ̂₀` gives `apex := σ̂₀ − total ≤ σ̂_N`),
    so the certificate IS the cone data. -/
def UniformGapG.ofPointwise {G : Nat → MassG S} (apex : MassG S)
    (apex_pos : S.lt S.zero apex.val)
    (h : ∀ L, S.le apex.val (G L).val) : UniformGapG G where
  apex := apex
  apex_pos := apex_pos
  leg L := unitLeg (h L)
  leg_unit _ := S.eqv_refl S.one

/-! ## The canonical comparison and its naturality

The standing-guard API (`square`, `squaresUpTo`) lives in
`SquareGuard.lean`; this section supplies the guard's generic POSITIVE
control.  The commute statement below is definitionally
`SquareGuard.square` at self-ratio ledgers — stated raw here to keep
this module free of the guard's (QS-demo-carrying) import. -/

/-- The canonical (ratio) comparison between two positive ledgers:
    component `σ'_k/σ_k`. -/
def ratioHom (F G : Nat → MassG S)
    (posF : ∀ k, S.lt S.zero (F k).val) (k : Nat) :
    DomG (F k) (G k) where
  num := (G k).val
  den := (F k).val
  num_nonneg := (G k).nonneg
  den_pos := posF k
  bound := S.le_of_eqv (S.mul_comm_eqv (G k).val (F k).val)

/-- **Positive control, generically**: between honest self-ratio
    presentations of any two positive ledgers, the canonical-comparison
    naturality square commutes at every index: both composites carry
    the ratio `G_{k+1}/F_k`, and the cross products of the square
    rearrange to the same 4-atom product by interchange.

    The audit-guard payoff is the CONTRAPOSITIVE: a ledger presented
    with step data that is NOT the self-ratio of its own values — e.g.
    a vacuum-shifted ledger keeping the unshifted ratios, the
    `EigShiftOrder` class — makes this square FAIL, and the failure is
    kernel-decidable.  See `SquareGuard.lean` for the standing device
    and its banked refutation. -/
theorem selfRatio_squares_commute (F G : Nat → MassG S)
    (posF : ∀ k, S.lt S.zero (F k).val)
    (posG : ∀ k, S.lt S.zero (G k).val) (k : Nat) :
    DomG.eqv
      (DomG.comp (selfRatioStep F posF k) (ratioHom F G posF (k + 1)))
      (DomG.comp (ratioHom F G posF k) (selfRatioStep G posG k)) := by
  -- LHS composite: num = G_{k+1}·F_{k+1}, den = F_{k+1}·F_k
  -- RHS composite: num = G_{k+1}·G_k,     den = G_k·F_k
  -- Square: (G_{k+1}·F_{k+1})·(G_k·F_k) ≈ (G_{k+1}·G_k)·(F_{k+1}·F_k)
  -- — the interchange law.
  show S.eqv
    (S.mul (S.mul (G (k + 1)).val (F (k + 1)).val)
           (S.mul (G k).val (F k).val))
    (S.mul (S.mul (G (k + 1)).val (G k).val)
           (S.mul (F (k + 1)).val (F k).val))
  exact S.mul_interchange_eqv (G (k + 1)).val (F (k + 1)).val
    (G k).val (F k).val

#print axioms selfRatioStep
#print axioms selfRatio_chain_collapse
#print axioms UniformGapG.ofPointwise
#print axioms selfRatio_squares_commute

end CatStructural
