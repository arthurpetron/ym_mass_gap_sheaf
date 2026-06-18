/-
The constructive **product floor** — converting the open RG persistence
obligation into a single summability statement.

# What this module delivers

The per-block persistence obligation (`RGBlockPersistence`) needs a single
positive constant `c > 0` with `c ≤ ∏_{k<n} ρ_k` for every prefix length `n`
(the per-block gap multipliers' product stays bounded below).  Writing
`η_k := 1 − ρ_k` for the per-block *loss*, this module proves — entirely in the
constructive rationals `Q'`, axiom-clean — the elementary product floor

    ∏_{k<n} (1 − η_k)  ≥  1 − ∑_{k<n} η_k          (Weierstrass form)

valid for `0 ≤ η_k`, and hence, from any uniform partial-sum bound
`∑_{k<n} η_k ≤ R`, the uniform floor

    ∏_{k<n} (1 − η_k)  ≥  1 − R ,

which is **strictly positive whenever `R < 1`**.  This reduces the persistence
product-floor obligation to the clean *summability* statement
`∑_k (1 − ρ_k) ≤ R < 1`, i.e. the per-block losses are summable with a small
enough total.

# Why the Weierstrass floor (and the `R < 1` honesty)

The sharper floor `∏(1 − η_k) ≥ e^{−2R}` (positive for *all* finite `R`) needs a
reciprocal / division on the constructive reals to bound `e^{−2x}` from above by
a symbolic `1 − x`, which the present `CReal` layer does not carry (its order is
the one-slack Bishop order, not transitively chainable, and there is no `CReal`
reciprocal).  The Weierstrass floor needs none of that: it is a pure `Q'`
induction, it is genuinely *proved*, and — crucially — its floor constant
`1 − R` is itself a `Q'`, so it populates the persistence `prodFloor` field
(also a `Q'`) directly.  The cost is the regime restriction `R < 1`; this module
states that restriction openly.

The accompanying `exp` facts that the present `CReal` layer *does* support
(`1 + x ≤ e^x` and the strict positivity of `e^{x}` for `x ≥ 0`) are recorded as
companions, but the load-bearing floor is the Weierstrass one.

# The named obligation this reduces to

This module proves the *reduction*.  It does NOT inhabit the summability
hypothesis `∑_k (1 − ρ_k) ≤ R < 1` for 4D Yang–Mills — that is the open RG
content (the per-block losses being summable along the asymptotic-freedom
trajectory).  The reduction is honest: a finite-prefix, explicit-`R` statement,
no compactness, no inhabitant of the open hypothesis.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms` at the bottom; the
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  Every constant is `Type`-level `Q'` data.
-/

import YMGap.Constructive.ExpPos
import YMGap.Continuum.RGGapPersistence

namespace YMGap.Continuum.ProductFloor

open YMGap.Constructive

/-! ## 1. The finite loss sum and the one-minus-loss product (in `Q'`)

`lossSum η n = ∑_{k<n} η_k` and `prodOneSub η n = ∏_{k<n} (1 − η_k)`.  Both are
pure `Q'` recursions; the empty sum is `0` and the empty product is `1`. -/

/-- The finite partial sum `∑_{k<n} η_k`. -/
def lossSum (η : Nat → Q') : Nat → Q'
  | 0 => 0
  | n + 1 => lossSum η n + η n

/-- The finite product `∏_{k<n} (1 − η_k)` (empty product `= 1`). -/
def prodOneSub (η : Nat → Q') : Nat → Q'
  | 0 => (1 : Q')
  | n + 1 => prodOneSub η n * (1 - η n)

@[simp] theorem lossSum_zero (η : Nat → Q') : lossSum η 0 = 0 := rfl
@[simp] theorem lossSum_succ (η : Nat → Q') (n : Nat) :
    lossSum η (n + 1) = lossSum η n + η n := rfl
@[simp] theorem prodOneSub_zero (η : Nat → Q') : prodOneSub η 0 = 1 := rfl
@[simp] theorem prodOneSub_succ (η : Nat → Q') (n : Nat) :
    prodOneSub η (n + 1) = prodOneSub η n * (1 - η n) := rfl

/-- The loss sum is nonnegative when every loss is. -/
theorem lossSum_nonneg (η : Nat → Q') (hη : ∀ k, (0 : Q') ≤ η k) :
    ∀ n, (0 : Q') ≤ lossSum η n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
    show (0 : Q') ≤ lossSum η n + η n
    exact Q'.zero_le_add _ _ (lossSum_nonneg η hη n) (hη n)

/-! ## 2. The elementary Weierstrass step (pure `Q'`)

The crux: for `0 ≤ S` and `0 ≤ η`,

    (1 − S) · (1 − η)  ≥  1 − (S + η) .

Reason: `(1 − S)(1 − η) = (1 − (S + η)) + S·η`, and `S·η ≥ 0`.  The proof
establishes the `eqv` identity `(1 − (S + η)) + S·η ≃ (1 − S)·(1 − η)` and then
drops the nonnegative `S·η`. -/

/-- The algebraic identity `(1 − (S + η)) + S·η ≃ (1 − S)·(1 − η)`, all in `Q'`. -/
theorem weierstrass_identity (S η : Q') :
    ((1 - (S + η)) + S * η).eqv ((1 - S) * (1 - η)) := by
  -- Expand the RHS: (1 - S)*(1 - η) = (1 + -S)*(1 + -η)
  --   ≃ 1*(1+-η) + (-S)*(1+-η)
  --   ≃ (1 + -η) + ((-S) + (-S)*(-η))
  -- and the LHS: (1 + -(S+η)) + S*η.
  -- We prove RHS ≃ LHS by normalizing both to (1 + -S + -η + S*η)-shaped sums.
  -- Work on the RHS, transforming it down to the LHS, then take eqv_symm.
  -- `1 - x` is `1 + (-x)` definitionally.
  -- (1 + -S) * (1 + -η) ≃ (1 + -S)*1 + (1 + -S)*(-η)
  have e1 : ((1 + -S) * (1 + -η)).eqv ((1 + -S) * 1 + (1 + -S) * (-η)) :=
    Q'.mul_add_eqv (1 + -S) 1 (-η)
  -- (1 + -S)*1 ≃ 1 + -S
  have e2 : ((1 + -S) * 1).eqv (1 + -S) := Q'.mul_one_eqv (1 + -S)
  -- (1 + -S)*(-η) ≃ -( (1 + -S)*η ) ≃ -( 1*η + (-S)*η ) ≃ -(η + -(S*η))
  --   ≃ -η + S*η
  have e3 : ((1 + -S) * (-η)).eqv ((-η) + S * η) := by
    -- (1+-S)*(-η) ≃ -((1+-S)*η)
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (1 + -S) η) ?_
    -- (1+-S)*η ≃ 1*η + (-S)*η ≃ η + -(S*η)
    have h : ((1 + -S) * η).eqv (η + -(S * η)) := by
      refine Q'.eqv_trans _ _ _ (ExpNeg.add_mul_eqv 1 (-S) η) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (1 * η) η (-S * η) (Q'.one_mul_eqv η)) ?_
      exact Q'.add_eqv_congr_left η (-S * η) (-(S * η)) (Q'.neg_mul_eqv S η)
    -- -( η + -(S*η) ) ≃ (-η) + S*η
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h) ?_
    -- -(η + -(S*η)) ≃ -η + -(-(S*η)) ≃ -η + S*η ; use add_mul / neg laws
    -- Direct: -(a + b) ≃ (-a) + (-b) via neg of add — derive from add_mul? use components.
    -- Build -(η + -(S*η)) ≃ (-η) + (S*η) by: it equals -1*(η + -(S*η)).
    have hneg : (-(η + -(S * η))).eqv ((-η) + S * η) := by
      -- -(x) ≃ (-1)*x for any x; then distribute.
      -- Use: -(η + c) where c = -(S*η).  -(η+c) ≃ (-1)*(η+c) ≃ (-1)*η + (-1)*c
      --   ≃ -η + -c ≃ -η + -(-(S*η)) ≃ -η + S*η.
      have hm1 : (-(η + -(S * η))).eqv ((-1 : Q') * (η + -(S * η))) :=
        Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (η + -(S*η)))
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (η + -(S*η)))))
      refine Q'.eqv_trans _ _ _ hm1 ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-1 : Q') η (-(S*η))) ?_
      -- (-1)*η ≃ -η ; (-1)*(-(S*η)) ≃ S*η
      have ha : ((-1 : Q') * η).eqv (-η) :=
        Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 η) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv η))
      have hb : ((-1 : Q') * (-(S*η))).eqv (S * η) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-1 : Q') (S*η)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv 1 (S*η))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (1 * (S*η))) ?_
        exact Q'.one_mul_eqv (S*η)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((-1:Q')*η) (-η) ((-1:Q')*(-(S*η))) ha)
        (Q'.add_eqv_congr_left (-η) ((-1:Q')*(-(S*η))) (S*η) hb)
    exact hneg
  -- Assemble: RHS ≃ (1 + -S) + ((-η) + S*η)
  have eR : ((1 + -S) * (1 + -η)).eqv ((1 + -S) + ((-η) + S * η)) :=
    Q'.eqv_trans _ _ _ e1
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ e2)
        (Q'.add_eqv_congr_left (1 + -S) _ _ e3))
  -- Now (1 + -S) + ((-η) + S*η) ≃ ((1 + -S) + -η) + S*η  ≃  (1 + -(S+η)) + S*η.
  have eAssoc : ((1 + -S) + ((-η) + S * η)).eqv (((1 + -S) + -η) + S * η) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (1 + -S) (-η) (S * η))
  -- (1 + -S) + -η ≃ 1 + (-S + -η) ≃ 1 + -(S+η)
  have eHead : (((1 + -S) + -η)).eqv (1 + -(S + η)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-S) (-η)) ?_
    -- -S + -η ≃ -(S+η)
    have hneg_add : ((-S) + -η).eqv (-(S + η)) := by
      -- -(S+η) ≃ (-1)*(S+η) ≃ (-1)*S + (-1)*η ≃ -S + -η
      have hm1 : (-(S + η)).eqv ((-1 : Q') * (S + η)) :=
        Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (S+η))
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (S+η))))
      have hdist : ((-1 : Q') * (S + η)).eqv ((-S) + -η) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-1 : Q') S η) ?_
        have ha : ((-1 : Q') * S).eqv (-S) :=
          Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 S) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv S))
        have hb : ((-1 : Q') * η).eqv (-η) :=
          Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 η) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv η))
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right ((-1:Q')*S) (-S) ((-1:Q')*η) ha)
          (Q'.add_eqv_congr_left (-S) ((-1:Q')*η) (-η) hb)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hm1 hdist)
    exact Q'.add_eqv_congr_left 1 (-S + -η) (-(S + η)) hneg_add
  -- (1 + -(S+η)) is exactly (1 - (S+η)) definitionally.
  -- chain : ((1-S)*(1-η)).eqv ((1-(S+η))+S*η); goal is its symm.
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ eR (Q'.eqv_trans _ _ _ eAssoc ?_))
  -- ((1+-S)+-η)+S*η  ≃  (1+-(S+η))+S*η  =  (1-(S+η))+S*η
  exact Q'.add_eqv_congr_right ((1 + -S) + -η) (1 + -(S + η)) (S * η) eHead

/-- **The Weierstrass step.**  For `0 ≤ S` and `0 ≤ η`,
`1 − (S + η) ≤ (1 − S) · (1 − η)`. -/
theorem weierstrass_step (S η : Q') (hS : (0 : Q') ≤ S) (hη : (0 : Q') ≤ η) :
    (1 - (S + η)) ≤ (1 - S) * (1 - η) := by
  -- 1 - (S+η) ≤ (1 - (S+η)) + S*η ≃ (1-S)*(1-η)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (1 - (S + η)) (S * η) (Q'.mul_nonneg S η hS hη)) ?_
  exact Q'.le_of_eqv (weierstrass_identity S η)

/-! ## 3. The finite Weierstrass product floor -/

/-- **The finite product floor (Weierstrass form).**  For nonnegative losses,
`1 − ∑_{k<n} η_k ≤ ∏_{k<n} (1 − η_k)`.  Induction on `n`: the step applies
`weierstrass_step` at `S = lossSum η n`, `η = η n` and multiplies by the
nonnegative `(1 − η n)` factor — using that, for `η n ≤ 1`, `0 ≤ 1 − η n`. -/
theorem prod_floor_weierstrass (η : Nat → Q')
    (hη0 : ∀ k, (0 : Q') ≤ η k) (hη1 : ∀ k, η k ≤ 1) :
    ∀ n, (1 - lossSum η n) ≤ prodOneSub η n
  | 0 => by
    show (1 - lossSum η 0) ≤ (1 : Q')
    rw [lossSum_zero]
    exact Q'.le_of_eqv (Q'.sub_zero' 1 ▸ Q'.eqv_refl (1 : Q'))
  | n + 1 => by
    have ih := prod_floor_weierstrass η hη0 hη1 n
    -- 1 - lossSum η (n+1) = 1 - (lossSum η n + η n)
    show (1 - (lossSum η n + η n)) ≤ prodOneSub η n * (1 - η n)
    -- Step 1: 1 - (S + η n) ≤ (1 - S)*(1 - η n)
    have hstep : (1 - (lossSum η n + η n)) ≤ (1 - lossSum η n) * (1 - η n) :=
      weierstrass_step (lossSum η n) (η n) (lossSum_nonneg η hη0 n) (hη0 n)
    -- Step 2: (1 - S)*(1 - η n) ≤ prodOneSub η n * (1 - η n), since 0 ≤ 1 - η n
    have hfac : (0 : Q') ≤ 1 - η n := by
      -- 0 ≤ 1 - η n  ⟺  η n ≤ 1
      show (0 : Q') ≤ 1 + (- η n)
      -- 1 + (-η n) ≥ 0 from η n ≤ 1: add (-η n) to both sides of η n ≤ 1
      have h := Q'.add_le_add_right (η n) 1 (- η n) (hη1 n)
      -- h : η n + (-η n) ≤ 1 + (-η n)
      refine Q'.le_trans' _ _ _ ?_ h
      exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (η n))
    have hmul : (1 - lossSum η n) * (1 - η n) ≤ prodOneSub η n * (1 - η n) :=
      Q'.mul_le_mul_of_nonneg_right (1 - lossSum η n) (prodOneSub η n) (1 - η n) ih hfac
    exact Q'.le_trans' _ _ _ hstep hmul

/-! ## 4. The floor from a uniform summability bound

From a uniform partial-sum bound `∑_{k<n} η_k ≤ R` we get `1 − R ≤ ∏_{k<n}(1−η_k)`
for every `n`; the floor is the single `Q'` constant `1 − R`, strictly positive
exactly when `R < 1`. -/

/-- **The product floor from summability.**  If every loss partial sum is `≤ R`,
then `1 − R ≤ ∏_{k<n} (1 − η_k)` for every prefix length `n`. -/
theorem prod_floor_of_sum_le (η : Nat → Q')
    (hη0 : ∀ k, (0 : Q') ≤ η k) (hη1 : ∀ k, η k ≤ 1)
    (R : Q') (hR : ∀ n, lossSum η n ≤ R) :
    ∀ n, (1 - R) ≤ prodOneSub η n := by
  intro n
  -- 1 - R ≤ 1 - lossSum η n ≤ prodOneSub η n
  refine Q'.le_trans' _ _ _ ?_ (prod_floor_weierstrass η hη0 hη1 n)
  -- 1 - R ≤ 1 - lossSum η n  ⟺  lossSum η n ≤ R: subtract from 1 (antitone)
  show (1 + (-R)) ≤ (1 + (- lossSum η n))
  -- from lossSum η n ≤ R: -R ≤ -lossSum η n, then add 1 on the left
  have hneg : (-R) ≤ (- lossSum η n) := by
    -- -R ≤ -S from S ≤ R : add (-R + -S) ... use cross form via add_le_add
    -- S ≤ R  ⟹  S + (-R) + (-S) ≤ R + (-R) + (-S); simpler: use that
    -- (-R) = (-R), (-S) and the order lemma on negation.
    -- Build: -R ≤ -S  ⟺  S ≤ R via adding (-R) and (-S).
    have h1 : lossSum η n + (-R) ≤ R + (-R) :=
      Q'.add_le_add_right (lossSum η n) R (-R) (hR n)
    have h2 : (-(lossSum η n)) + (lossSum η n + (-R)) ≤ (-(lossSum η n)) + (R + (-R)) :=
      Q'.add_le_add_left (-(lossSum η n)) _ _ h1
    -- LHS ≃ -R ; RHS ≃ -lossSum η n
    have eL : ((-(lossSum η n)) + (lossSum η n + (-R))).eqv (-R) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (-(lossSum η n)) (lossSum η n) (-R))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ 0 (-R) (Q'.neg_add_self_eqv (lossSum η n))) ?_
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 (-R)) (Q'.eqv_of_eq (Q'.add_zero' (-R)))
    have eR' : ((-(lossSum η n)) + (R + (-R))).eqv (-(lossSum η n)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ (R + (-R)) 0 (Q'.add_neg_self_eqv R)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (-(lossSum η n)))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL) (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv eR'))
  exact Q'.add_le_add_left 1 (-R) (- lossSum η n) hneg

/-- **Strict positivity of the floor.**  When `R < 1`, the floor constant
`1 − R` is strictly positive. -/
theorem oneSubR_pos (R : Q') (hR1 : R < 1) : (0 : Q') < 1 - R := by
  -- Work at the Int cross-product level.  `R < 1` is `R.num * 1 < 1 * R.den`,
  -- i.e. `R.num < R.den`.  Goal `0 < 1 - R` is `0 < (1-R).num`, and
  -- `(1 - R).num = 1*R.den + (-R.num)*1 = R.den - R.num > 0`.
  have hRnd : R.num < (R.den : Int) := by
    have h : R.num * ((1 : Q').den : Int) < (1 : Q').num * (R.den : Int) := hR1
    show R.num < (R.den : Int)
    -- (1:Q').num = 1, (1:Q').den = 1
    have hn : (1 : Q').num = 1 := rfl
    have hd : ((1 : Q').den : Int) = 1 := rfl
    rw [hn, hd, Int.mul_one, Int.one_mul] at h
    exact h
  show (0 : Q').num * ((1 - R).den : Int) < (1 - R).num * ((0 : Q').den : Int)
  have h0n : (0 : Q').num = 0 := rfl
  have h0d : ((0 : Q').den : Int) = 1 := rfl
  rw [h0n, h0d, Int.zero_mul, Int.mul_one]
  -- (1 - R).num = (1).num * (-R).den + (-R).num * (1).den
  --             = 1 * R.den + (-R.num) * 1 = R.den - R.num
  show (0 : Int) < ((1 : Q').num * ((-R).den : Int) + (-R).num * ((1 : Q').den : Int))
  have e1 : ((-R).den : Int) = (R.den : Int) := rfl
  have e2 : (-R).num = -R.num := rfl
  rw [e1, e2]
  have hn : (1 : Q').num = 1 := rfl
  have hd : ((1 : Q').den : Int) = 1 := rfl
  rw [hn, hd, Int.one_mul, Int.mul_one]
  -- 0 < R.den + (-R.num)  ⟺  R.num < R.den
  omega

/-! ## 5. The persistence bridge

With `η_k := 1 − ρ_k` (the per-block *loss*), the product `∏_{k<n}(1 − η_k)` is
`∏_{k<n} ρ_k`, and the floor above becomes exactly the product-floor datum the
per-block persistence form (`RGBlockPersistence`) requires.  We provide the
standalone reduction: from `0 ≤ ρ_k ≤ 1`, the summability hypothesis on the
losses `1 − ρ_k`, and `R < 1`, CONSTRUCT a strictly-positive `Q'` constant
`c := 1 − R` with `c ≤ ∏_{k<n} ρ_k` for all `n`.

We match `RGGapPersistence.prodPrefix ρ` (the prefix product the per-block
structure's `prodFloor_le` field is stated against) so the connector is exact. -/

/-- `prodOneSub (fun k => 1 − ρ k)` is definitionally `RGGapPersistence.prodPrefix ρ`
shifted by the `1 − (1 − ρ k) ≃ ρ k` simplification.  We instead relate them by a
direct `eqv` induction: `∏_{k<n}(1 − (1 − ρ k)) ≃ ∏_{k<n} ρ k`. -/
theorem prodOneSub_loss_eqv (ρ : Nat → Q') :
    ∀ n, (prodOneSub (fun k => 1 - ρ k) n).eqv (RGGapPersistence.prodPrefix ρ n)
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
    -- prodOneSub (..) (n+1) = prodOneSub (..) n * (1 - (1 - ρ n))
    -- prodPrefix ρ (n+1) = prodPrefix ρ n * ρ n
    show (prodOneSub (fun k => 1 - ρ k) n * (1 - (1 - ρ n))).eqv
        (RGGapPersistence.prodPrefix ρ n * ρ n)
    have ih := prodOneSub_loss_eqv ρ n
    -- 1 - (1 - ρ n) ≃ ρ n
    have hfac : ((1 - (1 - ρ n))).eqv (ρ n) := by
      -- 1 + -(1 + -ρ n) ≃ 1 + (-1 + ρ n) ≃ (1 + -1) + ρ n ≃ 0 + ρ n ≃ ρ n
      show ((1 : Q') + -(1 + -ρ n)).eqv (ρ n)
      have e1 : (-(1 + -ρ n)).eqv ((-1 : Q') + ρ n) := by
        -- -(1 + -ρ n) ≃ (-1)*(1 + -ρ n) ≃ (-1)*1 + (-1)*(-ρ n) ≃ -1 + ρ n
        have hm1 : (-(1 + -ρ n)).eqv ((-1 : Q') * (1 + -ρ n)) :=
          Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (1 + -ρ n))
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (1 + -ρ n))))
        refine Q'.eqv_trans _ _ _ hm1 ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-1 : Q') 1 (-ρ n)) ?_
        have ha : ((-1 : Q') * 1).eqv (-1 : Q') := Q'.mul_one_eqv (-1 : Q')
        have hb : ((-1 : Q') * (-ρ n)).eqv (ρ n) := by
          refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-1 : Q') (ρ n)) ?_
          refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv 1 (ρ n))) ?_
          refine Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (1 * ρ n)) ?_
          exact Q'.one_mul_eqv (ρ n)
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right ((-1:Q')*1) (-1:Q') ((-1:Q')*(-ρ n)) ha)
          (Q'.add_eqv_congr_left (-1:Q') ((-1:Q')*(-ρ n)) (ρ n) hb)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ e1) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1 : Q') (ρ n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (1 + (-1 : Q')) 0 (ρ n) (Q'.add_neg_self_eqv 1)) ?_
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 (ρ n)) (Q'.eqv_of_eq (Q'.add_zero' (ρ n)))
    -- combine: a*x ≃ b*y from a ≃ b, x ≃ y
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (1 - (1 - ρ n)) ih)
      (Q'.mul_eqv_congr_left (RGGapPersistence.prodPrefix ρ n) _ _ hfac)

/-- **The persistence bridge.**  From per-block multipliers `0 ≤ ρ_k ≤ 1` whose
losses `η_k = 1 − ρ_k` have all partial sums `≤ R < 1`, construct a strictly-
positive `Q'` constant `c = 1 − R` with `c ≤ ∏_{k<n} ρ_k` for every `n` — exactly
the product-floor datum (`prodFloor`, `prodFloor_pos`, and the
`prodPrefix`-shaped bound) that the per-block persistence form requires.

This is the standalone reduction.  Wiring `c` into a full `RGBlockPersistence`
also needs the anchor / recursion / ceiling fields, which are separate physical
inputs; this lemma supplies precisely the product-floor field, in the exact
`RGGapPersistence.prodPrefix ρ` shape, so the connector is a verbatim plug. -/
def sum_block_loss_to_productFloor (ρ : Nat → Q')
    (hρ0 : ∀ k, (0 : Q') ≤ ρ k) (hρ1 : ∀ k, ρ k ≤ 1)
    (R : Q') (hR1 : R < 1)
    (hsum : ∀ n, lossSum (fun k => 1 - ρ k) n ≤ R) :
    Σ' c : Q', (0 : Q') < c ∧ ∀ n, c ≤ RGGapPersistence.prodPrefix ρ n := by
  refine ⟨1 - R, oneSubR_pos R hR1, fun n => ?_⟩
  -- losses η_k = 1 - ρ_k satisfy 0 ≤ η_k (ρ_k ≤ 1) and η_k ≤ 1 (0 ≤ ρ_k).
  have hη0 : ∀ k, (0 : Q') ≤ (1 - ρ k) := by
    intro k
    show (0 : Q') ≤ 1 + (-ρ k)
    have h := Q'.add_le_add_right (ρ k) 1 (-ρ k) (hρ1 k)
    refine Q'.le_trans' _ _ _ ?_ h
    exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (ρ k))
  have hη1 : ∀ k, (1 - ρ k) ≤ 1 := by
    intro k
    -- 1 - ρ k ≤ 1  ⟺  0 ≤ ρ k
    show (1 : Q') + (-ρ k) ≤ 1
    -- 1 + (-ρ k) ≤ 1 + 0 ≃ 1, since -ρ k ≤ 0
    have hnegle : (-ρ k) ≤ (0 : Q') := by
      have h : (0 : Q') + (-ρ k) ≤ ρ k + (-ρ k) :=
        Q'.add_le_add_right (0 : Q') (ρ k) (-ρ k) (hρ0 k)
      -- (-ρ k) ≃ 0 + (-ρ k) ≤ ρ k + (-ρ k) ≃ 0
      refine Q'.le_trans' (-ρ k) (ρ k + (-ρ k)) 0 ?_ ?_
      · exact Q'.le_trans' (-ρ k) ((0 : Q') + (-ρ k)) (ρ k + (-ρ k))
          (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-ρ k)))) h
      · exact Q'.le_of_eqv (Q'.add_neg_self_eqv (ρ k))
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 (-ρ k) 0 hnegle) ?_
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  -- floor on prodOneSub, then transport along prodOneSub ≃ prodPrefix.
  have hfloor : (1 - R) ≤ prodOneSub (fun k => 1 - ρ k) n :=
    prod_floor_of_sum_le (fun k => 1 - ρ k) hη0 hη1 R hsum n
  exact Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv (prodOneSub_loss_eqv ρ n))

/-! ## 6. (Optional) dyadic sufficient condition

A per-step geometric decay `1 − ρ_k ≤ A · r^k` with `0 ≤ r < 1` makes the loss
sum bounded by the geometric closed form, supplying the summability hypothesis of
the bridge for free.  We package the *bounded-partial-sums* form (the exact shape
`sum_block_loss_to_productFloor` consumes): if every loss partial sum is `≤ R`,
nothing more is needed; the dyadic lemma below produces such an `R` from a
geometric tail bound assumption stated as a uniform partial-sum bound. -/

/-- **Dyadic / geometric summability (uniform-bound form).**  If the loss partial
sums are uniformly bounded by `R` (the conclusion of a geometric-series estimate
`∑_{k<n} A r^k ≤ A/(1−r) =: R`), then the bridge applies.  This restates the
hypothesis already consumed by `sum_block_loss_to_productFloor`, recording that a
per-step decay rate suffices once its geometric tail bound is in hand. -/
def dyadic_block_loss (ρ : Nat → Q')
    (hρ0 : ∀ k, (0 : Q') ≤ ρ k) (hρ1 : ∀ k, ρ k ≤ 1)
    (R : Q') (hR1 : R < 1)
    (hgeo : ∀ n, lossSum (fun k => 1 - ρ k) n ≤ R) :
    Σ' c : Q', (0 : Q') < c ∧ ∀ n, c ≤ RGGapPersistence.prodPrefix ρ n :=
  sum_block_loss_to_productFloor ρ hρ0 hρ1 R hR1 hgeo

/-! ## 7. `exp` companions (the facts the present `CReal` layer supports)

The sharper `∏(1 − η_k) ≥ e^{−2R}` floor needs a `CReal` reciprocal to bound
`e^{−2x}` above by `1 − x`, which the layer does not carry.  What it *does*
support, and what is genuinely proved here, are the two elementary exponential
facts: `1 + x ≤ e^x` (`ExpPos.oneAddX_le_expPos`) and the strict positivity of
`e^{x}` for `x ≥ 0`.  The latter gives the positive *constant* `e^{x} > 0`; the
former is the convexity tangent.  These are recorded so the `exp` route's
ingredients are on record, even though the load-bearing floor is Weierstrass. -/

/-- **`e^{x} > 0` for `x ≥ 0`** (constructive positivity).  Every partial sum
`partialSumAbs x n` with `n ≥ 1` is `≥ 1`, so the limit dominates the positive
`Q'`-rational `1` — an `IsPositive` witness with `ε = 1`. -/
theorem expPos_isPositive (x : Q') (hx : (0 : Q') ≤ x) :
    CReal.IsPositive (ExpPos.expPos x hx) := by
  refine ⟨1, by decide, ?_⟩
  -- ofQ' 1 ≤ expPos x : every partial sum from index ≥ 1 is ≥ partialSumAbs x 1 = 1.
  -- Use the monotone lower bound: partialSumAbs x 1 ≤ e^x, and partialSumAbs x 1 = 1.
  -- geRat gives the lower bound; lift to ofQ' via ofQ'_le_of_approx_ge needs ∀ n.
  -- partialSumAbs x 0 = 0, so we cannot use ofQ'_le_of_approx_ge directly at n=0.
  -- Instead use the one-slack order: ofQ' 1 ≤ expPos x means
  --   ∀ n, 1 ≤ partialSumAbs x n + invSucc n.
  intro n
  show (1 : Q') ≤ (ExpPos.expPos x hx).approx n + Q'.invSucc n
  rw [ExpPos.expPos_approx]
  -- For n ≥ 1, partialSumAbs x n ≥ partialSumAbs x 1 = 1, so ≥ 1; for n = 0,
  -- partialSumAbs x 0 = 0 but invSucc 0 = 1, so 0 + 1 ≥ 1.
  cases n with
  | zero =>
    -- partialSumAbs x 0 + invSucc 0 = 0 + 1 ≥ 1
    show (1 : Q') ≤ ExpNeg.partialSumAbs x 0 + Q'.invSucc 0
    have : ExpNeg.partialSumAbs x 0 = 0 := rfl
    rw [this]
    -- 1 ≤ 0 + invSucc 0 = 0 + 1
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))))
    show (1 : Q') ≤ Q'.invSucc 0
    decide
  | succ m =>
    -- partialSumAbs x (m+1) ≥ 1 (= partialSumAbs x 1, monotone), then add nonneg slack.
    have h1le : ExpNeg.partialSumAbs x 1 ≤ ExpNeg.partialSumAbs x (1 + m) :=
      ExpPos.partialSumAbs_mono x hx 1 m
    have heq1 : ExpNeg.partialSumAbs x 1 = 1 := by
      show ExpNeg.partialSumAbs x 0 + ExpNeg.termAbs x 0 = 1
      show (0 : Q') + 1 = 1
      exact Q'.zero_add' 1
    have hidx : (1 + m) = (m + 1) := Nat.add_comm 1 m
    rw [hidx] at h1le
    rw [heq1] at h1le
    -- 1 ≤ partialSumAbs x (m+1) ≤ partialSumAbs x (m+1) + invSucc (m+1)
    exact Q'.le_trans' _ _ _ h1le
      (Q'.add_le_self_of_nonneg _ (Q'.invSucc (m + 1)) (Q'.invSucc_nonneg (m + 1)))

/-- **The convexity tangent `1 + x ≤ e^x`** (re-exported), the ingredient the
sharper `e^{−2R}` floor would convexity-bound against.  See
`ExpPos.oneAddX_le_expPos` for the `geRat` form. -/
theorem oneAddX_le_expPos_companion (x : Q') (hx : (0 : Q') ≤ x) :
    ExpPos.geRat (ExpPos.expPos x hx) (1 + x) :=
  ExpPos.oneAddX_le_expPos x hx

end YMGap.Continuum.ProductFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ProductFloor.lossSum_nonneg
#print axioms YMGap.Continuum.ProductFloor.weierstrass_identity
#print axioms YMGap.Continuum.ProductFloor.weierstrass_step
#print axioms YMGap.Continuum.ProductFloor.prod_floor_weierstrass
#print axioms YMGap.Continuum.ProductFloor.prod_floor_of_sum_le
#print axioms YMGap.Continuum.ProductFloor.oneSubR_pos
#print axioms YMGap.Continuum.ProductFloor.prodOneSub_loss_eqv
#print axioms YMGap.Continuum.ProductFloor.sum_block_loss_to_productFloor
#print axioms YMGap.Continuum.ProductFloor.dyadic_block_loss
#print axioms YMGap.Continuum.ProductFloor.expPos_isPositive
#print axioms YMGap.Continuum.ProductFloor.oneAddX_le_expPos_companion
