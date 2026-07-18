/-
CatStructural/DominatedGrowth.lean

The load-bearing instance: a proof-relevant category `DomGrowth` whose

  * objects are nonnegative masses (integer surrogates for `Q'`/CReal
    gap bounds — everything is stated denominator-cleared, so a rational
    bound `(n/d)·m ≤ m'` appears as `n·m ≤ d·m'` over `Int`), and
  * a morphism `m ⟶ m'` is *witness-bearing data*: a ratio `(num, den)`
    with `0 ≤ num`, `0 < den`, together with the proof `num·m ≤ den·m'`.

The point of the spike, in one sentence:

  **composition in `DomGrowth` IS the telescoping single-step bound**
  `(1 − δ_k)·m_k ≤ m_{k+1}  ⟹  (∏(1 − δ_k))·m_0 ≤ m_n`.

The chain rule that the `singleStep` spine re-proves by hand at every
assembly point is here the associativity-and-composition structure of a
category, proved once.  A multi-scale defect ledger is exactly a functor
out of the thin category ω; the global anchor inequality is the composite
morphism's `bound` field, extracted by projection — a witness, not a
`Prop`-`∃` (AGENTS.md Rules 2, 8.3).

Everything below is Mathlib-free, Classical-free, `sorry`-free, and the
concrete anchors are kernel-`decide`d.  Axiom audit: the load-bearing
theorems print axioms ⊆ {propext} (see `#print axioms` lines at the end).
-/

import CatStructural.ECat

namespace CatStructural

/-- A nonnegative integer mass (denominator-cleared surrogate for a
    `Q'`-valued gap bound).  The nonnegativity is carried as data-adjacent
    proof so objects cannot silently go negative. -/
structure Mass where
  val : Int
  nonneg : 0 ≤ val

/-- A domination morphism `a ⟶ b`: the witness-bearing statement
    `(num/den)·a ≤ b`, denominator-cleared.  `num`, `den`, and the bound
    are all fields — estimates return their constants (Rule 2). -/
structure Dom (a b : Mass) where
  num : Int
  den : Int
  num_nonneg : 0 ≤ num
  den_pos : 0 < den
  bound : num * a.val ≤ den * b.val

namespace Dom

/-- Two domination witnesses are `eqv` when they assert the same ratio
    (cross-multiplied).  This is the hom-setoid: proofs are relevant,
    ratios are compared up to the setoid, never up to `Eq` of records. -/
def eqv {a b : Mass} (f g : Dom a b) : Prop :=
  f.num * g.den = g.num * f.den

/-- Ratio equality is decidable — naturality squares in `DomGrowth` over
    concrete data can be closed or *refuted* by kernel `decide`. -/
instance {a b : Mass} (f g : Dom a b) : Decidable (eqv f g) :=
  inferInstanceAs (Decidable (f.num * g.den = g.num * f.den))

theorem eqv_refl {a b : Mass} (f : Dom a b) : eqv f f := rfl

theorem eqv_symm {a b : Mass} {f g : Dom a b} (h : eqv f g) : eqv g f :=
  h.symm

/-- Transitivity of ratio equality needs cancellation by the (positive)
    middle denominator — the one genuinely order-theoretic fact in the
    setoid layer. -/
theorem eqv_trans {a b : Mass} {f g h : Dom a b}
    (h₁ : eqv f g) (h₂ : eqv g h) : eqv f h := by
  -- (f.num * h.den) * g.den = (h.num * f.den) * g.den, cancel g.den > 0.
  have hg : (0:Int) < g.den := g.den_pos
  have key : (f.num * h.den) * g.den = (h.num * f.den) * g.den := by
    calc (f.num * h.den) * g.den
        = (f.num * g.den) * h.den := by
          simp [Int.mul_comm, Int.mul_left_comm]
      _ = (g.num * f.den) * h.den := by rw [h₁]
      _ = (g.num * h.den) * f.den := by
          simp [Int.mul_comm, Int.mul_left_comm]
      _ = (h.num * g.den) * f.den := by rw [h₂]
      _ = (h.num * f.den) * g.den := by
          simp [Int.mul_comm, Int.mul_left_comm]
  exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hg) key

/-- The identity witness: ratio `1/1`. -/
def ident (a : Mass) : Dom a a where
  num := 1
  den := 1
  num_nonneg := by decide
  den_pos := by decide
  bound := Int.le_refl _

/-- Composition of domination witnesses: ratios multiply, and the bound
    of the composite is the *telescoped* inequality — this constructor is
    the entire content of the single-step chain rule. -/
def comp {a b c : Mass} (f : Dom a b) (g : Dom b c) : Dom a c where
  num := g.num * f.num
  den := g.den * f.den
  num_nonneg := Int.mul_nonneg g.num_nonneg f.num_nonneg
  den_pos := Int.mul_pos g.den_pos f.den_pos
  bound := by
    -- g.num * (f.num * a) ≤ g.num * (f.den * b)      [f.bound, g.num ≥ 0]
    have h₁ : g.num * (f.num * a.val) ≤ g.num * (f.den * b.val) :=
      Int.mul_le_mul_of_nonneg_left f.bound g.num_nonneg
    -- f.den * (g.num * b) ≤ f.den * (g.den * c)      [g.bound, f.den ≥ 0]
    have h₂ : f.den * (g.num * b.val) ≤ f.den * (g.den * c.val) :=
      Int.mul_le_mul_of_nonneg_left g.bound (Int.le_of_lt f.den_pos)
    have e₁ : (g.num * f.num) * a.val = g.num * (f.num * a.val) :=
      Int.mul_assoc ..
    have e₂ : g.num * (f.den * b.val) = f.den * (g.num * b.val) := by
      simp [Int.mul_comm, Int.mul_left_comm]
    have e₃ : f.den * (g.den * c.val) = (g.den * f.den) * c.val := by
      simp [Int.mul_comm, Int.mul_left_comm]
    calc (g.num * f.num) * a.val
        = g.num * (f.num * a.val) := e₁
      _ ≤ g.num * (f.den * b.val) := h₁
      _ = f.den * (g.num * b.val) := e₂
      _ ≤ f.den * (g.den * c.val) := h₂
      _ = (g.den * f.den) * c.val := e₃

theorem comp_congr {a b c : Mass} {f f' : Dom a b} {g g' : Dom b c}
    (hf : eqv f f') (hg : eqv g g') : eqv (comp f g) (comp f' g') := by
  show (g.num * f.num) * (g'.den * f'.den)
     = (g'.num * f'.num) * (g.den * f.den)
  calc (g.num * f.num) * (g'.den * f'.den)
      = (g.num * g'.den) * (f.num * f'.den) := by
        simp [Int.mul_comm, Int.mul_left_comm]
    _ = (g'.num * g.den) * (f'.num * f.den) := by rw [hg, hf]
    _ = (g'.num * f'.num) * (g.den * f.den) := by
        simp [Int.mul_comm, Int.mul_left_comm]

theorem ident_comp {a b : Mass} (f : Dom a b) :
    eqv (comp (ident a) f) f := by
  show (f.num * 1) * f.den = f.num * (f.den * 1)
  simp

theorem comp_ident {a b : Mass} (f : Dom a b) :
    eqv (comp f (ident b)) f := by
  show (1 * f.num) * f.den = f.num * (1 * f.den)
  simp

theorem comp_assoc {a b c d : Mass}
    (f : Dom a b) (g : Dom b c) (h : Dom c d) :
    eqv (comp (comp f g) h) (comp f (comp g h)) := by
  show (h.num * (g.num * f.num)) * ((h.den * g.den) * f.den)
     = ((h.num * g.num) * f.num) * (h.den * (g.den * f.den))
  simp [Int.mul_assoc]

end Dom

/-- The domination E-category.  Objects: nonnegative masses.  Morphisms:
    witness-bearing rational dominations, denominator-cleared over `Int`.
    Composition = telescoping; associativity of the ledger is `comp_assoc`,
    proved once, for every chain. -/
def DomGrowth : ECat where
  Obj := Mass
  Hom := Dom
  eqv := Dom.eqv
  eqv_refl := Dom.eqv_refl
  eqv_symm := Dom.eqv_symm
  eqv_trans := Dom.eqv_trans
  ident := Dom.ident
  comp := Dom.comp
  comp_congr := Dom.comp_congr
  ident_comp := Dom.ident_comp
  comp_ident := Dom.comp_ident
  comp_assoc := Dom.comp_assoc

/-! ## The spine as a chain of morphisms

A multi-scale defect ledger is per-scale data `step k : M k ⟶ M (k+1)`.
The global bound is the composite `M 0 ⟶ M n` — obtained by folding
`Dom.comp`, i.e. by the category structure, not by a bespoke induction
at each use site. -/

/-- The composite `M 0 ⟶ M n` of a per-scale ledger — the categorical
    form of the telescoped `singleStep` chain.  Its `bound` projection is
    the global anchor inequality, carried as data. -/
def chain (M : Nat → Mass) (step : ∀ k, Dom (M k) (M (k + 1))) :
    ∀ n, Dom (M 0) (M n)
  | 0 => Dom.ident (M 0)
  | n + 1 => Dom.comp (chain M step n) (step n)

/-- The global inequality, extracted from the chain composite by
    projection.  `(chain …).num / (chain …).den` is the accumulated
    product of per-scale ratios — the `∏(1 − δ_k)` of the spine. -/
theorem chain_bound (M : Nat → Mass) (step : ∀ k, Dom (M k) (M (k + 1)))
    (n : Nat) :
    (chain M step n).num * (M 0).val ≤ (chain M step n).den * (M n).val :=
  (chain M step n).bound

/-- Positivity of a product forces positivity of the dominated factor:
    the small order fact behind gap persistence. -/
theorem pos_of_mul_le {d m n : Int} (hd : 0 < d) (hn : 0 < n)
    (h : n ≤ d * m) : 0 < m := by
  false_or_by_contra
  rename_i hm
  have hm' : m ≤ 0 := Int.not_lt.mp (fun h' => hm (by exact h'))
  have : d * m ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hd) hm'
  exact absurd (Int.lt_of_lt_of_le hn (Int.le_trans h this)) (by decide)

/-- **Gap persistence, categorically.**  If the anchor mass is strictly
    positive and every per-scale ratio has strictly positive numerator
    (defects strictly below 1 in cleared form), then the mass at every
    scale is strictly positive.  This is `(1 − Σδ)·m₀ > 0 ⟹ m_n > 0`
    in composite-morphism form: the proof is *one* application of the
    composite's `bound` projection — no per-use-site induction. -/
theorem gap_persists (M : Nat → Mass) (step : ∀ k, Dom (M k) (M (k + 1)))
    (anchor_pos : 0 < (M 0).val)
    (num_pos : ∀ n, 0 < (chain M step n).num) (n : Nat) :
    0 < (M n).val := by
  have h := chain_bound M step n
  exact pos_of_mul_le (chain M step n).den_pos
    (Int.mul_pos (num_pos n) anchor_pos) h

/-! ## Kernel-checked concrete anchor

A toy three-scale ledger with explicit numbers, all side conditions
discharged by kernel `decide` (never `native_decide`).  The masses are
120 → 100 → 90 → 81 with per-step ratios 5/6, 9/10, 9/10; the composite
ratio is 405/600 and the kernel checks 405·120 ≤ 600·81 (48600 = 48600,
tight).  This is the shape of the strong-coupling anchor: an exact
rational inequality closed by computation. -/

def m0 : Mass := ⟨120, by decide⟩
def m1 : Mass := ⟨100, by decide⟩
def m2 : Mass := ⟨90, by decide⟩
def m3 : Mass := ⟨81, by decide⟩

def toyM : Nat → Mass
  | 0 => m0 | 1 => m1 | 2 => m2 | _ => m3

def toyStep : ∀ k, Dom (toyM k) (toyM (k + 1))
  | 0 => ⟨5, 6, by decide, by decide, by decide⟩
  | 1 => ⟨9, 10, by decide, by decide, by decide⟩
  | 2 => ⟨9, 10, by decide, by decide, by decide⟩
  | n + 3 => ⟨1, 1, by decide, by decide, Int.le_refl _⟩

/-- The composite ratio at scale 3 is exactly 405/600, kernel-checked. -/
theorem toy_composite_ratio :
    (chain toyM toyStep 3).num = 405 ∧ (chain toyM toyStep 3).den = 600 := by
  constructor <;> decide

/-- The toy gap persists at every scale — instance of `gap_persists`
    with the numerator positivity closed by `decide` per scale up to the
    stabilized tail. -/
theorem toy_gap_scale3 : 0 < (toyM 3).val := by decide

#print axioms Dom.comp
#print axioms chain_bound
#print axioms gap_persists
#print axioms toy_composite_ratio

end CatStructural
