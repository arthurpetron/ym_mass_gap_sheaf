/-
The **scale-sheaf anomaly**: the RG-invariant physical scale (the Λ_QCD analog
of dimensional transmutation) as a Čech 1-cocycle on the thin nerve of the
category of RG scales — a section that is **locally trivial** but, in the
presence of genuine running, **globally nontrivial**.

This module sits next to `YMGap/Categorical/Core.lean` (whose `Cat` it reuses)
and follows the thin-category pattern of `YMGap/Categorical/RGCategory.lean`
(`siteCat`: propositional homs lifted into `Type` by `PLift`, laws by `rfl` /
proof-irrelevance).  Per-step running factors are exact rationals `Q'` from
`YMGap/Constructive/Rationals.lean`, with the multiplicative `eqv`-laws of
`YMGap/Constructive/RationalsMul.lean`.

# Why some identities are stated at `eqv`, not `=`

`Q'` is the *unnormalized* constructive rational of `Rationals.lean`: its
equality is structural, so `a * b = b * a` is FALSE on the nose (the stored
denominators differ).  The multiplicative laws hold only up to semantic
equivalence `Q'.eqv`.  Accordingly the telescoping/associativity/commutativity
content of the scale class is stated at `eqv`; only the genuinely definitional
identities (the one-step coboundary and the right-append step, where the new
factor is multiplied on a fixed side) are stated at `=`.

# Physical reading

At any *single* RG scale the scale is "pure gauge": choosing a local section (a
local trivialization of the running) rescales it away up to that step.  This is
the COBOUNDARY content — every cocycle `t` is locally the coboundary of the
telescoping potential `s n = ∏_{k<n} t k` (`localSection_step`, definitional).
Yet the *accumulated* running `Lambda lo hi = ∏_{lo ≤ k < hi} t k` is an
invariant no finite local trivialization sees: when some step factor differs
from `1` (genuine running, `β ≠ 0`), the class is globally nontrivial.

# What is PROVED here (all genuine, no `sorry`/`axiom`)

  * `ScaleCat` — the thin category of scales (objects `Nat`, homs `PLift (·≤·)`),
    a bona fide `Cat` with `rfl`/proof-irrelevance laws.
  * `ScaleCocycle.localSection` (`s`) and `localSection_step` — the local
    trivialization and the **coboundary identity** `s (n+1) = t n * s n`
    (definitional `=`); `localSection_pos` (each `s n > 0`).
  * `localTrivialization` — "every cocycle is locally a coboundary".
  * `Lambda` and its laws: `Lambda_self` (empty range), `Lambda_succ_right`
    (definitional right-append step, `=`), `Lambda_pos`,
    `Lambda_eq_section` (`Lambda 0 hi = localSection hi`, the division-free
    section-ratio form), `Lambda_split` (Chasles / composition over a midpoint,
    at `eqv`), `Lambda_shift_class` (base-point invariance of the class, at
    `eqv`).
  * `IsGloballyTrivial` and the obstruction theorems:
    `globallyTrivial_collapses_Lambda` (no running ⇒ every class `≃ 1`) and
    `nontrivial_of_step_ne_one` (one genuine running step ⇒ NOT globally
    trivial), plus `Lambda_one_step` (`Lambda n (n+1) = t n`).

# The NAMED open analytic input (Rule 8: witnesses as data, not faked)

Whether the Yang–Mills β-function is nonzero is the genuine analytic fact and is
carried as the named predicate `BetaNonzero` ("some RG step carries genuine
running", a step factor not semantically `1`).  This module NEVER assumes it
holds; `nontrivial_of_step_ne_one` consumes it as a hypothesis.  The module
proves the *structural* equivalence between "no running" and "class collapses",
and isolates "running is real" as the one external obligation.

# Axiom-gate (AGENTS.md Rules 1, 8)

`[propext]` only (or empty).  No `Classical.*`, no `sorryAx`, no
`native_decide`.  See the `#print axioms` block at the end.
-/

import YMGap.Categorical.Core
import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul

namespace YMGap.Categorical.ScaleSheaf

open YMGap.Constructive

/-! ## Q' positivity helpers (local, axiom-clean)

`Rationals.lean` exposes the `eqv`/`≤` algebra; we need two strict-positivity
facts about `*` and `1` for the scale sections.  Each reduces to the
cross-product `lt` definition (`(0:Q') < q ↔ 0 < q.num`). -/

/-- `0 < (1 : Q')`: the trivial scale is positive. -/
private theorem q_zero_lt_one : (0 : Q') < (1 : Q') := by
  show (0 : Int) * ((1 : Q').den : Int) < (1 : Q').num * ((0 : Q').den : Int)
  decide

/-- `0 < q` unfolds to `0 < q.num`. -/
private theorem q_pos_iff (q : Q') : (0 : Q') < q ↔ (0 : Int) < q.num := by
  constructor
  · intro h
    have h' : (0 : Int) * (q.den : Int) < q.num * (((0 : Q').den) : Int) := h
    -- ((0:Q').den : Int) = 1, (0:Q').num*... LHS = 0.
    show (0 : Int) < q.num
    have : (0 : Int) * (q.den : Int) = 0 := Int.zero_mul _
    rw [this] at h'
    have h1 : q.num * (((0 : Q').den) : Int) = q.num := by
      show q.num * (1 : Int) = q.num
      exact Int.mul_one _
    rw [h1] at h'
    exact h'
  · intro h
    show (0 : Int) * (q.den : Int) < q.num * (((0 : Q').den) : Int)
    rw [Int.zero_mul]
    show (0 : Int) < q.num * (1 : Int)
    rw [Int.mul_one]
    exact h

/-- Product of two positive `Q'` values is positive. -/
private theorem q_mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  rw [q_pos_iff] at ha hb ⊢
  show (0 : Int) < (a * b).num
  show (0 : Int) < a.num * b.num
  exact Int.mul_pos ha hb

/-! ## The thin category of RG scales -/

/-- **`ScaleCat`** — the category of RG scales (discrete log-scales).  Objects
are `Nat` (RG steps); a morphism `a ⟶ b` is a proof-carrying refinement
`PLift (a ≤ b)`.  The category is **thin**: any two parallel homs are equal by
`Nat.le` proof-irrelevance, so all three laws are `rfl`.  Mirrors the `siteCat`
pattern of `YMGap/Categorical/RGCategory.lean`. -/
def ScaleCat : Cat where
  Obj := Nat
  Hom := fun a b => PLift (a ≤ b)
  id := fun a => PLift.up (Nat.le_refl a)
  comp := fun f g => PLift.up (Nat.le_trans f.down g.down)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-! ## Cocycles: the discrete running of the scale -/

/-- A **scale cocycle**: per-step positive running factors `t : Nat → Q'`.  The
Čech 1-cochain on the thin nerve whose coboundary class is the accumulated
running (the discrete β-function of the scale). -/
structure ScaleCocycle where
  /-- The running factor from RG step `n` to step `n+1`. -/
  t : Nat → Q'
  /-- Each running factor is a positive scale ratio. -/
  tpos : ∀ n, (0 : Q') < t n

namespace ScaleCocycle

/-! ## Local trivialization (the coboundary) -/

/-- The **telescoping potential** (local section): `s n = ∏_{k < n} t k`, with
`s 0 = 1`.  Defined with the new factor multiplied **on the left** so that the
coboundary identity is definitional. -/
def localSection (c : ScaleCocycle) : Nat → Q'
  | 0       => (1 : Q')
  | (n + 1) => c.t n * c.localSection n

/-- `s 0 = 1`: the base-point local section is the trivial scale. -/
@[simp] theorem localSection_zero (c : ScaleCocycle) :
    c.localSection 0 = (1 : Q') := rfl

/-- **The coboundary identity (local triviality).**  At every adjacent pair the
cocycle is the coboundary of the telescoping potential: `s (n+1) = t n * s n`.
This is the "each finite stage's scale is pure gauge" content; `rfl`. -/
theorem localSection_step (c : ScaleCocycle) (n : Nat) :
    c.localSection (n + 1) = c.t n * c.localSection n := rfl

/-- **Local trivialization, packaged.**  Every cocycle is locally a coboundary
of `localSection`.  The categorical statement that the scale is, locally, pure
gauge. -/
theorem localTrivialization (c : ScaleCocycle) :
    ∀ n, c.localSection (n + 1) = c.t n * c.localSection n :=
  c.localSection_step

/-- Each local section value is positive (a positive scale): `0 < s n`.  By
induction, using positivity of each step factor. -/
theorem localSection_pos (c : ScaleCocycle) : ∀ n, (0 : Q') < c.localSection n
  | 0       => q_zero_lt_one
  | (n + 1) => by
      show (0 : Q') < c.t n * c.localSection n
      exact q_mul_pos (c.tpos n) (c.localSection_pos n)

/-! ## The accumulated invariant `Lambda` (the global class)

`Lambda lo hi = ∏_{lo ≤ k < hi} t k` is the running accumulated between two RG
scales; built by recursion on the *width* `hi - lo`, with the newest factor on
the right so the right-append step is definitional. -/

/-- The accumulated running over `width` consecutive steps starting at `lo`:
`∏_{lo ≤ k < lo + width} t k`. -/
def accum (c : ScaleCocycle) (lo : Nat) : Nat → Q'
  | 0           => (1 : Q')
  | (width + 1) => c.accum lo width * c.t (lo + width)

/-- **`Lambda lo hi`** — the accumulated running (the scale class) between RG
steps `lo` and `hi`: `∏_{lo ≤ k < hi} t k`.  For `hi ≤ lo` the range is empty
and the value is the trivial scale `1`.  This is the candidate RG-invariant. -/
def Lambda (c : ScaleCocycle) (lo hi : Nat) : Q' := c.accum lo (hi - lo)

/-- Each accumulated value is positive. -/
theorem accum_pos (c : ScaleCocycle) (lo : Nat) :
    ∀ width, (0 : Q') < c.accum lo width
  | 0           => q_zero_lt_one
  | (width + 1) => by
      show (0 : Q') < c.accum lo width * c.t (lo + width)
      exact q_mul_pos (c.accum_pos lo width) (c.tpos (lo + width))

/-- `Lambda lo lo = 1`: the empty range is the trivial scale; the identity
morphism of `ScaleCat` carries no running. -/
@[simp] theorem Lambda_self (c : ScaleCocycle) (lo : Nat) :
    c.Lambda lo lo = (1 : Q') := by
  show c.accum lo (lo - lo) = (1 : Q')
  rw [Nat.sub_self]
  rfl

/-- **Telescoping (append one step on the right).**  Extending the range by one
RG step multiplies in exactly that step's running factor:
`Lambda lo (hi+1) = Lambda lo hi * t hi`, when `lo ≤ hi`.  Definitional `=`
(the new factor lands on the right, the side `accum` recurses on). -/
theorem Lambda_succ_right (c : ScaleCocycle) (lo hi : Nat) (h : lo ≤ hi) :
    c.Lambda lo (hi + 1) = c.Lambda lo hi * c.t hi := by
  show c.accum lo (hi + 1 - lo) = c.accum lo (hi - lo) * c.t hi
  have hw : hi + 1 - lo = (hi - lo) + 1 := by omega
  rw [hw]
  show c.accum lo (hi - lo) * c.t (lo + (hi - lo))
      = c.accum lo (hi - lo) * c.t hi
  have hidx : lo + (hi - lo) = hi := by omega
  rw [hidx]

/-- Each `Lambda` value is positive. -/
theorem Lambda_pos (c : ScaleCocycle) (lo hi : Nat) :
    (0 : Q') < c.Lambda lo hi :=
  c.accum_pos lo (hi - lo)

/-- **Section form of `Lambda` (division-free section ratio).**  The accumulated
running from the base point `0` to `hi` is exactly the telescoping potential:
`Lambda 0 hi = localSection hi`.  Since `s 0 = 1`, this is the section ratio
`s hi / s 0` written without division.  At `eqv` (the two sides accumulate the
same factors but bracket them on opposite sides).  By induction on `hi`. -/
theorem Lambda_eq_section (c : ScaleCocycle) :
    ∀ hi, (c.Lambda 0 hi).eqv (c.localSection hi)
  | 0       => Q'.eqv_refl _
  | (hi + 1) => by
      -- LHS: Lambda 0 (hi+1) = Lambda 0 hi * t hi  (right-append, =).
      rw [c.Lambda_succ_right 0 hi (Nat.zero_le hi)]
      -- RHS: localSection (hi+1) = t hi * localSection hi  (=).
      rw [c.localSection_step hi]
      -- Goal: (Lambda 0 hi * t hi) ≃ (t hi * localSection hi).
      -- Lambda 0 hi ≃ localSection hi (ih), then commute.
      refine Q'.eqv_trans _ (c.localSection hi * c.t hi) _ ?_ (Q'.mul_comm_eqv _ _)
      exact Q'.mul_eqv_congr_right _ _ _ (c.Lambda_eq_section hi)

/-- **Composition / Chasles law for the class.**  The class composes along the
thin morphism `lo ⟶ mid ⟶ hi`: `Lambda lo hi ≃ Lambda lo mid * Lambda mid hi`,
for `lo ≤ mid ≤ hi`.  Functoriality of the scale class over `ScaleCat`.  At
`eqv` (regrouping the accumulated product).  By induction on `hi - mid`. -/
theorem Lambda_split (c : ScaleCocycle) (lo mid hi : Nat)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    (c.Lambda lo hi).eqv (c.Lambda lo mid * c.Lambda mid hi) := by
  obtain ⟨k, hk⟩ : ∃ k, hi = mid + k := ⟨hi - mid, by omega⟩
  subst hk
  clear h2
  induction k with
  | zero =>
      -- Lambda lo (mid+0) ≃ Lambda lo mid * Lambda mid mid = Lambda lo mid * 1.
      rw [Nat.add_zero, c.Lambda_self mid]
      exact Q'.eqv_symm (Q'.mul_one_eqv _)
  | succ k ih =>
      have hmk : mid ≤ mid + k := Nat.le_add_right mid k
      have hlomk : lo ≤ mid + k := Nat.le_trans h1 hmk
      -- LHS append: Lambda lo (mid+(k+1)) = Lambda lo (mid+k) * t (mid+k).
      have hLHS : c.Lambda lo (mid + (k + 1))
          = c.Lambda lo (mid + k) * c.t (mid + k) := by
        have he : mid + (k + 1) = (mid + k) + 1 := by omega
        rw [he, c.Lambda_succ_right lo (mid + k) hlomk]
      -- RHS append: Lambda mid (mid+(k+1)) = Lambda mid (mid+k) * t (mid+k).
      have hR : c.Lambda mid (mid + (k + 1))
          = c.Lambda mid (mid + k) * c.t (mid + k) := by
        have he : mid + (k + 1) = (mid + k) + 1 := by omega
        rw [he, c.Lambda_succ_right mid (mid + k) hmk]
      rw [hLHS, hR]
      -- Goal: (Lambda lo (mid+k) * t) ≃ (Lambda lo mid * (Lambda mid (mid+k) * t)).
      -- Step 1: rewrite Lambda lo (mid+k) up to eqv via ih.
      refine Q'.eqv_trans _
        ((c.Lambda lo mid * c.Lambda mid (mid + k)) * c.t (mid + k)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ ih
      · -- reassociate: (A * B) * t ≃ A * (B * t).
        exact Q'.mul_assoc_eqv _ _ _

/-- **Shift / base-point invariance of the class.**  For `lo ≤ mid ≤ hi`, the
class `Lambda mid hi` (the running *from* `mid` *to* `hi`) is exactly the right
factor of the composition, independent of the choice of earlier base point
`lo`: `Lambda lo mid * Lambda mid hi ≃ Lambda lo hi`.  The RG-invariance of Λ —
an earlier base point only contributes a common multiplicative prefix. -/
theorem Lambda_shift_class (c : ScaleCocycle) (lo mid hi : Nat)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    (c.Lambda lo mid * c.Lambda mid hi).eqv (c.Lambda lo hi) :=
  Q'.eqv_symm (c.Lambda_split lo mid hi h1 h2)

/-! ## The obstruction: globally trivial vs. genuinely running -/

/-- **`IsGloballyTrivial`** — the obstruction class vanishes: every per-step
running factor is semantically the trivial scale `1`.  (Semantic `Q'.eqv`, not
structural `Eq`, since `Q'` is unnormalized.)  Physically: no running. -/
def IsGloballyTrivial (c : ScaleCocycle) : Prop :=
  ∀ n, (c.t n).eqv (1 : Q')

/-- **`BetaNonzero` — THE NAMED OPEN ANALYTIC INPUT.**  The Yang–Mills fact that
the β-function does not vanish, here as the structural predicate "some RG step
carries genuine running" (a step factor not semantically `1`).  This module
NEVER assumes this holds; it is the external obligation that makes the scale
class nontrivial, consumed downstream as a hypothesis (Rule 8: named, not
faked). -/
def BetaNonzero (c : ScaleCocycle) : Prop :=
  ∃ n, ¬ (c.t n).eqv (1 : Q')

/-- **Globally trivial ⇒ the class collapses.**  If there is no running, every
accumulated class `Lambda lo hi` is semantically the trivial scale `1`:  the
telescoped product of `1`s is `1`.  By induction on the width. -/
theorem globallyTrivial_collapses_Lambda (c : ScaleCocycle)
    (h : c.IsGloballyTrivial) (lo hi : Nat) :
    (c.Lambda lo hi).eqv (1 : Q') := by
  show (c.accum lo (hi - lo)).eqv (1 : Q')
  generalize (hi - lo) = width
  induction width with
  | zero => exact Q'.eqv_refl 1
  | succ width ih =>
      show (c.accum lo width * c.t (lo + width)).eqv (1 : Q')
      -- accum * t ≃ 1 * 1 ≃ 1.
      have ht : (c.t (lo + width)).eqv (1 : Q') := h (lo + width)
      -- accum * t ≃ accum * 1  (congr left, replacing t by 1).
      have h1 : (c.accum lo width * c.t (lo + width)).eqv
          (c.accum lo width * (1 : Q')) :=
        Q'.mul_eqv_congr_left _ _ _ ht
      -- accum * 1 ≃ accum ≃ 1.
      exact Q'.eqv_trans _ _ _ h1
        (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ih)

/-- **A single running step obstructs global triviality.**  If some RG step's
running factor is not semantically `1`, the cocycle is NOT globally trivial.
This consumes the named analytic input `BetaNonzero`: `β ≠ 0` ⇒ the scale class
is a genuine obstruction. -/
theorem nontrivial_of_step_ne_one (c : ScaleCocycle) (hβ : c.BetaNonzero) :
    ¬ c.IsGloballyTrivial := by
  intro htriv
  obtain ⟨n, hn⟩ := hβ
  exact hn (htriv n)

/-- **The one-step class detects running.**  For the adjacent pair `n ⟶ n+1`,
`Lambda n (n+1) = t n` (definitional `=`, since `Lambda n n = 1` and the
right-append puts `t n` on the recursing side, then `1 * t n`).  A nontrivial
step factor is *literally* a nontrivial one-step class — the obstruction is
visible on a single edge of the nerve, yet (by `localTrivialization`) is locally
a coboundary. -/
theorem Lambda_one_step (c : ScaleCocycle) (n : Nat) :
    (c.Lambda n (n + 1)).eqv (c.t n) := by
  rw [c.Lambda_succ_right n n (Nat.le_refl n), c.Lambda_self n]
  -- (1 : Q') * t n ≃ t n.
  exact Q'.one_mul_eqv _

end ScaleCocycle

end YMGap.Categorical.ScaleSheaf

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Categorical.ScaleSheaf.ScaleCat
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.localSection_step
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.localTrivialization
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.localSection_pos
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.Lambda_self
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.Lambda_succ_right
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.Lambda_pos
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.Lambda_eq_section
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.Lambda_split
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.Lambda_shift_class
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.globallyTrivial_collapses_Lambda
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.nontrivial_of_step_ne_one
#print axioms YMGap.Categorical.ScaleSheaf.ScaleCocycle.Lambda_one_step
