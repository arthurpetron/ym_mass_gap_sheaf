/-
# Codynamic core — reusable error/defect + trajectory tools (Lean transpose)

A faithful, axiom-clean Lean-core transposition of the machine-verified
Agda development `Codynamic.*` (Metric.agda, Trajectory.agda, and the
minimal Signature/Term/Rewrite/Completion scaffolding they rest on).
The point is *reusable infrastructure*: an abstract ordered cost
structure with joins (`Costs`), a metric/interpretation layer
(`MetricVal`), a monotone-modulus Lipschitz control (`Lipschitz`), the
compositional defect law (`derivBound`/`deriv_d`, `eqBound`/`eqBound_append`),
the reflection-unit defect (`unit_defect`), and — the crown jewel — the
n-step discrete-Grönwall trajectory bound (`nBound`, `nstep_d`).

Design notes (following the Agda register + `lean/AGENTS.md`):

* `Costs` carries its arithmetic as EVIDENCE (no ambient ring). The
  intended instance is the repo's constructive rationals `Q'`; supplied
  as `qCosts` below, reusing the existing `Q'` order/add/max lemmas — no
  arithmetic is rebuilt here.
* The Agda `Costs` used propositional `≡` for `+#-assoc`/`+#-identityˡ`.
  On `Q'` addition is UNNORMALIZED, so those laws hold only up to the
  semantic setoid `eqv`, not structural `Eq`.  Following AGENTS.md
  Rule 8 ("`Q'` with `eqv` already IS a setoid, reason in the setoid"),
  `Costs` carries `eqv` and phrases the equational laws (and the
  conclusion of `eqBound_append`) w.r.t. it.  All order reasoning stays
  in `le`.
* Lipschitz control is a MONOTONE SCALING MAP per rule symbol
  (`scale : Fin Ops → Q → Q`), subsuming the multiplicative `L(ω)·(−)`
  of the paper — nonlinear moduli included, no multiplication needed.
* Witnesses are `Type`-level data (Rule 8): `All`, `Term`, derivations
  (`Star`), `Step`/`Traj` are `Type`-valued inductives; only the order
  and equivalence relations live in `Prop`.  The bounds themselves
  (`nBound` values, `derivBound` values) are honest `Q'` data.

`#print axioms` on the load-bearing declarations is ⊆ {propext, Quot.sound}
(in fact empty for most).  See `CodynamicCoreTest.lean` for the
non-vacuous computed tests (a two-point carrier + toy doubling scale).
-/
import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul

namespace YMGap.CodynamicCore

open YMGap.Constructive

universe u v

/-! ## Section 1 — typed signatures (transpose of `Signature.agda`) -/

/-! Colors: the finite set of state colors, presented as `Fin c`. -/
abbrev Color (c : Nat) : Type := Fin c

/-- A profile `(w ; γ)`: input word and result color. -/
structure Profile (c : Nat) where
  dom : List (Color c)
  cod : Color c

/-- A typed signature: finitely many rule symbols, each with a profile. -/
structure Signature (c : Nat) where
  Ops : Nat
  profile : Fin Ops → Profile c

/-- A witnessed-finitely presented typed set (the carrier `D`). -/
structure TypedSet (c : Nat) where
  size : Nat
  color : Fin size → Color c

/-! ## Section 2 — the abstract cost structure (transpose of `Costs`)

Every law is an evidence field; no ambient arithmetic is assumed.  The
join `max` gives the pointwise-tuple distance its least-upper-bound
structure. -/

structure Costs where
  Q : Type
  zero : Q
  add : Q → Q → Q
  max : Q → Q → Q
  le : Q → Q → Prop
  eqv : Q → Q → Prop
  le_refl : ∀ {x}, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  add_mono : ∀ {a b x y}, le a b → le x y → le (add a x) (add b y)
  eqv_refl : ∀ {x}, eqv x x
  eqv_symm : ∀ {x y}, eqv x y → eqv y x
  eqv_trans : ∀ {x y z}, eqv x y → eqv y z → eqv x z
  /-- Right congruence of `add` w.r.t. the setoid equality (all
      `eqBound_append` needs). -/
  add_congr_right : ∀ {x y y'}, eqv y y' → eqv (add x y) (add x y')
  add_assoc : ∀ x y z, eqv (add (add x y) z) (add x (add y z))
  zero_add : ∀ x, eqv (add zero x) x
  le_max_left : ∀ {x y}, le x (max x y)
  le_max_right : ∀ {x y}, le y (max x y)
  max_lub : ∀ {x y z}, le x z → le y z → le (max x y) z

/-! ### The intended instance: the repo's constructive rationals `Q'`.

Reuses the existing `Q'` order/add/max/eqv lemmas (Rationals.lean,
RationalsMul.lean).  The three `max'` lemmas are reproved locally (a few
lines each on `Int`) to avoid pulling the heavy `RegularCReal` import. -/

private theorem q_le_of_not_le {p q : Q'} (h : ¬ (p ≤ q)) : q ≤ p := by
  show q.num * (p.den : Int) ≤ p.num * (q.den : Int)
  have h' : ¬ (p.num * (q.den : Int) ≤ q.num * (p.den : Int)) := h
  exact Int.le_of_lt (Int.not_le.mp h')

private theorem q_le_max_left (p q : Q') : p ≤ Q'.max' p q := by
  unfold Q'.max'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Q'.le_refl' p

private theorem q_le_max_right (p q : Q') : q ≤ Q'.max' p q := by
  unfold Q'.max'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact Q'.le_refl' q
  · rw [if_neg h]; exact q_le_of_not_le h

private theorem q_max_lub {p q r : Q'} (hp : p ≤ r) (hq : q ≤ r) :
    Q'.max' p q ≤ r := by
  unfold Q'.max'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact hq
  · rw [if_neg h]; exact hp

/-- `Costs` instantiated with the constructive rationals `Q'`.  Reducible so
that `qCosts.Q ≡ Q'`, `qCosts.le ≡ Q'.le`, etc. drive instance resolution
(`OfNat`, `Decidable`) at use sites. -/
abbrev qCosts : Costs where
  Q := Q'
  zero := (0 : Q')
  add := (· + ·)
  max := Q'.max'
  le := (· ≤ ·)
  eqv := Q'.eqv
  le_refl := Q'.le_refl' _
  le_trans := fun h1 h2 => Q'.le_trans' _ _ _ h1 h2
  add_mono := fun {a b x y} hab hxy =>
    Q'.le_trans' _ _ _ (Q'.add_le_add_right a b x hab) (Q'.add_le_add_left b x y hxy)
  eqv_refl := Q'.eqv_refl _
  eqv_symm := Q'.eqv_symm
  eqv_trans := fun h1 h2 => Q'.eqv_trans _ _ _ h1 h2
  add_congr_right := fun {x y y'} h => Q'.add_eqv_congr_left x y y' h
  add_assoc := fun x y z => Q'.add_assoc_eqv x y z
  zero_add := fun x => by
    show Q'.eqv ((0 : Q') + x) x
    rw [Q'.zero_add']; exact Q'.eqv_refl x
  le_max_left := fun {x y} => q_le_max_left x y
  le_max_right := fun {x y} => q_le_max_right x y
  max_lub := fun {x y z} hx hy => q_max_lub hx hy

/-! ## Section 3 — a dependent `All` container (Type-valued, Rule 8) -/

inductive All {A : Type u} (P : A → Type v) : List A → Type (max u v) where
  | nil : All P []
  | cons : {x : A} → {xs : List A} → P x → All P xs → All P (x :: xs)

/-! ## Section 4 — the metric/interpretation layer (transpose of `MetricVal`)

Interpretation data `⟦ω⟧`, the recorded points, and the color-indexed
distance, with the four metric-resolution laws valued in the abstract
costs. -/

structure MetricVal {c : Nat} (Sg : Signature c) (D : TypedSet c) (C : Costs) where
  Val : Color c → Type
  point : (i : Fin D.size) → Val (D.color i)
  interp : (ω : Fin Sg.Ops) → All Val (Sg.profile ω).dom → Val (Sg.profile ω).cod
  d : ∀ {γ}, Val γ → Val γ → C.Q
  d_refl : ∀ {γ} (x : Val γ), C.le (d x x) C.zero
  d_sym : ∀ {γ} (x y : Val γ), C.le (d x y) (d y x)
  triangle : ∀ {γ} (x y z : Val γ), C.le (d x z) (C.add (d x y) (d y z))
  nonneg : ∀ {γ} (x y : Val γ), C.le C.zero (d x y)

variable {c : Nat} {Sg : Signature c} {D : TypedSet c} {C : Costs}

/-- Pointwise-join distance on tuples. -/
def dAll (M : MetricVal Sg D C) :
    {w : List (Color c)} → All M.Val w → All M.Val w → C.Q
  | [], .nil, .nil => C.zero
  | _ :: _, .cons x xs, .cons y ys => C.max (M.d x y) (dAll M xs ys)

/-- The tuple distance of a tuple to itself is `≤ 0`. -/
theorem dAll_refl (M : MetricVal Sg D C) :
    {w : List (Color c)} → (xs : All M.Val w) → C.le (dAll M xs xs) C.zero
  | [], .nil => C.le_refl
  | _ :: _, .cons x xs => C.max_lub (M.d_refl x) (dAll_refl M xs)

/-- The tuple distance is nonnegative. -/
theorem dAll_nonneg (M : MetricVal Sg D C) :
    {w : List (Color c)} → (xs ys : All M.Val w) → C.le C.zero (dAll M xs ys)
  | [], .nil, .nil => C.le_refl
  | _ :: _, .cons x xs, .cons y ys =>
      C.le_trans (M.nonneg x y) C.le_max_left

/-! ### Finite joins over an enumerated family (`maxOver`, `εX` building block) -/

/-- Finite join over an enumerated family `Fin n → Q`. -/
def maxOver {C : Costs} : (n : Nat) → (Fin n → C.Q) → C.Q
  | 0, _ => C.zero
  | n + 1, f => C.max (f ⟨0, Nat.succ_pos n⟩) (maxOver n (fun k => f k.succ))

/-- Each member of the family is below the finite join. -/
theorem maxOver_ub {C : Costs} :
    (n : Nat) → (f : Fin n → C.Q) → (k : Fin n) → C.le (f k) (maxOver n f)
  | 0, _, k => k.elim0
  | n + 1, f, ⟨kv, hk⟩ => by
    cases kv with
    | zero => exact C.le_max_left
    | succ j =>
      have hj : j < n := Nat.lt_of_succ_lt_succ hk
      exact C.le_trans (maxOver_ub n (fun i => f i.succ) ⟨j, hj⟩) C.le_max_right

/-- The finite join of a nonnegative family is nonnegative. -/
theorem maxOver_nonneg {C : Costs} :
    (n : Nat) → (f : Fin n → C.Q) → (∀ k, C.le C.zero (f k)) → C.le C.zero (maxOver n f)
  | 0, _, _ => C.le_refl
  | n + 1, f, h => C.le_trans (h ⟨0, Nat.succ_pos n⟩) C.le_max_left

/-! ## Section 5a — Lipschitz control (monotone modulus, transpose of `Lipschitz`) -/

structure Lipschitz (M : MetricVal Sg D C) where
  scale : Fin Sg.Ops → C.Q → C.Q
  scale_mono : ∀ (ω : Fin Sg.Ops) {a b : C.Q}, C.le a b → C.le (scale ω a) (scale ω b)
  scale_zero : ∀ (ω : Fin Sg.Ops), C.le C.zero (scale ω C.zero)
  lip : ∀ (ω : Fin Sg.Ops) (xs ys : All M.Val (Sg.profile ω).dom),
        C.le (M.d (M.interp ω xs) (M.interp ω ys)) (scale ω (dAll M xs ys))

/-! ## Section 5b — trajectories and the n-step Grönwall bound
(transpose of `Trajectory.agda`) -/

/-- Positions: the argument slot through which the running state flows. -/
inductive Pos {c : Nat} : List (Color c) → Color c → Type where
  | phere : {γ : Color c} → {w : List (Color c)} → Pos (γ :: w) γ
  | pthere : {γ γ' : Color c} → {w : List (Color c)} → Pos w γ → Pos (γ' :: w) γ

/-- Replace the designated slot of a tuple. -/
def fill (M : MetricVal Sg D C) :
    {w : List (Color c)} → {γ : Color c} → All M.Val w → Pos w γ → M.Val γ → All M.Val w
  | _, _, .cons _ xs, .phere, v => .cons v xs
  | _, _, .cons x xs, .pthere p, v => .cons x (fill M xs p v)

/-- Changing only the designated slot moves the tuple distance by at
most the slot distance. -/
theorem dAll_fill (M : MetricVal Sg D C) :
    {w : List (Color c)} → {γ : Color c} → (xs : All M.Val w) → (p : Pos w γ) →
    (v y : M.Val γ) → C.le (dAll M (fill M xs p v) (fill M xs p y)) (M.d v y)
  | _, _, .cons _ xs, .phere, v, y =>
      C.max_lub C.le_refl (C.le_trans (dAll_refl M xs) (M.nonneg v y))
  | _, _, .cons x xs, .pthere p, v, y =>
      C.max_lub (C.le_trans (M.d_refl x) (M.nonneg v y)) (dAll_fill M xs p v y)

/-- One evolution step: a rule, the flow slot, and recorded side data. -/
structure Step (M : MetricVal Sg D C) (γ : Color c) where
  rule : Fin Sg.Ops
  pos : Pos (Sg.profile rule).dom γ
  sides : All M.Val (Sg.profile rule).dom

/-- The output color of a step. -/
def Step.outc {M : MetricVal Sg D C} {γ : Color c} (s : Step M γ) : Color c :=
  (Sg.profile s.rule).cod

/-- The computed action of a step on the running state. -/
def stepF (M : MetricVal Sg D C) {γ : Color c} (s : Step M γ) (v : M.Val γ) :
    M.Val s.outc :=
  M.interp s.rule (fill M s.sides s.pos v)

/-- A step together with its recorded output value (the y-chain). -/
structure Linked (M : MetricVal Sg D C) (γ : Color c) where
  step : Step M γ
  recVal : M.Val step.outc

/-- A trajectory: a chain of linked steps with definitional color matching. -/
inductive Traj (M : MetricVal Sg D C) : Color c → Color c → Type where
  | tnil : {γ : Color c} → Traj M γ γ
  | tcons : {γ γ'' : Color c} → (sy : Linked M γ) →
            Traj M sy.step.outc γ'' → Traj M γ γ''

/-- The computed run of a trajectory from an initial value. -/
def run (M : MetricVal Sg D C) :
    {γ γ' : Color c} → M.Val γ → Traj M γ γ' → M.Val γ'
  | _, _, v, .tnil => v
  | _, _, v, .tcons sy tr => run M (stepF M sy.step v) tr

/-- The recorded endpoint of a trajectory (following the y-chain). -/
def endRec (M : MetricVal Sg D C) :
    {γ γ' : Color c} → M.Val γ → Traj M γ γ' → M.Val γ'
  | _, _, y, .tnil => y
  | _, _, y, .tcons sy tr => endRec M sy.recVal tr

/-- The n-step bound as a LEFT FOLD: scale the running certificate by the
step's rule modulus, then add the step's defect against the recorded
chain.  Unrolled classically this is `(∏ L)·b + Σ (∏ downstream L)·η`. -/
def nBound (M : MetricVal Sg D C) (L : Lipschitz M) :
    {γ γ' : Color c} → C.Q → M.Val γ → Traj M γ γ' → C.Q
  | _, _, b, _, .tnil => b
  | _, _, b, y, .tcons sy tr =>
      nBound M L (C.add (L.scale sy.step.rule b) (M.d (stepF M sy.step y) sy.recVal)) sy.recVal tr

/-- The n-step bound is monotone in the initial certificate. -/
theorem nBound_mono (M : MetricVal Sg D C) (L : Lipschitz M) :
    {γ γ' : Color c} → {b b' : C.Q} → (y : M.Val γ) → (tr : Traj M γ γ') →
    C.le b b' → C.le (nBound M L b y tr) (nBound M L b' y tr)
  | _, _, _, _, _, .tnil, h => h
  | _, _, _, _, y, .tcons sy tr, h =>
      nBound_mono M L sy.recVal tr (C.add_mono (L.scale_mono sy.step.rule h) C.le_refl)

/-- **The n-step transition theorem** (discrete Grönwall, transpose of
`nstep-d`).  A certificate `d v y ≤ b` for the initial discrepancy is
transported along the trajectory to a certificate for the final
discrepancy, with bound computed by the fold.  Each step is
`prop:error-composition`'s recursion `e' ≤ scale(e) + η`, discharged by
triangle, `lip`, `dAll_fill`, and monotonicity. -/
theorem nstep_d (M : MetricVal Sg D C) (L : Lipschitz M) :
    {γ γ' : Color c} → (v y : M.Val γ) → (b : C.Q) → C.le (M.d v y) b →
    (tr : Traj M γ γ') → C.le (M.d (run M v tr) (endRec M y tr)) (nBound M L b y tr)
  | _, _, _, _, _, hb, .tnil => hb
  | _, _, v, y, b, hb, .tcons sy tr =>
      nstep_d M L (stepF M sy.step v) sy.recVal
        (C.add (L.scale sy.step.rule b) (M.d (stepF M sy.step y) sy.recVal))
        (C.le_trans (M.triangle (stepF M sy.step v) (stepF M sy.step y) sy.recVal)
          (C.add_mono
            (C.le_trans
              (L.lip sy.step.rule (fill M sy.step.sides sy.step.pos v)
                (fill M sy.step.sides sy.step.pos y))
              (L.scale_mono sy.step.rule
                (C.le_trans (dAll_fill M sy.step.sides sy.step.pos v y) hb)))
            C.le_refl))
        tr


/-! ## Section 6 — polynomials over a typed signature (transpose of `Term.agda`)

A nested inductive: application nodes carry a color-correct argument
tuple `All (Term Sg Γ)`.  Well-typedness is intrinsic. -/

inductive Term {c : Nat} (Sg : Signature c) (Γ : TypedSet c) : Color c → Type where
  | var : (i : Fin Γ.size) → Term Sg Γ (Γ.color i)
  | app : (ω : Fin Sg.Ops) → All (Term Sg Γ) (Sg.profile ω).dom →
          Term Sg Γ (Sg.profile ω).cod

/-- Color-preserving assignments (substitution data `Γ → Term Δ`). -/
def Assignment (Sg : Signature c) (Γ Δ : TypedSet c) : Type :=
  (i : Fin Γ.size) → Term Sg Δ (Γ.color i)

/- Polynomial substitution.  Structurally recursive (mutual with `substAll`). -/
mutual
def subst {Γ Δ : TypedSet c} (σ : Assignment Sg Γ Δ) :
    {γ : Color c} → Term Sg Γ γ → Term Sg Δ γ
  | _, .var i => σ i
  | _, .app ω ts => .app ω (substAll σ ts)
def substAll {Γ Δ : TypedSet c} (σ : Assignment Sg Γ Δ) :
    {w : List (Color c)} → All (Term Sg Γ) w → All (Term Sg Δ) w
  | _, .nil => .nil
  | _, .cons t ts => .cons (subst σ t) (substAll σ ts)
end

/- A canonical well-founded size measure (mutual with `sizeAll`). -/
mutual
def tsize {Γ : TypedSet c} : {γ : Color c} → Term Sg Γ γ → Nat
  | _, .var _ => 1
  | _, .app _ ts => (sizeAll ts) + 1
def sizeAll {Γ : TypedSet c} : {w : List (Color c)} → All (Term Sg Γ) w → Nat
  | _, .nil => 0
  | _, .cons t ts => tsize t + sizeAll ts
end

/-! ## Section 7a — semantic readout of the term model (`eval`) -/

mutual
/-- Evaluate a polynomial in the recorded points through the
interpretation data. -/
def eval (M : MetricVal Sg D C) : {γ : Color c} → Term Sg D γ → M.Val γ
  | _, .var i => M.point i
  | _, .app ω ts => M.interp ω (evalAll M ts)
def evalAll (M : MetricVal Sg D C) : {w : List (Color c)} → All (Term Sg D) w → All M.Val w
  | _, .nil => .nil
  | _, .cons t ts => .cons (eval M t) (evalAll M ts)
end


/-! ## Section 8 — the contextual rewrite engine (transpose of `Rewrite.agda`)

Reflexive-transitive and symmetric closures are Type-valued (a
derivation is a certificate whose length prices the Lipschitz weight,
Rule 8).  The engine closes an arbitrary ROOT relation under argument
contexts, then normalizes with fuel bounded by a tameness measure. -/

/-- Reflexive-transitive closure (Type-valued). -/
inductive Star {A : Type u} (R : A → A → Type v) : A → A → Type (max u v) where
  | nil : {a : A} → Star R a a
  | cons : {a b c : A} → R a b → Star R b c → Star R a c

/-- Concatenation of derivations. -/
def Star.append {A : Type u} {R : A → A → Type v} :
    {a b c : A} → Star R a b → Star R b c → Star R a c
  | _, _, _, .nil, ys => ys
  | _, _, _, .cons x xs, ys => .cons x (Star.append xs ys)

/-- One symmetric edge. -/
inductive SymClosure {A : Type u} (R : A → A → Type v) : A → A → Type (max u v) where
  | fwd : {a b : A} → R a b → SymClosure R a b
  | bwd : {a b : A} → R b a → SymClosure R a b

/-- Color-indexed root relations on terms in a fixed context. -/
def RootRel (Sg : Signature c) (Γ : TypedSet c) : Type 1 :=
  {γ : Color c} → Term Sg Γ γ → Term Sg Γ γ → Type

/-- Union of root relations (identities together with trace data). -/
inductive RootUnion {Γ : TypedSet c} (R S : RootRel Sg Γ) :
    {γ : Color c} → Term Sg Γ γ → Term Sg Γ γ → Type where
  | inl : {γ : Color c} → {t t' : Term Sg Γ γ} → R t t' → RootUnion R S t t'
  | inr : {γ : Color c} → {t t' : Term Sg Γ γ} → S t t' → RootUnion R S t t'

/-! One-step contextual rewriting: a root step, at the root or inside one
argument position (mutual with `CAllStep`). -/
mutual
inductive CStep {Γ : TypedSet c} (Root : RootRel Sg Γ) :
    {γ : Color c} → Term Sg Γ γ → Term Sg Γ γ → Type where
  | root : {γ : Color c} → {t t' : Term Sg Γ γ} → Root t t' → CStep Root t t'
  | under : {ω : Fin Sg.Ops} → {ts ts' : All (Term Sg Γ) (Sg.profile ω).dom} →
            CAllStep Root ts ts' → CStep Root (.app ω ts) (.app ω ts')
inductive CAllStep {Γ : TypedSet c} (Root : RootRel Sg Γ) :
    {w : List (Color c)} → All (Term Sg Γ) w → All (Term Sg Γ) w → Type where
  | here : {γ : Color c} → {w : List (Color c)} → {t t' : Term Sg Γ γ} →
           {ts : All (Term Sg Γ) w} → CStep Root t t' →
           CAllStep Root (.cons t ts) (.cons t' ts)
  | there : {γ : Color c} → {w : List (Color c)} → {t : Term Sg Γ γ} →
            {ts ts' : All (Term Sg Γ) w} → CAllStep Root ts ts' →
            CAllStep Root (.cons t ts) (.cons t ts')
end

/-! The derivation closure `t ↝* u` (per color). -/
abbrev CStar {Γ : TypedSet c} (Root : RootRel Sg Γ) {γ : Color c}
    (t u : Term Sg Γ γ) : Type :=
  Star (fun (a b : Term Sg Γ γ) => CStep Root a b) t u

/-- The generated congruence `t ≈ u` (per color). -/
abbrev CEq {Γ : TypedSet c} (Root : RootRel Sg Γ) {γ : Color c}
    (t u : Term Sg Γ γ) : Type :=
  Star (fun (a b : Term Sg Γ γ) => SymClosure (fun x y => CStep Root x y) a b) t u

/-- No step applies. -/
def Normal {Γ : TypedSet c} (Root : RootRel Sg Γ) {γ : Color c}
    (t : Term Sg Γ γ) : Prop :=
  ∀ {t' : Term Sg Γ γ}, CStep Root t t' → False

/-- The redex decision, as data (a reducing step, or a normality proof). -/
inductive StepDec {Γ : TypedSet c} (Root : RootRel Sg Γ) {γ : Color c}
    (t : Term Sg Γ γ) : Type where
  | redex : (t' : Term Sg Γ γ) → CStep Root t t' → StepDec Root t
  | normal : Normal Root t → StepDec Root t

/-- Tameness as data: a well-founded measure, its strict decrease along
every step, and the redex decision procedure. -/
structure Tame {Γ : TypedSet c} (Root : RootRel Sg Γ) where
  μ : {γ : Color c} → Term Sg Γ γ → Nat
  decrease : {γ : Color c} → {t t' : Term Sg Γ γ} → CStep Root t t' → μ t' < μ t
  stepDec : {γ : Color c} → (t : Term Sg Γ γ) → StepDec Root t

/-- Output of normalization: the normal form, its certificate, and the
normality witness. -/
structure Result {Γ : TypedSet c} (Root : RootRel Sg Γ) {γ : Color c}
    (t : Term Sg Γ γ) where
  nf : Term Sg Γ γ
  derives : CStar Root t nf
  normal : Normal Root nf

/-- Fuel-indexed normalization: total by strict decrease of the carried
measure below the fuel. -/
def normFuel {Γ : TypedSet c} {Root : RootRel Sg Γ} (T : Tame Root) :
    {γ : Color c} → (f : Nat) → (t : Term Sg Γ γ) → T.μ t ≤ f → Result Root t
  | _, f, t, hle =>
    match T.stepDec t with
    | .normal hn => ⟨t, Star.nil, hn⟩
    | .redex t' d =>
      match f, hle with
      | 0, hle0 => absurd (Nat.lt_of_lt_of_le (T.decrease d) hle0) (Nat.not_lt_zero _)
      | _ + 1, hleS =>
        let r := normFuel T _ t' (Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (T.decrease d) hleS))
        ⟨r.nf, Star.cons d r.derives, r.normal⟩

/-- The normalization algorithm. -/
def normalize {Γ : TypedSet c} {Root : RootRel Sg Γ} (T : Tame Root)
    {γ : Color c} (t : Term Sg Γ γ) : Result Root t :=
  normFuel T (T.μ t) t (Nat.le_refl _)

/-! ## Section 9 — traces, presentations, and the priced propagation layer
(transpose of `Completion.agda` + the `Priced`/`Propagation` layer of
`Metric.agda`). -/

/-- `All.map` over the dependent container. -/
def All.map {A : Type u} {P Q : A → Type v} (f : {x : A} → P x → Q x) :
    {w : List A} → All P w → All Q w
  | _, .nil => .nil
  | _, .cons x xs => .cons (f x) (All.map f xs)

/-- A recorded point of a given color: a carrier index + a color proof. -/
structure Point (D : TypedSet c) (γ : Color c) where
  idx : Fin D.size
  hcol : D.color idx = γ

/-- The variable term of a recorded point. -/
def pointVar {Sg : Signature c} {D : TypedSet c} {γ : Color c}
    (p : Point D γ) : Term Sg D γ :=
  p.hcol ▸ Term.var (Sg := Sg) p.idx

/-- A witnessed application `(θ; y; x)`. -/
structure Witness (Sg : Signature c) (D : TypedSet c) where
  rule : Fin Sg.Ops
  args : All (Point D) (Sg.profile rule).dom
  out : Point D (Sg.profile rule).cod

/-- Formal-application side of a witness. -/
def wlhs {Sg : Signature c} {D : TypedSet c} (w : Witness Sg D) :
    Term Sg D (Sg.profile w.rule).cod :=
  .app w.rule (All.map pointVar w.args)

/-- Recorded-value side of a witness. -/
def wrhs {Sg : Signature c} {D : TypedSet c} (w : Witness Sg D) :
    Term Sg D (Sg.profile w.rule).cod :=
  pointVar w.out

/-- A finitely presented trace. -/
structure Trace (Sg : Signature c) (D : TypedSet c) where
  nwits : Nat
  wit : Fin nwits → Witness Sg D

/-- The trace-generated root: formal application ↝ recorded value. -/
inductive TraceRoot {Sg : Signature c} {D : TypedSet c} (X : Trace Sg D) :
    {γ : Color c} → Term Sg D γ → Term Sg D γ → Type where
  | at_wit : (k : Fin X.nwits) → TraceRoot X (wlhs (X.wit k)) (wrhs (X.wit k))

/-- A presentation: finitely many oriented basic identities. -/
structure Presentation (Sg : Signature c) where
  nrules : Nat
  ctx : Fin nrules → TypedSet c
  col : Fin nrules → Color c
  lhs : (r : Fin nrules) → Term Sg (ctx r) (col r)
  rhs : (r : Fin nrules) → Term Sg (ctx r) (col r)

/-- The rule-instance root: an oriented identity fires under any
substitution instance. -/
inductive PresRoot {Sg : Signature c} {D : TypedSet c} (P : Presentation Sg) :
    {γ : Color c} → Term Sg D γ → Term Sg D γ → Type where
  | at_root : (r : Fin P.nrules) → (σ : Assignment Sg (P.ctx r) D) →
              PresRoot P (subst σ (P.lhs r)) (subst σ (P.rhs r))

/-- The priced presentation: theory identities (exactly sound) together
with a recorded trace.  `sound` is the `ExactlySound` hypothesis. -/
structure Priced (M : MetricVal Sg D C) where
  P : Presentation Sg
  X : Trace Sg D
  sound : ∀ (r : Fin P.nrules) (σ : Assignment Sg (P.ctx r) D),
          C.le (M.d (eval M (subst σ (P.lhs r))) (eval M (subst σ (P.rhs r)))) C.zero

/-- The lawful-completion root: theory identities ∪ trace relations. -/
def pricedRoot {M : MetricVal Sg D C} (PR : Priced M) : RootRel Sg D :=
  RootUnion (PresRoot PR.P) (TraceRoot PR.X)

/-- The defect of a witnessed application. -/
def wdef (M : MetricVal Sg D C) (PR : Priced M) (k : Fin PR.X.nwits) : C.Q :=
  M.d (eval M (wlhs (PR.X.wit k))) (eval M (wrhs (PR.X.wit k)))

/-- The trace error profile `εX` (transpose of `εX`). -/
def epsX (M : MetricVal Sg D C) (PR : Priced M) : C.Q :=
  maxOver PR.X.nwits (wdef M PR)

theorem epsX_nonneg (M : MetricVal Sg D C) (PR : Priced M) :
    C.le C.zero (epsX M PR) :=
  maxOver_nonneg _ _ (fun _ => M.nonneg _ _)

/-! The weight of one step: identities free, trace instances cost `εX`, a
step under a symbol scaled by its modulus (mutual with `allStepBound`). -/
mutual
def stepBound (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {γ : Color c} → {t u : Term Sg D γ} →
    CStep (pricedRoot PR) t u → C.Q
  | _, _, _, .root (.inl (.at_root _ _)) => C.zero
  | _, _, _, .root (.inr (.at_wit k)) => epsX M PR
  | _, _, _, .under (ω := ω) s => L.scale ω (allStepBound M L PR s)
def allStepBound (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {w : List (Color c)} → {ts us : All (Term Sg D) w} →
    CAllStep (pricedRoot PR) ts us → C.Q
  | _, _, _, .here s => stepBound M L PR s
  | _, _, _, .there s => allStepBound M L PR s
end

/-! One step moves the semantics by at most its weight (mutual). -/
mutual
def stepBound_nonneg (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {γ : Color c} → {t u : Term Sg D γ} → (s : CStep (pricedRoot PR) t u) →
    C.le C.zero (stepBound M L PR s)
  | _, _, _, .root (.inl (.at_root _ _)) => C.le_refl
  | _, _, _, .root (.inr (.at_wit k)) => epsX_nonneg M PR
  | _, _, _, .under (ω := ω) s =>
      C.le_trans (L.scale_zero ω) (L.scale_mono ω (allStepBound_nonneg M L PR s))
def allStepBound_nonneg (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {w : List (Color c)} → {ts us : All (Term Sg D) w} →
    (s : CAllStep (pricedRoot PR) ts us) → C.le C.zero (allStepBound M L PR s)
  | _, _, _, .here s => stepBound_nonneg M L PR s
  | _, _, _, .there s => allStepBound_nonneg M L PR s
end

mutual
def step_d (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {γ : Color c} → {t u : Term Sg D γ} → (s : CStep (pricedRoot PR) t u) →
    C.le (M.d (eval M t) (eval M u)) (stepBound M L PR s)
  | _, _, _, .root (.inl (.at_root r σ)) => PR.sound r σ
  | _, _, _, .root (.inr (.at_wit k)) => maxOver_ub PR.X.nwits (wdef M PR) k
  | _, _, _, .under (ω := ω) s =>
      C.le_trans (L.lip ω _ _) (L.scale_mono ω (allStep_d M L PR s))
def allStep_d (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {w : List (Color c)} → {ts us : All (Term Sg D) w} →
    (s : CAllStep (pricedRoot PR) ts us) →
    C.le (dAll M (evalAll M ts) (evalAll M us)) (allStepBound M L PR s)
  | _, _, _, .here (ts := ts) s =>
      C.max_lub (step_d M L PR s)
        (C.le_trans (dAll_refl M (evalAll M ts)) (stepBound_nonneg M L PR s))
  | _, _, _, .there (t := t) s =>
      C.max_lub (C.le_trans (M.d_refl (eval M t)) (allStepBound_nonneg M L PR s))
        (allStep_d M L PR s)
end

/-- The weight of a derivation certificate: the sum of its step weights. -/
def derivBound (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {γ : Color c} → {t u : Term Sg D γ} → CStar (pricedRoot PR) t u → C.Q
  | _, _, _, .nil => C.zero
  | _, _, _, .cons s ds => C.add (stepBound M L PR s) (derivBound M L PR ds)

/-- **Defect propagation** (transpose of `deriv-d`): the semantic distance
of the endpoints is bounded by the certificate's weight. -/
def deriv_d (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) {γ : Color c}
    {t u : Term Sg D γ} (ds : CStar (pricedRoot PR) t u) :
    C.le (M.d (eval M t) (eval M u)) (derivBound M L PR ds) := by
  induction ds with
  | nil => simp only [derivBound]; exact M.d_refl _
  | cons s ds ih =>
      simp only [derivBound]
      exact C.le_trans (M.triangle _ _ _) (C.add_mono (step_d M L PR s) ih)

/-- The congruence weight: symmetric steps priced by the same weight. -/
def eqBound (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) :
    {γ : Color c} → {t u : Term Sg D γ} → CEq (pricedRoot PR) t u → C.Q
  | _, _, _, .nil => C.zero
  | _, _, _, .cons (.fwd s) e => C.add (stepBound M L PR s) (eqBound M L PR e)
  | _, _, _, .cons (.bwd s) e => C.add (stepBound M L PR s) (eqBound M L PR e)

/-- Congruence defect bound. -/
def eq_d (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) {γ : Color c}
    {t u : Term Sg D γ} (e : CEq (pricedRoot PR) t u) :
    C.le (M.d (eval M t) (eval M u)) (eqBound M L PR e) := by
  induction e with
  | nil => simp only [eqBound]; exact M.d_refl _
  | cons sc e ih =>
      cases sc with
      | fwd s =>
          simp only [eqBound]
          exact C.le_trans (M.triangle _ _ _) (C.add_mono (step_d M L PR s) ih)
      | bwd s =>
          simp only [eqBound]
          exact C.le_trans (M.triangle _ _ _)
            (C.add_mono (C.le_trans (M.d_sym _ _) (step_d M L PR s)) ih)

/-- **The compositional error law** (transpose of `eqBound-◅◅`): the weight
of a composite derivation is the sum of the weights, up to the cost setoid. -/
def eqBound_append (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M) {γ : Color c}
    {t u v : Term Sg D γ} (e : CEq (pricedRoot PR) t u) (e' : CEq (pricedRoot PR) u v) :
    C.eqv (eqBound M L PR (Star.append e e'))
          (C.add (eqBound M L PR e) (eqBound M L PR e')) := by
  induction e with
  | nil => simp only [Star.append, eqBound]; exact C.eqv_symm (C.zero_add _)
  | cons sc e ih =>
      cases sc with
      | fwd s =>
          simp only [Star.append, eqBound]
          exact C.eqv_trans (C.add_congr_right (ih e')) (C.eqv_symm (C.add_assoc _ _ _))
      | bwd s =>
          simp only [Star.append, eqBound]
          exact C.eqv_trans (C.add_congr_right (ih e')) (C.eqv_symm (C.add_assoc _ _ _))

/-- **The reflection-unit defect** (transpose of `unit-defect`): the distance
from a polynomial to its lawful normal-form representative is bounded by the
weight of the normalizer's own certificate. -/
def unit_defect (M : MetricVal Sg D C) (L : Lipschitz M) (PR : Priced M)
    (T : Tame (pricedRoot PR)) {γ : Color c} (t : Term Sg D γ) :
    C.le (M.d (eval M t) (eval M (normalize T t).nf))
         (derivBound M L PR (normalize T t).derives) :=
  deriv_d M L PR (normalize T t).derives

end YMGap.CodynamicCore


