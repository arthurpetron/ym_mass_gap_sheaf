/-
Route 2 — the constructive discrete Bakry–Émery template: curvature ⇒ gap
MAGNITUDE on a finite reversible Markov generator.

# Why this module (the substantive "magnitude" route)

The located-gap module upgrades a bare gap predicate to a Type-level
`LocatedSpectralGap` witness, but it does NOT explain *why* the excited
spectrum sits strictly below the vacuum eigenvalue — it takes the separator
as given.  The Bakry–Émery curvature-dimension criterion supplies the
missing MAGNITUDE: a lower curvature bound `CD(K,∞)` (the Bochner inequality
`Γ₂ ≥ K·Γ`) on a finite reversible Markov generator forces every nonzero
eigenvalue to be `≥ K`, hence a spectral gap of size at least `K`.  This is
the geometric analog of the way a uniform cluster bound packages the
correlation-decay route: a single reusable bridge from a curvature
hypothesis to a quantitative gap.

# The eigenfunction route — no time integral

Bakry–Émery is usually run as a semigroup interpolation, which needs
continuous-time integration `∫₀^∞`.  That is unavailable (and unwanted) in a
choice-free finite `Q'` setting.  We use the algebraic *eigenfunction*
route instead, which is pure finite linear algebra over the finite
stationary measure π (a finite π-weighted sum, never an integral):

  * Carré du champ  `Γ(f,g) = ½(L(fg) − f·Lg − g·Lf)`,  `Γ(f) := Γ(f,f)`.
  * Iterated        `Γ₂(f) = ½(L Γ(f) − 2 Γ(f, Lf))`.
  * The two facts that make the whole identity stack collapse are, for the
    π-mean `E[h] = Σ_x π(x) h(x)`:
      (A)  SELF-ADJOINTNESS    `E[f · Lg] = E[g · Lf]`   (reversibility),
      (B)  MEAN-ZERO           `E[L h] = 0`              (mass conservation:
           reversibility + zero row sums of the generator).
  * From (A),(B):
      DIRICHLET  `E[Γ(f)] = E[f · (−Lf)]`,
      BOCHNER    `E[Γ₂(f)] = E[(Lf)²]`.
  * For an eigenfunction `Lf = −λf`: `E[Γ(f)] = λ·E[f²]` and
    `E[Γ₂(f)] = λ²·E[f²]`.  The curvature bound in π-mean,
    `E[Γ₂(f)] ≥ K·E[Γ(f)]`, then reads `λ²·E[f²] ≥ K·λ·E[f²]`, and
    cancelling the positive factor `λ·E[f²]` gives `λ ≥ K`.

So CD(K) with `K > 0` ⇒ spectral gap ≥ K, by finite `Q'` algebra alone.
Bridged to the located-gap datum: the transfer operator `P = I − sL` has
every excited eigenvalue `≤ 1 − sK < 1`, a located gap with margin `sK`.

# Honest scope — the uniform-curvature wall

This is the abstract reusable bridge.  It gives a genuine gap MAGNITUDE from
curvature, unlike a purely topological / located-but-unquantified witness.
But it only *reshapes* the continuum problem: closing the Yang–Mills mass
gap through this route requires inhabiting `CD(K)` with a single `K > 0`
holding UNIFORMLY for the lattice heat-kernel measure as the spacing
`a → 0`.  That uniform lower curvature bound is the named open analytic
content — the "uniform curvature wall."  The free/Haar part is
curved-positive (a compact Lie group with its bi-invariant metric has
nonnegative Ricci curvature; `SU(2) = S³` is positively curved), so the
obstruction is the interacting Wilson-action Hessian at weak coupling.  The
mechanism is the Bakry–Émery criterion; the closest rigorous lattice
precedent is the strong-coupling log-Sobolev / curvature program for
lattice gauge measures (Shen–Zhu–Zhu, CMP 2023).  None of that uniform
content is asserted here; only the abstract `CD ⇒ gap` bridge is proved.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext]` / `[propext, Quot.sound]` only.  No
`Classical.*`, no `sorryAx`, no `native_decide`.  Witnesses are Type-level
data (Rule 8).
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.BakryEmery

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum

/-! ## Small `Q'` / `finSum` lemmas used below -/

/-- Structural equality lifts to `eqv`. -/
theorem eqv_of_eq {a b : Q'} (h : a = b) : a.eqv b := by subst h; exact Q'.eqv_refl a

/-- `Σ (−f) ≃ −(Σ f)`. -/
theorem finSum_neg (f : QSeq) :
    ∀ m, (finSum (fun i => -(f i)) m).eqv (-(finSum f m))
  | 0 => by
      show (0 : Q').eqv (-(0 : Q'))
      decide
  | m + 1 => by
      show (finSum (fun i => -(f i)) m + (-(f m))).eqv (-(finSum f m + f m))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-(f m)) (finSum_neg f m)) ?_
      -- (−Σ) + (−fm) ≃ −(Σ + fm)
      exact Q'.eqv_symm (Q'.neg_add_eqv (finSum f m) (f m))
  -- (the local `neg_add_eqv` mirror lives in CRealMul, re-exported via Q')

/-- A half constant `1/2 : Q'`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The constant `2 : Q'`. -/
def two : Q' := Q'.ofNat 2

/-- `½·2 ≃ 1`. -/
theorem half_two : (half * two).eqv 1 := by decide

/-- `2·a ≃ a + a`. -/
theorem two_mul_eqv (a : Q') : (two * a).eqv (a + a) := by
  -- two*a num = 2*a.num, den = 1*a.den; (a+a) num = 2*a.num*a.den, den = a.den²
  show (two * a).num * ((a + a).den : Int) = (a + a).num * ((two * a).den : Int)
  rw [Q'.mul_den_cast two a, Q'.add_den_cast a a]
  show ((2 : Int) * a.num) * ((a.den : Int) * (a.den : Int))
      = (a.num * (a.den : Int) + a.num * (a.den : Int)) * ((1 : Int) * (a.den : Int))
  have e : a.num * (a.den : Int) + a.num * (a.den : Int)
         = (2 : Int) * (a.num * (a.den : Int)) := by
    rw [Int.two_mul]
  rw [e, Int.one_mul]
  rw [Int.mul_assoc (2 : Int) (a.num * (a.den : Int)) (a.den : Int),
      Int.mul_assoc (2 : Int) a.num ((a.den : Int) * (a.den : Int)),
      Int.mul_assoc a.num (a.den : Int) (a.den : Int)]

/-- `½·(2·a) ≃ a`. -/
theorem half_two_mul (a : Q') : (half * (two * a)).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half two a))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (half * two) 1 a half_two)
      (Q'.one_mul_eqv a))

/-- `½·(a + a) ≃ a`. -/
theorem half_double (a : Q') : (half * (a + a)).eqv a :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left half (a + a) (two * a) (Q'.eqv_symm (two_mul_eqv a)))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half two a))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (half * two) 1 a half_two)
        (Q'.one_mul_eqv a)))

/-- Product of two positive `Q'` values is positive. -/
theorem mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) : (0 : Q') < a * b := by
  show (0 : Int) * ((a * b).den : Int) < (a * b).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  exact Int.mul_pos (CReal.num_pos_of_pos ha) (CReal.num_pos_of_pos hb)

/-- Cancel a positive right factor: `0 < c → a·c ≤ b·c → a ≤ b`. -/
theorem le_of_mul_le_mul_right_pos {a b c : Q'} (hc : (0 : Q') < c) (h : a * c ≤ b * c) :
    a ≤ b := by
  have hcn : 0 < c.num := CReal.num_pos_of_pos hc
  have hh : (a * c).num * ((b * c).den : Int) ≤ (b * c).num * ((a * c).den : Int) := h
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  rw [show (a * c).num = a.num * c.num from rfl,
      show (b * c).num = b.num * c.num from rfl,
      Q'.mul_den_cast b c, Q'.mul_den_cast a c] at hh
  -- (a.num·c.num)·(b.den·c.den) ≤ (b.num·c.num)·(a.den·c.den)
  -- ⇔ (c.num·c.den)·(a.num·b.den) ≤ (c.num·c.den)·(b.num·a.den)
  have e1 : (a.num * c.num) * ((b.den : Int) * (c.den : Int))
          = (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by ac_rfl
  have e2 : (b.num * c.num) * ((a.den : Int) * (c.den : Int))
          = (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by ac_rfl
  rw [e1, e2] at hh
  have hcc : 0 < c.num * (c.den : Int) := Int.mul_pos hcn (by exact_mod_cast c.den_pos)
  exact Int.le_of_mul_le_mul_left hh hcc

/-- Four-factor rearrangement `a·(b·(c·d)) ≃ (a·c)·(b·d)`. -/
theorem rearr4 (a b c d : Q') : (a * (b * (c * d))).eqv ((a * c) * (b * d)) := by
  -- a·(b·(c·d)) ≃ a·((b·c)·d) ≃ a·((c·b)·d) ≃ a·(c·(b·d)) ≃ (a·c)·(b·d)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a (b * (c * d)) ((b * c) * d)
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a ((b * c) * d) ((c * b) * d)
      (Q'.mul_eqv_congr_right (b * c) (c * b) d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a ((c * b) * d) (c * (b * d)) (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-! ## The finite reversible Markov generator

A finite state space `n` (only the first `n` indices are read), a generator
matrix `L`, a stationary measure `pi > 0`.  The two analytic hypotheses are
carried as `eqv` facts:

  * `reversible` : the detailed-balance symmetry `π(x)·L(x,y) ≃ π(y)·L(y,x)`,
  * `rowSumZero` : each row of `L` sums to zero (a Markov *generator*).

These are exactly the two facts the Dirichlet and Bochner identities below
are derived from.  No normalization `Σπ = 1` is needed for the eigenvalue
bound (it only rescales `E`), so we omit it to keep the structure minimal;
`pi_pos` and `E[f²] > 0` for a non-constant `f` are what the cancellation
uses. -/
structure RevGen where
  /-- Number of states (finite); only indices `< n` are read. -/
  n : Nat
  /-- Stationary measure `π : state → Q'`. -/
  pi : Nat → Q'
  /-- Generator matrix `L : state → state → Q'`  (off-diagonal `≥ 0`,
  row sums zero; only the off-diagonal sign is irrelevant to the algebra). -/
  L : Nat → Nat → Q'
  /-- `π` is strictly positive on every state. -/
  pi_pos : ∀ x, (0 : Q') < pi x
  /-- Detailed balance / reversibility: `π(x)·L(x,y) ≃ π(y)·L(y,x)`. -/
  reversible : ∀ x y, ((pi x * L x y).eqv (pi y * L y x))
  /-- Generator: every row of `L` sums to zero, `Σ_{y<n} L(x,y) ≃ 0`. -/
  rowSumZero : ∀ x, (finSum (fun y => L x y) n).eqv 0

namespace RevGen

variable (G : RevGen)

/-- The generator applied to a function: `(Lf)(x) = Σ_{y<n} L(x,y)·f(y)`. -/
def Lapp (f : Nat → Q') (x : Nat) : Q' := finSum (fun y => G.L x y * f y) G.n

/-- The π-mean (expectation) `E[h] = Σ_{x<n} π(x)·h(x)`. -/
def E (h : Nat → Q') : Q' := finSum (fun x => G.pi x * h x) G.n

/-! ### Carré du champ and its iterate -/

/-- Pointwise product of two functions. -/
def pmul (f g : Nat → Q') (x : Nat) : Q' := f x * g x

/-- Bilinear carré du champ `Γ(f,g)(x) = ½(L(fg) − f·Lg − g·Lf)(x)`. -/
def Gamma (f g : Nat → Q') (x : Nat) : Q' :=
  half * (G.Lapp (pmul f g) x + (-(f x * G.Lapp g x)) + (-(g x * G.Lapp f x)))

/-- Carré du champ `Γ(f) = Γ(f,f)`. -/
def Gamma1 (f : Nat → Q') (x : Nat) : Q' := G.Gamma f f x

/-- Iterated carré du champ `Γ₂(f)(x) = ½(L Γ(f) − 2·Γ(f, Lf))(x)`. -/
def Gamma2 (f : Nat → Q') (x : Nat) : Q' :=
  half * (G.Lapp (G.Gamma1 f) x + (-(two * G.Gamma f (G.Lapp f) x)))

/-! ### Linearity of the π-mean `E` -/

/-- `E[h₁ + h₂] ≃ E[h₁] + E[h₂]`. -/
theorem E_add (h₁ h₂ : Nat → Q') :
    (G.E (fun x => h₁ x + h₂ x)).eqv (G.E h₁ + G.E h₂) := by
  show (finSum (fun x => G.pi x * (h₁ x + h₂ x)) G.n).eqv
       (finSum (fun x => G.pi x * h₁ x) G.n + finSum (fun x => G.pi x * h₂ x) G.n)
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun x => G.pi x * h₁ x + G.pi x * h₂ x)
      (fun x => Q'.mul_add_eqv (G.pi x) (h₁ x) (h₂ x)) G.n) ?_
  exact finSum_add (fun x => G.pi x * h₁ x) (fun x => G.pi x * h₂ x) G.n

/-- `E[−h] ≃ −E[h]`. -/
theorem E_neg (h : Nat → Q') :
    (G.E (fun x => -(h x))).eqv (-(G.E h)) := by
  show (finSum (fun x => G.pi x * (-(h x))) G.n).eqv (-(finSum (fun x => G.pi x * h x) G.n))
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun x => -(G.pi x * h x))
      (fun x => Q'.mul_neg_eqv (G.pi x) (h x)) G.n) ?_
  exact finSum_neg (fun x => G.pi x * h x) G.n

/-- `E[c·h] ≃ c·E[h]`. -/
theorem E_const_mul (c : Q') (h : Nat → Q') :
    (G.E (fun x => c * h x)).eqv (c * G.E h) := by
  show (finSum (fun x => G.pi x * (c * h x)) G.n).eqv (c * finSum (fun x => G.pi x * h x) G.n)
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun x => c * (G.pi x * h x))
      (fun x => ?_) G.n)
    (Q'.eqv_symm (const_mul_finSum (fun x => G.pi x * h x) c G.n))
  -- π x * (c * h x) ≃ c * (π x * h x)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (G.pi x) (c * h x) (h x * c) (Q'.mul_comm_eqv c (h x)))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (G.pi x) (h x) c))
      (Q'.mul_comm_eqv (G.pi x * h x) c))

/-- `E` respects pointwise `eqv`. -/
theorem E_eqv_congr (h₁ h₂ : Nat → Q') (h : ∀ x, (h₁ x).eqv (h₂ x)) :
    (G.E h₁).eqv (G.E h₂) :=
  finSum_eqv_congr _ _ (fun x => Q'.mul_eqv_congr_left (G.pi x) (h₁ x) (h₂ x) (h x)) G.n

/-! ### (B) MEAN-ZERO  `E[L h] ≃ 0`

The π-mean of `L` applied to any function vanishes: a finite double-sum
that, after a swap and the detailed-balance rewrite `π(x)L(x,y)=π(y)L(y,x)`,
factors through the zero row sums of the generator. -/

/-- Inner reduction: for a fixed `y`, `Σ_{x} π(x)·(L(x,y)·h(y)) ≃ 0`. -/
private theorem mean_zero_inner (h : Nat → Q') (y : Nat) :
    (finSum (fun x => G.pi x * (G.L x y * h y)) G.n).eqv 0 := by
  -- π(x)·(L x y · h y) ≃ (π(y)·L(y,x))·h(y)  (assoc + reversibility)
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun x => (G.pi y * G.L y x) * h y) (fun x => ?_) G.n) ?_
  · -- π(x)·(L x y · h y) ≃ (π x · L x y)·h y ≃ (π y · L y x)·h y
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (G.pi x) (G.L x y) (h y)))
      (Q'.mul_eqv_congr_right (G.pi x * G.L x y) (G.pi y * G.L y x) (h y) (G.reversible x y))
  · -- Σ_x (π y · L y x)·h y ≃ (Σ_x π y · L y x)·h y ≃ (π y · Σ_x L y x)·h y ≃ (π y · 0)·h y ≃ 0
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (finSum_mul_const (fun x => G.pi y * G.L y x) (h y) G.n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (h y)
        (Q'.eqv_symm (const_mul_finSum (fun x => G.L y x) (G.pi y) G.n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (h y)
        (Q'.mul_eqv_congr_left (G.pi y) _ 0 (G.rowSumZero y))) ?_
    -- (π y · 0)·h y ≃ 0·h y ≃ 0
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 (h y) (Q'.mul_zero_eqv (G.pi y)))
      (Q'.zero_mul_eqv (h y))

/-- **(B) Mean-zero.**  `E[L h] ≃ 0`. -/
theorem E_Lapp_zero (h : Nat → Q') : (G.E (G.Lapp h)).eqv 0 := by
  show (finSum (fun x => G.pi x * finSum (fun y => G.L x y * h y) G.n) G.n).eqv 0
  -- pull π(x) into the inner sum, swap, then collapse each inner column by mean_zero_inner
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun x => finSum (fun y => G.pi x * (G.L x y * h y)) G.n)
      (fun x => const_mul_finSum (fun y => G.L x y * h y) (G.pi x) G.n) G.n) ?_
  refine Q'.eqv_trans _ _ _ (finSum_swap (fun x y => G.pi x * (G.L x y * h y)) G.n G.n) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun _ => (0 : Q')) (fun y => G.mean_zero_inner h y) G.n) ?_
  rw [finSum_zero_seq G.n]
  exact Q'.eqv_refl 0

/-! ### (A) SELF-ADJOINTNESS  `E[f·Lg] ≃ E[g·Lf]`

Reflexivity of `L` w.r.t. the π-inner-product: the double sum is symmetric
under the detailed-balance rewrite, so the two means agree. -/

/-- The common symmetric double-sum form of `E[f·Lg]`:
`E[f·Lg] ≃ Σ_x Σ_y π(x)·(f(x)·(L(x,y)·g(y)))`. -/
private theorem E_pmul_Lapp_double (f g : Nat → Q') :
    (G.E (pmul f (G.Lapp g))).eqv
      (finSum (fun x => finSum (fun y => G.pi x * (f x * (G.L x y * g y))) G.n) G.n) := by
  show (finSum (fun x => G.pi x * (f x * finSum (fun y => G.L x y * g y) G.n)) G.n).eqv _
  refine finSum_eqv_congr _ _ (fun x => ?_) G.n
  -- π(x)·(f(x)·Σ_y L x y · g y) ≃ Σ_y π(x)·(f(x)·(L x y · g y))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (G.pi x) _ _ (const_mul_finSum (fun y => G.L x y * g y) (f x) G.n)) ?_
  exact const_mul_finSum (fun y => f x * (G.L x y * g y)) (G.pi x) G.n

/-- **(A) Self-adjointness.**  `E[f·Lg] ≃ E[g·Lf]`. -/
theorem E_self_adjoint (f g : Nat → Q') :
    (G.E (pmul f (G.Lapp g))).eqv (G.E (pmul g (G.Lapp f))) := by
  -- both sides reduce to a common double sum; rev makes the terms agree after a swap
  refine Q'.eqv_trans _ _ _ (G.E_pmul_Lapp_double f g) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (G.E_pmul_Lapp_double g f))
  -- Goal: Σ_x Σ_y T_fg(x,y) ≃ Σ_x Σ_y T_gf(x,y)
  -- where T_fg(x,y) = π x·(f x·(L x y·g y)),  T_gf(x,y) = π x·(g x·(L x y·f y)).
  -- Use swap on RHS, then termwise rev: T_fg(x,y) ≃ T_gf(y,x).
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (finSum_swap (fun x y => G.pi x * (g x * (G.L x y * f y))) G.n G.n))
  -- now RHS is Σ_x Σ_y T_gf(y,x) (outer x, inner y, term π y·(g y·(L y x·f x)))
  refine finSum_eqv_congr _ _ (fun x => finSum_eqv_congr _ _ (fun y => ?_) G.n) G.n
  -- termwise: π x·(f x·(L x y·g y)) ≃ π y·(g y·(L y x·f x))
  -- canonicalize both via rearr4 to (a·c)·(b·d):
  --   LHS → (π x·L x y)·(f x·g y),   RHS → (π y·L y x)·(g y·f x)
  refine Q'.eqv_trans _ _ _ (rearr4 (G.pi x) (f x) (G.L x y) (g y)) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (rearr4 (G.pi y) (g y) (G.L y x) (f x)))
  -- (π x·L x y)·(f x·g y) ≃ (π y·L y x)·(g y·f x)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (f x * g y) (G.reversible x y))
    (Q'.mul_eqv_congr_left (G.pi y * G.L y x) (f x * g y) (g y * f x)
      (Q'.mul_comm_eqv (f x) (g y)))

/-! ### The DIRICHLET identity  `E[Γ(f)] ≃ E[f·(−Lf)] = −E[f·Lf]` -/

/-- **Dirichlet identity.**  `E[Γ(f)] ≃ −E[f·Lf]` (integration by parts on the
finite measure: `⟨f, −Lf⟩_π = ⟨Γ(f)⟩_π`). -/
theorem dirichlet (f : Nat → Q') :
    (G.E (G.Gamma1 f)).eqv (-(G.E (pmul f (G.Lapp f)))) := by
  -- Γ₁(f) x = ½·( A x + B x + B x ),  A = Lapp(ff),  B x = −(f x·Lf x).
  -- E(Γ₁ f) ≃ ½·E(A + B + B).  Reduce the inner mean to −EP + −EP.
  refine Q'.eqv_trans _ _ _ (G.E_const_mul half
    (fun x => G.Lapp (pmul f f) x + (-(f x * G.Lapp f x)) + (-(f x * G.Lapp f x)))) ?_
  -- inner-mean facts
  have hA : (G.E (fun x => G.Lapp (pmul f f) x)).eqv 0 := G.E_Lapp_zero (pmul f f)
  have hB : (G.E (fun x => -(f x * G.Lapp f x))).eqv (-(G.E (pmul f (G.Lapp f)))) :=
    G.E_neg (fun x => f x * G.Lapp f x)
  -- E((A+B)+B) ≃ (E A + E B) + E B ≃ (0 + −EP) + −EP
  have hinner :
      (G.E (fun x => G.Lapp (pmul f f) x + (-(f x * G.Lapp f x)) + (-(f x * G.Lapp f x)))).eqv
        ((-(G.E (pmul f (G.Lapp f)))) + (-(G.E (pmul f (G.Lapp f))))) := by
    refine Q'.eqv_trans _ _ _
      (G.E_add (fun x => G.Lapp (pmul f f) x + (-(f x * G.Lapp f x)))
               (fun x => -(f x * G.Lapp f x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (G.E_add (fun x => G.Lapp (pmul f f) x) (fun x => -(f x * G.Lapp f x)))) ?_
    -- ((E A + E B) + E B) ≃ ((0 + −EP) + −EP) ≃ (−EP + −EP)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hA)
          (Q'.add_eqv_congr_left 0 _ _ hB))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hB) ?_
    -- (0 + −EP) + −EP ≃ −EP + −EP
    exact Q'.add_eqv_congr_right _ _ _ (eqv_of_eq (Q'.zero_add' _))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ hinner) ?_
  exact half_double (-(G.E (pmul f (G.Lapp f))))

/-! ### The BOCHNER identity  `E[Γ₂(f)] ≃ E[(Lf)²]` -/

/-- The cross carré-du-champ mean `E[Γ(f, Lf)] ≃ −E[(Lf)²]` — the step where
self-adjointness `E[f·L(Lf)] = E[(Lf)²]` collapses the two cross terms. -/
private theorem E_Gamma_fLf (f : Nat → Q') :
    (G.E (G.Gamma f (G.Lapp f))).eqv (-(G.E (pmul (G.Lapp f) (G.Lapp f)))) := by
  -- Γ(f,Lf) x = ½·( Lapp(f·Lf) x + −(f x·L(Lf) x) + −(Lf x·Lf x) )
  refine Q'.eqv_trans _ _ _ (G.E_const_mul half
    (fun x => G.Lapp (pmul f (G.Lapp f)) x
      + (-(f x * G.Lapp (G.Lapp f) x)) + (-(G.Lapp f x * G.Lapp f x)))) ?_
  let Q : Nat → Q' := pmul (G.Lapp f) (G.Lapp f)
  have hA : (G.E (fun x => G.Lapp (pmul f (G.Lapp f)) x)).eqv 0 :=
    G.E_Lapp_zero (pmul f (G.Lapp f))
  -- E(−(f·L(Lf))) ≃ −E(f·L(Lf)) ≃ −E((Lf)²)  [self-adjoint]
  have hSA : (G.E (pmul f (G.Lapp (G.Lapp f)))).eqv (G.E Q) :=
    G.E_self_adjoint f (G.Lapp f)
  have hB1 : (G.E (fun x => -(f x * G.Lapp (G.Lapp f) x))).eqv (-(G.E Q)) :=
    Q'.eqv_trans _ _ _ (G.E_neg (fun x => f x * G.Lapp (G.Lapp f) x))
      (Q'.neg_eqv_congr _ _ hSA)
  have hB2 : (G.E (fun x => -(G.Lapp f x * G.Lapp f x))).eqv (-(G.E Q)) :=
    G.E_neg (fun x => G.Lapp f x * G.Lapp f x)
  -- assemble inner mean to (−EQ) + (−EQ)
  have hinner :
      (G.E (fun x => G.Lapp (pmul f (G.Lapp f)) x
        + (-(f x * G.Lapp (G.Lapp f) x)) + (-(G.Lapp f x * G.Lapp f x)))).eqv
        ((-(G.E Q)) + (-(G.E Q))) := by
    refine Q'.eqv_trans _ _ _
      (G.E_add (fun x => G.Lapp (pmul f (G.Lapp f)) x + (-(f x * G.Lapp (G.Lapp f) x)))
               (fun x => -(G.Lapp f x * G.Lapp f x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (G.E_add (fun x => G.Lapp (pmul f (G.Lapp f)) x)
                 (fun x => -(f x * G.Lapp (G.Lapp f) x)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hA)
          (Q'.add_eqv_congr_left 0 _ _ hB1))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hB2) ?_
    exact Q'.add_eqv_congr_right _ _ _ (eqv_of_eq (Q'.zero_add' _))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ hinner) ?_
  exact half_double (-(G.E Q))

/-- **Bochner identity.**  `E[Γ₂(f)] ≃ E[(Lf)²]` (the π-mean Bochner formula;
no time integral). -/
theorem bochner (f : Nat → Q') :
    (G.E (G.Gamma2 f)).eqv (G.E (pmul (G.Lapp f) (G.Lapp f))) := by
  let Q : Nat → Q' := pmul (G.Lapp f) (G.Lapp f)
  -- Γ₂ f x = ½·( Lapp(Γ₁ f) x + −(2·Γ(f,Lf) x) )
  refine Q'.eqv_trans _ _ _ (G.E_const_mul half
    (fun x => G.Lapp (G.Gamma1 f) x + (-(two * G.Gamma f (G.Lapp f) x)))) ?_
  have hA : (G.E (fun x => G.Lapp (G.Gamma1 f) x)).eqv 0 := G.E_Lapp_zero (G.Gamma1 f)
  -- E(−(2·Γ(f,Lf))) ≃ −(2·E(Γ(f,Lf))) ≃ −(2·(−EQ)) ≃ 2·EQ
  have hC : (G.E (fun x => -(two * G.Gamma f (G.Lapp f) x))).eqv (two * G.E Q) := by
    refine Q'.eqv_trans _ _ _ (G.E_neg (fun x => two * G.Gamma f (G.Lapp f) x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (G.E_const_mul two (G.Gamma f (G.Lapp f)))) ?_
    -- −(2·E(Γ(f,Lf))) ≃ −(2·(−EQ)) ≃ −(−(2·EQ)) ≃ 2·EQ
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left two _ _ (G.E_Gamma_fLf f))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv two (G.E Q))) ?_
    exact Q'.neg_neg_eqv (two * G.E Q)
  -- ½·( E(Lapp Γ₁f) + E(−2Γ) ) ≃ ½·( 0 + 2·EQ ) ≃ ½·(2·EQ) ≃ EQ
  have hinner :
      (G.E (fun x => G.Lapp (G.Gamma1 f) x + (-(two * G.Gamma f (G.Lapp f) x)))).eqv
        (two * G.E Q) := by
    refine Q'.eqv_trans _ _ _
      (G.E_add (fun x => G.Lapp (G.Gamma1 f) x)
               (fun x => -(two * G.Gamma f (G.Lapp f) x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hA) (Q'.add_eqv_congr_left 0 _ _ hC)) ?_
    exact eqv_of_eq (Q'.zero_add' _)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ hinner) ?_
  exact half_two_mul (G.E Q)

/-! ### Eigenfunctions and the curvature-dimension predicate -/

/-- `f` is an eigenfunction of `L` for eigenvalue `−λ` (so `Lf = −λ f`,
the energy `λ` of the transfer operator): `(Lf)(x) ≃ −(λ·f(x))` for all `x`. -/
def Eigen (f : Nat → Q') (lam : Q') : Prop := ∀ x, (G.Lapp f x).eqv (-(lam * f x))

/-- The curvature-dimension predicate `CD(K,∞)` in π-mean:
`E[Γ₂(f)] ≥ K·E[Γ(f)]` for every test function `f`. -/
def CD (K : Q') : Prop := ∀ f : Nat → Q', K * G.E (G.Gamma1 f) ≤ G.E (G.Gamma2 f)

/-- For an eigenfunction, the Dirichlet energy is `λ·E[f²]`:
`E[Γ(f)] ≃ λ·E[f²]`. -/
theorem dirichlet_eigen (f : Nat → Q') (lam : Q') (hf : G.Eigen f lam) :
    (G.E (G.Gamma1 f)).eqv (lam * G.E (pmul f f)) := by
  refine Q'.eqv_trans _ _ _ (G.dirichlet f) ?_
  -- −E(f·Lf) ≃ −(−(λ·E(f²))) ≃ λ·E(f²)
  have hP : (G.E (pmul f (G.Lapp f))).eqv (-(lam * G.E (pmul f f))) := by
    -- termwise: f x · Lapp f x ≃ −(λ·(f x·f x))
    refine Q'.eqv_trans _ _ _
      (G.E_eqv_congr (pmul f (G.Lapp f)) (fun x => -(lam * (f x * f x))) (fun x => ?_)) ?_
    · -- f x · Lapp f x ≃ f x · (−(λ f x)) ≃ −(f x·(λ·f x)) ≃ −(λ·(f x·f x))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (f x) _ _ (hf x)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (f x) (lam * f x)) ?_
      refine Q'.neg_eqv_congr _ _ ?_
      -- f x·(λ·f x) ≃ (f x·λ)·f x ≃ (λ·f x)·f x ≃ λ·(f x·f x)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (f x) lam (f x))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (f x * lam) (lam * f x) (f x) (Q'.mul_comm_eqv (f x) lam)) ?_
      exact Q'.mul_assoc_eqv lam (f x) (f x)
    · -- E(−(λ·(f²))) ≃ −(λ·E(f²))
      refine Q'.eqv_trans _ _ _ (G.E_neg (fun x => lam * (f x * f x))) ?_
      exact Q'.neg_eqv_congr _ _ (G.E_const_mul lam (pmul f f))
  refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hP) ?_
  exact Q'.neg_neg_eqv (lam * G.E (pmul f f))

/-- For an eigenfunction, the iterated energy is `λ²·E[f²]`:
`E[Γ₂(f)] ≃ λ²·E[f²]`. -/
theorem bochner_eigen (f : Nat → Q') (lam : Q') (hf : G.Eigen f lam) :
    (G.E (G.Gamma2 f)).eqv ((lam * lam) * G.E (pmul f f)) := by
  refine Q'.eqv_trans _ _ _ (G.bochner f) ?_
  -- E((Lf)²) ≃ λ²·E(f²)
  refine Q'.eqv_trans _ _ _
    (G.E_eqv_congr (pmul (G.Lapp f) (G.Lapp f)) (fun x => (lam * lam) * (f x * f x))
      (fun x => ?_)) ?_
  · -- Lapp f x · Lapp f x ≃ (−(λ f x))·(−(λ f x)) ≃ (λ f x)·(λ f x) ≃ (λ·λ)·(f x·f x)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (G.Lapp f x) (hf x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (-(lam * f x)) _ _ (hf x)) ?_
    -- (−(λ f x))·(−(λ f x)) ≃ (λ f x)·(λ f x)
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (lam * f x) (-(lam * f x))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (lam * f x) (lam * f x))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv ((lam * f x) * (lam * f x))) ?_
    -- (λ f x)·(λ f x) ≃ λ·(f x·(λ·f x)) ≃ (λ·λ)·(f x·f x)  via assoc + rearr4
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv lam (f x) (lam * f x)) ?_
    exact rearr4 lam (f x) lam (f x)
  · exact G.E_const_mul (lam * lam) (pmul f f)

/-! ### THE TEMPLATE THEOREM:  CD(K) ⇒ every nonzero eigenvalue `λ ≥ K` -/

/-- **Curvature ⇒ gap magnitude (the template).**  If the generator satisfies
the curvature-dimension bound `CD(K)` in π-mean, then EVERY eigenfunction `f`
with eigenvalue `−λ` (`Lf = −λf`), positive eigenvalue `λ > 0`, and positive
`π`-variance `E[f²] > 0`, has `λ ≥ K`.  Pure finite `Q'` linear algebra via the
Dirichlet and Bochner identities — no time integral.  Hence the spectral gap
(smallest positive eigenvalue) is at least `K`. -/
theorem eigenvalue_ge_of_CD {K lam : Q'} (hCD : G.CD K)
    (f : Nat → Q') (hf : G.Eigen f lam)
    (hlam : (0 : Q') < lam) (hm : (0 : Q') < G.E (pmul f f)) :
    K ≤ lam := by
  -- the curvature inequality at this eigenfunction
  have hineq : K * G.E (G.Gamma1 f) ≤ G.E (G.Gamma2 f) := hCD f
  -- rewrite both sides with the eigen-identities to a common `(·)·(λ·m)` form
  -- m := E[f²];  E[Γ₁ f] ≃ λ·m,  E[Γ₂ f] ≃ λ²·m ≃ λ·(λ·m).
  have hD : (G.E (G.Gamma1 f)).eqv (lam * G.E (pmul f f)) := G.dirichlet_eigen f lam hf
  have hB : (G.E (G.Gamma2 f)).eqv ((lam * lam) * G.E (pmul f f)) := G.bochner_eigen f lam hf
  -- LHS: K·E[Γ₁ f] ≥ K·(λ·m)  (i.e. K·(λ·m) ≤ K·E[Γ₁ f])
  have hL : K * (lam * G.E (pmul f f)) ≤ K * G.E (G.Gamma1 f) :=
    Q'.le_of_eqv (Q'.mul_eqv_congr_left K _ _ (Q'.eqv_symm hD))
  -- RHS: E[Γ₂ f] ≤ λ²·m ≃ λ·(λ·m)
  have hR : G.E (G.Gamma2 f) ≤ lam * (lam * G.E (pmul f f)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hB)
      (Q'.le_of_eqv (Q'.mul_assoc_eqv lam lam (G.E (pmul f f))))
  -- chain: K·(λ·m) ≤ K·E[Γ₁ f] ≤ E[Γ₂ f] ≤ λ·(λ·m)
  have hchain : K * (lam * G.E (pmul f f)) ≤ lam * (lam * G.E (pmul f f)) :=
    Q'.le_trans' _ _ _ hL (Q'.le_trans' _ _ _ hineq hR)
  -- cancel the positive factor (λ·m) appearing on the right of both sides
  have hpos : (0 : Q') < lam * G.E (pmul f f) := mul_pos hlam hm
  exact le_of_mul_le_mul_right_pos hpos hchain

end RevGen

/-! ## Bridge to the LOCATED spectral gap

The generator bound `λ ≥ K` (energies bounded below by the curvature `K`)
becomes, for the transfer operator `P = I − sL`, the eigenvalue bound
`1 − sλ ≤ 1 − sK` for every excited mode, i.e. an excited spectrum `≤ 1 − sK`
strictly below the vacuum eigenvalue `1`.  Packaged as a `LocatedSpectralGap`
with margin `m = sK > 0`. -/

/-- `0 < m ⟹ 1 − m < 1` (the margin pushes the separator below the vacuum
eigenvalue `1`). -/
theorem one_sub_lt_one {m : Q'} (h : (0 : Q') < m) : (1 : Q') - m < (1 : Q') := by
  show ((1 : Q') - m).num * ((1 : Q').den : Int) < (1 : Q').num * (((1 : Q') - m).den : Int)
  have hmn : 0 < m.num := CReal.num_pos_of_pos h
  -- (1 - m) = 1 + (-m); compute its num/den via add_den_cast
  have hnum : ((1 : Q') - m).num = (1 : Int) * (m.den : Int) + (-m.num) * (1 : Int) := rfl
  have hden : (((1 : Q') - m).den : Int) = (1 : Int) * (m.den : Int) := by
    show (((1 : Q') + (-m)).den : Int) = (1 : Int) * (m.den : Int)
    rw [Q'.add_den_cast (1 : Q') (-m)]; rfl
  rw [hnum, hden]
  show ((1 : Int) * (m.den : Int) + (-m.num) * (1 : Int)) * (1 : Int)
      < (1 : Int) * ((1 : Int) * (m.den : Int))
  have hd : (0 : Int) < (m.den : Int) := by exact_mod_cast m.den_pos
  rw [Int.one_mul, Int.one_mul, Int.mul_one, Int.mul_one]
  -- m.den + (-m.num) < m.den  ⇔  -m.num < 0  ⇔  0 < m.num
  omega

/-- **Curvature ⇒ located gap (the bridge).**  Given a transfer-operator
spectral model `S` whose excited spectrum is bounded by `1 − m` (the curvature
margin `m = sK > 0` from the template), produce the located spectral-gap
witness with separator `1 − m < 1`.  This realizes the curvature lower bound
as a genuine located gap of positive MAGNITUDE `m` in transfer-eigenvalue
space. -/
def locatedGapOfMargin (S : SpectralGap.SpectralModel) (m : Q') (hm : (0 : Q') < m)
    (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - m)) : LocatedSpectralGap S where
  sep := (1 : Q') - m
  sep_lt_one := one_sub_lt_one hm
  bound := hbd

/-- The bridge's located gap has margin exactly the curvature margin `m`:
`gapMargin = 1 − (1 − m) = m > 0`.  (Definitional: `gapMargin = 1 − sep`.) -/
theorem locatedGapOfMargin_margin (S : SpectralGap.SpectralModel) (m : Q')
    (hm : (0 : Q') < m) (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - m)) :
    (locatedGapOfMargin S m hm hbd).gapMargin = (1 : Q') - ((1 : Q') - m) := rfl

/-! ## SANITY: a concrete 2-state reversible chain with a genuine positive gap

The simplest non-trivial reversible chain: two states, uniform `π = (½,½)`,
the symmetric rate-1 generator `L = [[−1, 1], [1, −1]]`.  It is a valid
`RevGen` (positive, reversible, zero row sums), its difference mode
`f = (1, −1)` is an eigenfunction with energy `λ = 2 > 0`, and its
`π`-variance is positive — so the template machinery applies non-vacuously
and the located-gap bridge yields a genuine positive margin. -/

/-- Uniform 2-state measure `π(0) = π(1) = ½` (other indices `½`, unused). -/
def pi2 : Nat → Q' := fun _ => half

/-- The symmetric rate-1 generator on two states, zero outside the two-state
block: `L(x,y) = 0` if `x ≥ 2` or `y ≥ 2`, else `−1` on the diagonal and `1`
off it.  Zeroing the out-of-range rows/columns keeps the (total) `RevGen`
hypotheses true everywhere while reading exactly the `2×2` block. -/
def L2 : Nat → Nat → Q' := fun x y =>
  if x < 2 ∧ y < 2 then (if x = y then (-1 : Q') else (1 : Q')) else (0 : Q')

/-- `x < 2 → x = 0 ∨ x = 1`. -/
theorem lt_two_cases {x : Nat} (h : x < 2) : x = 0 ∨ x = 1 := by omega

/-- `L2` is structurally symmetric: `L2 x y = L2 y x`. -/
theorem L2_symm_eq (x y : Nat) : L2 x y = L2 y x := by
  have hand : (x < 2 ∧ y < 2) ↔ (y < 2 ∧ x < 2) := ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have heq : (x = y) ↔ (y = x) := ⟨Eq.symm, Eq.symm⟩
  unfold L2
  by_cases hx : x < 2 ∧ y < 2
  · simp only [if_pos hx, if_pos (hand.mp hx)]
    by_cases h : x = y
    · simp only [if_pos h, if_pos (heq.mp h)]
    · simp only [if_neg h, if_neg (fun he => h (heq.mpr he))]
  · simp only [if_neg hx, if_neg (fun hc => hx (hand.mpr hc))]

theorem L2_symm (x y : Nat) : (L2 x y).eqv (L2 y x) := eqv_of_eq (L2_symm_eq x y)

/-- The two-state reversible chain. -/
def chain2 : RevGen where
  n := 2
  pi := pi2
  L := L2
  pi_pos := fun _ => by show (0 : Q') < half; decide
  reversible := fun x y => by
    show (half * L2 x y).eqv (half * L2 y x)
    exact Q'.mul_eqv_congr_left half (L2 x y) (L2 y x) (L2_symm x y)
  rowSumZero := fun x => by
    -- Σ_{y<2} L2 x y = (0 + L2 x 0) + L2 x 1 ≃ 0
    show ((0 : Q') + L2 x 0 + L2 x 1).eqv 0
    by_cases hx : x < 2
    · rcases lt_two_cases hx with h | h
      · subst h -- x = 0: L2 0 0 = −1, L2 0 1 = 1
        have e0 : L2 0 0 = (-1 : Q') := by unfold L2; rw [if_pos (by decide), if_pos rfl]
        have e1 : L2 0 1 = (1 : Q') := by unfold L2; rw [if_pos (by decide), if_neg (by decide)]
        rw [e0, e1]; decide
      · subst h -- x = 1: L2 1 0 = 1, L2 1 1 = −1
        have e0 : L2 1 0 = (1 : Q') := by unfold L2; rw [if_pos (by decide), if_neg (by decide)]
        have e1 : L2 1 1 = (-1 : Q') := by unfold L2; rw [if_pos (by decide), if_pos rfl]
        rw [e0, e1]; decide
    · -- x ≥ 2: the whole row is zero
      have e0 : L2 x 0 = (0 : Q') := by unfold L2; rw [if_neg (fun hc => hx hc.1)]
      have e1 : L2 x 1 = (0 : Q') := by unfold L2; rw [if_neg (fun hc => hx hc.1)]
      rw [e0, e1]; decide

/-- The difference-mode eigenfunction `f = (1, −1)` on the two states, zero
elsewhere (so the eigen-relation holds at every index, not just `< 2`). -/
def f2 : Nat → Q' := fun x => if x = 0 then (1 : Q') else (if x = 1 then (-1 : Q') else (0 : Q'))

/-- `f₂ = (1,−1)` is an eigenfunction of `chain2`'s generator with energy `2`
(`L f₂ = −2 f₂`): a GENUINE nonzero spectral mode. -/
theorem f2_eigen : chain2.Eigen f2 two := by
  intro x
  show (chain2.Lapp f2 x).eqv (-(two * f2 x))
  show (finSum (fun y => L2 x y * f2 y) 2).eqv (-(two * f2 x))
  -- (0 + L2 x 0 · f2 0) + L2 x 1 · f2 1
  show ((0 : Q') + L2 x 0 * f2 0 + L2 x 1 * f2 1).eqv (-(two * f2 x))
  have g0 : f2 0 = (1 : Q') := by unfold f2; rw [if_pos rfl]
  have g1 : f2 1 = (-1 : Q') := by unfold f2; rw [if_neg (by decide), if_pos rfl]
  by_cases hx : x < 2
  · rcases lt_two_cases hx with h | h
    · subst h -- x = 0: (−1)·1 + 1·(−1) = −2;  −(2·1) = −2
      have e0 : L2 0 0 = (-1 : Q') := by unfold L2; rw [if_pos (by decide), if_pos rfl]
      have e1 : L2 0 1 = (1 : Q') := by unfold L2; rw [if_pos (by decide), if_neg (by decide)]
      rw [e0, e1, g0, g1]; decide
    · subst h -- x = 1: 1·1 + (−1)·(−1) = 2;  −(2·(−1)) = 2
      have e0 : L2 1 0 = (1 : Q') := by unfold L2; rw [if_pos (by decide), if_neg (by decide)]
      have e1 : L2 1 1 = (-1 : Q') := by unfold L2; rw [if_pos (by decide), if_pos rfl]
      rw [e0, e1, g0, g1]; decide
  · -- x ≥ 2: the row is zero and f2 x = 0, so both sides are 0
    have e0 : L2 x 0 = (0 : Q') := by unfold L2; rw [if_neg (fun hc => hx hc.1)]
    have e1 : L2 x 1 = (0 : Q') := by unfold L2; rw [if_neg (fun hc => hx hc.1)]
    have gx : f2 x = (0 : Q') := by
      unfold f2; rw [if_neg (by omega), if_neg (by omega)]
    rw [e0, e1, gx]; decide

/-- The eigenvalue `2` of `chain2` is strictly positive — a genuine gap. -/
theorem chain2_eigenvalue_pos : (0 : Q') < two := by decide

/-- The `π`-variance of `f₂` on `chain2` is positive: `E[f₂²] = 1 > 0`. -/
theorem chain2_variance_pos : (0 : Q') < chain2.E (RevGen.pmul f2 f2) := by
  show (0 : Q') < finSum (fun x => pi2 x * (f2 x * f2 x)) 2
  show (0 : Q') < (0 : Q') + pi2 0 * (f2 0 * f2 0) + pi2 1 * (f2 1 * f2 1)
  have g0 : f2 0 = (1 : Q') := by unfold f2; rw [if_pos rfl]
  have g1 : f2 1 = (-1 : Q') := by unfold f2; rw [if_neg (by decide), if_pos rfl]
  show (0 : Q') < (0 : Q') + half * (f2 0 * f2 0) + half * (f2 1 * f2 1)
  rw [g0, g1]; decide

/-- **Sanity (non-vacuity).**  On the concrete chain `chain2`, IF the curvature
bound `CD K` holds then the genuine nonzero eigenvalue `2` of the difference
mode satisfies `K ≤ 2` — the template fires on a real reversible chain with a
real positive gap.  (For this chain `CD 2` is the sharp bound, so the gap
magnitude delivered is exactly the curvature `K = 2`.) -/
theorem chain2_template {K : Q'} (hCD : chain2.CD K) : K ≤ two :=
  chain2.eigenvalue_ge_of_CD hCD f2 f2_eigen chain2_eigenvalue_pos chain2_variance_pos

/-- **Sanity (located gap of positive magnitude).**  A concrete transfer-model
gap: any spectral model whose excited spectrum is `≤ ½` carries a located gap
with margin `½ > 0` — the curvature margin `m = sK` realized concretely
(here `m = ½`, e.g. `s = ¼`, `K = 2`). -/
def chain2_locatedGap (S : SpectralGap.SpectralModel)
    (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - half)) : LocatedSpectralGap S :=
  locatedGapOfMargin S half (by decide) hbd

end YMGap.Continuum.BakryEmery

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

-- The two integration-by-parts workhorses
#print axioms YMGap.Continuum.BakryEmery.RevGen.E_Lapp_zero
#print axioms YMGap.Continuum.BakryEmery.RevGen.E_self_adjoint
-- The Dirichlet and Bochner identities
#print axioms YMGap.Continuum.BakryEmery.RevGen.dirichlet
#print axioms YMGap.Continuum.BakryEmery.RevGen.bochner
#print axioms YMGap.Continuum.BakryEmery.RevGen.dirichlet_eigen
#print axioms YMGap.Continuum.BakryEmery.RevGen.bochner_eigen
-- The template: CD(K) ⇒ eigenvalue ≥ K (curvature ⇒ gap magnitude)
#print axioms YMGap.Continuum.BakryEmery.RevGen.eigenvalue_ge_of_CD
-- The located-gap bridge
#print axioms YMGap.Continuum.BakryEmery.locatedGapOfMargin
#print axioms YMGap.Continuum.BakryEmery.one_sub_lt_one
-- The concrete sanity inhabitant
#print axioms YMGap.Continuum.BakryEmery.chain2
#print axioms YMGap.Continuum.BakryEmery.f2_eigen
#print axioms YMGap.Continuum.BakryEmery.chain2_template
#print axioms YMGap.Continuum.BakryEmery.chain2_locatedGap
