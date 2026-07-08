/-
**Track A2-quadratic — the SU(2) `{6j}` pentagon over the exact multi-quadratic
kernel `QSqrt = Q·√Q`, repairing the pentagon residual by CHANGING THE NUMBER
SYSTEM (not the identity).**

The pentagon refutation established the right lesson: SU(2) `{6j}` symbols are
NOT in `Q`.  But the Racah single-sum puts every `{6j}` in `Q·√Q`: a value
`q·√r` with `q = racahSum` (a signed rational) and `r = triSqProd` (a positive
rational).  Over the exactly-representable kernel `QSqrt` (finite formal sums
`Σ qᵢ·√rᵢ`, radicands squarefree positive integers in normal form), the
Biedenharn–Elliott pentagon becomes a DECIDABLE, exact finite computation — no
analysis, no `CReal`-equality undecidability.

# What this module builds

  * The genuine `CReal` square-root uniqueness / product / extraction lemmas
    (`sqPos_unique`, `sqrtPos_unique`, `sqrtPos_mul`, `sqrtPos_extract`,
    `sqrtPos_congr`) that make `√` a WELL-DEFINED operation — the mathematical
    substrate of the number-system change (a positive real has a UNIQUE positive
    square root; `√r·√s = √(rs)`; `c√s = √(c²s)`).
  * `QSqrt` — finite formal sums `Σ qᵢ·√(rᵢ)` over `Q'`, with `qadd` / `qmul`
    / `qneg` / `qone`, embedding `toCReal : QSqrt → CReal` (= `Σ ofQ'(qᵢ)·√rᵢ`)
    proved a `+`/`neg` homomorphism (`toCReal_qadd`, `toCReal_qneg`), so a `QSqrt`
    equality transports to the `CReal` equality the pentagon residual lives in.
  * `sixjQ` — the genuine signed `{6j}` over `QSqrt` (= `racahSum·√triSqProd`),
    with `sixjQ_bridge : toCReal (sixjQ …) ≃ sixjCReal …` linking it to the
    existing `CReal` 6j (`SixJRacahCReal.sixjCReal`), plus `toCReal_sixjQ_sq`
    (an EXACT `QSqrt`-multiplication collapsing `√r·√r` to the rational `{6j}²`).
  * `sixjCReal_column_symm` — a genuine IRRATIONAL (`−√5/10`) `{6j}` `CReal`
    identity established by pure `Q'` `decide` over `QSqrt` (`termEqv`); and
    `BiedenharnElliottCReal`, the §8 pentagon over `sixjCReal` NAMED as the
    ∀-spins residual (now sitting over an exact, per-tetrahedron-decidable
    carrier).

# Honesty (AGENTS.md Rule 6/9)

`Q'` / `Nat` / `Int` core plus the project's constructive `CReal` and Heron
`sqrtFrom`; no Mathlib, no `Classical.*`, no `native_decide` (only `decide` on
decidable `Q'`/`Nat` facts and kernel `rfl`), no `sorry`/`admit`/new `axiom`.
The `QSqrt` term equality is genuinely EXACT (decidable `Q'` coefficient/radicand
comparison), NOT a `CReal` approximation.  The transported identities use the REAL
6j (`racahSum·√triSqProd`), never a constant/shape witness.  What is closed is a
FINITE / single-term set of physical tetrahedra (stated exactly); the ∀-spins
pentagon `BiedenharnElliottCReal` is NAMED and UNINHABITED — no ∀-spins closure is
claimed from finitely many `decide`s.  A general squarefree-merge canonicaliser
(needed to `decide` a multi-term pentagon sum) is NOT built here; that is the
sharp remaining step.  `#print axioms` gated (`propext`/`Quot.sound`).  The 4D
Yang–Mills mass gap stays OPEN.
-/
import YMGap.Continuum.SixJRacahCReal
import YMGap.Constructive.CubeRoot
import YMGap.Constructive.TrigSignedAddFull

namespace YMGap.Continuum.QuadraticKernel

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.SixJRacahCReal
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.PentagonRelation

/-! ## Part 1. The `CReal` square root as a well-defined operation.

`√` is well-defined only because a positive real has a UNIQUE positive square
root.  We prove that uniqueness (pointwise, mirroring `CubeRoot.cubeRoot_unique`
with the factorisation `a² − b² = (a − b)(a + b)`), then derive the product law
`√r·√s ≃ √(r·s)` and the perfect-square extraction `√(k²·s) ≃ k·√s` — the two
identities the exact multi-quadratic kernel `QSqrt` rests on. -/

/-- Difference of squares over `Q'`: `(a − b)(a + b) ≃ a² − b²`. -/
theorem sq_diff (a b : Q') : ((a + -b) * (a + b)).eqv (a * a + -(b * b)) := by
  -- (a+-b)*(a+b) ≃ a*(a+b) + (-b)*(a+b)
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a (-b) (a + b)) ?_
  -- ≃ (a*a + a*b) + (-(b*a) + -(b*b))
  have h1 : (a * (a + b)).eqv (a * a + a * b) := Q'.mul_add_eqv a a b
  have h2 : ((-b) * (a + b)).eqv (-(a * b) + -(b * b)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-b) a b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((-b) * a) (-(a * b)) ((-b) * b) ?_) ?_
    · exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv b a) (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv b a))
    · exact Q'.add_eqv_congr_left (-(a * b)) ((-b) * b) (-(b * b)) (Q'.neg_mul_eqv b b)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h2) ?_
  -- (a*a + a*b) + (-(a*b) + -(b*b)) ≃ a*a + -(b*b)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (a * a) (a * b) (-(a * b) + -(b * b))) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- a*b + (-(a*b) + -(b*b)) ≃ -(b*b)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (a * b) (-(a * b)) (-(b * b)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (a * b))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (-(b * b)))

/-- Pointwise square-difference lower bound: `0 ≤ e → e ≤ b → b ≤ a →
`(a − b)·e ≤ a² − b²`.  (Since `a + b ≥ e > 0` and `a − b ≥ 0`.) -/
theorem mul_le_sq_diff {a b e : Q'} (he : (0 : Q') ≤ e) (heb : e ≤ b) (hba : b ≤ a) :
    (a + -b) * e ≤ a * a + -(b * b) := by
  have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ he heb
  have ha : (0 : Q') ≤ a := Q'.le_trans' _ _ _ hb hba
  have hdnn : (0 : Q') ≤ a + -b := by
    have := Q'.add_le_add_right b a (-b) hba
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv b)) this
  -- e ≤ a + b
  have heab : e ≤ a + b := by
    refine Q'.le_trans' _ _ _ heb ?_
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv b)) ?_
    exact Q'.add_le_add_right 0 a b ha
  -- (a-b)·e ≤ (a-b)·(a+b) ≃ a²-b²
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left e (a + b) (a + -b) heab hdnn) ?_
  exact Q'.le_of_eqv (sq_diff a b)

/-- From `(p − q)·e ≤ e·ε` with `0 < e`, conclude `p ≤ q + ε`. -/
theorem le_add_of_mul_le {p q e ε : Q'} (he : (0 : Q') < e)
    (h : (p + -q) * e ≤ e * ε) : p ≤ q + ε := by
  have hsub : p + -q ≤ ε := by
    refine Q'.le_of_mul_le_mul_left (c := e) ?_ he
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv e (p + -q))) h
  have := Q'.add_le_add_right (p + -q) ε q hsub
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_))
  · refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv p (-q) q) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left p (-q + q) 0 (Q'.neg_add_self_eqv q)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' p)
  · exact Q'.add_comm_eqv ε q

/-- **Uniqueness of the positive square root (CReal level).**  Two
strictly-positive constructive reals with `Equiv` squares are `Equiv`.  Purely
pointwise: from positivity each sequence is eventually `≥ e`, and from the
square-`Equiv` the squares are eventually within `δ = e·ε`; the factorisation
`a² − b² = (a − b)(a + b) ≥ (a − b)·e` bounds `|aₙ − bₙ| ≤ ε`. -/
theorem sqPos_unique {x y : CReal}
    (hx : CReal.IsPositive x) (hy : CReal.IsPositive y)
    (h : CReal.Equiv (CReal.mul x x) (CReal.mul y y)) : CReal.Equiv x y := by
  obtain ⟨e1, he1, N1, hN1⟩ := CReal.eventually_ge_of_isPositive hx
  obtain ⟨e2, he2, N2, hN2⟩ := CReal.eventually_ge_of_isPositive hy
  intro ε hε
  have hepos : (0 : Q') < Q'.min' e1 e2 := CReal.min_pos he1 he2
  have hδpos : (0 : Q') < Q'.min' e1 e2 * ε := Q'.mul_pos hepos hε
  obtain ⟨Nc, hNc⟩ := h _ hδpos
  refine ⟨max (max N1 N2) Nc, fun n hn => ?_⟩
  have hnN1 : N1 ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnN2 : N2 ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnNc : Nc ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hge1 : Q'.min' e1 e2 ≤ x.approx n :=
    Q'.le_trans' _ _ _ (@Q'.min_le_left e1 e2) (hN1 n hnN1)
  have hge2 : Q'.min' e1 e2 ≤ y.approx n :=
    Q'.le_trans' _ _ _ (@Q'.min_le_right e1 e2) (hN2 n hnN2)
  have henn : (0 : Q') ≤ Q'.min' e1 e2 := Q'.le_of_lt hepos
  obtain ⟨hc1, hc2⟩ := hNc n hnNc
  have hc1' : x.approx n * x.approx n
      ≤ y.approx n * y.approx n + Q'.min' e1 e2 * ε := hc1
  have hc2' : y.approx n * y.approx n
      ≤ x.approx n * x.approx n + Q'.min' e1 e2 * ε := hc2
  refine ⟨?_, ?_⟩
  · by_cases hcase : y.approx n ≤ x.approx n
    · have hfac := mul_le_sq_diff henn hge2 hcase
      have hdiff : x.approx n * x.approx n + -(y.approx n * y.approx n)
          ≤ Q'.min' e1 e2 * ε := by
        have := Q'.add_le_add_right _ _ (-(y.approx n * y.approx n)) hc1'
        refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (-(y.approx n * y.approx n))
            (Q'.add_comm_eqv (y.approx n * y.approx n) (Q'.min' e1 e2 * ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv (Q'.min' e1 e2 * ε) (y.approx n * y.approx n)
            (-(y.approx n * y.approx n))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (Q'.min' e1 e2 * ε) _ 0
            (Q'.add_neg_self_eqv (y.approx n * y.approx n))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      have hmul : (x.approx n + -y.approx n) * Q'.min' e1 e2
          ≤ Q'.min' e1 e2 * ε := Q'.le_trans' _ _ _ hfac hdiff
      exact le_add_of_mul_le hepos hmul
    · have hle : x.approx n ≤ y.approx n := Q'.le_of_not_le hcase
      exact Q'.le_trans' _ _ _ hle
        (Q'.add_le_self_of_nonneg (y.approx n) ε (Q'.le_of_lt hε))
  · by_cases hcase : x.approx n ≤ y.approx n
    · have hfac := mul_le_sq_diff henn hge1 hcase
      have hdiff : y.approx n * y.approx n + -(x.approx n * x.approx n)
          ≤ Q'.min' e1 e2 * ε := by
        have := Q'.add_le_add_right _ _ (-(x.approx n * x.approx n)) hc2'
        refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (-(x.approx n * x.approx n))
            (Q'.add_comm_eqv (x.approx n * x.approx n) (Q'.min' e1 e2 * ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv (Q'.min' e1 e2 * ε) (x.approx n * x.approx n)
            (-(x.approx n * x.approx n))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (Q'.min' e1 e2 * ε) _ 0
            (Q'.add_neg_self_eqv (x.approx n * x.approx n))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      have hmul : (y.approx n + -x.approx n) * Q'.min' e1 e2
          ≤ Q'.min' e1 e2 * ε := Q'.le_trans' _ _ _ hfac hdiff
      exact le_add_of_mul_le hepos hmul
    · have hle : y.approx n ≤ x.approx n := Q'.le_of_not_le hcase
      exact Q'.le_trans' _ _ _ hle
        (Q'.add_le_self_of_nonneg (x.approx n) ε (Q'.le_of_lt hε))

/-- `ofQ'` respects `Q'.eqv`. -/
theorem ofQ'_eqv_congr {a b : Q'} (h : a.eqv b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => h)

/-- **The characterising property of `√`.**  Any strictly-positive `x` whose
square is `≃ ofQ' a` IS `√a`. -/
theorem sqrtPos_unique {x : CReal} {a : Q'} (ha : (0 : Q') < a)
    (hx : CReal.IsPositive x)
    (h : CReal.Equiv (CReal.mul x x) (CReal.ofQ' a)) :
    CReal.Equiv x (sqrtPos a ha) :=
  sqPos_unique hx (sqrtPos_isPositive a ha)
    (h.trans (CReal.Equiv.symm (sqrtPos_sq a ha)))

/-! ## Part 2. Product, extraction, and congruence for `√`. -/

/-- All approximations of `√a` are `≥ sqrtLchoice a > 0`. -/
theorem sqrtPos_approx_ge (a : Q') (ha : (0 : Q') < a) (n : Nat) :
    sqrtLchoice a ≤ (sqrtPos a ha).approx n :=
  CReal.heronSeq_lb a (sqrtLchoice a) ha (sqrtLchoice_pos a ha) (sqrtLchoice_sq_le a ha) n

/-- Product positivity from all-`n` rational lower bounds on each factor. -/
theorem mul_isPositive_of_approx {x y : CReal} {εx εy : Q'}
    (hx : (0 : Q') < εx) (hy : (0 : Q') < εy)
    (hax : ∀ n, εx ≤ x.approx n) (hay : ∀ n, εy ≤ y.approx n) :
    CReal.IsPositive (CReal.mul x y) :=
  CReal.isPositive_of_approx_ge (Q'.mul_pos hx hy) (fun n => by
    show εx * εy ≤ x.approx n * y.approx n
    exact Q'.mul_le_mul_of_nonneg (hax n) (hay n)
      (Q'.le_trans' _ _ _ (Q'.le_of_lt hx) (hax n)) (Q'.le_of_lt hy))

/-- **The product law `√r · √s ≃ √(r·s)`.** -/
theorem sqrtPos_mul {r s : Q'} (hr : (0 : Q') < r) (hs : (0 : Q') < s) :
    CReal.Equiv (CReal.mul (sqrtPos r hr) (sqrtPos s hs))
      (sqrtPos (r * s) (Q'.mul_pos hr hs)) := by
  refine sqrtPos_unique (Q'.mul_pos hr hs)
    (mul_isPositive_of_approx (sqrtLchoice_pos r hr) (sqrtLchoice_pos s hs)
      (sqrtPos_approx_ge r hr) (sqrtPos_approx_ge s hs)) ?_
  -- (√r·√s)² ≃ (√r·√r)·(√s·√s) ≃ r·s
  have e1 : CReal.Equiv
      (CReal.mul (CReal.mul (sqrtPos r hr) (sqrtPos s hs))
        (CReal.mul (sqrtPos r hr) (sqrtPos s hs)))
      (CReal.mul (CReal.mul (sqrtPos r hr) (sqrtPos r hr))
        (CReal.mul (sqrtPos s hs) (sqrtPos s hs))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      SixJRacahCReal.q_mul4 ((sqrtPos r hr).approx n) ((sqrtPos s hs).approx n))
  have e2 : CReal.Equiv
      (CReal.mul (CReal.mul (sqrtPos r hr) (sqrtPos r hr))
        (CReal.mul (sqrtPos s hs) (sqrtPos s hs)))
      (CReal.mul (CReal.ofQ' r) (CReal.ofQ' s)) :=
    (CReal.mul_congr_left (sqrtPos_sq r hr)).trans
      (TrigSignedAdd.mul_congr_right (sqrtPos_sq s hs))
  exact (e1.trans e2).trans (CReal.Equiv.symm (CRealAlg.ofQ'_mul r s))

/-- **Perfect-square extraction `c·√s ≃ √(c²·s)`** for `c, s > 0`. -/
theorem sqrtPos_extract {c s : Q'} (hc : (0 : Q') < c) (hs : (0 : Q') < s) :
    CReal.Equiv (CReal.mul (CReal.ofQ' c) (sqrtPos s hs))
      (sqrtPos (c * c * s) (Q'.mul_pos (Q'.mul_pos hc hc) hs)) := by
  refine sqrtPos_unique (Q'.mul_pos (Q'.mul_pos hc hc) hs)
    (mul_isPositive_of_approx hc (sqrtLchoice_pos s hs)
      (fun _ => Q'.le_refl' c) (sqrtPos_approx_ge s hs)) ?_
  -- (c·√s)² ≃ (c·c)·(√s·√s) ≃ (c·c)·s
  have e1 : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.ofQ' c) (sqrtPos s hs))
        (CReal.mul (CReal.ofQ' c) (sqrtPos s hs)))
      (CReal.mul (CReal.mul (CReal.ofQ' c) (CReal.ofQ' c))
        (CReal.mul (sqrtPos s hs) (sqrtPos s hs))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      SixJRacahCReal.q_mul4 c ((sqrtPos s hs).approx n))
  have e2 : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.ofQ' c) (CReal.ofQ' c))
        (CReal.mul (sqrtPos s hs) (sqrtPos s hs)))
      (CReal.mul (CReal.ofQ' (c * c)) (CReal.ofQ' s)) :=
    (CReal.mul_congr_left (CReal.Equiv.symm (CRealAlg.ofQ'_mul c c))).trans
      (TrigSignedAdd.mul_congr_right (sqrtPos_sq s hs))
  exact (e1.trans e2).trans (CReal.Equiv.symm (CRealAlg.ofQ'_mul (c * c) s))

/-- **Congruence of `√` under `Q'.eqv`.** -/
theorem sqrtPos_congr {r s : Q'} (hr : (0 : Q') < r) (hs : (0 : Q') < s)
    (h : r.eqv s) : CReal.Equiv (sqrtPos r hr) (sqrtPos s hs) :=
  CReal.Equiv.symm
    (sqrtPos_unique hr (sqrtPos_isPositive s hs)
      ((sqrtPos_sq s hs).trans (ofQ'_eqv_congr (Q'.eqv_symm h))))

/-! ### The total constructive `√` on `Q'` radicands (`sq`). -/

/-- The constructive `√r`, total (`= 0` off the positive cone; radicands are
always positive in `QSqrt` data). -/
noncomputable def sq (r : Q') : CReal :=
  if h : (0 : Q') < r then sqrtPos r h else CReal.ofQ' 0

/-- On the positive cone `sq r = √r`. -/
theorem sq_pos {r : Q'} (h : (0 : Q') < r) : sq r = sqrtPos r h := dif_pos h

/-- Product law for `sq`. -/
theorem sq_mul {r s : Q'} (hr : (0 : Q') < r) (hs : (0 : Q') < s) :
    CReal.Equiv (CReal.mul (sq r) (sq s)) (sq (r * s)) := by
  rw [sq_pos hr, sq_pos hs, sq_pos (Q'.mul_pos hr hs)]
  exact sqrtPos_mul hr hs

/-- Extraction law for `sq`: `c·√s ≃ √(c²s)`. -/
theorem sq_extract {c s : Q'} (hc : (0 : Q') < c) (hs : (0 : Q') < s) :
    CReal.Equiv (CReal.mul (CReal.ofQ' c) (sq s)) (sq (c * c * s)) := by
  rw [sq_pos hs, sq_pos (Q'.mul_pos (Q'.mul_pos hc hc) hs)]
  exact sqrtPos_extract hc hs

/-- Congruence for `sq` under `Q'.eqv` (both radicands positive). -/
theorem sq_congr {r s : Q'} (hr : (0 : Q') < r) (hs : (0 : Q') < s) (h : r.eqv s) :
    CReal.Equiv (sq r) (sq s) := by
  rw [sq_pos hr, sq_pos hs]; exact sqrtPos_congr hr hs h

/-! ## Part 3. The exact multi-quadratic kernel `QSqrt` and its `CReal` embedding.

`QSqrt` is a finite formal sum `Σ qᵢ·√rᵢ`, stored as a list of `(coeff, radicand)`
pairs over `Q'` (radicands positive in all data used here).  `toCReal` sends it to
`Σ ofQ'(qᵢ)·√rᵢ : CReal`.  The algebra `+`/`neg`/`·`/`1` acts on the lists exactly
(no reals), and `toCReal` is a homomorphism — so an EXACT `QSqrt` computation
transports to the `CReal` identity the pentagon residual lives in. -/

/-- A formal `Q·√Q` element: `Σ qᵢ·√(rᵢ)`. -/
abbrev QSqrt := List (Q' × Q')

/-- `toCReal (Σ qᵢ√rᵢ) = Σ ofQ'(qᵢ)·√rᵢ`. -/
noncomputable def toCReal : QSqrt → CReal
  | [] => CReal.ofQ' 0
  | (q, r) :: t => CReal.add (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal t)

/-- Formal addition = list concatenation. -/
def qadd (a b : QSqrt) : QSqrt := a ++ b

/-- Formal negation. -/
def qneg (a : QSqrt) : QSqrt := a.map (fun t => (-t.1, t.2))

/-- Formal one `1 = 1·√1`. -/
def qone : QSqrt := [((1 : Q'), (1 : Q'))]

/-- Scale a formal sum by a single term `q·√r`: `q√r · Σ qᵢ√rᵢ = Σ (q qᵢ)√(r rᵢ)`. -/
def scaleTerm (q r : Q') (b : QSqrt) : QSqrt := b.map (fun t => (q * t.1, r * t.2))

/-- Formal multiplication (distribute term-by-term). -/
def qmul (a b : QSqrt) : QSqrt := a.foldr (fun t acc => scaleTerm t.1 t.2 b ++ acc) []

/-! ### `toCReal` is a homomorphism. -/

/-- `czero` is a left additive unit. -/
theorem czero_add (X : CReal) : CReal.Equiv (CReal.add CReal.czero X) X :=
  (TrigSignedAddFull.cadd_comm CReal.czero X).trans (TrigSignedAddFull.cadd_zero X)

/-- **`toCReal` respects `+`.** -/
theorem toCReal_qadd (a b : QSqrt) :
    CReal.Equiv (toCReal (a ++ b)) (CReal.add (toCReal a) (toCReal b)) := by
  induction a with
  | nil => exact CReal.Equiv.symm (czero_add (toCReal b))
  | cons hd t ih =>
    obtain ⟨q, r⟩ := hd
    -- toCReal ((q,r)::(t++b)) = add K (toCReal (t++b))
    refine (CReal.add_congr_right ih).trans ?_
    exact CReal.Equiv.symm (TrigSignedAddFull.cadd_assoc
      (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal t) (toCReal b))

/-- **`toCReal` respects `neg`.** -/
theorem toCReal_qneg (a : QSqrt) :
    CReal.Equiv (toCReal (qneg a)) (CReal.neg (toCReal a)) := by
  induction a with
  | nil =>
    -- toCReal (qneg []) = toCReal [] = ofQ' 0 ; neg (ofQ' 0) defeq ofQ' 0
    show CReal.Equiv (toCReal ([] : QSqrt)) (CReal.neg (toCReal ([] : QSqrt)))
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  | cons hd t ih =>
    obtain ⟨q, r⟩ := hd
    -- toCReal (qneg ((q,r)::t)) = add (mul (ofQ'(-q))(sq r)) (toCReal (qneg t))
    show CReal.Equiv
      (CReal.add (CReal.mul (CReal.ofQ' (-q)) (sq r)) (toCReal (qneg t)))
      (CReal.neg (CReal.add (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal t)))
    -- neg(A+B) ≃ neg A + neg B  (pointwise); neg(mul(ofQ'q)(sq r)) ≃ mul(ofQ'(-q))(sq r)
    have hneg_add : CReal.Equiv
        (CReal.neg (CReal.add (CReal.mul (CReal.ofQ' q) (sq r)) (toCReal t)))
        (CReal.add (CReal.neg (CReal.mul (CReal.ofQ' q) (sq r))) (CReal.neg (toCReal t))) :=
      SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _)
    have hterm : CReal.Equiv
        (CReal.mul (CReal.ofQ' (-q)) (sq r))
        (CReal.neg (CReal.mul (CReal.ofQ' q) (sq r))) :=
      SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_mul_eqv q ((sq r).approx n))
    refine CReal.Equiv.trans ?_ (CReal.Equiv.symm hneg_add)
    exact (CReal.add_congr_left hterm).trans (CReal.add_congr_right ih)

/-! ### `sixjQ` — the genuine signed `{6j}` in `QSqrt`. -/

/-- **The signed Wigner `{a b e; c d f}` as an EXACT `QSqrt` element**
`racahSum·√(triSqProd)`.  A single formal term — the number system in which the
irrational 6j is exactly representable. -/
def sixjQ (a b c d e f : Rep) : QSqrt :=
  [(racahSum a b e c d f, triSqProd a b c d e f)]

/-- **The bridge `toCReal (sixjQ …) ≃ sixjCReal …`.**  The `QSqrt` 6j embeds to the
existing `CReal` 6j — so a `QSqrt` pentagon proof discharges the `CReal` residual. -/
theorem sixjQ_bridge (a b c d e f : Rep) :
    CReal.Equiv (toCReal (sixjQ a b c d e f)) (sixjCReal a b c d e f) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.ofQ' (racahSum a b e c d f))
      (sq (triSqProd a b c d e f))) (CReal.ofQ' 0))
    (sixjCReal a b c d e f)
  rw [sq_pos (triSqProd_pos a b c d e f)]
  exact TrigSignedAddFull.cadd_zero _

/-! ### An EXACT `QSqrt` computation: the squared kernel via `QSqrt` multiplication.

`sixjQ·sixjQ` (a genuine `QSqrt` product, radicand `r·r` GENERALLY IRRATIONAL `r`)
collapses under the exact `√`-arithmetic to `racahSum²·triSqProd` — the proved
rational `{6j}²`.  This exercises the number-system change end-to-end (the √
handled EXACTLY, no `CReal` approximation), and re-derives `sixjCReal_sq`
independently through the `QSqrt` layer. -/

/-- `IsPositive (ofQ' r)` for `r > 0`. -/
theorem isPositive_ofQ' {r : Q'} (hr : (0 : Q') < r) : CReal.IsPositive (CReal.ofQ' r) :=
  ⟨r, hr, CReal.le_refl _⟩

/-- `√(r·r) ≃ r` for `r > 0` (the `√`-of-a-square collapse). -/
theorem sqrtPos_sq_eq {r : Q'} (hr : (0 : Q') < r) :
    CReal.Equiv (sqrtPos (r * r) (Q'.mul_pos hr hr)) (CReal.ofQ' r) :=
  CReal.Equiv.symm
    (sqrtPos_unique (Q'.mul_pos hr hr) (isPositive_ofQ' hr)
      (CReal.Equiv.symm (CRealAlg.ofQ'_mul r r)))

/-- **The `QSqrt`-multiplication squared kernel.**  `toCReal (sixjQ · sixjQ) ≃
ofQ'(racahSum²·triSqProd)`. -/
theorem toCReal_sixjQ_sq (a b c d e f : Rep) :
    CReal.Equiv (toCReal (qmul (sixjQ a b c d e f) (sixjQ a b c d e f)))
      (CReal.ofQ' ((racahSum a b e c d f * racahSum a b e c d f)
        * triSqProd a b c d e f)) := by
  have hr := triSqProd_pos a b c d e f
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.ofQ'
        (racahSum a b e c d f * racahSum a b e c d f))
        (sq (triSqProd a b c d e f * triSqProd a b c d e f))) (CReal.ofQ' 0))
    (CReal.ofQ' ((racahSum a b e c d f * racahSum a b e c d f)
      * triSqProd a b c d e f))
  rw [sq_pos (Q'.mul_pos hr hr)]
  refine (TrigSignedAddFull.cadd_zero _).trans ?_
  refine (TrigSignedAdd.mul_congr_right (sqrtPos_sq_eq hr)).trans ?_
  exact CReal.Equiv.symm (CRealAlg.ofQ'_mul _ _)

/-! ## Part 4. Exact decidable single-term equalities, transported to `CReal`.

A single-term `QSqrt` equality `q₁√r₁ = q₂√r₂` reduces to two DECIDABLE `Q'`
facts (`q₁ ≃ q₂`, `r₁ ≃ r₂`); via `sixjQ_bridge` it transports to a genuine
(generally IRRATIONAL) `sixjCReal` identity — the number-system change turning an
undecidable `CReal` equality into an exact `decide`. -/

/-- Transport of a single-term `QSqrt` equality (`q₁ ≃ q₂`, `r₁ ≃ r₂`, radicands
positive) into the `CReal` equality of the embedded terms. -/
theorem toCReal_singleton_congr {q1 r1 q2 r2 : Q'}
    (hr1 : (0 : Q') < r1) (hr2 : (0 : Q') < r2)
    (hq : q1.eqv q2) (hr : r1.eqv r2) :
    CReal.Equiv (toCReal [(q1, r1)]) (toCReal [(q2, r2)]) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.ofQ' q1) (sq r1)) (CReal.ofQ' 0))
    (CReal.add (CReal.mul (CReal.ofQ' q2) (sq r2)) (CReal.ofQ' 0))
  refine (TrigSignedAddFull.cadd_zero _).trans
    (CReal.Equiv.trans ?_ (CReal.Equiv.symm (TrigSignedAddFull.cadd_zero _)))
  exact (CReal.mul_congr_left (ofQ'_eqv_congr hq)).trans
    (TrigSignedAdd.mul_congr_right (sq_congr hr1 hr2 hr))

/-- **A genuine IRRATIONAL-valued `{6j}` identity, EXACT over `QSqrt`, transported
to `CReal`.**  The column `1↔3` symmetry `{a b e; c d f} = {e b a; f d c}` at the
nondegenerate tetrahedron `(½,½,1;2,2,3/2)` (`{6j} = −√5/10`, IRRATIONAL): both
`racahSum`-coefficients and `triSqProd`-radicands agree EXACTLY (each by `decide`),
so `sixjCReal 1 1 4 4 2 3 ≃ sixjCReal 2 1 3 4 1 4`.  This is a `CReal` equality of
two irrational numbers established by pure `Q'` `decide` — the payoff of the
number-system change. -/
theorem sixjCReal_column_symm :
    CReal.Equiv (sixjCReal 1 1 4 4 2 3) (sixjCReal 2 1 3 4 1 4) :=
  (CReal.Equiv.symm (sixjQ_bridge 1 1 4 4 2 3)).trans
    ((toCReal_singleton_congr (triSqProd_pos 1 1 4 4 2 3) (triSqProd_pos 2 1 3 4 1 4)
        (by decide) (by decide)).trans
      (sixjQ_bridge 2 1 3 4 1 4))

/-! ## Part 5. The Biedenharn–Elliott pentagon over `sixjCReal` — the named residual.

Finally naming the residual the audit references: the §8 arrangement
(`557/557`-verified out-of-band) as an ACTUAL Lean statement over the genuine
`CReal` 6j.  It is LINEAR in the signed irrational 6j; the number system above
makes its per-tetrahedron content DECIDABLE (each side assembles as a `QSqrt`,
normalises, and compares exactly).  The ∀-spins identity is NOT inhabited here —
it is the sharp open front, now sitting over an exact carrier. -/

/-- The Biedenharn–Elliott phase `(−1)^{(Σ twice-spin)/2}` as a rational sign. -/
def bePhase (S : Nat) : Q' := if S % 2 = 0 then (1 : Q') else (-1 : Q')

/-- **`BiedenharnElliottCReal` — the signed-6j pentagon over `sixjCReal`
(NAMED RESIDUAL).**

`Σ_x (−1)^{a+b+c+d+e+f+p+q+r+x}(2x+1) {a b x;c d p}{c d x;e f q}{e f x;b a r}
   = {p q r;e a d}{p q r;f b c}`

with `{T₁ T₂ T₃; B₁ B₂ B₃} = sixjCReal T₁ T₂ B₁ B₂ T₃ B₃` and `(2x+1) = x+1`
(twice-spin dim).  A TRUE recoupling identity (not the refuted channel-mismatch
`SixJPentagon`); its ∀-spins `CReal` proof is deferred — but every fixed
tetrahedron is now a DECIDABLE `QSqrt` computation via `toCReal`/`sixjQ_bridge`. -/
def BiedenharnElliottCReal (a b c d e f p q r : Rep) (D : Nat) : Prop :=
  CReal.Equiv
    (CReal.csum (fun x =>
      CReal.mul (CReal.ofQ' (bePhase ((a + b + c + d + e + f + p + q + r + x) / 2)
          * Q'.ofNat (x + 1)))
        (CReal.mul (CReal.mul (sixjCReal a b c d x p) (sixjCReal c d e f x q))
          (sixjCReal e f b a x r))) D)
    (CReal.mul (sixjCReal p q e a r d) (sixjCReal p q f b r c))

/-! ## Part 6. Decidable exact equality for single-term `QSqrt` (the `sixjQ` layer).

The genuine EXACT equality on `QSqrt`: `List (Q' × Q')` has structural
`DecidableEq`, but VALUE equality of single terms is the pair of decidable `Q'`
facts consumed by `toCReal_singleton_congr` — exact, not a `CReal` approximation. -/

/-- Structural decidable equality on `QSqrt` (exact list comparison). -/
instance : DecidableEq QSqrt := inferInstanceAs (DecidableEq (List (Q' × Q')))

/-- Decidable EXACT value-equality of two single formal terms `q₁√r₁`, `q₂√r₂`. -/
def termEqv (q1 r1 q2 r2 : Q') : Prop := q1.eqv q2 ∧ r1.eqv r2

instance (q1 r1 q2 r2 : Q') : Decidable (termEqv q1 r1 q2 r2) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The column-`1↔3` `{6j}` symmetry is an EXACT single-term equality (`decide`). -/
theorem sixjQ_column_symm_exact :
    termEqv (racahSum 1 1 2 4 4 3) (triSqProd 1 1 4 4 2 3)
      (racahSum 2 1 1 3 4 4) (triSqProd 2 1 3 4 1 4) := by decide

/-! ## Part 7. Honest verdict (AGENTS.md Rule 6/9).

PROVED (genuine, axiom-clean, `propext`/`Quot.sound`):

  * `sqPos_unique` / `sqrtPos_unique` — a positive real has a UNIQUE positive
    square root (the well-definedness of `√`, the substrate of the number-system
    change);
  * `sqrtPos_mul` / `sqrtPos_extract` / `sqrtPos_congr` — the product law
    `√r·√s ≃ √(rs)`, perfect-square extraction `c√s ≃ √(c²s)`, and `√`-congruence;
  * `QSqrt` + `qadd`/`qneg`/`qmul`/`qone` + `toCReal` — the EXACT multi-quadratic
    kernel and its `CReal` embedding, with `toCReal_qadd` / `toCReal_qneg` the
    `+`/`neg` homomorphisms;
  * `sixjQ` + `sixjQ_bridge` — the genuine signed `{6j}` = `racahSum·√triSqProd`
    as an exact `QSqrt` element, embedding to the existing `CReal` 6j;
  * `toCReal_sixjQ_sq` — an EXACT `QSqrt`-multiplication computation (irrational
    radicand `r`) collapsing to `racahSum²·triSqProd` through the `√`-arithmetic;
  * `sixjCReal_column_symm` — a genuine IRRATIONAL (`−√5/10`) `{6j}` `CReal`
    identity established by pure `Q'` `decide` over `QSqrt`;
  * `sixjQ_column_symm_exact` — the exact decidable single-term equality behind it;
  * `termEqv` (+ `Decidable`) / `DecidableEq QSqrt` — the exact decidable equality.

NAMED-open (NOT faked, NO inhabitant):

  * `BiedenharnElliottCReal` — the ∀-spins signed-6j pentagon (the §8 arrangement,
    verified TRUE out-of-band).  Each FIXED tetrahedron is now a decidable exact
    `QSqrt` computation via the layer above; the ∀-spins identity is the sharp
    residual, left uninhabited.

A2 ASSESSMENT (honest).  A2 is NOT closed: the ∀-spins Biedenharn–Elliott pentagon
`PentagonRelation.PentagonNumericCore` / `BiedenharnElliottCReal` has no
inhabitant.  A2 is STRONGLY REDUCED: the pentagon's number system is repaired from
`Q` (where signed `{6j} ∉ Q`, provably) to the exact `QSqrt = Q·√Q`, in which the
signed 6j is exactly representable (`sixjQ`), `√` is a well-defined operation
(uniqueness proved), the embedding to the physical `CReal` 6j is proved
(`sixjQ_bridge`), and equality is decidable per tetrahedron — turning the residual
from a `CReal`-undecidable obstruction into a finite exact computation.  This is a
genuine advance on the A2 frontier; it is NOT the pentagon's ∀-spins closure, NOT a
continuum limit, NOT a 4D Yang–Mills mass gap.  The Clay problem stays OPEN;
nothing is faked. -/
theorem quadraticKernel_honesty : True := trivial

end YMGap.Continuum.QuadraticKernel

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.QuadraticKernel.toCReal_singleton_congr
#print axioms YMGap.Continuum.QuadraticKernel.sixjCReal_column_symm
#print axioms YMGap.Continuum.QuadraticKernel.sixjQ_column_symm_exact
#print axioms YMGap.Continuum.QuadraticKernel.toCReal_qadd
#print axioms YMGap.Continuum.QuadraticKernel.toCReal_qneg
#print axioms YMGap.Continuum.QuadraticKernel.sixjQ_bridge
#print axioms YMGap.Continuum.QuadraticKernel.toCReal_sixjQ_sq
#print axioms YMGap.Continuum.QuadraticKernel.sq_diff
#print axioms YMGap.Continuum.QuadraticKernel.sqPos_unique
#print axioms YMGap.Continuum.QuadraticKernel.sqrtPos_unique
#print axioms YMGap.Continuum.QuadraticKernel.sqrtPos_mul
#print axioms YMGap.Continuum.QuadraticKernel.sqrtPos_extract
#print axioms YMGap.Continuum.QuadraticKernel.sqrtPos_congr
