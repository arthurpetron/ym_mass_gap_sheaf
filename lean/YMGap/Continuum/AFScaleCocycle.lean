/-
Track B / R2 — **the asymptotic-freedom scale cocycle**: the bridge that
DISCHARGES the dimensional-transmutation "running is real" input from the
two-loop AF certificate.

# What this module delivers

The scale-sheaf anomaly carries the RG-invariant physical scale (the Λ_QCD
analog of dimensional transmutation) as a Čech 1-cocycle on the thin nerve of
the category of RG scales.  Its global nontriviality — that the accumulated
running class does NOT collapse to the trivial scale `1` — rests on a single
external predicate: that SOME RG step carries genuine running (a step factor not
semantically `1`).  Upstream that predicate is the *named open input*
"the β-function does not vanish": one cannot conclude a nontrivial scale class
without first knowing the coupling actually runs.

Here that input is turned into a THEOREM.  From an `AFTrajectoryCertificate` —
the two-loop AF flow `τ_{k+1} = τ_k − β·τ_k² + O(τ_k³)` packaged as DATA with
`β > 0`, an explicit cubic remainder, and the smallness window — we build a
genuine scale cocycle and PROVE its running steps differ from `1`, because the
positive two-loop coefficient `β > 0` forces the log-coupling to *strictly
decrease*: `τ_{k+1} < τ_k`.  Asymptotic freedom (`β > 0`) MEANS the coupling
runs, and a running coupling is exactly a nontrivial scale cocycle.

# The cocycle (the honest running factor)

The per-step running factor is the ratio of consecutive log-couplings along the
AF trajectory,

      t_k  :=  τ_{k+1} / τ_k          (constructive `Q'.divPos`, `> 0`),

restricted to the AF window `k ≥ k0` where the certificate's small-`τ` regime
holds (off-window steps are set to the trivial scale `1`, carrying no running).
This `t_k` is a positive scale ratio, and `t_k ≃ 1` iff `τ_{k+1} ≃ τ_k`.

# What is PROVED here (all genuine, no `sorry`/`axiom`)

  * `afCocycle` — a bona fide `ScaleSheaf.ScaleCocycle` built from the
    certificate, with each running factor a positive `Q'.divPos` ratio.
  * `strict_drop` — `β > 0` ⇒ the coupling strictly decreases on the AF window:
    `τ_{k+1} < τ_k` (the `−βτ²` term, dominated only up to half by the cubic
    remainder via the certificate's drop lemma, leaves a genuine negative slope).
  * `af_step_ne_one` — consequently the running factor at any in-window step is
    NOT semantically `1`: `¬ (afCocycle.t k).eqv 1`.  This is the genuine
    content of asymptotic freedom at the level of the scale cocycle.
  * `af_BetaNonzero` — **THE PAYOFF.**  `ScaleSheaf.BetaNonzero afCocycle`,
    proved directly from the certificate's `β > 0` with NO named hypothesis.
    The dimensional-transmutation "running is real" input is now a THEOREM.
  * `af_scale_nontrivial` — composing with `nontrivial_of_step_ne_one`, the AF
    scale class is NOT globally trivial, UNCONDITIONALLY for the AF trajectory.
  * `afCocycle_Lambda_one_step` — the Λ connection at the edge level: the
    one-step accumulated class `Lambda k (k+1)` is exactly the coupling ratio
    `t_k = τ_{k+1}/τ_k`, and the in-window step's class is nontrivial.

# What stays NAMED (honest)

This module discharges the *dimensional-transmutation "running is real"* input:
that the AF scale cocycle is globally nontrivial.  It does NOT touch the
continuum limit of the accumulated class.  The finiteness/positivity of the
`a → 0` limit of `Lambda` (the genuine continuum Λ as a located real number)
remains the named continuum wall; the structural cocycle identities relating
`Lambda` to the telescoped coupling ratio are exact at fixed spacing and are
recorded here, with the continuum endpoint left explicitly external.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'` arithmetic (`divPos` and its order characterizations, the certificate's
drop lemma, reused `eqv`/order lemmas) plus the structural cocycle laws of the
scale sheaf.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.AFTrajectoryCertificate
import YMGap.Categorical.ScaleSheaf

namespace YMGap.Continuum.AFScaleCocycle

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Categorical.ScaleSheaf

/-! ## 0. Small order glue (local, axiom-clean)

The two strict-order facts we need that are not in the foundation namespace:
`<`-then-`≤` transitivity, and `<` excludes `eqv`. -/

/-- `a < b` and `b ≤ c` gives `a < c` (re-derived locally from the `Int`
cross-product order). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (b.den : Int)) * (a.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    rwa [hr] at this
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) := by
    have hcomm : (c.num * (b.den : Int)) * (a.den : Int)
               = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    exact Int.lt_of_lt_of_le s1 (by rw [hcomm] at s2; exact s2)
  have hb : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  exact Int.lt_of_mul_lt_mul_right s3 (Int.le_of_lt hb)

/-- A strict order excludes semantic equivalence: `a < b ⟹ ¬ a.eqv b`.
`<` is `a.num·b.den < b.num·a.den`; `eqv` is the corresponding `=`; these are
incompatible on `Int`. -/
theorem not_eqv_of_lt {a b : Q'} (h : a < b) : ¬ a.eqv b := by
  intro he
  have hlt : a.num * (b.den : Int) < b.num * (a.den : Int) := h
  have heq : a.num * (b.den : Int) = b.num * (a.den : Int) := he
  exact (Int.lt_irrefl _) (heq ▸ hlt)

/-- `0 < q ⟹ 0 < q.num` (local, axiom-clean). -/
theorem num_pos_of_pos {q : Q'} (hq : (0 : Q') < q) : (0 : Int) < q.num := by
  have h : (0 : Int) * (q.den : Int) < q.num * (1 : Int) := hq
  rw [Int.zero_mul, Int.mul_one] at h; exact h

/-- Strict left multiplication by a positive factor: `0 < c → a < b → c*a < c*b`
(local copy; the foundation copy lives in a module not on this import path). -/
theorem mul_lt_mul_of_pos_left {a b c : Q'} (hc : (0 : Q') < c) (hab : a < b) :
    c * a < c * b := by
  show (c * a).num * ((c * b).den : Int) < (c * b).num * ((c * a).den : Int)
  rw [show (c * a).num = c.num * a.num from rfl,
      show (c * b).num = c.num * b.num from rfl,
      Q'.mul_den_cast c b, Q'.mul_den_cast c a]
  have hcn : 0 < c.num := num_pos_of_pos hc
  have habn : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have e1 : (c.num * a.num) * ((c.den : Int) * (b.den : Int))
          = (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by ac_rfl
  have e2 : (c.num * b.num) * ((c.den : Int) * (a.den : Int))
          = (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by ac_rfl
  rw [e1, e2]
  exact Int.mul_lt_mul_of_pos_left habn
    (Int.mul_pos hcn (by exact_mod_cast c.den_pos))

/-! ## 1. The strict drop: `β > 0` forces the coupling to run

The certificate's `drop` lemma gives the contracting bound
`τ_{k+1} ≤ τ_k·(1 − (β/2)·τ_k)`.  Since `(β/2)·τ_k > 0`, the bracket is
strictly below `1`, so `τ_k·(1 − (β/2)·τ_k) < τ_k`: the coupling STRICTLY
decreases.  This is the precise sense in which `β > 0` (asymptotic freedom)
means the coupling genuinely runs. -/

/-- **The strict drop.**  On the AF window `k ≥ k0`, `τ_{k+1} < τ_k`.
From `drop` (`τ_{k+1} ≤ τ_k·(1 − (β/2)·τ_k)`) and the strict bound
`τ_k·(1 − (β/2)·τ_k) < τ_k` (because `0 < (β/2)·τ_k`, so the bracket is `< 1`,
and `τ_k > 0`). -/
theorem strict_drop (C : AFTrajectoryCertificate) (k : Nat) (hk : C.k0 ≤ k) :
    C.τ (k + 1) < C.τ k := by
  -- The contracting bound.
  have hdrop : C.τ (k + 1) ≤ C.τ k * (1 - halfBeta C.β * C.τ k) := drop C k hk
  -- 0 < (β/2)·τ_k.
  have hctk : (0 : Q') < halfBeta C.β * C.τ k :=
    Q'.mul_pos (halfBeta_pos C.β_pos) (C.τ_pos k)
  -- so 1 − (β/2)·τ_k < 1.
  have hbracket : (1 : Q') - halfBeta C.β * C.τ k < 1 := one_sub_lt_one hctk
  -- τ_k·(1 − (β/2)·τ_k) < τ_k·1  (strict left-mult by τ_k > 0).
  have hmul : C.τ k * (1 - halfBeta C.β * C.τ k) < C.τ k * 1 :=
    mul_lt_mul_of_pos_left (C.τ_pos k) hbracket
  -- τ_k·1 ≃ τ_k, so τ_k·(1 − (β/2)·τ_k) < τ_k.
  have hstrict : C.τ k * (1 - halfBeta C.β * C.τ k) < C.τ k :=
    lt_of_lt_of_le hmul (Q'.le_of_eqv (Q'.mul_one_eqv (C.τ k)))
  -- chain ≤ with <.
  exact Q'.lt_of_le_of_lt hdrop hstrict

/-! ## 2. The AF scale cocycle

The running factor is the consecutive-coupling ratio `t_k = τ_{k+1}/τ_k` on the
AF window `k ≥ k0`, and the trivial scale `1` off-window (no running carried
where the certificate makes no claim). -/

/-- The per-step running factor: `τ_{k+1}/τ_k` on the AF window, `1` off it.
A positive scale ratio: a quotient of two positive couplings inside the window,
the trivial scale outside. -/
def stepFactor (C : AFTrajectoryCertificate) (k : Nat) : Q' :=
  if C.k0 ≤ k then Q'.divPos (C.τ (k + 1)) (C.τ k) (C.τ_pos k) else (1 : Q')

/-- Each step factor is positive (a positive ratio inside the window; `1`
outside). -/
theorem stepFactor_pos (C : AFTrajectoryCertificate) (k : Nat) :
    (0 : Q') < stepFactor C k := by
  unfold stepFactor
  by_cases h : C.k0 ≤ k
  · rw [if_pos h]
    exact Q'.divPos_pos (C.τ (k + 1)) (C.τ k) (C.τ_pos k) (C.τ_pos (k + 1))
  · rw [if_neg h]
    show (0 : Int) * ((1 : Q').den : Int) < (1 : Q').num * ((0 : Q').den : Int)
    decide

/-- **The AF scale cocycle.**  An `AFTrajectoryCertificate` PRODUCES a genuine
`ScaleSheaf.ScaleCocycle`: the per-step running factors are the
consecutive-coupling ratios of the AF trajectory, all positive. -/
def afCocycle (C : AFTrajectoryCertificate) : ScaleCocycle where
  t := stepFactor C
  tpos := stepFactor_pos C

/-! ## 3. The running steps are genuinely ≠ 1

On the AF window the ratio `τ_{k+1}/τ_k` is `< 1` (strict drop), hence not
semantically `1`.  The proof routes `¬ (divPos ≃ 1)` through the cancellation
`divPos a b · b ≃ a`: were `divPos ≃ 1`, then `a ≃ b`, contradicting `a < b`. -/

/-- If `a < b` then the quotient `a/b` is not semantically `1`.
From `divPos a b · b ≃ a` and `(divPos a b ≃ 1) ⟹ divPos a b · b ≃ 1 · b ≃ b`,
a `divPos ≃ 1` would force `a ≃ b`, impossible for `a < b`. -/
theorem divPos_ne_one_of_lt {a b : Q'} (hb : (0 : Q') < b) (hab : a < b) :
    ¬ (Q'.divPos a b hb).eqv 1 := by
  intro he
  -- a ≃ divPos a b hb · b ≃ 1 · b ≃ b.
  have h1 : (Q'.divPos a b hb * b).eqv a := Q'.divPos_mul_eqv a b hb
  have h2 : (Q'.divPos a b hb * b).eqv (1 * b) :=
    Q'.mul_eqv_congr_right _ _ b he
  have h3 : ((1 : Q') * b).eqv b := Q'.one_mul_eqv b
  -- a ≃ b.
  have hab_eqv : a.eqv b :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm h1) (Q'.eqv_trans _ _ _ h2 h3)
  exact not_eqv_of_lt hab hab_eqv

/-- **AF running step ≠ 1.**  For an in-window step `k ≥ k0`, the AF running
factor is NOT semantically the trivial scale `1`: `¬ (afCocycle C).t k ≃ 1`.
This is asymptotic freedom (`β > 0`) at the level of the scale cocycle — the
coupling actually runs, so the per-step scale ratio is a genuine departure from
`1`. -/
theorem af_step_ne_one (C : AFTrajectoryCertificate) (k : Nat) (hk : C.k0 ≤ k) :
    ¬ ((afCocycle C).t k).eqv (1 : Q') := by
  show ¬ (stepFactor C k).eqv (1 : Q')
  unfold stepFactor
  rw [if_pos hk]
  exact divPos_ne_one_of_lt (C.τ_pos k) (strict_drop C k hk)

/-! ## 4. THE PAYOFF — discharging `BetaNonzero`

`ScaleSheaf.BetaNonzero` is `∃ n, ¬ (t n).eqv 1`.  The base index `k0` of the
certificate is exactly such an `n`: `af_step_ne_one` at `k0` (which is `≥ k0`)
supplies the witness.  No named hypothesis: the only input is the certificate's
`β > 0`, consumed through `strict_drop`.  This converts `BetaNonzero` from a
free-standing named wall into a proved consequence of the AF data. -/

/-- **`BetaNonzero` DISCHARGED.**  For the AF trajectory, the named
dimensional-transmutation input `ScaleSheaf.BetaNonzero` is a THEOREM:
the base-index step `k0` carries genuine running (its factor is not `1`),
witnessed directly from the certificate's `β > 0`.  No named hypothesis is
re-assumed — this is the genuine discharge. -/
theorem af_BetaNonzero (C : AFTrajectoryCertificate) :
    ScaleCocycle.BetaNonzero (afCocycle C) :=
  ⟨C.k0, af_step_ne_one C C.k0 (Nat.le_refl C.k0)⟩

/-- **The AF scale class is globally nontrivial — UNCONDITIONALLY.**
Composing the discharged `af_BetaNonzero` with the scale-sheaf obstruction
theorem `nontrivial_of_step_ne_one`: the AF scale cocycle is NOT globally
trivial.  The dimensional-transmutation class is a genuine obstruction for the
AF trajectory, with no external "running is real" assumption remaining. -/
theorem af_scale_nontrivial (C : AFTrajectoryCertificate) :
    ¬ ScaleCocycle.IsGloballyTrivial (afCocycle C) :=
  ScaleCocycle.nontrivial_of_step_ne_one (afCocycle C) (af_BetaNonzero C)

/-! ## 5. The Λ connection (fixed-spacing structural identities)

The accumulated invariant `Lambda` of the scale sheaf is, on a single AF edge,
exactly the coupling ratio `t_k = τ_{k+1}/τ_k`; hence the in-window one-step
class is nontrivial.  These identities hold at fixed lattice spacing.  The
`a → 0` continuum limit of `Lambda` (its finiteness/positivity as a located
real number — the genuine dimensional-transmutation scale) is NOT addressed
here and remains the named continuum wall. -/

/-- **One-step Λ = the AF coupling ratio.**  The accumulated scale class over a
single AF edge `k ⟶ k+1` is exactly the running factor `t_k`; for an in-window
edge that is the consecutive-coupling ratio `τ_{k+1}/τ_k`.  At `eqv`, from the
scale sheaf's `Lambda_one_step`. -/
theorem afCocycle_Lambda_one_step (C : AFTrajectoryCertificate) (k : Nat) :
    ((afCocycle C).Lambda k (k + 1)).eqv ((afCocycle C).t k) :=
  ScaleCocycle.Lambda_one_step (afCocycle C) k

/-- **The in-window one-step class is nontrivial.**  On the AF window the
one-step accumulated class `Lambda k (k+1)` is NOT semantically `1`: the genuine
running of the AF coupling is visible as a nontrivial scale class on a single
edge of the nerve.  From `afCocycle_Lambda_one_step` and `af_step_ne_one`. -/
theorem afCocycle_Lambda_one_step_ne_one
    (C : AFTrajectoryCertificate) (k : Nat) (hk : C.k0 ≤ k) :
    ¬ ((afCocycle C).Lambda k (k + 1)).eqv (1 : Q') := by
  intro hcontra
  -- Lambda k (k+1) ≃ t k, so t k ≃ Lambda k (k+1) ≃ 1.
  have h := afCocycle_Lambda_one_step C k
  exact af_step_ne_one C k hk (Q'.eqv_trans _ _ _ (Q'.eqv_symm h) hcontra)

end YMGap.Continuum.AFScaleCocycle

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFScaleCocycle.lt_of_lt_of_le
#print axioms YMGap.Continuum.AFScaleCocycle.num_pos_of_pos
#print axioms YMGap.Continuum.AFScaleCocycle.mul_lt_mul_of_pos_left
#print axioms YMGap.Continuum.AFScaleCocycle.not_eqv_of_lt
#print axioms YMGap.Continuum.AFScaleCocycle.strict_drop
#print axioms YMGap.Continuum.AFScaleCocycle.stepFactor_pos
#print axioms YMGap.Continuum.AFScaleCocycle.afCocycle
#print axioms YMGap.Continuum.AFScaleCocycle.divPos_ne_one_of_lt
#print axioms YMGap.Continuum.AFScaleCocycle.af_step_ne_one
#print axioms YMGap.Continuum.AFScaleCocycle.af_BetaNonzero
#print axioms YMGap.Continuum.AFScaleCocycle.af_scale_nontrivial
#print axioms YMGap.Continuum.AFScaleCocycle.afCocycle_Lambda_one_step
#print axioms YMGap.Continuum.AFScaleCocycle.afCocycle_Lambda_one_step_ne_one
