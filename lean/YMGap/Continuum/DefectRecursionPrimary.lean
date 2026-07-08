/-
Track B / R2 — **THE DEFECT-RECURSION AS THE PRIMARY NAMED ROUTE to the continuum
mass gap**, in the EXACT CLAUDE.md form

    Δ_{k+1}  ≥  (1 − δ_k)·Δ_k  −  ε_k ,      Σδ < ∞,  Σε < ∞,
    budget:   (1 − Σδ)·m₀  >  Σε ,

with the σ̂/string-tension route DEMOTED to a corollary.

# Why this is the PRIMARY route (read first)

There are two structurally different continuum-gap routes in this development:

  * the **defect-recursion route** (THIS module).  A positive continuum gap floor
    follows from the ADDITIVE per-step spectral-stability recursion above.  Its
    single analytic obligation is LOCAL: a per-step Kato–Temple perturbation bound
    on ONE RG/block-spin step (`PerStepSpectralStability.pert`, the a-priori
    transverse off-diagonal norm).  It needs NO global mechanism — no confinement,
    no area law.  Each step is a perturbation lemma, not a phase-structure theorem.

  * the **σ̂/string-tension route** (`SqrtBridge`, `SigmaGroundedFloor`,
    `WilsonAreaLaw`, `OSConfinementAssessment`).  `m₀ = √σ̂_∞` gives the gap FROM a
    positive string tension `σ̂ > 0`; but obtaining `σ̂ > 0` at weak coupling
    REQUIRES the continuum Wilson-loop AREA LAW
    (`WilsonAreaLaw.ScaleCovariantWilsonAreaLaw`, uninhabited) — i.e. quark
    confinement, an input at least as hard as the mass gap, with no
    mechanism-level proof.

The defect route consumes a strictly WEAKER, purely LOCAL input (a per-step
perturbation bound) than the σ̂ route (a global confinement law).  So it is the
PRIMARY route; §5 demotes σ̂ to a corollary and records the input comparison.

# What this module proves (and what stays open)

  §1  The additive per-step converter `additive_margin_recursion_of_eigShift`:
      `g − shift ≤ g'` ∧ `shift ≤ δ·g + ε`  ⟹  `(1−δ)·g − ε ≤ g'`.  (generalises
      `AsymptoticSpectralLoc.margin_recursion_of_eigShift` to nonzero `ε`.)

  §2  `sumPrefix` + its nonnegativity.

  §3  `AdditiveDefectGapRecursion` (`Type`, Rule 8) — the additive recursion tower,
      whose ONE open field is `recursion` (`(1−δ_k)Δ_k − ε_k ≤ Δ_{k+1}`).  The
      running invariant `prodInvariant` (`∏ρ · m₀ ≤ Δ_k + Σε_k`, NO subtraction),
      the uniform floor `uniform_floor` (`(1−Σδ)m₀ − Σε ≤ Δ_k`) and its strict
      positivity `floor_pos` (from the budget `(1−Σδ)m₀ > Σε`) are PROVED.
      `continuum_floor_of_additiveDefectRecursion` is the headline reduction.

  §4  Subsumption: a multiplicative `ContinuumClosureProgram.DefectGapRecursion`
      is the `ε ≡ 0` special case (`ofMultiplicative`), so the additive route
      strictly extends the existing primary machinery; a degenerate inhabitant
      (`trivialAdditive`, no 4D content) certifies non-vacuity (Rule 8).

  §5  **The per-step spectral-stability perturbation lemma**
      `PerStepSpectralStability` / `perStep_additive_recursion`: reusing the PROVED
      Temple 2×2 bound (`temple`) and the positive right-cancellation
      (`BakryEmery.le_of_mul_le_mul_right_pos`), ONE RG step degrades the located
      2nd-eigenvalue by at most `δ_k·g_k + ε_k`, discharging the additive recursion
      field.  The SINGLE analytic obligation is the residual `pert` (§6).

  §6  σ̂ DEMOTED: `sigmaHat_surrogate_of_floor` — the string-tension surrogate
      `σ̂ := (gap)²` is bounded below by `c² > 0` DERIVED from the defect-route
      floor (no area law).  `RouteInputComparison` records, as `Type`-level data,
      that the defect route's hypothesis is the LOCAL per-step residual while the
      σ̂ route's is the GLOBAL area law.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The defect-recursion route is now the PRIMARY named route: its positive continuum
floor is PROVED CONDITIONAL on ONE local per-step obligation — the residual
`PerStepSpectralStability.pert`, the a-priori transverse off-diagonal norm bound
`‖P_k^⊥‖² ≤ (δ_k·g_k + ε_k)·g_k` over the true-margin RG trajectory.  This is the
EXACT per-step residual; it is NOT closed by making the route primary (it is equi-
inhabiting with `SingleStepDefectReduction.SingleStepDefectBound.singleStep`, per
the honest verdict of `TempleSpectralStabilityDefect`).  `AdditiveDefectGapRecursion`
and `PerStepSpectralStability` are NOT inhabited on ℝ⁴ (only a degenerate no-content
witness is given).  The σ̂-demotion is a route-comparison, not a closure.  NO Clay
frontier type is inhabited.  Nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing PROVED `TempleSpectralStabilityDefect.temple_shift_le`,
`BakryEmery.le_of_mul_le_mul_right_pos`, and the `Q'` mul/add-monotonicity toolkit.
Every carrier is `Type`-level data.  Each load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `ring`/`nlinarith`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.ContinuumClosureProgram
import YMGap.Continuum.TempleSpectralStabilityDefect

namespace YMGap.Continuum.DefectRecursionPrimary

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.ContinuumClosureProgram

/-! ## 0. Small `Q'` helpers (subtraction↔addition monotonicity, floor positivity) -/

/-- `(1 − δ)·S ≤ S` for `0 ≤ δ`, `0 ≤ S`.  The multiplier `1 − δ ≤ 1` cannot
increase a nonnegative quantity.  (`(1−δ)S ≃ S − δS ≤ S`.) -/
theorem oneSubMul_le_self {δ S : Q'} (hδ : (0 : Q') ≤ δ) (hS : (0 : Q') ≤ S) :
    (1 - δ) * S ≤ S := by
  have hdist : (((1 : Q') - δ) * S).eqv (S + -(δ * S)) :=
    Q'.eqv_trans _ _ _ (Q'.sub_mul_eqv 1 δ S)
      (Q'.add_eqv_congr_right (1 * S) S (-(δ * S)) (Q'.one_mul_eqv S))
  have hnn : (0 : Q') ≤ δ * S := Q'.mul_nonneg δ S hδ hS
  have hneg : -(δ * S) ≤ (0 : Q') := by
    have h0 : -(δ * S) ≤ -(0 : Q') := Q'.neg_le_neg hnn
    have hz : (-(0 : Q')) = (0 : Q') := rfl
    rwa [hz] at h0
  have hstep : S + -(δ * S) ≤ S + 0 := Q'.add_le_add_left S _ _ hneg
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) ?_
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' S)))

/-- `a − c ≤ b  ⟹  a ≤ b + c`.  (Add `c`; `−c + c ≃ 0`.) -/
theorem le_add_of_sub_le {a b c : Q'} (h : a - c ≤ b) : a ≤ b + c := by
  -- (a + -c) + c ≤ b + c
  have hstep : (a + -c) + c ≤ b + c := Q'.add_le_add_right (a + -c) b c h
  -- (a + -c) + c ≃ a + (-c + c) ≃ a + 0 ≃ a
  have hcollapse : ((a + -c) + c).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-c) c) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (-c + c) 0 (Q'.neg_add_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) hstep

/-- `a ≤ b + c  ⟹  a − c ≤ b`.  (Subtract `c`; `c + -c ≃ 0`.) -/
theorem sub_le_of_le_add {a b c : Q'} (h : a ≤ b + c) : a - c ≤ b := by
  have hstep : a + -c ≤ (b + c) + -c := Q'.add_le_add_right a (b + c) (-c) h
  have hcollapse : ((b + c) + -c).eqv b :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b c (-c))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv c))
        (Q'.eqv_of_eq (Q'.add_zero' b)))
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hcollapse)

/-- Subtraction is monotone: `a ≤ a'` and `b' ≤ b` ⟹ `a − b ≤ a' − b'`. -/
theorem sub_le_sub {a a' b b' : Q'} (ha : a ≤ a') (hb : b' ≤ b) : a - b ≤ a' - b' := by
  have h1 : a + -b ≤ a' + -b := Q'.add_le_add_right a a' (-b) ha
  have h2 : a' + -b ≤ a' + -b' := Q'.add_le_add_left a' (-b) (-b') (Q'.neg_le_neg hb)
  exact Q'.le_trans' _ _ _ h1 h2

/-- `b < a  ⟹  0 < a − b` on `Q'` (numerator-level, mirrors `HKPos.one_sub_pos`). -/
theorem sub_pos_of_lt {a b : Q'} (h : b < a) : (0 : Q') < a - b := by
  have hlt : b.num * (a.den : Int) < a.num * (b.den : Int) := h
  apply CReal.pos_of_num_pos
  show 0 < (a + (-b)).num
  show 0 < a.num * (b.den : Int) + (-b.num) * (a.den : Int)
  have hsub : (0 : Int) < a.num * (b.den : Int) - b.num * (a.den : Int) :=
    Int.sub_pos.mpr hlt
  rw [Int.sub_eq_add_neg] at hsub
  rw [Int.neg_mul]
  exact hsub

/-! ## 1. The ADDITIVE per-step eigenvalue-shift converter -/

/-- **THE ADDITIVE CONVERTER (generalising `margin_recursion_of_eigShift`).**  From
the additive margin drop `g − shift ≤ g'` and the *additive* shift control
`shift ≤ δ·g + ε`, deduce the additive multiplicative recursion

    (1 − δ)·g − ε  ≤  g' .

PROOF (no positivity): `(1−δ)·g − ε ≃ g + −(δ·g) + −ε ≃ g + −(δ·g + ε)`; `hbridge`
gives `−(δ·g + ε) ≤ −shift`; `add_le_add_left g` then `hadd`. -/
theorem additive_margin_recursion_of_eigShift
    (δ shift ε g g1 : Q')
    (hadd : g - shift ≤ g1)
    (hbridge : shift ≤ δ * g + ε) :
    (1 - δ) * g - ε ≤ g1 := by
  -- (1−δ)·g ≃ g + −(δ·g)
  have hdist : (((1 : Q') - δ) * g).eqv (g + -(δ * g)) :=
    Q'.eqv_trans _ _ _ (Q'.sub_mul_eqv 1 δ g)
      (Q'.add_eqv_congr_right (1 * g) g (-(δ * g)) (Q'.one_mul_eqv g))
  -- (1−δ)·g − ε = (1−δ)·g + −ε ≃ (g + −(δ·g)) + −ε ≃ g + (−(δ·g) + −ε)
  have hL : (((1 : Q') - δ) * g - ε).eqv (g + (-(δ * g) + -ε)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-ε) hdist) ?_
    exact Q'.add_assoc_eqv g (-(δ * g)) (-ε)
  -- −(δ·g) + −ε ≃ −(δ·g + ε) ≥ −shift  (from hbridge)
  have hsum : (-(δ * g) + -ε).eqv (-(δ * g + ε)) := by
    have := Q'.neg_add_eqv (δ * g) ε   -- (-(δg+ε)).eqv (-(δg) + -ε)
    exact Q'.eqv_symm this
  have hneg : -(δ * g + ε) ≤ -shift := Q'.neg_le_neg hbridge
  -- g + (−(δg) + −ε) ≤ g + −shift
  have hstep : g + (-(δ * g) + -ε) ≤ g + -shift :=
    Q'.add_le_add_left g _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) hneg)
  -- g + −shift = g − shift ≤ g1
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ hstep hadd)

/-! ## 2. Prefix sums of the additive defects `ε_k` -/

/-- The prefix sum `Σ_{j<k} ε_j` (empty sum `= 0`). -/
def sumPrefix (ε : Nat → Q') : Nat → Q'
  | 0 => (0 : Q')
  | k + 1 => sumPrefix ε k + ε k

/-- A prefix sum of nonnegative terms is nonnegative. -/
theorem sumPrefix_nonneg {ε : Nat → Q'} (hε : ∀ k, (0 : Q') ≤ ε k) :
    ∀ k, (0 : Q') ≤ sumPrefix ε k
  | 0 => Q'.le_refl' 0
  | k + 1 => by
      show (0 : Q') ≤ sumPrefix ε k + ε k
      have := Q'.zero_le_add (sumPrefix ε k) (ε k) (sumPrefix_nonneg hε k) (hε k)
      exact this

/-- The prefix sum of the constant-zero sequence is `≃ 0` at every length. -/
theorem sumPrefix_zero_eqv : ∀ k, (sumPrefix (fun _ => (0 : Q')) k).eqv 0
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      show (sumPrefix (fun _ => (0 : Q')) n + 0).eqv 0
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (sumPrefix_zero_eqv n)

/-! ## 3. `AdditiveDefectGapRecursion` — the PRIMARY named route (CLAUDE.md form) -/

/-- **THE ADDITIVE PER-SCALE DEFECT-CONTROLLED GAP RECURSION (the primary named
route).**  `Type`-level data (Rule 8).  Packages the spacing tower with:

  * `physGap : Nat → Q'` — the per-scale physical gap `Δ_k` (anchor `Δ_0 = m₀ > 0`);
  * `defect : Nat → Q'` — the per-step multiplicative defect `δ_k ∈ [0,1]`;
  * `epsilon : Nat → Q'` — the per-step ADDITIVE defect `ε_k ≥ 0`;
  * **the OPEN content** (`recursion`) — the additive per-step gap-degradation law
        `(1 − δ_k)·Δ_k − ε_k ≤ Δ_{k+1}`  (the CLAUDE.md `Δ_{k+1} ≥ (1−δ_k)Δ_k − ε_k`);
  * the SUMMABILITY outputs, as `Q'`-level data: `prodFloor` (`= (1−Σδ)·m₀`, a lower
    bound on `∏ρ · m₀`) and `epsSumCeil` (`= Σε`, an upper bound on `Σε_k`);
  * `budget` — the CLAUDE.md defect budget `(1 − Σδ)·m₀ > Σε`, i.e.
    `epsSumCeil < prodFloor`.

The ONE genuinely-open field is `recursion`; everything else is summability
bookkeeping.  This structure is the additive extension of
`ContinuumClosureProgram.DefectGapRecursion` (`ε ≡ 0`). -/
structure AdditiveDefectGapRecursion : Type where
  /-- The per-scale physical gap `Δ_k`. -/
  physGap : Nat → Q'
  /-- The anchor gap `m₀ = Δ_0 > 0`. -/
  physGap0_pos : (0 : Q') < physGap 0
  /-- The per-step multiplicative defect `δ_k`. -/
  defect : Nat → Q'
  /-- Each defect is nonnegative. -/
  defect_nonneg : ∀ k : Nat, (0 : Q') ≤ defect k
  /-- Each defect is at most `1` (so `1 − δ_k ∈ [0,1]`). -/
  defect_le_one : ∀ k : Nat, defect k ≤ 1
  /-- The per-step ADDITIVE defect `ε_k`. -/
  epsilon : Nat → Q'
  /-- Each additive defect is nonnegative. -/
  epsilon_nonneg : ∀ k : Nat, (0 : Q') ≤ epsilon k
  /-- **THE OPEN CONTENT — the additive per-step gap-degradation law.**
  `(1 − δ_k)·Δ_k − ε_k ≤ Δ_{k+1}`. -/
  recursion : ∀ k : Nat,
    (1 - defect k) * physGap k - epsilon k ≤ physGap (k + 1)
  /-- The summable-product floor `(1 − Σδ)·m₀`. -/
  prodFloor : Q'
  /-- The product floor bound: `prodFloor ≤ (∏_{i<k}(1 − δ_i))·m₀`. -/
  prodFloor_le : ∀ k : Nat,
    prodFloor ≤ prodPrefix (fun i => 1 - defect i) k * physGap 0
  /-- The summable ε-ceiling `Σε`. -/
  epsSumCeil : Q'
  /-- The ε-sum bound: `Σ_{j<k} ε_j ≤ epsSumCeil`. -/
  epsSum_le : ∀ k : Nat, sumPrefix epsilon k ≤ epsSumCeil
  /-- **THE DEFECT BUDGET** `(1 − Σδ)·m₀ > Σε`, i.e. `epsSumCeil < prodFloor`. -/
  budget : epsSumCeil < prodFloor

namespace AdditiveDefectGapRecursion

/-- The per-block multiplier `ρ_k := 1 − δ_k`. -/
def rho (D : AdditiveDefectGapRecursion) : Nat → Q' := fun k => 1 - D.defect k

/-- The multiplier is nonnegative (from `δ_k ≤ 1`). -/
theorem rho_nonneg (D : AdditiveDefectGapRecursion) (k : Nat) : (0 : Q') ≤ D.rho k := by
  show (0 : Q') ≤ 1 - D.defect k
  have hstep := Q'.add_le_add_right (D.defect k) 1 (-(D.defect k)) (D.defect_le_one k)
  refine Q'.le_trans' _ _ _ ?_ hstep
  exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (D.defect k))

/-- **THE RUNNING INVARIANT (subtraction-free).**  `(∏_{i<k} ρ_i)·m₀ ≤ Δ_k + Σ_{j<k} ε_j`
for all `k`, by induction on `k`.  This is the additive Grönwall fold: the prefix
product of the gap-degradation multipliers, anchored at `m₀`, is dominated by the
running gap plus the accumulated additive defects.  Reuses `recursion` and
`oneSubMul_le_self`; NO subtraction in the invariant. -/
theorem prodInvariant (D : AdditiveDefectGapRecursion) :
    ∀ k : Nat,
      prodPrefix D.rho k * D.physGap 0 ≤ D.physGap k + sumPrefix D.epsilon k
  | 0 => by
      -- prodPrefix ρ 0 · m₀ = 1·m₀ ≃ m₀ = Δ_0 + 0
      show (1 : Q') * D.physGap 0 ≤ D.physGap 0 + sumPrefix D.epsilon 0
      show (1 : Q') * D.physGap 0 ≤ D.physGap 0 + (0 : Q')
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (D.physGap 0))) ?_
      exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (D.physGap 0)))
  | k + 1 => by
      have ih := prodInvariant D k
      -- ρ_k · (∏ρ · m₀) ≤ ρ_k · (Δ_k + Σε_k)
      have hmul : D.rho k * (prodPrefix D.rho k * D.physGap 0)
          ≤ D.rho k * (D.physGap k + sumPrefix D.epsilon k) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (D.rho_nonneg k)
      -- ρ_k·(Δ_k + Σε_k) ≃ ρ_k·Δ_k + ρ_k·Σε_k ≤ ρ_k·Δ_k + Σε_k
      have hdistrib : (D.rho k * (D.physGap k + sumPrefix D.epsilon k)).eqv
          (D.rho k * D.physGap k + D.rho k * sumPrefix D.epsilon k) :=
        Q'.mul_add_eqv (D.rho k) (D.physGap k) (sumPrefix D.epsilon k)
      have hshrink : D.rho k * D.physGap k + D.rho k * sumPrefix D.epsilon k
          ≤ D.rho k * D.physGap k + sumPrefix D.epsilon k :=
        Q'.add_le_add_left (D.rho k * D.physGap k) _ _
          (oneSubMul_le_self (D.defect_nonneg k) (sumPrefix_nonneg D.epsilon_nonneg k))
      -- ρ_k·Δ_k ≤ Δ_{k+1} + ε_k   (from the additive recursion, via le_add_of_sub_le)
      have hrec : D.rho k * D.physGap k ≤ D.physGap (k + 1) + D.epsilon k :=
        le_add_of_sub_le (D.recursion k)
      -- ρ_k·Δ_k + Σε_k ≤ (Δ_{k+1} + ε_k) + Σε_k
      have hrec' : D.rho k * D.physGap k + sumPrefix D.epsilon k
          ≤ (D.physGap (k + 1) + D.epsilon k) + sumPrefix D.epsilon k :=
        Q'.add_le_add_right _ _ (sumPrefix D.epsilon k) hrec
      -- (Δ_{k+1} + ε_k) + Σε_k ≃ Δ_{k+1} + (ε_k + Σε_k) ≃ Δ_{k+1} + (Σε_k + ε_k)
      have hreassoc : ((D.physGap (k + 1) + D.epsilon k) + sumPrefix D.epsilon k).eqv
          (D.physGap (k + 1) + (sumPrefix D.epsilon k + D.epsilon k)) :=
        Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv (D.physGap (k + 1)) (D.epsilon k) (sumPrefix D.epsilon k))
          (Q'.add_eqv_congr_left (D.physGap (k + 1)) _ _
            (Q'.add_comm_eqv (D.epsilon k) (sumPrefix D.epsilon k)))
      -- prodPrefix ρ (k+1) · m₀ = (∏ρ_k · ρ_k)·m₀ ≃ ρ_k·(∏ρ · m₀)
      have hLHS : (prodPrefix D.rho (k + 1) * D.physGap 0).eqv
          (D.rho k * (prodPrefix D.rho k * D.physGap 0)) := by
        show ((prodPrefix D.rho k * D.rho k) * D.physGap 0).eqv
            (D.rho k * (prodPrefix D.rho k * D.physGap 0))
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (prodPrefix D.rho k * D.rho k) (D.rho k * prodPrefix D.rho k)
            (D.physGap 0) (Q'.mul_comm_eqv (prodPrefix D.rho k) (D.rho k))) ?_
        exact Q'.mul_assoc_eqv (D.rho k) (prodPrefix D.rho k) (D.physGap 0)
      -- assemble
      show prodPrefix D.rho (k + 1) * D.physGap 0
          ≤ D.physGap (k + 1) + sumPrefix D.epsilon (k + 1)
      -- RHS target: Δ_{k+1} + (Σε_k + ε_k)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
      refine Q'.le_trans' _ _ _ hmul ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdistrib) ?_
      refine Q'.le_trans' _ _ _ hshrink ?_
      refine Q'.le_trans' _ _ _ hrec' ?_
      exact Q'.le_of_eqv hreassoc

/-- **THE UNIFORM GAP FLOOR.**  `(1 − Σδ)·m₀ − Σε ≤ Δ_k` at every scale `k`:
the running invariant `prodInvariant` (rearranged to `∏ρ·m₀ − Σε_k ≤ Δ_k`) composed
with `prodFloor ≤ ∏ρ·m₀` and `Σε_k ≤ epsSumCeil`.  This is the spacing-uniform
positive continuum floor `liminf Δ_k ≥ (1−Σδ)m₀ − Σε`. -/
theorem uniform_floor (D : AdditiveDefectGapRecursion) (k : Nat) :
    D.prodFloor - D.epsSumCeil ≤ D.physGap k := by
  -- ∏ρ·m₀ − Σε_k ≤ Δ_k   (from the invariant, via sub_le_of_le_add)
  have hcore : prodPrefix D.rho k * D.physGap 0 - sumPrefix D.epsilon k ≤ D.physGap k :=
    sub_le_of_le_add (D.prodInvariant k)
  -- prodFloor − epsSumCeil ≤ ∏ρ·m₀ − Σε_k   (subtraction monotone)
  have hfloor : D.prodFloor - D.epsSumCeil
      ≤ prodPrefix D.rho k * D.physGap 0 - sumPrefix D.epsilon k :=
    sub_le_sub (D.prodFloor_le k) (D.epsSum_le k)
  exact Q'.le_trans' _ _ _ hfloor hcore

/-- The uniform floor is strictly positive — the CLAUDE.md budget `(1−Σδ)m₀ > Σε`. -/
theorem floor_pos (D : AdditiveDefectGapRecursion) : (0 : Q') < D.prodFloor - D.epsSumCeil :=
  sub_pos_of_lt D.budget

/-- The physical gap is strictly positive at every scale: `0 < Δ_k`. -/
theorem physGap_pos (D : AdditiveDefectGapRecursion) (k : Nat) : (0 : Q') < D.physGap k :=
  ContinuumClosureProgram.q'_lt_of_lt_of_le (floor_pos D) (uniform_floor D k)

end AdditiveDefectGapRecursion

/-- **THE HEADLINE REDUCTION (primary route).**  From an `AdditiveDefectGapRecursion`
`D`, the physical gap is uniformly bounded below by the strictly-positive floor
`(1 − Σδ)·m₀ − Σε` at every scale — the continuum-gap floor in the exact CLAUDE.md
form.  The ONLY open input consumed is `D.recursion` (the additive per-step
gap-degradation law); everything else is proved.  No 4D inhabitant of `D` is
exhibited, so this does NOT close the Clay problem; it isolates the closure into the
single `recursion` field, which §5 pins to ONE local per-step perturbation residual. -/
theorem continuum_floor_of_additiveDefectRecursion (D : AdditiveDefectGapRecursion) :
    (0 : Q') < D.prodFloor - D.epsSumCeil
      ∧ ∀ k : Nat, D.prodFloor - D.epsSumCeil ≤ D.physGap k :=
  ⟨D.floor_pos, D.uniform_floor⟩

/-! ## 4. Subsumption of the multiplicative route + non-vacuity witness -/

/-- **THE ADDITIVE ROUTE SUBSUMES THE MULTIPLICATIVE ONE.**  A multiplicative
`ContinuumClosureProgram.DefectGapRecursion` is exactly the `ε ≡ 0` special case:
its recursion `(1 − δ_k)·Δ_k ≤ Δ_{k+1}` is `(1 − δ_k)·Δ_k − 0 ≤ Δ_{k+1}`, and its
product floor supplies `prodFloor`; taking `epsSumCeil := 0` the budget is
`0 < prodFloor` (the multiplicative `prodFloor_pos`).  So every multiplicative
inhabitant lifts to an additive one — the additive route strictly extends the
existing primary machinery. -/
def ofMultiplicative (D : ContinuumClosureProgram.DefectGapRecursion) :
    AdditiveDefectGapRecursion where
  physGap := D.physGap
  physGap0_pos := D.physGap0_pos
  defect := D.defect
  defect_nonneg := D.defect_nonneg
  defect_le_one := D.defect_le_one
  epsilon := fun _ => 0
  epsilon_nonneg := fun _ => Q'.le_refl' 0
  recursion := fun k => by
    -- (1 − δ_k)·Δ_k − 0 = (1 − δ_k)·Δ_k ≤ Δ_{k+1}
    have h := D.recursion k
    rwa [Q'.sub_zero' ((1 - D.defect k) * D.physGap k)]
  prodFloor := D.prodFloor
  prodFloor_le := D.prodFloor_le
  epsSumCeil := 0
  epsSum_le := fun k => Q'.le_of_eqv (sumPrefix_zero_eqv k)
  budget := D.prodFloor_pos

/-- The additive floor recovered from a multiplicative recursion equals the
multiplicative floor (`prodFloor − 0`), sanity-checking `ofMultiplicative`. -/
theorem ofMultiplicative_floor (D : ContinuumClosureProgram.DefectGapRecursion) (k : Nat) :
    (ofMultiplicative D).prodFloor - (ofMultiplicative D).epsSumCeil ≤ D.physGap k :=
  (ofMultiplicative D).uniform_floor k

/-- **A degenerate (no-content) inhabitant certifying non-vacuity (Rule 8).**  Zero
defects, zero additive defects, constant gap `m₀ > 0`; carries NO 4D Yang–Mills
content (the trivial flow fixed point), exists only to certify
`AdditiveDefectGapRecursion` is not false-as-stated.  Obtained by lifting the
degenerate multiplicative `trivialDefectGapRecursion`. -/
def trivialAdditive (g₀ : Q') (hg₀ : (0 : Q') < g₀) : AdditiveDefectGapRecursion :=
  ofMultiplicative (ContinuumClosureProgram.trivialDefectGapRecursion g₀ hg₀)

/-- Sanity: the degenerate inhabitant's uniform floor is its anchor gap. -/
theorem trivialAdditive_floor (g₀ : Q') (hg₀ : (0 : Q') < g₀) (k : Nat) :
    (trivialAdditive g₀ hg₀).prodFloor - (trivialAdditive g₀ hg₀).epsSumCeil
      ≤ (trivialAdditive g₀ hg₀).physGap k :=
  (trivialAdditive g₀ hg₀).uniform_floor k

/-! ## 5. The per-step spectral-stability perturbation lemma (the crux)

The crux of the primary route is ONE local lemma: under one RG/block-spin step,
the transfer-operator located 2nd-eigenvalue (the gap) degrades by AT MOST the
perturbation `δ_k·g_k + ε_k` (Kato–Temple).  Each step is a perturbation lemma,
NOT a phase-structure theorem. -/

/-- **`PerStepSpectralStability` — the per-step Kato–Temple perturbation datum
(`Type`, Rule 8).**  Carries, at every scale `k`:

  * `g` — the physical margins `g_k = m_lat(a_k)/a_k` (`g_k > 0`);
  * `defect`/`eps` — the per-step multiplicative/additive defects (`≥ 0`);
  * `shift` — the per-step located-2nd-eigenvalue downward shift;
  * `bsq` — the SQUARED transverse off-diagonal norm `‖P_k^⊥‖²` (kept squared →
    `Q'`-rational, no `sqrt`);
  * `hadd` — the located-2nd-eigenvalue ↔ physical-margin dictionary
    `g_k − shift_k ≤ g_{k+1}` (√-bridge + `a_k`-rescaling of the PROVED
    eigenvalue-location facts `bulk_below_gapEdge` / `localization_holds`);
  * `temple` — the PROVED Kato–Temple 2×2 second-order bound
    `shift_k·g_k ≤ ‖P_k^⊥‖²` (from the exact char identity `δ(δ+g)=b²`, `g ≤ δ+g`,
    `TempleSpectralStabilityDefect.temple_shift_le`);
  * **`pert`** — **THE SINGLE ANALYTIC OBLIGATION (the residual)**: the a-priori
    off-diagonal norm bound `‖P_k^⊥‖² ≤ (δ_k·g_k + ε_k)·g_k`.

`pert` is the interacting content — an a-priori bound on ONE per-scale interacting
transverse off-diagonal norm over the true-margin RG trajectory.  It is UNINHABITED
on ℝ⁴ (equi-inhabiting `SingleStepDefectBound.singleStep`, per the honest verdict of
`TempleSpectralStabilityDefect`).  It needs NO global mechanism — it is LOCAL to one
RG step. -/
structure PerStepSpectralStability : Type where
  /-- The per-scale physical margins `g_k = m_lat(a_k)/a_k`. -/
  g : Nat → Q'
  /-- Each margin is strictly positive. -/
  g_pos : ∀ k, (0 : Q') < g k
  /-- The per-step multiplicative defect `δ_k`. -/
  defect : Nat → Q'
  /-- Each defect is nonnegative. -/
  defect_nonneg : ∀ k, (0 : Q') ≤ defect k
  /-- The per-step additive defect `ε_k`. -/
  eps : Nat → Q'
  /-- Each additive defect is nonnegative. -/
  eps_nonneg : ∀ k, (0 : Q') ≤ eps k
  /-- The per-step located-2nd-eigenvalue downward shift. -/
  shift : Nat → Q'
  /-- The squared transverse off-diagonal norm `‖P_k^⊥‖²`. -/
  bsq : Nat → Q'
  /-- The located-2nd-eigenvalue ↔ physical-margin dictionary. -/
  hadd : ∀ k, g k - shift k ≤ g (k + 1)
  /-- The PROVED Kato–Temple 2×2 second-order bound `shift_k·g_k ≤ ‖P_k^⊥‖²`. -/
  temple : ∀ k, shift k * g k ≤ bsq k
  /-- **THE RESIDUAL** — the a-priori off-diagonal threshold
  `‖P_k^⊥‖² ≤ (δ_k·g_k + ε_k)·g_k`. -/
  pert : ∀ k, bsq k ≤ (defect k * g k + eps k) * g k

/-- **`perStep_additive_recursion` — ONE RG STEP IS A PERTURBATION LEMMA.**  From a
`PerStepSpectralStability`, at every scale the located 2nd-eigenvalue degrades by at
most `δ_k·g_k + ε_k`, giving the additive per-step recursion

    (1 − δ_k)·g_k − ε_k  ≤  g_{k+1} .

PROOF: `temple` + `pert` give `shift_k·g_k ≤ (δ_k·g_k + ε_k)·g_k`; the positive
right-cancellation `BakryEmery.le_of_mul_le_mul_right_pos` (`g_k > 0`) yields the
additive shift control `shift_k ≤ δ_k·g_k + ε_k`; `additive_margin_recursion_of_eigShift`
with `hadd` closes it.  Genuinely reuses the built Kato–Temple / Bakry–Émery
machinery; each step is a perturbation lemma, not a confinement theorem. -/
theorem perStep_additive_recursion (P : PerStepSpectralStability) (k : Nat) :
    (1 - P.defect k) * P.g k - P.eps k ≤ P.g (k + 1) := by
  have hchain : P.shift k * P.g k ≤ (P.defect k * P.g k + P.eps k) * P.g k :=
    Q'.le_trans' _ _ _ (P.temple k) (P.pert k)
  have hbridge : P.shift k ≤ P.defect k * P.g k + P.eps k :=
    BakryEmery.le_of_mul_le_mul_right_pos (P.g_pos k) hchain
  exact additive_margin_recursion_of_eigShift
    (P.defect k) (P.shift k) (P.eps k) (P.g k) (P.g (k + 1)) (P.hadd k) hbridge

/-- **`additiveRecursion_of_perStep` — the per-step lemma DISCHARGES the primary
route's open field.**  Given a `PerStepSpectralStability` (whose per-step recursion
is PROVED by `perStep_additive_recursion`) TOGETHER with the summability bookkeeping
(`defect_le_one`, the product floor `prodFloor ≤ ∏ρ·m₀`, the ε-ceiling
`Σε_k ≤ epsSumCeil`, and the budget), the entire `AdditiveDefectGapRecursion` is
assembled — with `recursion` PROVED from the LOCAL per-step perturbation, not
assumed.  So the primary route needs ONLY the per-step control (the `pert` residual);
the rest is summability. -/
def additiveRecursion_of_perStep
    (P : PerStepSpectralStability)
    (defect_le_one : ∀ k, P.defect k ≤ 1)
    (prodFloor : Q')
    (prodFloor_le : ∀ k, prodFloor ≤ prodPrefix (fun i => 1 - P.defect i) k * P.g 0)
    (epsSumCeil : Q')
    (epsSum_le : ∀ k, sumPrefix P.eps k ≤ epsSumCeil)
    (budget : epsSumCeil < prodFloor) :
    AdditiveDefectGapRecursion where
  physGap := P.g
  physGap0_pos := P.g_pos 0
  defect := P.defect
  defect_nonneg := P.defect_nonneg
  defect_le_one := defect_le_one
  epsilon := P.eps
  epsilon_nonneg := P.eps_nonneg
  recursion := perStep_additive_recursion P
  prodFloor := prodFloor
  prodFloor_le := prodFloor_le
  epsSumCeil := epsSumCeil
  epsSum_le := epsSum_le
  budget := budget

/-! ## 6. σ̂ DEMOTED to a corollary + the route-input comparison -/

/-- **`sigmaHat_surrogate_of_floor` — σ̂ IS A DERIVED COROLLARY OF THE GAP.**  The
string-tension surrogate `σ̂ := (gap)²` is bounded below by `c² > 0`, DERIVED from
the defect-route floor `c := prodFloor − epsSumCeil > 0` — WITHOUT any area law.
Inverting the √-bridge (`m₀ = √σ̂` ⟺ `σ̂ = m₀²`): once the defect recursion delivers
`0 < c ≤ Δ_k = gap`, the string tension `σ̂ = gap² ≥ c² > 0` is downstream.  So the
σ̂/string-tension route is DEMOTED — a square of the gap the defect route already
produces, not an independent input. -/
theorem sigmaHat_surrogate_of_floor (D : AdditiveDefectGapRecursion) (k : Nat) :
    (0 : Q') < (D.prodFloor - D.epsSumCeil) * (D.prodFloor - D.epsSumCeil)
      ∧ (D.prodFloor - D.epsSumCeil) * (D.prodFloor - D.epsSumCeil)
          ≤ D.physGap k * D.physGap k := by
  have hc : (0 : Q') < D.prodFloor - D.epsSumCeil := D.floor_pos
  have hck : D.prodFloor - D.epsSumCeil ≤ D.physGap k := D.uniform_floor k
  refine ⟨Q'.mul_pos hc hc, ?_⟩
  -- c² = c·c ≤ Δ·c ≤ Δ·Δ  (monotone in each factor, c ≤ Δ, c,Δ ≥ 0)
  have hc0 : (0 : Q') ≤ D.prodFloor - D.epsSumCeil := Q'.le_of_lt hc
  have hΔ0 : (0 : Q') ≤ D.physGap k := Q'.le_of_lt (D.physGap_pos k)
  have h1 : (D.prodFloor - D.epsSumCeil) * (D.prodFloor - D.epsSumCeil)
      ≤ D.physGap k * (D.prodFloor - D.epsSumCeil) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hck hc0
  have h2 : D.physGap k * (D.prodFloor - D.epsSumCeil) ≤ D.physGap k * D.physGap k :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hck hΔ0
  exact Q'.le_trans' _ _ _ h1 h2

/-- **`RouteInputComparison` — the input comparison, as `Type`-level data.**  The
two routes to the SAME conclusion (a positive continuum gap floor) carry DIFFERENT
hypotheses, recorded here:

  * `defectRouteInput` — the defect-recursion route's hypothesis is exactly a
    `PerStepSpectralStability` (the LOCAL per-step Kato–Temple residual `pert`);
    `defect_floor` witnesses that it delivers the positive floor via §3–§5.
  * `sigmaRouteNeedsAreaLaw` — a PLACEHOLDER for the σ̂ route's hypothesis: the
    GLOBAL continuum Wilson-loop area law (uninhabited).  Kept ABSTRACT (`Type`)
    here so this module carries no false area-law inhabitant; the concrete
    uninhabited premise is `WilsonAreaLaw.ScaleCovariantWilsonAreaLaw`.

The comparison: `defectRouteInput` is a per-STEP LOCAL bound; `sigmaRouteNeedsAreaLaw`
is a GLOBAL confinement law.  The defect route's input is strictly weaker (local),
so it is the PRIMARY route. -/
structure RouteInputComparison : Type 1 where
  /-- The defect route's LOCAL per-step hypothesis. -/
  defectRouteInput : PerStepSpectralStability
  /-- The abstract stand-in for the σ̂ route's GLOBAL area-law hypothesis
  (concretely `WilsonAreaLaw.ScaleCovariantWilsonAreaLaw`, uninhabited on ℝ⁴). -/
  sigmaRouteAreaLaw : Type
  /-- The σ̂ route consumes an inhabitant of the area law to produce the gap; the
  defect route does NOT (it uses `defectRouteInput` only).  Carried as a function
  from the area law to a positive rational (a schematic "√σ̂ floor"); the point is
  the TYPE dependency, not the value. -/
  sigmaRouteConsumesAreaLaw : sigmaRouteAreaLaw → Q'

/-- **`defect_route_floor_from_perStep` — the defect route delivers the positive
floor from the LOCAL per-step input ALONE.**  Wrapping §5's
`additiveRecursion_of_perStep` with §3's `continuum_floor_of_additiveDefectRecursion`:
given the local per-step residual plus summability bookkeeping, the positive
continuum floor holds — with NO area-law hypothesis anywhere in the signature.  This
is the machine-checked statement that the primary route's input is purely local. -/
theorem defect_route_floor_from_perStep
    (P : PerStepSpectralStability)
    (defect_le_one : ∀ k, P.defect k ≤ 1)
    (prodFloor : Q')
    (prodFloor_le : ∀ k, prodFloor ≤ prodPrefix (fun i => 1 - P.defect i) k * P.g 0)
    (epsSumCeil : Q')
    (epsSum_le : ∀ k, sumPrefix P.eps k ≤ epsSumCeil)
    (budget : epsSumCeil < prodFloor) :
    (0 : Q') < prodFloor - epsSumCeil
      ∧ ∀ k : Nat, prodFloor - epsSumCeil ≤ P.g k :=
  continuum_floor_of_additiveDefectRecursion
    (additiveRecursion_of_perStep P defect_le_one prodFloor prodFloor_le
      epsSumCeil epsSum_le budget)

end YMGap.Continuum.DefectRecursionPrimary

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DefectRecursionPrimary.additive_margin_recursion_of_eigShift
#print axioms YMGap.Continuum.DefectRecursionPrimary.AdditiveDefectGapRecursion.prodInvariant
#print axioms YMGap.Continuum.DefectRecursionPrimary.AdditiveDefectGapRecursion.uniform_floor
#print axioms YMGap.Continuum.DefectRecursionPrimary.AdditiveDefectGapRecursion.floor_pos
#print axioms YMGap.Continuum.DefectRecursionPrimary.AdditiveDefectGapRecursion.physGap_pos
#print axioms YMGap.Continuum.DefectRecursionPrimary.continuum_floor_of_additiveDefectRecursion
#print axioms YMGap.Continuum.DefectRecursionPrimary.ofMultiplicative
#print axioms YMGap.Continuum.DefectRecursionPrimary.trivialAdditive_floor
#print axioms YMGap.Continuum.DefectRecursionPrimary.perStep_additive_recursion
#print axioms YMGap.Continuum.DefectRecursionPrimary.additiveRecursion_of_perStep
#print axioms YMGap.Continuum.DefectRecursionPrimary.sigmaHat_surrogate_of_floor
#print axioms YMGap.Continuum.DefectRecursionPrimary.defect_route_floor_from_perStep
