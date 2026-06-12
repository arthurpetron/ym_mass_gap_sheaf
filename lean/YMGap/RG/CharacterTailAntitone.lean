/-
The constructive antitonicity of the heat-kernel exponential in the
Casimir gap — the single most load-bearing analytic input of the
uniform (all-simple-groups) σ̂-budget reduction (the plan's `E_antitone`
/ S1 lemma).

# What this module delivers

The σ̂-budget reduction (`RG/UniformBudget.lean`) collapses
"budget of `R` ≤ budget of SU(2)" to one scalar inequality,
`R.eta_max ≤ su2.eta_max`, named `UniformBudgetWitness.eta_dominated`.
Per the plan, that inequality rests on the **antitonicity of the
heat-kernel exponential `e^{−tΔ}` in the Casimir gap Δ** — larger gap ⇒
faster character-tail decay ⇒ smaller `Z_t` ⇒ smaller per-step `η`.

The exponential lives outside `Q'` (it is a genuine `CReal`), so the
antitone fact is a `CReal` statement.  The pure-`Q'` order wrappers it
feeds (the `K_lf = q/(1−q)` monotone wrapper, `recip_antitone`,
`finSum` budget-monotonicity) are already proven in `UniformBudget.lean`.
This module supplies the missing `CReal` core:

  * **`expNeg_antitone_leRat`** — the genuine antitone-in-argument fact:
    `a ≤ b ⟹ (any rational upper bound for e^{−a} is one for e^{−b})`.
    This is `E_antitone` at the *true* exponential (not the rational
    Padé surrogate, which cannot carry the irreducibly-exponential tail —
    cf. `ExpNeg.lean`'s design note).  Proof: `e^{−b} ≃ e^{−a}·e^{−(b−a)}`
    (addition law `expNeg_add_equiv` across the split `b ≃ a + (b−a)`),
    and `e^{−(b−a)} ≤ 1` (`expNeg_le_one`); the second factor is absorbed.
  * **`expNeg_scaled_antitone_leRat`** — scaled by heat-kernel time
    `t ≥ 0`: `Δ_a ≤ Δ_b ⟹` any rational bound for `e^{−t·Δ_a}` bounds
    `e^{−t·Δ_b}`.  This *is* "`e^{−tΔ}` non-increasing in Δ" — the S1
    obligation, discharged constructively.
  * **`charTerm_gap_antitone_leRat`** — the per-character-term consequence:
    a single heat-kernel term `dim²·e^{−t·C₂}` at the larger gap is
    dominated (as a rational upper bound) by the same term at the smaller
    gap.  This is the termwise input the `Z_t = Σ dim²·e^{−t·C₂}` sum
    monotonicity is built from.

# Transport to `eta_max` and the residual obligation

`RepData.eta_max` is a *free* `Q'` field: it carries no structural tie to
the Casimir gap `C2_fund`.  So the antitone-in-Δ exponential fact above,
by itself, cannot force `R.eta_max ≤ su2.eta_max` for an arbitrary `R` —
that step needs the (paper-layer) chain `Δ ↦ Z_t ↦ K_lf ↦ η_max` that
turns the gap into the per-step bound.  The antitone exponential is the
**analytic heart** of that chain; the chain's *assembly* (`Z_t` as an
explicit function of `R`'s Casimirs via the rank-general Weyl-dimension
majorant of `notes/uniform-character-tail-bound.md`) is the residual
rank-general step.

We therefore expose:

  * **`EtaGapMonotone R`** — the ONE named structural hypothesis (a
    `Type`-level `Prop` field per AGENTS.md Rule 2): the per-step bound is
    antitone in the Casimir gap *down to the SU(2) floor*, i.e.
    `Δ_su2 ≤ R.C2_fund ⟹ R.eta_max ≤ su2.eta_max`.  This is exactly the
    `Δ ↦ η` monotonicity whose analytic engine is the antitone exponential
    of this module; isolating it as one named field (the quarantine
    pattern the plan §3 prescribes) keeps the Lean chain axiom-clean and
    the analytic debt *named and bounded*, not faked.
  * **`uniformBudgetWitness_of_gapMonotone`** — builds
    `UniformBudgetWitness R` (hence discharges `eta_dominated`) from an
    `AdmissibleSimpleGroup R` (which supplies `Δ_su2 = 3/4 ≤ R.C2_fund`)
    plus an `EtaGapMonotone R` and the same-window fact.  For the SU(N)
    family the `EtaGapMonotone` premise is `decide`-able at the instance
    (the per-step bounds are concrete rationals); for the general group it
    is the paper-layer obligation whose engine is proven here.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` / `[propext, Quot.sound]`
(the `Quot.sound`/`omega` from `Nat`/`Int`).  No `Classical.*`, no
`sorryAx`, no `native_decide`.  See the `#print axioms` block at the end.
-/

import YMGap.Constructive.SU3CharFactor
import YMGap.RG.UniformBudget

namespace YMGap.RG

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.SU3CharFactor
open YMGap.RepTheory

/-! ## `Q'` gap-split helpers

For `a ≤ b` the gap `z := b − a` is nonnegative and `a + z ≃ b`.  These
are the two pure-`Q'` facts that turn the additive split `b = a + (b−a)`
into the exponential product `e^{−b} ≃ e^{−a}·e^{−(b−a)}` (via the
addition law) with the second factor `≤ 1`. -/

/-- **The gap is nonnegative.**  `a ≤ b ⟹ 0 ≤ b − a`.

Cross-multiplied (`Q'.le`/`Q'.sub`): `b − a = b + (−a)` has numerator
`b.num·a.den + (−a.num)·b.den` over `b.den·a.den`; nonnegativity is the
hypothesis `a.num·b.den ≤ b.num·a.den` rearranged, discharged by `omega`
with `↑(b.den·a.den) = ↑b.den·↑a.den`. -/
theorem sub_nonneg_of_le {a b : Q'} (hab : a ≤ b) : (0 : Q') ≤ b - a := by
  -- Goal: (0:Q') ≤ b + (-a), i.e. 0 · den ≤ (b+(-a)).num · 1.
  show (0 : Int) * (((b - a)).den : Int) ≤ ((b - a)).num * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  -- (b - a).num = b.num · a.den + (-a.num) · b.den  (Q'.add over Q'.neg).
  show (0 : Int) ≤ (b.num * (a.den : Int) + (-a.num) * (b.den : Int)) * (1 : Int)
  rw [Int.mul_one]
  have hle : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := hab
  have e1 : (-a.num) * (b.den : Int) = -(a.num * (b.den : Int)) := by rw [Int.neg_mul]
  rw [e1]
  omega

/-- **The split is exact.**  `b ≃ a + (b − a)`.

A direct rename of the substrate add–sub cancellation
`Q'.add_sub_cancel_eqv b a : b ≃ a + (b + −a)` (and `b − a = b + −a`
definitionally), recorded here for the antitone proof. -/
theorem split_eqv (a b : Q') : (b).eqv (a + (b - a)) :=
  Q'.add_sub_cancel_eqv b a

/-! ## The antitone exponential core (`E_antitone` at the true `e^{−x}`)

The genuine monotone input the plan flags as "the single most
load-bearing constructive obligation".  `e^{−x}` is non-increasing in
`x`: for `a ≤ b`, every rational upper bound for `e^{−a}` also bounds
`e^{−b}`.  This is the exact transport the budget chain consumes (it
feeds `leRat`-bounds of `Z_t` factors, which `K_lf`'s monotone wrapper
then turns into the per-step `η`). -/

/-- **`expNeg` antitone in its argument (transport form).**

For `0 ≤ a ≤ b`, any rational upper bound `c` for `e^{−a}` is also an
upper bound for `e^{−b}`:

    e^{−a} ≤ c   ⟹   e^{−b} ≤ c.

The constructive content of `a ≤ b ⟹ e^{−b} ≤ e^{−a}` (`E_antitone`),
proven at the *true* exponential via the addition law: `e^{−b} ≃
e^{−a}·e^{−(b−a)}` (`expNeg_add_equiv` transported across the exact split
`b ≃ a + (b−a)`, `add_sub_cancel_eqv` + `expNeg_eqv_congr`), and the gap
factor `e^{−(b−a)} ≤ 1` (`expNeg_le_one`) is absorbed via `leRat_mul`. -/
theorem expNeg_antitone_leRat {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b)
    (c : Q') (hc0 : (0 : Q') ≤ c)
    (hca : CReal.leRat (expNeg a ha) c) :
    CReal.leRat (expNeg b (Q'.le_trans' _ _ _ ha hab)) c := by
  -- z := b - a ≥ 0, and a + z ≃ b.
  have hz : (0 : Q') ≤ b - a := sub_nonneg_of_le hab
  have hsplit : (b).eqv (a + (b - a)) := split_eqv a b
  -- e^{−b} ≃ e^{−(a + z)} ≃ e^{−a}·e^{−z}, and e^{−a}·e^{−z} ≤ c·1 = c.
  -- Step A: e^{−(a+z)} ≤ c   (addition law + leRat_mul, absorbing e^{−z} ≤ 1).
  have hsum_nn : (0 : Q') ≤ a + (b - a) := Q'.zero_le_add a (b - a) ha hz
  have hAZ : CReal.leRat (expNeg (a + (b - a)) hsum_nn) c := by
    refine CReal.leRat_mono ?_ (Q'.le_of_eqv (Q'.mul_one_eqv c))
    refine CReal.leRat_of_equiv
      (CReal.Equiv.symm (expNeg_add_equiv a (b - a) ha hz)) ?_
    exact CReal.leRat_mul hca (expNeg_le_one (b - a) hz)
      (expNeg_geRat_zero _ _) (expNeg_geRat_zero _ _) hc0 (by decide)
  -- Step B: transport across b ≃ a + z.
  exact CReal.leRat_of_equiv
    (expNeg_eqv_congr (Q'.le_trans' _ _ _ ha hab) hsum_nn hsplit) hAZ

/-! ## Antitone in the Casimir gap, at heat-kernel time `t ≥ 0`

Scaling the argument by `t = conv/g² ≥ 0` is order-preserving, so the
antitone-in-argument fact becomes antitone-in-Δ: `e^{−t·Δ}` is
non-increasing in the gap Δ.  This is the S1 / `E_antitone` obligation in
its operating form (the heat-kernel time enters as the scale). -/

/-- **`t·Δ` monotone in Δ.**  For `t ≥ 0` and `Δ_a ≤ Δ_b`,
`t·Δ_a ≤ t·Δ_b`. -/
theorem tGap_mono {t Δa Δb : Q'} (ht : (0 : Q') ≤ t) (hΔ : Δa ≤ Δb) :
    t * Δa ≤ t * Δb :=
  Q'.mul_le_mul_of_nonneg_left Δa Δb t hΔ ht

/-- **`e^{−tΔ}` non-increasing in the Casimir gap Δ** (the S1 lemma).

For heat-kernel time `t ≥ 0` and gaps `0 ≤ Δ_a ≤ Δ_b`, any rational upper
bound for `e^{−t·Δ_a}` is also one for `e^{−t·Δ_b}`:

    e^{−t·Δ_a} ≤ c   ⟹   e^{−t·Δ_b} ≤ c.

Larger gap ⇒ faster tail decay ⇒ smaller heat-kernel weight.  This is the
antitone-in-Δ input the uniform character-tail bound is assembled from,
discharged constructively via `expNeg_antitone_leRat` at the scaled
argument `t·Δ`. -/
theorem expNeg_scaled_antitone_leRat {t Δa Δb : Q'}
    (ht : (0 : Q') ≤ t) (hΔa : (0 : Q') ≤ Δa) (hΔ : Δa ≤ Δb)
    (c : Q') (hc0 : (0 : Q') ≤ c)
    (hca : CReal.leRat (expNeg (t * Δa) (Q'.mul_nonneg t Δa ht hΔa)) c) :
    CReal.leRat (expNeg (t * Δb)
        (Q'.mul_nonneg t Δb ht (Q'.le_trans' _ _ _ hΔa hΔ))) c := by
  have htΔa : (0 : Q') ≤ t * Δa := Q'.mul_nonneg t Δa ht hΔa
  have htΔ : t * Δa ≤ t * Δb := tGap_mono ht hΔ
  -- expNeg_antitone_leRat at a := t·Δa, b := t·Δb; the two nonneg proofs
  -- are propositionally the same target (`0 ≤ t·Δb`), so leRat re-types.
  have h := expNeg_antitone_leRat htΔa htΔ c hc0 hca
  exact h

/-! ## Per-character-term consequence

A single heat-kernel term is `dim(λ)²·e^{−t·C₂(λ)}` (a `CReal`, the
prefactor `dim²` a rational times the exponential).  At the larger Casimir
gap the term is dominated, as a rational upper bound, by the term at the
smaller gap — the termwise input the `Z_t = Σ_λ dim²·e^{−t·C₂}` sum
monotonicity rests on.  We render the term as `ofQ'(dim²)·e^{−t·C₂}` and
push the gap antitonicity through the (nonneg) `dim²` prefactor with
`leRat_mul`. -/

/-- The single heat-kernel character term `dim²·e^{−t·C₂}` as a `CReal`,
with `dim² , C₂ ≥ 0`. -/
def charTermGap (dimSq t C2 : Q') (hC2 : (0 : Q') ≤ t * C2) : CReal :=
  CReal.mul (CReal.ofQ' dimSq) (expNeg (t * C2) hC2)

/-- **The character term is antitone in the Casimir gap.**

Fix `dim² ≥ 0` and heat-kernel time `t ≥ 0`.  For gaps `0 ≤ C₂a ≤ C₂b`,
if `dim²·e^{−t·C₂a} ≤ M` (a rational upper bound at the smaller gap) then
`dim²·e^{−t·C₂b} ≤ M` at the larger gap.  This is the termwise
"larger Δ ⇒ smaller `Z_t`-contribution", from `expNeg_scaled_antitone_leRat`
through the nonneg prefactor. -/
theorem charTerm_gap_antitone_leRat {dimSq t C2a C2b M : Q'}
    (hdim : (0 : Q') ≤ dimSq) (ht : (0 : Q') ≤ t)
    (hC2a : (0 : Q') ≤ C2a) (hC2 : C2a ≤ C2b)
    (hMfac : ∃ e : Q', (0 : Q') ≤ e ∧ M = dimSq * e ∧
        CReal.leRat (expNeg (t * C2a) (Q'.mul_nonneg t C2a ht hC2a)) e) :
    CReal.leRat (charTermGap dimSq t C2b
        (Q'.mul_nonneg t C2b ht (Q'.le_trans' _ _ _ hC2a hC2))) M := by
  -- Use the explicit per-factor witness `e ≥ e^{−t·C2a}`; antitonicity in Δ
  -- gives `e ≥ e^{−t·C2b}`, then `leRat_mul` on the (nonneg) prefactor.
  obtain ⟨e, he0, hMe, hea⟩ := hMfac
  have heb : CReal.leRat
      (expNeg (t * C2b) (Q'.mul_nonneg t C2b ht (Q'.le_trans' _ _ _ hC2a hC2))) e :=
    expNeg_scaled_antitone_leRat ht hC2a hC2 e he0 hea
  -- charTermGap = ofQ'(dim²)·e^{−t·C2b} ≤ dim²·e = M.
  show CReal.leRat
    (CReal.mul (CReal.ofQ' dimSq)
      (expNeg (t * C2b) (Q'.mul_nonneg t C2b ht (Q'.le_trans' _ _ _ hC2a hC2)))) M
  rw [hMe]
  exact CReal.leRat_mul (CReal.leRat_ofQ' (Q'.le_refl' dimSq)) heb
    (ExpPos.geRat_of_eventually ⟨0, fun _ _ => hdim⟩)
    (expNeg_geRat_zero _ _) hdim he0

/-! ## Transport to `eta_max` — the named structural obligation + constructor

The antitone exponential above is the engine of the gap → η monotonicity.
The *assembly* of that monotonicity for `eta_max` (a free `RepData` field)
is the residual rank-general step; we isolate it as ONE named hypothesis,
`EtaGapMonotone`, and build the `UniformBudgetWitness` from it. -/

/-- **The named gap → η monotonicity obligation.**

The per-step σ̂-degradation bound is antitone in the Casimir gap down to
the SU(2) floor: a group whose fundamental Casimir clears `Δ_su2 = 3/4`
has its per-step bound dominated by SU(2)'s.

This is the `Δ ↦ Z_t ↦ K_lf ↦ η_max` chain whose analytic engine is the
antitone exponential `expNeg_scaled_antitone_leRat` (this module) composed
with the proven `Q'` wrappers (`qOver1mq_mono`, `recip_antitone` of
`UniformBudget.lean`).  Its assembly as an explicit function of `R`'s
Casimirs (the rank-general Weyl-dimension `Z_t` majorant) is the
paper-layer residual; per AGENTS.md Rule 2 it is carried as one named
field, not faked.  For the SU(N) family it is `decide`-able at the
instance (concrete rational per-step bounds). -/
structure EtaGapMonotone (R : RepData) : Prop where
  /-- Gap-clears-floor ⟹ η-dominated.  The hypothesis `Casimir.gapFloor ≤
  R.C2_fund` is exactly `AdmissibleSimpleGroup.gap_lb`. -/
  eta_antitone : Casimir.gapFloor ≤ R.C2_fund → R.eta_max ≤ su2.eta_max

/-- **Build the budget witness from gap-monotonicity.**

Given an `AdmissibleSimpleGroup R` (which supplies the gap floor
`3/4 ≤ R.C2_fund` and the same `K = 3` window) and the named
`EtaGapMonotone R`, the η-domination `R.eta_max ≤ su2.eta_max` follows,
discharging `UniformBudgetWitness.eta_dominated`.

`same_window` is supplied by the caller (`R.K_steps = su2.K_steps`); for
the admissible SU(N) instances it is `decide`-able. -/
def uniformBudgetWitness_of_gapMonotone (R : RepData)
    (hadm : AdmissibleSimpleGroup R) (hmono : EtaGapMonotone R)
    (hwin : R.K_steps = su2.K_steps) :
    UniformBudgetWitness R where
  same_window   := hwin
  eta_dominated := hmono.eta_antitone hadm.gap_lb

/-! ## SU(N)-family discharge (the `decide`-able instances)

For the SU(N) instances the per-step bound is a concrete rational, so
`EtaGapMonotone` holds with the implication discharged by `decide` (the
conclusion `R.eta_max ≤ su2.eta_max` is a closed `Q'` inequality,
independent of the floor hypothesis).  This exhibits the constructor end
to end on real numbers; the general group supplies `EtaGapMonotone` from
the paper-layer chain whose engine is proven above. -/

/-- SU(2): η-domination is reflexive (`3e-4 ≤ 3e-4`), so `EtaGapMonotone`
holds. -/
theorem su2_etaGapMonotone : EtaGapMonotone su2 where
  eta_antitone := fun _ => by decide

/-- SU(3): per-step bound `13e-6 ≤ 3e-4`, so `EtaGapMonotone` holds. -/
theorem su3_etaGapMonotone : EtaGapMonotone su3 where
  eta_antitone := fun _ => by decide

/-- SU(2) budget witness, assembled through the gap-monotone constructor
(same `K = 3` window by `decide`). -/
def su2_uniform_witness_via_gap : UniformBudgetWitness su2 :=
  uniformBudgetWitness_of_gapMonotone su2 su2_admissible su2_etaGapMonotone (by decide)

/-- SU(3) budget witness, assembled through the gap-monotone constructor. -/
def su3_uniform_witness_via_gap : UniformBudgetWitness su3 :=
  uniformBudgetWitness_of_gapMonotone su3 su3_admissible su3_etaGapMonotone (by decide)

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.sub_nonneg_of_le
#print axioms YMGap.RG.split_eqv
#print axioms YMGap.RG.expNeg_antitone_leRat
#print axioms YMGap.RG.tGap_mono
#print axioms YMGap.RG.expNeg_scaled_antitone_leRat
#print axioms YMGap.RG.charTerm_gap_antitone_leRat
#print axioms YMGap.RG.uniformBudgetWitness_of_gapMonotone
#print axioms YMGap.RG.su2_etaGapMonotone
#print axioms YMGap.RG.su3_etaGapMonotone
#print axioms YMGap.RG.su2_uniform_witness_via_gap
#print axioms YMGap.RG.su3_uniform_witness_via_gap
