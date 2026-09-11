/-
CatStructural/StepBridge.lean

Residual (1): wiring `chainG` to the actual `singleStep` certificates.

The main tree's per-step data (`lean/YMGap/RG/BlockSpin.lean`) is
ADDITIVE: the Θ_k 2-cell `TwoCellTheta` carries
`(sigma_in, eta_k, sigma_out, decrease : sigma_in - eta_k ≤ sigma_out)`,
and an `Obligation_sigma` inhabitant, iterated from a `Valid` initial
state, emits exactly a σ̂-trajectory `sigma : Nat → V` with per-step
budgets `eta : Nat → V`, the S4 decrease at every scale, and V1
positivity at the anchor.  The categorical layer's morphisms are
MULTIPLICATIVE ratio dominations.  This file is the translation:

  `ThetaLedgerG` — the certificate trajectory, field-for-field the
  data an iterated `Obligation_sigma` witness produces:
    · `sigma k`        =  `s_k.sigmaHat`
    · `eta k`          =  `eta b g_k` (the chosen budget function at
                          the scale-k coupling)
    · `decrease k`     =  S4 at scale k
    · `anchor_pos`     =  V1 at the initial state
    · `residual_pos k` =  per-step survival `0 < σ̂_k − η_k`, the
                          scale-k consequence of the Phase-3 global
                          closure `Σ_k η_k < σ̂_0` (work_plan §10.4);
                          carried per-step here because the global
                          closure is 3.4's separate constructive-limit
                          obligation, per the `Rationals.lean` boundary
                          note.

  `stepOfTheta` — each additive certificate becomes the domination
  witness with ratio `(σ_k − η_k)/σ_k`: numerator = the residual,
  denominator = the current tension, bound = the S4 inequality
  scaled by `σ_k` (one `mul_le_mul_left`, one commutation — the
  decrease certificate is consumed AS-IS, and `sub` is passed as
  opaque data: the bridge needs NO subtraction laws).

  `thetaChain`/`theta_telescoped_bound` — the chain composite of the
  translated steps.  Its numerator and denominator are DEFINITIONALLY
  the folded products `∏(σ_k − η_k)` and `∏σ_k` (the `rfl` lemmas
  below), and its `bound` projection IS the global telescoped product
  inequality — obtained with zero induction over inequalities.

  `theta_gap_all` — gap persistence at every scale through the
  categorical route (`gap_persistsG`), agreeing with the direct
  3-line induction (`sigma_pos`) — stated separately so the audit can
  confirm the categorical route adds no hypotheses.

Promotion is now mechanical: instantiate `S` at `Q'`, `sub` at
`Q'.sub`, and feed the trajectory extracted from the main tree's
`step_obligation_witness` iteration.  Mathlib-free, Classical-free,
sorry-free.
-/

import CatStructural.Substrate
import CatStructural.DomOver
import CatStructural.QSpike

namespace CatStructural

variable {S : GapSubstrate}

/-- A σ̂-trajectory of per-step Θ-certificates: the exact data an
    iterated `Obligation_sigma` witness emits (see module docstring
    for the field-by-field correspondence).  `sub` is opaque data —
    no subtraction laws are demanded. -/
structure ThetaLedgerG (S : GapSubstrate)
    (sub : S.Carrier → S.Carrier → S.Carrier) where
  sigma : Nat → S.Carrier
  eta : Nat → S.Carrier
  /-- S4 at every scale: `σ̂_k − η_k ≤ σ̂_{k+1}`. -/
  decrease : ∀ k, S.le (sub (sigma k) (eta k)) (sigma (k + 1))
  /-- V1 at the anchor: `0 < σ̂_0`. -/
  anchor_pos : S.lt S.zero (sigma 0)
  /-- Per-step survival: `0 < σ̂_k − η_k`. -/
  residual_pos : ∀ k, S.lt S.zero (sub (sigma k) (eta k))

namespace ThetaLedgerG

variable {sub : S.Carrier → S.Carrier → S.Carrier}

/-- Direct positivity at every scale: the anchor case is V1; the
    successor case is survival chained through S4 (`lt_of_lt_of_le`).
    Three lines, no category theory — the control the categorical
    route (`theta_gap_all`) must and does agree with. -/
theorem sigma_pos (T : ThetaLedgerG S sub) : ∀ n, S.lt S.zero (T.sigma n)
  | 0 => T.anchor_pos
  | n + 1 => S.lt_of_lt_of_le (T.residual_pos n) (T.decrease n)

/-- The scale-`k` mass object carried by the trajectory. -/
def massOf (T : ThetaLedgerG S sub) (k : Nat) : MassG S :=
  ⟨T.sigma k, S.le_of_lt (T.sigma_pos k)⟩

/-- **The bridge**: an additive Θ-certificate becomes a multiplicative
    domination witness with ratio `(σ_k − η_k)/σ_k`.  The S4 decrease
    inequality is consumed as-is: scale by `σ_k ≥ 0` on the left and
    commute. -/
def stepOfTheta (T : ThetaLedgerG S sub) (k : Nat) :
    DomG (T.massOf k) (T.massOf (k + 1)) where
  num := sub (T.sigma k) (T.eta k)
  den := T.sigma k
  num_nonneg := S.le_of_lt (T.residual_pos k)
  den_pos := T.sigma_pos k
  bound :=
    S.le_trans
      (S.le_of_eqv (S.mul_comm_eqv (sub (T.sigma k) (T.eta k)) (T.sigma k)))
      (S.mul_le_mul_left (T.decrease k) (S.le_of_lt (T.sigma_pos k)))

/-- The categorical chain over the translated certificates. -/
def thetaChain (T : ThetaLedgerG S sub) (n : Nat) :
    DomG (T.massOf 0) (T.massOf n) :=
  chainG T.massOf T.stepOfTheta n

/-- Definitional transparency: the composite numerator at `n+1` IS the
    next residual times the previous composite numerator — `∏(σ−η)`
    as a fold, by `rfl`. -/
theorem chain_num_succ (T : ThetaLedgerG S sub) (n : Nat) :
    (T.thetaChain (n + 1)).num
      = S.mul (sub (T.sigma n) (T.eta n)) (T.thetaChain n).num := rfl

/-- Definitional transparency: the composite denominator at `n+1` IS
    the scale-`n` tension times the previous composite denominator —
    `∏σ` as a fold, by `rfl`. -/
theorem chain_den_succ (T : ThetaLedgerG S sub) (n : Nat) :
    (T.thetaChain (n + 1)).den
      = S.mul (T.sigma n) (T.thetaChain n).den := rfl

/-- **The telescoped product bound**, extracted from the composite by
    projection: `∏(σ_k − η_k) · σ̂_0 ≤ ∏σ_k · σ̂_n`.  This is the
    multiplicative global ledger of the additive per-step S4
    certificates, and it required no induction over inequalities —
    composition did the telescoping. -/
theorem theta_telescoped_bound (T : ThetaLedgerG S sub) (n : Nat) :
    S.le (S.mul (T.thetaChain n).num (T.sigma 0))
         (S.mul (T.thetaChain n).den (T.sigma n)) :=
  (T.thetaChain n).bound

/-- Composite numerators are positive: base = `0 < 1`, step =
    survival times induction hypothesis. -/
theorem chain_num_pos (T : ThetaLedgerG S sub) :
    ∀ n, S.lt S.zero (T.thetaChain n).num
  | 0 => S.zero_lt_one
  | n + 1 => S.mul_pos (T.residual_pos n) (T.chain_num_pos n)

/-- Gap persistence at every scale through the CATEGORICAL route:
    `gap_persistsG` applied to the translated certificates.  Same
    proposition as `sigma_pos` — the audit point is that the
    categorical derivation consumes exactly the same hypotheses
    (anchor V1 + per-step survival + S4), no more. -/
theorem theta_gap_all (T : ThetaLedgerG S sub) (n : Nat) :
    S.lt S.zero (T.sigma n) :=
  gap_persistsG T.massOf T.stepOfTheta T.anchor_pos T.chain_num_pos n

end ThetaLedgerG

namespace ThetaDemo

/-! ## Kernel-decided Θ-ledger over the setoid substrate

A three-phase σ̂-trajectory `1 → 3/4 → 5/8 → 5/8 → …` with budgets
`η = 1/4, 1/8, 0, 0, …` — every S4 certificate, survival condition,
and the tightness of the telescoped bound checked by kernel `decide`
on unnormalized `QS` data (`Q'`'s exact representation). -/

def dSigma : Nat → QS
  | 0 => ⟨1, 0⟩          -- σ̂_0 = 1
  | 1 => ⟨3, 3⟩          -- σ̂_1 = 3/4
  | _ + 2 => ⟨5, 7⟩      -- σ̂_k = 5/8 thereafter

def dEta : Nat → QS
  | 0 => ⟨1, 3⟩          -- η_0 = 1/4
  | 1 => ⟨1, 7⟩          -- η_1 = 1/8
  | _ + 2 => QS.zero     -- η_k = 0 thereafter

/-- Tail S4, as a closed proposition for the wildcard match arm. -/
theorem tail_decrease :
    qSubstrate.le (QS.sub ⟨5, 7⟩ QS.zero) ⟨5, 7⟩ := by decide

/-- Tail survival, as a closed proposition. -/
theorem tail_residual_pos :
    qSubstrate.lt qSubstrate.zero (QS.sub ⟨5, 7⟩ QS.zero) := by decide

/-- The demo trajectory as a `ThetaLedgerG` over the `Q'`-mirror
    substrate with `Q'.sub`'s mirror as the opaque subtraction. -/
def demoLedger : ThetaLedgerG qSubstrate QS.sub where
  sigma := dSigma
  eta := dEta
  decrease k := by
    match k with
    | 0 => decide
    | 1 => decide
    | _ + 2 => exact tail_decrease
  anchor_pos := by decide
  residual_pos k := by
    match k with
    | 0 => decide
    | 1 => decide
    | _ + 2 => exact tail_residual_pos

/-- Gap persistence for the demo, via the categorical route. -/
theorem demo_gap_all (n : Nat) :
    qSubstrate.lt qSubstrate.zero (dSigma n) :=
  demoLedger.theta_gap_all n

/-- **Tightness of the telescoped bound at n = 2**, kernel-checked:
    the composite's `∏(σ−η)·σ̂_0` and `∏σ·σ̂_2` are semantically EQUAL
    (`60/128 ≈ 15/32` — cross-product `60·32 = 15·128`), i.e. the
    categorical composite reproduces the additive ledger's telescoping
    exactly, with no slack introduced by the translation. -/
theorem demo_telescoping_tight :
    QS.eqv (QS.mul (demoLedger.thetaChain 2).num (dSigma 0))
           (QS.mul (demoLedger.thetaChain 2).den (dSigma 2)) := by
  decide

end ThetaDemo

#print axioms ThetaLedgerG.stepOfTheta
#print axioms ThetaLedgerG.theta_telescoped_bound
#print axioms ThetaLedgerG.theta_gap_all
#print axioms ThetaDemo.demo_gap_all
#print axioms ThetaDemo.demo_telescoping_tight

end CatStructural
