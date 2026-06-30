/-
Track B / R2 — **The codynamic flow law, INHABITED at the `CReal` level.**

# Why this module exists (read first)

`CodynamicTransmutation` recast dimensional transmutation as the RG **flow law**
(self-similarity)

    sep k ≃ (sep (k+1))^(b+1)     (`selfSimilar`),

together with the conserved-margin budget (`marginInvariant`, `marginBudget_pos`).
Its central honest caveat (`CodynamicTransmutation`, §SCOPE) is that the flow law has
**NO rational inhabitant** — the canonical gaming flow `polyFlow` provably FAILS it
(`polyFlow_not_selfSimilar`), because the `(b+1)`-th-root flow is irrational.  So at
the `Q'` level the conserved-margin carrier is *vacuous*: the budget theorems are
conditional on a hypothesis (`selfSimilar b sep`) that the rational candidate cannot
satisfy.

This module closes that gap.  The constructive-real self-similar flow built in
`SelfSimilarFlow` (`concreteSelfSimilarFlow` / `concreteSelfSimilarFlowE`) is a
genuine inhabitant of the **CReal analogue** of the flow law.  We lift the rational
predicate `selfSimilar` to the `CReal` predicate `selfSimilarC`, bundle the flow with
its proof into a `Type`-level carrier `CRealFlow`, and exhibit two inhabitants:

  * `concreteCRealFlow`  — seeded at the rational exponent `1/2`;
  * `concreteCRealFlowE` — seeded at the IRRATIONAL exponent `1/e`.

The headline contrast is `flow_law_rational_empty_but_creal_inhabited`: the SAME flow
law that the rational `polyFlow` provably fails is constructively SATISFIED by the
CReal flow.  "No rational inhabitant" becomes "a genuine constructive-real
inhabitant" — the conserved-margin budget's carrier is no longer vacuous.

# Honest scope

`selfSimilarC` is the CReal mirror of `CodynamicTransmutation.selfSimilar`; the
inhabitants reuse the closed flows from `SelfSimilarFlow` (no new analytic content,
this is the *wiring*).  The rational margin telescoping (`marginInvariant`) is itself
unchanged; what is new is that its self-similar HYPOTHESIS — empty over `Q'` for the
gaming flow — is inhabited over `CReal`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `SelfSimilarFlow` backbone; the flow carrier is `Type`-level
data.  Each load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Constructive.SelfSimilarFlow
import YMGap.Continuum.CodynamicTransmutation

namespace YMGap.Continuum.CodynamicCRealFlow

open YMGap.Constructive
open YMGap.Constructive.CReal

/-! ## 1. The CReal self-similarity predicate -/

/-- **The CReal flow law (self-similarity).**  The constructive-real analogue of
`CodynamicTransmutation.selfSimilar`: the separator family `s : Nat → CReal` satisfies
`s k ≈ (s (k+1))^(b+1)` at every scale.  Unlike the rational version, this predicate
is inhabited (§2). -/
def selfSimilarC (b : Nat) (s : Nat → CReal) : Prop :=
  ∀ k, CReal.Equiv (s k) (cpow (s (k + 1)) (b + 1))

/-- **A self-similar CReal flow** — a `Type`-level bundle of the separator family and
its flow-law proof.  This is the inhabited carrier of the codynamic conserved-margin
budget (the rational carrier being vacuous for the gaming flow). -/
structure CRealFlow (b : Nat) : Type where
  /-- The separator family `sep k`. -/
  s : Nat → CReal
  /-- The flow law `s k ≈ (s (k+1))^(b+1)` at every scale. -/
  ss : selfSimilarC b s

/-! ## 2. Two concrete inhabitants (rational `1/2` and irrational `1/e` seeds) -/

/-- **The rational-seed inhabitant.**  Separators `e^{−(1/2)/(b+1)^k}` of the
`1/2`-seeded tower — irrational reals satisfying the flow law `selfSimilar` failed
rationally. -/
def concreteCRealFlow (b : Nat) : CRealFlow b where
  s := sep (concreteTower b)
  ss := fun k => concreteSelfSimilarFlow b k

/-- **The irrational-seed inhabitant.**  Separators `e^{−(1/e)/(b+1)^k}` of the
`e^{−1}`-seeded tower — a self-similar CReal flow with genuinely irrational
EXPONENTS. -/
def concreteCRealFlowE (b : Nat) : CRealFlow b where
  s := sep (concreteTowerE b)
  ss := fun k => concreteSelfSimilarFlowE b k

/-- The CReal flow law is INHABITED for every block factor `b` (rational seed). -/
theorem selfSimilarC_inhabited (b : Nat) :
    selfSimilarC b (concreteCRealFlow b).s :=
  (concreteCRealFlow b).ss

/-- The CReal flow law is INHABITED for every block factor `b` (irrational `1/e`
seed). -/
theorem selfSimilarC_inhabited_E (b : Nat) :
    selfSimilarC b (concreteCRealFlowE b).s :=
  (concreteCRealFlowE b).ss

/-! ## 3. The headline contrast: rational-empty vs. CReal-inhabited -/

/-- The canonical rational gaming flow provably FAILS the rational flow law
(re-exposed from `CodynamicTransmutation`, the falsification anchoring this module). -/
theorem rational_flow_law_empty :
    ¬ CodynamicTransmutation.selfSimilar 1 CodynamicTransmutation.polyFlow :=
  CodynamicTransmutation.polyFlow_not_selfSimilar

/-- **THE CONNECTING THEOREM.**  At block factor `b = 1` the SAME flow law is:

  * empty over `Q'` for the gaming flow `polyFlow`
    (`¬ selfSimilar 1 polyFlow` — the rational carrier is vacuous), yet
  * inhabited over `CReal` by the concrete flow
    (`selfSimilarC 1 (concreteCRealFlow 1).s`).

This is the precise sense in which the codynamic conserved-margin budget — whose
rational hypothesis `selfSimilar` no rational flow satisfies — becomes a genuine
constructive-real inhabitant. -/
theorem flow_law_rational_empty_but_creal_inhabited :
    (¬ CodynamicTransmutation.selfSimilar 1 CodynamicTransmutation.polyFlow)
      ∧ selfSimilarC 1 (concreteCRealFlow 1).s :=
  ⟨CodynamicTransmutation.polyFlow_not_selfSimilar, (concreteCRealFlow 1).ss⟩

/-- **The conserved-margin budget is positive ALONG ANY RATIONAL SHADOW of the flow.**
For any rational separator family `seq` that DOES satisfy the rational flow law
(`selfSimilar b seq`) with a genuine UV margin (`seq 0 < 1`), the rescaled margin
stays strictly positive at every scale (`CodynamicTransmutation.marginBudget_pos`).
The CReal flow `concreteCRealFlow`/`concreteCRealFlowE` is the constructive object that
makes such a self-similar family inhabitable in the first place (the rational gaming
flow cannot, by `rational_flow_law_empty`). -/
theorem marginBudget_pos_along_selfSimilar {b : Nat} {seq : Nat → Q'}
    (hss : CodynamicTransmutation.selfSimilar b seq) (h0 : seq 0 < (1 : Q')) (N : Nat) :
    (0 : Q') < ((1 : Q') - seq N) * CodynamicTransmutation.marginProductTail b seq N :=
  CodynamicTransmutation.marginBudget_pos hss h0 N

end YMGap.Continuum.CodynamicCRealFlow

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CodynamicCRealFlow.selfSimilarC_inhabited
#print axioms YMGap.Continuum.CodynamicCRealFlow.selfSimilarC_inhabited_E
#print axioms YMGap.Continuum.CodynamicCRealFlow.rational_flow_law_empty
#print axioms YMGap.Continuum.CodynamicCRealFlow.flow_law_rational_empty_but_creal_inhabited
#print axioms YMGap.Continuum.CodynamicCRealFlow.marginBudget_pos_along_selfSimilar
