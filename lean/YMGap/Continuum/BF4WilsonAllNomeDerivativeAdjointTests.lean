/-
# Adjoint pairing tests characterize the original graph on its witnessed sector

There is a direct route, without first constructing a resolvent: symmetry
turns the core pairing tests into Au=T(1)v, and the proved two-coordinate
range criterion constructs the graph. Thus no additional weak adjoint
pairs occur within the explicitly witnessed original time-range sector.

The sector restriction is essential: ambient boundary-kernel components
can be invisible to the pairing tests. This is a precise graph-pairing
criterion, not yet a packaged Hilbert-space adjoint/self-adjoint operator,
a resolvent construction, or a physical Hamiltonian identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeAdjointTests

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (derivativeAction_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit core)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm (graph_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
  (graphOfEquation graphOfEquation_representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum (inverseSumRepresentative)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- Actual core tests, using the original time and derivative, not an
arbitrary operator family. No computational witness is hidden here. -/
def CorePairings (u v : V) : Prop := ∀ x : V, B u (A x) = B v (T 1 x)

/-- Pairing tests against EVERY existing witnessed graph pair. -/
def GraphPairings (u v : V) : Prop :=
  ∀ x y : V, GraphLimit hw0 hw1 x y → B u y = B v x

theorem corePairings_iff_equation (u v : V) :
    CorePairings hw0 hw1 u v ↔ A u = T 1 v := by
  constructor
  · intro h
    apply completed_eq_of_pairings hw0 hw1
    intro x
    rw [derivativeAction_symmetric,completedInner_time_balance]
    exact h x
  · intro h x
    rw [← derivativeAction_symmetric,← completedInner_time_balance,h]

theorem graph_pairings {u v : V} (G : GraphLimit hw0 hw1 u v) :
    GraphPairings hw0 hw1 u v :=
  fun _ _ H => (graph_symmetric hw0 hw1 G H).symm

theorem graphPairings_core {u v : V} (h : GraphPairings hw0 hw1 u v) :
    CorePairings hw0 hw1 u v :=
  fun x => h (T 1 x) (A x) (core hw0 hw1 x)

/-- The core tests suffice once both candidate coordinates belong to the
witnessed sector. The graph and its modulus are constructed, not assumed. -/
def graphOfCorePairings {u v : V} (Ru : RangeLimit hw0 hw1 u)
    (Rv : RangeLimit hw0 hw1 v) (h : CorePairings hw0 hw1 u v) :
    GraphLimit hw0 hw1 u v :=
  graphOfEquation hw0 hw1 Ru Rv ((corePairings_iff_equation hw0 hw1 u v).mp h)

def graphOfPairings {u v : V} (Ru : RangeLimit hw0 hw1 u)
    (Rv : RangeLimit hw0 hw1 v) (h : GraphPairings hw0 hw1 u v) :
    GraphLimit hw0 hw1 u v :=
  graphOfCorePairings hw0 hw1 Ru Rv (graphPairings_core hw0 hw1 h)

theorem corePairings_iff_graphPairings {u v : V}
    (Ru : RangeLimit hw0 hw1 u) (Rv : RangeLimit hw0 hw1 v) :
    CorePairings hw0 hw1 u v ↔ GraphPairings hw0 hw1 u v :=
  ⟨fun h => graph_pairings hw0 hw1 (graphOfCorePairings hw0 hw1 Ru Rv h),
    graphPairings_core hw0 hw1⟩

/-- Return actual graph-source data from the weak pairing criterion,
without countable selection of representatives or an assumed resolvent. -/
def representedGraphOfPairings (U V' : (D).Cauchy)
    (Ru : RangeLimit hw0 hw1 (Class U)) (Rv : RangeLimit hw0 hw1 (Class V'))
    (h : GraphPairings hw0 hw1 (Class U) (Class V')) :
    Σ' G : GraphLimit hw0 hw1 (Class U) (Class V'),
      Σ' preimages : Nat → (D).Cauchy,
        ∀ n, Class (preimages n) = G.source n :=
  ⟨graphOfPairings hw0 hw1 Ru Rv h,
    (fun n => inverseSumRepresentative hw0 hw1 n U),
    graphOfEquation_representative_pin hw0 hw1 U Ru Rv
      ((corePairings_iff_equation hw0 hw1 (Class U) (Class V')).mp
        (graphPairings_core hw0 hw1 h))⟩

#print axioms CorePairings
#print axioms GraphPairings
#print axioms corePairings_iff_equation
#print axioms graph_pairings
#print axioms graphPairings_core
#print axioms graphOfCorePairings
#print axioms graphOfPairings
#print axioms corePairings_iff_graphPairings
#print axioms representedGraphOfPairings

end YMGap.Continuum.BF4WilsonAllNomeDerivativeAdjointTests
