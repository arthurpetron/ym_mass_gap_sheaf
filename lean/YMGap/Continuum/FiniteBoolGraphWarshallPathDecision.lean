/-
# Executable directed-path decisions in a finite Boolean graph

This module turns the existing finite Warshall closure into the exact
`ChainIn` interface used by the constructive Boolean-graph compilers.
Warshall is run on an edge predicate which also records membership of every
edge target in the explicit finite support.  Consequently a successful
Boolean check extracts a support-certified chain without choice.

The converse is proved as well: every `ChainIn` makes the Boolean check true.
Thus a false check constructively refutes the existence of such a chain.  A
list-recursive family decision either returns chains for every demanded
endpoint pair or a literal endpoint pair whose exact reachability check is
false.

No symmetry assumption is made; directed deletion problems are supported.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.FiniteBoolGraphComponents
import YMGap.Continuum.FiniteSimpleWalk

namespace YMGap.Continuum.FiniteBoolGraphWarshallPathDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4CanonicalBipartitePath

/-! ## 1. Support-marked Warshall reachability -/

def supportMarkedAdjacentB {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (first next : State) : Bool :=
  adjacent first next && decide (next ∈ support)

def finiteSupportReachableB {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (first last : State) : Bool :=
  warshall (supportMarkedAdjacentB adjacent support) support first last

def ChainIn.ofSupportMarkedCWalk
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State) :
    {first last : State} ->
      CWalk (supportMarkedAdjacentB adjacent support) first last ->
        ChainIn adjacent support first last
  | _, _, CWalk.single first => ChainIn.refl first
  | _, _, CWalk.cons hedge rest =>
      let hparts := (Bool.and_eq_true _ _).mp hedge
      ChainIn.step hparts.1 (of_decide_eq_true hparts.2)
        (ChainIn.ofSupportMarkedCWalk adjacent support rest)

/-- A true finite reachability check extracts an actual support-certified
directed chain. -/
def chainInOfFiniteSupportReachableB
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (first last : State)
    (hreaches : finiteSupportReachableB adjacent support first last = true) :
    ChainIn adjacent support first last :=
  ChainIn.ofSupportMarkedCWalk adjacent support
    (CWalk.ofDWalk
      (warshallSound (supportMarkedAdjacentB adjacent support)
        support first last hreaches))

/-! ## 2. Completeness and exact failure -/

/-- Every support-certified chain is detected by the finite Warshall check. -/
theorem finiteSupportReachableB_complete
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State) :
    {first last : State} -> ChainIn adjacent support first last ->
      finiteSupportReachableB adjacent support first last = true
  | _, _, ChainIn.refl first => by
      exact warshall_refl
        (supportMarkedAdjacentB adjacent support) support first
  | first, last, ChainIn.step (b := next) hedge hnext rest => by
      apply warshall_trans_of_mem
        (supportMarkedAdjacentB adjacent support)
        support first next last hnext
      · apply warshall_edge
        exact (Bool.and_eq_true _ _).mpr
          ⟨hedge, decide_eq_true hnext⟩
      · exact finiteSupportReachableB_complete adjacent support rest

theorem noChainInOfFiniteSupportReachableBFalse
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    {first last : State}
    (hfalse : finiteSupportReachableB adjacent support first last = false) :
    ChainIn adjacent support first last -> False := by
  intro chain
  have htrue := finiteSupportReachableB_complete adjacent support chain
  rw [hfalse] at htrue
  cases htrue

inductive FiniteSupportPathDecision
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (first last : State) : Type
  | found (chain : ChainIn adjacent support first last)
  | blocked
      (check_false :
        finiteSupportReachableB adjacent support first last = false)

def decideFiniteSupportPath
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (first last : State) :
    FiniteSupportPathDecision adjacent support first last := by
  cases hcheck : finiteSupportReachableB adjacent support first last with
  | false => exact .blocked hcheck
  | true =>
      exact .found
        (chainInOfFiniteSupportReachableB
          adjacent support first last hcheck)

def FiniteSupportPathDecision.blockedNoChain
    {State : Type} [DecidableEq State]
    {adjacent : State -> State -> Bool} {support : List State}
    {first last : State}
    (hfalse : finiteSupportReachableB adjacent support first last = false) :
    ChainIn adjacent support first last -> False :=
  noChainInOfFiniteSupportReachableBFalse adjacent support hfalse

/-! ## 3. A finite demanded family of endpoint paths -/

def FiniteSupportPathFamily
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    (endpointPairs : List (State × State)) : Type :=
  forall endpointPair, endpointPair ∈ endpointPairs ->
    ChainIn adjacent support endpointPair.1 endpointPair.2

inductive FiniteSupportPathFamilyDecision
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State) :
    List (State × State) -> Type
  | found {endpointPairs : List (State × State)}
      (paths : FiniteSupportPathFamily adjacent support endpointPairs) :
      FiniteSupportPathFamilyDecision adjacent support endpointPairs
  | blocked {endpointPairs : List (State × State)}
      (endpointPair : State × State)
      (endpoint_mem : endpointPair ∈ endpointPairs)
      (check_false :
        finiteSupportReachableB adjacent support
          endpointPair.1 endpointPair.2 = false) :
      FiniteSupportPathFamilyDecision adjacent support endpointPairs

def decideFiniteSupportPathFamily
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State) :
    forall endpointPairs : List (State × State),
      FiniteSupportPathFamilyDecision adjacent support endpointPairs
  | [] =>
      .found (fun endpointPair hmem =>
        False.elim (List.not_mem_nil hmem))
  | endpointPair :: rest =>
      match decideFiniteSupportPath adjacent support
          endpointPair.1 endpointPair.2 with
      | .blocked hfalse =>
          .blocked endpointPair List.mem_cons_self hfalse
      | .found headPath =>
          match decideFiniteSupportPathFamily adjacent support rest with
          | .blocked blockedPair hmem hfalse =>
              .blocked blockedPair
                (List.mem_cons_of_mem endpointPair hmem) hfalse
          | .found tailPaths =>
              .found (fun pair hpair => by
                by_cases hhead : pair = endpointPair
                · subst pair
                  exact headPath
                · exact tailPaths pair
                    ((List.mem_cons.mp hpair).resolve_left hhead))

theorem finiteSupportPathFamilyImpossibleOfBlocked
    {State : Type} [DecidableEq State]
    (adjacent : State -> State -> Bool) (support : List State)
    {endpointPairs : List (State × State)}
    {endpointPair : State × State}
    (hmem : endpointPair ∈ endpointPairs)
    (hfalse : finiteSupportReachableB adjacent support
      endpointPair.1 endpointPair.2 = false) :
    FiniteSupportPathFamily adjacent support endpointPairs -> False := by
  intro paths
  exact noChainInOfFiniteSupportReachableBFalse adjacent support hfalse
    (paths endpointPair hmem)

/-! ## Axiom audit -/

#print axioms ChainIn.ofSupportMarkedCWalk
#print axioms chainInOfFiniteSupportReachableB
#print axioms finiteSupportReachableB_complete
#print axioms noChainInOfFiniteSupportReachableBFalse
#print axioms decideFiniteSupportPath
#print axioms FiniteSupportPathDecision.blockedNoChain
#print axioms decideFiniteSupportPathFamily
#print axioms finiteSupportPathFamilyImpossibleOfBlocked

end YMGap.Continuum.FiniteBoolGraphWarshallPathDecision
