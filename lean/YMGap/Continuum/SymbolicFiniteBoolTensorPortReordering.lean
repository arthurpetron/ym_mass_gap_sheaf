/-
# Constructive port reordering for symbolic Boolean tensors

The contraction layer needs a factor's free ports on the outside and its
shared ports in the innermost block.  This file supplies a small, typed
compiler for exactly that finite bookkeeping.  A program is an explicit
list of valid adjacent-coordinate swaps; validity is carried by its type,
so compilation neither searches through assignments nor extracts data from
an arbitrary `List.Perm` proof.

There are three independent certificates:

* the compiled `SignedBoolWiring` preserves the Boolean tensor Gram form;
* evaluation of the compiled wiring is exactly evaluation after the typed
  port tuple has run the same swap program;
* erasing a typed port tuple to a list runs the advertised list of adjacent
  swap positions.

For a concrete factor, the remaining finite obligation is deliberately
explicit: provide a program and prove that it sends that factor's source
port tuple to `outerThenInner freePorts sharedPorts`.  The final theorem then
puts the tensor in the `BoolTensor (shared + free)` convention consumed by
`boolTensorContract`, with the shared block innermost.  No arbitrary
permutation proof is eliminated into computational wiring data.

# Constructive discipline

All definitions and proofs recurse only over typed tuples and swap syntax.
There is no `Classical`, assignment enumeration, `native_decide`,
`sorry`/`admit`, or custom axiom.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensor

namespace YMGap.Continuum.SymbolicFiniteBoolTensor

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

/-! ## Length-indexed port tuples -/

/-- A port tuple whose length is present in its type.  Its head is the
outermost Boolean coordinate of a `BoolTensor`. -/
inductive PortTuple (alpha : Type) : Nat -> Type
  | nil : PortTuple alpha 0
  | cons {n : Nat} : alpha -> PortTuple alpha n -> PortTuple alpha (n + 1)

/-- Erase the length index while preserving port order. -/
def PortTuple.toList {alpha : Type} :
    {n : Nat} -> PortTuple alpha n -> List alpha
  | _, .nil => []
  | _, .cons head tail => head :: tail.toList

/-- Canonically package a list as a port tuple of exactly its list length.
This is structural data, so downstream tensor evaluation does not need a
length decision or an impossible mismatch branch. -/
def PortTuple.ofList {alpha : Type} :
    (entries : List alpha) -> PortTuple alpha entries.length
  | [] => .nil
  | head :: tail => .cons head (PortTuple.ofList tail)

/-- Pointwise relabelling without changing coordinate positions. -/
def PortTuple.map {alpha beta : Type} (f : alpha -> beta) :
    {n : Nat} -> PortTuple alpha n -> PortTuple beta n
  | _, .nil => .nil
  | _, .cons head tail => .cons (f head) (tail.map f)

/-- Package the pointwise image of a list while retaining the original
list-length index definitionally.  This transport-free companion to
`ofList` is useful when a tag list is converted to a Boolean assignment
tuple for evaluation of a tensor indexed by the tag-list length. -/
def PortTuple.ofListMap {alpha beta : Type} (f : alpha -> beta) :
    (entries : List alpha) -> PortTuple beta entries.length
  | [] => .nil
  | head :: tail => .cons (f head) (PortTuple.ofListMap f tail)

/-- Erasing a canonical list-derived tuple recovers the input list exactly. -/
theorem PortTuple.toList_ofList {alpha : Type} :
    forall entries : List alpha,
      (PortTuple.ofList entries).toList = entries
  | [] => rfl
  | head :: tail => by
      change head :: (PortTuple.ofList tail).toList = head :: tail
      exact congrArg (List.cons head) (PortTuple.toList_ofList tail)

/-- Erasing a pointwise-relabeled tuple is pointwise list relabelling. -/
theorem PortTuple.toList_map {alpha beta : Type} (f : alpha -> beta) :
    {n : Nat} -> (ports : PortTuple alpha n) ->
      (ports.map f).toList = ports.toList.map f
  | _, .nil => rfl
  | _, .cons head tail => by
      change
        f head :: (tail.map f).toList =
          f head :: tail.toList.map f
      exact congrArg (List.cons (f head)) (PortTuple.toList_map f tail)

/-- Mapping a canonical tuple is exactly the transport-free mapped-list
tuple.  Both sides retain the original list length in their type. -/
theorem PortTuple.map_ofList {alpha beta : Type} (f : alpha -> beta) :
    forall entries : List alpha,
      (PortTuple.ofList entries).map f =
        PortTuple.ofListMap f entries
  | [] => rfl
  | head :: tail => by
      change
        PortTuple.cons (f head) ((PortTuple.ofList tail).map f) =
          PortTuple.cons (f head) (PortTuple.ofListMap f tail)
      exact congrArg (PortTuple.cons (f head))
        (PortTuple.map_ofList f tail)

/-- Erasing the transport-free mapped-list tuple recovers `List.map`. -/
theorem PortTuple.toList_ofListMap {alpha beta : Type}
    (f : alpha -> beta) :
    forall entries : List alpha,
      (PortTuple.ofListMap f entries).toList = entries.map f
  | [] => rfl
  | head :: tail => by
      change
        f head :: (PortTuple.ofListMap f tail).toList =
          f head :: tail.map f
      exact congrArg (List.cons (f head))
        (PortTuple.toList_ofListMap f tail)

/-- In particular, mapping a canonical list-derived tuple has exactly the
expected erased Boolean/tag word. -/
theorem PortTuple.toList_map_ofList {alpha beta : Type}
    (f : alpha -> beta) (entries : List alpha) :
    ((PortTuple.ofList entries).map f).toList = entries.map f := by
  calc
    ((PortTuple.ofList entries).map f).toList =
        (PortTuple.ofList entries).toList.map f :=
      PortTuple.toList_map f (PortTuple.ofList entries)
    _ = entries.map f :=
      congrArg (List.map f) (PortTuple.toList_ofList entries)

theorem PortTuple.toList_length {alpha : Type} {n : Nat}
    (ports : PortTuple alpha n) :
    ports.toList.length = n := by
  induction ports with
  | nil => rfl
  | cons head tail ih =>
      change (head :: tail.toList).length = _
      exact congrArg Nat.succ ih

/-- Put `outer` before `inner`.  The result has arity `shared + free`
because addition computes recursively in `free`; hence the `free` ports are
the outer coordinates and the `shared` ports are the innermost block. -/
def PortTuple.outerThenInner {alpha : Type} {shared : Nat} :
    {free : Nat} ->
      PortTuple alpha free -> PortTuple alpha shared ->
        PortTuple alpha (shared + free)
  | 0, .nil, inner => inner
  | _ + 1, .cons head tail, inner =>
      .cons head (PortTuple.outerThenInner tail inner)

theorem PortTuple.toList_outerThenInner
    {alpha : Type} {free shared : Nat}
    (outer : PortTuple alpha free) (inner : PortTuple alpha shared) :
    (PortTuple.outerThenInner outer inner).toList =
      outer.toList ++ inner.toList := by
  induction outer with
  | nil => rfl
  | cons head tail ih =>
      change
        head :: (PortTuple.outerThenInner tail inner).toList =
          head :: (tail.toList ++ inner.toList)
      exact congrArg (fun entries => head :: entries) ih

theorem PortTuple.map_outerThenInner
    {alpha beta : Type} {free shared : Nat}
    (f : alpha -> beta)
    (outer : PortTuple alpha free) (inner : PortTuple alpha shared) :
    (PortTuple.outerThenInner outer inner).map f =
      PortTuple.outerThenInner (outer.map f) (inner.map f) := by
  induction outer with
  | nil => rfl
  | cons head tail ih =>
      change
        PortTuple.cons (f head)
            ((PortTuple.outerThenInner tail inner).map f) =
          PortTuple.cons (f head)
            (PortTuple.outerThenInner (tail.map f) (inner.map f))
      exact congrArg (PortTuple.cons (f head)) ih

/-! ## Evaluation and untyped list semantics -/

/-- Evaluate a curried Boolean tensor at a typed Boolean port tuple. -/
def evalAt : {n : Nat} -> BoolTensor n -> PortTuple Bool n -> Q'
  | 0, x, .nil => show Q' from x
  | _ + 1, x, .cons bit tail => evalAt (x bit) tail

/-- Total adjacent-list swap.  Valid typed programs below only encounter the
two-or-more-element branch at their selected position; the short-list cases
make the erased semantics a total standalone function. -/
def swapAdjacentAt {alpha : Type} : Nat -> List alpha -> List alpha
  | 0, first :: second :: tail => second :: first :: tail
  | 0, entries => entries
  | position + 1, head :: tail =>
      head :: swapAdjacentAt position tail
  | _ + 1, [] => []

theorem swapAdjacentAt_length {alpha : Type}
    (position : Nat) (entries : List alpha) :
    (swapAdjacentAt position entries).length = entries.length := by
  induction position generalizing entries with
  | zero =>
      cases entries with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => rfl
          | cons second rest => rfl
  | succ position ih =>
      cases entries with
      | nil => rfl
      | cons head tail =>
          change Nat.succ (swapAdjacentAt position tail).length =
            Nat.succ tail.length
          exact congrArg Nat.succ (ih tail)

/-- Execute adjacent-list swaps from left to right. -/
def runAdjacentSwaps {alpha : Type} : List Nat -> List alpha -> List alpha
  | [], entries => entries
  | position :: rest, entries =>
      runAdjacentSwaps rest (swapAdjacentAt position entries)

theorem runAdjacentSwaps_length {alpha : Type}
    (positions : List Nat) (entries : List alpha) :
    (runAdjacentSwaps positions entries).length = entries.length := by
  induction positions generalizing entries with
  | nil => rfl
  | cons position rest ih =>
      exact Eq.trans
        (ih (swapAdjacentAt position entries))
        (swapAdjacentAt_length position entries)

/-! ## One typed adjacent swap -/

/-- A valid adjacent-swap position in an `n`-port tuple.  `here` swaps the
first two ports; `there` moves a valid swap behind one untouched leading
port.  Thus an ill-scoped swap cannot be represented. -/
inductive AdjacentSwapStep : Nat -> Type
  | here (suffix : Nat) : AdjacentSwapStep (suffix + 2)
  | there {n : Nat} : AdjacentSwapStep n -> AdjacentSwapStep (n + 1)

/-- The zero-based list position selected by a typed adjacent swap. -/
def AdjacentSwapStep.position :
    {n : Nat} -> AdjacentSwapStep n -> Nat
  | _, .here _ => 0
  | _, .there step => Nat.succ step.position

/-- Construct the adjacent swap after `leading` untouched ports and before
`suffix` trailing ports. -/
def AdjacentSwapStep.at :
    (leading suffix : Nat) ->
      AdjacentSwapStep ((suffix + 2) + leading)
  | 0, suffix => .here suffix
  | leading + 1, suffix => .there (AdjacentSwapStep.at leading suffix)

theorem AdjacentSwapStep.position_at (leading suffix : Nat) :
    (AdjacentSwapStep.at leading suffix).position = leading := by
  induction leading with
  | zero => rfl
  | succ leading ih =>
      change Nat.succ (AdjacentSwapStep.at leading suffix).position =
        Nat.succ leading
      exact congrArg Nat.succ ih

/-- Compile one typed swap to the generic Gram-preserving wiring language. -/
def AdjacentSwapStep.toWiring :
    {n : Nat} -> AdjacentSwapStep n -> SignedBoolWiring n
  | _, .here suffix => .adjacentSwap suffix
  | _, .there step => .tailLift step.toWiring

/-- Apply one typed swap to a typed tuple of arbitrary port tags. -/
def AdjacentSwapStep.actTags {alpha : Type} :
    {n : Nat} -> AdjacentSwapStep n -> PortTuple alpha n -> PortTuple alpha n
  | _, .here _, .cons first (.cons second tail) =>
      .cons second (.cons first tail)
  | _, .there step, .cons head tail =>
      .cons head (step.actTags tail)

/-- Typed and erased-list semantics of one adjacent swap coincide exactly. -/
theorem AdjacentSwapStep.toList_actTags
    {alpha : Type} {n : Nat}
    (step : AdjacentSwapStep n) (ports : PortTuple alpha n) :
    (step.actTags ports).toList =
      swapAdjacentAt step.position ports.toList := by
  induction step with
  | here suffix =>
      cases ports with
      | cons first rest =>
          cases rest with
          | cons second tail => rfl
  | there step ih =>
      cases ports with
      | cons head tail =>
          change
            head :: (step.actTags tail).toList =
              head :: swapAdjacentAt step.position tail.toList
          exact congrArg (fun entries => head :: entries) (ih tail)

/-- A typed swap changes positions only, so it commutes with every
pointwise relabelling of the ports. -/
theorem AdjacentSwapStep.actTags_map
    {alpha beta : Type} {n : Nat}
    (step : AdjacentSwapStep n) (f : alpha -> beta)
    (ports : PortTuple alpha n) :
    step.actTags (ports.map f) = (step.actTags ports).map f := by
  induction step with
  | here suffix =>
      cases ports with
      | cons first rest =>
          cases rest with
          | cons second tail => rfl
  | there step ih =>
      cases ports with
      | cons head tail =>
          change
            PortTuple.cons (f head) (step.actTags (tail.map f)) =
              PortTuple.cons (f head) ((step.actTags tail).map f)
          exact congrArg (PortTuple.cons (f head)) (ih tail)

/-- Compiling one typed swap acts on tensor evaluation by the same swap of
the coordinate-tag tuple. -/
theorem AdjacentSwapStep.evalAt_toWiring
    {n : Nat} (step : AdjacentSwapStep n)
    (x : BoolTensor n) (ports : PortTuple Bool n) :
    evalAt (step.toWiring.act x) ports =
      evalAt x (step.actTags ports) := by
  induction step with
  | here suffix =>
      cases ports with
      | cons first rest =>
          cases rest with
          | cons second tail => rfl
  | there step ih =>
      cases ports with
      | cons head tail =>
          change
            evalAt (step.toWiring.act (x head)) tail =
              evalAt (x head) (step.actTags tail)
          exact ih (x head) tail

/-! ## Explicit lists of typed adjacent swaps -/

/-- An explicit left-to-right list of valid adjacent swaps at fixed arity. -/
inductive AdjacentSwapProgram (n : Nat) : Type
  | nil : AdjacentSwapProgram n
  | cons : AdjacentSwapStep n -> AdjacentSwapProgram n ->
      AdjacentSwapProgram n

/-- The advertised zero-based swap positions, in execution order. -/
def AdjacentSwapProgram.positions {n : Nat} :
    AdjacentSwapProgram n -> List Nat
  | .nil => []
  | .cons step rest => step.position :: rest.positions

/-- Execute a typed swap program on arbitrary port tags. -/
def AdjacentSwapProgram.actTags {alpha : Type} {n : Nat} :
    AdjacentSwapProgram n -> PortTuple alpha n -> PortTuple alpha n
  | .nil, ports => ports
  | .cons step rest, ports => rest.actTags (step.actTags ports)

/-- Compile a whole swap program.  The composition order is chosen so that
tensor evaluation runs tag swaps in the displayed left-to-right order. -/
def AdjacentSwapProgram.toWiring {n : Nat} :
    AdjacentSwapProgram n -> SignedBoolWiring n
  | .nil => .identity n
  | .cons step rest =>
      .compose step.toWiring rest.toWiring

/-- The typed program's tag action erases to exactly its advertised list of
adjacent swap positions. -/
theorem AdjacentSwapProgram.toList_actTags
    {alpha : Type} {n : Nat}
    (program : AdjacentSwapProgram n) (ports : PortTuple alpha n) :
    (program.actTags ports).toList =
      runAdjacentSwaps program.positions ports.toList := by
  induction program generalizing ports with
  | nil => rfl
  | cons step rest ih =>
      calc
        (rest.actTags (step.actTags ports)).toList =
            runAdjacentSwaps rest.positions (step.actTags ports).toList :=
          ih (step.actTags ports)
        _ = runAdjacentSwaps rest.positions
              (swapAdjacentAt step.position ports.toList) := by
          rw [step.toList_actTags ports]
        _ = runAdjacentSwaps (step.position :: rest.positions)
              ports.toList := rfl

/-- An entire swap program is likewise natural under port relabelling. -/
theorem AdjacentSwapProgram.actTags_map
    {alpha beta : Type} {n : Nat}
    (program : AdjacentSwapProgram n) (f : alpha -> beta)
    (ports : PortTuple alpha n) :
    program.actTags (ports.map f) = (program.actTags ports).map f := by
  induction program generalizing ports with
  | nil => rfl
  | cons step rest ih =>
      calc
        rest.actTags (step.actTags (ports.map f)) =
            rest.actTags ((step.actTags ports).map f) :=
          congrArg rest.actTags (step.actTags_map f ports)
        _ = (rest.actTags (step.actTags ports)).map f :=
          ih (step.actTags ports)

/-- Evaluation of the compiled wiring is exactly evaluation after running
the explicit tag-reordering program. -/
theorem AdjacentSwapProgram.evalAt_toWiring
    {n : Nat} (program : AdjacentSwapProgram n)
    (x : BoolTensor n) (ports : PortTuple Bool n) :
    evalAt (program.toWiring.act x) ports =
      evalAt x (program.actTags ports) := by
  induction program generalizing x ports with
  | nil => rfl
  | cons step rest ih =>
      change
        evalAt (step.toWiring.act (rest.toWiring.act x)) ports =
          evalAt x (rest.actTags (step.actTags ports))
      exact Eq.trans
        (step.evalAt_toWiring (rest.toWiring.act x) ports)
        (ih x (step.actTags ports))

/-- Every compiled port-reordering program preserves the full tensor Gram
form. -/
theorem AdjacentSwapProgram.gram_eqv
    {n : Nat} (program : AdjacentSwapProgram n)
    (x y : BoolTensor n) :
    boolTensorDot n (program.toWiring.act x) (program.toWiring.act y) ≈
      boolTensorDot n x y :=
  program.toWiring.gram_eqv x y

/-! ## The factor-to-contraction boundary -/

/-- A concrete program arranges a factor for contraction when its tag action
puts all free ports outside and the shared block inside.  This is kept as an
explicit equality certificate rather than converted from `List.Perm`. -/
def AdjacentSwapProgram.ArrangesAsOuterThenInner
    {alpha : Type} {free shared : Nat}
    (program : AdjacentSwapProgram (shared + free))
    (source : PortTuple alpha (shared + free))
    (freePorts : PortTuple alpha free)
    (sharedPorts : PortTuple alpha shared) : Prop :=
  program.actTags source =
    PortTuple.outerThenInner freePorts sharedPorts

/-- A certified arrangement has exactly the expected erased tag list. -/
theorem AdjacentSwapProgram.arranged_toList
    {alpha : Type} {free shared : Nat}
    (program : AdjacentSwapProgram (shared + free))
    (source : PortTuple alpha (shared + free))
    (freePorts : PortTuple alpha free)
    (sharedPorts : PortTuple alpha shared)
    (harrange : program.ArrangesAsOuterThenInner
      source freePorts sharedPorts) :
    runAdjacentSwaps program.positions source.toList =
      freePorts.toList ++ sharedPorts.toList := by
  calc
    runAdjacentSwaps program.positions source.toList =
        (program.actTags source).toList :=
      (program.toList_actTags source).symm
    _ = (PortTuple.outerThenInner freePorts sharedPorts).toList :=
      congrArg PortTuple.toList harrange
    _ = freePorts.toList ++ sharedPorts.toList :=
      PortTuple.toList_outerThenInner freePorts sharedPorts

/-- The exact evaluation bridge used immediately before
`boolTensorContract`: the compiled tensor wiring evaluates according to the
certified outer-free/inner-shared port order. -/
theorem AdjacentSwapProgram.evalAt_compiled_of_arranges
    {free shared : Nat}
    (program : AdjacentSwapProgram (shared + free))
    (source : PortTuple Bool (shared + free))
    (freePorts : PortTuple Bool free)
    (sharedPorts : PortTuple Bool shared)
    (x : BoolTensor (shared + free))
    (harrange : program.ArrangesAsOuterThenInner
      source freePorts sharedPorts) :
    evalAt (program.toWiring.act x) source =
      evalAt x (PortTuple.outerThenInner freePorts sharedPorts) := by
  calc
    evalAt (program.toWiring.act x) source =
        evalAt x (program.actTags source) :=
      program.evalAt_toWiring x source
    _ = evalAt x (PortTuple.outerThenInner freePorts sharedPorts) :=
      congrArg (evalAt x) harrange

/-- Tag-level arrangement controls every Boolean assignment to those tags.
This is the bridge a factor compiler uses: prove one finite equality of port
tags, then obtain the correct outer-free/inner-shared tensor evaluation for
an arbitrary valuation without enumerating assignments. -/
theorem AdjacentSwapProgram.evalAt_compiled_of_tag_arranges
    {alpha : Type} {free shared : Nat}
    (program : AdjacentSwapProgram (shared + free))
    (source : PortTuple alpha (shared + free))
    (freePorts : PortTuple alpha free)
    (sharedPorts : PortTuple alpha shared)
    (valuation : alpha -> Bool)
    (x : BoolTensor (shared + free))
    (harrange : program.ArrangesAsOuterThenInner
      source freePorts sharedPorts) :
    evalAt (program.toWiring.act x) (source.map valuation) =
      evalAt x (PortTuple.outerThenInner
        (freePorts.map valuation) (sharedPorts.map valuation)) := by
  calc
    evalAt (program.toWiring.act x) (source.map valuation) =
        evalAt x (program.actTags (source.map valuation)) :=
      program.evalAt_toWiring x (source.map valuation)
    _ = evalAt x ((program.actTags source).map valuation) :=
      congrArg (evalAt x) (program.actTags_map valuation source)
    _ = evalAt x
          ((PortTuple.outerThenInner freePorts sharedPorts).map valuation) :=
      congrArg (fun ports => evalAt x (ports.map valuation)) harrange
    _ = evalAt x (PortTuple.outerThenInner
          (freePorts.map valuation) (sharedPorts.map valuation)) :=
      congrArg (evalAt x)
        (PortTuple.map_outerThenInner valuation freePorts sharedPorts)

/-! ## Axiom audit -/

#print axioms PortTuple.outerThenInner
#print axioms PortTuple.ofList
#print axioms PortTuple.toList_ofList
#print axioms PortTuple.map_ofList
#print axioms PortTuple.toList_map_ofList
#print axioms swapAdjacentAt_length
#print axioms AdjacentSwapStep.toWiring
#print axioms AdjacentSwapStep.evalAt_toWiring
#print axioms AdjacentSwapProgram.toWiring
#print axioms AdjacentSwapProgram.toList_actTags
#print axioms AdjacentSwapProgram.evalAt_toWiring
#print axioms AdjacentSwapProgram.gram_eqv
#print axioms AdjacentSwapProgram.evalAt_compiled_of_arranges
#print axioms AdjacentSwapProgram.evalAt_compiled_of_tag_arranges

end YMGap.Continuum.SymbolicFiniteBoolTensor
