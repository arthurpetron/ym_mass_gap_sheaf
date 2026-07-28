/-
# Constructive compiler for certified degree-two Boolean tensor graphs

This module is the finite bookkeeping boundary between a tagged factor graph
and `BoolTensorContractionPlan`.  It deliberately does not turn a proof of
`List.Perm` into executable wiring.  Instead, every binary merge carries the
actual `AdjacentSwapProgram`s to run and exact equations saying what those
programs do to the port tags.

A merge exposes the same typed `sharedPorts` in its two children.  The
children's remaining ports are explicit, and the result convention is the
one forced by `boolTensorContract`: right-free ports are outermost, followed
by left-free ports.  Thus the syntax itself is an executable elimination
tree, including for graphs with odd cycles; no bipartition is assumed.

The separate `CertifiedDegreeTwoTaggedNetwork` records the incidence facts:

* no factor contains the same port tag twice;
* every internal edge tag and every surviving boundary tag is globally
  fresh in the one-copy ledger;
* the concatenated factor-port word is a permutation of two copies of every
  internal edge tag followed by the surviving boundary word.

The compiler never inspects the last proof.  It follows only the explicit
merge tree and its swap programs.  `compiled_eval_eq_taggedNetworkEval` then
identifies evaluation of the resulting contraction plan with the independent
recursive tagged-network evaluator.  The port-reordering lemma strengthens
this equality pointwise: under every tag valuation, each compiled rewire
evaluates at the advertised source ports.

The cutoff-one structure at the end states the exact remaining structural
obligation.  The existing global degree-two theorem proves the untyped
incidence permutation, but it cannot construct a merge tree or swap programs.
A later fixed-channel module must supply those programs, explicitly identify
its factor tensors in the advertised coordinate order, and prove the
displayed factor-word and edge-tag permutation laws.

# Constructive discipline

There is no `Classical`, Boolean assignment list, extraction from
`List.Perm`, `native_decide`, `sorry`/`admit`, or custom axiom.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensorContractionPlan
import YMGap.Continuum.SymbolicFiniteBoolTensorContractionEvaluation
import YMGap.Continuum.SymbolicFiniteBoolTensorPortReordering
import YMGap.Continuum.SU2QuaternionCutoffOneGlobalDegreeTwoPorts

namespace YMGap.Continuum.SymbolicFiniteBoolTensorDegreeTwoCompiler

open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SymbolicFiniteBoolTensorContraction
open YMGap.Continuum.SymbolicFiniteBoolTensorContractionEvaluation
open YMGap.Continuum.SymbolicFiniteBoolTensorContractionPlan

/-! ## 1. Executable, exact port reorderings -/

/-- An explicit reordering from `orderedPorts` to `sourcePorts`.

The direction of `tags_exact` is the direction required by tensor
evaluation: `program.toWiring.act x`, evaluated using `orderedPorts`, equals
`x` evaluated using `sourcePorts`.  No inverse permutation is inferred. -/
structure ExactPortReordering (Tag : Type) {n : Nat}
    (sourcePorts orderedPorts : PortTuple Tag n) where
  program : AdjacentSwapProgram n
  tags_exact : program.actTags orderedPorts = sourcePorts

/-- Exact semantic correctness of an explicit port-reordering program under
an arbitrary Boolean valuation of the tags. -/
theorem ExactPortReordering.evalAt_compiled
    {Tag : Type} {n : Nat}
    {sourcePorts orderedPorts : PortTuple Tag n}
    (reordering : ExactPortReordering Tag sourcePorts orderedPorts)
    (valuation : Tag -> Bool) (tensor : BoolTensor n) :
    evalAt (reordering.program.toWiring.act tensor)
        (orderedPorts.map valuation) =
      evalAt tensor (sourcePorts.map valuation) := by
  calc
    evalAt (reordering.program.toWiring.act tensor)
        (orderedPorts.map valuation) =
        evalAt tensor
          (reordering.program.actTags (orderedPorts.map valuation)) :=
      reordering.program.evalAt_toWiring tensor
        (orderedPorts.map valuation)
    _ = evalAt tensor
          ((reordering.program.actTags orderedPorts).map valuation) :=
      congrArg (evalAt tensor)
        (reordering.program.actTags_map valuation orderedPorts)
    _ = evalAt tensor (sourcePorts.map valuation) :=
      congrArg (fun ports => evalAt tensor (ports.map valuation))
        reordering.tags_exact

/-! ## 2. Explicit tagged merge trees -/

/-- An executable binary elimination tree for a tagged Boolean tensor graph.

The second index is the exact ordered boundary-port tuple of the represented
subnetwork.  A merge contracts `sharedPorts` between two disjoint child
subnetworks.  Both reordering certificates are data, not consequences
extracted from a propositional permutation witness.  `unit` is the empty
factor network required by empty cutoff support. -/
inductive TaggedDegreeTwoMergeTree (Tag : Type) :
    {n : Nat} -> PortTuple Tag n -> Type
  | unit : TaggedDegreeTwoMergeTree Tag
      (PortTuple.nil : PortTuple Tag 0)
  | leaf (n : Nat) (ports : PortTuple Tag n) (tensor : BoolTensor n) :
      TaggedDegreeTwoMergeTree Tag ports
  | merge (shared leftFree rightFree : Nat)
      (sharedPorts : PortTuple Tag shared)
      (leftFreePorts : PortTuple Tag leftFree)
      (rightFreePorts : PortTuple Tag rightFree)
      (leftPorts : PortTuple Tag (shared + leftFree))
      (rightPorts : PortTuple Tag (shared + rightFree))
      (left : TaggedDegreeTwoMergeTree Tag leftPorts)
      (right : TaggedDegreeTwoMergeTree Tag rightPorts)
      (leftReordering : ExactPortReordering Tag leftPorts
        (PortTuple.outerThenInner leftFreePorts sharedPorts))
      (rightReordering : ExactPortReordering Tag rightPorts
        (PortTuple.outerThenInner rightFreePorts sharedPorts)) :
      TaggedDegreeTwoMergeTree Tag
        (PortTuple.outerThenInner rightFreePorts leftFreePorts)

namespace TaggedDegreeTwoMergeTree

/-- Recursive tensor-valued evaluation of the tagged tensor network. -/
def taggedNetworkEval {Tag : Type} :
    {n : Nat} -> {ports : PortTuple Tag n} ->
      TaggedDegreeTwoMergeTree Tag ports -> BoolTensor n
  | _, _, .unit => (1 : YMGap.Constructive.Q')
  | _, _, .leaf _ _ tensor => tensor
  | _, _, .merge shared leftFree rightFree _ _ _ _ _ left right
      leftReordering rightReordering =>
      boolTensorContract shared leftFree rightFree
        (leftReordering.program.toWiring.act left.taggedNetworkEval)
        (rightReordering.program.toWiring.act right.taggedNetworkEval)

/-- Compile the explicit merge tree to the analytic contraction-plan
language.  Only executable tree fields are used. -/
def compile {Tag : Type} :
    {n : Nat} -> {ports : PortTuple Tag n} ->
      TaggedDegreeTwoMergeTree Tag ports -> BoolTensorContractionPlan n
  | _, _, .unit => .leaf 0 (1 : YMGap.Constructive.Q')
  | _, _, .leaf n _ tensor => .leaf n tensor
  | _, _, .merge shared leftFree rightFree _ _ _ _ _ left right
      leftReordering rightReordering =>
      .contract shared leftFree rightFree
        (.rewire (shared + leftFree)
          leftReordering.program.toWiring left.compile)
        (.rewire (shared + rightFree)
          rightReordering.program.toWiring right.compile)

/-- Evaluation of the compiled plan is exactly the recursively defined
tagged-network evaluation. -/
theorem compiled_eval_eq_taggedNetworkEval
    {Tag : Type} {n : Nat} {ports : PortTuple Tag n}
    (tree : TaggedDegreeTwoMergeTree Tag ports) :
    tree.compile.eval = tree.taggedNetworkEval := by
  induction tree with
  | unit => rfl
  | leaf n ports tensor => rfl
  | merge shared leftFree rightFree sharedPorts leftFreePorts rightFreePorts
      leftPorts rightPorts left right leftReordering rightReordering
      leftIH rightIH =>
      change
        boolTensorContract shared leftFree rightFree
            (leftReordering.program.toWiring.act left.compile.eval)
            (rightReordering.program.toWiring.act right.compile.eval) =
          boolTensorContract shared leftFree rightFree
            (leftReordering.program.toWiring.act left.taggedNetworkEval)
            (rightReordering.program.toWiring.act right.taggedNetworkEval)
      rw [leftIH, rightIH]

/-! ## 3. Literal nested-sum semantics -/

/-- Take the `outer` coordinates from a tuple of arity `inner + outer`.
This is structural in the exposed outer block. -/
def portTupleOuter {A : Type} (inner : Nat) :
    {outer : Nat} -> PortTuple A (inner + outer) -> PortTuple A outer
  | 0, _ => .nil
  | outer + 1, .cons head tail =>
      .cons head (portTupleOuter inner tail)

/-- Drop the exposed outer coordinates and retain the innermost block. -/
def portTupleInner {A : Type} (inner : Nat) :
    {outer : Nat} -> PortTuple A (inner + outer) -> PortTuple A inner
  | 0, ports => ports
  | outer + 1, .cons _ tail => portTupleInner inner tail

/-- Splitting an explicitly concatenated tuple recovers its outer block. -/
theorem portTupleOuter_outerThenInner
    {A : Type} {inner outer : Nat}
    (outerPorts : PortTuple A outer)
    (innerPorts : PortTuple A inner) :
    portTupleOuter inner
        (PortTuple.outerThenInner outerPorts innerPorts) = outerPorts := by
  induction outerPorts with
  | nil => rfl
  | cons head tail ih =>
      change
        PortTuple.cons head
            (portTupleOuter inner
              (PortTuple.outerThenInner tail innerPorts)) =
          PortTuple.cons head tail
      exact congrArg (PortTuple.cons head) ih

/-- Splitting an explicitly concatenated tuple recovers its inner block. -/
theorem portTupleInner_outerThenInner
    {A : Type} {inner outer : Nat}
    (outerPorts : PortTuple A outer)
    (innerPorts : PortTuple A inner) :
    portTupleInner inner
        (PortTuple.outerThenInner outerPorts innerPorts) = innerPorts := by
  induction outerPorts with
  | nil => rfl
  | cons head tail ih =>
      change
        portTupleInner inner
            (PortTuple.outerThenInner tail innerPorts) = innerPorts
      exact ih

/-- Every tuple is exactly its exposed outer block followed by its retained
inner block. -/
theorem outerThenInner_portTupleOuter_portTupleInner
    {A : Type} (inner : Nat) :
    forall {outer : Nat} (ports : PortTuple A (inner + outer)),
      PortTuple.outerThenInner
          (portTupleOuter inner ports) (portTupleInner inner ports) = ports
  | 0, ports => rfl
  | outer + 1, .cons head tail => by
      change
        PortTuple.cons head
            (PortTuple.outerThenInner
              (portTupleOuter inner tail) (portTupleInner inner tail)) =
          PortTuple.cons head tail
      exact congrArg (PortTuple.cons head)
        (outerThenInner_portTupleOuter_portTupleInner inner tail)

/-- **Literal factor-network semantics.**

At a leaf this evaluates the actual factor tensor.  At a merge it performs a
structural nested sum over the shared Boolean word and multiplies the two
child amplitudes.  This definition never calls `boolTensorContract`, never
forms a global assignment carrier, and never uses the incidence permutation
as executable data. -/
def scalarNetworkEval {Tag : Type} :
    {n : Nat} -> {ports : PortTuple Tag n} ->
      TaggedDegreeTwoMergeTree Tag ports -> PortTuple Bool n ->
        YMGap.Constructive.Q'
  | _, _, .unit, .nil => (1 : YMGap.Constructive.Q')
  | _, _, .leaf _ _ tensor, bits => evalAt tensor bits
  | _, _, .merge shared leftFree rightFree _ _ _ _ _ left right
      leftReordering rightReordering, bits =>
      boolTupleSum shared (fun sharedBits =>
        left.scalarNetworkEval
            (leftReordering.program.actTags
              (PortTuple.outerThenInner
                (portTupleInner leftFree bits) sharedBits)) *
          right.scalarNetworkEval
            (rightReordering.program.actTags
              (PortTuple.outerThenInner
                (portTupleOuter leftFree bits) sharedBits)))

/-- The recursive tensor evaluator has exactly the literal nested factor-sum
semantics at every boundary Boolean word. -/
theorem taggedNetworkEval_evalAt_eq_scalarNetworkEval
    {Tag : Type} {n : Nat} {ports : PortTuple Tag n}
    (tree : TaggedDegreeTwoMergeTree Tag ports) :
    forall bits : PortTuple Bool n,
      evalAt tree.taggedNetworkEval bits = tree.scalarNetworkEval bits := by
  induction tree with
  | unit =>
      intro bits
      cases bits
      rfl
  | leaf n ports tensor =>
      intro bits
      rfl
  | merge shared leftFree rightFree sharedPorts leftFreePorts rightFreePorts
      leftPorts rightPorts left right leftReordering rightReordering
      leftIH rightIH =>
      intro bits
      let rightBits := portTupleOuter leftFree bits
      let leftBits := portTupleInner leftFree bits
      have hbits :
          PortTuple.outerThenInner rightBits leftBits = bits :=
        outerThenInner_portTupleOuter_portTupleInner leftFree bits
      rw [← hbits]
      simp only [taggedNetworkEval, scalarNetworkEval,
        portTupleOuter_outerThenInner, portTupleInner_outerThenInner]
      rw [boolTensorContract_evalAt_eq_boolTupleSum]
      apply congrArg (boolTupleSum shared)
      funext sharedBits
      rw [leftReordering.program.evalAt_toWiring,
        rightReordering.program.evalAt_toWiring,
        leftIH, rightIH]

/-! ## 4. Incidence words carried by the executable tree -/

/-- The ordered port word of every factor leaf, retaining factor boundaries. -/
def factorPortWords {Tag : Type} :
    {n : Nat} -> {ports : PortTuple Tag n} ->
      TaggedDegreeTwoMergeTree Tag ports -> List (List Tag)
  | _, _, .unit => []
  | _, _, .leaf _ ports _ => [ports.toList]
  | _, _, .merge _ _ _ _ _ _ _ _ left right _ _ =>
      left.factorPortWords ++ right.factorPortWords

/-- The concatenated port word of all factor leaves. -/
def factorPortWord {Tag : Type} {n : Nat} {ports : PortTuple Tag n}
    (tree : TaggedDegreeTwoMergeTree Tag ports) : List Tag :=
  tree.factorPortWords.flatten

/-- Every internal edge tag, recorded once at the unique merge which
contracts it. -/
def internalEdgeTags {Tag : Type} :
    {n : Nat} -> {ports : PortTuple Tag n} ->
      TaggedDegreeTwoMergeTree Tag ports -> List Tag
  | _, _, .unit => []
  | _, _, .leaf _ _ _ => []
  | _, _, .merge _ _ _ sharedPorts _ _ _ _ left right _ _ =>
      left.internalEdgeTags ++ right.internalEdgeTags ++ sharedPorts.toList

/-- Repeat every entry twice, without requiring decidable equality. -/
def doubledWord {Tag : Type} : List Tag -> List Tag
  | [] => []
  | tag :: tags => tag :: tag :: doubledWord tags

/-- The recursive incidence word is exactly the flattened word obtained by
replacing every tag by its two occurrences.  This is the constructive bridge
from the compiler's ledger convention to concrete factor-port enumerations. -/
@[simp] theorem doubledWord_eq_flatMap_pair {Tag : Type} (tags : List Tag) :
    doubledWord tags = tags.flatMap (fun tag => [tag, tag]) := by
  induction tags with
  | nil => rfl
  | cons tag tags ih =>
      simp only [doubledWord, List.flatMap_cons, ih]

/-- Doubling commutes exactly with concatenation of incidence ledgers. -/
@[simp] theorem doubledWord_append {Tag : Type} (left right : List Tag) :
    doubledWord (left ++ right) = doubledWord left ++ doubledWord right := by
  induction left with
  | nil => rfl
  | cons tag left ih =>
      simp only [List.cons_append, doubledWord, ih]

/-- Every individual factor uses each tag at most once. -/
def FactorwiseNodup {Tag : Type} {n : Nat}
    {ports : PortTuple Tag n}
    (tree : TaggedDegreeTwoMergeTree Tag ports) : Prop :=
  forall word, word ∈ tree.factorPortWords -> word.Nodup

/-- Product of all leaf-tensor evaluations in factor-tree order under one
total named Boolean environment.  Merge wiring does not occur here: tags,
not positions, identify the two occurrences of every internal edge. -/
def flatFactorProduct {Tag : Type} :
    {n : Nat} -> {ports : PortTuple Tag n} ->
      TaggedDegreeTwoMergeTree Tag ports -> (Tag -> Bool) ->
        YMGap.Constructive.Q'
  | _, _, .unit, _ => (1 : YMGap.Constructive.Q')
  | _, _, .leaf _ ports tensor, environment =>
      evalAt tensor (ports.map environment)
  | _, _, .merge _ _ _ _ _ _ _ _ left right _ _, environment =>
      left.flatFactorProduct environment *
        right.flatFactorProduct environment

end TaggedDegreeTwoMergeTree

/-! ## 5. Explicit degree-two certification and compilation -/

/-! ### Canonical named Boolean sums -/

/-- Constructive update of one coordinate in a total named environment. -/
def namedBoolUpdate {Tag : Type} [DecidableEq Tag]
    (environment : Tag -> Bool) (tag : Tag) (value : Bool) : Tag -> Bool :=
  fun query => if query = tag then value else environment query

/-- Structurally bind the displayed tag word, starting from a supplied
environment.  No assignment list is constructed. -/
def namedQBoolSumFrom {Tag : Type} [DecidableEq Tag] :
    List Tag -> (Tag -> Bool) ->
      ((Tag -> Bool) -> YMGap.Constructive.Q') ->
        YMGap.Constructive.Q'
  | [], environment, family => family environment
  | tag :: tags, environment, family =>
      namedQBoolSumFrom tags (namedBoolUpdate environment tag false) family +
        namedQBoolSumFrom tags
          (namedBoolUpdate environment tag true) family

/-- Canonical named rational Boolean sum, with the constantly-false default
environment outside the displayed tag word. -/
def namedQBoolSum {Tag : Type} [DecidableEq Tag]
    (tags : List Tag)
    (family : (Tag -> Bool) -> YMGap.Constructive.Q') :
    YMGap.Constructive.Q' :=
  namedQBoolSumFrom tags (fun _ => false) family

/-- A certified finite degree-two tagged tensor network.

`incidence_exact` is deliberately a proof-only audit field.  The compiler
does not eliminate it into a permutation program.  The executable programs
already occur at every merge of `tree`. -/
structure CertifiedDegreeTwoTaggedNetwork (Tag : Type) {n : Nat}
    (boundaryPorts : PortTuple Tag n) where
  tree : TaggedDegreeTwoMergeTree Tag boundaryPorts
  factorwise_nodup : tree.FactorwiseNodup
  edge_boundary_ledger_nodup :
    (tree.internalEdgeTags ++ boundaryPorts.toList).Nodup
  incidence_exact :
    tree.factorPortWord.Perm
      (TaggedDegreeTwoMergeTree.doubledWord tree.internalEdgeTags ++
        boundaryPorts.toList)

/-- The exact remaining flat-Fubini statement for a closed certified tree:
its recursive contraction semantics is the canonical named sum of the flat
product of all factor leaves.  It is separated as a proposition because its
generic proof must use the freshness ledger to commute and distribute the
left, right, and newly shared binder blocks; no permutation proof may be
eliminated into executable wiring. -/
def HasFlatCanonicalNamedSemantics {Tag : Type} [DecidableEq Tag]
    (network : CertifiedDegreeTwoTaggedNetwork Tag
      (PortTuple.nil : PortTuple Tag 0)) : Prop :=
  network.tree.scalarNetworkEval .nil =
    namedQBoolSum network.tree.internalEdgeTags
      network.tree.flatFactorProduct

/-- Compile a certified graph.  The three proof fields are intentionally not
used computationally. -/
def CertifiedDegreeTwoTaggedNetwork.compile
    {Tag : Type} {n : Nat} {boundaryPorts : PortTuple Tag n}
    (network : CertifiedDegreeTwoTaggedNetwork Tag boundaryPorts) :
    BoolTensorContractionPlan n :=
  network.tree.compile

/-- Tagged-network evaluation before passage to the plan syntax. -/
def CertifiedDegreeTwoTaggedNetwork.taggedNetworkEval
    {Tag : Type} {n : Nat} {boundaryPorts : PortTuple Tag n}
    (network : CertifiedDegreeTwoTaggedNetwork Tag boundaryPorts) :
    BoolTensor n :=
  network.tree.taggedNetworkEval

/-- The honest compiler theorem: the compiled plan evaluates to the tagged
network value. -/
theorem CertifiedDegreeTwoTaggedNetwork.compiled_eval_eq_taggedNetworkEval
    {Tag : Type} {n : Nat} {boundaryPorts : PortTuple Tag n}
    (network : CertifiedDegreeTwoTaggedNetwork Tag boundaryPorts) :
    network.compile.eval = network.taggedNetworkEval :=
  network.tree.compiled_eval_eq_taggedNetworkEval

/-- Extensional semantics of the compiled plan: at every boundary Boolean
word it is the literal nested sum of products of the factor leaves. -/
theorem CertifiedDegreeTwoTaggedNetwork.compiled_evalAt_eq_scalarNetworkEval
    {Tag : Type} {n : Nat} {boundaryPorts : PortTuple Tag n}
    (network : CertifiedDegreeTwoTaggedNetwork Tag boundaryPorts)
    (bits : PortTuple Bool n) :
    evalAt network.compile.eval bits =
      network.tree.scalarNetworkEval bits := by
  rw [network.compiled_eval_eq_taggedNetworkEval]
  exact network.tree.taggedNetworkEval_evalAt_eq_scalarNetworkEval bits

/-- Once the constructive flat-Fubini obligation is supplied, the compiled
closed plan is exactly the canonical named Boolean sum/product. -/
theorem CertifiedDegreeTwoTaggedNetwork.compiled_eval_eq_namedQBoolSum
    {Tag : Type} [DecidableEq Tag]
    (network : CertifiedDegreeTwoTaggedNetwork Tag
      (PortTuple.nil : PortTuple Tag 0))
    (hflat : HasFlatCanonicalNamedSemantics network) :
    (show YMGap.Constructive.Q' from network.compile.eval) =
      namedQBoolSum network.tree.internalEdgeTags
        network.tree.flatFactorProduct := by
  calc
    (show YMGap.Constructive.Q' from network.compile.eval) =
        network.tree.scalarNetworkEval .nil :=
      network.compiled_evalAt_eq_scalarNetworkEval .nil
    _ = namedQBoolSum network.tree.internalEdgeTags
          network.tree.flatFactorProduct := hflat

/-- Closed certified networks compile to closed contraction plans. -/
abbrev CertifiedClosedDegreeTwoTaggedNetwork (Tag : Type) :=
  CertifiedDegreeTwoTaggedNetwork Tag (PortTuple.nil : PortTuple Tag 0)

/-- The certified empty factor network.  Its factor word and internal-edge
ledger are both empty, so it is the constructive unit needed when the
cutoff support is empty. -/
def certifiedUnitNetwork (Tag : Type) :
    CertifiedClosedDegreeTwoTaggedNetwork Tag where
  tree := .unit
  factorwise_nodup := by
    intro word hword
    cases hword
  edge_boundary_ledger_nodup := List.nodup_nil
  incidence_exact := List.Perm.nil

/-- The empty factor network compiles to the scalar unit plan. -/
theorem certifiedUnitNetwork_compile_eval (Tag : Type) :
    (show YMGap.Constructive.Q' from
      (certifiedUnitNetwork Tag).compile.eval) =
      (1 : YMGap.Constructive.Q') := rfl

/-- Its literal nested-sum semantics is also the empty product, namely one. -/
theorem certifiedUnitNetwork_scalarNetworkEval (Tag : Type) :
    (certifiedUnitNetwork Tag).tree.scalarNetworkEval .nil =
      (1 : YMGap.Constructive.Q') := rfl

/-- The flat canonical named-sum law is definitionally true for the empty
network. -/
theorem certifiedUnitNetwork_hasFlatCanonicalNamedSemantics
    (Tag : Type) [DecidableEq Tag] :
    HasFlatCanonicalNamedSemantics (certifiedUnitNetwork Tag) := rfl

/-- Exact scalar equality for a closed tagged network. -/
theorem CertifiedClosedDegreeTwoTaggedNetwork.compiled_scalar_exact
    {Tag : Type} (network : CertifiedClosedDegreeTwoTaggedNetwork Tag) :
    (show YMGap.Constructive.Q' from network.compile.eval) =
      (show YMGap.Constructive.Q' from network.taggedNetworkEval) :=
  network.compiled_eval_eq_taggedNetworkEval

/-! ## 6. Honest cutoff-one specialization boundary -/

namespace CutoffOne

open YMGap.Continuum.SU2QuaternionCutoffOneGlobalDegreeTwoPorts
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.SU2QuaternionCutoffOneNamedTraceExpansionProduct

/-- The factor-port words already fixed by the cutoff-one link-major,
target-before-source grouping. -/
def endpointFactorTagWords
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List (List Nat) :=
  (cutoffOneEndpointFactors orientationAt n support).map
    CutoffOneEndpointFactor.tags

/-- Concrete input still required from the fixed-channel network.

It supplies an actual closed merge tree with tensor leaves and swap programs.
The first equation identifies its leaf port words with the existing
cutoff-one factor grouping.  The second is intentionally only a permutation:
a sequential elimination scan chooses its own internal-edge order.  Neither
proof is used to manufacture executable wiring from
`cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts`.

Honest residual: this structural certificate does not by itself identify a
leaf tensor with the positive-channel tensor of its keyed cutoff-one factor.
That fixed-channel theorem must be supplied separately.  In particular, a
four-valent tensor whose native coordinate order is occurrence
`[1, 3, 2, 4]` must carry the explicit middle adjacent swap before its leaf
is advertised with the literal factor order `[1, 2, 3, 4]`. -/
structure CompilationCertificate
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) where
  network : CertifiedClosedDegreeTwoTaggedNetwork Nat
  factor_words_exact :
    network.tree.factorPortWords =
      endpointFactorTagWords orientationAt n support
  internal_edges_exact :
    network.tree.internalEdgeTags.Perm (cutoffOneCornerTags support)

/-- Empty cutoff support is represented by the certified empty factor
network, not by an artificial scalar factor leaf. -/
def emptyCompilationCertificate
    (orientationAt : CutoffOneFaceOrientationChoice) (n : Nat) :
    CompilationCertificate orientationAt n [] where
  network := certifiedUnitNetwork Nat
  factor_words_exact := rfl
  internal_edges_exact := List.Perm.nil

/-- The plan produced by a concrete cutoff-one compilation certificate. -/
def CompilationCertificate.compile
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    (certificate : CompilationCertificate orientationAt n support) :
    BoolTensorContractionPlan 0 :=
  certificate.network.compile

/-- End-to-end evaluator bridge for any supplied cutoff-one certificate. -/
theorem CompilationCertificate.compiled_eval_exact
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    (certificate : CompilationCertificate orientationAt n support) :
    (show YMGap.Constructive.Q' from certificate.compile.eval) =
      (show YMGap.Constructive.Q' from
        certificate.network.taggedNetworkEval) :=
  certificate.network.compiled_scalar_exact

/-- The empty-support cutoff plan evaluates to the multiplicative unit. -/
theorem emptyCompilationCertificate_compile_eval
    (orientationAt : CutoffOneFaceOrientationChoice) (n : Nat) :
    (show YMGap.Constructive.Q' from
      (emptyCompilationCertificate orientationAt n).compile.eval) =
      (1 : YMGap.Constructive.Q') := rfl

/-- A supplied cutoff-one certificate evaluates to its literal recursively
nested factor sum.  This is the semantic theorem later matched to the
existing `namedBoolSum` recursion. -/
theorem CompilationCertificate.compiled_eval_eq_scalarNetworkEval
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    (certificate : CompilationCertificate orientationAt n support) :
    (show YMGap.Constructive.Q' from certificate.compile.eval) =
      certificate.network.tree.scalarNetworkEval .nil :=
  certificate.network.compiled_evalAt_eq_scalarNetworkEval .nil

end CutoffOne

/-! ## Axiom audit -/

#print axioms ExactPortReordering.evalAt_compiled
#print axioms TaggedDegreeTwoMergeTree.taggedNetworkEval
#print axioms TaggedDegreeTwoMergeTree.compile
#print axioms TaggedDegreeTwoMergeTree.compiled_eval_eq_taggedNetworkEval
#print axioms TaggedDegreeTwoMergeTree.scalarNetworkEval
#print axioms TaggedDegreeTwoMergeTree.taggedNetworkEval_evalAt_eq_scalarNetworkEval
#print axioms TaggedDegreeTwoMergeTree.flatFactorProduct
#print axioms namedQBoolSum
#print axioms CertifiedDegreeTwoTaggedNetwork.compile
#print axioms CertifiedDegreeTwoTaggedNetwork.compiled_eval_eq_taggedNetworkEval
#print axioms CertifiedDegreeTwoTaggedNetwork.compiled_evalAt_eq_scalarNetworkEval
#print axioms CertifiedDegreeTwoTaggedNetwork.compiled_eval_eq_namedQBoolSum
#print axioms certifiedUnitNetwork_compile_eval
#print axioms certifiedUnitNetwork_hasFlatCanonicalNamedSemantics
#print axioms CertifiedClosedDegreeTwoTaggedNetwork.compiled_scalar_exact
#print axioms CutoffOne.CompilationCertificate.compiled_eval_exact
#print axioms CutoffOne.CompilationCertificate.compiled_eval_eq_scalarNetworkEval
#print axioms CutoffOne.emptyCompilationCertificate_compile_eval

end YMGap.Continuum.SymbolicFiniteBoolTensorDegreeTwoCompiler
