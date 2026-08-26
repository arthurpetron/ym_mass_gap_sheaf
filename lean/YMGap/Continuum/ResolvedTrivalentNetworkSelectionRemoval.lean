/-
# Compile a mate-closed strand selection into coherent fusion removal

A global face-strand component should enter a resolved link only through its
Boolean characteristic function.  Pushing dependent terminal witnesses into
the global component graph and reconstructing them later is unnecessary.
Instead, pull the characteristic function back to every graph-edge strand
copy.  If the resulting selection is invariant under the exact local
trivalent mate, finite counting gives the three removal multiplicities
`(ab,bc,ca)` and one common edge-drop labelling.

This module proves that conservation theorem.  The key equalities are the
literal discrete Kirchhoff laws

    drop(a) = removed(ca) + removed(ab),
    drop(b) = removed(bc) + removed(ab),
    drop(c) = removed(bc) + removed(ca).

They compile structurally over an arbitrary resolved trivalent network into
the existing `ResolvedTrivalentRemovalPlan`.  Specialization to an accepted
corrected-slab link therefore constructs an actually accepted lower auxiliary
witness, assuming only the external physical labels realize the computed
drops.

Honest scope: the module consumes a mate-closed selection.  Constructing that
selection from one seed-generated global face-strand component, and proving
the global external-label equation and inverse-encoding bound, remain open.

Constructive contract: primitive recursion on natural intervals and the
ordered resolved-vertex list only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval

namespace YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity

/-! ## 1. Constructive counting on a translated natural interval -/

/-- The natural indicator of a Boolean. -/
def boolIndicator : Bool -> Nat
  | false => 0
  | true => 1

/-- Count selected integers in the half-open interval
`[start, start + length)`. -/
def boolCountFrom (selected : Nat -> Bool) (start : Nat) : Nat -> Nat
  | 0 => 0
  | Nat.succ length =>
      boolIndicator (selected start) +
        boolCountFrom selected (start + 1) length

/-- Splitting an interval splits its Boolean count exactly. -/
theorem boolCountFrom_add
    (selected : Nat -> Bool) (start left right : Nat) :
    boolCountFrom selected start (left + right) =
      boolCountFrom selected start left +
        boolCountFrom selected (start + left) right := by
  induction left generalizing start with
  | zero => simp [boolCountFrom]
  | succ left ih =>
      rw [Nat.succ_add, boolCountFrom, boolCountFrom, ih]
      have hstart : start + 1 + left = start + (left + 1) := by
        omega
      rw [hstart]
      exact (Nat.add_assoc _ _ _).symm

/-- A Boolean interval count never exceeds the interval length. -/
theorem boolCountFrom_le
    (selected : Nat -> Bool) (start length : Nat) :
    boolCountFrom selected start length <= length := by
  induction length generalizing start with
  | zero => simp [boolCountFrom]
  | succ length ih =>
      rw [boolCountFrom]
      cases hselected : selected start <;>
        simp [boolIndicator] <;>
        have htail := ih (start + 1) <;>
        omega

/-- Pointwise equal selections on two translated intervals have equal
counts. -/
theorem boolCountFrom_congr
    (left right : Nat -> Bool) (leftStart rightStart length : Nat)
    (heq : forall offset, offset < length ->
      left (leftStart + offset) = right (rightStart + offset)) :
    boolCountFrom left leftStart length =
      boolCountFrom right rightStart length := by
  induction length generalizing leftStart rightStart with
  | zero => rfl
  | succ length ih =>
      rw [boolCountFrom, boolCountFrom]
      have hzero := heq 0 (by omega)
      simp only [Nat.add_zero] at hzero
      rw [hzero]
      congr 1
      apply ih
      intro offset hoffset
      have hnext := heq (offset + 1) (by omega)
      have hleft : leftStart + 1 + offset =
          leftStart + (offset + 1) := by
        omega
      have hright : rightStart + 1 + offset =
          rightStart + (offset + 1) := by
        omega
      rw [hleft, hright]
      exact hnext

/-! ## 2. The local discrete conservation theorem -/

/-- A Boolean choice of strand copies at one trivalent vertex, invariant
under the exact local strand mate.  Values outside the bounded leg ranges are
irrelevant; this unbounded presentation keeps interval arithmetic simple and
all semantically used slots remain bounded by typed ports. -/
structure TrivalentMateClosedSelection
    {a b c : Nat} (resolution : TrivalentStrandResolution a b c) : Type where
  selected : TrivalentLeg -> Nat -> Bool
  mate_closed : forall port : TrivalentStrandPort a b c,
    selected (strandMate resolution port).leg
        (strandMate resolution port).slot =
      selected port.leg port.slot

/-- Selected strands in the `ab` bundle, represented on the final `ab`
slots of leg `a`. -/
def TrivalentMateClosedSelection.abCount
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) : Nat :=
  boolCountFrom (selection.selected .a) resolution.ca resolution.ab

/-- Selected strands in the `bc` bundle, represented on the initial `bc`
slots of leg `b`. -/
def TrivalentMateClosedSelection.bcCount
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) : Nat :=
  boolCountFrom (selection.selected .b) 0 resolution.bc

/-- Selected strands in the `ca` bundle, represented on the initial `ca`
slots of leg `a`. -/
def TrivalentMateClosedSelection.caCount
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) : Nat :=
  boolCountFrom (selection.selected .a) 0 resolution.ca

/-- The selected-copy count on a whole trivalent leg. -/
def TrivalentMateClosedSelection.legCount
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution)
    (leg : TrivalentLeg) : Nat :=
  boolCountFrom (selection.selected leg) 0 (legSize a b c leg)

/-- Counting the three selected bundles gives a bounded simultaneous strand
removal. -/
def TrivalentMateClosedSelection.removal
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) :
    TrivalentStrandRemoval resolution where
  ab := selection.abCount
  bc := selection.bcCount
  ca := selection.caCount
  ab_le := boolCountFrom_le _ _ _
  bc_le := boolCountFrom_le _ _ _
  ca_le := boolCountFrom_le _ _ _

/-- On leg `a`, the initial `ca` block and final `ab` block are a literal
partition, so no mate equation is needed. -/
theorem TrivalentMateClosedSelection.legCount_a
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) :
    selection.legCount .a =
      selection.removal.ca + selection.removal.ab := by
  have ha := resolution.a_balance
  unfold TrivalentMateClosedSelection.legCount
    TrivalentMateClosedSelection.removal
    TrivalentMateClosedSelection.caCount
    TrivalentMateClosedSelection.abCount
    legSize
  calc
    boolCountFrom (selection.selected .a) 0 a =
        boolCountFrom (selection.selected .a) 0
          (resolution.ca + resolution.ab) :=
      congrArg (boolCountFrom (selection.selected .a) 0) ha
    _ = boolCountFrom (selection.selected .a) 0 resolution.ca +
          boolCountFrom (selection.selected .a) resolution.ca
            resolution.ab :=
      by
        simpa using
          (boolCountFrom_add (selection.selected .a) 0
            resolution.ca resolution.ab)

/-- The `ab` block has the same count on legs `a` and `b`, by local
mate-closure. -/
theorem TrivalentMateClosedSelection.abCount_on_b
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) :
    boolCountFrom (selection.selected .b) resolution.bc resolution.ab =
      selection.abCount := by
  unfold TrivalentMateClosedSelection.abCount
  apply boolCountFrom_congr
  intro offset hoffset
  let port : TrivalentStrandPort a b c :=
    .onA <| Fin.mk (resolution.ca + offset) (by
      have ha := resolution.a_balance
      omega)
  have hclosed := selection.mate_closed port
  have hnot : ¬ resolution.ca + offset < resolution.ca := by
    omega
  have hsub : resolution.ca + offset - resolution.ca = offset := by
    omega
  simp only [port, strandMate] at hclosed
  rw [dif_neg hnot] at hclosed
  simp only [TrivalentStrandPort.leg,
    TrivalentStrandPort.slot] at hclosed
  rw [hsub] at hclosed
  exact hclosed

/-- On leg `b`, mate-closure identifies the final `ab` block with its
representatives on `a`, yielding the second Kirchhoff law. -/
theorem TrivalentMateClosedSelection.legCount_b
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) :
    selection.legCount .b =
      selection.removal.bc + selection.removal.ab := by
  have hb := resolution.b_balance
  unfold TrivalentMateClosedSelection.legCount
    TrivalentMateClosedSelection.removal
    TrivalentMateClosedSelection.bcCount
    legSize
  change boolCountFrom (selection.selected .b) 0 b =
    boolCountFrom (selection.selected .b) 0 resolution.bc +
      selection.abCount
  calc
    boolCountFrom (selection.selected .b) 0 b =
        boolCountFrom (selection.selected .b) 0
          (resolution.bc + resolution.ab) :=
      congrArg (boolCountFrom (selection.selected .b) 0) hb
    _ = boolCountFrom (selection.selected .b) 0 resolution.bc +
          boolCountFrom (selection.selected .b) resolution.bc
            resolution.ab :=
      by
        simpa using
          (boolCountFrom_add (selection.selected .b) 0
            resolution.bc resolution.ab)
    _ = boolCountFrom (selection.selected .b) 0 resolution.bc +
          selection.abCount := by
      rw [selection.abCount_on_b]

/-- The `bc` block has the same count on legs `b` and `c`. -/
theorem TrivalentMateClosedSelection.bcCount_on_c
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) :
    boolCountFrom (selection.selected .c) 0 resolution.bc =
      selection.bcCount := by
  unfold TrivalentMateClosedSelection.bcCount
  apply boolCountFrom_congr
  intro offset hoffset
  let port : TrivalentStrandPort a b c :=
    .onB <| Fin.mk offset (by
      have hb := resolution.b_balance
      omega)
  have hclosed := selection.mate_closed port
  have hlt : offset < resolution.bc := hoffset
  simpa [port, strandMate, hlt,
    TrivalentStrandPort.leg, TrivalentStrandPort.slot] using hclosed

/-- The `ca` block has the same count on its representatives on `a` and the
final `ca` slots on `c`. -/
theorem TrivalentMateClosedSelection.caCount_on_c
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) :
    boolCountFrom (selection.selected .c) resolution.bc resolution.ca =
      selection.caCount := by
  unfold TrivalentMateClosedSelection.caCount
  apply boolCountFrom_congr
  intro offset hoffset
  let port : TrivalentStrandPort a b c :=
    .onA <| Fin.mk offset (by
      have ha := resolution.a_balance
      omega)
  have hclosed := selection.mate_closed port
  have hlt : offset < resolution.ca := hoffset
  simpa [port, strandMate, hlt,
    TrivalentStrandPort.leg, TrivalentStrandPort.slot] using hclosed

/-- On leg `c`, the `bc` and `ca` blocks give the third Kirchhoff law. -/
theorem TrivalentMateClosedSelection.legCount_c
    {a b c : Nat} {resolution : TrivalentStrandResolution a b c}
    (selection : TrivalentMateClosedSelection resolution) :
    selection.legCount .c =
      selection.removal.bc + selection.removal.ca := by
  have hc := resolution.c_balance
  unfold TrivalentMateClosedSelection.legCount
    TrivalentMateClosedSelection.removal
    legSize
  change boolCountFrom (selection.selected .c) 0 c =
    selection.bcCount + selection.caCount
  calc
    boolCountFrom (selection.selected .c) 0 c =
        boolCountFrom (selection.selected .c) 0
          (resolution.bc + resolution.ca) :=
      congrArg (boolCountFrom (selection.selected .c) 0) hc
    _ = boolCountFrom (selection.selected .c) 0 resolution.bc +
          boolCountFrom (selection.selected .c) resolution.bc
            resolution.ca :=
      by
        simpa using
          (boolCountFrom_add (selection.selected .c) 0
            resolution.bc resolution.ca)
    _ = selection.bcCount + selection.caCount := by
      rw [selection.bcCount_on_c, selection.caCount_on_c]

/-! ## 3. Compile conservation over an arbitrary resolved network -/

/-- One Boolean choice on the strand copies of graph edges, with local
mate-closure at every displayed resolved vertex. -/
structure ResolvedNetworkMateClosedSelection
    {label : EdgeLabelling}
    (resolved : List (ResolvedTrivalentVertex label)) : Type where
  selected : Nat -> Nat -> Bool
  mate_closed : forall (vertex : ResolvedTrivalentVertex label),
    vertex ∈ resolved ->
      forall port : TrivalentStrandPort
        (label vertex.vertex.1)
        (label vertex.vertex.2.1)
        (label vertex.vertex.2.2),
        selected
            (vertexEdgeId vertex.vertex (strandMate vertex.strands port).leg)
            (strandMate vertex.strands port).slot =
          selected (vertexEdgeId vertex.vertex port.leg) port.slot

/-- The common graph-edge drop is exactly the number of selected bounded
strand copies carried by that edge. -/
def ResolvedNetworkMateClosedSelection.drop
    {label : EdgeLabelling}
    {resolved : List (ResolvedTrivalentVertex label)}
    (selection : ResolvedNetworkMateClosedSelection resolved) :
    EdgeLabelling :=
  fun edge => boolCountFrom (selection.selected edge) 0 (label edge)

/-- Pull the common edge selection back to one displayed trivalent vertex. -/
def ResolvedNetworkMateClosedSelection.atVertex
    {label : EdgeLabelling}
    {resolved : List (ResolvedTrivalentVertex label)}
    (selection : ResolvedNetworkMateClosedSelection resolved)
    (vertex : ResolvedTrivalentVertex label) (hvertex : vertex ∈ resolved) :
    TrivalentMateClosedSelection vertex.strands where
  selected := fun leg slot =>
    selection.selected (vertexEdgeId vertex.vertex leg) slot
  mate_closed := selection.mate_closed vertex hvertex

/-- Restrict a mate-closed selection to the tail of an ordered resolved
network without changing the selected edge copies. -/
def ResolvedNetworkMateClosedSelection.tail
    {label : EdgeLabelling}
    {head : ResolvedTrivalentVertex label}
    {tail : List (ResolvedTrivalentVertex label)}
    (selection : ResolvedNetworkMateClosedSelection (head :: tail)) :
    ResolvedNetworkMateClosedSelection tail where
  selected := selection.selected
  mate_closed := by
    intro vertex hvertex port
    exact selection.mate_closed vertex (List.mem_cons_of_mem head hvertex) port

/-- **Selection-to-plan compiler.**  Local mate conservation at every vertex
constructs one coherent simultaneous removal plan with a common edge drop.
Target fusion admissibility is therefore an output of the existing removal
theorem, not an assumption hidden in this compiler. -/
def ResolvedNetworkMateClosedSelection.toRemovalPlan
    {label : EdgeLabelling} :
    forall {resolved : List (ResolvedTrivalentVertex label)},
      (selection : ResolvedNetworkMateClosedSelection resolved) ->
        ResolvedTrivalentRemovalPlan label selection.drop resolved
  | [], _ => .nil
  | head :: tail, selection =>
      let localSelection := selection.atVertex head (List.mem_cons_self)
      let tailSelection := selection.tail
      .cons head tail localSelection.removal
        (by
          simpa [ResolvedNetworkMateClosedSelection.drop,
            ResolvedNetworkMateClosedSelection.atVertex,
            TrivalentMateClosedSelection.legCount, legSize, vertexEdgeId]
            using localSelection.legCount_a)
        (by
          simpa [ResolvedNetworkMateClosedSelection.drop,
            ResolvedNetworkMateClosedSelection.atVertex,
            TrivalentMateClosedSelection.legCount, legSize, vertexEdgeId]
            using localSelection.legCount_b)
        (by
          simpa [ResolvedNetworkMateClosedSelection.drop,
            ResolvedNetworkMateClosedSelection.atVertex,
            TrivalentMateClosedSelection.legCount, legSize, vertexEdgeId]
            using localSelection.legCount_c)
        (by
          change ResolvedTrivalentRemovalPlan label selection.drop tail
          exact tailSelection.toRemovalPlan)

/-- Package the compiled plan as a data-bearing coherent removal of a resolved
network. -/
def ResolvedNetworkMateClosedSelection.toCoherentRemoval
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (selection : ResolvedNetworkMateClosedSelection network.resolved) :
    CoherentResolvedTrivalentRemoval network where
  drop := selection.drop
  plan := selection.toRemovalPlan

/-! ## 4. Accepted corrected-slab specialization -/

/-- A mate-closed Boolean strand selection on the resolved network of one
literal accepted corrected-slab link witness. -/
abbrev SlabLinkMateClosedSelection
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link) :=
  ResolvedNetworkMateClosedSelection
    (slabLinkResolvedStrandNetwork
      cutoff extent physical link auxiliary hmem).resolved

/-- The general conservation compiler has exactly the canonical accepted-link
removal-plan type required by fusion preservation. -/
def SlabLinkMateClosedSelection.toStrandRemovalPlan
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkMateClosedSelection hmem) :
    SlabLinkStrandRemovalPlan hmem selection.drop :=
  selection.toRemovalPlan

/-- **Accepted lower witness from conserved selection.**  Once the target
physical external labels realize the selected edge drops, mate conservation
constructs the lower accepted auxiliary witness with no further fusion
hypothesis. -/
theorem SlabLinkMateClosedSelection.lower_auxiliary_mem
    {cutoff extent : Nat}
    {sourcePhysical targetPhysical : SlabLabelling} {link : SlabLink}
    {sourceAuxiliary : SlabLabelling}
    {hmem : sourceAuxiliary ∈
      slabLinkFusionWitnesses cutoff extent sourcePhysical link}
    (selection : SlabLinkMateClosedSelection hmem)
    (hexternal :
      slabLinkExternalSpins extent targetPhysical link =
        lowerEdgeLabellingBy
          (slabLinkExternalSpins extent sourcePhysical link)
          selection.drop) :
    lowerEdgeLabellingBy sourceAuxiliary selection.drop ∈
      slabLinkFusionWitnesses cutoff extent targetPhysical link :=
  slabLinkFusionWitness_lower_mem_of_plan
    hmem hexternal selection.toStrandRemovalPlan

#print axioms boolIndicator
#print axioms boolCountFrom
#print axioms boolCountFrom_add
#print axioms boolCountFrom_le
#print axioms boolCountFrom_congr
#print axioms TrivalentMateClosedSelection
#print axioms TrivalentMateClosedSelection.abCount
#print axioms TrivalentMateClosedSelection.bcCount
#print axioms TrivalentMateClosedSelection.caCount
#print axioms TrivalentMateClosedSelection.legCount
#print axioms TrivalentMateClosedSelection.removal
#print axioms TrivalentMateClosedSelection.legCount_a
#print axioms TrivalentMateClosedSelection.abCount_on_b
#print axioms TrivalentMateClosedSelection.legCount_b
#print axioms TrivalentMateClosedSelection.bcCount_on_c
#print axioms TrivalentMateClosedSelection.caCount_on_c
#print axioms TrivalentMateClosedSelection.legCount_c
#print axioms ResolvedNetworkMateClosedSelection
#print axioms ResolvedNetworkMateClosedSelection.drop
#print axioms ResolvedNetworkMateClosedSelection.atVertex
#print axioms ResolvedNetworkMateClosedSelection.tail
#print axioms ResolvedNetworkMateClosedSelection.toRemovalPlan
#print axioms ResolvedNetworkMateClosedSelection.toCoherentRemoval
#print axioms SlabLinkMateClosedSelection
#print axioms SlabLinkMateClosedSelection.toStrandRemovalPlan
#print axioms SlabLinkMateClosedSelection.lower_auxiliary_mem

end YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
