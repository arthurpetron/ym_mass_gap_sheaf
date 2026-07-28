/-
# Fine-witness routing reduction for the SU(2) outer carrier

The positive fine corrected-slab term already has a finite list of explicit
link-intertwiner assignments.  The older extraction theorem states its
nonemptiness in `Prop`.  That statement cannot supply data to the
`Type`-valued outer positive-row constructor, so this module first exposes a
literal member of the list as a dependent pair.

The remaining geometric theorem is then named exactly.  A
`WholeSlabFineWitnessRouter` must send every retained fine intertwiner
assignment to a member of the explicit finite joint coarse carrier.  A
family of such routers on all positive higher-cutoff rows constructs
`SU2OuterJointCarrierNonempty`, hence the physical positive-row closure.

No router is constructed here.  The reverse reduction sends an already
nonempty joint carrier to a constant router, showing that this interface is
equivalent to carrier nonemptiness on the relevant positive rows.  Thus the
module repairs the Prop-to-Type extraction boundary and identifies the exact
strand-routing support lift; it does not prove that lift.

## Axiom gate

Finite list recursion and exact `Q'` order only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration

namespace YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction

set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Type-level extraction of one fine intertwiner field -/

/-- A positive corrected-slab term constructively returns one member of its
literal finite fine-intertwiner list.  This is the `Type`-level replacement
needed by later routing code; no `Exists` elimination is used. -/
def positivePhysicalTermFineFusionWitness
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (hpositive : (0 : Q') < D.physicalTerm physical) :
    Σ' witness : SlabFusionWitnessAssignment,
      witness ∈ slabFineFusionWitnesses D physical := by
  have hlength :
      (slabFineFusionWitnesses D physical).length ≠ 0 := by
    rw [slabFineFusionWitnesses_length]
    exact fineLinkProduct_ne_zero_of_physicalTerm_pos
      D physical hpositive
  cases hwitnesses : slabFineFusionWitnesses D physical with
  | nil =>
      exact False.elim (hlength (by simp [hwitnesses]))
  | cons witness rest =>
      refine ⟨witness, ?_⟩
      exact List.mem_cons_self

/-! ## 2. The exact unresolved strand router -/

/-- **OPEN STRAND-ROUTING INPUT.** Route every explicit fine link-intertwiner
assignment to an actually enumerated joint coarse target/channel/intertwiner
code.

The output membership is checked against `wholeSlabJointCarrierCodes`, so an
inhabitant cannot insert an opaque coarse target or a Dirac-completed row.
Constructing this function is precisely the global support-lift theorem. -/
structure WholeSlabFineWitnessRouter
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  route :
    ∀ fineWitness : SlabFusionWitnessAssignment,
      fineWitness ∈ slabFineFusionWitnesses S.fine fineState →
        WholeSlabEnumeratedJointCarrier S fineState

namespace WholeSlabFineWitnessRouter

/-- A positive fine term supplies the fine witness consumed by the router. -/
def routePositive
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (router : WholeSlabFineWitnessRouter S fineState)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    WholeSlabEnumeratedJointCarrier S fineState :=
  let fineWitness :=
    positivePhysicalTermFineFusionWitness
      S.fine fineState hpositive
  router.route fineWitness.1 fineWitness.2

/-- Routing one extracted fine witness proves literal finite-carrier
nonemptiness. -/
def toCarrierNonempty
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (router : WholeSlabFineWitnessRouter S fineState)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    WholeSlabJointCarrierNonempty S fineState :=
  (router.routePositive hpositive).toNonempty

end WholeSlabFineWitnessRouter

/-- Carrier nonemptiness gives a constant router.  This converse records
honestly that the router interface is a structured presentation of the same
nonemptiness obstruction, not a proof of it. -/
def fineWitnessRouterOfCarrierNonempty
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (nonempty : WholeSlabJointCarrierNonempty S fineState) :
    WholeSlabFineWitnessRouter S fineState where
  route := fun _ _ => nonempty.toEnumeratedCarrier

/-! ## 3. All-row routing and the physical closure -/

/-- **OPEN ALL-ROW ROUTING INPUT.** On every positive row away from the
already-closed cutoff-one anchor, construct the exact fine-witness router.
The positivity argument is retained because it is what makes the finite fine
witness list inhabited. -/
structure SU2OuterFineWitnessRouting
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  router :
    ∀ K source,
      K ≠ 1 →
      source ∈
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalTerm source →
        WholeSlabFineWitnessRouter
          (su2OuterScalePair
            G g hg candidate hcandidate K) source

/-- The family router constructs the finite nonemptiness certificate by
routing the Sigma-extracted fine witness on each positive row. -/
def SU2OuterFineWitnessRouting.toJointCarrierNonempty
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (routing :
      SU2OuterFineWitnessRouting
        G g hg candidate hcandidate) :
    SU2OuterJointCarrierNonempty
      G g hg candidate hcandidate where
  nonempty := by
    intro K source hK hsource hpositive
    exact
      (routing.router
        K source hK hsource hpositive).toCarrierNonempty hpositive

/-- The exact strand router therefore yields the previously isolated joint
channel selection. -/
def SU2OuterFineWitnessRouting.toJointChannelSelection
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (routing :
      SU2OuterFineWitnessRouting
        G g hg candidate hcandidate) :
    SU2OuterJointChannelSelection
      G g hg candidate hcandidate :=
  routing.toJointCarrierNonempty.toJointChannelSelection

/-- The exact strand router yields the physical positive-row closure, with
all later normalization and cutoff-coherence machinery remaining derived. -/
def SU2OuterFineWitnessRouting.toPositiveRowClosure
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (routing :
      SU2OuterFineWitnessRouting
        G g hg candidate hcandidate) :
    SU2OuterPositiveRowClosure
      G g hg candidate hcandidate :=
  routing.toJointCarrierNonempty.toPositiveRowClosure

/-- Conversely, a finite-carrier nonemptiness family supplies a constant
fine-witness router on every relevant positive row. -/
def fineWitnessRoutingOfJointCarrierNonempty
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (nonempty :
      SU2OuterJointCarrierNonempty
        G g hg candidate hcandidate) :
    SU2OuterFineWitnessRouting
      G g hg candidate hcandidate where
  router := by
    intro K source hK hsource hpositive
    exact
      fineWitnessRouterOfCarrierNonempty
        (nonempty.nonempty
          K source hK hsource hpositive)

#print axioms positivePhysicalTermFineFusionWitness
#print axioms WholeSlabFineWitnessRouter
#print axioms WholeSlabFineWitnessRouter.routePositive
#print axioms WholeSlabFineWitnessRouter.toCarrierNonempty
#print axioms fineWitnessRouterOfCarrierNonempty
#print axioms SU2OuterFineWitnessRouting
#print axioms SU2OuterFineWitnessRouting.toJointCarrierNonempty
#print axioms SU2OuterFineWitnessRouting.toJointChannelSelection
#print axioms SU2OuterFineWitnessRouting.toPositiveRowClosure
#print axioms fineWitnessRoutingOfJointCarrierNonempty

end YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
