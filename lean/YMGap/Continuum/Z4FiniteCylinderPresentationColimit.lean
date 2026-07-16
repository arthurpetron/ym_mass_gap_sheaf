/-
# A quotient-free colimit of finite Z4 cylinder presentations

A local Boolean cylinder event is presented by a finite canonical box, a list
of marked canonical polymers, and a Boolean predicate on their occurrence
fingerprint.  Refinement means moving to a larger base presentation without
changing the transported event in any still larger box.  Two presentations
are equivalent when they possess an explicit common refinement.

The interface is deliberately quotient-free: a refinement/equivalence carries
its computable witness, while later state values are required to respect it up
to constructive-real equivalence.  This packages only the finite-cylinder
colimit; it does not assert countable additivity or OS reconstruction.
-/

import YMGap.Continuum.Z4CanonicalCylinderFunctional

namespace YMGap.Continuum.Z4FiniteCylinderPresentationColimit

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalPolymerUniverse

/-- A finite Boolean cylinder chart: a canonical box and a finite ordered list
of canonical polymer coordinates in that box. -/
structure FiniteCylinderChart where
  base : Nat
  roots : List (List Nat)
  rootsCanonical : ∀ root, root ∈ roots →
    root ∈ canonicalSurfacePolymers base

/-- A Boolean event in one finite cylinder chart. -/
structure FiniteCylinderPresentation where
  chart : FiniteCylinderChart
  predicate : List Bool → Bool

def FiniteCylinderChart.present (chart : FiniteCylinderChart)
    (predicate : List Bool → Bool) : FiniteCylinderPresentation :=
  ⟨chart, predicate⟩

/-- Transport a whole chart into a larger canonical base box. -/
def FiniteCylinderChart.transport (chart : FiniteCylinderChart)
    (outerBase : Nat) (hbase : chart.base ≤ outerBase) :
    FiniteCylinderChart where
  base := outerBase
  roots := transportedCylinderRoots chart.base outerBase chart.roots
  rootsCanonical := transportedCylinderRoots_canonical
    hbase chart.rootsCanonical

/-- Transport a presentation, retaining its Boolean predicate. -/
def FiniteCylinderPresentation.transport
    (presentation : FiniteCylinderPresentation)
    (outerBase : Nat) (hbase : presentation.chart.base ≤ outerBase) :
    FiniteCylinderPresentation :=
  (presentation.chart.transport outerBase hbase).present
    presentation.predicate

/-- Append finitely many coordinates and make the event ignore them. -/
def FiniteCylinderPresentation.appendIgnored
    (presentation : FiniteCylinderPresentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers presentation.chart.base) :
    FiniteCylinderPresentation :=
  {
    chart := {
      base := presentation.chart.base
      roots := presentation.chart.roots ++ extra
      rootsCanonical := fun root hroot => by
        rcases List.mem_append.mp hroot with hleft | hright
        · exact presentation.chart.rootsCanonical root hleft
        · exact hextra root hright
    }
    predicate := extendCylinderPredicate
      presentation.chart.roots.length presentation.predicate
  }

/-- `source ≼ target` means that `target` is a larger finite presentation of
the same local event.  The event equality is required in every common outer
box, so the witness composes without any choice principle. -/
structure CylinderPresentationRefines
    (source target : FiniteCylinderPresentation) : Prop where
  base_le : source.chart.base ≤ target.chart.base
  event_eq : ∀ outer, target.chart.base ≤ outer →
    targetCylinderEvent target.chart.base outer
        target.chart.roots target.predicate =
      targetCylinderEvent source.chart.base outer
        source.chart.roots source.predicate

theorem CylinderPresentationRefines.refl
    (presentation : FiniteCylinderPresentation) :
    CylinderPresentationRefines presentation presentation :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem CylinderPresentationRefines.trans
    {first middle last : FiniteCylinderPresentation}
    (hfirst : CylinderPresentationRefines first middle)
    (hlast : CylinderPresentationRefines middle last) :
    CylinderPresentationRefines first last := by
  refine ⟨Nat.le_trans hfirst.base_le hlast.base_le, ?_⟩
  intro outer houter
  exact Eq.trans (hlast.event_eq outer houter)
    (hfirst.event_eq outer (Nat.le_trans hlast.base_le houter))

/-- Literal base transport is a refinement. -/
theorem FiniteCylinderPresentation.refines_transport
    (presentation : FiniteCylinderPresentation)
    (outerBase : Nat) (hbase : presentation.chart.base ≤ outerBase) :
    CylinderPresentationRefines presentation
      (presentation.transport outerBase hbase) := by
  refine ⟨hbase, ?_⟩
  intro outer houter
  exact targetCylinderEvent_trans hbase houter
    presentation.chart.rootsCanonical presentation.predicate

/-- Appending ignored coordinates is a refinement. -/
theorem FiniteCylinderPresentation.refines_appendIgnored
    (presentation : FiniteCylinderPresentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers presentation.chart.base) :
    CylinderPresentationRefines presentation
      (presentation.appendIgnored extra hextra) := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro outer _
  exact targetCylinderEvent_append_extend
    presentation.chart.base outer presentation.chart.roots extra
      presentation.predicate

/-- Quotient-free colimit equivalence: an explicitly witnessed finite
presentation refines both events. -/
def CylinderPresentationEquivalent
    (left right : FiniteCylinderPresentation) : Prop :=
  ∃ common : FiniteCylinderPresentation,
    CylinderPresentationRefines left common ∧
      CylinderPresentationRefines right common

theorem CylinderPresentationEquivalent.refl
    (presentation : FiniteCylinderPresentation) :
    CylinderPresentationEquivalent presentation presentation :=
  ⟨presentation, CylinderPresentationRefines.refl presentation,
    CylinderPresentationRefines.refl presentation⟩

theorem CylinderPresentationEquivalent.symm
    {left right : FiniteCylinderPresentation}
    (h : CylinderPresentationEquivalent left right) :
    CylinderPresentationEquivalent right left := by
  rcases h with ⟨common, hleft, hright⟩
  exact ⟨common, hright, hleft⟩

/-- Common-refinement equivalence is transitive.  The construction transports
the first common refinement to the maximum of the two common base boxes and
uses the shared middle event to attach the second one. -/
theorem CylinderPresentationEquivalent.trans
    {first middle last : FiniteCylinderPresentation}
    (hfirst : CylinderPresentationEquivalent first middle)
    (hlast : CylinderPresentationEquivalent middle last) :
    CylinderPresentationEquivalent first last := by
  rcases hfirst with ⟨firstCommon, hfirstLeft, hfirstRight⟩
  rcases hlast with ⟨lastCommon, hlastLeft, hlastRight⟩
  let outerBase := max firstCommon.chart.base lastCommon.chart.base
  have hfirstBase : firstCommon.chart.base ≤ outerBase :=
    Nat.le_max_left _ _
  have hlastBase : lastCommon.chart.base ≤ outerBase :=
    Nat.le_max_right _ _
  let common := firstCommon.transport outerBase hfirstBase
  have hfirstCommon :
      CylinderPresentationRefines firstCommon common :=
    firstCommon.refines_transport outerBase hfirstBase
  have hlastCommon :
      CylinderPresentationRefines lastCommon common := by
    refine ⟨hlastBase, ?_⟩
    intro outer houter
    exact Eq.trans (hfirstCommon.event_eq outer houter)
      (Eq.trans
        (hfirstRight.event_eq outer
          (Nat.le_trans hfirstBase houter))
        (Eq.symm
          (hlastLeft.event_eq outer
            (Nat.le_trans hlastBase houter))))
  exact
    ⟨common,
      hfirstLeft.trans hfirstCommon,
      hlastRight.trans hlastCommon⟩

theorem cylinderPresentationEquivalent_equivalence :
    Equivalence CylinderPresentationEquivalent :=
  ⟨CylinderPresentationEquivalent.refl,
    @CylinderPresentationEquivalent.symm,
    @CylinderPresentationEquivalent.trans⟩

/-- Every base transport is equivalent to its source presentation. -/
theorem FiniteCylinderPresentation.equivalent_transport
    (presentation : FiniteCylinderPresentation)
    (outerBase : Nat) (hbase : presentation.chart.base ≤ outerBase) :
    CylinderPresentationEquivalent
      (presentation.transport outerBase hbase) presentation :=
  ⟨presentation.transport outerBase hbase,
    CylinderPresentationRefines.refl _,
    presentation.refines_transport outerBase hbase⟩

/-- Every ignored-coordinate extension is equivalent to its source. -/
theorem FiniteCylinderPresentation.equivalent_appendIgnored
    (presentation : FiniteCylinderPresentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers presentation.chart.base) :
    CylinderPresentationEquivalent
      (presentation.appendIgnored extra hextra) presentation :=
  ⟨presentation.appendIgnored extra hextra,
    CylinderPresentationRefines.refl _,
    presentation.refines_appendIgnored extra hextra⟩

#print axioms CylinderPresentationRefines.trans
#print axioms FiniteCylinderPresentation.refines_transport
#print axioms FiniteCylinderPresentation.refines_appendIgnored
#print axioms CylinderPresentationEquivalent.trans
#print axioms cylinderPresentationEquivalent_equivalence

end YMGap.Continuum.Z4FiniteCylinderPresentationColimit
