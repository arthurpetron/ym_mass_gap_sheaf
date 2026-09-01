/-
# Local-constraint BF4 vacuum-root spoke classifier

The positive lower-link product classifier can be decomposed into its exact
local constraints: a finite natural-number product is positive exactly when
every factor is positive.  This module packages those linkwise production
fusion constraints as one executable `List.all` decision.

At strictly positive coupling, the routing-level vacuum-root predecessor
carrier is therefore exactly the finite-sector filter by this all-link local
admissibility test.  The remaining carrier-growth problem is a finite CSP over
the explicit incident-spin multiplicities, rather than an opaque kernel or
amplitude calculation.

No cardinality bound, routing, gap, continuum limit, or Clay conclusion is
asserted.  No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier

namespace YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

private theorem natListProduct_pos_iff_pointwise
    {Item : Type} (value : Item → Nat) :
    ∀ items : List Item,
      0 < natListProduct value items ↔
        ∀ item, item ∈ items → 0 < value item
  | [] => by
      constructor
      · intro _ item hitem
        exact False.elim (List.not_mem_nil hitem)
      · intro _
        change 0 < 1
        omega
  | head :: tail => by
      constructor
      · intro hproduct item hitem
        rw [natListProduct] at hproduct
        rcases List.mem_cons.mp hitem with heq | htail
        · subst item
          exact Nat.pos_of_mul_pos_right hproduct
        · exact (natListProduct_pos_iff_pointwise value tail).mp
            (Nat.pos_of_mul_pos_left hproduct) item htail
      · intro hpointwise
        rw [natListProduct]
        exact Nat.mul_pos
          (hpointwise head List.mem_cons_self)
          ((natListProduct_pos_iff_pointwise value tail).mpr
            (fun item hitem =>
              hpointwise item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Exact linkwise admissibility test -/

/-- Every literal lower link has positive production fusion multiplicity
against the all-vacuum fixed and upper coordinates. -/
def centralVacuumLowerLinksAdmissibleB
    (K : Nat) (source : EdgeLabelling) : Bool :=
  (centralLowerLinks 0).all fun link => decide
    (0 < slabExplicitLinkMultiplicity K (centralExtent 0)
      (centralVacuumLowerPhysical source) link)

theorem centralVacuumLowerLinksAdmissibleB_true_iff
    (K : Nat) (source : EdgeLabelling) :
    centralVacuumLowerLinksAdmissibleB K source = true ↔
      ∀ link, link ∈ centralLowerLinks 0 →
        0 < slabExplicitLinkMultiplicity K (centralExtent 0)
          (centralVacuumLowerPhysical source) link := by
  constructor
  · intro hall link hlink
    exact of_decide_eq_true
      (List.all_eq_true.mp hall link hlink)
  · intro hpointwise
    apply List.all_eq_true.mpr
    intro link hlink
    exact decide_eq_true (hpointwise link hlink)

theorem centralVacuumLowerLinkMultiplicityProduct_pos_iff_admissibleB
    (K : Nat) (source : EdgeLabelling) :
    0 < centralVacuumLowerLinkMultiplicityProduct K source ↔
      centralVacuumLowerLinksAdmissibleB K source = true := by
  unfold centralVacuumLowerLinkMultiplicityProduct
  exact Iff.trans
    (natListProduct_pos_iff_pointwise
      (slabExplicitLinkMultiplicity K (centralExtent 0)
        (centralVacuumLowerPhysical source))
      (centralLowerLinks 0))
    (Iff.symm
      (centralVacuumLowerLinksAdmissibleB_true_iff K source))

/-! ## 2. Exact finite-sector local-constraint filter -/

def centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
    (w : YMGap.Constructive.Q')
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun source => centralVacuumLowerLinksAdmissibleB K
      (centralPhysicalFiniteStateAt w hw K 0 source))

theorem mem_locallyAdmissibleRootIndices_iff
    {w : YMGap.Constructive.Q'}
    {hw : (0 : YMGap.Constructive.Q') ≤ w}
    {K source : Nat} :
    source ∈
        centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
          w hw K ↔
      source ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
        centralVacuumLowerLinksAdmissibleB K
          (centralPhysicalFiniteStateAt w hw K 0 source) = true := by
  unfold centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
  simp only [List.mem_filter]

theorem centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices_eq_localConstraints
    (w : YMGap.Constructive.Q')
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (K : Nat) :
    centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices w hw K =
      centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
        w hw K := by
  unfold centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices
    centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
  apply List.filter_congr
  intro source _hsource
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact centralVacuumLowerLinkMultiplicityProduct_pos_iff_admissibleB
    K (centralPhysicalFiniteStateAt w hw K 0 source)

theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_localConstraints
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (hwpos : (0 : YMGap.Constructive.Q') < w)
    (K : Nat) :
    centralPhysicalFiniteVacuumSectorPositiveRootPredecessors w hw K =
      centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
        w hw K :=
  Eq.trans
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_lowerLinkIndices
      hw hwpos K)
    (centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices_eq_localConstraints
      w hw K)

theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_localConstraintCount
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') ≤ w)
    (hwpos : (0 : YMGap.Constructive.Q') < w)
    (K : Nat) :
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
        w hw K).length =
      (centralPhysicalFiniteVacuumSectorLocallyAdmissibleRootIndices
        w hw K).length :=
  congrArg List.length
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_localConstraints
      hw hwpos K)

end YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier.centralVacuumLowerLinksAdmissibleB_true_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier.centralVacuumLowerLinkMultiplicityProduct_pos_iff_admissibleB
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier.mem_locallyAdmissibleRootIndices_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier.centralPhysicalFiniteVacuumSectorPositiveLowerLinkIndices_eq_localConstraints
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_localConstraints
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_localConstraintCount
