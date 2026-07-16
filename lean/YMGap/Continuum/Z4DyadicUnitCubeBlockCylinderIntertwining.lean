/-
# Coarse/fine unit-cube cylinder intertwining

The elementary six-face cube and its 24-face dyadic refinement are assembled
as two coordinates of one exact strong-coupling cylinder law.  The first and
second coordinate marginals are proved to recover, respectively, the coarse
cube law (after exact base-box transport) and the previously constructed
dyadic cube law.

This is an observable-level block interface, not yet an RG theorem.  Both
marginals still use the same strong-coupling anchor.  The final definition
exposes their finite-cutoff, finite-volume discrepancy as an exact rational
quantity; the next analytic step is to replace that same-coupling discrepancy
by a summable comparison between genuinely coupling-shifted laws.
-/

import YMGap.Continuum.Z4CoarseUnitCubeActivity
import YMGap.Continuum.Z4DyadicUnitCubeCylinderInterface

namespace YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining

set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeCylinderInterface
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointFunctional

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The coarse singleton cylinder -/

def unitCubeSingleOccurrencePredicate : List Bool → Bool
  | [] => false
  | bit :: _ => bit

def coarseUnitCubeCylinderRoots : List (List Nat) :=
  [coarseUnitCubeSupportIds]

theorem coarseUnitCubeCylinderRoots_allCanonical :
    ∀ root, root ∈ coarseUnitCubeCylinderRoots →
      root ∈ canonicalSurfacePolymers 2 := by
  intro root hroot
  have hrootEq : root = coarseUnitCubeSupportIds :=
    List.mem_singleton.mp hroot
  rw [hrootEq]
  exact coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers

def spinSummedCoarseUnitCubeCylinderLimit
    (predicate : List Bool → Bool) : CReal :=
  spinSummedJointCylinderLimitFunctional
    coarseUnitCubeCylinderRoots_allCanonical predicate

@[simp] theorem spinSummedCoarseUnitCubeCylinderLimit_approx
    (stage : Nat) (predicate : List Bool → Bool) :
    (spinSummedCoarseUnitCubeCylinderLimit predicate).approx stage =
      parametricKCompatibleSupportEventProbability
        (spinSummedJointCutoff stage (2 + stage)) (2 + stage)
        (targetCylinderEvent 2 (2 + stage)
          coarseUnitCubeCylinderRoots predicate) := rfl

def spinSummedCoarseUnitCubeOccurrenceLimit : CReal :=
  spinSummedCoarseUnitCubeCylinderLimit
    unitCubeSingleOccurrencePredicate

theorem coarseUnitCube_targetCylinderEvent_occurrence (n : Nat) :
    targetCylinderEvent 2 n coarseUnitCubeCylinderRoots
        unitCubeSingleOccurrencePredicate =
      familyContainsPolymerB
        (transportPolymer 2 n coarseUnitCubeSupportIds) := by
  rfl

/-! ## 2. A common box-four presentation and the two-coordinate law -/

def coarseUnitCubeCylinderRootsAtFour : List (List Nat) :=
  transportedCylinderRoots 2 4 coarseUnitCubeCylinderRoots

theorem coarseUnitCubeCylinderRootsAtFour_allCanonical :
    ∀ root, root ∈ coarseUnitCubeCylinderRootsAtFour →
      root ∈ canonicalSurfacePolymers 4 :=
  transportedCylinderRoots_canonical (by omega)
    coarseUnitCubeCylinderRoots_allCanonical

def unitCubeBlockCylinderRoots : List (List Nat) :=
  coarseUnitCubeCylinderRootsAtFour ++ dyadicUnitCubeCylinderRoots

theorem unitCubeBlockCylinderRoots_allCanonical :
    ∀ root, root ∈ unitCubeBlockCylinderRoots →
      root ∈ canonicalSurfacePolymers 4 := by
  intro root hroot
  rcases List.mem_append.mp hroot with hcoarse | hrefined
  · exact coarseUnitCubeCylinderRootsAtFour_allCanonical root hcoarse
  · exact dyadicUnitCubeCylinderRoots_allCanonical root hrefined

/-- The predicate on the joint law that ignores the appended refined
coordinate and reads only the coarse occurrence bit. -/
def unitCubeBlockCoarseOccurrencePredicate : List Bool → Bool :=
  extendCylinderPredicate coarseUnitCubeCylinderRootsAtFour.length
    unitCubeSingleOccurrencePredicate

/-- The predicate that reads the second, refined-cube coordinate. -/
def unitCubeBlockRefinedOccurrencePredicate : List Bool → Bool
  | _ :: refined :: _ => refined
  | _ => false

def spinSummedUnitCubeBlockCylinderLimit
    (predicate : List Bool → Bool) : CReal :=
  spinSummedJointCylinderLimitFunctional
    unitCubeBlockCylinderRoots_allCanonical predicate

@[simp] theorem spinSummedUnitCubeBlockCylinderLimit_approx
    (stage : Nat) (predicate : List Bool → Bool) :
    (spinSummedUnitCubeBlockCylinderLimit predicate).approx stage =
      parametricKCompatibleSupportEventProbability
        (spinSummedJointCutoff stage (4 + stage)) (4 + stage)
        (targetCylinderEvent 4 (4 + stage)
          unitCubeBlockCylinderRoots predicate) := rfl

/-! ## 3. Exact marginal intertwining -/

theorem unitCubeBlock_targetCoarse_eq_singleton (n : Nat) :
    targetCylinderEvent 4 n unitCubeBlockCylinderRoots
        unitCubeBlockCoarseOccurrencePredicate =
      targetCylinderEvent 4 n coarseUnitCubeCylinderRootsAtFour
        unitCubeSingleOccurrencePredicate := by
  unfold unitCubeBlockCylinderRoots
    unitCubeBlockCoarseOccurrencePredicate
  exact targetCylinderEvent_append_extend 4 n
    coarseUnitCubeCylinderRootsAtFour dyadicUnitCubeCylinderRoots
    unitCubeSingleOccurrencePredicate

theorem unitCubeBlock_targetRefined_eq_singleton (n : Nat) :
    targetCylinderEvent 4 n unitCubeBlockCylinderRoots
        unitCubeBlockRefinedOccurrencePredicate =
      targetCylinderEvent 4 n dyadicUnitCubeCylinderRoots
        unitCubeSingleOccurrencePredicate := by
  funext family
  rfl

private theorem equiv_ofQ'_of_eqv_local {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hepsilon))

private theorem creal_equiv_of_approx_eqv_local {A B : CReal}
    (h : ∀ stage, A.approx stage ≈ B.approx stage) :
    CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal
    (fun stage => equiv_ofQ'_of_eqv_local (h stage))

/-- Reading the first bit of the joint law is exactly the coarse singleton
law, including the change from its box-four presentation back to box two. -/
theorem spinSummedUnitCubeBlock_coarseMarginal :
    CReal.Equiv
      (spinSummedUnitCubeBlockCylinderLimit
        unitCubeBlockCoarseOccurrencePredicate)
      spinSummedCoarseUnitCubeOccurrenceLimit := by
  have hrefinement :=
    spinSummedJointCylinderLimitFunctional_refinement
      coarseUnitCubeCylinderRootsAtFour_allCanonical
      dyadicUnitCubeCylinderRoots_allCanonical
      unitCubeSingleOccurrencePredicate
  have htransport :=
    spinSummedJointCylinderLimitFunctional_base_transport
      (base := 2) (outerBase := 4) (by omega)
      coarseUnitCubeCylinderRoots_allCanonical
      unitCubeSingleOccurrencePredicate
  exact CReal.Equiv.trans
    (by
      simpa [spinSummedUnitCubeBlockCylinderLimit,
        unitCubeBlockCylinderRoots,
        unitCubeBlockCoarseOccurrencePredicate] using hrefinement)
    (by
      simpa [spinSummedCoarseUnitCubeOccurrenceLimit,
        spinSummedCoarseUnitCubeCylinderLimit,
        coarseUnitCubeCylinderRootsAtFour] using htransport)

/-- Reading the second bit of the joint law is exactly the established
dyadic singleton law. -/
theorem spinSummedUnitCubeBlock_refinedMarginal :
    CReal.Equiv
      (spinSummedUnitCubeBlockCylinderLimit
        unitCubeBlockRefinedOccurrencePredicate)
      (spinSummedDyadicUnitCubeCylinderLimit
        unitCubeSingleOccurrencePredicate) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  rw [spinSummedUnitCubeBlockCylinderLimit_approx,
    spinSummedDyadicUnitCubeCylinderLimit_approx,
    unitCubeBlock_targetRefined_eq_singleton]
  exact Q'.eqv_refl _

/-! ## 4. The exact same-coupling defect exposed to the next RG estimate -/

/-- Exact finite-cutoff, finite-volume discrepancy between the two block
coordinates in their common anchor-coupling law. -/
def anchorSameCouplingUnitCubeBlockDefect
    (cutoff volume : Nat) : Q' :=
  Q'.abs
    (parametricKCompatibleSupportEventProbability cutoff volume
        (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
          unitCubeBlockCoarseOccurrencePredicate) +
      (-parametricKCompatibleSupportEventProbability cutoff volume
        (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
          unitCubeBlockRefinedOccurrencePredicate)))

theorem anchorSameCouplingUnitCubeBlockDefect_nonnegative
    (cutoff volume : Nat) :
    (0 : Q') ≤
      anchorSameCouplingUnitCubeBlockDefect cutoff volume :=
  Q'.abs_nonneg _

#print axioms coarseUnitCubeCylinderRoots_allCanonical
#print axioms unitCubeBlockCylinderRoots_allCanonical
#print axioms unitCubeBlock_targetCoarse_eq_singleton
#print axioms unitCubeBlock_targetRefined_eq_singleton
#print axioms spinSummedUnitCubeBlock_coarseMarginal
#print axioms spinSummedUnitCubeBlock_refinedMarginal
#print axioms anchorSameCouplingUnitCubeBlockDefect_nonnegative

end YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
