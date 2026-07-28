/-
# Canonical BF4 tree-gauge class-coordinate carrier

The BF4 retained kinetic carrier is the connected side-two cube boundary.
Its literal link list has 48 entries.  This file fixes an explicit 25-link
spanning tree and the complementary 23 chord links, rather than retaining
the number `23` only as a comment.

The five temporal directions are then the chord indices `0,4,5,6,10`.
On both the 23-cycle carrier and its five-coordinate projection we use
rational unit quaternions.  The source/target heat coordinate is their
four-coordinate dot product, i.e. the scalar part of `g h⁻¹`.

Finite Cauchy--Schwarz proves the genuine class-coordinate bounds

    -1 <= x(g,h) <= 1.

Finally, the complete source/target/path/factor tuple is exposed as the
`Local` type consumed by `FinitePhysicalLocationCarrier`; no naked rational
coordinate is substituted for a physical location.

## Axiom gate

Explicit finite geometry, finite rational sums, and rational
Cauchy--Schwarz only.  No `Classical.*`, `sorry`, `native_decide`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
import YMGap.Continuum.ThetaExponentConvexity
import YMGap.Continuum.Z4HalfTimeReflectionGeometry

namespace YMGap.Continuum.BF4CanonicalClassCoordinateCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow
open YMGap.Continuum.BF4RetainedPathConditionalOrder
open YMGap.Continuum.BF4RetainedKineticWindow
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.ThetaExponentConvexity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal 48 = 25 + 23 BF4 boundary split -/

/-- Select the lower spatial faces of the one-slab BF4 geometry. -/
def bf4SourceSpatialPlaquetteB : Z4Plaq → Bool
  | ((_, _, _, time), .p01)
  | ((_, _, _, time), .p02)
  | ((_, _, _, time), .p12) => decide (time = 0)
  | _ => false

/-- The actual 24 lower spatial faces in the boundary-complete extent-one
slab, rather than the different refined-cube-surface support. -/
def bf4SourceSpatialFaces : List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes 1).filter
    bf4SourceSpatialPlaquetteB

/-- The actual duplicate-free 48-link lower spatial boundary graph. -/
def bf4SourceSpatialBoundaryLinks : List Z4Link :=
  (bf4SourceSpatialFaces.flatMap edgesOf).eraseDups

theorem bf4SourceSpatialFaces_length :
    bf4SourceSpatialFaces.length = 24 := by
  decide

theorem bf4SourceSpatialBoundaryLinks_length :
    bf4SourceSpatialBoundaryLinks.length = 48 := by
  decide

/-- A deterministic 25-link spanning tree of the side-two cube boundary.
The order is the breadth-first order rooted at `(0,0,0,0)`. -/
def bf4SpatialTreeLinks : List Z4Link :=
  [((0, 0, 0, 0), .x2),
   ((0, 0, 0, 0), .x1),
   ((0, 0, 0, 0), .x0),
   ((0, 0, 1, 0), .x2),
   ((0, 0, 1, 0), .x1),
   ((0, 0, 1, 0), .x0),
   ((0, 1, 0, 0), .x1),
   ((0, 1, 0, 0), .x0),
   ((1, 0, 0, 0), .x0),
   ((0, 0, 2, 0), .x1),
   ((0, 0, 2, 0), .x0),
   ((0, 1, 1, 0), .x1),
   ((0, 1, 1, 0), .x0),
   ((1, 0, 1, 0), .x0),
   ((0, 2, 0, 0), .x0),
   ((1, 1, 0, 0), .x0),
   ((0, 1, 2, 0), .x1),
   ((0, 1, 2, 0), .x0),
   ((1, 0, 2, 0), .x0),
   ((0, 2, 1, 0), .x0),
   ((1, 1, 1, 0), .x0),
   ((1, 2, 0, 0), .x0),
   ((1, 1, 2, 0), .x1),
   ((1, 1, 2, 0), .x0),
   ((1, 2, 1, 0), .x0)]

/-- The complementary 23 chord links.  These are the literal BF4
tree-gauge spatial coordinates. -/
def bf4SpatialChordLinks : List Z4Link :=
  [((0, 1, 0, 0), .x2),
   ((0, 1, 1, 0), .x2),
   ((0, 2, 0, 0), .x2),
   ((0, 2, 1, 0), .x2),
   ((1, 0, 0, 0), .x1),
   ((1, 0, 0, 0), .x2),
   ((1, 0, 1, 0), .x1),
   ((1, 0, 1, 0), .x2),
   ((1, 0, 2, 0), .x1),
   ((1, 1, 0, 0), .x1),
   ((1, 1, 0, 0), .x2),
   ((1, 1, 1, 0), .x1),
   ((1, 1, 1, 0), .x2),
   ((1, 2, 0, 0), .x2),
   ((1, 2, 1, 0), .x2),
   ((2, 0, 0, 0), .x1),
   ((2, 0, 0, 0), .x2),
   ((2, 0, 1, 0), .x1),
   ((2, 0, 1, 0), .x2),
   ((2, 1, 0, 0), .x1),
   ((2, 1, 0, 0), .x2),
   ((2, 1, 1, 0), .x1),
   ((2, 1, 1, 0), .x2)]

theorem bf4SpatialTreeLinks_length :
    bf4SpatialTreeLinks.length = 25 := rfl

theorem bf4SpatialChordLinks_length :
    bf4SpatialChordLinks.length = bf4SpatialCycleCount := rfl

theorem bf4SpatialTreeLinks_nodup :
    bf4SpatialTreeLinks.Nodup := by
  decide

theorem bf4SpatialChordLinks_nodup :
    bf4SpatialChordLinks.Nodup := by
  decide

/-- A constructive reflection bridge from a closed Boolean membership
scan to propositional list inclusion.  This avoids using `List.Perm`,
whose general decidable equality proof in the library imports choice. -/
private theorem subset_of_all_mem_true
    {α : Type} [DecidableEq α]
    (left right : List α)
    (scan :
      left.all (fun entry => decide (entry ∈ right)) = true) :
    left.Subset right := by
  intro entry hentry
  exact of_decide_eq_true
    (List.all_eq_true.mp scan entry hentry)

/-- Every displayed tree or chord edge is an edge of the physical lower
spatial boundary graph. -/
theorem bf4SpatialTreeChord_subset_boundary :
    (bf4SpatialTreeLinks ++ bf4SpatialChordLinks).Subset
      bf4SourceSpatialBoundaryLinks := by
  apply subset_of_all_mem_true
  decide

/-- Conversely, every physical lower spatial edge occurs in the displayed
tree/chord split. -/
theorem bf4SpatialBoundary_subset_treeChord :
    bf4SourceSpatialBoundaryLinks.Subset
      (bf4SpatialTreeLinks ++ bf4SpatialChordLinks) := by
  apply subset_of_all_mem_true
  decide

/-- A tree-gauge BF4 spatial cycle is an index into the literal 23-link
chord list. -/
abbrev BF4SpatialCycle := Fin bf4SpatialCycleCount

/-- The actual geometric chord represented by a tree-gauge coordinate. -/
def bf4SpatialChord (cycle : BF4SpatialCycle) : Z4Link :=
  bf4SpatialChordLinks.get
    ⟨cycle.val, by
      rw [bf4SpatialChordLinks_length]
      exact cycle.isLt⟩

/-! ## 2. The five transmitted temporal chord coordinates -/

def bf4TransmittedCycleTable : List BF4SpatialCycle :=
  [⟨0, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩,
   ⟨6, by decide⟩, ⟨10, by decide⟩]

theorem bf4TransmittedCycleTable_length :
    bf4TransmittedCycleTable.length = 5 := rfl

theorem bf4TransmittedCycleTable_nodup :
    bf4TransmittedCycleTable.Nodup := by
  decide

abbrev BF4TemporalHolonomy := Fin 5

/-- The exact inclusion `{0,4,5,6,10} -> Fin 23`. -/
def transmittedSpatialCycle
    (coordinate : BF4TemporalHolonomy) : BF4SpatialCycle :=
  bf4TransmittedCycleTable.get
    ⟨coordinate.val, by
      rw [bf4TransmittedCycleTable_length]
      exact coordinate.isLt⟩

/-! ## 3. Rational unit-quaternion point carrier -/

/-- A rational four-coordinate quaternion, totalized on `Nat` so it can be
fed directly to the constructive finite-sum library. -/
structure RationalQuaternion : Type where
  coordinate : Fin 4 → Q'

namespace RationalQuaternion

def coordinateNat (q : RationalQuaternion) (index : Nat) : Q' :=
  if h : index < 4 then q.coordinate ⟨index, h⟩ else 0

def normSq (q : RationalQuaternion) : Q' :=
  fsum (fun index =>
    q.coordinateNat index * q.coordinateNat index) 4

def dot (left right : RationalQuaternion) : Q' :=
  fsum (fun index =>
    left.coordinateNat index * right.coordinateNat index) 4

end RationalQuaternion

/-- The rational points of the unit three-sphere, retained with their exact
unit-norm certificate. -/
structure RationalUnitQuaternion : Type where
  quaternion : RationalQuaternion
  unit_norm : quaternion.normSq ≈ 1

/-- The exact rational identity point of `SU(2) = S³`. -/
def rationalUnitQuaternionOne : RationalUnitQuaternion where
  quaternion :=
    { coordinate := fun index =>
        if index.val = 0 then 1 else 0 }
  unit_norm := by
    decide

/-- Relative SU(2) class coordinate, i.e. the scalar part of `g h⁻¹`. -/
def relativeClassCoordinate
    (left right : RationalUnitQuaternion) : Q' :=
  left.quaternion.dot right.quaternion

theorem relativeClassCoordinate_sq_le_one
    (left right : RationalUnitQuaternion) :
    relativeClassCoordinate left right *
        relativeClassCoordinate left right ≤
      (1 : Q') * 1 := by
  have hcs :=
    cauchy_schwarz
      left.quaternion.coordinateNat
      right.quaternion.coordinateNat 4
  have hnorm :
      left.quaternion.normSq * right.quaternion.normSq ≈
        (1 : Q') * 1 :=
    Q'.eqv_trans _
      ((1 : Q') * right.quaternion.normSq) _
      (Q'.mul_eqv_congr_right _ _ _
        left.unit_norm)
      (Q'.mul_eqv_congr_left _ _ _
        right.unit_norm)
  exact Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv hnorm)

theorem relativeClassCoordinate_abs_le_one
    (left right : RationalUnitQuaternion) :
    Q'.abs (relativeClassCoordinate left right) ≤ (1 : Q') := by
  exact Q'.abs_le_of_sq_le_sq
    (by decide)
    (relativeClassCoordinate_sq_le_one left right)

theorem relativeClassCoordinate_upper
    (left right : RationalUnitQuaternion) :
    relativeClassCoordinate left right ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.le_abs_self (relativeClassCoordinate left right))
    (relativeClassCoordinate_abs_le_one left right)

theorem relativeClassCoordinate_lower
    (left right : RationalUnitQuaternion) :
    (-(1 : Q')) ≤ relativeClassCoordinate left right := by
  have hfirst :
      (-(1 : Q')) ≤
        -(Q'.abs (relativeClassCoordinate left right)) :=
    Q'.neg_le_neg
      (relativeClassCoordinate_abs_le_one left right)
  have hsecond :
      -(Q'.abs (relativeClassCoordinate left right)) ≤
        -(-(relativeClassCoordinate left right)) :=
    Q'.neg_le_neg
      (Q'.neg_le_abs (relativeClassCoordinate left right))
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.neg_neg_eqv
          (relativeClassCoordinate left right))))

theorem relativeClassCoordinate_one :
    relativeClassCoordinate
        rationalUnitQuaternionOne rationalUnitQuaternionOne ≈
      1 := by
  decide

/-! ## 4. Full 23-cycle and effective five-holonomy configurations -/

abbrev BF4SpatialConfiguration :=
  BF4SpatialCycle → RationalUnitQuaternion

abbrev BF4FiveHolonomyConfiguration :=
  BF4TemporalHolonomy → RationalUnitQuaternion

/-- The canonical identity point of the enlarged 23-cycle carrier. -/
def identitySpatialConfiguration : BF4SpatialConfiguration :=
  fun _ => rationalUnitQuaternionOne

/-- Exact projection from the enlarged 23-cycle carrier to the five
transmitted temporal chords. -/
def projectFiveHolonomies
    (configuration : BF4SpatialConfiguration) :
    BF4FiveHolonomyConfiguration :=
  fun coordinate =>
    configuration (transmittedSpatialCycle coordinate)

/-- The identity point projects to the identity point of the five-holonomy
carrier. -/
theorem projectFiveHolonomies_identity :
    projectFiveHolonomies identitySpatialConfiguration =
      (fun _ => rationalUnitQuaternionOne) :=
  rfl

/-- The actual per-cycle kinetic class coordinate on the enlarged BF4
source/target carrier. -/
def spatialRelativeClassCoordinate
    (source target : BF4SpatialConfiguration)
    (factor : BF4SpatialCycle) : Q' :=
  relativeClassCoordinate (source factor) (target factor)

/-- The actual per-coordinate class variable on the effective five-holonomy
source/target carrier. -/
def fiveRelativeClassCoordinate
    (source target : BF4FiveHolonomyConfiguration)
    (factor : BF4TemporalHolonomy) : Q' :=
  relativeClassCoordinate (source factor) (target factor)

theorem spatialRelativeClassCoordinate_lower
    (source target : BF4SpatialConfiguration)
    (factor : BF4SpatialCycle) :
    (-(1 : Q')) ≤
      spatialRelativeClassCoordinate source target factor :=
  relativeClassCoordinate_lower _ _

theorem spatialRelativeClassCoordinate_upper
    (source target : BF4SpatialConfiguration)
    (factor : BF4SpatialCycle) :
    spatialRelativeClassCoordinate source target factor ≤ (1 : Q') :=
  relativeClassCoordinate_upper _ _

theorem projectedFiveRelativeClassCoordinate
    (source target : BF4SpatialConfiguration)
    (factor : BF4TemporalHolonomy) :
    fiveRelativeClassCoordinate
        (projectFiveHolonomies source)
        (projectFiveHolonomies target) factor =
      spatialRelativeClassCoordinate source target
        (transmittedSpatialCycle factor) :=
  rfl

/-! ## 5. Complete physical source/target/path/factor locations -/

/-- One literal location at which a BF4 spatial kinetic factor is
evaluated.  The path is retained even though the bare kinetic coordinate
depends only on the source, target, and cycle factor. -/
structure BF4SpatialClassLocation (State : Type) : Type where
  source : BF4SpatialConfiguration
  target : BF4SpatialConfiguration
  path : List State
  factor : BF4SpatialCycle

/-- The exact class-coordinate map on the full physical-location type. -/
def spatialLocationClassCoordinate
    {State : Type}
    (location : BF4SpatialClassLocation State) : Q' :=
  spatialRelativeClassCoordinate
    location.source location.target location.factor

/-- Cartesian enumeration of every displayed source/target/path/factor
location. -/
def bf4SpatialClassLocations
    {State : Type}
    (sources targets : List BF4SpatialConfiguration)
    (paths : List (List State)) :
    List (BF4SpatialClassLocation State) :=
  sources.flatMap fun source =>
    targets.flatMap fun target =>
      paths.flatMap fun path =>
        (List.finRange bf4SpatialCycleCount).map fun factor =>
          { source := source
            target := target
            path := path
            factor := factor }

/-- Nonempty endpoint/path data from which the complete retained physical
location carrier is computed. -/
structure BF4SpatialLocationCarrierData (State : Type) : Type where
  firstSource : BF4SpatialConfiguration
  otherSources : List BF4SpatialConfiguration
  firstTarget : BF4SpatialConfiguration
  otherTargets : List BF4SpatialConfiguration
  firstPath : List State
  otherPaths : List (List State)

/-- A genuine `FinitePhysicalLocationCarrier` whose entries are the complete
BF4 source/target/path/factor tuples above.  The full Cartesian list is kept
in `rest`; retaining the distinguished first location once more is harmless
and makes nonemptiness definitionally visible. -/
def BF4SpatialLocationCarrierData.toFiniteCarrier
    {State : Type}
    (data : BF4SpatialLocationCarrierData State) :
    FinitePhysicalLocationCarrier (BF4SpatialClassLocation State) where
  first :=
    { source := data.firstSource
      target := data.firstTarget
      path := data.firstPath
      factor := ⟨0, by
        unfold bf4SpatialCycleCount
        omega⟩ }
  rest :=
    bf4SpatialClassLocations
      (data.firstSource :: data.otherSources)
      (data.firstTarget :: data.otherTargets)
      (data.firstPath :: data.otherPaths)

/-- A completely explicit nonempty canonical BF4 physical-location carrier.
It retains the identity source and target, the empty `Unit` path, and all
23 literal cycle factors. -/
def canonicalBF4SpatialLocationCarrierData :
    BF4SpatialLocationCarrierData Unit where
  firstSource := identitySpatialConfiguration
  otherSources := []
  firstTarget := identitySpatialConfiguration
  otherTargets := []
  firstPath := []
  otherPaths := []

def canonicalBF4SpatialFiniteLocationCarrier :
    FinitePhysicalLocationCarrier
      (BF4SpatialClassLocation Unit) :=
  canonicalBF4SpatialLocationCarrierData.toFiniteCarrier

theorem spatialLocationClassCoordinate_lower
    {State : Type}
    (location : BF4SpatialClassLocation State) :
    (-(1 : Q')) ≤ spatialLocationClassCoordinate location :=
  spatialRelativeClassCoordinate_lower _ _ _

theorem spatialLocationClassCoordinate_upper
    {State : Type}
    (location : BF4SpatialClassLocation State) :
    spatialLocationClassCoordinate location ≤ (1 : Q') :=
  spatialRelativeClassCoordinate_upper _ _ _

/-! ## 6. Literal 23-factor heat corridor on the canonical carrier -/

theorem bf4SpatialFactors_length :
    (List.finRange bf4SpatialCycleCount).length =
      bf4SpatialCycleCount := by
  simp

/-- The all-label finite heat corridor instantiated on the actual 23
tree-gauge BF4 cycle coordinates.  This constructs the kinetic reference
layer; it does not identify the spatially weighted nonlinear transfer with
the five-holonomy Mehler operator. -/
def canonicalBF4SpatialFiniteHeatHarnack
    {State : Type}
    (paths : List (List State))
    (heatNome : BF4SpatialCycle → Q')
    (cutoff : BF4SpatialCycle → Nat)
    (sources targets : List BF4SpatialConfiguration)
    (nome_nonnegative :
      ∀ factor, factor ∈ List.finRange bf4SpatialCycleCount →
        (0 : Q') ≤ heatNome factor)
    (nome_le_half :
      ∀ factor, factor ∈ List.finRange bf4SpatialCycleCount →
        heatNome factor ≤ SU2AllLabelPointwiseHeatCorridor.half) :
    RetainedKineticHarnackData
      paths
      (finitePointwiseRetainedKinetic
        (List.finRange bf4SpatialCycleCount)
        heatNome
        (fun source target _path factor =>
          spatialRelativeClassCoordinate source target factor)
        cutoff)
      sources targets :=
  finitePointwiseBF4RetainedKineticHarnack
    paths
    (List.finRange bf4SpatialCycleCount)
    bf4SpatialFactors_length
    heatNome
    (fun source target _path factor =>
      spatialRelativeClassCoordinate source target factor)
    cutoff sources targets
    nome_nonnegative nome_le_half
    (fun source _ target _ _path _ factor _ =>
      spatialRelativeClassCoordinate_lower source target factor)
    (fun source _ target _ _path _ factor _ =>
      spatialRelativeClassCoordinate_upper source target factor)

#print axioms bf4SpatialTreeChord_subset_boundary
#print axioms bf4SpatialBoundary_subset_treeChord
#print axioms bf4SpatialChord
#print axioms transmittedSpatialCycle
#print axioms relativeClassCoordinate_sq_le_one
#print axioms relativeClassCoordinate_abs_le_one
#print axioms relativeClassCoordinate_lower
#print axioms relativeClassCoordinate_upper
#print axioms rationalUnitQuaternionOne
#print axioms relativeClassCoordinate_one
#print axioms projectFiveHolonomies
#print axioms projectedFiveRelativeClassCoordinate
#print axioms BF4SpatialLocationCarrierData.toFiniteCarrier
#print axioms canonicalBF4SpatialFiniteLocationCarrier
#print axioms spatialLocationClassCoordinate_lower
#print axioms spatialLocationClassCoordinate_upper
#print axioms canonicalBF4SpatialFiniteHeatHarnack

end YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
