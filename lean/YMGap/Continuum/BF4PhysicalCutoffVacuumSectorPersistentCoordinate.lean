/-
# Persistent coordinates for arbitrary sector Cauchy representatives

The stationary weight at a fixed old sector state has a positive floor at
all sufficiently large cutoffs. Thus evaluation at that state controls its
squared difference by the actual cutoff-removed squared distance, even for
two cylinder presentations with different bases. Applying the supplied
completion modulus at `floor * epsilon^2` constructs a rational Cauchy
coordinate sequence and its Bishop-real limit without choosing representatives.

Explicit closeness moduli make the limits independent of representatives,
so evaluation descends to the actual completion. The completed Dirichlet
endpoint bound is a separate obligation. No uniform spectral gap or continuum
construction is asserted.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

-- The proof uses the retained-carrier lemmas, not enumeration of the lattice.
attribute [local irreducible] centralPhysicalFiniteCarrierSize
  centralPhysicalFiniteIndexCarrier centralPhysicalFiniteVacuumSectorIndices
  centralPositiveHalfStates

private theorem term_le_sum {A : Type} (f : A → Q')
    (hf : ∀ a, (0 : Q') ≤ f a) :
    ∀ (items : List A) {a : A}, a ∈ items → f a ≤ listQSum f items
  | [], _, ha => False.elim (List.not_mem_nil ha)
  | head :: tail, a, ha => by
      rcases List.mem_cons.mp ha with heq | htail
      · subst a
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on f tail (fun item _ => hf item))
      · exact Q'.le_trans' _ _ _ (term_le_sum f hf tail htail)
          (Q'.le_trans' _ (listQSum f tail + f head) _
            (Q'.add_le_self_of_nonneg _ _ (hf head))
            (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Evaluate the actual cylinder observable at a retained base-sector state. -/
def coordinate {w : Q'} {hw : (0 : Q') ≤ w}
    (base half index : Nat)
    (p : CentralPhysicalVacuumSectorCylinderPresentation w hw half) : Q' :=
  p.toLinearObservable.value (centralPhysicalFiniteStateAt w hw base half index)

private theorem finiteDistance_eq_weightedDifference
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : EdgeLabelling → Q') :
    (centralPhysicalSmulGNS w hw cutoff half).toGNSData.distSqQ left right =
      centralPhysicalWeightedInner w hw cutoff half
        (fun state => left state + -right state)
        (fun state => left state + -right state) := rfl

/-- A fixed coordinate has a base-dependent positive visibility floor on
arbitrary cylinder differences. The two presentation bases need not agree. -/
theorem coordinateDifferenceSq_floor_le_distSq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (left right : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.leEv
      (CReal.ofQ'
        (centralPhysicalVacuumSectorCoordinateFloor
            w (Q'.le_of_lt hw0) base half *
          ((coordinate base half index left + -coordinate base half index right) *
            (coordinate base half index left + -coordinate base half index right))))
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).distSq left right) := by
  intro epsilon hepsilon
  let anchor := centralPhysicalVacuumSectorCoordinateAnchor w base half
  refine ⟨anchor, fun later hlater => ?_⟩
  have hbaseAnchor : base ≤ anchor := Nat.le_max_right _ _
  have hbaseLater : base ≤ later := Nat.le_trans hbaseAnchor hlater
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw0) base half hindex
  let target := centralPhysicalFiniteCutoffIndexMap
    w (Q'.le_of_lt hw0) base later half index
  have htargetLt : target < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) later half :=
    centralPhysicalFiniteCutoffIndexMap_lt
      (w := w) (hw := Q'.le_of_lt hw0) (base := base) (later := later)
      (half := half) (index := index) hbaseLater hindexLt
  let difference := fun state => left.toLinearObservable.value state +
    -right.toLinearObservable.value state
  let coefficient := centralPhysicalFiniteCoefficient
    w (Q'.le_of_lt hw0) later half difference
  let weight := centralPhysicalFiniteWeight w (Q'.le_of_lt hw0) later half
  let delta := coordinate base half index left + -coordinate base half index right
  let floor := centralPhysicalVacuumSectorCoordinateFloor
    w (Q'.le_of_lt hw0) base half
  have hstate := centralPhysicalFiniteStateAt_cutoffIndexMap_eq
    (w := w) (hw := Q'.le_of_lt hw0) (base := base) (later := later)
    (half := half) (index := index) hbaseLater hindexLt
  have hcoordinate : coefficient target = delta :=
    congrArg (fun state => left.toLinearObservable.value state +
      -right.toLinearObservable.value state) hstate
  have hsourceAnchor :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw0) base half index ∈
        centralPositiveHalfStates w (Q'.le_of_lt hw0) anchor half :=
    mem_centralPositiveHalfStates_of_le (Q'.le_of_lt hw0) hbaseAnchor
      (centralPhysicalFiniteStateAt_mem_positive
        w (Q'.le_of_lt hw0) base half hindexLt)
  have hfloor : floor ≤ weight target := by
    have hrow := centralPhysicalMovingPositiveRowFloor_le hw0 hw1 half
      (show centralPhysicalUniformRowFloorCutoff w half ≤ anchor from
        Nat.le_max_left _ _) hlater hsourceAnchor
    have hweight : weight target = centralPhysicalRowMarginal
        w (Q'.le_of_lt hw0) later half
        (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw0) base half index) :=
      congrArg (centralPhysicalRowMarginal w (Q'.le_of_lt hw0) later half) hstate
    exact Q'.le_trans' _ _ _ hrow
      (Q'.le_of_eqv (Q'.eqv_of_eq hweight.symm))
  have hterm : (coefficient target * coefficient target) * weight target ≤
      finiteDiagonalQuadratic
        (centralPhysicalFiniteCarrierSize w (Q'.le_of_lt hw0) later half)
        weight coefficient := by
    unfold finiteDiagonalQuadratic
    exact term_le_sum
      (fun i => (coefficient i * coefficient i) * weight i)
      (fun i => Q'.mul_nonneg _ _ (q_mul_self_nonneg (coefficient i))
        (centralPhysicalRowMarginal_nonnegative (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw0) later half i)))
      (List.range (centralPhysicalFiniteCarrierSize w (Q'.le_of_lt hw0) later half))
      (List.mem_range.mpr htargetLt)
  have hfloorTerm : floor * (delta * delta) ≤
      (coefficient target * coefficient target) * weight target := by
    have hscaled : floor * (delta * delta) ≤ (delta * delta) * weight target :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor (q_mul_self_nonneg delta))
    have hsquare := congrArg (fun value => (value * value) * weight target) hcoordinate
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.eqv_of_eq hsquare.symm))
  have hbridge := centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
    w (Q'.le_of_lt hw0) later half difference
  have hdiag : floor * (delta * delta) ≤
      (centralPhysicalSmulGNS w (Q'.le_of_lt hw0) later half).toGNSData.distSqQ
        left.toLinearObservable.value right.toLinearObservable.value := by
    have hweighted := Q'.le_trans' _ _ _ hterm (Q'.le_of_eqv hbridge)
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hfloorTerm hweighted)
      (Q'.le_of_eqv (Q'.eqv_of_eq
        (finiteDistance_eq_weightedDifference w (Q'.le_of_lt hw0)
          later half left.toLinearObservable.value right.toLinearObservable.value).symm))
  have hstage := physicalLinearDistSq_approx_eqv_stage
    hw0 hw1 half later left.toLinearObservable right.toLinearObservable
  exact Q'.le_trans' _ _ _ hdiag
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hstage)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))

private theorem rational_le_of_constant_le {a b : Q'}
    (h : CReal.leEv (CReal.ofQ' a) (CReal.ofQ' b)) : a ≤ b := by
  refine Q'.le_of_forall_pos_add (fun epsilon hepsilon => ?_)
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  simpa using hN N (Nat.le_refl N)

/-- The supplied completion modulus gives an explicit rational coordinate
Cauchy modulus `epsilon |-> X.modulus (floor * epsilon^2)`. -/
def coordinateQCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).Cauchy) :
    CReal.QCauchy (fun n => coordinate base half index (X.seq n)) where
  M := fun epsilon => X.modulus
    (centralPhysicalVacuumSectorCoordinateFloor
      w (Q'.le_of_lt hw0) base half * (epsilon * epsilon))
  bound := by
    intro epsilon hepsilon first second hfirst hsecond
    let floor := centralPhysicalVacuumSectorCoordinateFloor
      w (Q'.le_of_lt hw0) base half
    let delta := coordinate base half index (X.seq first) +
      -coordinate base half index (X.seq second)
    have hfloor := centralPhysicalVacuumSectorCoordinateFloor_pos
      w (Q'.le_of_lt hw0) base half
    have hdist := X.isCauchy (floor * (epsilon * epsilon))
      (Q'.mul_pos hfloor (Q'.mul_pos hepsilon hepsilon))
      first second hfirst hsecond
    have hcoordinate := coordinateDifferenceSq_floor_le_distSq
      hw0 hw1 base half index hindex (X.seq first) (X.seq second)
    have hsquare : delta * delta ≤ epsilon * epsilon :=
      Q'.le_of_mul_le_mul_left
        (rational_le_of_constant_le (CReal.leEv_trans hcoordinate hdist)) hfloor
    exact Q'.two_sided_of_abs_sub_le (Q'.abs_le_of_sq_le_sq hepsilon hsquare)

/-- The coordinate limit of the given Cauchy representative; no representative
is selected from a completed quotient or a proposition. -/
def coordinateLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).Cauchy) :
    CReal :=
  CReal.ofQ'CauchySeq (fun n => coordinate base half index (X.seq n))
    (coordinateQCauchy hw0 hw1 base half index hindex X)

theorem coordinate_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo (fun n => CReal.ofQ' (coordinate base half index (X.seq n)))
      (coordinateLimit hw0 hw1 base half index hindex X) :=
  CReal.convergesTo_ofQ'CauchySeq _ _

/-- Explicit coordinate closeness rate, retained as data before quotient
well-definedness uses it in a propositional convergence argument. -/
def coordinateCloseModulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat)
    {X Y : (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).Cauchy}
    (close : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Close X Y) (epsilon : Q') : Nat :=
  close.modulus (centralPhysicalVacuumSectorCoordinateFloor
    w (Q'.le_of_lt hw0) base half * (epsilon * epsilon))

theorem coordinateLimit_equiv_of_close
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    {X Y : (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).Cauchy}
    (close : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Close X Y) :
    CReal.Equiv (coordinateLimit hw0 hw1 base half index hindex X)
      (coordinateLimit hw0 hw1 base half index hindex Y) := by
  apply CReal.Equiv_of_ofQ'_limit_close
    (coordinate_converges hw0 hw1 base half index hindex X)
    (coordinate_converges hw0 hw1 base half index hindex Y)
  intro epsilon hepsilon
  refine ⟨coordinateCloseModulus hw0 hw1 base half close epsilon, ?_⟩
  intro n hn
  let floor := centralPhysicalVacuumSectorCoordinateFloor
    w (Q'.le_of_lt hw0) base half
  let delta := coordinate base half index (X.seq n) +
    -coordinate base half index (Y.seq n)
  have hfloor := centralPhysicalVacuumSectorCoordinateFloor_pos
    w (Q'.le_of_lt hw0) base half
  have hdist := close.close (floor * (epsilon * epsilon))
    (Q'.mul_pos hfloor (Q'.mul_pos hepsilon hepsilon)) n hn
  have hcoordinate := coordinateDifferenceSq_floor_le_distSq
    hw0 hw1 base half index hindex (X.seq n) (Y.seq n)
  have hsquare : delta * delta ≤ epsilon * epsilon :=
    Q'.le_of_mul_le_mul_left
      (rational_le_of_constant_le (CReal.leEv_trans hcoordinate hdist)) hfloor
  exact Q'.two_sided_of_abs_sub_le (Q'.abs_le_of_sq_le_sq hepsilon hsquare)

/-- Evaluation at a fixed retained sector state on the actual completion.
This is quotient descent, not a choice of Cauchy representative. -/
def completedCoordinate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).Completion →
      CReal.RC :=
  Quotient.lift
    (fun X => Quotient.mk CReal.crealSetoid
      (coordinateLimit hw0 hw1 base half index hindex X))
    (by
      intro X Y hclose
      rcases hclose with ⟨close⟩
      exact Quotient.sound
        (coordinateLimit_equiv_of_close hw0 hw1 base half index hindex close))

/-- On a dense cylinder this completed functional is literal evaluation of
the unchanged observable at the fixed old state. -/
theorem completedCoordinate_embedRep
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (p : CentralPhysicalVacuumSectorCylinderPresentation w (Q'.le_of_lt hw0) half) :
    completedCoordinate hw0 hw1 base half index hindex
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).embedRep p) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (coordinate base half index p)) := by
  rfl

#print axioms coordinateDifferenceSq_floor_le_distSq
#print axioms coordinateQCauchy
#print axioms coordinateLimit
#print axioms coordinate_converges
#print axioms coordinateCloseModulus
#print axioms coordinateLimit_equiv_of_close
#print axioms completedCoordinate
#print axioms completedCoordinate_embedRep

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate
