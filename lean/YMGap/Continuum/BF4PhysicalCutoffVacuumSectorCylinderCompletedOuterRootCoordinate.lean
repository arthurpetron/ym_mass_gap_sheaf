/-
# Root-coordinate control for arbitrary completed BF4 sector vectors

The distinguished vacuum-row weight has a positive cutoff-uniform floor.
Consequently, the square of the difference of the root coefficients of two
dense sector presentations is dominated, after multiplication by that floor,
by their actual cutoff-removed squared distance.  Reindexing the supplied
completion modulus at `floor * epsilon^2` therefore makes the root-coordinate
sequence of every sector Cauchy representative rational Cauchy.

This constructs the missing moving root limit needed to compare outer raw and
head-centered diagonals.  It does not yet prove centered-diagonal convergence,
the matrix comparison, a common strict rate, or any thermodynamic, continuum,
or Clay claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite root-coordinate domination -/

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items → value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          exact Q'.le_trans' _ (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head) (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem le_of_leEv_ofQ'_local {a b : Q'}
    (h : CReal.leEv (CReal.ofQ' a) (CReal.ofQ' b)) : a ≤ b := by
  refine Q'.le_of_forall_pos_add (fun epsilon hepsilon => ?_)
  obtain ⟨cutoff, hcutoff⟩ := h epsilon hepsilon
  simpa using hcutoff cutoff (Nat.le_refl cutoff)

/-- At every containing cutoff, evaluation of a sector presentation at the
distinguished carrier root recovers its source root coefficient. -/
private theorem centralPhysicalVacuumSectorCylinder_rootCoefficient_eqv
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation w hw half)
    {later : Nat} (hlater : presentation.base ≤ later) :
    centralPhysicalFiniteCoefficient w hw later half
        presentation.toLinearObservable.value 0 ≈
      presentation.coefficient 0 := by
  have hzeroBase := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w hw presentation.base half
  have hzeroLater :
      0 < centralPhysicalFiniteCarrierSize w hw later half :=
    centralPhysicalFiniteVacuumSectorIndex_lt w hw later half
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw later half)
  have hext :=
    centralPhysicalFiniteCoefficient_linearObservable_eqv_extension
      hlater presentation.coefficient hzeroLater
  have hroot :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map
      hlater hzeroBase presentation.coefficient
  rw [centralPhysicalFiniteCutoffIndexMap_zero] at hroot
  exact Q'.eqv_trans _ _ _ hext hroot

/-- The positive vacuum-row floor times the squared root-coordinate difference
is below the cutoff-removed physical squared distance of two presentations. -/
theorem centralPhysicalVacuumSectorCylinder_rootDifferenceSq_floor_le_distSq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.leEv
      (CReal.ofQ'
        (centralPhysicalUniformPositiveRowFloor
            w (Q'.le_of_lt hw0) half *
          ((left.coefficient 0 + -(right.coefficient 0)) *
            (left.coefficient 0 + -(right.coefficient 0)))))
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).distSq left right) := by
  intro epsilon hepsilon
  let start := max (centralPhysicalUniformRowFloorCutoff w half)
    (max left.base right.base)
  refine ⟨start, fun later hlater => ?_⟩
  have hfloorLater :
      centralPhysicalUniformRowFloorCutoff w half ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hleftLater : left.base ≤ later :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_max_right _ _)) hlater
  have hrightLater : right.base ≤ later :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_max_right _ _)) hlater
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) later half).toGNSData
  let difference := D.sub
    left.toLinearObservable.value right.toLinearObservable.value
  let coefficient := centralPhysicalFiniteCoefficient
    w (Q'.le_of_lt hw0) later half difference
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw0) later half
  let delta := left.coefficient 0 + -(right.coefficient 0)
  let floor := centralPhysicalUniformPositiveRowFloor
    w (Q'.le_of_lt hw0) half
  have hleftRoot := centralPhysicalVacuumSectorCylinder_rootCoefficient_eqv
    left hleftLater
  have hrightRoot := centralPhysicalVacuumSectorCylinder_rootCoefficient_eqv
    right hrightLater
  have hroot : coefficient 0 ≈ delta := by
    change left.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) later half 0) +
        -(right.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) later half 0)) ≈ delta
    exact Q'.add_eqv_congr' hleftRoot
      (Q'.neg_eqv_congr _ _ hrightRoot)
  have hrootSq : coefficient 0 * coefficient 0 ≈ delta * delta :=
    Q'.eqv_trans _ (delta * coefficient 0) _
      (Q'.mul_eqv_congr_right _ _ _ hroot)
      (Q'.mul_eqv_congr_left delta _ _ hroot)
  have hfloor : floor ≤ weight 0 := by
    have hpulled :=
      centralPhysicalUniformPositiveRowFloor_le_pulledWeight_zero
        hw0 hw1 left.base half hfloorLater
    unfold centralPhysicalFinitePulledWeight at hpulled
    rw [centralPhysicalFiniteCutoffIndexMap_zero] at hpulled
    exact hpulled
  have hterm :
      (coefficient 0 * coefficient 0) * weight 0 ≤
        finiteDiagonalQuadratic
          (centralPhysicalFiniteCarrierSize
            w (Q'.le_of_lt hw0) later half)
          weight coefficient := by
    unfold finiteDiagonalQuadratic
    exact listQSum_member_le_nonnegative_local
      (fun index => (coefficient index * coefficient index) * weight index)
      (fun index => Q'.mul_nonneg _ _
        (q_mul_self_nonneg (coefficient index))
        (centralPhysicalRowMarginal_nonnegative
          (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) later half index)))
      (List.range
        (centralPhysicalFiniteCarrierSize
          w (Q'.le_of_lt hw0) later half))
      (List.mem_range.mpr
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw0) later half
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw0) later half)))
  have hfloorTerm : floor * (delta * delta) ≤
      (coefficient 0 * coefficient 0) * weight 0 := by
    have hscaled : (delta * delta) * floor ≤ (delta * delta) * weight 0 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor
        (q_mul_self_nonneg delta)
    exact le_of_eqv_le (Q'.mul_comm_eqv floor (delta * delta))
      (le_of_le_eqv hscaled
        (Q'.eqv_trans _ ((coefficient 0 * coefficient 0) * weight 0) _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hrootSq))
          (Q'.eqv_refl _)))
  have hdiag : floor * (delta * delta) ≤ D.distSqQ
      left.toLinearObservable.value right.toLinearObservable.value := by
    have hbridge := centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
      w (Q'.le_of_lt hw0) later half difference
    have hweighted := le_of_le_eqv hterm hbridge
    exact Q'.le_trans' _ _ _ hfloorTerm (by
      simpa only [D, GNSQuotient.GNSData.distSqQ, difference,
        centralPhysicalSmulGNS_B_eq] using hweighted)
  have hstage := physicalLinearDistSq_approx_eqv_stage
    hw0 hw1 half later left.toLinearObservable right.toLinearObservable
  exact Q'.le_trans' _ _ _ hdiag
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hstage)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))

/-! ## 2. The root-coordinate Cauchy limit -/

/-- Root coefficient of the selected dense representative term. -/
def centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : Q' :=
  (X.seq stage).coefficient 0

/-- The completion modulus and the positive root-weight floor give an explicit
rational Cauchy modulus for the outer root coefficients. -/
def centralPhysicalVacuumSectorCylinderOuterRootCoefficientQCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.QCauchy
      (centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X) where
  M := fun epsilon => X.modulus
    (centralPhysicalUniformPositiveRowFloor
      w (Q'.le_of_lt hw0) half * (epsilon * epsilon))
  bound := by
    intro epsilon hepsilon first second hfirst hsecond
    let floor := centralPhysicalUniformPositiveRowFloor
      w (Q'.le_of_lt hw0) half
    let delta := (X.seq first).coefficient 0 +
      -((X.seq second).coefficient 0)
    have hfloor := centralPhysicalUniformPositiveRowFloor_pos
      w (Q'.le_of_lt hw0) half
    have htolerance : (0 : Q') < floor * (epsilon * epsilon) :=
      Q'.mul_pos hfloor (Q'.mul_pos hepsilon hepsilon)
    have hdist := X.isCauchy
      (floor * (epsilon * epsilon)) htolerance
      first second hfirst hsecond
    have hroot :=
      centralPhysicalVacuumSectorCylinder_rootDifferenceSq_floor_le_distSq
        hw0 hw1 half (X.seq first) (X.seq second)
    have hscaled : floor * (delta * delta) ≤
        floor * (epsilon * epsilon) :=
      le_of_leEv_ofQ'_local (CReal.leEv_trans hroot hdist)
    have hsquare : delta * delta ≤ epsilon * epsilon :=
      Q'.le_of_mul_le_mul_left hscaled hfloor
    exact Q'.two_sided_of_abs_sub_le
      (Q'.abs_le_of_sq_le_sq hepsilon hsquare)

/-- The Bishop-real root coordinate of an arbitrary completed-sector
representative. -/
def centralPhysicalVacuumSectorCylinderOuterRootCoefficientLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) : CReal :=
  CReal.ofQ'CauchySeq
    (centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X)
    (centralPhysicalVacuumSectorCylinderOuterRootCoefficientQCauchy
      hw0 hw1 half X)

/-- The rational root coefficients converge to their explicitly constructed
Bishop-real limit. -/
theorem centralPhysicalVacuumSectorCylinder_outerRootCoefficient_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        (centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X stage))
      (centralPhysicalVacuumSectorCylinderOuterRootCoefficientLimit
        hw0 hw1 half X) :=
  CReal.convergesTo_ofQ'CauchySeq _ _

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate.centralPhysicalVacuumSectorCylinder_rootDifferenceSq_floor_le_distSq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate.centralPhysicalVacuumSectorCylinder_outerRootCoefficient_converges
