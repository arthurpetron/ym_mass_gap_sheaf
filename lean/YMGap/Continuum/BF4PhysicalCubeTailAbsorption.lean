/-
# Raw physical tail control and fixed-head Dirichlet absorption

The already proved self-return trace controls the UNCENTERED physical Gram,
not just its component-centered version. At extent one and 0<w<=1/2,
base=1400+epsilon.den bounds every literal new-tail form by epsilon times
its own stationary norm, uniformly in every later cutoff.

Taking epsilon=1/4 fixes base=1404. Positivity absorbs the mixed block and
leaves the all-vector estimate

    stationaryNormSquared(f) <= directedEnergy(f) + 3*headNormSquared(f).

This is a defective Poincare inequality for the original kernel and original
marginal. The directed energy is twice the conventional Dirichlet deficit.
It is NOT a spectral gap: a root-anchored finite-head energy estimate is still
needed, followed by the existing completion and physical-identification work.
No action/geometric-time, volume/spacing, continuum or Clay closure is claimed.
-/

import YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance

namespace YMGap.Continuum.BF4PhysicalCubeTailAbsorption

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeGaussianReturn
open YMGap.Continuum.BF4PhysicalCubeHighLabelTrace
open YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace
open YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveFormHeadTailGluing
open YMGap.Continuum.FinitePositiveFormTraceGluing
open YMGap.Continuum.FiniteWeightedGramGNSData
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The raw self-return trace itself is small, before stationary subtraction. -/
theorem newTailSelfReturnTrace_small {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (later : Nat) (hlater : newTailBase epsilon ≤ later) :
    centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
      w (Q'.le_of_lt hw0) (newTailBase epsilon) later 0 ≤ epsilon := by
  refine Q'.le_trans' _ _ _ (newTailSelfReturnTrace_le_highLabel hw0
    (newTailBase epsilon) later (by unfold newTailBase; omega) hlater) ?_
  have hi : newTailBase epsilon + 1 = radialTailCutoff epsilon := by
    unfold newTailBase radialTailCutoff
    omega
  rw [hi]
  exact highLabelTrace_small hw0 hw epsilon he later

-- Private packaging of the EXISTING uncentered boundary transform. Its exact
-- equality to the original physical matrix is used below, not assumed.
private def rawGram (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : GNSData :=
  finiteWeightedGramGNSData
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralBoundaryChannels K 0)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw K 0)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw K 0)
    (fun b hb => centralPhysicalFiniteVacuumSectorGramWeight_nonnegative b hb)

private theorem matrix_eq_rawGram (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (f : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw K 0 f ≈
      (rawGram w hw K).B f f :=
  Q'.eqv_trans _ _ _ (centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_weightedGram
    w hw K 0 f) (weightedGramQuadratic_eq_sos _ _ _ _ _)

private theorem raw_coordinate (w : Q') (hw : (0 : Q') ≤ w) (K i : Nat)
    (hi : i ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (rawGram w hw K).B (centralPhysicalFiniteVacuumSectorCoordinate i)
      (centralPhysicalFiniteVacuumSectorCoordinate i) ≈
      centralPhysicalFiniteKernel w hw K 0 i i :=
  Q'.eqv_trans _ _ _
    (weightedGramBilinear_finiteCoordinate_self_eqv_weightedGram _ _ _ _ i
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0) hi)
    (Q'.eqv_symm (centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram hi hi))

private theorem raw_combination_eq_centered (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (f : Nat → Q') : ∀ indices : List Nat,
    finiteLinearCombination (rawGram w hw K)
      centralPhysicalFiniteVacuumSectorCoordinate f indices =
    finiteLinearCombination (centralPhysicalFiniteVacuumSectorCenteredGramGNSData w hw K 0)
      centralPhysicalFiniteVacuumSectorCoordinate f indices
  | [] => rfl
  | i :: rest => by
      change (fun j => f i * centralPhysicalFiniteVacuumSectorCoordinate i j +
        (finiteLinearCombination (rawGram w hw K)
          centralPhysicalFiniteVacuumSectorCoordinate f rest) j) = _
      rw [raw_combination_eq_centered w hw K f rest]
      rfl

/-- A raw self-return trace bound controls the full UNCENTERED physical
new-tail form. This is the generic algebraic seam used by both the fixed-nome
and coupling-adaptive trace estimates. -/
theorem matrix_newTail_le_of_selfReturnTrace {w : Q'} (hw0 : (0 : Q') < w)
    (base later : Nat) (_hbase : base ≤ later) (epsilon : Q')
    (htrace : centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
      w (Q'.le_of_lt hw0) base later 0 ≤ epsilon) (f : Nat → Q') :
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w (Q'.le_of_lt hw0) base later 0 f
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) later 0 tail ≤
      epsilon * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) later 0 tail := by
  let hw' := Q'.le_of_lt hw0
  let D := rawGram w hw' later
  let indices := centralPhysicalFiniteVacuumSectorNewBlockIndices w hw' base later 0
  let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient w hw' base later 0 f
  let assembled := finiteLinearCombination D centralPhysicalFiniteVacuumSectorCoordinate f indices
  have hgram := finiteLinearCombination_self_le_traceBudget D
    centralPhysicalFiniteVacuumSectorCoordinate (centralPhysicalFiniteWeight w hw' later 0)
    (centralPhysicalFiniteVacuumSectorSelfReturnProbability w hw' later 0) f indices
    (fun i hi => Q'.le_of_lt (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hi).1))
    (fun i hi => by
      have his := (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hi).1
      rw [selfReturnProbability_eq_conditional w hw' later 0 his]
      exact centralPhysicalConditionalKernel_nonnegative hw' later 0 _ _)
    (fun i hi => by
      have his := (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hi).1
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (raw_coordinate w hw' later i his)) ?_
      unfold centralPhysicalFiniteVacuumSectorSelfReturnProbability
      rw [dif_pos his]
      exact Q'.ge_of_eqv (Q'.divPos_mul_eqv _ _ _))
  have hagree (i : Nat) (hi : i ∈ centralPhysicalFiniteVacuumSectorIndices w hw' later 0) :
      assembled i ≈ tail i := by
    unfold assembled D
    rw [raw_combination_eq_centered]
    exact centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_newTail_on
      w hw' base later 0 f i hi
  have hform : D.B assembled assembled ≈ D.B tail tail :=
    weightedGramBilinear_congr_on _ _ _ _ hagree hagree
  have hbudget := centralPhysicalFiniteVacuumSectorDiagonalQuadratic_newTail_eqv_budget
    w hw' base later 0 f
  have hgrow := Q'.mul_le_mul_of_nonneg_right _ _ _
    htrace
    (centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget_nonnegative w hw' base later 0 f)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (matrix_eq_rawGram w hw' later tail))
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hform)
      (Q'.le_trans' _ _ _ hgram (Q'.le_trans' _ _ _ hgrow
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left epsilon _ _ (Q'.eqv_symm hbudget))))))

/-- Full UNCENTERED physical new-tail estimate, in the original stationary
norm and uniformly over every later admitting cutoff. -/
theorem matrix_newTail_le {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (later : Nat) (hlater : newTailBase epsilon ≤ later) (f : Nat → Q') :
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w (Q'.le_of_lt hw0) (newTailBase epsilon) later 0 f
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) later 0 tail ≤
      epsilon * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) later 0 tail :=
  matrix_newTail_le_of_selfReturnTrace hw0 (newTailBase epsilon) later hlater epsilon
    (newTailSelfReturnTrace_small hw0 hw epsilon he later hlater) f

/-! ## Fixed-head absorption, without a head spectral-gap hypothesis -/

/-- The fixed raw-tail rate used for absorption. -/
def absorptionTailRate : Q' := Q'.mkPos 1 4 (by decide)

theorem absorptionTailRate_pos : (0 : Q') < absorptionTailRate := by decide

theorem absorption_base_eq : newTailBase absorptionTailRate = 1404 := rfl

private theorem twice_quarter (X Y : Q') :
    2 * (2 * (X + absorptionTailRate * Y)) ≈ 4 * X + Y := by
  refine Q'.eqv_trans _ ((2 * 2) * (X + absorptionTailRate * Y)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ (4 * (X + absorptionTailRate * Y)) _
    (Q'.mul_eqv_congr_right _ _ _ (by decide)) ?_
  refine Q'.eqv_trans _ (4 * X + 4 * (absorptionTailRate * Y)) _
    (Q'.mul_add_eqv _ _ _) ?_
  apply Q'.add_eqv_congr_left
  exact Q'.eqv_trans _ ((4 * absorptionTailRate) * Y) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ (1 * Y) _ (Q'.mul_eqv_congr_right _ _ _ (by decide)) (Q'.one_mul_eqv Y))

private theorem absorption_left (X Y : Q') :
    ((X + Y) + (X + Y) + 3 * X) + -(4 * X + Y) ≈ X + Y := by
  let x := PolyExpr.var 0
  let y := PolyExpr.var 1
  let e : PolyExpr := .add (.add (.add (.add x y) (.add x y)) (.mul (.const 3) x))
    (.neg (.add (.mul (.const 4) x) y))
  let rhs : PolyExpr := .add x y
  have h := poly_identity_of_normal_eq e rhs (by decide) (fun i => if i = 0 then X else Y)
  simpa [e, rhs, x, y, RingNormaliser.eval] using h

private theorem absorption_right (A X P : Q') :
    (A + X) + -(2 * P) ≈ (A + -(P + P)) + X := by
  refine Q'.eqv_trans _ ((A + X) + -(P + P)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (OSReconstructionProgress.q_two_mul P)))) ?_
  refine Q'.eqv_trans _ (A + (X + -(P + P))) _ (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (A + (-(P + P) + X)) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem absorption_algebra (N P X Y E : Q')
    (hsplit : N ≈ X + Y) (he : E ≈ (N + N) + -(P + P))
    (hp : 2 * P ≤ 4 * X + Y) : N ≤ E + 3 * X := by
  have hneg := Q'.add_le_add_left ((X + Y) + (X + Y) + 3 * X) _ _ (Q'.neg_le_neg hp)
  have hleft := absorption_left X Y
  have hright : ((X + Y) + (X + Y) + 3 * X) + -(2 * P) ≈
      ((X + Y) + (X + Y) + -(P + P)) + 3 * X := absorption_right _ _ _
  have henergy : E ≈ (X + Y) + (X + Y) + -(P + P) :=
    Q'.eqv_trans _ _ _ he (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr' hsplit hsplit))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hneg (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
        (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ (3 * X) henergy)))))

/-- Raw positivity bounds the full form using only head contractivity and an
actual quarter bound for the self-return trace at the chosen base. -/
theorem matrix_le_two_head_quarter_tail_of_selfReturnTrace {w : Q'}
    (hw0 : (0 : Q') < w) (base later : Nat) (hbase : base ≤ later)
    (htrace : centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
      w (Q'.le_of_lt hw0) base later 0 ≤ absorptionTailRate) (f : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      2 * (centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w (Q'.le_of_lt hw0) base later 0 f) +
        absorptionTailRate * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorNewTailCoefficient w (Q'.le_of_lt hw0) base later 0 f)) := by
  let hw' := Q'.le_of_lt hw0
  let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w hw' base later 0 f
  let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient w hw' base later 0 f
  let X := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw' later 0 head
  let Y := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw' later 0 tail
  have hhead : centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw' later 0 head ≤ 1 * X :=
    Q'.le_trans' _ _ _ (centralPhysicalFiniteVacuumSectorMatrix_le_diagonal w hw' later 0 head)
      (Q'.ge_of_eqv (Q'.one_mul_eqv X))
  have htail : centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw' later 0 tail ≤
      1 * (absorptionTailRate * Y) :=
    Q'.le_trans' _ _ _
      (matrix_newTail_le_of_selfReturnTrace hw0 base later hbase absorptionTailRate htrace f)
      (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  have hglue := centralPhysicalFiniteVacuumSectorMatrix_head_tail_bilinear_le
    hw0 later 0 head tail 1 1 X (absorptionTailRate * Y) (by decide) (by decide) hhead htail
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_head_cross_tail hw0 base later 0 f))
    (Q'.le_trans' _ _ _ hglue
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ (X + absorptionTailRate * Y) (by decide))))

/-- Raw positivity bounds the full form using only head CONTRACTIVITY and
the proved quarter-tail bound. No strict head rate is assumed. -/
theorem matrix_le_two_head_quarter_tail {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (later : Nat) (hlater : 1404 ≤ later) (f : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      2 * (centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w (Q'.le_of_lt hw0) 1404 later 0 f) +
        absorptionTailRate * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorNewTailCoefficient w (Q'.le_of_lt hw0) 1404 later 0 f)) :=
  matrix_le_two_head_quarter_tail_of_selfReturnTrace hw0 1404 later hlater
    (by
      rw [← absorption_base_eq]
      exact newTailSelfReturnTrace_small hw0 hw absorptionTailRate absorptionTailRate_pos later
        (by simpa [absorption_base_eq] using hlater)) f

/-- Defective Poincare estimate at any base whose raw new-tail self-return
trace is at most one quarter. -/
theorem norm_le_energy_add_head_of_selfReturnTrace {w : Q'} (hw0 : (0 : Q') < w)
    (base later : Nat) (hbase : base ≤ later)
    (htrace : centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
      w (Q'.le_of_lt hw0) base later 0 ≤ absorptionTailRate) (f : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) +
        3 * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w (Q'.le_of_lt hw0) base later 0 f) := by
  let hw' := Q'.le_of_lt hw0
  let N := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw' later 0 f
  let P := centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw' later 0 f
  let X := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw' later 0
    (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w hw' base later 0 f)
  let Y := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw' later 0
    (centralPhysicalFiniteVacuumSectorNewTailCoefficient w hw' base later 0 f)
  let E := finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw' later 0)
    f (centralPhysicalFiniteKernel w hw' later 0)
  have hsplit : N ≈ X + Y := centralPhysicalFiniteVacuumSectorDiagonal_eqv_head_add_tail w hw' base later 0 f
  have he : E ≈ (N + N) + -(P + P) :=
    centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit w hw' later 0 f
  have hp : 2 * P ≤ 4 * X + Y :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 2
      (matrix_le_two_head_quarter_tail_of_selfReturnTrace hw0 base later hbase htrace f) (by decide))
      (Q'.le_of_eqv (twice_quarter X Y))
  exact absorption_algebra N P X Y E hsplit he hp

/-- Unconditional defective Poincare estimate on EVERY coefficient vector.
The head is fixed at 1404 while the outer cutoff is arbitrary. The energy
is the ORIGINAL directed physical edge energy (twice the usual deficit). -/
theorem norm_le_energy_add_head {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (later : Nat) (hlater : 1404 ≤ later) (f : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) +
        3 * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w (Q'.le_of_lt hw0) 1404 later 0 f) :=
  norm_le_energy_add_head_of_selfReturnTrace hw0 1404 later hlater
    (newTailSelfReturnTrace_small hw0 hw absorptionTailRate absorptionTailRate_pos later
      (by simpa [absorption_base_eq] using hlater)) f

/-! ## Root anchoring: only a fixed-head energy comparison remains -/

/-- Subtracting the value at the canonical vacuum index produces a literal
root-zero coefficient without changing the vector's differences. -/
def rootShift (f : Nat → Q') (i : Nat) : Q' := f i + -f 0

theorem rootShift_at_root (f : Nat → Q') : rootShift f 0 ≈ 0 :=
  Q'.add_neg_self_eqv (f 0)

/-- A centered coefficient has no larger stationary norm than its root
shift. This does not assume the sector has mass one. -/
theorem centered_norm_le_rootShift_norm (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w hw K 0 f ≈ 0) :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw K 0 f ≤
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw K 0 (rootShift f) := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw K 0
  let weight := centralPhysicalFiniteWeight w hw K 0
  let mass := centralPhysicalFiniteVacuumSectorMass w hw K 0
  let N := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw K 0 f
  let R := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw K 0 (rootShift f)
  have hr : finiteWeightedRootVariance states weight f 0 ≈ R := by
    unfold finiteWeightedRootVariance R centralPhysicalFiniteVacuumSectorDiagonalQuadratic rootShift
    apply listQSum_congr
    intro i
    exact Q'.mul_comm_eqv _ _
  have hpair := finiteWeightedPairwiseVariance_le_twice_mass_rootVariance states weight f 0
  have hc := centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv w hw K 0 f hcenter
  have hscaled : (mass + mass) * N ≤ (mass + mass) * R :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_mul_eqv mass mass N))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc)
        (Q'.le_trans' _ _ _ hpair (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left mass _ _ hr) (Q'.mul_eqv_congr_left mass _ _ hr)))
          (Q'.ge_of_eqv (Q'.add_mul_eqv mass mass R)))))
  have hm : (0 : Q') < mass := centralPhysicalFiniteVacuumSectorMass_pos w hw K 0
  exact Q'.le_of_mul_le_mul_left hscaled
    (Q'.pos_of_lt_of_le hm (Q'.add_le_self_of_nonneg mass mass (Q'.le_of_lt hm)))

private theorem shifted_difference (a b c : Q') :
    (a + -c) + -(b + -c) ≈ a + -b := by
  have hn : -(b + -c) ≈ -b + c :=
    Q'.eqv_trans _ _ _ (Q'.neg_add_eqv _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv c))
  refine Q'.eqv_trans _ ((a + -c) + (-b + c)) _
    (Q'.add_eqv_congr_left _ _ _ hn) ?_
  refine Q'.eqv_trans _ ((a + -b) + (-c + c)) _ (Q'.add_swap_inner _ _ _ _) ?_
  refine Q'.eqv_trans _ ((a + -b) + 0) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv c)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- Exact invariance of the original physical edge energy under root shift. -/
theorem energy_rootShift_eqv (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (f : Nat → Q') :
    finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      (rootShift f) (centralPhysicalFiniteKernel w hw K 0) ≈
    finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      f (centralPhysicalFiniteKernel w hw K 0) := by
  unfold finiteJointDirichletEnergy rootShift
  apply listQSum_congr
  intro i
  apply listQSum_congr
  intro j
  apply Q'.mul_eqv_congr_left
  have h := shifted_difference (f i) (f j) (f 0)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h)

/-- At any base with quarter-small raw trace, the full centered norm is
controlled by the original energy plus the corresponding anchored head. -/
theorem centered_norm_le_energy_add_anchored_head_of_selfReturnTrace {w : Q'}
    (hw0 : (0 : Q') < w) (base later : Nat) (hbase : base ≤ later)
    (htrace : centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
      w (Q'.le_of_lt hw0) base later 0 ≤ absorptionTailRate) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w (Q'.le_of_lt hw0) later 0 f ≈ 0) :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) +
        3 * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
            w (Q'.le_of_lt hw0) base later 0 (rootShift f)) :=
  Q'.le_trans' _ _ _ (centered_norm_le_rootShift_norm w (Q'.le_of_lt hw0) later f hcenter)
    (Q'.le_trans' _ _ _
      (norm_le_energy_add_head_of_selfReturnTrace hw0 base later hbase htrace (rootShift f))
      (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _
        (energy_rootShift_eqv w (Q'.le_of_lt hw0) later f))))

/-- The full centered norm is controlled by the same original energy plus
the norm on the FIXED head of the ROOT-ZERO coefficient. A finite-head
rooted path estimate now suffices; no strict head spectral rate is needed. -/
theorem centered_norm_le_energy_add_anchored_head {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (later : Nat) (hlater : 1404 ≤ later) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w (Q'.le_of_lt hw0) later 0 f ≈ 0) :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) +
        3 * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
            w (Q'.le_of_lt hw0) 1404 later 0 (rootShift f)) :=
  centered_norm_le_energy_add_anchored_head_of_selfReturnTrace hw0 1404 later hlater
    (newTailSelfReturnTrace_small hw0 hw absorptionTailRate absorptionTailRate_pos later
      (by simpa [absorption_base_eq] using hlater)) f hcenter

end YMGap.Continuum.BF4PhysicalCubeTailAbsorption

#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.newTailSelfReturnTrace_small
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.matrix_newTail_le_of_selfReturnTrace
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.matrix_newTail_le
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.absorptionTailRate
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.absorptionTailRate_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.absorption_base_eq
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.matrix_le_two_head_quarter_tail_of_selfReturnTrace
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.matrix_le_two_head_quarter_tail
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.norm_le_energy_add_head_of_selfReturnTrace
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.norm_le_energy_add_head
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.rootShift
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.rootShift_at_root
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.centered_norm_le_rootShift_norm
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.energy_rootShift_eqv
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.centered_norm_le_energy_add_anchored_head_of_selfReturnTrace
#print axioms YMGap.Continuum.BF4PhysicalCubeTailAbsorption.centered_norm_le_energy_add_anchored_head
