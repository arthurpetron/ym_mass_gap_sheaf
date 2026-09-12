/-
# A constructed strict form bound on the whole reflected vacuum complement

Positivity gives ||P x||_M^2 <= q(w) <P x,x>_M on the completed marginal
vacuum sector. The already proved pairing and intertwining identities say
these are exactly <T R x,R x>_E and <R x,R x>_E. Thus the SAME rational
rate bounds the dense centered reflected images; the existing explicit
density/completion argument extends it to EVERY reflected vacuum-orthogonal
vector. No gap, comparison, or density certificate is an input here.

Scope: actual SU(2) BF4 conditional dynamics, extent one, w=1/400, all spin
labels and the entire reflected completion. This does not identify T with
geometric Euclidean time or the exact signed-Haar YM action, and supplies
no volume/spacing limit, continuum QFT, all-group result, or Clay theorem.
-/

import YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
import YMGap.Continuum.BF4PhysicalCubeDenseFormClosure

namespace YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
open YMGap.Continuum.BF4PhysicalCubeDissipation
open YMGap.Continuum.BF4PhysicalCubeDenseFormClosure
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "BM" => centralPhysicalVacuumSectorCylinderCompletedInner
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "PM" => centralPhysicalVacuumSectorCylinderCompletedTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "MC" => CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local notation "R" => sectorToReflected

/-- The original computed finite-sector rate, unchanged by both completions. -/
def reflectedGapRate : Q' := cutoffUniformRate anchorCoupling (by decide)

theorem reflectedGapRate_pos : (0 : Q') < reflectedGapRate :=
  cutoffUniformRate_pos anchorCoupling (by decide)

theorem reflectedGapRate_lt_one : reflectedGapRate < (1 : Q') :=
  cutoffUniformRate_lt_one anchorCoupling (by decide)

private theorem scale_eq_mul (q : Q') (x : RC) : RCscale q x = RCmul (Rq q) x := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

/-- Exact E pairing as ONE insertion of the SAME marginal-sector transfer;
this is not an assertion that R preserves the marginal norm. -/
theorem reflected_pairing_eq_sector (x y : (M).Completion) :
    B (R x) (R y) = BM x (PM y) := by
  rw [sectorToReflected_pairing]
  unfold completedReflectedForm centralPhysicalVacuumSectorCylinderCompletedInner
  have h := (centralPhysicalVacuumSectorCylinderTransferLiftData
    (w := anchorCoupling) (by decide) (by decide) 0).intertwines y
  unfold centralPhysicalVacuumSectorCylinderCompletedTransfer
  rw [h]

/-- The sharp square-form inequality becomes the desired reflected FORM
bound. In particular it has no marginal-norm prefactor on the right. -/
theorem sector_image_form_bound (x : MC) :
    RCle (B (T (R x.val)) (R x.val))
      (RCmul (Rq reflectedGapRate) (B (R x.val) (R x.val))) := by
  have h := centralPhysicalVacuumSectorCylinderCompletedTransfer_square_form_gap
    (centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
      (w := anchorCoupling) (by decide) (by decide) 0)
    (completedSectorFormGap (w := anchorCoupling) (by decide) (by decide) (by decide)) x
  rw [cubeTransfer_sector]
  change RCle (B (R (PM x.val)) (R x.val))
    (RCmul (Rq reflectedGapRate) (B (R x.val) (R x.val)))
  rw [reflected_pairing_eq_sector, reflected_pairing_eq_sector]
  have hs : BM x.val (PM x.val) = BM (PM x.val) x.val :=
    centralPhysicalCutoffCompletedInner_symm
      (w := anchorCoupling) (by decide) (by decide) 0 _ _
  rw [hs, ← scale_eq_mul]
  exact h

/-- The existing moving-centered observable has the same strict reflected
bound, with its zero mean proved by the original construction. -/
theorem dense_reflected_form_bound (base : Nat) (coefficient : Nat → Q') :
    let y := (centeredCubeVector base coefficient).val
    RCle (B (T y) y) (RCmul (Rq reflectedGapRate) (B y y)) :=
  sector_image_form_bound
    ⟨centeredSectorSource base coefficient, centeredSectorSource_mean_zero base coefficient⟩

/-- A strict common bound for EVERY vector of the actual completed reflected
vacuum complement. No analytic premise, chosen representative, or rate loss. -/
theorem completed_reflected_form_bound (x : CubeSectorVacuumComplement) :
    RCle (B (T x.val) x.val) (RCmul (Rq reflectedGapRate) (B x.val x.val)) :=
  completed_form_bound_of_dense reflectedGapRate
    (fun p => dense_reflected_form_bound p.base p.coefficient) x

end YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap

#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap.reflectedGapRate
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap.reflectedGapRate_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap.reflectedGapRate_lt_one
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap.reflected_pairing_eq_sector
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap.sector_image_form_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap.dense_reflected_form_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap.completed_reflected_form_bound
