/-
# Spatial swap of the ORIGINAL roots and witnessed time sector

The checked completed spatial swap commutes with every finite polynomial
in the actual time defect. The existing represented root limits then give
commutation at every supplied fixed depth, using their original convergence
rates and uniqueness, not a new root or functional-calculus assumption.

Each original time-range witness is transported by mapping its supplied
preimages and retaining its modulus verbatim. The resulting state preserves
the underlying pairing, distance and time action. The literal dense bond
image is identified through the already constructed first root.

All statements concern one spatial permutation at fixed width and nome.
No bond-completion map, uniform root-depth modulus, continuous rotation,
continuum covariance, scaling estimate or physical mass gap is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion
import YMGap.Continuum.BF4WilsonAllNomeBondOSRealization

namespace YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly (Poly)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedSmul completedSub completedZero)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect defectPower)
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial (actionFrom action)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root finiteRoot)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
  (rootRows rootRows_point limit_rootRows)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (limit limitRate limit_bound limit_unique)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image)
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm (swapIntrinsic)
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra (swapNonexpansive)
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "U" => completedSwap hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "B" => completedInner hw0 hw1
local notation "S" => swapNonexpansive hw0 hw1 (width := width)
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem completedSwap_defect (x : V) :
    U (defect hw0 hw1 x) = defect hw0 hw1 (U x) := by
  unfold defect
  rw [completedSwap_sub, completedSwap_time]

theorem completedSwap_defectPower (n : Nat) (x : V) :
    U (defectPower hw0 hw1 n x) = defectPower hw0 hw1 n (U x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change U (defect hw0 hw1 (defectPower hw0 hw1 n x)) =
        defect hw0 hw1 (defectPower hw0 hw1 n (U x))
      rw [completedSwap_defect, ih]

/-- Every actual finite signed coefficient list; no coefficient positivity
or abstract functional calculus is needed for this equality. -/
theorem completedSwap_actionFrom (p : Poly) (i : Nat) (x : V) :
    U (actionFrom hw0 hw1 p i x) = actionFrom hw0 hw1 p i (U x) := by
  induction p generalizing i with
  | nil => exact completedSwap_zero hw0 hw1
  | cons c p ih =>
      change U (completedAdd hw0 hw1
          (completedSmul hw0 hw1 c (defectPower hw0 hw1 i x))
          (actionFrom hw0 hw1 p (i+1) x)) =
        completedAdd hw0 hw1
          (completedSmul hw0 hw1 c (defectPower hw0 hw1 i (U x)))
          (actionFrom hw0 hw1 p (i+1) (U x))
      rw [completedSwap_add, completedSwap_smul, completedSwap_defectPower, ih]

theorem completedSwap_action (p : Poly) (x : V) :
    U (action hw0 hw1 p x) = action hw0 hw1 p (U x) :=
  completedSwap_actionFrom hw0 hw1 p 0 x

theorem completedSwap_finiteRoot (k n : Nat) (x : V) :
    U (finiteRoot hw0 hw1 k n x) = finiteRoot hw0 hw1 k n (U x) := by
  unfold finiteRoot
  exact completedSwap_action hw0 hw1 _ x

/-- Pass the exact finite polynomial identity through the SAME represented
root limit. Its original rate is supplied to uniqueness independently of
the mapped input's root-row modulus, so no modulus equality is assumed. -/
theorem completedSwap_root (k : Nat) (x : V) :
    U (root hw0 hw1 k x) = root hw0 hw1 k (U x) := by
  refine Quotient.inductionOn x ?_
  intro X
  let Y : (D).Cauchy := (S).mapCauchy X
  have hY : Class Y = U (Class X) := rfl
  have h : limit hw0 hw1 (rootRows hw0 hw1 k Y) = U (root hw0 hw1 k (Class X)) := by
    apply limit_unique hw0 hw1 (rootRows hw0 hw1 k Y)
      (U (root hw0 hw1 k (Class X)))
      (limitRate hw0 hw1 (rootRows hw0 hw1 k X))
    intro epsilon he n hn
    rw [rootRows_point, hY, ← completedSwap_finiteRoot, completedDist_swap]
    simpa only [rootRows_point, limit_rootRows] using
      limit_bound hw0 hw1 (rootRows hw0 hw1 k X) epsilon he n hn
  rw [limit_rootRows, hY] at h
  exact h.symm

/-- Concrete original preimages, with the existing all-tail modulus retained.
No inverse of the original transfer or representative selection is used. -/
def swapRange {x : V} (R : RangeLimit hw0 hw1 x) : RangeLimit hw0 hw1 (U x) where
  preimage := fun n => (S).mapCauchy (R.preimage n)
  modulus := R.modulus
  bound := by
    intro epsilon he n hn
    change RCle (dist (T 1 (U (Class (R.preimage n)))) (U x)) (rat epsilon)
    rw [← completedSwap_time, completedDist_swap]
    exact R.bound epsilon he n hn

theorem swapRange_modulus {x : V} (R : RangeLimit hw0 hw1 x) :
    (swapRange hw0 hw1 R).modulus = R.modulus := rfl

/-- The original `State` type retains the transported Type-valued witness. -/
def swapState (x : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) where
  val := U x.val
  range := swapRange hw0 hw1 x.range

theorem swapState_val (x : State hw0 hw1 (width := width)) :
    (swapState hw0 hw1 x).val = U x.val := rfl

theorem swapState_distance (x y : State hw0 hw1 (width := width)) :
    dist (swapState hw0 hw1 x).val (swapState hw0 hw1 y).val = dist x.val y.val :=
  completedDist_swap hw0 hw1 x.val y.val

theorem swapState_inner (x y : State hw0 hw1 (width := width)) :
    B (swapState hw0 hw1 x).val (swapState hw0 hw1 y).val = B x.val y.val :=
  completedInner_swap hw0 hw1 x.val y.val

/-- Equality of underlying vectors, not equality of arbitrary stored range
certificates. This is precisely the existing `stateSetoid` relation. -/
theorem swapState_involutive_val (x : State hw0 hw1 (width := width)) :
    (swapState hw0 hw1 (swapState hw0 hw1 x)).val = x.val :=
  completedSwap_involutive hw0 hw1 x.val

theorem swapState_time (n : Nat) (x : State hw0 hw1 (width := width)) :
    U (T n x.val) = T n (swapState hw0 hw1 x).val :=
  completedSwap_time hw0 hw1 n x.val

/-- Actual original one-step images are transported to actual one-step
images of the mapped supplied representative. -/
theorem swapState_fromTime_val (X : (D).Cauchy) :
    (swapState hw0 hw1 (BF4WilsonAllNomeTimeSector.fromTime hw0 hw1 X)).val =
      (BF4WilsonAllNomeTimeSector.fromTime hw0 hw1 ((S).mapCauchy X)).val :=
  completedSwap_time hw0 hw1 1 (Class X)

/-- The literal dense physical bond image uses the SAME constructed first
root and SAME original source embedding on both sides. -/
theorem image_swap_pin (x : IntrinsicExpression width) :
    (image hw0 hw1 (swapIntrinsic x)).val = U (image hw0 hw1 x).val := by
  change root hw0 hw1 1 (embed hw0 hw1 (swapIntrinsic x)) =
    U (root hw0 hw1 1 (embed hw0 hw1 x))
  rw [← completedSwap_embed]
  exact (completedSwap_root hw0 hw1 1 (embed hw0 hw1 x)).symm

end YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector

#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.completedSwap_defect
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.completedSwap_defectPower
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.completedSwap_actionFrom
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.completedSwap_action
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.completedSwap_finiteRoot
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.completedSwap_root
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapRange
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapRange_modulus
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapState
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapState_val
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapState_distance
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapState_inner
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapState_involutive_val
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapState_time
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.swapState_fromTime_val
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapTimeSector.image_swap_pin
