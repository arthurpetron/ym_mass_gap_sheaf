/-
# Dense branches into one completed spatial-union carrier

The fixed-width Wilson completions do not yet have maps between different
widths.  The spatial-union construction supplies the correct common carrier:
its staged syntax identifies a finite expression with the same completed class
at every larger support base.  Restricting the scale site to positive widths
therefore gives a genuine natural transformation from the dense observable
diagram to the constant spatial-union completion.

The second transformation sends the same dense observable to its physically
time-advanced union-completion class.  The two transformations are related by
the existing completed-time intertwining theorem.  This is a concrete
sheaf/cosheaf-style branch join.  It does not identify the union completion
with the canonical OS/GNS completion, prove a uniform changing-spacing gap, or
construct the continuum Clay theory.
-/

import YMGap.Categorical.Core
import YMGap.Categorical.ScaleSheaf
import YMGap.Continuum.BF4WilsonSpatialUnion
import YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
import YMGap.Continuum.BF4WilsonChronologicalBaseCoherence
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
import YMGap.Continuum.FiniteSizeGeometricSum
import YMGap.Continuum.QuaternionHaarCharacterInterval

namespace YMGap.Continuum.BF4WilsonSpatialUnionNaturalTransformation

set_option autoImplicit false
set_option maxHeartbeats 3000000

open YMGap.Categorical
open YMGap.Categorical.ScaleSheaf
open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
  (inclusion inclusion_refl inclusion_trans)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance)
open YMGap.Continuum.BF4WilsonSpatialUnion
  (Stage ofExpression atBase time atBase_time)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
  (UnionCompletion embedStage completedTime completedTime_embedStage)
open YMGap.Continuum.BF4WilsonChronologicalBaseCoherence
  (embedStage_atBase)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs

/-! ## Positive-width scale diagram and common completed target -/

/-- The dense observable branch on positive widths.  The object `n` denotes
the intrinsic carrier at width `n+1`, and a scale refinement uses the proved
zero-spatial inclusion. -/
def positiveDenseDiagram : Functor ScaleCat TypeCat where
  obj := fun n => IntrinsicExpression (Nat.succ n)
  map := fun {n m} f => inclusion (Nat.succ_le_succ f.down)
  map_id := fun n => by
    funext x
    change inclusion (Nat.succ_le_succ (Nat.le_refl n)) x = x
    exact inclusion_refl x
  map_comp := fun {n m k} f g => by
    funext x
    exact (inclusion_trans (Nat.succ_le_succ f.down)
      (Nat.succ_le_succ g.down) x).symm

/-- The constant target diagram with value the one common spatial-union
completion.  Its morphisms are identity maps because base changes have
already been quotiented by `embedStage_atBase`. -/
def unionCompletionDiagram : Functor ScaleCat TypeCat where
  obj := fun _ => V
  map := fun _ => fun x => x
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ## The completed cross-width natural transformation -/

/-- Every positive-width dense observable has a canonical class in the SAME
spatial-union completion, naturally in width. -/
def denseToUnion : NatTrans
    positiveDenseDiagram
    (unionCompletionDiagram hw0 hw1 hsmall hd hs) where
  app := fun n => fun x =>
    embedStage hw0 hw1 hsmall hd hs
      (ofExpression (Nat.succ n) (Nat.succ_pos n) x)
  naturality := fun {n m} f => by
    funext x
    change
      embedStage hw0 hw1 hsmall hd hs
        (ofExpression (Nat.succ m) (Nat.succ_pos m)
          (inclusion (Nat.succ_le_succ f.down) x)) =
      embedStage hw0 hw1 hsmall hd hs
        (ofExpression (Nat.succ n) (Nat.succ_pos n) x)
    have h := embedStage_atBase hw0 hw1 hsmall hd hs
      (ofExpression (Nat.succ n) (Nat.succ_pos n) x)
      (Nat.succ_le_succ f.down)
    simpa only [atBase, ofExpression] using h.symm

/-- The same dense source, read after a fixed physical-time advance, lands in
the common union completion. -/
def denseTimeToUnion (lag : Nat) : NatTrans
    positiveDenseDiagram
    (unionCompletionDiagram hw0 hw1 hsmall hd hs) where
  app := fun n => fun x =>
    embedStage hw0 hw1 hsmall hd hs
      (time lag (ofExpression (Nat.succ n) (Nat.succ_pos n) x))
  naturality := fun {n m} f => by
    funext x
    change
      embedStage hw0 hw1 hsmall hd hs
        (time lag (ofExpression (Nat.succ m) (Nat.succ_pos m)
          (inclusion (Nat.succ_le_succ f.down) x))) =
      embedStage hw0 hw1 hsmall hd hs
        (time lag (ofExpression (Nat.succ n) (Nat.succ_pos n) x))
    have h := embedStage_atBase hw0 hw1 hsmall hd hs
      (time lag (ofExpression (Nat.succ n) (Nat.succ_pos n) x))
      (Nat.succ_le_succ f.down)
    rw [atBase_time] at h
    simpa only [atBase, time, ofExpression] using h.symm

/-- The completed union time map intertwines the unadvanced and advanced
components of the two branch transformations. -/
theorem completedTime_denseToUnion (lag n : Nat)
    (x : IntrinsicExpression (Nat.succ n)) :
    completedTime hw0 hw1 hsmall hd hs lag
      ((denseToUnion hw0 hw1 hsmall hd hs).app n x) =
      (denseTimeToUnion hw0 hw1 hsmall hd hs lag).app n x := by
  change completedTime hw0 hw1 hsmall hd hs lag
      (embedStage hw0 hw1 hsmall hd hs
        (ofExpression (Nat.succ n) (Nat.succ_pos n) x)) =
    embedStage hw0 hw1 hsmall hd hs
      (time lag (ofExpression (Nat.succ n) (Nat.succ_pos n) x))
  exact completedTime_embedStage hw0 hw1 hsmall hd hs lag
    (ofExpression (Nat.succ n) (Nat.succ_pos n) x)

#print axioms positiveDenseDiagram
#print axioms unionCompletionDiagram
#print axioms denseToUnion
#print axioms denseTimeToUnion
#print axioms completedTime_denseToUnion

end YMGap.Continuum.BF4WilsonSpatialUnionNaturalTransformation
