/-
# Dense branch natural transformation: width inclusion versus discrete time

The checked width inclusion is covariant: enlarging the intrinsic source box
maps a dense expression into the larger-width dense carrier.  Therefore the
honest categorical object at this stage is a scale diagram (a cosheaf-style
diagram), not a presheaf on completed Hilbert spaces.  This module packages
that diagram and the actual discrete-time advance as a natural transformation.

The source diagram is the dense observable/nontriviality side.  The target
diagram has the same dense carrier and width maps, but its object component is
the physically advanced expression used by the transfer/gap side.  Naturality
is exactly the kernel-checked identity that width inclusion commutes with time
advance.  No map between different completed carriers, no interacting-action
comparison, and no continuum or Clay conclusion is introduced here.
-/

import YMGap.Categorical.Core
import YMGap.Categorical.ScaleSheaf
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4WilsonAllNomeDyadicDenseNaturality

namespace YMGap.Continuum.BF4WilsonAllNomeDenseTimeNaturalTransformation

set_option autoImplicit false
set_option maxHeartbeats 3000000

open YMGap.Categorical
open YMGap.Categorical.ScaleSheaf
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
  (inclusion inclusion_refl inclusion_trans inclusion_advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)

/-! ## The two scale diagrams -/

/-- The dense observable/nontriviality diagram: a width carries its intrinsic
Wilson expressions, and a refinement carries the proved zero-spatial inclusion.
This is covariant in the width order because the available map enlarges the
source box. -/
def denseObservableDiagram : Functor ScaleCat TypeCat where
  obj := fun width => IntrinsicExpression width
  map := fun {base larger} f => inclusion f.down
  map_id := fun width => by
    funext x
    exact inclusion_refl x
  map_comp := fun {base middle larger} f g => by
    funext x
    exact (inclusion_trans f.down g.down x).symm

/-- The dense transfer/gap diagram.  It has the same width carriers and
restriction maps; the time shift is supplied by the transformation component
below.  Keeping the diagram itself independent of `n` makes the branch
interface explicit: width transport is one functorial layer, while physical
time is a separate natural-transformation layer. -/
def denseTransferDiagram : Functor ScaleCat TypeCat where
  obj := fun width => IntrinsicExpression width
  map := fun {base larger} f => inclusion f.down
  map_id := fun width => by
    funext x
    exact inclusion_refl x
  map_comp := fun {base middle larger} f g => by
    funext x
    exact (inclusion_trans f.down g.down x).symm

/-! ## The branch-to-branch natural transformation -/

/-- Discrete physical time is a natural transformation from the dense
observable branch to the dense transfer/gap branch.  Its component at width
`width` is the actual intrinsic `advance n`, not an abstract identity. -/
def denseTimeNaturalTransformation (n : Nat) :
    NatTrans denseObservableDiagram denseTransferDiagram where
  app := fun _ => advance n
  naturality := fun {base larger} f => by
    funext x
    exact (inclusion_advance f.down n x).symm

/-- The naturality square evaluated on any dense expression: advancing first
or enlarging the width first gives the same intrinsic expression. -/
theorem denseTime_naturality {base larger : Nat} (h : base ≤ larger)
    (n : Nat) (x : IntrinsicExpression base) :
    advance n (inclusion h x) = inclusion h (advance n x) := by
  exact (inclusion_advance h n x).symm

/-! ## Dyadic-square specialization -/

open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)

/-- The component/naturality square is the dyadic-square branch square used by
the nontriviality and transfer/gap constructions. -/
theorem denseTime_naturality_paddedSquare
    {scale base larger : Nat} (hbase : side scale < base)
    (h : base ≤ larger) (n : Nat) :
    advance n (inclusion h (loopState (paddedSquare scale base hbase))) =
      inclusion h (advance n (loopState (paddedSquare scale base hbase))) := by
  exact denseTime_naturality h n (loopState (paddedSquare scale base hbase))

#print axioms denseObservableDiagram
#print axioms denseTransferDiagram
#print axioms denseTimeNaturalTransformation
#print axioms denseTime_naturality
#print axioms denseTime_naturality_paddedSquare

end YMGap.Continuum.BF4WilsonAllNomeDenseTimeNaturalTransformation
