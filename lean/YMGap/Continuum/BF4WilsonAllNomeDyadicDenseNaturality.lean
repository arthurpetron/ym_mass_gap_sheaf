/-
# Dense dyadic-square naturality across spatial widths

The original Wilson carrier already provides a proof-relevant inclusion of
intrinsic expressions when the spatial room is enlarged.  This module
specializes that inclusion to the geometrically scaled dyadic-square family:
the same source word, centered at zero, is transported coherently across
widths, and physical time commutes with the transport.

This is the dense/intrinsic half of a sheaf-style restriction square.  It does
not construct a map between the completed width-indexed Hilbert carriers,
identify different interacting actions, or prove a changing-width response
floor.  Those remain explicit analytic obligations.
-/

import YMGap.Continuum.BF4WilsonAllNomeLoopTimePin
import YMGap.Continuum.BF4DyadicWilsonSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicDenseNaturality

set_option autoImplicit false
set_option maxHeartbeats 3000000

open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
  (recenterLoop recenterLoop_comp)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
  (inclusion inclusion_refl inclusion_trans inclusion_advance)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4DyadicWilsonSquare

/-- The dense inclusion sends a literal loop state to the recentered loop
state, preserving its radius and ordered source word. -/
theorem inclusion_loopState {base larger : Nat} (h : base ≤ larger)
    (loop : SourceLoop base) :
    inclusion h (loopState loop) =
      loopState (recenterLoop (space := 0)
        (by simpa only [Nat.add_zero] using h) loop) := by
  rfl

/-- The dense inclusion sends a padded dyadic square at one width to the same
geometric square padded at a larger width.  This is the object component of
the dyadic restriction square. -/
theorem inclusion_paddedSquare_loopState
    {scale base larger : Nat} (hbase : side scale < base)
    (h : base ≤ larger) (hlarger : side scale < larger) :
    inclusion h (loopState (paddedSquare scale base hbase)) =
      loopState (paddedSquare scale larger hlarger) := by
  rw [inclusion_loopState]
  exact congrArg loopState (recenterLoop_comp
    (by simpa only [Nat.add_zero] using (Nat.le_of_lt hbase))
    (by simpa only [Nat.add_zero] using h)
    (square scale))

/-- The dyadic restriction square is functorial in width: two successive
inclusions agree with the direct inclusion. -/
theorem inclusion_paddedSquare_trans
    {scale base middle larger : Nat}
    (hbase : side scale < base) (h₁ : base ≤ middle)
    (h₂ : middle ≤ larger) :
    inclusion h₂ (inclusion h₁
      (loopState (paddedSquare scale base hbase))) =
      inclusion (Nat.le_trans h₁ h₂)
        (loopState (paddedSquare scale base hbase)) := by
  exact inclusion_trans h₁ h₂ (loopState (paddedSquare scale base hbase))

/-- Physical discrete time commutes with the dense dyadic width transport. -/
theorem inclusion_paddedSquare_advance
    {scale base larger : Nat} (hbase : side scale < base)
    (h : base ≤ larger) (n : Nat) :
    inclusion h (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance
      n (loopState (paddedSquare scale base hbase))) =
      YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance n
        (inclusion h (loopState (paddedSquare scale base hbase))) := by
  exact inclusion_advance h n (loopState (paddedSquare scale base hbase))

#print axioms inclusion_loopState
#print axioms inclusion_paddedSquare_loopState
#print axioms inclusion_paddedSquare_trans
#print axioms inclusion_paddedSquare_advance

end YMGap.Continuum.BF4WilsonAllNomeDyadicDenseNaturality
