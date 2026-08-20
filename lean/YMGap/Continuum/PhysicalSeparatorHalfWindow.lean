/-
M2f -- a simple constructive producer for the direct physical logarithm window.

The direct artanh implementation needs

  |(q - 1)/(q + 1)| <= 1/3.

For a physical separator `1/2 <= q < 1`, this is already the rational
negative-branch theorem proved in `HamiltonianAllSep`.  This file packages the
uniform lower bound `q_j >= 1/2` and turns it into `PhysicalLogWindow` data.

This is useful on an eventual near-continuum tail where `q_j -> 1`.  It is not
a proof that an arbitrary physical separator has such a tail, and it does not
replace the full binary logarithm range reduction for earlier scales.
-/

import YMGap.Continuum.PhysicalRateBridgeExactLog
import YMGap.Continuum.HamiltonianAllSep
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.PhysicalSeparatorHalfWindow

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.NonAbelianGapChain

/-- A physical separator which stays in the directly reducible half-window at
every indexed scale. -/
structure SeparatorHalfWindow (P : PhysicalSeparator) : Type where
  sep_ge_half : forall j : Nat, HalfPow.half <= P.sep j

namespace SeparatorHalfWindow

variable {P : PhysicalSeparator}

/-- The rational half bound in the cross-multiplied integer form consumed by
`HamiltonianAllSep.window_neg`. -/
theorem denominator_le_twice_numerator
    (H : SeparatorHalfWindow P) (j : Nat) :
    (P.sep j).den <= (P.sep j).num * 2 := by
  have h := H.sep_ge_half j
  unfold HalfPow.half at h
  change (1 : Int) * ((P.sep j).den : Int) <=
    (P.sep j).num * (2 : Int) at h
  simpa only [Int.one_mul] using h

/-- `q_j >= 1/2` and the defining `q_j < 1` property of a physical separator
produce the direct artanh window uniformly in `j`. -/
def toPhysicalLogWindow (H : SeparatorHalfWindow P) : PhysicalLogWindow P where
  inWindow := fun j =>
    window_neg (P.sep j) (separatorPlusOne_pos P j) (P.sep_lt_one j)
      (H.denominator_le_twice_numerator j)

end SeparatorHalfWindow

/-! ## The existing non-abelian bridge can now avoid a raw log-window field -/

/-- A non-abelian physical-rate bridge plus the simple uniform half bound gives
the complete exact logarithmic separator certificate. -/
def exactCertificateOfHalfWindow
    (B : PhysicalRateBridge)
    (H : SeparatorHalfWindow B.physicalSeparator) :
    ExactPhysicalSeparatorCertificate :=
  B.exactPhysicalSeparatorCertificate H.toPhysicalLogWindow

@[simp] theorem exactCertificateOfHalfWindow_floor
    (B : PhysicalRateBridge)
    (H : SeparatorHalfWindow B.physicalSeparator) :
    (exactCertificateOfHalfWindow B H).uniformBand.floor = B.floorConst :=
  rfl

@[simp] theorem exactCertificateOfHalfWindow_ceiling
    (B : PhysicalRateBridge)
    (H : SeparatorHalfWindow B.physicalSeparator) :
    (exactCertificateOfHalfWindow B H).uniformBand.ceiling =
      YMGap.Continuum.EffMassConvergence.c94 * B.ceilConst :=
  rfl

end YMGap.Continuum.PhysicalSeparatorHalfWindow

#print axioms YMGap.Continuum.PhysicalSeparatorHalfWindow.SeparatorHalfWindow.denominator_le_twice_numerator
#print axioms YMGap.Continuum.PhysicalSeparatorHalfWindow.SeparatorHalfWindow.toPhysicalLogWindow
#print axioms YMGap.Continuum.PhysicalSeparatorHalfWindow.exactCertificateOfHalfWindow
#print axioms YMGap.Continuum.PhysicalSeparatorHalfWindow.exactCertificateOfHalfWindow_floor
#print axioms YMGap.Continuum.PhysicalSeparatorHalfWindow.exactCertificateOfHalfWindow_ceiling
