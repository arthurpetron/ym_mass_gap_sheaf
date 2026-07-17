/-
# The eight explicit outward fine/coarse character cells

The remaining local character/fusion estimate is a universal statement over
the Boolean three-block pattern.  This module splits it constructively into
the eight literal cells.  The equivalence is useful both for independent
analytic attacks and for banking a checked counterexample to any proposed
uniform bound at a specific cell.
-/

import YMGap.Continuum.Z4OutwardFineCoarseLocalCharacterQuotient

namespace YMGap.Continuum.Z4OutwardFineCoarseLocalEightCells

set_option maxRecDepth 8000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.Z4OutwardFineCoarseCharacterNumeratorAdapter
open YMGap.Continuum.Z4OutwardFineCoarseLocalCharacterQuotient
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope

/-- One named Boolean cell of the exact local character/fusion estimate. -/
def OutwardFineCoarseLocalCellBound
    (fineCoupling bound : Q')
    (left shared right : Bool) : Prop :=
  absQ (outwardFineCoarseLocalCharacterCrossDifference
      fineCoupling (left, shared, right)) ≤
    bound * outwardFineCoarseLocalCharacterDenominator
      fineCoupling (left, shared, right)

theorem outwardFineCoarseLocalCrossDifferenceBound_iff_eightCells
    (fineCoupling bound : Q') :
    OutwardFineCoarseLocalCrossDifferenceBound fineCoupling bound ↔
      OutwardFineCoarseLocalCellBound
          fineCoupling bound false false false ∧
      OutwardFineCoarseLocalCellBound
          fineCoupling bound false false true ∧
      OutwardFineCoarseLocalCellBound
          fineCoupling bound false true false ∧
      OutwardFineCoarseLocalCellBound
          fineCoupling bound false true true ∧
      OutwardFineCoarseLocalCellBound
          fineCoupling bound true false false ∧
      OutwardFineCoarseLocalCellBound
          fineCoupling bound true false true ∧
      OutwardFineCoarseLocalCellBound
          fineCoupling bound true true false ∧
      OutwardFineCoarseLocalCellBound
          fineCoupling bound true true true := by
  constructor
  · intro h
    unfold OutwardFineCoarseLocalCrossDifferenceBound at h
    unfold OutwardFineCoarseLocalCellBound
    exact ⟨h (false, false, false),
      h (false, false, true),
      h (false, true, false),
      h (false, true, true),
      h (true, false, false),
      h (true, false, true),
      h (true, true, false),
      h (true, true, true)⟩
  · rintro ⟨h000, h001, h010, h011, h100, h101, h110, h111⟩
    unfold OutwardFineCoarseLocalCellBound at h000 h001 h010 h011 h100 h101 h110 h111
    unfold OutwardFineCoarseLocalCrossDifferenceBound
    intro pattern
    obtain ⟨left, ⟨shared, right⟩⟩ := pattern
    cases left <;> cases shared <;> cases right
    · exact h000
    · exact h001
    · exact h010
    · exact h011
    · exact h100
    · exact h101
    · exact h110
    · exact h111

theorem outwardFineCoarseLocalCrossDifferenceBound_of_eightCells
    (fineCoupling bound : Q')
    (h000 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false false false)
    (h001 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false false true)
    (h010 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false true false)
    (h011 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false true true)
    (h100 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true false false)
    (h101 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true false true)
    (h110 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true true false)
    (h111 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true true true) :
    OutwardFineCoarseLocalCrossDifferenceBound
      fineCoupling bound :=
  (outwardFineCoarseLocalCrossDifferenceBound_iff_eightCells
    fineCoupling bound).2
      ⟨h000, h001, h010, h011, h100, h101, h110, h111⟩

theorem outwardFineCoarseRetuneDefect_le_of_eightLocalCells
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling)
    (bound : Q')
    (h000 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false false false)
    (h001 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false false true)
    (h010 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false true false)
    (h011 : OutwardFineCoarseLocalCellBound
      fineCoupling bound false true true)
    (h100 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true false false)
    (h101 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true false true)
    (h110 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true true false)
    (h111 : OutwardFineCoarseLocalCellBound
      fineCoupling bound true true true) :
    threeBlockPatternRetuneDefect
        (outwardActivityMatchedCoarseSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw fineCoupling hfine)
        (outwardFineSubsupportLaw_patternMass_pos fineCoupling hfine) ≤
      bound :=
  outwardFineCoarseRetuneDefect_le_of_localCharacterCrossDifference
    fineCoupling hfine bound
    (outwardFineCoarseLocalCrossDifferenceBound_of_eightCells
      fineCoupling bound h000 h001 h010 h011 h100 h101 h110 h111)

#print axioms outwardFineCoarseLocalCrossDifferenceBound_iff_eightCells
#print axioms outwardFineCoarseLocalCrossDifferenceBound_of_eightCells
#print axioms outwardFineCoarseRetuneDefect_le_of_eightLocalCells

end YMGap.Continuum.Z4OutwardFineCoarseLocalEightCells
