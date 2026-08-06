/-
Track 11.7-fusion / R4af -- assemble the independently checked scale-four
half-time blocks.

Each imported block was normalized in a separate Lean process.  This module
contains no large computation: it joins their interval soundness theorems,
transports the resulting direct cells to the rational coefficient row, and
combines them with the already-proved head and macroscopic endpoint band.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeScaleFourCertificate18
import YMGap.Continuum.P2HalfTimeScaleFourCertificate34
import YMGap.Continuum.P2HalfTimeScaleFourCertificate50
import YMGap.Continuum.P2HalfTimeScaleFourCertificate66
import YMGap.Continuum.P2HalfTimeScaleFourCertificate82
import YMGap.Continuum.P2HalfTimeScaleFourCertificate98
import YMGap.Continuum.P2HalfTimeScaleFourCertificate114
import YMGap.Continuum.P2HalfTimeScaleFourCertificate130

namespace YMGap.Continuum.P2HalfTimeScaleFourComplete

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent
open YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2HalfTimeScaleFourCertificate
open YMGap.Continuum.P2RetunedParityStrandCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem scaleFour_coordinates :
    physicalWeightNum 4 = 3071 ∧
      physicalWeightDen 4 = 3072 ∧ blockNcut 4 = 79 := by
  decide

/-- Transport one proved Clebsch-box cell back to the genuine `p = 2`
bond-moved coefficient row.  Keeping this as an explicit setoid transport
avoids treating `Q'.eqv` as definitional equality. -/
private theorem coeffHalfTime_of_box
    {N s : Nat} {w : Q'}
    (hbox : boxTailLeft N w s <= halfTimeBoxRight N w s) :
    dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow w (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
  have eleft :
      dimQ s * bondMovedCoeff N w 2 (s + 1) ≈
        boxTailLeft N w s := by
    unfold boxTailLeft
    exact Q'.mul_eqv_congr_left _ _ _
      (bondMovedCoeff_eq_boxSum N (s + 1))
  have ebase :
      boxTailBase N w s ≈
        dimQ (s + 1) * bondMovedCoeff N w 2 s := by
    unfold boxTailBase
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (bondMovedCoeff_eq_boxSum N s))
  have eright :
      halfTimeBoxRight N w s ≈
        qpow w (s + 2) *
          (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
    unfold halfTimeBoxRight
    exact Q'.mul_eqv_congr_left _ _ _ ebase
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hbox (Q'.le_of_eqv eright))

/-- All direct cells below the symbolic endpoint cover at scale four. -/
theorem physicalHalfTimeScaleFourInteriorAt
    (s : Nat) (hs : 2 <= s) (hs' : s < 137) :
    halfTimeIntegralTailAt 3071 3072 79 s := by
  by_cases h18 : s < 18
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_2_17 hs h18
  by_cases h34 : s < 34
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_18_33 (by omega) h34
  by_cases h50 : s < 50
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_34_49 (by omega) h50
  by_cases h66 : s < 66
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_50_65 (by omega) h66
  by_cases h82 : s < 82
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_66_81 (by omega) h82
  by_cases h98 : s < 98
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_82_97 (by omega) h98
  by_cases h114 : s < 114
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_98_113 (by omega) h114
  by_cases h130 : s < 130
  · exact halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_114_129 (by omega) h130
  exact halfTimeIntegralTailBlockCheck_sound
    physicalHalfTimeScaleFourCheck_130_136 (by omega) (by omega)

/-- Rational half-time inequality on every scale-four cell below the
macroscopic endpoint band. -/
theorem physical_halfTime_scaleFour_interior
    (s : Nat) (hs : 2 <= s) (hs' : s < 137) :
    dimQ s * bondMovedCoeff (blockNcut 4) (blockWeight 4) 2 (s + 1) <=
      qpow (blockWeight 4) (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff
          (blockNcut 4) (blockWeight 4) 2 s) := by
  have hcell := physicalHalfTimeScaleFourInteriorAt s hs hs'
  have hcoords := scaleFour_coordinates
  rw [hcoords.2.2]
  exact halfTimeIntegralTailAt_sound 3071 3072 79 s (by decide)
    (blockWeight 4) (by simpa only [hcoords.1, hcoords.2.1] using
      blockWeight_eqv_closed 4) hcell

/-- The complete physical half-time row at `k=4`: the checked interior is
joined to the symbolic head and to the exact endpoint cover `s >= 137`. -/
theorem physical_halfTime_scaleFour
    (s : Nat) (hs : 1 <= s) (hsN : s < 2 * blockNcut 4) :
    dimQ s * bondMovedCoeff (blockNcut 4) (blockWeight 4) 2 (s + 1) <=
      qpow (blockWeight 4) (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff
          (blockNcut 4) (blockWeight 4) 2 s) := by
  by_cases h2 : 2 <= s
  · by_cases h137 : s < 137
    · exact physical_halfTime_scaleFour_interior s h2 h137
    · have hN : blockNcut 4 = 79 := by decide
      have hD : physicalWeightDen 4 = 3072 := by decide
      have hcover : physicalEndpointCoverAt 4 s := by
        unfold physicalEndpointCoverAt
        rw [hN, hD]
        constructor
        · omega
        · have hsCases :
              s = 137 ∨ s = 138 ∨ s = 139 ∨ s = 140 ∨
              s = 141 ∨ s = 142 ∨ s = 143 ∨ s = 144 ∨
              s = 145 ∨ s = 146 ∨ s = 147 ∨ s = 148 ∨
              s = 149 ∨ s = 150 ∨ s = 151 ∨ s = 152 ∨
              s = 153 ∨ s = 154 ∨ s = 155 ∨ s = 156 ∨
              s = 157 := by
            omega
          rcases hsCases with h | h | h | h | h | h | h | h | h | h |
            h | h | h | h | h | h | h | h | h | h | h <;>
            subst s <;> decide
      exact coeffHalfTime_of_box
        (physical_halfTime_box_of_endpointCoverAt
          4 s (by decide) hs hsN hcover)
  · have hs1 : s = 1 := by omega
    subst s
    exact coeffHalfTime_of_box
      (physical_halfTime_box_head_from_four 4 (by decide))

end YMGap.Continuum.P2HalfTimeScaleFourComplete

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeScaleFourComplete.physicalHalfTimeScaleFourInteriorAt
#print axioms YMGap.Continuum.P2HalfTimeScaleFourComplete.physical_halfTime_scaleFour_interior
#print axioms YMGap.Continuum.P2HalfTimeScaleFourComplete.physical_halfTime_scaleFour
