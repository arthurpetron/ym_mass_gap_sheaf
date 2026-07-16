/-
# Structural closure of the measure-eight Omega-correction shell

The first two positive-order shells, of measures six and seven, are exact
parity anchors for the label-lowering transports.  This file isolates the
general coordinate partition which is independent of the shell size, then
classifies measure eight.  Only the coordinate-zero and genuinely higher
inner-support remainder is left to closed exact evaluation.
-/

import YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell
import YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily

namespace YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahMeasureSevenCorrectionShell
open YMGap.Continuum.SU2OrderedRacahMutualMeasureInvariant
open YMGap.Continuum.SU2OrderedRacahMutualMeasurePhysicalBoundary
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure
open YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily

/-! ## Shell-independent coordinate partition -/

/-- For every adjacent positive-order block, only two regions remain after
the established support and Hahn calculations: a coordinate-zero face, or
the common output shell strictly above the first bulk `j+l=p`.  This is the
structural completion mechanism used below; finite evaluation is confined to
the two explicitly stated remainders. -/
theorem omegaCorrectionPhysical_of_boundary_and_highShell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (hboundary : ∀ i j l s,
      i < a + 1 → j < b + 1 → l < c + 1 → s < d + 1 →
      (i = 0 ∨ j = 0 ∨ l = 0) →
      OmegaCorrectionThreeCarrierAt qm q qp i j l s)
    (hhigh : ∀ i j l s,
      i < a + 1 → j < b + 1 → l < c + 1 → s < d + 1 →
      0 < i → 0 < j → 0 < l →
      s + q.r + q.p = i + j + l → q.p < j + l →
      OmegaCorrectionThreeCarrierAt qm q qp i j l s) :
    OmegaCorrectionPhysicalCoordinateFamily qm q qp := by
  intro i j l s hi hj hl hs
  by_cases hi0 : i = 0
  · exact hboundary i j l s hi hj hl hs (Or.inl hi0)
  by_cases hj0 : j = 0
  · exact hboundary i j l s hi hj hl hs (Or.inr (Or.inl hj0))
  by_cases hl0 : l = 0
  · exact hboundary i j l s hi hj hl hs (Or.inr (Or.inr hl0))
  have hip : 0 < i := by omega
  have hjp : 0 < j := by omega
  have hlp : 0 < l := by omega
  by_cases hbelow : j + l < qm.p
  · exact omegaCorrectionThreeCarrier_below_lower_support
      qm q qp hp hprev hnext i j l s hbelow
  by_cases hshell : s + q.r + q.p = i + j + l
  · by_cases hlower : j + l = qm.p
    · exact omegaCorrectionThreeCarrierAt_lower_boundary_on_shell
        qm q qp hp hprev hnext i j l s hip hjp hlp hshell hlower
    by_cases hfirst : j + l = q.p
    · have hqp := Nat.le_min.mp qp.p_le
      exact omegaCorrectionThreeCarrierAt_first_bulk_outer_closed_on_shell
        qm q qp hp hprev hnext i j l s hip hjp hlp hshell hfirst
          (by omega) (by omega) (by omega) (by omega)
    · exact hhigh i j l s hi hj hl hs hip hjp hlp hshell (by omega)
  · exact omegaCorrectionThreeCarrierAt_off_total_shell
      qm q qp hp hprev hnext i j l s hip hjp hlp hshell

/-! ## The first measure-eight block -/

def measureEight2244Lower : FixedRightCGChannel 2 2 4 4 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight2244Middle : FixedRightCGChannel 2 2 4 4 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight2244Upper : FixedRightCGChannel 2 2 4 4 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureEight2334Lower : FixedRightCGChannel 2 3 3 4 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight2334Middle : FixedRightCGChannel 2 3 3 4 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight2334Upper : FixedRightCGChannel 2 3 3 4 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureEight2332Lower : FixedRightCGChannel 2 3 3 2 where
  p := 1
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight2332Middle : FixedRightCGChannel 2 3 3 2 where
  p := 2
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight2332Upper : FixedRightCGChannel 2 3 3 2 where
  p := 3
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureEight2424Lower : FixedRightCGChannel 2 4 2 4 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight2424Middle : FixedRightCGChannel 2 4 2 4 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight2424Upper : FixedRightCGChannel 2 4 2 4 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureEight3234Lower : FixedRightCGChannel 3 2 3 4 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight3234Middle : FixedRightCGChannel 3 2 3 4 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight3234Upper : FixedRightCGChannel 3 2 3 4 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureEight3232Lower : FixedRightCGChannel 3 2 3 2 where
  p := 0
  p_le := by omega
  r := 3
  r_le := by omega
  degree_eq := by omega

def measureEight3232Middle : FixedRightCGChannel 3 2 3 2 where
  p := 1
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight3232Upper : FixedRightCGChannel 3 2 3 2 where
  p := 2
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight3324Lower : FixedRightCGChannel 3 3 2 4 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight3324Middle : FixedRightCGChannel 3 3 2 4 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight3324Upper : FixedRightCGChannel 3 3 2 4 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

def measureEight3322Lower : FixedRightCGChannel 3 3 2 2 where
  p := 0
  p_le := by omega
  r := 3
  r_le := by omega
  degree_eq := by omega

def measureEight3322Middle : FixedRightCGChannel 3 3 2 2 where
  p := 1
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight3322Upper : FixedRightCGChannel 3 3 2 2 where
  p := 2
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight4224Lower : FixedRightCGChannel 4 2 2 4 where
  p := 0
  p_le := by omega
  r := 2
  r_le := by omega
  degree_eq := by omega

def measureEight4224Middle : FixedRightCGChannel 4 2 2 4 where
  p := 1
  p_le := by omega
  r := 1
  r_le := by omega
  degree_eq := by omega

def measureEight4224Upper : FixedRightCGChannel 4 2 2 4 where
  p := 2
  p_le := by omega
  r := 0
  r_le := by omega
  degree_eq := by omega

private theorem nat_lt_three_cases (n : Nat) (h : n < 3) :
    n = 0 ∨ n = 1 ∨ n = 2 := by omega

private theorem nat_lt_four_cases (n : Nat) (h : n < 4) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega

private theorem nat_lt_five_cases (n : Nat) (h : n < 5) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega

private theorem measureEight2244_exceptional :
    ∀ i j l s, i < 3 → j < 3 → l < 5 → s < 5 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight2244Middle.r + measureEight2244Middle.p =
            i + j + l ∧ measureEight2244Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight2244Lower
        measureEight2244Middle measureEight2244Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_three_cases i hi
  have hj' := nat_lt_three_cases j hj
  have hl' := nat_lt_five_cases l hl
  have hs' := nat_lt_five_cases s hs
  rcases hi' with rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight2244Lower
        measureEight2244Middle measureEight2244Upper; decide)

theorem measureEight2244_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight2244Lower
      measureEight2244Middle measureEight2244Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight2244Lower measureEight2244Middle measureEight2244Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight2244_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight2244_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

/-! ## The remaining eight blocks -/

private theorem measureEight2334_exceptional :
    ∀ i j l s, i < 3 → j < 4 → l < 4 → s < 5 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight2334Middle.r + measureEight2334Middle.p =
            i + j + l ∧ measureEight2334Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight2334Lower
        measureEight2334Middle measureEight2334Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_three_cases i hi
  have hj' := nat_lt_four_cases j hj
  have hl' := nat_lt_four_cases l hl
  have hs' := nat_lt_five_cases s hs
  rcases hi' with rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight2334Lower
        measureEight2334Middle measureEight2334Upper; decide)

theorem measureEight2334_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight2334Lower
      measureEight2334Middle measureEight2334Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight2334Lower measureEight2334Middle measureEight2334Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight2334_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight2334_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

private theorem measureEight2332_exceptional :
    ∀ i j l s, i < 3 → j < 4 → l < 4 → s < 3 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight2332Middle.r + measureEight2332Middle.p =
            i + j + l ∧ measureEight2332Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight2332Lower
        measureEight2332Middle measureEight2332Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_three_cases i hi
  have hj' := nat_lt_four_cases j hj
  have hl' := nat_lt_four_cases l hl
  have hs' := nat_lt_three_cases s hs
  rcases hi' with rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight2332Lower
        measureEight2332Middle measureEight2332Upper; decide)

theorem measureEight2332_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight2332Lower
      measureEight2332Middle measureEight2332Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight2332Lower measureEight2332Middle measureEight2332Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight2332_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight2332_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

private theorem measureEight2424_exceptional :
    ∀ i j l s, i < 3 → j < 5 → l < 3 → s < 5 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight2424Middle.r + measureEight2424Middle.p =
            i + j + l ∧ measureEight2424Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight2424Lower
        measureEight2424Middle measureEight2424Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_three_cases i hi
  have hj' := nat_lt_five_cases j hj
  have hl' := nat_lt_three_cases l hl
  have hs' := nat_lt_five_cases s hs
  rcases hi' with rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight2424Lower
        measureEight2424Middle measureEight2424Upper; decide)

theorem measureEight2424_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight2424Lower
      measureEight2424Middle measureEight2424Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight2424Lower measureEight2424Middle measureEight2424Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight2424_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight2424_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

private theorem measureEight3234_exceptional :
    ∀ i j l s, i < 4 → j < 3 → l < 4 → s < 5 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight3234Middle.r + measureEight3234Middle.p =
            i + j + l ∧ measureEight3234Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight3234Lower
        measureEight3234Middle measureEight3234Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_four_cases i hi
  have hj' := nat_lt_three_cases j hj
  have hl' := nat_lt_four_cases l hl
  have hs' := nat_lt_five_cases s hs
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight3234Lower
        measureEight3234Middle measureEight3234Upper; decide)

theorem measureEight3234_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight3234Lower
      measureEight3234Middle measureEight3234Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight3234Lower measureEight3234Middle measureEight3234Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight3234_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight3234_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

private theorem measureEight3232_exceptional :
    ∀ i j l s, i < 4 → j < 3 → l < 4 → s < 3 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight3232Middle.r + measureEight3232Middle.p =
            i + j + l ∧ measureEight3232Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight3232Lower
        measureEight3232Middle measureEight3232Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_four_cases i hi
  have hj' := nat_lt_three_cases j hj
  have hl' := nat_lt_four_cases l hl
  have hs' := nat_lt_three_cases s hs
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight3232Lower
        measureEight3232Middle measureEight3232Upper; decide)

theorem measureEight3232_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight3232Lower
      measureEight3232Middle measureEight3232Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight3232Lower measureEight3232Middle measureEight3232Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight3232_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight3232_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

private theorem measureEight3324_exceptional :
    ∀ i j l s, i < 4 → j < 4 → l < 3 → s < 5 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight3324Middle.r + measureEight3324Middle.p =
            i + j + l ∧ measureEight3324Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight3324Lower
        measureEight3324Middle measureEight3324Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_four_cases i hi
  have hj' := nat_lt_four_cases j hj
  have hl' := nat_lt_three_cases l hl
  have hs' := nat_lt_five_cases s hs
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight3324Lower
        measureEight3324Middle measureEight3324Upper; decide)

theorem measureEight3324_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight3324Lower
      measureEight3324Middle measureEight3324Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight3324Lower measureEight3324Middle measureEight3324Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight3324_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight3324_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

private theorem measureEight3322_exceptional :
    ∀ i j l s, i < 4 → j < 4 → l < 3 → s < 3 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight3322Middle.r + measureEight3322Middle.p =
            i + j + l ∧ measureEight3322Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight3322Lower
        measureEight3322Middle measureEight3322Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_four_cases i hi
  have hj' := nat_lt_four_cases j hj
  have hl' := nat_lt_three_cases l hl
  have hs' := nat_lt_three_cases s hs
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight3322Lower
        measureEight3322Middle measureEight3322Upper; decide)

theorem measureEight3322_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight3322Lower
      measureEight3322Middle measureEight3322Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight3322Lower measureEight3322Middle measureEight3322Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight3322_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight3322_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

private theorem measureEight4224_exceptional :
    ∀ i j l s, i < 5 → j < 3 → l < 3 → s < 5 →
      ((i = 0 ∨ j = 0 ∨ l = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < l ∧
          s + measureEight4224Middle.r + measureEight4224Middle.p =
            i + j + l ∧ measureEight4224Middle.p < j + l)) →
      OmegaCorrectionThreeCarrierAt measureEight4224Lower
        measureEight4224Middle measureEight4224Upper i j l s := by
  intro i j l s hi hj hl hs hexceptional
  have hi' := nat_lt_five_cases i hi
  have hj' := nat_lt_three_cases j hj
  have hl' := nat_lt_three_cases l hl
  have hs' := nat_lt_five_cases s hs
  rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl <;>
    rcases hl' with rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; omega)
    | (unfold OmegaCorrectionThreeCarrierAt measureEight4224Lower
        measureEight4224Middle measureEight4224Upper; decide)

theorem measureEight4224_correctionPhysical :
    OmegaCorrectionPhysicalCoordinateFamily measureEight4224Lower
      measureEight4224Middle measureEight4224Upper :=
  omegaCorrectionPhysical_of_boundary_and_highShell
    measureEight4224Lower measureEight4224Middle measureEight4224Upper
    (by decide) rfl rfl
    (fun i j l s hi hj hl hs hzero =>
      measureEight4224_exceptional i j l s hi hj hl hs (Or.inl hzero))
    (fun i j l s hi hj hl hs hip hjp hlp hshell hhigh =>
      measureEight4224_exceptional i j l s hi hj hl hs
        (Or.inr ⟨hip, hjp, hlp, hshell, hhigh⟩))

/-! ## Constructive exhaustion and the first two-step pattern -/

/-- A constructor-valued classification avoids extracting witnesses from a
large propositional disjunction.  The nine constructors are exactly the
measure-eight adjacent positive-order blocks. -/
inductive MeasureEightAdjacentRegime {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) : Prop where
  | r2244 : a = 2 → b = 2 → c = 4 → d = 4 → q.p = 1 → q.r = 1 →
      MeasureEightAdjacentRegime qm q qp
  | r2334 : a = 2 → b = 3 → c = 3 → d = 4 → q.p = 1 → q.r = 1 →
      MeasureEightAdjacentRegime qm q qp
  | r2332 : a = 2 → b = 3 → c = 3 → d = 2 → q.p = 2 → q.r = 1 →
      MeasureEightAdjacentRegime qm q qp
  | r2424 : a = 2 → b = 4 → c = 2 → d = 4 → q.p = 1 → q.r = 1 →
      MeasureEightAdjacentRegime qm q qp
  | r3234 : a = 3 → b = 2 → c = 3 → d = 4 → q.p = 1 → q.r = 1 →
      MeasureEightAdjacentRegime qm q qp
  | r3232 : a = 3 → b = 2 → c = 3 → d = 2 → q.p = 1 → q.r = 2 →
      MeasureEightAdjacentRegime qm q qp
  | r3324 : a = 3 → b = 3 → c = 2 → d = 4 → q.p = 1 → q.r = 1 →
      MeasureEightAdjacentRegime qm q qp
  | r3322 : a = 3 → b = 3 → c = 2 → d = 2 → q.p = 1 → q.r = 2 →
      MeasureEightAdjacentRegime qm q qp
  | r4224 : a = 4 → b = 2 → c = 2 → d = 4 → q.p = 1 → q.r = 1 →
      MeasureEightAdjacentRegime qm q qp

/-- Channel admissibility constructively exhausts the measure-eight shell. -/
theorem measureEight_adjacent_classification {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = 8)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    MeasureEightAdjacentRegime qm q qp := by
  have hqmP := Nat.le_min.mp qm.p_le
  have hqP := Nat.le_min.mp q.p_le
  have hqpP := Nat.le_min.mp qp.p_le
  have hqmR := Nat.le_min.mp qm.r_le
  have hqR := Nat.le_min.mp q.r_le
  have hqpR := Nat.le_min.mp qp.r_le
  have hqmD := qm.degree_eq
  have hqD := q.degree_eq
  have hqpD := qp.degree_eq
  unfold rightLabelMeasure at hmeasure
  have ha : 2 ≤ a := by omega
  have hb : 2 ≤ b := by omega
  have hc : 2 ≤ c := by omega
  by_cases ha2 : a = 2
  · by_cases hb2 : b = 2
    · exact .r2244 ha2 hb2 (by omega) (by omega) (by omega) (by omega)
    · by_cases hb3 : b = 3
      · by_cases hp1 : q.p = 1
        · exact .r2334 ha2 hb3 (by omega) (by omega) hp1 (by omega)
        · exact .r2332 ha2 hb3 (by omega) (by omega) (by omega) (by omega)
      · exact .r2424 ha2 (by omega) (by omega) (by omega) (by omega) (by omega)
  · by_cases ha3 : a = 3
    · by_cases hb2 : b = 2
      · by_cases hr1 : q.r = 1
        · exact .r3234 ha3 hb2 (by omega) (by omega) (by omega) hr1
        · exact .r3232 ha3 hb2 (by omega) (by omega) (by omega) (by omega)
      · by_cases hr1 : q.r = 1
        · exact .r3324 ha3 (by omega) (by omega) (by omega) (by omega) hr1
        · exact .r3322 ha3 (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact .r4224 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem fixedRight_eq_of_p_r {a b c d : Nat}
    (q q' : FixedRightCGChannel a b c d)
    (hp : q.p = q'.p) (hr : q.r = q'.r) : q = q' := by
  cases q with
  | mk p p_le r r_le degree_eq =>
      cases q' with
      | mk p' p_le' r' r_le' degree_eq' =>
          dsimp only at hp hr
          subst p'
          subst r'
          rfl

/-- The higher-outer-order `(3,2,3;2)` block lowers in the first/third
direction to the symmetric measure-six correction fence. -/
theorem measureEight3232_firstThird_reduces_to_measureSix :
    reduceFirstThirdRightChannel measureEight3232Lower
        (by decide) (by decide) (by decide) (by decide) = correctionFenceLower ∧
    reduceFirstThirdRightChannel measureEight3232Middle
        (by decide) (by decide) (by decide) (by decide) = correctionFenceMiddle ∧
    reduceFirstThirdRightChannel measureEight3232Upper
        (by decide) (by decide) (by decide) (by decide) = correctionFenceUpper := by
  refine ⟨?_, ?_, ?_⟩ <;>
    apply fixedRight_eq_of_p_r <;> rfl

/-- The reflected `(3,3,2;2)` block lowers in the first/second direction to
the same measure-six correction fence. -/
theorem measureEight3322_firstSecond_reduces_to_measureSix :
    reduceFirstSecondRightChannel measureEight3322Lower
        (by decide) (by decide) (by decide) (by decide) = correctionFenceLower ∧
    reduceFirstSecondRightChannel measureEight3322Middle
        (by decide) (by decide) (by decide) (by decide) = correctionFenceMiddle ∧
    reduceFirstSecondRightChannel measureEight3322Upper
        (by decide) (by decide) (by decide) (by decide) = correctionFenceUpper := by
  refine ⟨?_, ?_, ?_⟩ <;>
    apply fixedRight_eq_of_p_r <;> rfl

/-- The first uniform two-step pattern.  Seven measure-eight blocks lie on
the upper-order-zero edge.  The only two blocks off that edge have outer
orders `(3,2,1)` and lower, in one of the two source directions, to the
measure-six fence. -/
theorem measureEight_edge_or_twoStep {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = 8)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    (q.r = 1 ∧ qp.r = 0) ∨
      (q.r = 2 ∧ qp.r = 1 ∧
        ((a = 3 ∧ b = 2 ∧ c = 3 ∧ d = 2) ∨
          (a = 3 ∧ b = 3 ∧ c = 2 ∧ d = 2))) := by
  have hreg := measureEight_adjacent_classification
    qm q qp hmeasure hp hprev hnext
  have hrp := adjacentRightChannel_outer_order q qp hnext
  cases hreg with
  | r2244 ha hb hc hd hqp hqr => exact Or.inl ⟨hqr, by omega⟩
  | r2334 ha hb hc hd hqp hqr => exact Or.inl ⟨hqr, by omega⟩
  | r2332 ha hb hc hd hqp hqr => exact Or.inl ⟨hqr, by omega⟩
  | r2424 ha hb hc hd hqp hqr => exact Or.inl ⟨hqr, by omega⟩
  | r3234 ha hb hc hd hqp hqr => exact Or.inl ⟨hqr, by omega⟩
  | r3232 ha hb hc hd hqp hqr =>
      exact Or.inr ⟨hqr, by omega, Or.inl ⟨ha, hb, hc, hd⟩⟩
  | r3324 ha hb hc hd hqp hqr => exact Or.inl ⟨hqr, by omega⟩
  | r3322 ha hb hc hd hqp hqr =>
      exact Or.inr ⟨hqr, by omega, Or.inr ⟨ha, hb, hc, hd⟩⟩
  | r4224 ha hb hc hd hqp hqr => exact Or.inl ⟨hqr, by omega⟩

/-- Every adjacent positive-order block on measure eight has the complete
physical Omega correction family. -/
theorem omegaCorrectionPhysical_measureEight {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c = 8)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    OmegaCorrectionPhysicalCoordinateFamily qm q qp := by
  have hreg := measureEight_adjacent_classification
    qm q qp hmeasure hp hprev hnext
  have hrm := adjacentRightChannel_outer_order qm q (by omega)
  have hrp := adjacentRightChannel_outer_order q qp hnext
  cases hreg with
  | r2244 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight2244Lower :=
        fixedRight_eq_of_p_r qm measureEight2244Lower
          (by simp only [measureEight2244Lower]; omega)
          (by simp only [measureEight2244Lower]; omega)
      have hq : q = measureEight2244Middle :=
        fixedRight_eq_of_p_r q measureEight2244Middle hqp hqr
      have hu : qp = measureEight2244Upper :=
        fixedRight_eq_of_p_r qp measureEight2244Upper
          (by simp only [measureEight2244Upper]; omega)
          (by simp only [measureEight2244Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight2244_correctionPhysical
  | r2334 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight2334Lower :=
        fixedRight_eq_of_p_r qm measureEight2334Lower
          (by simp only [measureEight2334Lower]; omega)
          (by simp only [measureEight2334Lower]; omega)
      have hq : q = measureEight2334Middle :=
        fixedRight_eq_of_p_r q measureEight2334Middle hqp hqr
      have hu : qp = measureEight2334Upper :=
        fixedRight_eq_of_p_r qp measureEight2334Upper
          (by simp only [measureEight2334Upper]; omega)
          (by simp only [measureEight2334Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight2334_correctionPhysical
  | r2332 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight2332Lower :=
        fixedRight_eq_of_p_r qm measureEight2332Lower
          (by simp only [measureEight2332Lower]; omega)
          (by simp only [measureEight2332Lower]; omega)
      have hq : q = measureEight2332Middle :=
        fixedRight_eq_of_p_r q measureEight2332Middle hqp hqr
      have hu : qp = measureEight2332Upper :=
        fixedRight_eq_of_p_r qp measureEight2332Upper
          (by simp only [measureEight2332Upper]; omega)
          (by simp only [measureEight2332Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight2332_correctionPhysical
  | r2424 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight2424Lower :=
        fixedRight_eq_of_p_r qm measureEight2424Lower
          (by simp only [measureEight2424Lower]; omega)
          (by simp only [measureEight2424Lower]; omega)
      have hq : q = measureEight2424Middle :=
        fixedRight_eq_of_p_r q measureEight2424Middle hqp hqr
      have hu : qp = measureEight2424Upper :=
        fixedRight_eq_of_p_r qp measureEight2424Upper
          (by simp only [measureEight2424Upper]; omega)
          (by simp only [measureEight2424Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight2424_correctionPhysical
  | r3234 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight3234Lower :=
        fixedRight_eq_of_p_r qm measureEight3234Lower
          (by simp only [measureEight3234Lower]; omega)
          (by simp only [measureEight3234Lower]; omega)
      have hq : q = measureEight3234Middle :=
        fixedRight_eq_of_p_r q measureEight3234Middle hqp hqr
      have hu : qp = measureEight3234Upper :=
        fixedRight_eq_of_p_r qp measureEight3234Upper
          (by simp only [measureEight3234Upper]; omega)
          (by simp only [measureEight3234Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight3234_correctionPhysical
  | r3232 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight3232Lower :=
        fixedRight_eq_of_p_r qm measureEight3232Lower
          (by simp only [measureEight3232Lower]; omega)
          (by simp only [measureEight3232Lower]; omega)
      have hq : q = measureEight3232Middle :=
        fixedRight_eq_of_p_r q measureEight3232Middle hqp hqr
      have hu : qp = measureEight3232Upper :=
        fixedRight_eq_of_p_r qp measureEight3232Upper
          (by simp only [measureEight3232Upper]; omega)
          (by simp only [measureEight3232Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight3232_correctionPhysical
  | r3324 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight3324Lower :=
        fixedRight_eq_of_p_r qm measureEight3324Lower
          (by simp only [measureEight3324Lower]; omega)
          (by simp only [measureEight3324Lower]; omega)
      have hq : q = measureEight3324Middle :=
        fixedRight_eq_of_p_r q measureEight3324Middle hqp hqr
      have hu : qp = measureEight3324Upper :=
        fixedRight_eq_of_p_r qp measureEight3324Upper
          (by simp only [measureEight3324Upper]; omega)
          (by simp only [measureEight3324Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight3324_correctionPhysical
  | r3322 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight3322Lower :=
        fixedRight_eq_of_p_r qm measureEight3322Lower
          (by simp only [measureEight3322Lower]; omega)
          (by simp only [measureEight3322Lower]; omega)
      have hq : q = measureEight3322Middle :=
        fixedRight_eq_of_p_r q measureEight3322Middle hqp hqr
      have hu : qp = measureEight3322Upper :=
        fixedRight_eq_of_p_r qp measureEight3322Upper
          (by simp only [measureEight3322Upper]; omega)
          (by simp only [measureEight3322Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight3322_correctionPhysical
  | r4224 ha hb hc hd hqp hqr =>
      subst a; subst b; subst c; subst d
      have hm : qm = measureEight4224Lower :=
        fixedRight_eq_of_p_r qm measureEight4224Lower
          (by simp only [measureEight4224Lower]; omega)
          (by simp only [measureEight4224Lower]; omega)
      have hq : q = measureEight4224Middle :=
        fixedRight_eq_of_p_r q measureEight4224Middle hqp hqr
      have hu : qp = measureEight4224Upper :=
        fixedRight_eq_of_p_r qp measureEight4224Upper
          (by simp only [measureEight4224Upper]; omega)
          (by simp only [measureEight4224Upper]; omega)
      subst qm; subst q; subst qp
      exact measureEight4224_correctionPhysical

/-- The two parity anchors and the structural measure-eight shell give the
complete physical correction family through measure eight. -/
theorem omegaCorrectionPhysical_throughEight {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hmeasure : rightLabelMeasure a b c ≤ 8)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) :
    OmegaCorrectionPhysicalCoordinateFamily qm q qp := by
  by_cases hsmall : rightLabelMeasure a b c ≤ 7
  · exact omegaCorrectionPhysical_throughSeven
      qm q qp hsmall hp hprev hnext
  · exact omegaCorrectionPhysical_measureEight
      qm q qp (by omega) hp hprev hnext

end YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell

#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.omegaCorrectionPhysical_of_boundary_and_highShell
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight2244_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight2334_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight2332_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight2424_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight3234_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight3232_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight3324_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight3322_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight4224_correctionPhysical
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight_adjacent_classification
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight3232_firstThird_reduces_to_measureSix
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight3322_firstSecond_reduces_to_measureSix
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.measureEight_edge_or_twoStep
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.omegaCorrectionPhysical_measureEight
#print axioms YMGap.Continuum.SU2OrderedRacahMeasureEightStructuralCorrectionShell.omegaCorrectionPhysical_throughEight
