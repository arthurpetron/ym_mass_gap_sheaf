/-
# The physical harmonic true margin and its exact AF-tail indexing

The Pascal theta certificate gives a pointwise lower floor for the actual
finite-character harmonic mass.  This module divides that mass by the actual
quadratic-cutoff spacing, records the resulting positive physical margin, and
aligns the harmonic schedule with the tail of the canonical `AFRateModulus`.

The remaining cross-scale input is stated without weakening: it is precisely
the multiplicative `singleStep` inequality for these constructed margins.
Supplying that input produces the existing `SingleStepDefectBound` with no
free margin function and no scalar identification hypothesis.
-/

import YMGap.Continuum.HarmonicThetaPascalClosure
import YMGap.Continuum.FusedSpacingStepBridge
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.HarmonicTrueMarginStep

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicRetuneFloor
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HeatKernelLinearBound
open YMGap.Continuum.SingleStepDefectReduction
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.UniformCouplingFromAF

/-- The actual harmonic lattice mass divided by the actual reciprocal-quadratic
cutoff spacing.  This is a concrete physical margin, not a free sequence. -/
def harmonicTrueMargin (k : Nat) : Q' :=
  Q'.divPos (harmonicMass k) (harmonicSpacing k) (harmonicSpacing_pos k)

/-- The exact quadratic mass floor furnished by the Pascal certificate. -/
def harmonicQuadraticMassFloor (k : Nat) : Q' :=
  (Q'.mkPos 1 2 (by decide) * harmU k) *
    (Q'.ofNat 3 +
      -(Q'.ofNat 3 * (Q'.mkPos 1 2 (by decide) * harmU k)))

/-- From the first non-base scale onward, the constructed harmonic physical
margin is strictly positive. -/
theorem harmonicTrueMargin_pos {k : Nat} (hk : 1 ≤ k) :
    (0 : Q') < harmonicTrueMargin k := by
  have hm : (0 : Q') < harmonicMass k :=
    lt_of_lt_of_le (harmU_pos k) (harmonic_unit_le_mass hk)
  unfold harmonicTrueMargin Q'.divPos
  exact Q'.mul_pos hm (Q'.recipPos_pos _ _)

/-- The harmonic-unit mass floor lifts monotonically through the positive
spacing quotient. -/
theorem harmonicTrueMargin_unit_floor {k : Nat} (hk : 1 ≤ k) :
    Q'.divPos (harmU k) (harmonicSpacing k) (harmonicSpacing_pos k) ≤
      harmonicTrueMargin k := by
  unfold harmonicTrueMargin
  exact divPos_le_divPos_of_le (harmonicSpacing_pos k)
    (harmonic_unit_le_mass hk)

/-- The sharper quadratic mass floor likewise lifts to the genuine physical
mass-over-spacing margin. -/
theorem harmonicTrueMargin_quadratic_floor {k : Nat} (hk : 1 ≤ k) :
    Q'.divPos (harmonicQuadraticMassFloor k)
        (harmonicSpacing k) (harmonicSpacing_pos k) ≤
      harmonicTrueMargin k := by
  unfold harmonicTrueMargin harmonicQuadraticMassFloor
  exact divPos_le_divPos_of_le (harmonicSpacing_pos k)
    (harmonic_quadratic_mass_floor hk)

/-- A concrete positive anchor for the physical harmonic margin. -/
theorem harmonicTrueMargin_anchor_pos :
    (0 : Q') < harmonicTrueMargin 1 :=
  harmonicTrueMargin_pos (by decide)

/-! ## Exact alignment with the canonical AF tail -/

/-- The canonical AF cutoff is a derived closed rational/natural value. -/
theorem canonical_afCutoff_eq :
    afCutoff afRateModulus_canonical = 144 := by
  decide

/-- Harmonic index corresponding to the tail-shifted canonical AF index. -/
def canonicalHarmonicIndex (k : Nat) : Nat :=
  afCutoff afRateModulus_canonical + k - 1

/-- Before the tail shift, the canonical weight at `k+1` is definitionally the
harmonic weight at `k`. -/
theorem canonical_weight_succ_eq_harmW (k : Nat) :
    afRateModulus_canonical.w (k + 1) = harmW k := by
  rfl

/-- The tail-shifted canonical AF weight is exactly the harmonic weight at the
corresponding harmonic index. -/
theorem canonical_tail_weight_eq_harmW (k : Nat) :
    afRateModulus_canonical.w
        (afCutoff afRateModulus_canonical + k) =
      harmW (canonicalHarmonicIndex k) := by
  have hcut : afCutoff afRateModulus_canonical = 144 := canonical_afCutoff_eq
  have hidx : afCutoff afRateModulus_canonical + k =
      canonicalHarmonicIndex k + 1 := by
    unfold canonicalHarmonicIndex
    rw [hcut]
    omega
  rw [hidx]
  exact canonical_weight_succ_eq_harmW _

/-- Consecutive canonical tail indices are consecutive harmonic indices. -/
theorem canonicalHarmonicIndex_succ (k : Nat) :
    canonicalHarmonicIndex (k + 1) = canonicalHarmonicIndex k + 1 := by
  unfold canonicalHarmonicIndex
  rw [canonical_afCutoff_eq]
  omega

/-- Every canonical tail index lies in the range where the Pascal mass floor is
available. -/
theorem one_le_canonicalHarmonicIndex (k : Nat) :
    1 ≤ canonicalHarmonicIndex k := by
  unfold canonicalHarmonicIndex
  rw [canonical_afCutoff_eq]
  omega

/-- The existing model-defect sequence on the canonical AF tail is exactly the
bond-moving defect evaluated at the aligned harmonic weight. -/
theorem canonical_afDefectSeq_eq_harmonic (k : Nat) :
    afDefectSeq afRateModulus_canonical k =
      bondMovingDeltaRen 1 pMult (harmW (canonicalHarmonicIndex k)) := by
  unfold afDefectSeq renDefect
  rw [canonical_tail_weight_eq_harmW]

/-- The concrete physical true-margin sequence on the canonical AF tail. -/
def canonicalHarmonicTrueMargin (k : Nat) : Q' :=
  harmonicTrueMargin (canonicalHarmonicIndex k)

/-- The canonical-tail physical margin has a derived positive anchor. -/
theorem canonicalHarmonicTrueMargin_anchor_pos :
    (0 : Q') < canonicalHarmonicTrueMargin 0 := by
  unfold canonicalHarmonicTrueMargin
  exact harmonicTrueMargin_pos (one_le_canonicalHarmonicIndex 0)

/-- The Pascal certificate supplies an explicit quadratic lower floor at every
canonical AF-tail scale. -/
theorem canonicalHarmonicTrueMargin_quadratic_floor (k : Nat) :
    Q'.divPos (harmonicQuadraticMassFloor (canonicalHarmonicIndex k))
        (harmonicSpacing (canonicalHarmonicIndex k))
        (harmonicSpacing_pos (canonicalHarmonicIndex k)) ≤
      canonicalHarmonicTrueMargin k := by
  unfold canonicalHarmonicTrueMargin
  exact harmonicTrueMargin_quadratic_floor
    (one_le_canonicalHarmonicIndex k)

/-- **Pointwise-floor fence.**  The new quadratic lower floors, by themselves,
do not imply the consecutive physical-margin step.  At the closed scale `k=5`,
the admissible mock masses `M₅=1` and `M₆=quadraticFloor₆` both obey their
respective lower-floor requirements, but the model-defect margin comparison
fails.  Thus a cross-scale erosion/weight-drift estimate is genuinely required;
no proof may compose the two pointwise lower bounds as though they were a
recursion. -/
theorem quadratic_floors_alone_do_not_force_step_k5 :
    harmonicQuadraticMassFloor 5 ≤ (1 : Q') ∧
    harmonicQuadraticMassFloor 6 ≤ harmonicQuadraticMassFloor 6 ∧
    ¬ ((1 - bondMovingDeltaRen 1 pMult (harmW 5)) *
          Q'.divPos 1 (harmonicSpacing 5) (harmonicSpacing_pos 5) ≤
        Q'.divPos (harmonicQuadraticMassFloor 6)
          (harmonicSpacing 6) (harmonicSpacing_pos 6)) := by
  decide

/-! ## The exact remaining cross-scale input -/

/-- The non-weakened physical harmonic drop statement.  It is the exact
consecutive-scale inequality needed after the pointwise Pascal floor: the real
harmonic mass-over-spacing margin loses no more than the derived transverse
bond-moving defect. -/
structure HarmonicTrueMarginDrop : Type where
  singleStep : ∀ (k : Nat), 1 ≤ k →
    (1 - bondMovingDeltaRen 1 pMult (harmW k)) * harmonicTrueMargin k ≤
      harmonicTrueMargin (k + 1)

/-- An exact harmonic drop proof inhabits the existing single-step carrier on
the canonical AF tail.  All weights, defects, margins, and the positive anchor
are constructed; no free scalar pin remains. -/
def singleStepDefectBound_of_harmonicDrop
    (H : HarmonicTrueMarginDrop) : SingleStepDefectBound where
  afr := afRateModulus_canonical
  trueMargin := canonicalHarmonicTrueMargin
  trueMargin0_pos := canonicalHarmonicTrueMargin_anchor_pos
  singleStep := by
    intro k
    have h := H.singleStep (canonicalHarmonicIndex k)
      (one_le_canonicalHarmonicIndex k)
    unfold canonicalHarmonicTrueMargin
    rw [canonical_afDefectSeq_eq_harmonic, canonicalHarmonicIndex_succ]
    exact h

#print axioms harmonicTrueMargin_pos
#print axioms harmonicTrueMargin_unit_floor
#print axioms harmonicTrueMargin_quadratic_floor
#print axioms canonical_afCutoff_eq
#print axioms canonical_tail_weight_eq_harmW
#print axioms canonical_afDefectSeq_eq_harmonic
#print axioms canonicalHarmonicTrueMargin_anchor_pos
#print axioms canonicalHarmonicTrueMargin_quadratic_floor
#print axioms quadratic_floors_alone_do_not_force_step_k5
#print axioms singleStepDefectBound_of_harmonicDrop

end YMGap.Continuum.HarmonicTrueMarginStep
