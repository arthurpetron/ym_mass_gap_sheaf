/-
# BF4 fence: a positive interior potential is not a grouped heat semigroup

`GroupedAllLabelHaarRefresh` proves exact heat-coordinate semigroup arithmetic
and the positive all-label Haar floor

  epsilon0 = 1055 / 2272.

A tempting but invalid shortcut is to apply that semigroup arithmetic across
the spatial Feynman--Kac factors in the physical five-holonomy kernel.  This
file gives a finite exact-rational countermodel.

Let `Q` be the strictly positive symmetric two-state raw heat kernel with
diagonal `1` and off-diagonal `epsilon0`.  Thus every entry lies in the exact
all-label interval `[epsilon0,1]`.  Compare

  grouped(x,z)    = sum_y Q(x,y) Q(y,z)
  interleaved(x,z)= sum_y Q(x,y) D(y) Q(y,z),

where the strictly positive interior potential is `D(false)=1`,
`D(true)=16`.  Exact arithmetic proves:

* `interleaved` is not the grouped heat convolution;
* it is not even bounded pointwise by `4 * grouped`.

Consequently the grouped heat-mode semigroup and positivity of intermediate
spatial weights do not imply the one-factor order estimate consumed by the
48-factor BF4 Perron ceiling.  The physical spatial conditional integral (or
an equivalent Yang--Mills-specific Harnack theorem) is indispensable.

This is a shortcut fence, not a counterexample to the Yang--Mills estimate.

# Axiom gate

No `Classical.*`, `native_decide`, `sorry`, or custom axioms.
-/

import YMGap.Continuum.GroupedAllLabelHaarRefresh

namespace YMGap.Continuum.BF4InterleavedPotentialShortcutFence

open YMGap.Constructive
open YMGap.Continuum.GroupedAllLabelHaarRefresh

local infix:50 " ≈ " => Q'.eqv

/-- A finite two-state raw kinetic kernel whose exact floor is the proved
all-label Haar floor. -/
def kineticRaw (source target : Bool) : Q' :=
  if source = target then 1 else allLabelHaarFloor

/-- A nonconstant but strictly positive interior Feynman--Kac weight. -/
def interiorPotential (middle : Bool) : Q' :=
  if middle then Q'.ofNat 16 else 1

/-- The flat potential used by bare heat convolution. -/
def flatPotential (_middle : Bool) : Q' := 1

/-- Exact two-step raw transfer with an intermediate potential. -/
def twoStepWithPotential
    (potential : Bool → Q') (source target : Bool) : Q' :=
  kineticRaw source false * potential false * kineticRaw false target +
  kineticRaw source true * potential true * kineticRaw true target

/-- Bare grouped heat convolution. -/
def groupedKinetic (source target : Bool) : Q' :=
  twoStepWithPotential flatPotential source target

/-- The same two heat steps with a positive spatial weight inserted. -/
def interleavedPhysical (source target : Bool) : Q' :=
  twoStepWithPotential interiorPotential source target

/-- Pointwise semantic equivalence of two finite raw kernels. -/
def KernelEqv (left right : Bool → Bool → Q') : Prop :=
  ∀ source target, left source target ≈ right source target

/-- Every kinetic entry has the actual grouped all-label floor. -/
theorem kineticRaw_ge_floor (source target : Bool) :
    allLabelHaarFloor ≤ kineticRaw source target := by
  cases source <;> cases target <;> decide

/-- Every kinetic entry is at most one. -/
theorem kineticRaw_le_one (source target : Bool) :
    kineticRaw source target ≤ (1 : Q') := by
  cases source <;> cases target <;> decide

/-- The inserted interior weight is strictly positive at both states. -/
theorem interiorPotential_pos (middle : Bool) :
    (0 : Q') < interiorPotential middle := by
  cases middle <;> decide

/-- Exact diagonal of the bare grouped convolution. -/
theorem grouped_true_true_value :
    groupedKinetic true true ≈
      allLabelHaarFloor * allLabelHaarFloor + 1 := by
  unfold groupedKinetic twoStepWithPotential flatPotential kineticRaw
  decide

/-- Exact diagonal after inserting the positive interior potential. -/
theorem interleaved_true_true_value :
    interleavedPhysical true true ≈
      allLabelHaarFloor * allLabelHaarFloor + Q'.ofNat 16 := by
  unfold interleavedPhysical twoStepWithPotential interiorPotential kineticRaw
  decide

/-- The positive interior weight cannot be absorbed into the grouped heat
semigroup: the two raw kernels differ at the `true,true` entry. -/
theorem interleaved_not_grouped :
    ¬ KernelEqv interleavedPhysical groupedKinetic := by
  intro hkernel
  have hentry := hkernel true true
  have hnot :
      ¬ interleavedPhysical true true ≈ groupedKinetic true true := by
    unfold interleavedPhysical groupedKinetic twoStepWithPotential
      interiorPotential flatPotential kineticRaw allLabelHaarFloor
    decide
  exact hnot hentry

/-- **Concrete failure of the naive single-factor ceiling.**
Despite the exact floor/ceiling bounds on `kineticRaw` and strict positivity
of the intermediate weight, the interleaved diagonal exceeds four times the
bare grouped diagonal. -/
theorem four_mul_grouped_lt_interleaved :
    Q'.ofNat 4 * groupedKinetic true true <
      interleavedPhysical true true := by
  unfold interleavedPhysical groupedKinetic twoStepWithPotential
    interiorPotential flatPotential kineticRaw allLabelHaarFloor
  decide

/-- Hence there is no pointwise `4`-order domination of the interleaved
kernel by the grouped kinetic kernel. -/
theorem no_four_pointwise_ceiling :
    ¬ ∀ source target,
      interleavedPhysical source target ≤
        Q'.ofNat 4 * groupedKinetic source target := by
  intro hceiling
  have hle := hceiling true true
  have hbad :
      ¬ interleavedPhysical true true ≤
        Q'.ofNat 4 * groupedKinetic true true := by
    unfold interleavedPhysical groupedKinetic twoStepWithPotential
      interiorPotential flatPotential kineticRaw allLabelHaarFloor
    decide
  exact hbad hle

/-- One bundled machine-checkable statement of the shortcut obstruction:
the all-label floor, unit ceiling, and positive-potential premises all hold,
but the proposed fourfold pointwise conclusion fails. -/
theorem grouped_semigroup_positive_potential_shortcut_refuted :
    (∀ source target,
      allLabelHaarFloor ≤ kineticRaw source target) ∧
    (∀ source target,
      kineticRaw source target ≤ (1 : Q')) ∧
    (∀ middle, (0 : Q') < interiorPotential middle) ∧
    ¬ ∀ source target,
      interleavedPhysical source target ≤
        Q'.ofNat 4 * groupedKinetic source target :=
  ⟨kineticRaw_ge_floor, kineticRaw_le_one,
    interiorPotential_pos, no_four_pointwise_ceiling⟩

end YMGap.Continuum.BF4InterleavedPotentialShortcutFence

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4InterleavedPotentialShortcutFence.kineticRaw_ge_floor
#print axioms YMGap.Continuum.BF4InterleavedPotentialShortcutFence.interiorPotential_pos
#print axioms YMGap.Continuum.BF4InterleavedPotentialShortcutFence.interleaved_not_grouped
#print axioms YMGap.Continuum.BF4InterleavedPotentialShortcutFence.four_mul_grouped_lt_interleaved
#print axioms YMGap.Continuum.BF4InterleavedPotentialShortcutFence.no_four_pointwise_ceiling
#print axioms YMGap.Continuum.BF4InterleavedPotentialShortcutFence.grouped_semigroup_positive_potential_shortcut_refuted
