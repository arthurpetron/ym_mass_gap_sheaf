/-
M2b/M3a -- a grouped contraction over fixed physical distance produces a
uniform physical mass floor.

Let `q_j` be the same separator which controls the connected
gauge-invariant correlators at lattice spacing `a_j`.  Suppose an analytic
producer supplies a positive block depth `n_j`, one uniform macro rate
`rho < 1`, and one uniform physical length `L` such that

    q_j ^ n_j <= rho,             n_j * a_j <= L.

Then Bernoulli's inequality gives

    1 - rho <= 1 - q_j ^ n_j <= n_j * (1 - q_j),

and positive rational division yields the dimensionful lower bound

    (1 - rho) / L <= (1 - q_j) / a_j.

This is the correct scaling interpretation of a BF4 macro-slab contraction.
In particular, it does not identify `rho` with a one-lattice-step separator,
which would generally manufacture a divergent mass as `a_j -> 0`.

The structure below is deliberately not inhabited here.  Its `groupedBound`
field is the genuine same-object producer seam: a future BF4/Gibbs argument
must prove that its fixed-cylinder contraction is the power of the physical
separator which controls the supplied gauge-invariant correlators.  A separate
upper rate bound is still required for finite dimensional transmutation.

All data are constructive and Type-level.  The proof uses exact `Q'` order,
Bernoulli's inequality, and positive rational division only.
-/

import YMGap.Continuum.PhysicalSeparatorLogRate
import YMGap.Continuum.R1CornerAtoms

namespace YMGap.Continuum.FixedDistancePhysicalSeparator

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.R1CornerAtoms

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The honest grouped-separator producer contract -/

/-- A contraction of the *same physical separator* over a uniformly bounded
physical distance.  `groupedBound` is the substantive Gibbs/BF4 identification
field; the remaining fields record its depth and dimensional bookkeeping. -/
structure FixedDistanceContraction
    (P : PhysicalSeparator) (A : PhysicalSpacing) : Type where
  /-- Number of lattice transfer steps in the grouped cylinder at scale `j`. -/
  depth : Nat -> Nat
  /-- The grouped cylinder is nonempty. -/
  depth_pos : forall j : Nat, 0 < depth j
  /-- Uniform contraction rate of the grouped physical transfer. -/
  macroRate : Q'
  /-- The macro rate is nonnegative. -/
  macroRate_nonnegative : (0 : Q') <= macroRate
  /-- The macro rate is strictly sub-unit. -/
  macroRate_lt_one : macroRate < (1 : Q')
  /-- Uniform upper bound on the physical length of a grouped cylinder. -/
  lengthCeiling : Q'
  /-- The physical-length ceiling is positive. -/
  lengthCeiling_pos : (0 : Q') < lengthCeiling
  /-- **Same-object grouped contraction:** the BF4/macro estimate must bound
  the power of the very separator carried by `P`. -/
  groupedBound : forall j : Nat,
    qpow (P.sep j) (depth j) <= macroRate
  /-- The grouped lattice depth occupies at most `lengthCeiling`. -/
  physicalLengthBound : forall j : Nat,
    Q'.ofNat (depth j) * A.spacing j <= lengthCeiling

namespace FixedDistanceContraction

variable {P : PhysicalSeparator} {A : PhysicalSpacing}

/-- The strict positive margin left by the macro contraction. -/
def macroMargin (D : FixedDistanceContraction P A) : Q' :=
  (1 : Q') - D.macroRate

/-- The physical mass floor extracted from macro margin divided by macro
physical length. -/
def floorRate (D : FixedDistanceContraction P A) : Q' :=
  Q'.divPos D.macroMargin D.lengthCeiling D.lengthCeiling_pos

/-- The macro margin is strictly positive. -/
theorem macroMargin_pos (D : FixedDistanceContraction P A) :
    (0 : Q') < D.macroMargin :=
  one_sub_pos_of_lt_one D.macroRate_lt_one

/-- The extracted physical floor is strictly positive. -/
theorem floorRate_pos (D : FixedDistanceContraction P A) :
    (0 : Q') < D.floorRate :=
  Q'.divPos_pos D.macroMargin D.lengthCeiling
    D.lengthCeiling_pos D.macroMargin_pos

/-- Bernoulli converts the grouped contraction into the dimensionless bound
`1 - rho <= n_j * (1 - q_j)`. -/
theorem macroMargin_le_depth_mul_margin
    (D : FixedDistanceContraction P A) (j : Nat) :
    D.macroMargin <= Q'.ofNat (D.depth j) * P.physMargin j := by
  have hneg : -D.macroRate <= -(qpow (P.sep j) (D.depth j)) :=
    Q'.neg_le_neg (D.groupedBound j)
  have hmacro :
      (1 : Q') + -D.macroRate <=
        (1 : Q') + -(qpow (P.sep j) (D.depth j)) :=
    Q'.add_le_add_left 1 (-D.macroRate)
      (-(qpow (P.sep j) (D.depth j))) hneg
  have hbern := oneSub_qpow_le (P.sep_nonneg j)
    (Q'.le_of_lt (P.sep_lt_one j)) (D.depth j)
  exact Q'.le_trans' _ _ _ hmacro hbern

/-- Cross-multiplied physical form of the grouped estimate:
`(1-rho) a_j <= (1-q_j) L`. -/
theorem macroMargin_mul_spacing_le_margin_mul_length
    (D : FixedDistanceContraction P A) (j : Nat) :
    D.macroMargin * A.spacing j <=
      P.physMargin j * D.lengthCeiling := by
  have hspacingNonnegative : (0 : Q') <= A.spacing j :=
    Q'.le_of_lt (A.spacing_pos j)
  have hmarginNonnegative : (0 : Q') <= P.physMargin j :=
    Q'.le_of_lt (P.physMargin_pos j)
  have hfirst :
      D.macroMargin * A.spacing j <=
        (Q'.ofNat (D.depth j) * P.physMargin j) * A.spacing j :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (D.macroMargin_le_depth_mul_margin j) hspacingNonnegative
  have hreorder :
      ((Q'.ofNat (D.depth j) * P.physMargin j) * A.spacing j) ≈
        P.physMargin j * (Q'.ofNat (D.depth j) * A.spacing j) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (Q'.ofNat (D.depth j) * P.physMargin j)
        (P.physMargin j * Q'.ofNat (D.depth j))
        (A.spacing j)
        (Q'.mul_comm_eqv (Q'.ofNat (D.depth j)) (P.physMargin j))) ?_
    exact Q'.mul_assoc_eqv (P.physMargin j)
      (Q'.ofNat (D.depth j)) (A.spacing j)
  have hsecond :
      P.physMargin j * (Q'.ofNat (D.depth j) * A.spacing j) <=
        P.physMargin j * D.lengthCeiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (D.physicalLengthBound j) hmarginNonnegative
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hsecond)

/-- Dividing the cross-multiplied estimate by the positive length ceiling
gives `floorRate * a_j <= 1 - q_j`. -/
theorem floorRate_mul_spacing_le_margin
    (D : FixedDistanceContraction P A) (j : Nat) :
    D.floorRate * A.spacing j <= P.physMargin j := by
  have hquot :
      Q'.divPos (D.macroMargin * A.spacing j)
          D.lengthCeiling D.lengthCeiling_pos <=
        P.physMargin j :=
    Q'.divPos_le_of_le_mul
      (D.macroMargin * A.spacing j)
      D.lengthCeiling D.lengthCeiling_pos
      (D.macroMargin_mul_spacing_le_margin_mul_length j)
  have hdivide :
      (D.floorRate * A.spacing j) ≈
        Q'.divPos (D.macroMargin * A.spacing j)
          D.lengthCeiling D.lengthCeiling_pos := by
    unfold floorRate Q'.divPos
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv D.macroMargin
        (Q'.recipPos D.lengthCeiling D.lengthCeiling_pos)
        (A.spacing j)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left D.macroMargin _ _
        (Q'.mul_comm_eqv
          (Q'.recipPos D.lengthCeiling D.lengthCeiling_pos)
          (A.spacing j))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv D.macroMargin (A.spacing j)
        (Q'.recipPos D.lengthCeiling D.lengthCeiling_pos))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdivide) hquot

/-- **Fixed-distance physical-floor theorem.**  The macro contraction gives
one positive lower bound on the rational physical margin rate at every scale. -/
theorem floorRate_le_marginRate
    (D : FixedDistanceContraction P A) (j : Nat) :
    D.floorRate <= marginRate P A j := by
  exact Q'.le_divPos_of_mul_le (P.physMargin j)
    (A.spacing j) (A.spacing_pos j)
    (D.floorRate_mul_spacing_le_margin j)

/-- The grouped fixed-distance producer supplies a uniform lower certificate
for the exact logarithmic rate on any supplied direct log window. -/
def exactLogRateFloor
    (D : FixedDistanceContraction P A) (W : PhysicalLogWindow P) :
    UniformPhysicalLogRateFloor
      (exactRateFamilyOfPhysicalData P A.spacing A.spacing_pos W) where
  floor := D.floorRate
  floor_pos := D.floorRate_pos
  floor_bound := fun j => by
    have hproxy :
        CReal.leEv (CReal.ofQ' D.floorRate)
          (CReal.ofQ' (marginRate P A j)) :=
      CReal.leEv_ofQ'_of_approx_ge (fun _ => D.floorRate_le_marginRate j)
    exact CReal.leEv_trans hproxy (marginRate_le_massRate P A W j)

/-! ## 2. Optional finiteness ceiling and the full exact M2 certificate -/

/-- The independent dimensional-transmutation ceiling for the margin rate.
This is not implied by a strict fixed-distance contraction. -/
structure MarginRateCeiling (D : FixedDistanceContraction P A) : Type where
  ceiling : Q'
  upper : forall j : Nat, marginRate P A j <= ceiling

/-- A fixed-distance lower producer plus the independent rate ceiling gives the
two-sided rational `PhysicalGapFloor`. -/
def physicalGapFloor
    (D : FixedDistanceContraction P A) (U : MarginRateCeiling D) :
    PhysicalGapFloor P A.spacing A.spacing_pos where
  c := D.floorRate
  c_pos := D.floorRate_pos
  floor := D.floorRate_le_marginRate
  ceil := U.ceiling
  finiteness := U.upper

/-- With a direct log window and the independent finiteness ceiling, the
grouped producer packages the complete exact physical-separator certificate. -/
def exactPhysicalSeparatorCertificate
    (D : FixedDistanceContraction P A) (W : PhysicalLogWindow P)
    (U : MarginRateCeiling D) : ExactPhysicalSeparatorCertificate :=
  exactPhysicalSeparatorCertificateOfPhysicalGapFloor
    P A.spacing A.spacing_pos W (D.physicalGapFloor U)

end FixedDistanceContraction

end YMGap.Continuum.FixedDistancePhysicalSeparator

#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.macroMargin_pos
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.floorRate_pos
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.macroMargin_le_depth_mul_margin
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.macroMargin_mul_spacing_le_margin_mul_length
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.floorRate_mul_spacing_le_margin
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.floorRate_le_marginRate
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.exactLogRateFloor
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.physicalGapFloor
#print axioms YMGap.Continuum.FixedDistancePhysicalSeparator.FixedDistanceContraction.exactPhysicalSeparatorCertificate
