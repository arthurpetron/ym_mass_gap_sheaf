/-
M4e -- construct fixed-physical-time lattice sampling from any positive
rational spacing with an explicit spacing-to-zero modulus.

For `a_j = p_j / d_j > 0`, use

    n_j(t) = floor(t d_j / p_j).

Euclidean division gives

    a_j n_j(t) <= t <= a_j n_j(t) + a_j.

Hence `a_j -> 0` implies `a_j n_j(t) -> t` constructively.  This removes
`PhysicalSeparationSampling` as an independent BF4/AF residual: the already
proved AF spacing modulus constructs it.
-/

import YMGap.Continuum.PhysicalSeparatorContinuumRealization

namespace YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate

/-- The floor sampling `floor(t/a_j)` computed entirely in `Nat`. -/
def floorLatticeSteps (A : PhysicalSpacing) (j t : Nat) : Nat :=
  (t * (PhysicalSpacing.spacing A j).den) /
    (PhysicalSpacing.spacing A j).num.toNat

/-- Positivity of the rational spacing makes the divisor in
`floorLatticeSteps` a positive natural number. -/
theorem spacingNumToNat_pos (A : PhysicalSpacing) (j : Nat) :
    0 < (PhysicalSpacing.spacing A j).num.toNat := by
  have hp : (0 : Int) < (PhysicalSpacing.spacing A j).num :=
    Q'.num_pos_of_pos (A.spacing_pos j)
  have hc : (0 : Int) <
      ((PhysicalSpacing.spacing A j).num.toNat : Int) := by
    rw [Int.toNat_of_nonneg (Int.le_of_lt hp)]
    exact hp
  exact_mod_cast hc

/-- The floor-sampled physical distance does not overshoot `t`. -/
theorem sampledDistance_le
    (A : PhysicalSpacing) (j t : Nat) :
    PhysicalSpacing.spacing A j * Q'.ofNat (floorLatticeSteps A j t) <=
      Q'.ofNat t := by
  let a := PhysicalSpacing.spacing A j
  let p : Nat := a.num.toNat
  let d : Nat := a.den
  let n : Nat := (t * d) / p
  have hpInt : (0 : Int) < a.num := Q'.num_pos_of_pos (A.spacing_pos j)
  have hpCast : (p : Int) = a.num := by
    dsimp [p]
    exact Int.toNat_of_nonneg (Int.le_of_lt hpInt)
  have hdiv : n * p <= t * d := by
    dsimp [n]
    exact Nat.div_mul_le_self (t * d) p
  show (a * Q'.ofNat n).num * ((Q'.ofNat t).den : Int) <=
    (Q'.ofNat t).num * ((a * Q'.ofNat n).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.mul_one, Int.mul_one]
  rw [Int.mul_comm a.num (n : Int), <- hpCast]
  exact_mod_cast hdiv

/-- The floor-sampled physical distance misses `t` by at most one lattice
spacing. -/
theorem le_sampledDistance_add_spacing
    (A : PhysicalSpacing) (j t : Nat) :
    Q'.ofNat t <=
      PhysicalSpacing.spacing A j * Q'.ofNat (floorLatticeSteps A j t) +
        PhysicalSpacing.spacing A j := by
  let a := PhysicalSpacing.spacing A j
  let p : Nat := a.num.toNat
  let d : Nat := a.den
  let n : Nat := (t * d) / p
  have hp : 0 < p := by
    dsimp [p, a]
    exact spacingNumToNat_pos A j
  have hpInt : (0 : Int) < a.num := Q'.num_pos_of_pos (A.spacing_pos j)
  have hpCast : (p : Int) = a.num := by
    dsimp [p]
    exact Int.toNat_of_nonneg (Int.le_of_lt hpInt)
  have hdecomp : p * n + (t * d) % p = t * d := by
    dsimp [n]
    exact Nat.div_add_mod (t * d) p
  have hmod : (t * d) % p < p := Nat.mod_lt _ hp
  have hstrict : t * d < p * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  show (Q'.ofNat t).num *
      ((a * Q'.ofNat n + a).den : Int) <=
    (a * Q'.ofNat n + a).num * ((Q'.ofNat t).den : Int)
  rw [Q'.add_num_cast, Q'.add_den_cast,
    Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.mul_one, Int.mul_one]
  rw [<- hpCast]
  have hstrictInt : (t : Int) * (d : Int) <
      (p : Int) * ((n + 1 : Nat) : Int) := by
    exact_mod_cast hstrict
  have hdPos : (0 : Int) < (d : Int) := by
    exact_mod_cast a.den_pos
  dsimp [d] at hstrictInt hdPos
  have hscaled := Int.mul_lt_mul_of_pos_right hstrictInt hdPos
  exact Int.le_of_lt (by
    calc
      (t : Int) * ((a.den : Int) * (a.den : Int)) =
          ((t : Int) * (a.den : Int)) * (a.den : Int) := by
            rw [Int.mul_assoc]
      _ < ((p : Int) * ((n : Int) + 1)) * (a.den : Int) := hscaled
      _ = (p : Int) * (n : Int) * (a.den : Int) +
          (p : Int) * (a.den : Int) := by
            rw [Int.mul_add, Int.mul_one, Int.add_mul])

/-- The floor sampling converges to each fixed integer physical separation. -/
theorem floorSampling_distanceConverges
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) :
    CReal.ConvergesTo
      (fun j => CReal.ofQ'
        (PhysicalSpacing.spacing A j *
          Q'.ofNat (floorLatticeSteps A j t)))
      (CReal.ofQ' (Q'.ofNat t)) := by
  intro epsilon hepsilon
  refine ⟨Z.modulus epsilon, fun j hj => ⟨0, fun n _hn => ?_⟩⟩
  simp only [CReal.ofQ'_approx]
  have hspacing : PhysicalSpacing.spacing A j <= epsilon :=
    Z.spacing_le epsilon hepsilon j hj
  have hsampleLe := sampledDistance_le A j t
  have htargetLe := le_sampledDistance_add_spacing A j t
  constructor
  · exact Q'.le_trans' _ _ _ hsampleLe
      (Q'.add_le_self_of_nonneg (Q'.ofNat t) epsilon
        (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ htargetLe
      (Q'.add_le_add_left
        (PhysicalSpacing.spacing A j *
          Q'.ofNat (floorLatticeSteps A j t))
        (PhysicalSpacing.spacing A j) epsilon hspacing)

/-- Any positive rational spacing with a Type-level zero modulus has the
required fixed-physical-time sampling. -/
def physicalSeparationSamplingOfSpacingToZero
    (A : PhysicalSpacing) (Z : SpacingToZero A) :
    PhysicalSeparationSampling A where
  latticeSteps := floorLatticeSteps A
  distanceConverges := floorSampling_distanceConverges A Z

end YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero

#print axioms YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero.spacingNumToNat_pos
#print axioms YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero.sampledDistance_le
#print axioms YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero.le_sampledDistance_add_spacing
#print axioms YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero.floorSampling_distanceConverges
#print axioms YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero.physicalSeparationSamplingOfSpacingToZero
