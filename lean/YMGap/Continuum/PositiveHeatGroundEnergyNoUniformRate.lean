/-
# No small relative energy follows from bare heat and exact ground stationarity

The computed two-state action and positive ground vector have an exact
interacting eigenrelation, and the action remains uniformly bounded. Yet
the actual OWN-variance-relative energy stays above one half as the bare
heat tends to the identity. The rational witness for each proposed rate
coefficient is reused, not assumed or obtained by choice.

Only the positive ORIGINAL edge partition is inverted. All normalized
moments below use the same action, ground vector, transfer and source.
This rules out a generic shortcut, NOT a BF4/Yang--Mills estimate. It does
not rule out action-specific cancellation, an action tending to a scalar,
or the original Wilson changing-family route.
-/

import YMGap.Continuum.PositiveHeatGroundEnergyObstruction
import YMGap.Continuum.PositiveSourceHeatModeScalingObstruction

namespace YMGap.Continuum.PositiveHeatGroundEnergyNoUniformRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.PositiveHeatGroundEnergyObstruction
open YMGap.Continuum.PositiveSourceHeatModeScalingObstruction
  (counterStep counterStep_bounds)

local infix:50 " ≈ " => Q'.eqv
local notation "half" => HalfPow.half

private theorem counterStep_lt_half (C : Q') (hC : (0 : Q') ≤ C) :
    counterStep C hC < half :=
  Q'.lt_of_le_of_lt (counterStep_bounds C hC).2.1 (by decide)

/-- Every proposed coefficient has a computed positive bare heat margin
that violates the ORIGINAL cleared relative-energy bound, even with the
exact positive ground pin and uniformly bounded action. -/
theorem counterStep_ground_bound_false (C : Q') (hC : (0 : Q') ≤ C) :
    ¬ (edgePartition (counterStep C hC) * groundEnergy (counterStep C hC) ≤
      (C * counterStep C hC) * determinantVariance (counterStep C hC)) := by
  let e := counterStep C hC
  have hb := counterStep_bounds C hC
  have hh : e < half := counterStep_lt_half C hC
  have hv := Q'.le_of_lt (determinant_positive hb.1 hh)
  have hsmall : (2 : Q') * (C*e) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 2 hb.2.2 (by decide))
      (by decide)
  intro hbound
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ 2 hbound (by decide)
  have hright : (2 : Q')*((C*e)*determinantVariance e) ≤ determinantVariance e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall hv)
        (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  have hleft : (2 : Q')*(edgePartition e*groundEnergy e) ≈
      (2 : Q')*edgePartition e*groundEnergy e := Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hbad : (2 : Q')*edgePartition e*groundEnergy e ≤ determinantVariance e :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled hright)
  exact (Int.not_le.mpr (energy_relative_obstruction hb.1 hh)) hbad

/-- SAME original edge-law mean; no replacement density is used. -/
def normalizedMean {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < half) : Q' :=
  sourceMomentOne e * Q'.recipPos (edgePartition e) (edgePartition_positive he0 hehalf)

/-- Actual source variance about that OWN mean, normalized by the original
positive partition, not by a source norm or its determinant. -/
def normalizedVariance {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < half) : Q' :=
  sourceMomentTwo e * Q'.recipPos (edgePartition e) (edgePartition_positive he0 hehalf) -
    normalizedMean he0 hehalf * normalizedMean he0 hehalf

/-- Energy normalized by the SAME original edge partition. -/
def normalizedEnergy {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < half) : Q' :=
  groundEnergy e * Q'.recipPos (edgePartition e) (edgePartition_positive he0 hehalf)

/-- Exact pin to the actual OWN variance; only the positive partition was
inverted, and the determinant may not be canceled. -/
theorem normalizedVariance_cleared {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < half) :
    (edgePartition e * edgePartition e) * normalizedVariance he0 hehalf ≈
      determinantVariance e := by
  let z := edgePartition e
  let a := sourceMomentOne e
  let b := sourceMomentTwo e
  let r := Q'.recipPos z (edgePartition_positive he0 hehalf)
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z (edgePartition_positive he0 hehalf)
  have hrr : (z*r)*(z*r) ≈ (1 : Q')*1 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hr) (Q'.mul_eqv_congr_left _ _ _ hr)
  have hp : (z*z)*(b*r-(a*r)*(a*r)) ≈
      (z*b)*(z*r)-(a*a)*((z*r)*(z*r)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.var 2) (.var 3))
          (.neg (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3))))))
      (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3)))
        (.neg (.mul (.mul (.var 1) (.var 1))
          (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 3))))))
      (by decide) (fun | 0 => z | 1 => a | 2 => b | _ => r)
  have hc := Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (z*b) _ _ hr)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (a*a) _ _ hrr))
  exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ hc
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 2)) (.const 1))
        (.neg (.mul (.mul (.var 1) (.var 1)) (.mul (.const 1) (.const 1)))))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => z | 1 => a | _ => b)))

/-- The actual OWN-centered source is nonconstant in its original law. -/
theorem normalizedVariance_positive {e : Q'} (he0 : (0 : Q') < e) (hehalf : e < half) :
    (0 : Q') < normalizedVariance he0 hehalf := by
  apply Int.not_le.mp
  intro hv
  have hz := Q'.le_of_lt (Q'.mul_pos (edgePartition_positive he0 hehalf)
    (edgePartition_positive he0 hehalf))
  have hbad : determinantVariance e ≤ (0 : Q') := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (normalizedVariance_cleared he0 hehalf))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hv hz)
      (Q'.le_of_eqv (Q'.mul_zero_eqv _)))
  exact (Int.not_le.mpr (determinant_positive he0 hehalf)) hbad

private theorem normalized_comparison_cleared {e : Q'}
    (he0 : (0 : Q') < e) (hehalf : e < half) (C : Q')
    (he : normalizedEnergy he0 hehalf ≤ (C*e)*normalizedVariance he0 hehalf) :
    edgePartition e*groundEnergy e ≤ (C*e)*determinantVariance e := by
  let z := edgePartition e
  let r := Q'.recipPos z (edgePartition_positive he0 hehalf)
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z (edgePartition_positive he0 hehalf)
  have hE : (z*z)*normalizedEnergy he0 hehalf ≈ z*groundEnergy e := by
    unfold normalizedEnergy
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => z | 1 => groundEnergy e | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _))
  have hV : (z*z)*((C*e)*normalizedVariance he0 hehalf) ≈ (C*e)*determinantVariance e :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => z*z | 1 => C*e | _ => normalizedVariance he0 hehalf))
      (Q'.mul_eqv_congr_left _ _ _ (normalizedVariance_cleared he0 hehalf))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hE)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (z*z) he
        (Q'.le_of_lt (Q'.mul_pos (edgePartition_positive he0 hehalf)
          (edgePartition_positive he0 hehalf)))) (Q'.le_of_eqv hV))

/-- No nonnegative rational coefficient gives a generic O(e) OWN-variance
initial-energy bound: the heat step is a constructed witness for each C. -/
theorem counterStep_normalized_ground_bound_false (C : Q') (hC : (0 : Q') ≤ C) :
    let e := counterStep C hC
    let he0 := (counterStep_bounds C hC).1
    let hehalf := counterStep_lt_half C hC
    ¬ (normalizedEnergy he0 hehalf ≤ (C*e)*normalizedVariance he0 hehalf) := by
  dsimp only
  intro h
  exact counterStep_ground_bound_false C hC
    (normalized_comparison_cleared (counterStep_bounds C hC).1
      (counterStep_lt_half C hC) C h)

/-- A Type-level family carrying its heat step, admissibility, nonzero
original variance and failed rate. No existence witness is erased. -/
def counterexample (C : Q') (hC : (0 : Q') ≤ C) :
    Σ' e : Q', Σ' he0 : (0 : Q') < e, Σ' hehalf : e < half,
      (0 : Q') < normalizedVariance he0 hehalf ∧
      ¬ (normalizedEnergy he0 hehalf ≤ (C*e)*normalizedVariance he0 hehalf) :=
  ⟨counterStep C hC, (counterStep_bounds C hC).1, counterStep_lt_half C hC,
    normalizedVariance_positive (counterStep_bounds C hC).1 (counterStep_lt_half C hC),
    counterStep_normalized_ground_bound_false C hC⟩

#print axioms counterStep_ground_bound_false
#print axioms normalizedVariance_cleared
#print axioms normalizedVariance_positive
#print axioms counterStep_normalized_ground_bound_false
#print axioms counterexample

end YMGap.Continuum.PositiveHeatGroundEnergyNoUniformRate
