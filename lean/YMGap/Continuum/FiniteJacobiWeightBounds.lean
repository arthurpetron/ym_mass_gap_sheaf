/-
# Exact finite Jacobi weights are two Euler segments

For 0<Q<1 and j<=N, the ORIGINAL normalized Gaussian coefficient equals

  centeredWeight Q N j
    = segment Q (N-j) j * segment Q (N+j) (N-j).

Thus it lies in (0,1], without an infinite-product denominator. The finite
segment loss bounds give an explicit geometric bound on its deficit from
one. Outside j<=N the original q-binomial, and hence the weight, is zero.
The estimates depend explicitly on Q and N-j; no coupling-uniform gap or
uniform-in-all-j convergence to one is claimed.
-/

import YMGap.Continuum.FiniteEulerSegment

namespace YMGap.Continuum.FiniteJacobiWeightBounds

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinom
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.FiniteEulerSegment

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.add_num, Q'.add_den_cast, Cheb.mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The finite Euler denominators cancel to TWO explicit products. -/
theorem centeredWeight_eq_segments {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (N j : Nat) (hj : j ≤ N) :
    centeredWeight Q N j ≈ segment Q (N - j) j * segment Q (N + j) (N - j) := by
  have hleft := euler_split Q (N - j) j
  rw [show N - j + j = N by omega] at hleft
  have hright := euler_split Q (N + j) (N - j)
  rw [show N + j + (N - j) = N + N by omega] at hright
  apply Q'.mul_left_cancel_of_pos
    (HKPos.q_mul_pos (euler_pos hQ0 hQ1 (N + j)) (euler_pos hQ0 hQ1 (N - j)))
  calc (euler Q (N + j) * euler Q (N - j)) * centeredWeight Q N j
      ≈ centeredWeight Q N j * (euler Q (N + j) * euler Q (N - j)) := Q'.mul_comm_eqv _ _
    _ ≈ euler Q N * euler Q (N + N) := centeredWeight_mul_euler Q N j hj
    _ ≈ (euler Q (N - j) * segment Q (N - j) j)
          * (euler Q (N + j) * segment Q (N + j) (N - j)) :=
      Cheb.mul_eqv_congr _ _ _ _ hleft hright
    _ ≈ (euler Q (N + j) * euler Q (N - j))
          * (segment Q (N - j) j * segment Q (N + j) (N - j)) := by mul_add_ring

theorem centeredWeight_pos {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (N j : Nat) (hj : j ≤ N) :
    (0 : Q') < centeredWeight Q N j :=
  Q'.pos_of_lt_of_le
    (HKPos.q_mul_pos (segment_pos hQ0 hQ1 (N - j) j) (segment_pos hQ0 hQ1 (N + j) (N - j)))
    (Q'.ge_of_eqv (centeredWeight_eq_segments hQ0 hQ1 N j hj))

theorem centeredWeight_le_one {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (N j : Nat) (hj : j ≤ N) :
    centeredWeight Q N j ≤ (1 : Q') := by
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv (centeredWeight_eq_segments hQ0 hQ1 N j hj))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (segment_le_one hQ0 hQ1 (N + j) (N - j))
      (Q'.le_of_lt (segment_pos hQ0 hQ1 (N - j) j)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) (segment_le_one hQ0 hQ1 (N - j) j))

theorem centeredWeight_out_of_range (Q : Q') (N j : Nat) (hj : N < j) :
    centeredWeight Q N j ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qbin_out_of_range Q (N + N) (N + j) (by omega)))
    (Q'.mul_zero_eqv _)

/-- The normalized coefficients are bounded in [0,1] at ALL indices.
This supplies a common majorant for later Gaussian tail estimates. -/
theorem centeredWeight_bounds {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (N j : Nat) :
    (0 : Q') ≤ centeredWeight Q N j ∧ centeredWeight Q N j ≤ (1 : Q') := by
  by_cases hj : j ≤ N
  · exact ⟨Q'.le_of_lt (centeredWeight_pos hQ0 hQ1 N j hj), centeredWeight_le_one hQ0 hQ1 N j hj⟩
  · have hz := centeredWeight_out_of_range Q N j (by omega)
    exact ⟨Q'.ge_of_eqv hz, Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) Q'.zero_le_one⟩

private theorem product_loss {p q r s : Q'}
    (hp0 : (0 : Q') ≤ p) (hp1 : p ≤ (1 : Q')) (hs : (0 : Q') ≤ s)
    (hpr : (1 : Q') ≤ p + r) (hqs : (1 : Q') ≤ q + s) :
    (1 : Q') ≤ p * q + (r + s) := by
  have hp : p ≤ p * q + p * s := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_one_eqv p))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ p hqs hp0)
      (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _)))
  have hps : p * s ≤ s := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ s hp1 hs) (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hp' : p ≤ p * q + s := Q'.le_trans' _ _ _ hp (Q'.add_le_add_left _ _ _ hps)
  exact Q'.le_trans' _ _ _ hpr
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ r hp')
      (Q'.le_of_eqv (by mul_add_ring : (p * q + s) + r ≈ p * q + (r + s))))

/-- The explicit deficit majorant: 2 Q^n/(1-Q). -/
def lossBound (Q : Q') (n : Nat) : Q' := HKConvGen.geoTailBase 2 Q n

theorem lossBound_nonnegative {Q : Q'} (hQ0 : (0 : Q') ≤ Q) (n : Nat) :
    (0 : Q') ≤ lossBound Q n :=
  HKConvGen.geoTailBase_nonneg (by decide : (0 : Q') ≤ 2) hQ0 n

private theorem two_tails (Q : Q') (n : Nat) :
    HKConvGen.geoTailBase 1 Q n + HKConvGen.geoTailBase 1 Q n ≈ lossBound Q n := by
  calc HKConvGen.geoTailBase 1 Q n + HKConvGen.geoTailBase 1 Q n
      ≈ (2 : Q') * HKConvGen.geoTailBase 1 Q n := Q'.eqv_symm (Cheb.two_mul_eqv _)
    _ ≈ lossBound Q n := by unfold lossBound HKConvGen.geoTailBase; mul_add_ring

/-- The actual normalized coefficient approaches one when N-j grows.
The loss bound names its base and cutoff distance explicitly. -/
theorem one_le_centeredWeight_add_loss {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (N j : Nat) (hj : j ≤ N) :
    (1 : Q') ≤ centeredWeight Q N j + lossBound Q (N - j + 1) := by
  have h := product_loss
    (Q'.le_of_lt (segment_pos hQ0 hQ1 (N - j) j)) (segment_le_one hQ0 hQ1 (N - j) j)
    (HKConvGen.geoTailBase_nonneg Q'.zero_le_one (Q'.le_of_lt hQ0) (N + j + 1))
    (one_le_segment_add_tail hQ0 hQ1 (N - j) j)
    (one_le_segment_add_tail hQ0 hQ1 (N + j) (N - j))
  have htail : HKConvGen.geoTailBase 1 Q (N + j + 1)
      ≤ HKConvGen.geoTailBase 1 Q (N - j + 1) := by
    apply Q'.mul_le_mul_of_nonneg_right
    · exact Q'.mul_le_mul_of_nonneg_left _ _ 1
        (HKConvGen.pow_base_antitone (Q'.le_of_lt hQ0) (Q'.le_of_lt hQ1) (by omega)) Q'.zero_le_one
    · exact HKConv.divPos_nonneg Q'.zero_le_one
  apply Q'.le_trans' _ _ _ h
  apply Q'.le_trans' _ _ _
    (Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _ htail))
  exact Q'.le_of_eqv (Cheb.add_eqv_congr _ _ _ _
    (Q'.eqv_symm (centeredWeight_eq_segments hQ0 hQ1 N j hj)) (two_tails Q (N - j + 1)))

end YMGap.Continuum.FiniteJacobiWeightBounds

#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.centeredWeight_eq_segments
#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.centeredWeight_pos
#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.centeredWeight_le_one
#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.centeredWeight_out_of_range
#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.centeredWeight_bounds
#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.lossBound
#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.lossBound_nonnegative
#print axioms YMGap.Continuum.FiniteJacobiWeightBounds.one_le_centeredWeight_add_loss
