/-
# A low bare heat mode does not give a source-uniform small energy ratio

On a two-state symmetric Markov heat, f=(1,-1) has the EXACT bare eigenvalue
1-2h. The positive source q=(1,h^2) nevertheless has original bridge energy
at least one half of its OWN centered bridge variance, for 0<h<=1/4.
For every proposed nonnegative coefficient C, the computed h=1/[4(C+1)]
therefore refutes E<=C*h*Var. All mass, mean and variance refer to q*P(q).

This is an abstract finite-chain obstruction to a positivity/heat-mode-only
argument. It is NOT a Wilson terminal source or a Yang--Mills counterexample.
The actual original source contrast/signed-remainder estimate remains open.
The pairing below uses counting measure; normalizing it to the uniform
probability measure scales both raw energy and mass by the same factor.
-/

import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.Soundness
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.PositiveSourceHeatModeScalingObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def quarter : Q' := Q'.mkPos 1 4 (by decide)
def half : Q' := Q'.mkPos 1 2 (by decide)

abbrev Vector := Bool → Q'

def pair (u v : Vector) : Q' := u false*v false+u true*v true
def times (u v : Vector) : Vector := fun b => u b*v b
def unit : Vector := fun _ => 1
def probe : Vector := fun | false => 1 | true => -1
def source (h : Q') : Vector := fun | false => 1 | true => h*h
def heat (h : Q') (u : Vector) : Vector :=
  fun b => ((1 : Q')-h)*u b+h*u (!b)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem positive_of_eqv {a b : Q'} (h : a ≈ b) (hb : (0 : Q') < b) :
    (0 : Q') < a := by
  exact Int.not_le.mp (by
    intro ha
    exact (Int.not_le.mpr hb) (Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) ha))

private theorem lt_of_sub_pos {a b : Q'} (h : (0 : Q') < b-a) : a < b := by
  have hn := Q'.num_pos_of_pos h
  change (0 : Int) < b.num*(a.den : Int)+(-a.num)*(b.den : Int) at hn
  change a.num*(b.den : Int) < b.num*(a.den : Int)
  rw [Int.neg_mul] at hn
  omega

private theorem sub_pos_of_lt {a b : Q'} (h : a < b) : (0 : Q') < b-a := by
  change a.num*(b.den : Int) < b.num*(a.den : Int) at h
  apply Q'.lt_of_le_of_lt (Q'.le_of_eqv (by decide : (0 : Q') ≈ 0))
  change (0 : Int)*(b-a).den < (b-a).num*(1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  change (0 : Int) < b.num*(a.den : Int)+(-a.num)*(b.den : Int)
  rw [Int.neg_mul]
  omega

/-- The two heat coefficients are nonnegative and sum to one. -/
theorem heat_markov {h : Q'} (h0 : (0 : Q') ≤ h) (h1 : h ≤ (1 : Q')) :
    (0 : Q') ≤ (1 : Q')-h ∧ (0 : Q') ≤ h ∧ ((1 : Q')-h)+h ≈ 1 :=
  ⟨Q'.sub_nonneg_of_le h1, h0,
    poly_identity_of_normal_eq (.add (.add (.const 1) (.neg (.var 0))) (.var 0))
      (.const 1) (by decide) (fun _ => h)⟩

theorem heat_unit (h : Q') (b : Bool) : heat h unit b ≈ 1 := by
  cases b <;> exact poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const 1))
      (.mul (.var 0) (.const 1))) (.const 1) (by decide) (fun _ => h)

/-- Symmetry is with respect to the SAME counting pairing. -/
theorem heat_selfAdjoint (h : Q') (u v : Vector) :
    pair u (heat h v) ≈ pair (heat h u) v :=
  poly_identity_of_normal_eq
    (.add
      (.mul (.var 0) (.add (.mul (.add (.const 1) (.neg (.var 4))) (.var 2))
        (.mul (.var 4) (.var 3))))
      (.mul (.var 1) (.add (.mul (.add (.const 1) (.neg (.var 4))) (.var 3))
        (.mul (.var 4) (.var 2)))))
    (.add
      (.mul (.add (.mul (.add (.const 1) (.neg (.var 4))) (.var 0))
        (.mul (.var 4) (.var 1))) (.var 2))
      (.mul (.add (.mul (.add (.const 1) (.neg (.var 4))) (.var 1))
        (.mul (.var 4) (.var 0))) (.var 3)))
    (by decide) (fun | 0 => u false | 1 => u true | 2 => v false | 3 => v true | _ => h)

/-- The SAME heat is a contraction for every vector, not merely for the probe. -/
theorem heat_contraction {h : Q'} (h0 : (0 : Q') ≤ h) (h1 : h ≤ (1 : Q'))
    (u : Vector) : pair (heat h u) (heat h u) ≤ pair u u := by
  have he : pair u u-pair (heat h u) (heat h u) ≈
      (2*h*((1 : Q')-h))*((u false-u true)*(u false-u true)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.neg (.add
          (.mul (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0))
              (.mul (.var 2) (.var 1)))
            (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0))
              (.mul (.var 2) (.var 1))))
          (.mul (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 1))
              (.mul (.var 2) (.var 0)))
            (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 1))
              (.mul (.var 2) (.var 0)))))))
      (.mul (.mul (.mul (.const 2) (.var 2)) (.add (.const 1) (.neg (.var 2))))
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1)))))
      (by decide) (fun | 0 => u false | 1 => u true | _ => h)
  have hp : (0 : Q') ≤ (2*h*((1 : Q')-h))*((u false-u true)*(u false-u true)) :=
    Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) h0)
      (Q'.sub_nonneg_of_le h1))
    (SumOfSquares.q_mul_self_nonneg (u false-u true))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv he))

/-- The heat is positive semidefinite, not just entrywise nonnegative. -/
theorem heat_positive {h : Q'} (h0 : (0 : Q') ≤ h) (hh : h ≤ half) (u : Vector) :
    (0 : Q') ≤ pair u (heat h u) := by
  have he : pair u (heat h u) ≈
      ((1 : Q')-2*h)*(u false*u false+u true*u true)+
        h*((u false+u true)*(u false+u true)) :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.var 0) (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0))
          (.mul (.var 2) (.var 1))))
        (.mul (.var 1) (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 1))
          (.mul (.var 2) (.var 0)))))
      (.add
        (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 2))))
          (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
        (.mul (.var 2) (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))))
      (by decide) (fun | 0 => u false | 1 => u true | _ => h)
  have h2 : (2 : Q')*h ≤ 1 := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 hh (by decide))
    (Q'.le_of_eqv (by decide : (2 : Q')*half ≈ 1))
  have hs : (0 : Q') ≤ u false*u false+u true*u true :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q') ≈ 0+0))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ 0 (SumOfSquares.q_mul_self_nonneg (u false)))
        (Q'.add_le_add_left _ _ _ (SumOfSquares.q_mul_self_nonneg (u true))))
  have hp := Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le h2) hs
  have hq := Q'.mul_nonneg _ _ h0
    (SumOfSquares.q_mul_self_nonneg (u false+u true))
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ hp (Q'.add_le_self_of_nonneg _ _ hq)) (Q'.ge_of_eqv he)

/-- Exact low bare eigenmode; there is no interacting eigenrelation here. -/
theorem heat_probe (h : Q') (b : Bool) :
    heat h probe b ≈ ((1 : Q')-2*h)*probe b := by
  cases b
  · exact poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const 1))
        (.mul (.var 0) (.const (-1))))
      (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (.const 1))
      (by decide) (fun _ => h)
  · exact poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const (-1)))
        (.mul (.var 0) (.const 1)))
      (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (.const (-1)))
      (by decide) (fun _ => h)

theorem source_positive {h : Q'} (h0 : (0 : Q') < h) (b : Bool) :
    (0 : Q') < source h b := by
  cases b
  · change (0 : Q') < 1; decide
  · exact Q'.mul_pos h0 h0

/-- Actual bridge weight q*P(q), not q^2 or a supplied variance proxy. -/
def weight (h : Q') : Vector := times (source h) (heat h (source h))
def mass (h : Q') : Q' := pair (weight h) unit
def firstMoment (h : Q') : Q' := pair (weight h) probe
def secondMoment (h : Q') : Q' := pair (weight h) (times probe probe)
def energy (h : Q') : Q' :=
  secondMoment h-pair (times (source h) probe) (heat h (times (source h) probe))
def varianceNumerator (h : Q') : Q' :=
  mass h*secondMoment h-firstMoment h*firstMoment h

private def A (h : Q') : Q' := (1 : Q')-h+h*h*h
private def R (h : Q') : Q' := (1 : Q')+h*((1 : Q')-h)
private def B (h : Q') : Q' := (h*h*h)*R h

private theorem weight_zero (h : Q') : weight h false ≈ A h :=
  poly_identity_of_normal_eq
    (.mul (.const 1) (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const 1))
      (.mul (.var 0) (.mul (.var 0) (.var 0)))))
    (.add (.add (.const 1) (.neg (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.var 0)))
    (by decide) (fun _ => h)

private theorem weight_one (h : Q') : weight h true ≈ B h :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0))
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 0) (.var 0)))
        (.mul (.var 0) (.const 1))))
    (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0))
      (.add (.const 1) (.mul (.var 0) (.add (.const 1) (.neg (.var 0))))))
    (by decide) (fun _ => h)

private theorem moments (h : Q') :
    mass h ≈ A h+B h ∧ firstMoment h ≈ A h-B h ∧ secondMoment h ≈ A h+B h := by
  have m := Q'.add_eqv_congr' (weight_zero h) (weight_one h)
  have hm : mass h ≈ weight h false+weight h true :=
    Q'.add_eqv_congr' (Q'.mul_one_eqv _) (Q'.mul_one_eqv _)
  have hf : firstMoment h ≈ weight h false-weight h true :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.const 1)) (.mul (.var 1) (.const (-1))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => weight h false | _ => weight h true)
  have hs : secondMoment h ≈ weight h false+weight h true :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.const 1) (.const 1)))
        (.mul (.var 1) (.mul (.const (-1)) (.const (-1)))))
      (.add (.var 0) (.var 1)) (by decide)
      (fun | 0 => weight h false | _ => weight h true)
  exact ⟨Q'.eqv_trans _ _ _ hm m,
    Q'.eqv_trans _ _ _ hf (Q'.add_eqv_congr' (weight_zero h)
      (Q'.neg_eqv_congr _ _ (weight_one h))), Q'.eqv_trans _ _ _ hs m⟩

theorem energy_pin (h : Q') : energy h ≈ 4*(h*h*h) :=
  poly_identity_of_normal_eq
    (.add
      (.add
        (.mul (.mul (.const 1)
          (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const 1))
            (.mul (.var 0) (.mul (.var 0) (.var 0))))) (.mul (.const 1) (.const 1)))
        (.mul (.mul (.mul (.var 0) (.var 0))
          (.add (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 0) (.var 0)))
            (.mul (.var 0) (.const 1)))) (.mul (.const (-1)) (.const (-1)))))
      (.neg (.add
        (.mul (.mul (.const 1) (.const 1))
          (.add (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.const 1) (.const 1)))
            (.mul (.var 0) (.mul (.mul (.var 0) (.var 0)) (.const (-1))))))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.const (-1)))
          (.add (.mul (.add (.const 1) (.neg (.var 0)))
            (.mul (.mul (.var 0) (.var 0)) (.const (-1))))
            (.mul (.var 0) (.mul (.const 1) (.const 1))))))))
    (.mul (.const 4) (.mul (.mul (.var 0) (.var 0)) (.var 0)))
    (by decide) (fun _ => h)

theorem varianceNumerator_pin (h : Q') : varianceNumerator h ≈ 4*(A h*B h) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (qmul (moments h).1 (moments h).2.2)
      (Q'.neg_eqv_congr _ _ (qmul (moments h).2.1 (moments h).2.1)))
    (poly_identity_of_normal_eq
      (.add (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
        (.neg (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))))
      (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => A h | _ => B h))

private theorem factors {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) :
    (0 : Q') < A h ∧ (0 : Q') < B h ∧ R h ≤ 2 := by
  have hh : h < (1 : Q') := Q'.lt_of_le_of_lt hq (by decide : quarter < (1 : Q'))
  have hgap : (0 : Q') < (1 : Q')-h := sub_pos_of_lt hh
  have hc : (0 : Q') < h*h*h := Q'.mul_pos (Q'.mul_pos h0 h0) h0
  have hA : (0 : Q') < A h := Q'.add_pos hgap hc
  have hR : (0 : Q') < R h := Q'.add_pos (by decide) (Q'.mul_pos h0 hgap)
  have hB : (0 : Q') < B h := Q'.mul_pos hc hR
  have hgap_le : (1 : Q')-h ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt h0)))
      (Q'.le_of_eqv (by decide : (1 : Q') + -0 ≈ 1))
  have hp : h*((1 : Q')-h) ≤ h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ h hgap_le (Q'.le_of_lt h0))
    (Q'.le_of_eqv (Q'.mul_one_eqv h))
  have hRle : R h ≤ 2 := Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ hp)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.le_of_lt hh))
      (Q'.le_of_eqv (by decide : (1 : Q')+1 ≈ 2)))
  exact ⟨hA, hB, hRle⟩

theorem mass_positive {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) :
    (0 : Q') < mass h :=
  positive_of_eqv (moments h).1 (Q'.add_pos (factors h0 hq).1 (factors h0 hq).2.1)

theorem varianceNumerator_positive {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) :
    (0 : Q') < varianceNumerator h :=
  positive_of_eqv (varianceNumerator_pin h)
    (Q'.mul_pos (by decide) (Q'.mul_pos (factors h0 hq).1 (factors h0 hq).2.1))

def normalizedMean {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) : Q' :=
  firstMoment h*Q'.recipPos (mass h) (mass_positive h0 hq)

def normalizedVariance {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) : Q' :=
  secondMoment h*Q'.recipPos (mass h) (mass_positive h0 hq)-
    normalizedMean h0 hq*normalizedMean h0 hq

def normalizedEnergy {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) : Q' :=
  energy h*Q'.recipPos (mass h) (mass_positive h0 hq)

/-- The numerator is pinned to the ACTUAL normalized variance at its own mean.
Only the positive original mass is inverted. -/
theorem normalizedVariance_cleared {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) :
    (mass h*mass h)*normalizedVariance h0 hq ≈ varianceNumerator h := by
  let z := mass h
  let a := firstMoment h
  let b := secondMoment h
  let r := Q'.recipPos z (mass_positive h0 hq)
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z (mass_positive h0 hq)
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
  have hc : (z*b)*(z*r)-(a*a)*((z*r)*(z*r)) ≈ (z*b)*1-(a*a)*(1*1) :=
    Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hr)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (qmul hr hr)))
  exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ hc
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 2)) (.const 1))
        (.neg (.mul (.mul (.var 1) (.var 1)) (.mul (.const 1) (.const 1)))))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => z | 1 => a | _ => b)))

theorem normalizedVariance_positive {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) :
    (0 : Q') < normalizedVariance h0 hq := by
  apply Int.not_le.mp
  intro hv
  have hz := Q'.le_of_lt (Q'.mul_pos (mass_positive h0 hq) (mass_positive h0 hq))
  have hn : varianceNumerator h ≤ 0 := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (normalizedVariance_cleared h0 hq))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hv hz)
      (Q'.le_of_eqv (Q'.mul_zero_eqv _)))
  exact (Int.not_le.mpr (varianceNumerator_positive h0 hq)) hn

attribute [local irreducible] mass firstMoment secondMoment energy varianceNumerator
  normalizedMean normalizedVariance normalizedEnergy

/-- The OWN bridge variance is nonzero, but its energy ratio does not shrink.
This cleared statement is exactly E >= (1/2)*Var after normalization by Z. -/
theorem half_variance_energy_floor {h : Q'} (h0 : (0 : Q') < h) (hq : h ≤ quarter) :
    half*varianceNumerator h ≤ mass h*energy h := by
  have hA := (factors h0 hq).1
  have hB := (factors h0 hq).2.1
  have hR := (factors h0 hq).2.2
  have hc := Q'.le_of_lt (Q'.mul_pos (Q'.mul_pos h0 h0) h0)
  have hAR : A h*R h ≤ (2 : Q')*(A h+B h) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (A h) hR (Q'.le_of_lt hA))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ 2
          (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hB)) (by decide)))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (2*(h*h*h)) hAR
    (Q'.mul_nonneg _ _ (by decide) hc)
  have hl : half*varianceNumerator h ≈ (2*(h*h*h))*(A h*R h) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ (varianceNumerator_pin h))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half 4 (A h*B h)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (A h*B h) (by decide : half*4 ≈ (2 : Q')))
          (poly_identity_of_normal_eq
            (.mul (.const 2) (.mul (.var 0) (.mul (.var 1) (.var 2))))
            (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2)))
            (by decide) (fun | 0 => A h | 1 => h*h*h | _ => R h))))
  have hr : (2*(h*h*h))*(2*(A h+B h)) ≈ mass h*energy h :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
        (.mul (.var 1) (.mul (.const 4) (.var 0))) (by decide)
        (fun | 0 => h*h*h | _ => A h+B h))
      (qmul (Q'.eqv_symm (moments h).1) (Q'.eqv_symm (energy_pin h)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

private theorem denominator_positive (C : Q') (hC : (0 : Q') ≤ C) :
    (0 : Q') < 4*(C+1) :=
  Q'.mul_pos (by decide) (positive_of_eqv (Q'.add_comm_eqv C 1)
    (Q'.pos_add_nonneg (by decide) hC))

/-- Computed rational heat step; no existence witness is erased. -/
def counterStep (C : Q') (hC : (0 : Q') ≤ C) : Q' :=
  Q'.recipPos (4*(C+1)) (denominator_positive C hC)

private theorem counterStep_pin (C : Q') (hC : (0 : Q') ≤ C) :
    C*counterStep C hC+counterStep C hC ≈ quarter := by
  let h := counterStep C hC
  have hbase : C*h+h ≈ (C+1)*h :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.var 1))
      (.mul (.add (.var 0) (.const 1)) (.var 1)) (by decide)
      (fun | 0 => C | _ => h)
  have hu : (C+1)*h ≈ (quarter*4)*((C+1)*h) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
      (Q'.mul_eqv_congr_right _ _ _ (by decide : (1 : Q') ≈ quarter*4))
  have halg : (quarter*4)*((C+1)*h) ≈ quarter*((4*(C+1))*h) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 2) (.const 4)) (.mul (.add (.var 0) (.const 1)) (.var 1)))
      (.mul (.var 2) (.mul (.mul (.const 4) (.add (.var 0) (.const 1))) (.var 1)))
      (by decide) (fun | 0 => C | 1 => h | _ => quarter)
  exact Q'.eqv_trans _ _ _ hbase (Q'.eqv_trans _ _ _ hu
    (Q'.eqv_trans _ _ _ halg (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left quarter _ _
        (Q'.mul_recipPos_eqv (4*(C+1)) (denominator_positive C hC)))
      (Q'.mul_one_eqv quarter))))

theorem counterStep_bounds (C : Q') (hC : (0 : Q') ≤ C) :
    (0 : Q') < counterStep C hC ∧ counterStep C hC ≤ quarter ∧
      C*counterStep C hC ≤ quarter := by
  have hp := Q'.recipPos_pos (4*(C+1)) (denominator_positive C hC)
  have hprod := Q'.mul_nonneg _ _ hC (Q'.le_of_lt hp)
  have he := counterStep_pin C hC
  exact ⟨hp,
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hprod)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) (Q'.le_of_eqv he)),
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hp)) (Q'.le_of_eqv he)⟩

/-- Uniform O(h) fails although the source is positive and f is an EXACT
low heat mode. The coefficient is arbitrary; h is constructed from it. -/
theorem counterStep_bound_false (C : Q') (hC : (0 : Q') ≤ C) :
    ¬ (mass (counterStep C hC)*energy (counterStep C hC) ≤
      (C*counterStep C hC)*varianceNumerator (counterStep C hC)) := by
  let h := counterStep C hC
  have hb := counterStep_bounds C hC
  have hv := varianceNumerator_positive hb.1 hb.2.1
  have hsmall : quarter*varianceNumerator h < half*varianceNumerator h :=
    lt_of_sub_pos (positive_of_eqv
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 2) (.var 0))))
        (.mul (.add (.var 1) (.neg (.var 2))) (.var 0)) (by decide)
        (fun | 0 => varianceNumerator h | 1 => half | _ => quarter))
        (Q'.mul_eqv_congr_right _ _ _ (by decide : half-quarter ≈ quarter)))
      (Q'.mul_pos (by decide) hv))
  have hc : (C*h)*varianceNumerator h < half*varianceNumerator h :=
    Q'.lt_of_le_of_lt
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hb.2.2 (Q'.le_of_lt hv)) hsmall
  intro he
  have bad := Q'.le_trans' _ _ _ (half_variance_energy_floor hb.1 hb.2.1) he
  exact (Int.not_le.mpr hc) bad

private theorem normalized_comparison_cleared {h : Q'}
    (h0 : (0 : Q') < h) (hq : h ≤ quarter) (C : Q')
    (he : normalizedEnergy h0 hq ≤ (C*h)*normalizedVariance h0 hq) :
    mass h*energy h ≤ (C*h)*varianceNumerator h := by
  let z := mass h
  let r := Q'.recipPos z (mass_positive h0 hq)
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z (mass_positive h0 hq)
  have hE : (z*z)*normalizedEnergy h0 hq ≈ z*energy h := by
    unfold normalizedEnergy
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => z | 1 => energy h | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _))
  have hV : (z*z)*((C*h)*normalizedVariance h0 hq) ≈ (C*h)*varianceNumerator h :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => z*z | 1 => C*h | _ => normalizedVariance h0 hq))
      (Q'.mul_eqv_congr_left _ _ _ (normalizedVariance_cleared h0 hq))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hE)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (z*z) he
        (Q'.le_of_lt (Q'.mul_pos (mass_positive h0 hq) (mass_positive h0 hq))))
      (Q'.le_of_eqv hV))

/-- Failure is on the ACTUAL normalized energy and its OWN normalized variance,
not merely on a cleared polynomial proxy. -/
theorem counterStep_normalized_bound_false (C : Q') (hC : (0 : Q') ≤ C) :
    let h0 := (counterStep_bounds C hC).1
    let hq := (counterStep_bounds C hC).2.1
    ¬ (normalizedEnergy h0 hq ≤
      (C*counterStep C hC)*normalizedVariance h0 hq) := by
  dsimp only
  intro he
  exact counterStep_bound_false C hC
    (normalized_comparison_cleared (counterStep_bounds C hC).1
      (counterStep_bounds C hC).2.1 C he)

/-- Type-level counterexample family for every proposed uniform coefficient. -/
def counterexample (C : Q') (hC : (0 : Q') ≤ C) :
    Σ' h : Q', Σ' h0 : (0 : Q') < h, Σ' hq : h ≤ quarter,
      (0 : Q') < normalizedVariance h0 hq ∧
      ¬ (normalizedEnergy h0 hq ≤ (C*h)*normalizedVariance h0 hq) :=
  ⟨counterStep C hC, (counterStep_bounds C hC).1, (counterStep_bounds C hC).2.1,
    normalizedVariance_positive (counterStep_bounds C hC).1 (counterStep_bounds C hC).2.1,
    counterStep_normalized_bound_false C hC⟩

#print axioms heat_markov
#print axioms heat_unit
#print axioms heat_selfAdjoint
#print axioms heat_contraction
#print axioms heat_positive
#print axioms heat_probe
#print axioms source_positive
#print axioms energy_pin
#print axioms varianceNumerator_pin
#print axioms mass_positive
#print axioms varianceNumerator_positive
#print axioms normalizedVariance_cleared
#print axioms normalizedVariance_positive
#print axioms half_variance_energy_floor
#print axioms counterStep_bounds
#print axioms counterStep_bound_false
#print axioms counterStep_normalized_bound_false
#print axioms counterexample

end YMGap.Continuum.PositiveSourceHeatModeScalingObstruction
