/-
Constructing the linear spacing modulus from summable one-step defects.

The continuum functional of `RegularLinearScalingLimit` asks for a
`RegularCReal.ModCauchy` witness for every observable.  This file constructs
that witness from the local output produced by a KP/polymer expansion:

  |E_{j+1}(o) - E_j(o)| <= C(o) (1/2)^j.

The only subtlety is that `ModCauchy.M` must be antitone in an arbitrary
positive rational tolerance.  Raw denominator cutoffs are not antitone.  We
therefore implement a bounded constructive *least* half-power cutoff.  Its
minimality proves antitonicity without choice or `Nat.find`.
-/

import YMGap.Continuum.RegularLinearScalingLimit
import YMGap.Continuum.RegularLinearSymmetryLimit
import YMGap.Continuum.KPLimit

namespace YMGap.Continuum.RegularLinearGeometricModulus

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.HamiltonianScalar

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

/-! ## 1. A constructive least half-power cutoff -/

/-- Scan the finite interval `0,...,B`, retaining the first index already
known to satisfy `half^n <= ε`, or advancing to the new endpoint. -/
def halfCutoffAux (ε : Q') : Nat → Nat
  | 0 => 0
  | B + 1 =>
      let m := halfCutoffAux ε B
      if half ^ m ≤ ε then m else B + 1

theorem halfCutoffAux_le (ε : Q') : ∀ B, halfCutoffAux ε B ≤ B
  | 0 => Nat.le_refl 0
  | B + 1 => by
      simp only [halfCutoffAux]
      split
      · exact Nat.le_trans (halfCutoffAux_le ε B) (Nat.le_succ B)
      · exact Nat.le_refl _

/-- If the endpoint has crossed the tolerance, the finite scan returns an
index which has crossed it. -/
theorem halfCutoffAux_spec (ε : Q') : ∀ B,
    half ^ B ≤ ε → half ^ (halfCutoffAux ε B) ≤ ε
  | 0, h => h
  | B + 1, h => by
      simp only [halfCutoffAux]
      split
      · assumption
      · exact h

/-- The scan returns the first crossing within its searched interval. -/
theorem halfCutoffAux_min (ε : Q') : ∀ B k,
    k ≤ B → half ^ k ≤ ε → halfCutoffAux ε B ≤ k
  | 0, k, hk, _ => by
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact Nat.le_refl 0
  | B + 1, k, hk, hpow => by
      simp only [halfCutoffAux]
      split
      next hprev =>
        by_cases hkn : k ≤ B
        · exact halfCutoffAux_min ε B k hkn hpow
        · have hkEq : k = B + 1 := by omega
          subst k
          exact Nat.le_trans (halfCutoffAux_le ε B) (Nat.le_succ B)
      next hnot =>
        by_cases hkn : k ≤ B
        · have hBpow : half ^ B ≤ ε :=
            Q'.le_trans' _ _ _ (half_pow_antitone k B hkn) hpow
          exact False.elim (hnot (halfCutoffAux_spec ε B hBpow))
        · omega

/-- The least half-power cutoff for a positive rational.  `ε.den` is only a
finite search bound; minimality, rather than the denominator itself, supplies
the monotonicity needed by `ModCauchy`. -/
def halfCutoff (ε : Q') : Nat := halfCutoffAux ε ε.den

theorem halfCutoff_spec (ε : Q') (hε : (0 : Q') < ε) :
    half ^ halfCutoff ε ≤ ε := by
  exact halfCutoffAux_spec ε ε.den (pow_half_le ε hε)

theorem halfCutoff_le_of_pow_le (ε : Q') (k : Nat)
    (hk : half ^ k ≤ ε) : halfCutoff ε ≤ k := by
  by_cases hkb : k ≤ ε.den
  · exact halfCutoffAux_min ε ε.den k hkb hk
  · exact Nat.le_trans (halfCutoffAux_le ε ε.den) (Nat.le_of_lt (Nat.lt_of_not_ge hkb))

/-- Smaller tolerance gives a later cutoff. -/
theorem halfCutoff_antitone {ε δ : Q'} (hδ : (0 : Q') < δ)
    (hδε : δ ≤ ε) : halfCutoff ε ≤ halfCutoff δ :=
  halfCutoff_le_of_pow_le ε (halfCutoff δ)
    (Q'.le_trans' _ _ _ (halfCutoff_spec δ hδ) hδε)

/-! ## 2. Rescaled geometric-tail cutoff -/

def tailAmplitude (C : Q') : Q' := Q'.ofNat 2 * C

def scaledTolerance (C ε : Q') : Q' :=
  ε * ExpUBInstance.oneOver1p (tailAmplitude C)

theorem tailAmplitude_nonneg (C : Q') (hC : (0 : Q') ≤ C) :
    (0 : Q') ≤ tailAmplitude C :=
  Q'.mul_nonneg _ _ (by decide) hC

theorem scaledTolerance_pos (C ε : Q') (hε : (0 : Q') < ε) :
    (0 : Q') < scaledTolerance C ε :=
  Q'.mul_pos hε (oneOver1p_pos (tailAmplitude C))

theorem scaledTolerance_mono_right (C : Q') {δ ε : Q'}
    (hδε : δ ≤ ε) : scaledTolerance C δ ≤ scaledTolerance C ε :=
  Q'.mul_le_mul_of_nonneg_right _ _ _ hδε
    (Q'.le_of_lt (oneOver1p_pos (tailAmplitude C)))

def geoOuterModulus (C ε : Q') : Nat := halfCutoff (scaledTolerance C ε)

theorem geoOuterModulus_mono (C : Q') (ε δ : Q')
    (hδ : (0 : Q') < δ) (hδε : δ ≤ ε) :
    geoOuterModulus C ε ≤ geoOuterModulus C δ := by
  apply halfCutoff_antitone (scaledTolerance_pos C δ hδ)
  exact scaledTolerance_mono_right C hδε

theorem geoTail_le_of_modulus (C : Q') (hC : (0 : Q') ≤ C)
    (ε : Q') (hε : (0 : Q') < ε) (n : Nat)
    (hn : geoOuterModulus C ε ≤ n) :
    geoTail C n ≤ ε := by
  have hp : half ^ n ≤ scaledTolerance C ε :=
    Q'.le_trans' _ _ _
      (half_pow_antitone (geoOuterModulus C ε) n hn)
      (halfCutoff_spec (scaledTolerance C ε) (scaledTolerance_pos C ε hε))
  have hA := tailAmplitude_nonneg C hC
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp hA) ?_
  simpa [tailAmplitude, scaledTolerance] using
    (key_bound (tailAmplitude C) ε hA (Q'.le_of_lt hε))

/-! ## 3. Geometric increments produce `ModCauchy` -/

/-- A two-sided `C half^j` one-step bound produces the exact regular-real
outer modulus required by constructive completeness. -/
def geoIncrementModCauchy (S : Nat → Q') (C : Q') (hC : (0 : Q') ≤ C)
    (hup : ∀ j, S (j + 1) ≤ S j + geoIncr C j)
    (hlo : ∀ j, S j ≤ S (j + 1) + geoIncr C j) :
    ModCauchy (fun j => ofQ' (S j)) where
  M := geoOuterModulus C
  Mmono := geoOuterModulus_mono C
  bound := by
    intro ε hε i j hi hj k
    change S i ≤ S j + ε ∧ S j ≤ S i + ε
    rcases Nat.le_total i j with hij | hji
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      have ht := geoTail_le_of_modulus C hC ε hε i hi
      refine ⟨?_, ?_⟩
      · refine Q'.le_trans' _ _ _ (telescope_lo S (geoIncr C) hlo i d) ?_
        exact Q'.add_le_add_left _ _ _
          (Q'.le_trans' _ _ _ (geoTail_series_le C hC i d) ht)
      · refine Q'.le_trans' _ _ _ (telescope_up S (geoIncr C) hup i d) ?_
        exact Q'.add_le_add_left _ _ _
          (Q'.le_trans' _ _ _ (geoTail_series_le C hC i d) ht)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
      have ht := geoTail_le_of_modulus C hC ε hε j hj
      refine ⟨?_, ?_⟩
      · refine Q'.le_trans' _ _ _ (telescope_up S (geoIncr C) hup j d) ?_
        exact Q'.add_le_add_left _ _ _
          (Q'.le_trans' _ _ _ (geoTail_series_le C hC j d) ht)
      · refine Q'.le_trans' _ _ _ (telescope_lo S (geoIncr C) hlo j d) ?_
        exact Q'.add_le_add_left _ _ _
          (Q'.le_trans' _ _ _ (geoTail_series_le C hC j d) ht)

/-- Per-observable geometric one-step control for a family of finite positive
linear functionals. -/
structure LinearGeometricIncrementFamily (A : LinearObsAlg) where
  atSpacing : Nat → QLinearFunctional A
  amplitude : A.carrier → Q'
  amplitude_nonneg : ∀ o, (0 : Q') ≤ amplitude o
  step_upper : ∀ o j,
    (atSpacing (j + 1)).E o ≤ (atSpacing j).E o + geoIncr (amplitude o) j
  step_lower : ∀ o j,
    (atSpacing j).E o ≤ (atSpacing (j + 1)).E o + geoIncr (amplitude o) j

/-- Main constructor: summable local spacing defects synthesize the formerly
opaque `LinearScalingLimitModulus`. -/
def LinearGeometricIncrementFamily.toScalingLimitModulus
    {A : LinearObsAlg} (F : LinearGeometricIncrementFamily A) :
    LinearScalingLimitModulus A where
  atSpacing := F.atSpacing
  modOf := fun o => geoIncrementModCauchy
    (fun j => (F.atSpacing j).E o) (F.amplitude o) (F.amplitude_nonneg o)
    (F.step_upper o) (F.step_lower o)

/-! ## 4. Nonzero-tail validation -/

theorem geoPolymer_step_upper (j : Nat) :
    geoPolymerSum (j + 1) ≤ geoPolymerSum j + geoIncr 1 j := by
  rw [geoPolymerSum_succ]
  exact Q'.add_le_add_left _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv (half ^ j))))

theorem geoPolymer_step_lower (j : Nat) :
    geoPolymerSum j ≤ geoPolymerSum (j + 1) + geoIncr 1 j := by
  rw [geoPolymerSum_succ]
  refine Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (geoPolymerSum j) (half ^ j)
      (Q'.pow_nonneg half half_nonneg j)) ?_
  exact Q'.add_le_self_of_nonneg _ _ (geoIncr_nonneg 1 Q'.zero_le_one j)

def geoPolymerRegularModCauchy :
    ModCauchy (fun j => ofQ' (geoPolymerSum j)) :=
  geoIncrementModCauchy geoPolymerSum 1 Q'.zero_le_one
    geoPolymer_step_upper geoPolymer_step_lower

/-! ## 5. A genuinely moving family of positive linear functionals -/

open YMGap.Continuum.RegularLinearSymmetryLimit (planeLinearAlg)

/-- On the plane algebra, the second-coordinate coefficient follows the
nonconstant geometric polymer partial sum.  Positivity is independent of that
coefficient because every star-square has second coordinate zero. -/
def movingPlaneFunctional (j : Nat) : QLinearFunctional planeLinearAlg where
  E := fun a => a.1 + geoPolymerSum j * a.2
  normalized := by
    change ((1 : Q') + geoPolymerSum j * 0).eqv 1
    exact Q'.eqv_trans _ _ _
      (QPoly.q_add_congr (Q'.eqv_refl 1) (Q'.mul_zero_eqv (geoPolymerSum j)))
      (QPoly.q_add_zero_eqv 1)
  positive := by
    intro a
    change (0 : Q') ≤ (a.1 * a.1 + a.2 * a.2) + geoPolymerSum j * 0
    exact Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _
        (SumOfSquares.q_mul_self_nonneg a.1)
        (SumOfSquares.q_mul_self_nonneg a.2))
      (Q'.ge_of_eqv
        (Q'.eqv_trans _ _ _
          (QPoly.q_add_congr (Q'.eqv_refl _)
            (Q'.mul_zero_eqv (geoPolymerSum j)))
          (QPoly.q_add_zero_eqv _)))
  additive := by
    intro a b
    change ((a.1 + b.1) + geoPolymerSum j * (a.2 + b.2)).eqv
      ((a.1 + geoPolymerSum j * a.2) + (b.1 + geoPolymerSum j * b.2))
    ring_qeqv
  homogeneous := by
    intro q a
    change (q * a.1 + geoPolymerSum j * (q * a.2)).eqv
      (q * (a.1 + geoPolymerSum j * a.2))
    ring_qeqv

private theorem add_increment_sub_base (X Y : Q') :
    ((X + Y) + -X).eqv Y := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (X + Y) (Y + X) (-X)
      (Q'.add_comm_eqv X Y)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv Y X (-X)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left Y (X + -X) 0 (Q'.add_neg_self_eqv X)) ?_
  exact QPoly.q_add_zero_eqv Y

private theorem base_sub_add_increment (X Y : Q') :
    (X + -(X + Y)).eqv (-Y) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left X (-(X + Y)) (-X + -Y)
      (Q'.neg_add_eqv X Y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv X (-X) (-Y))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (X + -X) 0 (-Y) (Q'.add_neg_self_eqv X)) ?_
  exact QPoly.q_zero_add_eqv (-Y)

theorem movingPlane_difference_forward (j : Nat) (o : Q' × Q') :
    ((movingPlaneFunctional (j + 1)).E o +
      -((movingPlaneFunctional j).E o)).eqv (half ^ j * o.2) := by
  change ((o.1 + geoPolymerSum (j + 1) * o.2) +
    -(o.1 + geoPolymerSum j * o.2)).eqv (half ^ j * o.2)
  rw [geoPolymerSum_succ]
  let X := o.1 + geoPolymerSum j * o.2
  let Y := half ^ j * o.2
  have hnew : (o.1 + (geoPolymerSum j + half ^ j) * o.2).eqv (X + Y) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left o.1 _ _
        (Q'.add_mul_eqv (geoPolymerSum j) (half ^ j) o.2)) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv o.1 (geoPolymerSum j * o.2) (half ^ j * o.2))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(o.1 + geoPolymerSum j * o.2)) hnew)
    (add_increment_sub_base X Y)

theorem movingPlane_difference_backward (j : Nat) (o : Q' × Q') :
    ((movingPlaneFunctional j).E o +
      -((movingPlaneFunctional (j + 1)).E o)).eqv (-(half ^ j * o.2)) := by
  change ((o.1 + geoPolymerSum j * o.2) +
    -(o.1 + geoPolymerSum (j + 1) * o.2)).eqv (-(half ^ j * o.2))
  rw [geoPolymerSum_succ]
  let X := o.1 + geoPolymerSum j * o.2
  let Y := half ^ j * o.2
  have hnew : (o.1 + (geoPolymerSum j + half ^ j) * o.2).eqv (X + Y) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left o.1 _ _
        (Q'.add_mul_eqv (geoPolymerSum j) (half ^ j) o.2)) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv o.1 (geoPolymerSum j * o.2) (half ^ j * o.2))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left X _ _ (Q'.neg_eqv_congr _ _ hnew))
    (base_sub_add_increment X Y)

theorem half_mul_le_abs_mul (j : Nat) (a : Q') :
    half ^ j * a ≤ Q'.abs a * half ^ j := by
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left a (Q'.abs a) (half ^ j)
      (Q'.le_abs_self a) (Q'.pow_nonneg half half_nonneg j)) ?_
  exact Q'.le_of_eqv (Q'.mul_comm_eqv (half ^ j) (Q'.abs a))

theorem neg_half_mul_le_abs_mul (j : Nat) (a : Q') :
    -(half ^ j * a) ≤ Q'.abs a * half ^ j := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_neg_eqv (half ^ j) a))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (-a) (Q'.abs a) (half ^ j)
      (Q'.neg_le_abs a) (Q'.pow_nonneg half half_nonneg j)) ?_
  exact Q'.le_of_eqv (Q'.mul_comm_eqv (half ^ j) (Q'.abs a))

def movingPlaneGeometricFamily :
    LinearGeometricIncrementFamily planeLinearAlg where
  atSpacing := movingPlaneFunctional
  amplitude := fun o => Q'.abs o.2
  amplitude_nonneg := fun o => Q'.abs_nonneg o.2
  step_upper := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (movingPlane_difference_forward j o))
      (half_mul_le_abs_mul j o.2)
  step_lower := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (movingPlane_difference_backward j o))
      (neg_half_mul_le_abs_mul j o.2)

def movingPlaneScalingLimit : LinearScalingLimitModulus planeLinearAlg :=
  movingPlaneGeometricFamily.toScalingLimitModulus

def movingPlaneContinuumFunctional : RegLinearFunctional planeLinearAlg :=
  linearFunctionalOfScalingLimit movingPlaneScalingLimit

/-- The validation family genuinely changes between stages on the second
coordinate; it is not a constant-tower loophole. -/
theorem movingPlane_stage_zero_ne_one :
    (movingPlaneFunctional 0).E ((0 : Q'), (1 : Q')) ≠
      (movingPlaneFunctional 1).E ((0 : Q'), (1 : Q')) := by
  change (0 : Q') ≠ 1
  decide

#print axioms halfCutoffAux
#print axioms halfCutoffAux_le
#print axioms halfCutoffAux_spec
#print axioms halfCutoffAux_min
#print axioms halfCutoff
#print axioms halfCutoff_spec
#print axioms halfCutoff_antitone
#print axioms geoOuterModulus_mono
#print axioms geoTail_le_of_modulus
#print axioms geoIncrementModCauchy
#print axioms LinearGeometricIncrementFamily
#print axioms LinearGeometricIncrementFamily.toScalingLimitModulus
#print axioms geoPolymerRegularModCauchy
#print axioms movingPlaneFunctional
#print axioms movingPlane_difference_forward
#print axioms movingPlaneGeometricFamily
#print axioms movingPlaneScalingLimit
#print axioms movingPlaneContinuumFunctional
#print axioms movingPlane_stage_zero_ne_one

end YMGap.Continuum.RegularLinearGeometricModulus
