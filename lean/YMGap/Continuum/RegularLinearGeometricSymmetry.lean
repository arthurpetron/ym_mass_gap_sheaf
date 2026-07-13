/-
Constructive symmetry restoration from a geometric finite-spacing defect.

`RegularLinearSymmetryLimit` transports an arbitrary eventually vanishing
finite-spacing defect to exact invariance of the continuum functional.  The
eventuality there is intentionally general, but the RG/polymer output has a
more concrete form:

  |E_j(g o) - E_j(o)| <= C(o) (1/2)^j.

This file turns that local geometric estimate into the required constructive
eventuality using the least half-power cutoff from
`RegularLinearGeometricModulus`.  No modulus remains to be selected.
-/

import YMGap.Continuum.RegularLinearGeometricModulus

namespace YMGap.Continuum.RegularLinearGeometricSymmetry

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.RegularLinearSymmetryLimit
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.HamiltonianScalar

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

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

private theorem flip_sub_forward (X Y : Q') :
    ((X + -Y) + -(X + Y)).eqv (-Y + -Y) := by
  have hneg : (-(X + Y)).eqv (-X + -Y) := Q'.neg_add_eqv X Y
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (X + -Y) _ _ hneg) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (X + -Y) (-X) (-Y))) ?_
  have hinner : ((X + -Y) + -X).eqv (-Y) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (X + -Y) (-Y + X) (-X)
        (Q'.add_comm_eqv X (-Y))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-Y) X (-X)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-Y) (X + -X) 0
        (Q'.add_neg_self_eqv X)) ?_
    exact QPoly.q_add_zero_eqv (-Y)
  exact Q'.add_eqv_congr_right _ _ (-Y) hinner

private theorem flip_sub_backward (X Y : Q') :
    ((X + Y) + -(X + -Y)).eqv (Y + Y) := by
  have hneg : (-(X + -Y)).eqv (-X + Y) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv X (-Y)) ?_
    exact Q'.add_eqv_congr_left (-X) (-(-Y)) Y (Q'.neg_neg_eqv Y)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (X + Y) _ _ hneg) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (X + Y) (-X) Y)) ?_
  have hinner : ((X + Y) + -X).eqv Y := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (X + Y) (Y + X) (-X)
        (Q'.add_comm_eqv X Y)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv Y X (-X)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left Y (X + -X) 0 (Q'.add_neg_self_eqv X)) ?_
    exact QPoly.q_add_zero_eqv Y
  exact Q'.add_eqv_congr_right _ _ Y hinner

/-! ## 1. Geometric finite-spacing symmetry defect -/

/-- A selected observable action whose two-sided finite-spacing defect is
bounded by `C(o) (1/2)^j`. -/
structure LinearGeometricSymmetryFamily (A : LinearObsAlg)
    (L : LinearScalingLimitModulus A) where
  map : A.carrier → A.carrier
  amplitude : A.carrier → Q'
  amplitude_nonneg : ∀ o, (0 : Q') ≤ amplitude o
  stage_upper : ∀ o j,
    (L.atSpacing j).E (map o) ≤
      (L.atSpacing j).E o + geoIncr (amplitude o) j
  stage_lower : ∀ o j,
    (L.atSpacing j).E o ≤
      (L.atSpacing j).E (map o) + geoIncr (amplitude o) j

/-- One geometric increment is bounded by the full geometric tail beginning
at the same scale. -/
theorem geoIncr_le_geoTail (C : Q') (hC : (0 : Q') ≤ C) (j : Nat) :
    geoIncr C j ≤ geoTail C j := by
  have hs := geoTail_series_le C hC j 1
  simpa [RationalTail.finSum, geoIncr, Nat.add_zero, Q'.zero_add'] using hs

/-- The geometric bound synthesizes the exact eventuality required by the
general continuum symmetry theorem. -/
def LinearGeometricSymmetryFamily.toDefect
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (G : LinearGeometricSymmetryFamily A L) : ScalingSymmetryDefect A L where
  map := G.map
  eventually_close := by
    intro o ε hε
    refine ⟨geoOuterModulus (G.amplitude o) ε, fun j hj => ?_⟩
    have ht := geoTail_le_of_modulus (G.amplitude o)
      (G.amplitude_nonneg o) ε hε j hj
    have hi : geoIncr (G.amplitude o) j ≤ ε :=
      Q'.le_trans' _ _ _
        (geoIncr_le_geoTail (G.amplitude o) (G.amplitude_nonneg o) j) ht
    exact ⟨
      Q'.le_trans' _ _ _ (G.stage_upper o j)
        (Q'.add_le_add_left _ _ _ hi),
      Q'.le_trans' _ _ _ (G.stage_lower o j)
        (Q'.add_le_add_left _ _ _ hi)⟩

/-- A geometric anisotropy estimate gives exact selected symmetry in the
constructive spacing limit. -/
theorem limitE_invariant_of_geometric_defect
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (G : LinearGeometricSymmetryFamily A L) (o : A.carrier) :
    Equiv (limitE L (G.map o)) (limitE L o) :=
  limitE_invariant_of_vanishing_defect G.toDefect o

/-! ## 2. A genuinely non-exact validation family -/

open YMGap.Continuum.RegularLinearSymmetryLimit (planeLinearAlg planeFlip)

/-- The second-coordinate coefficient is `(1/2)^j`, so every finite stage is
asymmetric under `planeFlip`, while the limiting functional forgets that
coordinate. -/
def tailPlaneFunctional (j : Nat) : QLinearFunctional planeLinearAlg where
  E := fun a => a.1 + half ^ j * a.2
  normalized := by
    change ((1 : Q') + half ^ j * 0).eqv 1
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ 0 (Q'.mul_zero_eqv (half ^ j)))
      (QPoly.q_add_zero_eqv 1)
  positive := by
    intro a
    change (0 : Q') ≤ (a.1 * a.1 + a.2 * a.2) + half ^ j * 0
    exact Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _
        (SumOfSquares.q_mul_self_nonneg a.1)
        (SumOfSquares.q_mul_self_nonneg a.2))
      (Q'.ge_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ 0 (Q'.mul_zero_eqv (half ^ j)))
          (QPoly.q_add_zero_eqv _)))
  additive := by
    intro a b
    change ((a.1 + b.1) + half ^ j * (a.2 + b.2)).eqv
      ((a.1 + half ^ j * a.2) + (b.1 + half ^ j * b.2))
    ring_qeqv
  homogeneous := by
    intro q a
    change (q * a.1 + half ^ j * (q * a.2)).eqv
      (q * (a.1 + half ^ j * a.2))
    ring_qeqv

theorem tailPlane_difference_forward (j : Nat) (o : Q' × Q') :
    ((tailPlaneFunctional (j + 1)).E o +
      -((tailPlaneFunctional j).E o)).eqv (-(half ^ (j + 1) * o.2)) := by
  let H := half ^ (j + 1) * o.2
  let B := o.1 + H
  have hpow : (half ^ j * o.2).eqv (H + H) := by
    change (half ^ j * o.2).eqv
      (half ^ (j + 1) * o.2 + half ^ (j + 1) * o.2)
    rw [Q'.pow_succ]
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (ExpNeg.two_halves (half ^ j * o.2))) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_assoc_eqv half (half ^ j) o.2))
      (Q'.eqv_symm (Q'.mul_assoc_eqv half (half ^ j) o.2))
  have hold : (o.1 + half ^ j * o.2).eqv (B + H) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left o.1 _ _ hpow) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv o.1 H H)
  change (B + -(o.1 + half ^ j * o.2)).eqv (-H)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left B _ _ (Q'.neg_eqv_congr _ _ hold)) ?_
  exact base_sub_add_increment B H

theorem tailPlane_difference_backward (j : Nat) (o : Q' × Q') :
    ((tailPlaneFunctional j).E o +
      -((tailPlaneFunctional (j + 1)).E o)).eqv (half ^ (j + 1) * o.2) := by
  let H := half ^ (j + 1) * o.2
  let B := o.1 + H
  have hpow : (half ^ j * o.2).eqv (H + H) := by
    change (half ^ j * o.2).eqv
      (half ^ (j + 1) * o.2 + half ^ (j + 1) * o.2)
    rw [Q'.pow_succ]
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (ExpNeg.two_halves (half ^ j * o.2))) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_assoc_eqv half (half ^ j) o.2))
      (Q'.eqv_symm (Q'.mul_assoc_eqv half (half ^ j) o.2))
  have hold : (o.1 + half ^ j * o.2).eqv (B + H) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left o.1 _ _ hpow) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv o.1 H H)
  change ((o.1 + half ^ j * o.2) + -B).eqv H
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-B) hold) ?_
  exact add_increment_sub_base B H

theorem abs_mul_half_succ_le (j : Nat) (a : Q') :
    Q'.abs a * half ^ (j + 1) ≤ Q'.abs a * half ^ j :=
  Q'.mul_le_mul_of_nonneg_left _ _ _
    (half_pow_antitone j (j + 1) (Nat.le_succ j)) (Q'.abs_nonneg a)

theorem half_pow_pos_local : ∀ j : Nat, (0 : Q') < half ^ j
  | 0 => CReal.pos_of_num_pos (by decide)
  | n + 1 => by
      rw [Q'.pow_succ]
      exact ExpNeg.half_mul_pos (half ^ n) (half_pow_pos_local n)

def tailPlaneGeometricFamily :
    LinearGeometricIncrementFamily planeLinearAlg where
  atSpacing := tailPlaneFunctional
  amplitude := fun o => Q'.abs o.2
  amplitude_nonneg := fun o => Q'.abs_nonneg o.2
  step_upper := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (tailPlane_difference_forward j o))
      (Q'.le_trans' _ _ _
        (neg_half_mul_le_abs_mul (j + 1) o.2)
        (abs_mul_half_succ_le j o.2))
  step_lower := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (tailPlane_difference_backward j o))
      (Q'.le_trans' _ _ _
        (half_mul_le_abs_mul (j + 1) o.2)
        (abs_mul_half_succ_le j o.2))

def tailPlaneScaling : LinearScalingLimitModulus planeLinearAlg :=
  tailPlaneGeometricFamily.toScalingLimitModulus

theorem tailPlane_flip_difference_forward (j : Nat) (o : Q' × Q') :
    ((tailPlaneFunctional j).E (planeFlip o) +
      -((tailPlaneFunctional j).E o)).eqv
      (-(half ^ j * o.2) + -(half ^ j * o.2)) := by
  let Y := half ^ j * o.2
  have hneg : (half ^ j * (-o.2)).eqv (-Y) := Q'.mul_neg_eqv _ _
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(o.1 + Y))
      (Q'.add_eqv_congr_left o.1 _ _ hneg)) ?_
  exact flip_sub_forward o.1 Y

theorem tailPlane_flip_difference_backward (j : Nat) (o : Q' × Q') :
    ((tailPlaneFunctional j).E o +
      -((tailPlaneFunctional j).E (planeFlip o))).eqv
      (half ^ j * o.2 + half ^ j * o.2) := by
  let Y := half ^ j * o.2
  have hneg : (half ^ j * (-o.2)).eqv (-Y) := Q'.mul_neg_eqv _ _
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (o.1 + Y) _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr_left o.1 _ _ hneg))) ?_
  exact flip_sub_backward o.1 Y

theorem twice_neg_half_mul_le (j : Nat) (a : Q') :
    -(half ^ j * a) + -(half ^ j * a) ≤
      (Q'.abs a + Q'.abs a) * half ^ j := by
  have h := Q'.add_le_add
    (neg_half_mul_le_abs_mul j a) (neg_half_mul_le_abs_mul j a)
  exact Q'.le_trans' _ _ _ h
    (Q'.ge_of_eqv (Q'.add_mul_eqv (Q'.abs a) (Q'.abs a) (half ^ j)))

theorem twice_half_mul_le (j : Nat) (a : Q') :
    half ^ j * a + half ^ j * a ≤
      (Q'.abs a + Q'.abs a) * half ^ j := by
  have h := Q'.add_le_add
    (half_mul_le_abs_mul j a) (half_mul_le_abs_mul j a)
  exact Q'.le_trans' _ _ _ h
    (Q'.ge_of_eqv (Q'.add_mul_eqv (Q'.abs a) (Q'.abs a) (half ^ j)))

def tailPlaneFlipGeometricSymmetry :
    LinearGeometricSymmetryFamily planeLinearAlg tailPlaneScaling where
  map := planeFlip
  amplitude := fun o => Q'.abs o.2 + Q'.abs o.2
  amplitude_nonneg := fun o =>
    Q'.zero_le_add _ _ (Q'.abs_nonneg o.2) (Q'.abs_nonneg o.2)
  stage_upper := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (tailPlane_flip_difference_forward j o))
      (twice_neg_half_mul_le j o.2)
  stage_lower := by
    intro o j
    apply Q'.le_add_of_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (tailPlane_flip_difference_backward j o))
      (twice_half_mul_le j o.2)

theorem tailPlane_limit_flip_invariant (o : Q' × Q') :
    Equiv (limitE tailPlaneScaling (planeFlip o))
      (limitE tailPlaneScaling o) :=
  limitE_invariant_of_geometric_defect tailPlaneFlipGeometricSymmetry o

/-- The example is not exact at any finite stage on the second basis vector;
the theorem really consumes a decaying defect. -/
theorem tailPlane_flip_not_exact_at_any_stage (j : Nat) :
    ¬ ((tailPlaneFunctional j).E (planeFlip ((0 : Q'), (1 : Q')))).eqv
      ((tailPlaneFunctional j).E ((0 : Q'), (1 : Q'))) := by
  intro h
  have hjpos : (0 : Q') < half ^ j := half_pow_pos_local j
  have hl : ((0 : Q') + half ^ j * (-(1 : Q'))).eqv (-(half ^ j)) := by
    refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (half ^ j) 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (half ^ j))
  have hr : ((0 : Q') + half ^ j * (1 : Q')).eqv (half ^ j) := by
    exact Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _)
      (Q'.mul_one_eqv (half ^ j))
  have hcanon : (-(half ^ j)).eqv (half ^ j) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hl) ?_
    refine Q'.eqv_trans _ _ _ h hr
  have hle : half ^ j ≤ -(half ^ j) := Q'.ge_of_eqv hcanon
  have hnum : (0 : Int) < (half ^ j).num := Q'.num_pos_of_pos hjpos
  have hden : (0 : Int) < (half ^ j).den :=
    by have hd := (half ^ j).den_pos; omega
  change (half ^ j).num * ((-(half ^ j)).den : Int) ≤
    (-(half ^ j)).num * ((half ^ j).den : Int) at hle
  rw [Q'.neg_den] at hle
  change (half ^ j).num * ((half ^ j).den : Int) ≤
    (-(half ^ j).num) * ((half ^ j).den : Int) at hle
  have hlpos : (0 : Int) < (half ^ j).num * ((half ^ j).den : Int) :=
    Int.mul_pos hnum hden
  have hrneg : (-(half ^ j).num) * ((half ^ j).den : Int) < 0 :=
    Int.mul_neg_of_neg_of_pos (by omega) hden
  omega

#print axioms LinearGeometricSymmetryFamily
#print axioms geoIncr_le_geoTail
#print axioms LinearGeometricSymmetryFamily.toDefect
#print axioms limitE_invariant_of_geometric_defect
#print axioms tailPlaneFunctional
#print axioms half_pow_pos_local
#print axioms tailPlaneGeometricFamily
#print axioms tailPlaneScaling
#print axioms tailPlaneFlipGeometricSymmetry
#print axioms tailPlane_limit_flip_invariant
#print axioms tailPlane_flip_not_exact_at_any_stage

end YMGap.Continuum.RegularLinearGeometricSymmetry
