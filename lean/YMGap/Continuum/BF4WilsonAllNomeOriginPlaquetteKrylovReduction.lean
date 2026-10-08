/-
# Independent finite filters of the actual origin plaquette orbit

The checked equal diagonal and cleared mixed responses are transported through
arbitrary finite signed time filters on the SAME original Wilson completion.
The two-orientation response becomes a sum of two scalar-filter responses of
the existing source x, with integer coefficients and without division.

This reduces the orientation part of a Hankel/variational screen. It supplies
no interacting moment estimate, slow rate or slow-mode overlap, and does not
assert that scalar filters cannot improve retention or that the local span is
time invariant. Scaling, continuum and physical-gap claims remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse

namespace YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteKrylovReduction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "D" => completedSub hw0 hw1
local notation "L" => lagPair hw0 hw1
local notation "O" => orbitSum hw0 hw1

private theorem scale_comm (a b : Q') (r : RC) :
    RCscale a (RCscale b r) = RCscale b (RCscale a r) := by
  rw [RCscale_RCscale, RCscale_RCscale]
  exact RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv a b) r

private theorem responseSum_scale (a : Q') (cs : List (Q' × Nat)) (f : Nat → RC) :
    responseSum cs (fun n => RCscale a (f n)) = RCscale a (responseSum cs f) := by
  induction cs with
  | nil => exact (RCscale_RCzero a).symm
  | cons c cs ih =>
      rcases c with ⟨b,n⟩
      simp only [responseSum, ih, scale_comm b a, RCscale_RCadd]

private theorem nested_scale (a : Q') (cs ds : List (Q' × Nat))
    (f : Nat → Nat → RC) :
    responseSum cs (fun m => responseSum ds (fun k => RCscale a (f m k))) =
      RCscale a (responseSum cs (fun m => responseSum ds (f m))) := by
  have h : (fun m => responseSum ds (fun k => RCscale a (f m k))) =
      (fun m => RCscale a (responseSum ds (f m))) :=
    funext (fun m => responseSum_scale a ds (f m))
  rw [h, responseSum_scale]

private theorem orbit_lag (p q : V) (cs ds : List (Q' × Nat)) (n : Nat) :
    L n (O p cs) (O q ds) =
      responseSum cs (fun m => responseSum ds (fun k => L (n+m+k) p q)) := by
  unfold lagPair
  rw [orbitSum_time, orbitSum_pairing]
  apply congrArg (responseSum cs)
  funext m
  apply congrArg (responseSum ds)
  funext k
  rw [← completedTime_add]
  have hn : m+k+n = n+m+k := by omega
  rw [hn]

/-- Both lists may be signed and different. Every mixed filter lag is retained. -/
theorem filtered_diagonal_response (hw : 1 ≤ width)
    (cs ds : List (Q' × Nat)) (n : Nat) :
    L n (O (y hw0 hw1 hw) cs) (O (y hw0 hw1 hw) ds) =
      L n (O (x hw0 hw1 hw) cs) (O (x hw0 hw1 hw) ds) := by
  rw [orbit_lag, orbit_lag]
  apply congrArg (responseSum cs)
  funext m
  apply congrArg (responseSum ds)
  funext k
  exact diagonal_response hw0 hw1 hw (n+m+k)

/-- The actual every-lag mixed response, cleared BEFORE either finite sum. -/
theorem filtered_mixed_response (hw : 1 ≤ width)
    (cs ds : List (Q' × Nat)) (n : Nat) :
    RCscale 2 (L n (O (x hw0 hw1 hw) cs) (O (y hw0 hw1 hw) ds)) =
      RCscale (-1) (L n (O (x hw0 hw1 hw) cs) (O (x hw0 hw1 hw) ds)) := by
  rw [orbit_lag, orbit_lag]
  rw [← nested_scale, ← nested_scale]
  apply congrArg (responseSum cs)
  funext m
  apply congrArg (responseSum ds)
  funext k
  exact mixed_response hw0 hw1 hw (n+m+k)

private theorem lag_add_left (n : Nat) (p q r : V) :
    L n (A p q) r = RCadd (L n p r) (L n q r) :=
  completedInner_add_left hw0 hw1 p q (T n r)

private theorem lag_add_right (n : Nat) (p q r : V) :
    L n p (A q r) = RCadd (L n p q) (L n p r) := by
  unfold lagPair
  rw [completedTime_additive, completedInner_add_right]

private theorem lag_smul_left (n : Nat) (a : Q') (p q : V) :
    L n (S a p) q = RCscale a (L n p q) :=
  completedInner_smul_left hw0 hw1 a p (T n q)

private theorem lag_smul_right (n : Nat) (a : Q') (p q : V) :
    L n p (S a q) = RCscale a (L n p q) := by
  unfold lagPair
  rw [completedTime_smul, completedInner_smul_right]

private theorem collect_left (a c d : RC) :
    RCscale 4 (RCadd (RCadd a c) (RCadd c d)) =
      RCadd (RCscale 4 a) (RCadd (RCscale 4 (RCscale 2 c)) (RCscale 4 d)) := by
  refine Quotient.inductionOn₃ a c d ?_
  intro p q r
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.mul (.const 4) (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2))))
      (.add (.mul (.const 4) (.var 0))
        (.add (.mul (.const 4) (.mul (.const 2) (.var 1))) (.mul (.const 4) (.var 2))))
      (by decide)
      (fun | 0 => p.approx k | 1 => q.approx k | _ => r.approx k))

private theorem collect_right (a m d : RC) :
    RCadd
      (RCadd
        (RCadd (RCscale 2 (RCscale 2 a)) (RCscale 2 (RCscale (-1) m)))
        (RCadd (RCscale (-1) (RCscale 2 m)) (RCscale (-1) (RCscale (-1) d))))
      (RCscale 3 d) =
      RCadd (RCscale 4 a) (RCadd (RCscale 4 (RCscale (-1) m)) (RCscale 4 d)) := by
  refine Quotient.inductionOn₃ a m d ?_
  intro p q r
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add
        (.add
          (.add (.mul (.const 2) (.mul (.const 2) (.var 0)))
            (.mul (.const 2) (.mul (.const (-1)) (.var 1))))
          (.add (.mul (.const (-1)) (.mul (.const 2) (.var 1)))
            (.mul (.const (-1)) (.mul (.const (-1)) (.var 2)))))
        (.mul (.const 3) (.var 2)))
      (.add (.mul (.const 4) (.var 0))
        (.add (.mul (.const 4) (.mul (.const (-1)) (.var 1))) (.mul (.const 4) (.var 2))))
      (by decide)
      (fun | 0 => p.approx k | 1 => q.approx k | _ => r.approx k))

/-- Independent orientation filters reduce to two scalar-filter responses of
the SAME source x. The congruence needs no norm inverse, sign or nonzero guard. -/
theorem independent_filters_response (hw : 1 ≤ width)
    (cs ds : List (Q' × Nat)) (n : Nat) :
    let X := O (x hw0 hw1 hw) cs
    let Y := O (y hw0 hw1 hw) ds
    let QX := O (x hw0 hw1 hw) ds
    RCscale 4 (L n (A X Y) (A X Y)) =
      RCadd (L n (D (S 2 X) QX) (D (S 2 X) QX)) (RCscale 3 (L n QX QX)) := by
  let X := O (x hw0 hw1 hw) cs
  let Y := O (y hw0 hw1 hw) ds
  let QX := O (x hw0 hw1 hw) ds
  change RCscale 4 (L n (A X Y) (A X Y)) =
    RCadd (L n (D (S 2 X) QX) (D (S 2 X) QX)) (RCscale 3 (L n QX QX))
  have hdiag : L n Y Y = L n QX QX :=
    filtered_diagonal_response hw0 hw1 hw ds ds n
  have hmix : RCscale 2 (L n X Y) = RCscale (-1) (L n X QX) :=
    filtered_mixed_response hw0 hw1 hw cs ds n
  simp only [completedSub, completedNeg, lag_add_left, lag_add_right,
    lag_smul_left, lag_smul_right, lagPair_symm hw0 hw1 n Y X,
    lagPair_symm hw0 hw1 n QX X, hdiag]
  rw [collect_left, RCscale_RCadd, RCscale_RCadd, collect_right, hmix]

private theorem scale_sub (a b : RC) :
    RCscale 4 (RCsub a b) = RCsub (RCscale 4 a) (RCscale 4 b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.mul (.const 4) (.add (.var 0) (.neg (.var 1))))
      (.add (.mul (.const 4) (.var 0)) (.neg (.mul (.const 4) (.var 1))))
      (by decide) (fun | 0 => p.approx k | _ => q.approx k))

private theorem sub_add_scale (a b c d : RC) :
    RCsub (RCadd a (RCscale 3 c)) (RCadd b (RCscale 3 d)) =
      RCadd (RCsub a b) (RCscale 3 (RCsub c d)) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro p q r
  refine Quotient.inductionOn d ?_
  intro s
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.const 3) (.var 2)))
        (.neg (.add (.var 1) (.mul (.const 3) (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.mul (.const 3) (.add (.var 2) (.neg (.var 3)))))
      (by decide)
      (fun | 0 => p.approx k | 1 => q.approx k | 2 => r.approx k | _ => s.approx k))

/-- The SAME reduction for forward lag differences, including the even-lag
costs used by the original filtered-cost limits. No cost sign is assumed. -/
theorem independent_filters_forward_cost (hw : 1 ≤ width)
    (cs ds : List (Q' × Nat)) (n : Nat) :
    let X := O (x hw0 hw1 hw) cs
    let Y := O (y hw0 hw1 hw) ds
    let QX := O (x hw0 hw1 hw) ds
    RCscale 4 (RCsub (L n (A X Y) (A X Y)) (L (n+1) (A X Y) (A X Y))) =
      RCadd
        (RCsub (L n (D (S 2 X) QX) (D (S 2 X) QX))
          (L (n+1) (D (S 2 X) QX) (D (S 2 X) QX)))
        (RCscale 3 (RCsub (L n QX QX) (L (n+1) QX QX))) := by
  dsimp only
  rw [scale_sub, independent_filters_response hw0 hw1 hw cs ds n,
    independent_filters_response hw0 hw1 hw cs ds (n+1)]
  exact sub_add_scale _ _ _ _

end YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteKrylovReduction

#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteKrylovReduction.filtered_diagonal_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteKrylovReduction.filtered_mixed_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteKrylovReduction.independent_filters_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteKrylovReduction.independent_filters_forward_cost
