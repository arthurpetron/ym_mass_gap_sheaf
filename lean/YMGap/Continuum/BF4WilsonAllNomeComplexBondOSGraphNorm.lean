/-
# Graph norm of the actual complex physical bond derivative

The imaginary plus shift is an isometry from the original derivative graph
pairing (input plus output) onto the already completed physical carrier.  The
represented inverse approximations below retain their actual `Rows` witness
and the supplied Cauchy modulus.  This is a fixed-nome, fixed-width graph
statement, not a continuous-time generator or a continuum Hamiltonian.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCayley

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGraphNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative (symmetric)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion inner distance distance_value ofRows limitRows limitRate limit_bound)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist completedDist_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSImaginaryShifts
  (plus plusDomain plus_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexification (valueAdd)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "Domain" => BF4WilsonAllNomeComplexBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "RIn" => BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
local notation "ROut" => BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "In" => BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
local notation "Out" => BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
local notation "I" => inner hw0 hw1
local notation "P" => plus hw0 hw1

private theorem b_add_left (x y z : RH) : B (Add x y) z = RCadd (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_left, bondValue_inner, bondValue_inner]

private theorem b_add_right (x y z : RH) : B x (Add y z) = RCadd (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_right, bondValue_inner, bondValue_inner]

private theorem b_sub_left (x y z : RH) : B (Sub x y) z = RCsub (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_left, bondValue_inner, bondValue_inner]

private theorem b_sub_right (x y z : RH) : B x (Sub y z) = RCsub (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_right, bondValue_inner, bondValue_inner]

private theorem real_cross_cancel (a b c d e f : RC) :
    RCadd (RCsub (RCsub a b) (RCsub c d))
      (RCadd (RCadd e c) (RCadd b f)) =
      RCadd (RCadd a e) (RCadd f d) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  refine Quotient.inductionOn₃ d e f ?_
  intro D E F
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 2) (.neg (.var 3)))))
        (.add (.add (.var 4) (.var 2)) (.add (.var 1) (.var 5))))
      (.add (.add (.var 0) (.var 4)) (.add (.var 5) (.var 3)))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | 2 => C.approx n
           | 3 => D.approx n | 4 => E.approx n | _ => F.approx n)))

private theorem imaginary_cross_cancel (a b c d e h : RC) :
    RCsub (RCsub (RCadd a b) (RCadd c d))
      (RCadd (RCsub e c) (RCsub b h)) =
      RCadd (RCsub a e) (RCsub h d) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  refine Quotient.inductionOn₃ d e h ?_
  intro D E H'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1))
          (.neg (.add (.var 2) (.var 3))))
        (.neg (.add (.add (.var 4) (.neg (.var 2)))
          (.add (.var 1) (.neg (.var 5))))))
      (.add (.add (.var 0) (.neg (.var 4)))
        (.add (.var 5) (.neg (.var 3))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | 2 => C.approx n
           | 3 => D.approx n | 4 => E.approx n | _ => H'.approx n)))

/-- Exact full Hermitian graph norm identity on the ORIGINAL complex physical
derivative domain.  Both mixed terms cancel by its proved graph symmetry. -/
theorem plus_graph_pairing (d e : Domain) :
    I (P d) (P e) = valueAdd (I (In d) (In e)) (I (Out d) (Out e)) := by
  apply Prod.ext
  · change RCadd (B (Sub (RIn d.1) (ROut d.2)) (Sub (RIn e.1) (ROut e.2)))
      (B (Add (RIn d.2) (ROut d.1)) (Add (RIn e.2) (ROut e.1))) =
      RCadd (RCadd (B (RIn d.1) (RIn e.1)) (B (RIn d.2) (RIn e.2)))
        (RCadd (B (ROut d.1) (ROut e.1)) (B (ROut d.2) (ROut e.2)))
    rw [b_sub_left hw0 hw1 (RIn d.1) (ROut d.2) (Sub (RIn e.1) (ROut e.2)),
      b_sub_right hw0 hw1 (RIn d.1) (RIn e.1) (ROut e.2),
      b_sub_right hw0 hw1 (ROut d.2) (RIn e.1) (ROut e.2),
      b_add_left hw0 hw1 (RIn d.2) (ROut d.1) (Add (RIn e.2) (ROut e.1)),
      b_add_right hw0 hw1 (RIn d.2) (RIn e.2) (ROut e.1),
      b_add_right hw0 hw1 (ROut d.1) (RIn e.2) (ROut e.1),
      symmetric hw0 hw1 d.2 e.1, symmetric hw0 hw1 d.1 e.2]
    exact real_cross_cancel _ _ _ _ _ _
  · change RCsub (B (Sub (RIn d.1) (ROut d.2)) (Add (RIn e.2) (ROut e.1)))
      (B (Add (RIn d.2) (ROut d.1)) (Sub (RIn e.1) (ROut e.2))) =
      RCadd (RCsub (B (RIn d.1) (RIn e.2)) (B (RIn d.2) (RIn e.1)))
        (RCsub (B (ROut d.1) (ROut e.2)) (B (ROut d.2) (ROut e.1)))
    rw [b_sub_left hw0 hw1 (RIn d.1) (ROut d.2) (Add (RIn e.2) (ROut e.1)),
      b_add_right hw0 hw1 (RIn d.1) (RIn e.2) (ROut e.1),
      b_add_right hw0 hw1 (ROut d.2) (RIn e.2) (ROut e.1),
      b_add_left hw0 hw1 (RIn d.2) (ROut d.1) (Sub (RIn e.1) (ROut e.2)),
      b_sub_right hw0 hw1 (RIn d.2) (RIn e.1) (ROut e.2),
      b_sub_right hw0 hw1 (ROut d.1) (RIn e.1) (ROut e.2),
      symmetric hw0 hw1 d.2 e.2, symmetric hw0 hw1 d.1 e.1]
    exact imaginary_cross_cancel _ _ _ _ _ _

/-- The constructed inverse of the plus shift is exactly an isometry for
the sum of its original physical input and output pairings. -/
theorem plusDomain_graph_pairing (x y : H) :
    valueAdd (I (In (plusDomain hw0 hw1 x)) (In (plusDomain hw0 hw1 y)))
      (I (Out (plusDomain hw0 hw1 x)) (Out (plusDomain hw0 hw1 y))) = I x y := by
  rw [← plus_graph_pairing hw0 hw1, plus_right, plus_right]

def graphQuadratic (d : Domain) : RC :=
  RCadd (I (In d) (In d)).1 (I (Out d) (Out d)).1

theorem plus_graphQuadratic (d : Domain) :
    graphQuadratic hw0 hw1 d = (I (P d) (P d)).1 := by
  exact (congrArg Prod.fst (plus_graph_pairing hw0 hw1 d d)).symm

theorem plusDomain_graphQuadratic (x : H) :
    graphQuadratic hw0 hw1 (plusDomain hw0 hw1 x) = (I x x).1 := by
  rw [plus_graphQuadratic, plus_right]

private theorem real_polar_cancel (a b c d : RC) :
    RCsub (RCsub a b) (RCsub c d) =
      RCsub (RCsub (RCadd a d) b) c := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.add (.var 0) (.var 3)) (.neg (.var 1)))
        (.neg (.var 2)))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n
           | 2 => C.approx n | _ => D.approx n)))

private theorem real_distance_pairing (x y : RH) :
    BF4WilsonAllNomeBondOSCompletion.bondCompletedDistance hw0 hw1 x y =
      RCsub (RCsub (RCadd (B x x) (B y y)) (B x y)) (B y x) := by
  calc
    BF4WilsonAllNomeBondOSCompletion.bondCompletedDistance hw0 hw1 x y =
        B (Sub x y) (Sub x y) := by
          rw [bondValue_distance, completedDist, bondValue_inner, bondValue_sub]
    _ = RCsub (RCsub (B x x) (B x y)) (RCsub (B y x) (B y y)) := by
          rw [b_sub_left, b_sub_right, b_sub_right]
    _ = _ := real_polar_cancel _ _ _ _

private theorem polar_sum (a b c d e f g h : RC) :
    RCsub (RCsub (RCadd (RCadd a e) (RCadd d h)) (RCadd b f)) (RCadd c g) =
      RCadd (RCsub (RCsub (RCadd a d) b) c)
        (RCsub (RCsub (RCadd e h) f) g) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  refine Quotient.inductionOn₃ d e f ?_
  intro D E F
  refine Quotient.inductionOn₂ g h ?_
  intro G H'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.add (.var 0) (.var 4))
            (.add (.var 3) (.var 7)))
          (.neg (.add (.var 1) (.var 5))))
        (.neg (.add (.var 2) (.var 6))))
      (.add (.add (.add (.add (.var 0) (.var 3))
            (.neg (.var 1))) (.neg (.var 2)))
        (.add (.add (.add (.var 4) (.var 7))
          (.neg (.var 5))) (.neg (.var 6))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | 2 => C.approx n
           | 3 => D.approx n | 4 => E.approx n | 5 => F.approx n
           | 6 => G.approx n | _ => H'.approx n)))

/-- Polarization of the already completed ORIGINAL complex physical distance. -/
theorem distance_pairing (x y : H) :
    distance hw0 hw1 x y =
      RCsub (RCsub (RCadd (I x x).1 (I y y).1) (I x y).1) (I y x).1 := by
  change RCadd
      (BF4WilsonAllNomeBondOSCompletion.bondCompletedDistance hw0 hw1 x.1 y.1)
      (BF4WilsonAllNomeBondOSCompletion.bondCompletedDistance hw0 hw1 x.2 y.2) = _
  rw [real_distance_pairing hw0 hw1 x.1 y.1,
    real_distance_pairing hw0 hw1 x.2 y.2]
  change RCadd
      (RCsub (RCsub (RCadd (B x.1 x.1) (B y.1 y.1)) (B x.1 y.1)) (B y.1 x.1))
      (RCsub (RCsub (RCadd (B x.2 x.2) (B y.2 y.2)) (B x.2 y.2)) (B y.2 x.2)) =
      RCsub (RCsub (RCadd
        (RCadd (B x.1 x.1) (B x.2 x.2))
        (RCadd (B y.1 y.1) (B y.2 y.2)))
        (RCadd (B x.1 y.1) (B x.2 y.2)))
        (RCadd (B y.1 x.1) (B y.2 x.2))
  exact (polar_sum _ _ _ _ _ _ _ _).symm

/-- The plus shift preserves the WHOLE graph distance: neither the input nor
the output component is silently replaced by a raw-source norm. -/
theorem plus_graph_distance (d e : Domain) :
    distance hw0 hw1 (P d) (P e) =
      RCadd (distance hw0 hw1 (In d) (In e))
        (distance hw0 hw1 (Out d) (Out e)) := by
  rw [distance_pairing, distance_pairing, distance_pairing,
    plus_graph_pairing hw0 hw1 d d,
    plus_graph_pairing hw0 hw1 e e,
    plus_graph_pairing hw0 hw1 d e,
    plus_graph_pairing hw0 hw1 e d]
  change RCsub (RCsub (RCadd
      (RCadd (I (In d) (In d)).1 (I (Out d) (Out d)).1)
      (RCadd (I (In e) (In e)).1 (I (Out e) (Out e)).1))
      (RCadd (I (In d) (In e)).1 (I (Out d) (Out e)).1))
      (RCadd (I (In e) (In d)).1 (I (Out e) (Out d)).1) = _
  exact polar_sum _ _ _ _ _ _ _ _

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_add_eqv (A.approx n)))

private theorem distance_nonnegative (x y : H) :
    RCnonneg (distance hw0 hw1 x y) := by
  rw [distance_value]
  have h := RCadd_le_add
    (completedDist_nonnegative hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.value hw0 hw1 x).1
      (BF4WilsonAllNomeComplexBondOSCompletion.value hw0 hw1 y).1)
    (completedDist_nonnegative hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.value hw0 hw1 x).2
      (BF4WilsonAllNomeComplexBondOSCompletion.value hw0 hw1 y).2)
  rw [rc_zero_add] at h
  exact h

/-- Each component has no larger squared distance than the graph distance. -/
theorem input_distance_le_graph (d e : Domain) :
    RCle (distance hw0 hw1 (In d) (In e))
      (distance hw0 hw1 (P d) (P e)) := by
  rw [plus_graph_distance]
  have h := RCadd_le_add
    (RCle_refl (distance hw0 hw1 (In d) (In e)))
    (distance_nonnegative hw0 hw1 (Out d) (Out e))
  rwa [rc_add_zero] at h

theorem output_distance_le_graph (d e : Domain) :
    RCle (distance hw0 hw1 (Out d) (Out e))
      (distance hw0 hw1 (P d) (P e)) := by
  rw [plus_graph_distance]
  have h := RCadd_le_add
    (distance_nonnegative hw0 hw1 (In d) (In e))
    (RCle_refl (distance hw0 hw1 (Out d) (Out e)))
  rwa [rc_zero_add] at h

/-- A represented graph approximant, with no quotient-representative choice:
the physical `Rows` remain the input to the explicitly constructed inverse. -/
def graphRows (C : BF4WilsonAllNomeComplexBondOSCompletion.CauchySequence
    hw0 hw1 (width := width)) (n : Nat) : Domain :=
  plusDomain hw0 hw1 (ofRows hw0 hw1 (C.seq n))

def graphRowsLimit (C : BF4WilsonAllNomeComplexBondOSCompletion.CauchySequence
    hw0 hw1 (width := width)) : Domain :=
  plusDomain hw0 hw1 (ofRows hw0 hw1 (limitRows hw0 hw1 C))

/-- The supplied Type-level completion modulus is preserved by the plus-shift
graph inverse.  Its distance is the physical plus-shift graph distance, not a
raw coefficient norm or an unproved derivative-limit selection. -/
theorem graphRows_bound
    (C : BF4WilsonAllNomeComplexBondOSCompletion.CauchySequence
      hw0 hw1 (width := width)) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : limitRate hw0 hw1 C e ≤ n) :
    RCle (distance hw0 hw1 (P (graphRows hw0 hw1 C n))
      (P (graphRowsLimit hw0 hw1 C)))
      (Quotient.mk crealSetoid (ofQ' e)) := by
  simp only [graphRows,graphRowsLimit,plus_right]
  exact limit_bound hw0 hw1 C e he n hn

/-- Both ORIGINAL graph components converge with the same represented rate.
This is stronger than convergence of the plus-shift image alone. -/
theorem graphRows_input_bound
    (C : BF4WilsonAllNomeComplexBondOSCompletion.CauchySequence
      hw0 hw1 (width := width)) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : limitRate hw0 hw1 C e ≤ n) :
    RCle (distance hw0 hw1 (In (graphRows hw0 hw1 C n))
      (In (graphRowsLimit hw0 hw1 C)))
      (Quotient.mk crealSetoid (ofQ' e)) :=
  RCle_trans
    (input_distance_le_graph hw0 hw1
      (graphRows hw0 hw1 C n) (graphRowsLimit hw0 hw1 C))
    (graphRows_bound hw0 hw1 C e he n hn)

theorem graphRows_output_bound
    (C : BF4WilsonAllNomeComplexBondOSCompletion.CauchySequence
      hw0 hw1 (width := width)) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : limitRate hw0 hw1 C e ≤ n) :
    RCle (distance hw0 hw1 (Out (graphRows hw0 hw1 C n))
      (Out (graphRowsLimit hw0 hw1 C)))
      (Quotient.mk crealSetoid (ofQ' e)) :=
  RCle_trans
    (output_distance_le_graph hw0 hw1
      (graphRows hw0 hw1 C n) (graphRowsLimit hw0 hw1 C))
    (graphRows_bound hw0 hw1 C e he n hn)

#print axioms plus_graph_pairing
#print axioms plusDomain_graph_pairing
#print axioms plus_graphQuadratic
#print axioms plusDomain_graphQuadratic
#print axioms distance_pairing
#print axioms plus_graph_distance
#print axioms input_distance_le_graph
#print axioms output_distance_le_graph
#print axioms graphRows
#print axioms graphRowsLimit
#print axioms graphRows_bound
#print axioms graphRows_input_bound
#print axioms graphRows_output_bound

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGraphNorm
