/-
Constructive transport of finite-spacing symmetries to a linear continuum
functional.

`RegularLinearScalingLimit` proves that a modulus-Cauchy family of finite
positive rational-linear functionals has a positive linear limit.  This file
adds the symmetry theorem needed on the OS4 lane.  A selected observable map
may be only asymptotically invariant: for every observable and tolerance, the
two finite-spacing expectations are eventually within that tolerance.  A
half-tolerance triangle estimate and constructive uniqueness then prove exact
invariance of the continuum functional.

Exact finite-spacing invariance is a special case.  The plane example at the
end is deliberately non-vacuous: a non-identity sign flip is an exact symmetry
at every spacing and therefore at the limit, while coordinate swap is not a
symmetry even of that same limit.  Thus this theorem transports a *selected*
action; it does not identify hypercubic symmetry with full O(4) symmetry.
-/

import YMGap.Continuum.RegularLinearScalingLimit

namespace YMGap.Continuum.RegularLinearSymmetryLimit

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit

/-- A selected observable map whose finite-spacing expectation defect vanishes
with an explicit, constructive eventuality statement. -/
structure ScalingSymmetryDefect (A : LinearObsAlg)
    (L : LinearScalingLimitModulus A) where
  map : A.carrier → A.carrier
  eventually_close : ∀ (o : A.carrier) (ε : Q'), (0 : Q') < ε →
    ∃ N, ∀ j, N ≤ j →
      (L.atSpacing j).E (map o) ≤ (L.atSpacing j).E o + ε ∧
      (L.atSpacing j).E o ≤ (L.atSpacing j).E (map o) + ε

/-- The finite-stage defect estimate makes the transformed spacing sequence
converge to the untransformed limit. -/
theorem transformed_regSeq_converges
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (S : ScalingSymmetryDefect A L) (o : A.carrier) :
    ConvergesTo (regSeq L (S.map o)) (limitE L o) := by
  intro ε hε
  have hhalf : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Ns, hNs⟩ := regSeq_converges L o (HalfPow.half * ε) hhalf
  obtain ⟨Nd, hNd⟩ := S.eventually_close o (HalfPow.half * ε) hhalf
  refine ⟨max Ns Nd, fun j hj => ?_⟩
  obtain ⟨P, hP⟩ := hNs j (Nat.le_trans (Nat.le_max_left _ _) hj)
  have hd := hNd j (Nat.le_trans (Nat.le_max_right _ _) hj)
  refine ⟨P, fun n hn => ?_⟩
  obtain ⟨hs1, hs2⟩ := hP n hn
  change (L.atSpacing j).E (S.map o) ≤
      (limitE L o).approx n + ε ∧
    (limitE L o).approx n ≤ (L.atSpacing j).E (S.map o) + ε
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ hd.1 ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ hs1) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv ((limitE L o).approx n)
          (HalfPow.half * ε) (HalfPow.half * ε))
        (Q'.add_eqv_congr_left ((limitE L o).approx n)
          (HalfPow.half * ε + HalfPow.half * ε) ε
          (ExpNeg.two_halves ε)))
  · refine Q'.le_trans' _ _ _ hs2 ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ hd.2) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv ((L.atSpacing j).E (S.map o))
          (HalfPow.half * ε) (HalfPow.half * ε))
        (Q'.add_eqv_congr_left ((L.atSpacing j).E (S.map o))
          (HalfPow.half * ε + HalfPow.half * ε) ε
          (ExpNeg.two_halves ε)))

/-- Vanishing finite-spacing symmetry defect gives exact invariance of the
constructive continuum functional. -/
theorem limitE_invariant_of_vanishing_defect
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (S : ScalingSymmetryDefect A L) (o : A.carrier) :
    Equiv (limitE L (S.map o)) (limitE L o) :=
  convergesTo_unique (regSeq L (S.map o))
    (regSeq_converges L (S.map o)) (transformed_regSeq_converges S o)

/-- Exact invariance of every finite-spacing functional under a selected map. -/
structure ExactScalingSymmetry (A : LinearObsAlg)
    (L : LinearScalingLimitModulus A) where
  map : A.carrier → A.carrier
  atSpacing_invariant : ∀ j o,
    ((L.atSpacing j).E (map o)).eqv ((L.atSpacing j).E o)

/-- Exact invariance has zero asymptotic defect. -/
def ExactScalingSymmetry.toDefect
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (S : ExactScalingSymmetry A L) : ScalingSymmetryDefect A L where
  map := S.map
  eventually_close := by
    intro o ε hε
    refine ⟨0, fun j _ => ?_⟩
    have he := S.atSpacing_invariant j o
    have hnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
    exact ⟨
      Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.add_le_self_of_nonneg _ _ hnn),
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
        (Q'.add_le_self_of_nonneg _ _ hnn)⟩

/-- Exact finite-spacing symmetry survives the constructive spacing limit. -/
theorem limitE_invariant_of_exact
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (S : ExactScalingSymmetry A L) (o : A.carrier) :
    Equiv (limitE L (S.map o)) (limitE L o) :=
  limitE_invariant_of_vanishing_defect S.toDefect o

/-- Identity is an exact symmetry of every scaling family, so the certificate
type is not vacuous. -/
def identityExactScalingSymmetry
    {A : LinearObsAlg} (L : LinearScalingLimitModulus A) :
    ExactScalingSymmetry A L where
  map := id
  atSpacing_invariant := fun _ _ => Q'.eqv_refl _

/-! ## A nontrivial selected symmetry and the O(4) overreach fence -/

def planeLinearAlg : LinearObsAlg where
  carrier := Q' × Q'
  zero := (0, 0)
  add := fun a b => (a.1 + b.1, a.2 + b.2)
  one := (1, 0)
  mul := fun a b => (a.1 * b.1 + a.2 * b.2, 0)
  star := id
  smul := fun q a => (q * a.1, q * a.2)

def planeQLinearFunctional : QLinearFunctional planeLinearAlg where
  E := Prod.fst
  normalized := Q'.eqv_refl 1
  positive := fun a => Q'.zero_le_add _ _
    (SumOfSquares.q_mul_self_nonneg a.1)
    (SumOfSquares.q_mul_self_nonneg a.2)
  additive := fun _ _ => Q'.eqv_refl _
  homogeneous := fun _ _ => Q'.eqv_refl _

def planeScaling : LinearScalingLimitModulus planeLinearAlg :=
  constantScaling planeQLinearFunctional

def planeFlip (a : Q' × Q') : Q' × Q' := (a.1, -a.2)

def planeFlipExact : ExactScalingSymmetry planeLinearAlg planeScaling where
  map := planeFlip
  atSpacing_invariant := fun _ _ => Q'.eqv_refl _

theorem planeFlip_nontrivial : ∃ a, planeFlip a ≠ a := by
  refine ⟨((0 : Q'), (1 : Q')), ?_⟩
  intro h
  have hs := congrArg Prod.snd h
  change (-(1 : Q')) = 1 at hs
  exact (by decide : ¬ ((-(1 : Q')) = 1)) hs

theorem planeLimit_flip_invariant (o : Q' × Q') :
    Equiv (limitE planeScaling (planeFlip o)) (limitE planeScaling o) :=
  limitE_invariant_of_exact planeFlipExact o

def planeSwap (a : Q' × Q') : Q' × Q' := (a.2, a.1)

/-- The same continuum functional is not invariant under an unrelated map.
This is the kernel-checked fence against promoting one selected finite symmetry
to full O(4) invariance. -/
theorem planeLimit_swap_not_invariant :
    ¬ Equiv
      (limitE planeScaling (planeSwap ((1 : Q'), (0 : Q'))))
      (limitE planeScaling ((1 : Q'), (0 : Q'))) := by
  intro h
  have h3 := (h 3).2
  change (1 : Q') ≤ 0 + (Q'.invSucc 3 + Q'.invSucc 3) at h3
  exact (by decide : ¬ ((1 : Q') ≤ 0 + (Q'.invSucc 3 + Q'.invSucc 3))) h3

#print axioms ScalingSymmetryDefect
#print axioms transformed_regSeq_converges
#print axioms limitE_invariant_of_vanishing_defect
#print axioms ExactScalingSymmetry
#print axioms ExactScalingSymmetry.toDefect
#print axioms limitE_invariant_of_exact
#print axioms identityExactScalingSymmetry
#print axioms planeQLinearFunctional
#print axioms planeScaling
#print axioms planeFlipExact
#print axioms planeFlip_nontrivial
#print axioms planeLimit_flip_invariant
#print axioms planeLimit_swap_not_invariant

end YMGap.Continuum.RegularLinearSymmetryLimit
