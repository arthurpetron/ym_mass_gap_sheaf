/-
# Actual polynomial differences and retained ORIGINAL Cauchy representatives

Polynomial addition/scaling/subtraction agree with the existing original
completed operations. The proved probe norm bound gives the squared-distance
bound ||p(T2)v-q(T2)v||^2 <= M^2 from a uniform rational |p-q|<=M.
Every polynomial vector has an explicitly constructed original Cauchy row;
no quotient representative is selected. Nome and lattice spacing are fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef (zeroPresentation)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows (probeCauchy probeCauchy_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm (probe_norm_bound)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem add_regroup (a b c d : Completion) :
    completedAdd (completedAdd a b) (completedAdd c d)=completedAdd (completedAdd a c) (completedAdd b d) := by
  rw [completedAdd_assoc,← completedAdd_assoc b c d,completedAdd_comm b c,
    completedAdd_assoc c b d,← completedAdd_assoc]

theorem smul_zero_state (c : Q') : completedSmul c completedZero=completedZero :=
  (congrArg (completedSmul c) (completedSmul_zero completedUnit).symm).trans
    ((completedSmul_mul c 0 completedUnit).trans
      ((completedSmul_congr (QPoly.q_mul_zero c) completedUnit).trans (completedSmul_zero completedUnit)))

theorem vector_add (x : Completion) (p q : QPoly.Poly) (r : Nat) :
    polynomialVector x (QPoly.padd p q) r=completedAdd (polynomialVector x p r) (polynomialVector x q r) := by
  induction p generalizing q r with
  | nil => exact (completedZero_add _).symm
  | cons c p ih =>
      cases q with
      | nil => exact (completedAdd_zero _).symm
      | cons d q =>
          simp only [QPoly.padd,polynomialVector,ih,← completedAdd_smul]
          exact add_regroup _ _ _ _

theorem vector_scale (x : Completion) (c : Q') (p : QPoly.Poly) (r : Nat) :
    polynomialVector x (QPoly.pscale c p) r=completedSmul c (polynomialVector x p r) := by
  induction p generalizing r with
  | nil => exact (smul_zero_state c).symm
  | cons d p ih => simp only [QPoly.pscale,polynomialVector,ih,← completedSmul_mul,← completedSmul_add]

theorem vector_sub (x : Completion) (p q : QPoly.Poly) (r : Nat) :
    polynomialVector x (QPoly.psub p q) r=completedSub (polynomialVector x p r) (polynomialVector x q r) := by
  unfold QPoly.psub QPoly.pneg
  rw [vector_add,vector_scale]
  rfl

theorem probe_distance_bound (p q : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t + -QPoly.eval q t)≤M) :
    RCle (completedDist (polynomialVector unitProbe.val p 0) (polynomialVector unitProbe.val q 0)) (rat (M*M)) := by
  unfold completedDist
  rw [← vector_sub]
  exact probe_norm_bound (QPoly.psub p q) M hM (fun t ht h1 =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (QPoly.eval_psub p q t))) (h t ht h1))

theorem probe_distance_two_sided (p q : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 →
      QPoly.eval p t≤QPoly.eval q t+M ∧ QPoly.eval q t≤QPoly.eval p t+M) :
    RCle (completedDist (polynomialVector unitProbe.val p 0) (polynomialVector unitProbe.val q 0)) (rat (M*M)) :=
  probe_distance_bound p q M hM (fun t ht h1 => abs_sub_le_of_bounds (h t ht h1).1 (h t ht h1).2)

def vectorRepresentative (X : seminorm.Cauchy) : QPoly.Poly → Nat → seminorm.Cauchy
  | [],_ => seminorm.constant zeroPresentation
  | c::p,r => addition.mapCauchy ((scalarContinuous c).mapCauchy (timeCauchy (r+r) X))
      (vectorRepresentative X p (r+1))

theorem vectorRepresentative_pin (X : seminorm.Cauchy) (p : QPoly.Poly) (r : Nat) :
    Quotient.mk seminorm.completionSetoid (vectorRepresentative X p r)=
      polynomialVector (Quotient.mk seminorm.completionSetoid X) p r := by
  induction p generalizing r with
  | nil => rfl
  | cons c p ih =>
      change completedAdd (completedSmul c (completedTime (r+r) (Quotient.mk seminorm.completionSetoid X)))
        (Quotient.mk seminorm.completionSetoid (vectorRepresentative X p (r+1)))=_
      rw [ih]
      rfl

def probeRepresentative (p : QPoly.Poly) : seminorm.Cauchy := vectorRepresentative probeCauchy p 0

theorem probeRepresentative_pin (p : QPoly.Poly) :
    Quotient.mk seminorm.completionSetoid (probeRepresentative p)=polynomialVector unitProbe.val p 0 := by
  rw [probeRepresentative,vectorRepresentative_pin,probeCauchy_pin]

end YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.add_regroup
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.smul_zero_state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.vector_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.vector_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.vector_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.probe_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.probe_distance_two_sided
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.vectorRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.vectorRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.probeRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference.probeRepresentative_pin
