/-
# Cross-cutoff Cauchy frontier for the physical BF4 Markov action

The cutoff-indexed physical Markov maps now act on one common finite-linear
syntax, but a completed transfer exists only if their images converge in the
cutoff-removed squared seminorm.  This file isolates exactly that missing
analytic estimate as Type-level data for each observable.

A supplied cross-cutoff modulus constructs an actual Cauchy representative
and hence a canonical point in the already-built completion.  Two different
modulus witnesses for the same observable give the same completed point.  A
family of such witnesses therefore gives a genuine dense transfer into the
completion.

The vacuum case is discharged without an assumption: the globally
vacuum-fixing cutoff recoding gives a zero-rate Cauchy sequence whose completed
limit is exactly the normalized vacuum.  Thus the residual is non-vacuous and
confined to nonconstant observables.

This still does not define an operator on arbitrary completed points.
Compatibility with radical-null inputs and with varying Cauchy
representatives is the next descent frontier.

## Axiom gate

Only explicit Type-level rates, the proved global vacuum identity, the
cutoff-removed squared seminorm, and `Quotient.sound` are used.  There is no
classical choice, noncomputable declaration, custom axiom, or unproved
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. The exact pointwise analytic residual -/

/-- Constructive cross-cutoff Cauchy data for the recoded Markov images of one
finite-linear observable.  The field is exactly the estimate absent from the
current arbitrary-cutoff covariance library. -/
structure CentralPhysicalLinearMarkovCrossCutoffModulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) : Type where
  rate : Q' -> Nat
  cauchy : forall (epsilon : Q'), (0 : Q') < epsilon ->
    forall m n, rate epsilon <= m -> rate epsilon <= n ->
      CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) m half observable)
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) n half observable))
        (CReal.ofQ' epsilon)

/-- The actual constructive Cauchy representative produced by one pointwise
cross-cutoff modulus. -/
def centralPhysicalLinearMarkovCutoffCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {observable : CentralPhysicalLinearObservable}
    (M : CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half observable) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq cutoff := centralPhysicalLinearMarkovCutoffAction
    (Q'.le_of_lt hw0) cutoff half observable
  modulus := M.rate
  isCauchy := M.cauchy

/-- The completed dense image selected by the cutoff-indexed actions and an
explicit cross-cutoff modulus. -/
def centralPhysicalLinearMarkovDenseLimit
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {observable : CentralPhysicalLinearObservable}
    (M : CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half observable) :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  Quotient.mk
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).completionSetoid
    (centralPhysicalLinearMarkovCutoffCauchy M)

/-! ## 2. Independence from the chosen rate witness -/

private theorem czero_le_ofQ'_of_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    CReal.leEv CReal.czero (CReal.ofQ' epsilon) :=
  CReal.leEv_of_le
    (CReal.ofQ'_le_ofQ' (Q'.le_of_lt hepsilon))

/-- Modulus witnesses alter proof data, not the cutoff image sequence. -/
def centralPhysicalLinearMarkovCutoffCauchy_close
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {observable : CentralPhysicalLinearObservable}
    (M N : CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half observable) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalLinearMarkovCutoffCauchy M)
      (centralPhysicalLinearMarkovCutoffCauchy N) where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon cutoff _
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).distSq_refl
            (centralPhysicalLinearMarkovCutoffAction
              (Q'.le_of_lt hw0) cutoff half observable)))
      (czero_le_ofQ'_of_pos hepsilon)

theorem centralPhysicalLinearMarkovDenseLimit_independent
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {observable : CentralPhysicalLinearObservable}
    (M N : CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half observable) :
    centralPhysicalLinearMarkovDenseLimit M =
      centralPhysicalLinearMarkovDenseLimit N :=
  Quotient.sound
    ⟨centralPhysicalLinearMarkovCutoffCauchy_close M N⟩

/-! ## 3. The unconditionally convergent vacuum sequence -/

/-- No analytic residual remains on the constant-one channel: every cutoff
image is semantically the same vacuum. -/
def centralPhysicalLinearMarkovVacuumCrossCutoffModulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half centralPhysicalLinearVacuum where
  rate := fun _ => 0
  cauchy := by
    intro epsilon hepsilon m n _ _
    have hmn : Equivalent
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) m half centralPhysicalLinearVacuum)
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) n half centralPhysicalLinearVacuum) :=
      equivalent_trans
        (centralPhysicalLinearMarkovCutoffAction_vacuum_equivalent
          (Q'.le_of_lt hw0) m half)
        (equivalent_symm
          (centralPhysicalLinearMarkovCutoffAction_vacuum_equivalent
            (Q'.le_of_lt hw0) n half))
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (physicalLinearDistSq_equiv_czero_of_equivalent
          hw0 hw1 half hmn))
      (czero_le_ofQ'_of_pos hepsilon)

/-- The vacuum cutoff sequence is close to the constant representative of the
already-constructed normalized completed vacuum. -/
def centralPhysicalLinearMarkovVacuumCutoffCauchy_close_constant
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalLinearMarkovCutoffCauchy
        (centralPhysicalLinearMarkovVacuumCrossCutoffModulus
          hw0 hw1 half))
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant centralPhysicalLinearVacuum) where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon cutoff _
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (physicalLinearDistSq_equiv_czero_of_equivalent
          hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction_vacuum_equivalent
            (Q'.le_of_lt hw0) cutoff half)))
      (czero_le_ofQ'_of_pos hepsilon)

/-- The actual cutoff limit on the vacuum is exactly the normalized completed
vacuum, without any cross-cutoff hypothesis. -/
theorem centralPhysicalLinearMarkovVacuumDenseLimit_eq_vacuum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    centralPhysicalLinearMarkovDenseLimit
        (centralPhysicalLinearMarkovVacuumCrossCutoffModulus
          hw0 hw1 half) =
      centralPhysicalCutoffCompletedVacuum hw0 hw1 half :=
  Quotient.sound
    ⟨centralPhysicalLinearMarkovVacuumCutoffCauchy_close_constant
      hw0 hw1 half⟩

/-! ## 4. A dense transfer from a family of pointwise moduli -/

/-- The remaining dense existence input: one explicit cross-cutoff modulus
for every finite-linear observable. -/
structure CentralPhysicalLinearMarkovDenseCauchyData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  modulus : forall observable : CentralPhysicalLinearObservable,
    CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half observable

/-- A family of pointwise moduli contracts to one actual map from the dense
finite-linear syntax into the completed physical carrier. -/
def centralPhysicalLinearMarkovDenseTransfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    CentralPhysicalLinearObservable ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  fun observable =>
    centralPhysicalLinearMarkovDenseLimit (M.modulus observable)

/-- Every dense transfer family fixes the normalized completed vacuum; the
result is independent of the supplied vacuum rate witness. -/
theorem centralPhysicalLinearMarkovDenseTransfer_vacuum
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    centralPhysicalLinearMarkovDenseTransfer M
        centralPhysicalLinearVacuum =
      centralPhysicalCutoffCompletedVacuum hw0 hw1 half := by
  exact Eq.trans
    (centralPhysicalLinearMarkovDenseLimit_independent
      (M.modulus centralPhysicalLinearVacuum)
      (centralPhysicalLinearMarkovVacuumCrossCutoffModulus
        hw0 hw1 half))
    (centralPhysicalLinearMarkovVacuumDenseLimit_eq_vacuum
      hw0 hw1 half)

/-! ## Axiom audit -/

#print axioms CentralPhysicalLinearMarkovCrossCutoffModulus
#print axioms centralPhysicalLinearMarkovCutoffCauchy
#print axioms centralPhysicalLinearMarkovDenseLimit_independent
#print axioms centralPhysicalLinearMarkovVacuumCrossCutoffModulus
#print axioms centralPhysicalLinearMarkovVacuumDenseLimit_eq_vacuum
#print axioms centralPhysicalLinearMarkovDenseTransfer
#print axioms centralPhysicalLinearMarkovDenseTransfer_vacuum

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
