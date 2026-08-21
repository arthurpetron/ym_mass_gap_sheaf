/-
# Completion frontier for the cutoff-dependent physical BF4 Markov action

Pointwise cross-cutoff moduli give a rational-linear map from the dense
finite-linear syntax into the physical completion.  Two further analytic
compatibilities are logically separate:

1. radical-null dense inputs must give close output sequences;
2. for an arbitrary input Cauchy representative `X`, the diagonal sequence
   `P_n (X_n)` must be Cauchy, and close input representatives must give close
   diagonal output representatives.

This file names both residuals as Type-level data at their exact use sites.
Dense radical data descends the pointwise map through the limiting null
quotient.  The stronger completion modulus constructs a genuine map on the
whole completed carrier by quotient lift.  It implies the pointwise and dense
radical data, agrees with the previously constructed dense cutoff limit, and
fixes the normalized completed vacuum.

No instance of the nonconstant completion modulus is claimed here.  Proving
its two quantitative fields from BF4 cross-cutoff estimates remains the
analytic frontier; the construction below prevents that obligation from being
blurred with quotient mechanics.

## Axiom gate

Only explicit Type-level Cauchy/close rates and quotient descent are used.
There is no classical choice, noncomputable declaration, custom axiom, or
unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Dense radical descent -/

/-- Pointwise cross-cutoff convergence together with the explicit statement
that limiting-radical-null dense inputs produce close output sequences. -/
structure CentralPhysicalLinearMarkovDenseRadicalData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half
  radicalClose : forall
    {left right : CentralPhysicalLinearObservable},
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Null left right ->
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalLinearMarkovCutoffCauchy
        (pointwise.modulus left))
      (centralPhysicalLinearMarkovCutoffCauchy
        (pointwise.modulus right))

/-- The pointwise dense transfer descended through the actual limiting
seminorm radical.  Its codomain is already complete. -/
def centralPhysicalLinearMarkovDenseQuotientTransfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovDenseRadicalData hw0 hw1 half) :
    CentralPhysicalCutoffLinearQuotient hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  Quotient.lift
    (centralPhysicalLinearMarkovDenseTransfer M.pointwise)
    (fun _ _ h => Quotient.sound ⟨M.radicalClose h⟩)

@[simp] theorem centralPhysicalLinearMarkovDenseQuotientTransfer_mk
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovDenseRadicalData hw0 hw1 half)
    (observable : CentralPhysicalLinearObservable) :
    centralPhysicalLinearMarkovDenseQuotientTransfer M
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).nullSetoid observable) =
      centralPhysicalLinearMarkovDenseTransfer
        M.pointwise observable := rfl

/-- Dense radical descent retains the exact vacuum identity. -/
theorem centralPhysicalLinearMarkovDenseQuotientTransfer_vacuum
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovDenseRadicalData hw0 hw1 half) :
    centralPhysicalLinearMarkovDenseQuotientTransfer M
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).nullSetoid centralPhysicalLinearVacuum) =
      centralPhysicalCutoffCompletedVacuum hw0 hw1 half :=
  centralPhysicalLinearMarkovDenseTransfer_vacuum M.pointwise

/-! ## 2. The two completion-level modulus fields -/

/-- Exact analytic data needed to apply the cutoff-indexed Markov family to
arbitrary completed representatives.

`diagonalCauchy` controls `P_m(X_m)` versus `P_n(X_n)` for one input Cauchy
sequence.  `diagonalClose` controls `P_n(X_n)` versus `P_n(Y_n)` when `X` and
`Y` are explicitly close. -/
structure CentralPhysicalLinearMarkovCompletionModulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  diagonalRate :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy -> Q' -> Nat
  diagonalCauchy : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall m n,
      diagonalRate X epsilon <= m ->
      diagonalRate X epsilon <= n ->
      CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) m half (X.seq m))
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) n half (X.seq n)))
        (CReal.ofQ' epsilon)
  closeRate : forall
    {X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy},
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X Y -> Q' -> Nat
  diagonalClose : forall
    {X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X Y)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall n, closeRate h epsilon <= n ->
      CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) n half (X.seq n))
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) n half (Y.seq n)))
        (CReal.ofQ' epsilon)

/-! ## 3. Contracting the modulus to a completed transfer -/

/-- Diagonal application of the cutoff-indexed action to one arbitrary input
Cauchy representative. -/
def centralPhysicalLinearMarkovMapCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq n := centralPhysicalLinearMarkovCutoffAction
    (Q'.le_of_lt hw0) n half (X.seq n)
  modulus := M.diagonalRate X
  isCauchy := M.diagonalCauchy X

/-- Explicit close witness for the diagonal images of close input
representatives. -/
def centralPhysicalLinearMarkovMapClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    {X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X Y) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalLinearMarkovMapCauchy M X)
      (centralPhysicalLinearMarkovMapCauchy M Y) where
  modulus := M.closeRate h
  close := M.diagonalClose h

theorem centralPhysicalLinearMarkovMap_completionRel
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    {X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).CompletionRel X Y) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).CompletionRel
      (centralPhysicalLinearMarkovMapCauchy M X)
      (centralPhysicalLinearMarkovMapCauchy M Y) := by
  rcases h with ⟨hdata⟩
  exact ⟨centralPhysicalLinearMarkovMapClose M hdata⟩

/-- The actual completed physical BF4 transfer constructed from the two
explicit completion modulus fields. -/
def centralPhysicalCutoffCompletedMarkovTransfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  Quotient.lift
    (fun X => Quotient.mk
      (centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).completionSetoid
      (centralPhysicalLinearMarkovMapCauchy M X))
    (fun _ _ h => Quotient.sound
      (centralPhysicalLinearMarkovMap_completionRel M h))

@[simp] theorem centralPhysicalCutoffCompletedMarkovTransfer_mk
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    centralPhysicalCutoffCompletedMarkovTransfer M
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid X) =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalLinearMarkovMapCauchy M X) := rfl

/-! ## 4. The stronger modulus implies every earlier transfer datum -/

/-- Completion-level diagonal Cauchy data specializes to the previously
isolated pointwise dense moduli on constant input representatives. -/
def CentralPhysicalLinearMarkovCompletionModulus.toDenseCauchyData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half where
  modulus observable :=
    { rate := M.diagonalRate
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant observable)
      cauchy := M.diagonalCauchy
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant observable) }

/-- The completion close field also supplies dense radical compatibility by
applying it to the standard constant-sequence close witness of a null pair. -/
def CentralPhysicalLinearMarkovCompletionModulus.toDenseRadicalData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    CentralPhysicalLinearMarkovDenseRadicalData hw0 hw1 half where
  pointwise := M.toDenseCauchyData
  radicalClose := by
    intro left right hnull
    exact centralPhysicalLinearMarkovMapClose M
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).closeConstantsOfNull hnull)

private def cauchyCloseOfSeqEq
    {D : SquaredSeminorm} (X Y : D.Cauchy)
    (hseq : forall n, X.seq n = Y.seq n) : D.Close X Y where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon n _
    rw [hseq n]
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv (D.distSq_refl (Y.seq n)))
      (CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ' (Q'.le_of_lt hepsilon)))

/-- On every embedded dense observable, the completed transfer is exactly the
pointwise cutoff limit induced by the same completion modulus. -/
theorem centralPhysicalCutoffCompletedMarkovTransfer_embed
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (observable : CentralPhysicalLinearObservable) :
    centralPhysicalCutoffCompletedMarkovTransfer M
        (embedCentralPhysicalLinearObservable
          hw0 hw1 half observable) =
      centralPhysicalLinearMarkovDenseTransfer
        M.toDenseCauchyData observable := by
  apply Quotient.sound
  exact ⟨cauchyCloseOfSeqEq
    (centralPhysicalLinearMarkovMapCauchy M
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant observable))
    (centralPhysicalLinearMarkovCutoffCauchy
      (M.toDenseCauchyData.modulus observable))
    (fun _ => rfl)⟩

/-- Every completed transfer constructed from the exact modulus fixes the
already normalized completed vacuum. -/
theorem centralPhysicalCutoffCompletedMarkovTransfer_vacuum
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    centralPhysicalCutoffCompletedMarkovTransfer M
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      centralPhysicalCutoffCompletedVacuum hw0 hw1 half := by
  exact Eq.trans
    (centralPhysicalCutoffCompletedMarkovTransfer_embed
      M centralPhysicalLinearVacuum)
    (centralPhysicalLinearMarkovDenseTransfer_vacuum
      M.toDenseCauchyData)

/-! ## Axiom audit -/

#print axioms CentralPhysicalLinearMarkovDenseRadicalData
#print axioms centralPhysicalLinearMarkovDenseQuotientTransfer
#print axioms CentralPhysicalLinearMarkovCompletionModulus
#print axioms centralPhysicalLinearMarkovMapCauchy
#print axioms centralPhysicalCutoffCompletedMarkovTransfer
#print axioms CentralPhysicalLinearMarkovCompletionModulus.toDenseRadicalData
#print axioms centralPhysicalCutoffCompletedMarkovTransfer_embed
#print axioms centralPhysicalCutoffCompletedMarkovTransfer_vacuum

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
