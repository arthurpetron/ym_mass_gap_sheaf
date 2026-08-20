/-
M4u -- representation-invariant strict positivity for completed constructive
reals.

The raw `CReal.IsPositive` predicate depends on the chosen Cauchy-sequence
representative because its one-slack order constrains every approximation.
The completed real line used by the Hilbert-space layer is instead
`RC = CReal / Equiv`, with the representation-invariant eventual order
`RCle`.  This file records strict positivity in that quotient currency.

For an embedded representative, `RCIsPositive` is exactly `PosEv`.  Thus an
eventually positive exact mass yields a positive completed real without any
choice of, or mutation to, its finitely many early approximations.
-/

import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.TuranPositivity

namespace YMGap.Continuum.RCStrictPositivity

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity

/-- Strict positivity on the completed constructive real line: a positive
rational lies below the value in the quotient's transitive order. -/
def RCIsPositive (x : RC) : Prop :=
  Exists fun epsilon : Q' =>
    (0 : Q') < epsilon /\
      RCle (Quotient.mk crealSetoid (CReal.ofQ' epsilon)) x

/-- A positive completed real carried as Type-level data.  The value is data;
its positivity is the corresponding proof field. -/
structure PositiveRC : Type 1 where
  value : RC
  isPositive : RCIsPositive value

/-- On an embedded `CReal` representative, quotient positivity is precisely
the stable eventual-order predicate `PosEv`. -/
theorem rcIsPositive_mk_iff_posEv (x : CReal) :
    RCIsPositive (Quotient.mk crealSetoid x) <-> PosEv x :=
  Iff.rfl

/-- Package any eventually positive representative as a positive completed
real, without eliminating its positivity witness into data. -/
def positiveRCOfPosEv (x : CReal) (hx : PosEv x) : PositiveRC where
  value := Quotient.mk crealSetoid x
  isPositive := (rcIsPositive_mk_iff_posEv x).2 hx

end YMGap.Continuum.RCStrictPositivity

#print axioms YMGap.Continuum.RCStrictPositivity.rcIsPositive_mk_iff_posEv
#print axioms YMGap.Continuum.RCStrictPositivity.positiveRCOfPosEv
