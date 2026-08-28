/-
# Local positivity for heterogeneous kernel products

The whole-slab recoupling entry is a dependent product of local SU(2)
matrix entries.  This module exposes the exact proposition needed to prove
that entry positive: every selected local coordinate is positive.  The
global result is then the structural fact that a finite product of strictly
positive rationals is strictly positive.

This is deliberately separate from row normalization.  A normalized row
always has some positive entry, whereas a prescribed strand-switching target
needs positivity at its own displayed local coordinates.

Constructive contract: structural recursion and exact `Q'` order only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or enlarged heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProduct

namespace YMGap.Continuum.FiniteBistochasticQKernelProductPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-- Every coordinate selected by a dependent source-target assignment has a
strictly positive local matrix entry. -/
def FiniteBistochasticCoordinatewisePositive :
    {packages : List FiniteBistochasticQKernelPackage} ->
      FiniteBistochasticSourceAssignment packages ->
      FiniteBistochasticTargetAssignment packages -> Prop
  | [], _, _ => True
  | package :: _, source, target =>
      (0 : Q') < package.kernel.weight source.1 target.1 /\
        FiniteBistochasticCoordinatewisePositive source.2 target.2

/-- Coordinatewise strict positivity contracts to strict positivity of the
exact heterogeneous product entry. -/
theorem finiteBistochasticProductWeight_pos_of_coordinatewise :
    {packages : List FiniteBistochasticQKernelPackage} ->
    (source : FiniteBistochasticSourceAssignment packages) ->
    (target : FiniteBistochasticTargetAssignment packages) ->
    FiniteBistochasticCoordinatewisePositive source target ->
      (0 : Q') < finiteBistochasticProductWeight source target
  | [], (), (), _ => by decide
  | _ :: _, source, target, hpositive =>
      Q'.mul_pos hpositive.1
        (finiteBistochasticProductWeight_pos_of_coordinatewise
          source.2 target.2 hpositive.2)

end YMGap.Continuum.FiniteBistochasticQKernelProductPositivity

#print axioms YMGap.Continuum.FiniteBistochasticQKernelProductPositivity.FiniteBistochasticCoordinatewisePositive
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProductPositivity.finiteBistochasticProductWeight_pos_of_coordinatewise
