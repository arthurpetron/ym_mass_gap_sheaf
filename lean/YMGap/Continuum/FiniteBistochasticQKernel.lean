/-
# Finite constructive bistochastic rational kernels

A normalized row is not yet a finite Markov matrix: column preservation
requires an explicit source carrier as well.  This structure records both
finite carriers and both exact normalization laws.  It is deliberately
agnostic about the origin of the entries, so later modules can distinguish
representation-theoretic recoupling kernels from Gibbs or OS kernels.

Constructive contract: finite lists and exact `Q'` algebra only; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.FiniteBistochasticQKernel

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- A finite nonnegative rational matrix with explicit source and target
carriers and exact unit mass in every row and every column. -/
structure FiniteBistochasticQKernel (Source Target : Type) where
  sources : List Source
  targets : List Target
  weight : Source → Target → Q'
  weight_nonnegative : ∀ source target, (0 : Q') ≤ weight source target
  row_normalized : ∀ source, listQSum (weight source) targets ≈ 1
  column_normalized : ∀ target,
    listQSum (fun source => weight source target) sources ≈ 1

end YMGap.Continuum.FiniteBistochasticQKernel

#print axioms YMGap.Continuum.FiniteBistochasticQKernel.FiniteBistochasticQKernel
