/-
# A constructive target point above an enumerated source

A finite bistochastic kernel cannot have a written source but no written
target: its two carrier lists have equal length.  This module packages that
elementary consequence as a Type-valued compiler.  Given a literal member of
the source enumeration, it returns the first literal target together with its
membership proof.

The construction is intentionally weaker than a positivity selector.  It is
used where every local target coordinate is already known positive and only a
typed complete target assignment is needed.

Constructive contract: finite carrier balance and structural list
elimination only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
or noncomputable declaration.
-/

import YMGap.Continuum.FiniteBistochasticCarrierBalance

namespace YMGap.Continuum.FiniteBistochasticPointedTarget

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticCarrierBalance
open YMGap.Continuum.FiniteBistochasticQKernel

/-- One literal target of a finite kernel, retaining enumeration membership
as data. -/
structure FiniteBistochasticPointedTarget
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target) : Type where
  target : Target
  target_mem : target ∈ kernel.targets

/-- A literal enumerated source constructively supplies the first literal
target.  Bistochastic carrier balance rules out the empty-target branch. -/
def FiniteBistochasticQKernel.firstTargetOfSource
    {Source Target : Type}
    (kernel : FiniteBistochasticQKernel Source Target)
    (source : Source) (hsource : source ∈ kernel.sources) :
    FiniteBistochasticPointedTarget kernel := by
  cases htargets : kernel.targets with
  | nil =>
      have hlength :=
        FiniteBistochasticCarrierBalance.FiniteBistochasticQKernel.sources_length_eq_targets_length
          kernel
      have hsourcesLength : kernel.sources.length = 0 := by
        rw [hlength, htargets]
        rfl
      have hsourcesNil : kernel.sources = [] :=
        List.length_eq_zero_iff.mp hsourcesLength
      rw [hsourcesNil] at hsource
      exact False.elim (List.not_mem_nil hsource)
  | cons target rest =>
      exact
        { target := target
          target_mem := by
            rw [htargets]
            exact List.mem_cons_self }

#print axioms FiniteBistochasticPointedTarget
#print axioms FiniteBistochasticQKernel.firstTargetOfSource

end YMGap.Continuum.FiniteBistochasticPointedTarget
