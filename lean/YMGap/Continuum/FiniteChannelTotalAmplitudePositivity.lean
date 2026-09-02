/-
# Strict positivity of a finite channel total

This is the generic finite-sum interface: one positive member of a
pointwise-nonnegative amplitude column makes its total strictly positive.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
import YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity

namespace YMGap.Continuum.FiniteChannelTotalAmplitudePositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity

theorem finiteChannelTotalAmplitude_pos_of_mem
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    {state : State} {channel : Channel}
    (hstate : state ∈ states)
    (hnonnegative : ∀ candidate,
      (0 : Q') ≤ amplitude candidate channel)
    (hpositive : (0 : Q') < amplitude state channel) :
    (0 : Q') <
      finiteChannelTotalAmplitude states amplitude channel := by
  unfold finiteChannelTotalAmplitude
  exact listQSum_pos_of_mem
    (fun candidate => amplitude candidate channel)
    hnonnegative states (item := state) hstate hpositive

end YMGap.Continuum.FiniteChannelTotalAmplitudePositivity

#print axioms
  YMGap.Continuum.FiniteChannelTotalAmplitudePositivity.finiteChannelTotalAmplitude_pos_of_mem
