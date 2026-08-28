/-
# A total first-target selector for physical-pair slab packages

The physical-pair recoupling package is dependent on a link valence between
zero and six.  Applying a generic finite-target selector directly at a
symbolic valence asks definitional reduction to discover which package is in
scope.  This module performs that dependency split once and explicitly.

At valences zero through three the carrier is `Unit`.  At valences four
through six, complete source enumeration and finite bistochastic carrier
balance construct the first literal target.  Geometric valence bounds remove
all remaining cases.

Constructive contract: the seven explicit valence cases and finite carrier
balance only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticPointedTarget
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingFirstTarget

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticPointedTarget
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness

/-- Choose one literal target for every possible corrected-slab link package.
The supplied source makes nonemptiness constructive in the nontrivial cases. -/
def slabPhysicalPairRecouplingFirstTarget {extent : Nat} :
    (degree : Nat) ->
    (D : SlabPhysicalPairRecouplingData extent degree) ->
    (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source) ->
      (slabPhysicalPairRecouplingKernelPackage degree D).Target
  | 0, _, _ => ()
  | 1, _, _ => ()
  | 2, _, _ => ()
  | 3, _, _ => ()
  | 4, D, source =>
      (FiniteBistochasticPointedTarget.FiniteBistochasticQKernel.firstTargetOfSource
        (slabPhysicalPairRecouplingKernelPackageFour D).kernel source
        (slabPhysicalPairRecouplingKernelPackageFour_sources_complete
          D source)).target
  | 5, D, source =>
      (FiniteBistochasticPointedTarget.FiniteBistochasticQKernel.firstTargetOfSource
        (slabPhysicalPairRecouplingKernelPackageFive D).kernel source
        (slabPhysicalPairRecouplingKernelPackageFive_sources_complete
          D source)).target
  | 6, D, source =>
      (FiniteBistochasticPointedTarget.FiniteBistochasticQKernel.firstTargetOfSource
        (slabPhysicalPairRecouplingKernelPackageSix D).kernel source
        (slabPhysicalPairRecouplingKernelPackageSix_sources_complete
          D source)).target
  | degree + 7, D, _ => False.elim (by
      have hdegree := D.degree_le_six
      omega)

#print axioms slabPhysicalPairRecouplingFirstTarget

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingFirstTarget
