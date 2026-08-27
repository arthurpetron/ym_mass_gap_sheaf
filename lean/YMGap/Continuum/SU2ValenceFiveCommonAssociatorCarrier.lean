/-
# A common middle carrier for the valence-five associator

The existing iterated row retains the first recoupling target inside a
dependent path type.  For matrix composition one instead needs three common
carrier types: a left tree, the transient tree after the first associator,
and the final right tree.  The transient output `y` belongs only to the
middle carrier; the final carrier retains the physical `(b,c)` intermediate
but forgets that recoupling history.

This module defines those carriers and proves that every existing dependent
two-step path factors pointwise through its canonical common middle state.
It does not yet enumerate all three carriers or sum the matrix product.

Constructive contract: proof-carrying SU(2) fusion data and exact `Q'` only;
no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport

namespace YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier

open YMGap.Constructive
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Source, middle, and final basis carriers -/

/-- A complete left-tree label consists of its three-input left channel and
the retained last fusion step to the fixed output. -/
structure ValenceFiveLeftCarrier (a b c d e : Nat) where
  y : Nat
  firstLeft : FixedLeftCGChannel a b c y
  suffix : CGFusionStep y d e

/-- The common middle tree after the first associator.  Its right channel
contains the physical `(b,c)` intermediate, while `suffix` retains the last
left-tree fusion through the transient output `y`. -/
structure ValenceFiveMiddleCarrier (a b c d e : Nat) where
  y : Nat
  first : FixedRightCGChannel a b c y
  suffix : CGFusionStep y d e

/-- A final fully right-associated label.  The `(b,c)` fusion witness keeps
the first physical intermediate `m`; the second right channel then records
`(m,d)` followed by fusion with `a` to the fixed output `e`. -/
structure ValenceFiveRightCarrier (a b c d e : Nat) where
  m : Nat
  inner : CGFusionStep b c m
  second : FixedRightCGChannel a m d e

/-! ## 2. Channel projections used by the two local associators -/

/-- The second local left channel represented by one common middle state. -/
def ValenceFiveMiddleCarrier.secondLeft {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    FixedLeftCGChannel a middle.first.intermediate d e :=
  fixedLeftChannelOfFusion a middle.first.intermediate d e middle.y
    (fixedRight_outer_fusionOK middle.first) middle.suffix.fusionOK

/-- First associator block on one aligned transient-output fiber. -/
def valenceFiveFirstBlockKernelAt {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e)
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (h : source.y = middle.y) : Q' :=
  physicalSchurRecouplingKernelAt source.firstLeft (h.symm ▸ middle.first)

/-- Second associator block on one aligned `(b,c)`-intermediate fiber. -/
def valenceFiveSecondBlockKernelAt {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (target : ValenceFiveRightCarrier a b c d e)
    (h : middle.first.intermediate = target.m) : Q' :=
  physicalSchurRecouplingKernelAt middle.secondLeft (h.symm ▸ target.second)

theorem valenceFiveFirstBlockKernelAt_nonnegative {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e)
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (h : source.y = middle.y) :
    (0 : Q') ≤ valenceFiveFirstBlockKernelAt source middle h :=
  physicalSchurRecouplingKernelAt_nonnegative _ _

theorem valenceFiveSecondBlockKernelAt_nonnegative {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (target : ValenceFiveRightCarrier a b c d e)
    (h : middle.first.intermediate = target.m) :
    (0 : Q') ≤ valenceFiveSecondBlockKernelAt middle target h :=
  physicalSchurRecouplingKernelAt_nonnegative _ _

/-! ## 3. The old dependent path embeds in the common carriers -/

def valenceFiveLeftCarrierOfChain {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e) :
    ValenceFiveLeftCarrier a b c d e where
  y := chain.y
  firstLeft := chain.prefixChannel
  suffix := chain.third

def valenceFiveMiddleCarrierOfPath {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e)
    (target : ValenceFiveRightTreeTarget chain) :
    ValenceFiveMiddleCarrier a b c d e where
  y := chain.y
  first := target.first
  suffix := chain.third

def valenceFiveRightCarrierOfPath {a b c d e : Nat}
    {chain : FixedLeftCGValenceFive a b c d e}
    (target : ValenceFiveRightTreeTarget chain) :
    ValenceFiveRightCarrier a b c d e where
  m := target.first.intermediate
  inner :=
    { order := target.first.p
      order_le := target.first.p_le
      output_eq := rfl }
  second := target.second

theorem valenceFiveMiddleCarrierOfPath_secondLeft
    {a b c d e : Nat} (chain : FixedLeftCGValenceFive a b c d e)
    (target : ValenceFiveRightTreeTarget chain) :
    (valenceFiveMiddleCarrierOfPath chain target).secondLeft =
      valenceFiveSecondLeftChannel chain target.first := by
  rfl

/-- The first block at the canonical middle point is exactly the first
factor of the existing iterated Schur row. -/
theorem valenceFiveFirstBlockKernelAt_path {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e)
    (target : ValenceFiveRightTreeTarget chain) :
    valenceFiveFirstBlockKernelAt
        (valenceFiveLeftCarrierOfChain chain)
        (valenceFiveMiddleCarrierOfPath chain target) rfl ≈
      physicalSchurRecouplingKernelAt chain.prefixChannel target.first := by
  simp only [valenceFiveFirstBlockKernelAt,
    valenceFiveLeftCarrierOfChain, valenceFiveMiddleCarrierOfPath]
  exact Q'.eqv_refl _

/-- The second block at the same middle point is exactly the second factor
of the existing iterated Schur row. -/
theorem valenceFiveSecondBlockKernelAt_path {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e)
    (target : ValenceFiveRightTreeTarget chain) :
    valenceFiveSecondBlockKernelAt
        (valenceFiveMiddleCarrierOfPath chain target)
        (valenceFiveRightCarrierOfPath target) rfl ≈
      physicalSchurRecouplingKernelAt
        (valenceFiveSecondLeftChannel chain target.first) target.second := by
  simp only [valenceFiveSecondBlockKernelAt,
    valenceFiveMiddleCarrierOfPath, valenceFiveRightCarrierOfPath]
  exact Q'.eqv_refl _

/-- **Every old dependent two-step weight is the product of two entries on
the new common-carrier path.** -/
theorem valenceFiveIteratedSchurKernelAt_common_path
    {a b c d e : Nat} (chain : FixedLeftCGValenceFive a b c d e)
    (target : ValenceFiveRightTreeTarget chain) :
    valenceFiveFirstBlockKernelAt
        (valenceFiveLeftCarrierOfChain chain)
        (valenceFiveMiddleCarrierOfPath chain target) rfl *
      valenceFiveSecondBlockKernelAt
        (valenceFiveMiddleCarrierOfPath chain target)
        (valenceFiveRightCarrierOfPath target) rfl ≈
      valenceFiveIteratedSchurKernelAt chain target := by
  refine Q'.eqv_trans _
    (physicalSchurRecouplingKernelAt chain.prefixChannel target.first *
      valenceFiveSecondBlockKernelAt
        (valenceFiveMiddleCarrierOfPath chain target)
        (valenceFiveRightCarrierOfPath target) rfl) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (valenceFiveFirstBlockKernelAt_path chain target)
  · exact Q'.eqv_trans _
      (physicalSchurRecouplingKernelAt chain.prefixChannel target.first *
        physicalSchurRecouplingKernelAt
          (valenceFiveSecondLeftChannel chain target.first) target.second) _
      (Q'.mul_eqv_congr_left
        (physicalSchurRecouplingKernelAt chain.prefixChannel target.first)
        _ _ (valenceFiveSecondBlockKernelAt_path chain target))
      (Q'.eqv_refl _)

end YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier

#print axioms YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier.ValenceFiveMiddleCarrier.secondLeft
#print axioms YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier.valenceFiveFirstBlockKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier.valenceFiveSecondBlockKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier.valenceFiveMiddleCarrierOfPath_secondLeft
#print axioms YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier.valenceFiveIteratedSchurKernelAt_common_path
