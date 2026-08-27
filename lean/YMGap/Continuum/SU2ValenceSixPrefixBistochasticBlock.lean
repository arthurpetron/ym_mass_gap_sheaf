/-
# The first two valence-six associators as an indexed valence-five block sum

The first four external factors of a six-valent chain form a complete
valence-five associator with retained output `z`.  The last fusion `z,e -> f`
is untouched by those first two moves.  Hence their all-source/all-target
matrix is not a new carrier calculation: it is the dependent block sum of the
already completed valence-five matrices over every admissible `z`.

This module performs that contraction with the generic indexed-sum compiler,
and embeds the production chain and every old three-step dependent target in
the new common carrier.  The remaining third associator is a separate block
diagonal matrix in the physical inner labels.

Constructive contract: proof-carrying SU(2) fusion data, finite lists, and
exact `Q'` algebra only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
import YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
import YMGap.Continuum.SU2ValenceSixIteratedSchurTransport

namespace YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport
open YMGap.Continuum.SU2ValenceSixIteratedSchurTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Retained output sectors -/

/-- Possible outputs of the first four external factors which can still fuse
with `e` to the fixed final output `f`. -/
def valenceSixPrefixOutputs (a b c d e f : Nat) : List Nat :=
  (List.range (a + b + c + d + 1)).filter (fun z => fusionOK z e f)

private theorem range_nodup (bound : Nat) : (List.range bound).Nodup := by
  induction bound with
  | zero => exact List.nodup_nil
  | succ bound ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

theorem valenceSixPrefixOutputs_nodup (a b c d e f : Nat) :
    (valenceSixPrefixOutputs a b c d e f).Nodup :=
  List.filter_sublist.nodup (range_nodup (a + b + c + d + 1))

private theorem valenceFiveChain_output_le_total {a b c d z : Nat}
    (chain : FixedLeftCGValenceFive a b c d z) :
    z ≤ a + b + c + d := by
  have hfirst := chain.first.output_eq
  have hsecond := chain.second.output_eq
  have hthird := chain.third.output_eq
  omega

theorem valenceSixChain_z_mem_prefixOutputs {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f) :
    chain.z ∈ valenceSixPrefixOutputs a b c d e f := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr
      (Nat.lt_succ_of_le
        (valenceFiveChain_output_le_total
          (YMGap.Continuum.SU2ValenceSixIteratedSchurTransport.FixedLeftCGValenceSix.valenceFivePrefix
            chain))),
    chain.fourth.fusionOK⟩

abbrev ValenceSixPrefixIndex (a b c d e f : Nat) :=
  {z // z ∈ valenceSixPrefixOutputs a b c d e f}

/-- The suffix carried by a written retained-output sector. -/
def valenceSixPrefixSuffix {a b c d e f : Nat}
    (index : ValenceSixPrefixIndex a b c d e f) :
    CGFusionStep index.val e f :=
  cgFusionStepOfFusionOK index.val e f
    (List.mem_filter.mp index.property).2

/-! ## 2. The dependent block sum -/

abbrev ValenceSixPrefixLeftFamily (a b c d : Nat) (z : Nat) :=
  ValenceFiveLeftCarrier a b c d z

abbrev ValenceSixPrefixRightFamily (a b c d : Nat) (z : Nat) :=
  ValenceFiveRightCarrier a b c d z

abbrev ValenceSixLeftCarrier (a b c d e f : Nat) :=
  IndexedSource
    (valenceSixPrefixOutputs a b c d e f)
    (ValenceSixPrefixLeftFamily a b c d)

abbrev ValenceSixCommonMiddleCarrier (a b c d e f : Nat) :=
  IndexedTarget
    (valenceSixPrefixOutputs a b c d e f)
    (ValenceSixPrefixRightFamily a b c d)

/-- The first two valence-six associators are the direct sum of complete
valence-five matrices over the retained output `z`. -/
def valenceSixPrefixBistochasticKernel (a b c d e f : Nat) :
    FiniteBistochasticQKernel
      (ValenceSixLeftCarrier a b c d e f)
      (ValenceSixCommonMiddleCarrier a b c d e f) :=
  indexedSum
    (valenceSixPrefixOutputs a b c d e f)
    (valenceSixPrefixOutputs_nodup a b c d e f)
    (ValenceSixPrefixLeftFamily a b c d)
    (ValenceSixPrefixRightFamily a b c d)
    (fun z => valenceFiveBistochasticKernel a b c d z)

theorem valenceSixPrefixKernel_row_normalized {a b c d e f : Nat}
    (source : ValenceSixLeftCarrier a b c d e f) :
    listQSum
        ((valenceSixPrefixBistochasticKernel a b c d e f).weight source)
        (valenceSixPrefixBistochasticKernel a b c d e f).targets ≈ 1 :=
  (valenceSixPrefixBistochasticKernel a b c d e f).row_normalized source

theorem valenceSixPrefixKernel_column_normalized {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    listQSum
        (fun source =>
          (valenceSixPrefixBistochasticKernel a b c d e f).weight
            source middle)
        (valenceSixPrefixBistochasticKernel a b c d e f).sources ≈ 1 :=
  (valenceSixPrefixBistochasticKernel a b c d e f).column_normalized middle

/-! ## 3. Production chain and old dependent targets -/

def valenceSixLeftCarrierOfChain {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f) :
    ValenceSixLeftCarrier a b c d e f where
  index := ⟨chain.z, valenceSixChain_z_mem_prefixOutputs chain⟩
  value := valenceFiveLeftCarrierOfChain
    (YMGap.Continuum.SU2ValenceSixIteratedSchurTransport.FixedLeftCGValenceSix.valenceFivePrefix
      chain)

def valenceSixCommonMiddleOfPath {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) :
    ValenceSixCommonMiddleCarrier a b c d e f where
  index := ⟨chain.z, valenceSixChain_z_mem_prefixOutputs chain⟩
  value := valenceFiveRightCarrierOfPath target.prior

/-- At the production retained-output sector, the first-two-move matrix entry
is exactly the corresponding entry of the complete valence-five matrix. -/
theorem valenceSixPrefixKernelAt_common_path {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) :
    (valenceSixPrefixBistochasticKernel a b c d e f).weight
        (valenceSixLeftCarrierOfChain chain)
        (valenceSixCommonMiddleOfPath chain target) ≈
      (valenceFiveBistochasticKernel a b c d chain.z).weight
        (valenceFiveLeftCarrierOfChain
          (YMGap.Continuum.SU2ValenceSixIteratedSchurTransport.FixedLeftCGValenceSix.valenceFivePrefix
            chain))
        (valenceFiveRightCarrierOfPath target.prior) := by
  exact indexedSumWeight_same
    (valenceSixPrefixOutputs a b c d e f)
    (ValenceSixPrefixLeftFamily a b c d)
    (ValenceSixPrefixRightFamily a b c d)
    (fun z => valenceFiveBistochasticKernel a b c d z)
    ⟨chain.z, valenceSixChain_z_mem_prefixOutputs chain⟩
    (valenceFiveLeftCarrierOfChain
      (YMGap.Continuum.SU2ValenceSixIteratedSchurTransport.FixedLeftCGValenceSix.valenceFivePrefix
        chain))
    (valenceFiveRightCarrierOfPath target.prior)

end YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock

#print axioms YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock.valenceSixChain_z_mem_prefixOutputs
#print axioms YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock.valenceSixPrefixBistochasticKernel
#print axioms YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock.valenceSixPrefixKernel_row_normalized
#print axioms YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock.valenceSixPrefixKernel_column_normalized
#print axioms YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock.valenceSixLeftCarrierOfChain
#print axioms YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock.valenceSixCommonMiddleOfPath
#print axioms YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock.valenceSixPrefixKernelAt_common_path
