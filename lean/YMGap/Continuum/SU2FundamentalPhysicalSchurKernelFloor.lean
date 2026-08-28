/-
# A sharp positive floor on the fundamental physical Schur block

The physical four-valent SU(2) recoupling kernel has two channels when all
four external doubled-spin labels are fundamental.  The existing exact Schur
calculation gives its four entries as `1/4, 3/4, 3/4, 1/4`.

This module first proves that the displayed singlet and triplet channels
exhaust both proof-carrying carrier types.  It then contracts the four exact
values to the sharp entrywise floor `1/4`.  Tensoring the two replica blocks
gives the sharp local paired floor `1/16`.

This is a strictly local non-abelian recoupling estimate.  It does not assert
that a complete corrected-slab source contains such a pivotal block, that a
chosen local target disconnects the global root-target strand component, or
that a product of local floors is uniform in volume.

Constructive contract: exact finite SU(2) channel classification and `Q'`
order only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernelComposition
import YMGap.Continuum.SU2PhysicalSchurBistochasticKernel

namespace YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The fundamental carriers have exactly two channels -/

theorem fundamentalFixedLeft_eq_singlet_or_triplet
    (channel : FixedLeftCGChannel 1 1 1 1) :
    channel = fundamentalFixedLeftSinglet ∨
      channel = fundamentalFixedLeftTriplet := by
  have hk : channel.k = 0 ∨ channel.k = 1 := by
    have hbound := Nat.le_min.mp channel.k_le
    omega
  rcases hk with hk | hk
  · exact Or.inr
      (fixedLeftChannel_eq_of_k_eq
        channel fundamentalFixedLeftTriplet hk)
  · exact Or.inl
      (fixedLeftChannel_eq_of_k_eq
        channel fundamentalFixedLeftSinglet hk)

theorem fundamentalFixedRight_eq_singlet_or_triplet
    (channel : FixedRightCGChannel 1 1 1 1) :
    channel = fundamentalFixedRightSinglet ∨
      channel = fundamentalFixedRightTriplet := by
  have hp : channel.p = 0 ∨ channel.p = 1 := by
    have hbound := Nat.le_min.mp channel.p_le
    omega
  rcases hp with hp | hp
  · exact Or.inr
      (fixedRightChannel_eq_of_p_eq
        channel fundamentalFixedRightTriplet hp)
  · exact Or.inl
      (fixedRightChannel_eq_of_p_eq
        channel fundamentalFixedRightSinglet hp)

/-! ## 2. Every one-replica entry is at least one quarter -/

theorem fundamental_physicalSchurKernel_oneQuarter_le
    (source : FixedLeftCGChannel 1 1 1 1)
    (target : FixedRightCGChannel 1 1 1 1) :
    oneQuarter ≤ physicalSchurRecouplingKernelAt source target := by
  rcases fundamentalFixedLeft_eq_singlet_or_triplet source with
      rfl | rfl <;>
    rcases fundamentalFixedRight_eq_singlet_or_triplet target with
      rfl | rfl
  · exact Q'.ge_of_eqv fundamental_physicalSchurKernel_values.1
  · exact Q'.le_trans' _ _ _ (by decide)
      (Q'.ge_of_eqv fundamental_physicalSchurKernel_values.2.1)
  · exact Q'.le_trans' _ _ _ (by decide)
      (Q'.ge_of_eqv fundamental_physicalSchurKernel_values.2.2.1)
  · exact Q'.ge_of_eqv fundamental_physicalSchurKernel_values.2.2.2

theorem fundamental_physicalSchurKernel_pos
    (source : FixedLeftCGChannel 1 1 1 1)
    (target : FixedRightCGChannel 1 1 1 1) :
    (0 : Q') < physicalSchurRecouplingKernelAt source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (fundamental_physicalSchurKernel_oneQuarter_le source target)

/-! ## 3. The paired local block has the sharp floor one sixteenth -/

def fundamentalPairedFloor : Q' := Q'.mkPos 1 16 (by decide)

theorem fundamentalPairedFloor_pos : (0 : Q') < fundamentalPairedFloor := by
  decide

theorem fundamental_twoReplicaSchurKernel_floor
    (source : FixedLeftCGChannel 1 1 1 1 ×
      FixedLeftCGChannel 1 1 1 1)
    (target : FixedRightCGChannel 1 1 1 1 ×
      FixedRightCGChannel 1 1 1 1) :
    fundamentalPairedFloor ≤
      tensorWeight
        (physicalSchurBistochasticKernel 1 1 1 1)
        (physicalSchurBistochasticKernel 1 1 1 1)
        source target := by
  have hleft := fundamental_physicalSchurKernel_oneQuarter_le
    source.1 target.1
  have hright := fundamental_physicalSchurKernel_oneQuarter_le
    source.2 target.2
  have hproduct : oneQuarter * oneQuarter ≤
      physicalSchurRecouplingKernelAt source.1 target.1 *
        physicalSchurRecouplingKernelAt source.2 target.2 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hleft
        (by decide : (0 : Q') ≤ oneQuarter))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hright
        (physicalSchurRecouplingKernelAt_nonnegative source.1 target.1))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : fundamentalPairedFloor ≈
      oneQuarter * oneQuarter)) hproduct

theorem fundamental_twoReplicaSchurKernel_pos
    (source : FixedLeftCGChannel 1 1 1 1 ×
      FixedLeftCGChannel 1 1 1 1)
    (target : FixedRightCGChannel 1 1 1 1 ×
      FixedRightCGChannel 1 1 1 1) :
    (0 : Q') <
      tensorWeight
        (physicalSchurBistochasticKernel 1 1 1 1)
        (physicalSchurBistochasticKernel 1 1 1 1)
        source target :=
  Q'.pos_of_lt_of_le fundamentalPairedFloor_pos
    (fundamental_twoReplicaSchurKernel_floor source target)

end YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor

#print axioms YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor.fundamentalFixedLeft_eq_singlet_or_triplet
#print axioms YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor.fundamentalFixedRight_eq_singlet_or_triplet
#print axioms YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor.fundamental_physicalSchurKernel_oneQuarter_le
#print axioms YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor.fundamental_physicalSchurKernel_pos
#print axioms YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor.fundamental_twoReplicaSchurKernel_floor
#print axioms YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor.fundamental_twoReplicaSchurKernel_pos
