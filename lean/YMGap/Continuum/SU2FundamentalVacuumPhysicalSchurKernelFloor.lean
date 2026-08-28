/-
# The fundamental-vacuum physical Schur floor

The all-zero four-valent SU(2) carrier has exactly one left channel and one
right channel.  Row normalization therefore forces its unique recoupling
entry to equal one.  Tensoring that deterministic vacuum block with the
fundamental block improves the relevant paired floor from `1/16` to `1/4`.

This is the local algebra expected at a switching surface carried by one
physical replica while the other replica remains vacuum.  It does not build
such a surface or prove that its alternate target disconnects the global
strand component.

Constructive contract: finite carrier uniqueness, exact row normalization,
and `Q'` order only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor

set_option maxHeartbeats 1000000

namespace YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The vacuum carriers are singletons -/

def vacuumFixedLeft : FixedLeftCGChannel 0 0 0 0 where
  k := 0
  k_le := by decide
  r := 0
  r_le := by decide
  degree_eq := by decide

def vacuumFixedRight : FixedRightCGChannel 0 0 0 0 where
  p := 0
  p_le := by decide
  r := 0
  r_le := by decide
  degree_eq := by decide

theorem vacuumFixedLeft_unique (channel : FixedLeftCGChannel 0 0 0 0) :
    channel = vacuumFixedLeft := by
  apply fixedLeftChannel_eq_of_k_eq
  change channel.k = 0
  have hk := Nat.le_min.mp channel.k_le
  omega

theorem vacuumFixedRight_unique (channel : FixedRightCGChannel 0 0 0 0) :
    channel = vacuumFixedRight := by
  apply fixedRightChannel_eq_of_p_eq
  change channel.p = 0
  have hp := Nat.le_min.mp channel.p_le
  omega

theorem fixedRightChannels_zero :
    fixedRightChannels 0 0 0 0 = [vacuumFixedRight] := by
  have hmem := fixedRightChannels_complete vacuumFixedRight
  have hnodup := fixedRightChannels_nodup 0 0 0 0
  cases hitems : fixedRightChannels 0 0 0 0 with
  | nil =>
    rw [hitems] at hmem
    exact False.elim (List.not_mem_nil hmem)
  | cons head tail =>
    rw [hitems] at hnodup
    have hhead : head = vacuumFixedRight := vacuumFixedRight_unique head
    have htail : tail = [] := by
      cases tail with
      | nil => rfl
      | cons next rest =>
        have hparts := List.nodup_cons.mp hnodup
        have hnext : next = vacuumFixedRight := vacuumFixedRight_unique next
        exact False.elim (hparts.1 (by
          rw [hnext, ← hhead]
          exact List.mem_cons_self))
    rw [hhead, htail]

/-! ## 2. The vacuum recoupling entry equals one -/

theorem vacuum_physicalSchurKernel_eqv_one
    (source : FixedLeftCGChannel 0 0 0 0)
    (target : FixedRightCGChannel 0 0 0 0) :
    physicalSchurRecouplingKernelAt source target ≈ 1 := by
  rw [vacuumFixedRight_unique target]
  have h := physicalSchurRecoupling_list_row_normalized source
  rw [show physicalSchurRightTargets source =
      fixedRightChannels 0 0 0 0 by rfl, fixedRightChannels_zero] at h
  simpa only [listQSum, Q'.add_zero'] using h

theorem vacuum_physicalSchurKernel_pos
    (source : FixedLeftCGChannel 0 0 0 0)
    (target : FixedRightCGChannel 0 0 0 0) :
    (0 : Q') < physicalSchurRecouplingKernelAt source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv (vacuum_physicalSchurKernel_eqv_one source target))

/-! ## 3. One fundamental replica and one vacuum replica -/

theorem fundamental_vacuum_twoReplicaSchurKernel_floor
    (source : FixedLeftCGChannel 1 1 1 1 ×
      FixedLeftCGChannel 0 0 0 0)
    (target : FixedRightCGChannel 1 1 1 1 ×
      FixedRightCGChannel 0 0 0 0) :
    oneQuarter ≤
      tensorWeight
        (physicalSchurBistochasticKernel 1 1 1 1)
        (physicalSchurBistochasticKernel 0 0 0 0)
        source target := by
  have hfundamental := fundamental_physicalSchurKernel_oneQuarter_le
    source.1 target.1
  have hvacuum := vacuum_physicalSchurKernel_eqv_one source.2 target.2
  have hproduct :
      physicalSchurRecouplingKernelAt source.1 target.1 *
          physicalSchurRecouplingKernelAt source.2 target.2 ≈
        physicalSchurRecouplingKernelAt source.1 target.1 :=
    Q'.eqv_trans _
      (physicalSchurRecouplingKernelAt source.1 target.1 * 1) _
      (Q'.mul_eqv_congr_left
        (physicalSchurRecouplingKernelAt source.1 target.1)
        (physicalSchurRecouplingKernelAt source.2 target.2) 1 hvacuum)
      (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _ hfundamental (Q'.ge_of_eqv hproduct)

theorem fundamental_vacuum_twoReplicaSchurKernel_pos
    (source : FixedLeftCGChannel 1 1 1 1 ×
      FixedLeftCGChannel 0 0 0 0)
    (target : FixedRightCGChannel 1 1 1 1 ×
      FixedRightCGChannel 0 0 0 0) :
    (0 : Q') <
      tensorWeight
        (physicalSchurBistochasticKernel 1 1 1 1)
        (physicalSchurBistochasticKernel 0 0 0 0)
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (fundamental_vacuum_twoReplicaSchurKernel_floor source target)

theorem vacuum_fundamental_twoReplicaSchurKernel_floor
    (source : FixedLeftCGChannel 0 0 0 0 ×
      FixedLeftCGChannel 1 1 1 1)
    (target : FixedRightCGChannel 0 0 0 0 ×
      FixedRightCGChannel 1 1 1 1) :
    oneQuarter ≤
      tensorWeight
        (physicalSchurBistochasticKernel 0 0 0 0)
        (physicalSchurBistochasticKernel 1 1 1 1)
        source target := by
  have hfundamental := fundamental_physicalSchurKernel_oneQuarter_le
    source.2 target.2
  have hvacuum := vacuum_physicalSchurKernel_eqv_one source.1 target.1
  have hproduct :
      physicalSchurRecouplingKernelAt source.1 target.1 *
          physicalSchurRecouplingKernelAt source.2 target.2 ≈
        physicalSchurRecouplingKernelAt source.2 target.2 :=
    Q'.eqv_trans _
      (1 * physicalSchurRecouplingKernelAt source.2 target.2) _
      (Q'.mul_eqv_congr_right
        (physicalSchurRecouplingKernelAt source.1 target.1) 1
        (physicalSchurRecouplingKernelAt source.2 target.2) hvacuum)
      (Q'.one_mul_eqv _)
  exact Q'.le_trans' _ _ _ hfundamental (Q'.ge_of_eqv hproduct)

theorem vacuum_fundamental_twoReplicaSchurKernel_pos
    (source : FixedLeftCGChannel 0 0 0 0 ×
      FixedLeftCGChannel 1 1 1 1)
    (target : FixedRightCGChannel 0 0 0 0 ×
      FixedRightCGChannel 1 1 1 1) :
    (0 : Q') <
      tensorWeight
        (physicalSchurBistochasticKernel 0 0 0 0)
        (physicalSchurBistochasticKernel 1 1 1 1)
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (vacuum_fundamental_twoReplicaSchurKernel_floor source target)

end YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor

#print axioms YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor.vacuum_physicalSchurKernel_eqv_one
#print axioms YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor.fundamental_vacuum_twoReplicaSchurKernel_floor
#print axioms YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor.fundamental_vacuum_twoReplicaSchurKernel_pos
#print axioms YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor.vacuum_fundamental_twoReplicaSchurKernel_floor
#print axioms YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor.vacuum_fundamental_twoReplicaSchurKernel_pos
