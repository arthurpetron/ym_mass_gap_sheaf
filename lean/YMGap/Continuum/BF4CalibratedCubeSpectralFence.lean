/-
# Exact six-face cube fence for the calibrated BF4 Mehler rate

The central lower cube is a genuine non-vacuum positive physical row.  Its
geometric BF4 spin-network coefficient at the first positive diagonal order
and empty cross-feature channel is exactly `1/16`.  Consequently the
vacuum-normalized rank-one Mehler Gram has cube diagonal `1/256`.

This module converts that exact Peter--Weyl coefficient into a necessary
scalar condition for the calibrated spectral `1/8` estimate.  It is a
kernel-checked diagnostic for the lowest endpoint order: any proof of the
eighth must control the physical cube marginal strongly enough to dominate
the displayed diagonal defect.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerCubePositiveRow
import YMGap.Continuum.BF4PhysicalRecenteredEndpointRate

namespace YMGap.Continuum.BF4CalibratedCubeSpectralFence

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalRecenteredEndpointRate
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Exact five-Haar coefficient of the genuine six-face BF4 cube
spin-network at the first positivity-preserving diagonal order. -/
theorem centralLowerCube_emptyHalf_eqv_sixteenth :
    bf4MehlerHalfAmplitude
        1 centralLowerCubeState [] ≈
      Q'.mkPos 1 16 (by decide) := by
  decide

/-- The corresponding normalized rank-one Mehler diagonal is exactly
`(1/16)^2 = 1/256`. -/
theorem normalizedMehlerGram_cube_cube_eqv_oneTwoFiftySixth :
    normalizedBF4MehlerGramJoint
        0 0 centralLowerCubeState centralLowerCubeState ≈
      Q'.mkPos 1 256 (by decide) := by
  decide

/-- The vacuum-to-cube entry of the same rank-one endpoint is exactly
`1/16`. -/
theorem normalizedMehlerGram_vacuum_cube_eqv_sixteenth :
    normalizedBF4MehlerGramJoint
        0 0 zeroEdgeLabelling centralLowerCubeState ≈
      Q'.mkPos 1 16 (by decide) := by
  decide

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items →
        value item ≤ listQSum value items
  | [], _, hmember =>
      False.elim (List.not_mem_nil hmember)
  | head :: tail, item, hmember => by
      rcases List.mem_cons.mp hmember with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun candidate _ => hvalue candidate))
      · have hinduction :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail)
              (value head) (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail)
                (value head)))
        exact Q'.le_trans' _ _ _
          hinduction htailLe

/-- The cube diagonal defect is one explicit summand of the complete
centered Mehler row mass. -/
theorem cube_diagonal_defect_le_centeredRowMass
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    let cubeMarginal :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 centralLowerCubeState
    Q'.abs
        (Q'.mkPos 1 256 (by decide) +
          (-(cubeMarginal * cubeMarginal))) ≤
      exactCenteredMehlerGramRowMass
        w (Q'.le_of_lt hw) K 0 0 0
        centralLowerCubeState := by
  let cubeMarginal :=
    centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0 centralLowerCubeState
  let value := fun target =>
    Q'.abs
      (normalizedBF4MehlerGramJoint
            0 0 centralLowerCubeState target +
        (-centralPhysicalVacuumJoint
            w (Q'.le_of_lt hw) K 0
            centralLowerCubeState target))
  have hmember :
      value centralLowerCubeState ≤
        listQSum value
          (centralPositiveHalfStates
            w (Q'.le_of_lt hw) K 0) :=
    listQSum_member_le_nonnegative
      value
      (fun target => Q'.abs_nonneg _)
      (centralPositiveHalfStates
        w (Q'.le_of_lt hw) K 0)
      (centralLowerCubeState_mem_centralPositiveHalfStates
        hw hK)
  have hentry :
      value centralLowerCubeState ≈
        Q'.abs
          (Q'.mkPos 1 256 (by decide) +
            (-(cubeMarginal * cubeMarginal))) := by
    unfold value centralPhysicalVacuumJoint cubeMarginal
    exact Q'.abs_eqv_congr
      (Q'.add_eqv_congr_right _ _ _
        normalizedMehlerGram_cube_cube_eqv_oneTwoFiftySixth)
  unfold exactCenteredMehlerGramRowMass
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hentry) hmember

/-- The executable centered rate must pay the cube diagonal defect. -/
theorem cube_diagonal_defect_le_centeredRate_mul_marginal
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    let cubeMarginal :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 centralLowerCubeState
    Q'.abs
        (Q'.mkPos 1 256 (by decide) +
          (-(cubeMarginal * cubeMarginal))) ≤
      exactCenteredMehlerGramRate
          w (Q'.le_of_lt hw) K 0 0 0 *
        cubeMarginal := by
  exact Q'.le_trans' _ _ _
    (cube_diagonal_defect_le_centeredRowMass hw hK)
    (exactCenteredMehlerGramRowMass_le_rate_mul_marginal
      (centralLowerCubeState_mem_centralPositiveHalfStates
        hw hK))

/-- After stationary-vacuum square calibration, the same exact cube defect
is paid by the calibrated endpoint rate. -/
theorem calibrated_cube_diagonal_defect_le_rate_mul_marginal
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    let pi0 :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
    let cubeMarginal :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 centralLowerCubeState
    (pi0 * pi0) *
        Q'.abs
          (Q'.mkPos 1 256 (by decide) +
            (-(cubeMarginal * cubeMarginal))) ≤
      (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w (Q'.le_of_lt hw) K 0 0 0).rate *
        cubeMarginal := by
  let pi0 :=
    centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
  let cubeMarginal :=
    centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0 centralLowerCubeState
  let centeredRate :=
    exactCenteredMehlerGramRate
      w (Q'.le_of_lt hw) K 0 0 0
  have hbase :=
    cube_diagonal_defect_le_centeredRate_mul_marginal
      hw hK
  have hpi0nonnegative :
      (0 : Q') ≤ pi0 :=
    centralPhysicalRowMarginal_nonnegative
      (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
  have hsquare :
      (0 : Q') ≤ pi0 * pi0 :=
    Q'.mul_nonneg _ _ hpi0nonnegative hpi0nonnegative
  have hscaled :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hbase hsquare
  refine Q'.le_trans' _ _ _ hscaled ?_
  exact Q'.le_of_eqv (by
    change
      (pi0 * pi0) * (centeredRate * cubeMarginal) ≈
        ((pi0 * pi0) * centeredRate) * cubeMarginal
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (pi0 * pi0) centeredRate cubeMarginal))

/-- **Lowest-order calibrated `1/8` obstruction.**

If the displayed physical vacuum/cube marginals make the exact cube defect
larger than the available eighth, then the calibrated spectral eighth is
false at diagonal order zero and cross order zero. -/
theorem not_calibrated_rate_le_eighth_of_cube_defect
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K)
    (hdefect :
      let pi0 :=
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
      let cubeMarginal :=
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 centralLowerCubeState
      Q'.mkPos 1 8 (by decide) * cubeMarginal <
        (pi0 * pi0) *
          Q'.abs
            (Q'.mkPos 1 256 (by decide) +
              (-(cubeMarginal * cubeMarginal)))) :
    ¬
      (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w (Q'.le_of_lt hw) K 0 0 0).rate ≤
        Q'.mkPos 1 8 (by decide) := by
  intro hrate
  let cubeMarginal :=
    centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0 centralLowerCubeState
  have hcubenonnegative :
      (0 : Q') ≤ cubeMarginal :=
    centralPhysicalRowMarginal_nonnegative
      (Q'.le_of_lt hw) K 0 centralLowerCubeState
  have hscaledRate :
      (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
            w (Q'.le_of_lt hw) K 0 0 0).rate *
          cubeMarginal ≤
        Q'.mkPos 1 8 (by decide) * cubeMarginal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hrate hcubenonnegative
  have hreverse :=
    Q'.le_trans' _ _ _
      (calibrated_cube_diagonal_defect_le_rate_mul_marginal
        hw hK)
      hscaledRate
  exact Int.not_lt_of_ge hreverse hdefect

/-! ## Correct post-calibration physical centering -/

/-- The cube diagonal of the physically recentered endpoint is the exact
square-calibrated value `pi0^2 / 256`. -/
theorem physicallyRecentered_cube_entry_eqv
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) :
    let pi0 :=
      centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
        w hw K 0 0 0).joint
        centralLowerCubeState centralLowerCubeState ≈
      (pi0 * pi0) *
        Q'.mkPos 1 256 (by decide) := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K 0 zeroEdgeLabelling
  exact Q'.eqv_trans _ _ _
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint_eqv_scaled
      w hw K 0 0 0
      centralLowerCubeState centralLowerCubeState)
    (Q'.mul_eqv_congr_left
      (pi0 * pi0) _ _
      normalizedMehlerGram_cube_cube_eqv_oneTwoFiftySixth)

/-- The genuine cube defect for the corrected rate is
`|pi0^2/256 - piCube^2|`; the obsolete expression
`pi0^2 * |1/256 - piCube^2|` does not occur. -/
theorem physicallyRecentered_cube_defect_le_rowMass
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    let pi0 :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
    let piCube :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 centralLowerCubeState
    Q'.abs
        ((pi0 * pi0) *
            Q'.mkPos 1 256 (by decide) +
          (-(piCube * piCube))) ≤
      physicalCenteredEndpointRowMass
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w (Q'.le_of_lt hw) K 0 0 0)
        centralLowerCubeState := by
  let pi0 :=
    centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
  let piCube :=
    centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0 centralLowerCubeState
  let endpoint :=
    vacuumCalibratedExactCenteredMehlerGramRawEndpoint
      w (Q'.le_of_lt hw) K 0 0 0
  let value := fun target =>
    Q'.abs
      (endpoint.joint centralLowerCubeState target +
        (-centralPhysicalVacuumJoint
          w (Q'.le_of_lt hw) K 0
          centralLowerCubeState target))
  have hmember :
      value centralLowerCubeState ≤
        listQSum value
          (centralPositiveHalfStates
            w (Q'.le_of_lt hw) K 0) :=
    listQSum_member_le_nonnegative
      value
      (fun target => Q'.abs_nonneg _)
      (centralPositiveHalfStates
        w (Q'.le_of_lt hw) K 0)
      (centralLowerCubeState_mem_centralPositiveHalfStates
        hw hK)
  have holdEntry :
      endpoint.joint
          centralLowerCubeState centralLowerCubeState ≈
        (pi0 * pi0) *
          Q'.mkPos 1 256 (by decide) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint_joint
          w (Q'.le_of_lt hw) K 0 0 0
          centralLowerCubeState centralLowerCubeState))
      (physicallyRecentered_cube_entry_eqv
        (Q'.le_of_lt hw) K)
  have hentry :
      value centralLowerCubeState ≈
        Q'.abs
          ((pi0 * pi0) *
              Q'.mkPos 1 256 (by decide) +
            (-(piCube * piCube))) := by
    unfold value centralPhysicalVacuumJoint piCube
    exact Q'.abs_eqv_congr
      (Q'.add_eqv_congr_right _ _ _ holdEntry)
  unfold physicalCenteredEndpointRowMass
    finiteJointDifferenceAbsRowMass endpoint
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hentry) hmember

/-- The exact corrected rate must pay the genuine cube defect. -/
theorem physicallyRecentered_cube_defect_le_rate_mul_marginal
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    let pi0 :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
    let piCube :=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 centralLowerCubeState
    Q'.abs
        ((pi0 * pi0) *
            Q'.mkPos 1 256 (by decide) +
          (-(piCube * piCube))) ≤
      (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
          w (Q'.le_of_lt hw) K 0 0 0).rate *
        piCube := by
  exact Q'.le_trans' _ _ _
    (physicallyRecentered_cube_defect_le_rowMass
      hw hK)
    (physicalCenteredEndpointRowMass_le_rate_mul_marginal
      (endpoint :=
        vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w (Q'.le_of_lt hw) K 0 0 0)
      (centralLowerCubeState_mem_centralPositiveHalfStates
        hw hK))

/-- Corrected cube no-go criterion for the new `1/8` rate. -/
theorem not_physicallyRecentered_rate_le_eighth_of_cube_defect
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K)
    (hdefect :
      let pi0 :=
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 zeroEdgeLabelling
      let piCube :=
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 centralLowerCubeState
      Q'.mkPos 1 8 (by decide) * piCube <
        Q'.abs
          ((pi0 * pi0) *
              Q'.mkPos 1 256 (by decide) +
            (-(piCube * piCube)))) :
    ¬
      (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
          w (Q'.le_of_lt hw) K 0 0 0).rate ≤
        Q'.mkPos 1 8 (by decide) := by
  intro hrate
  let piCube :=
    centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0 centralLowerCubeState
  have hpiCubeNonnegative :
      (0 : Q') ≤ piCube :=
    centralPhysicalRowMarginal_nonnegative
      (Q'.le_of_lt hw) K 0 centralLowerCubeState
  have hscaled :
      (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
            w (Q'.le_of_lt hw) K 0 0 0).rate *
          piCube ≤
        Q'.mkPos 1 8 (by decide) * piCube :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hrate hpiCubeNonnegative
  have hreverse :=
    Q'.le_trans' _ _ _
      (physicallyRecentered_cube_defect_le_rate_mul_marginal
        hw hK)
      hscaled
  exact Int.not_lt_of_ge hreverse hdefect

end YMGap.Continuum.BF4CalibratedCubeSpectralFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.centralLowerCube_emptyHalf_eqv_sixteenth
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.normalizedMehlerGram_cube_cube_eqv_oneTwoFiftySixth
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.normalizedMehlerGram_vacuum_cube_eqv_sixteenth
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.cube_diagonal_defect_le_centeredRowMass
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.cube_diagonal_defect_le_centeredRate_mul_marginal
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.calibrated_cube_diagonal_defect_le_rate_mul_marginal
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.not_calibrated_rate_le_eighth_of_cube_defect
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.physicallyRecentered_cube_entry_eqv
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.physicallyRecentered_cube_defect_le_rowMass
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.physicallyRecentered_cube_defect_le_rate_mul_marginal
#print axioms YMGap.Continuum.BF4CalibratedCubeSpectralFence.not_physicallyRecentered_rate_le_eighth_of_cube_defect
