/-
# Normalize cutoff-four excitation activity into the production kernel

The complete pointwise summand estimate is relative to a literal positive
parity-ground summand.  Since that ground summand belongs to the same complete
tilted row partition, division removes the source-dependent prefactor:

`physicalKernel(source,target) <= q(w)^K`.

The second theorem multiplies two such rows and combines their powers.  This
is the form needed by an observable-anchored two-replica connected carrier.
It is still pointwise; no global target sum or posterior-ground fraction is
claimed.

Constructive contract: exact rational division by a proved positive row mass
and the kernel-checked SU(2) activity bound only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceParityExcitationFullActivityBound

namespace YMGap.Continuum.Z4DyadicBinarySourceParityExcitationKernelBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationFullActivityBound
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound
open YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt

local infix:50 " ≈ " => Q'.eqv

private theorem spinFourParityExcitationFullActivityRate_nonnegative
    (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ spinFourParityExcitationFullActivityRate w := by
  unfold spinFourParityExcitationFullActivityRate
    spinFourParityExcitationFaceActivityRate
  exact Q'.mul_nonneg _ _ (zero_le_ofNat _) <|
    Q'.mul_nonneg _ _ (zero_le_ofNat 5) (qpow_nonneg w hw0 8)

private theorem listNatWeight_add_local {A : Type}
    (first second : A → Nat) : ∀ items : List A,
    listNatWeight (fun item => first item + second item) items =
      listNatWeight first items + listNatWeight second items
  | [] => rfl
  | _head :: rest => by
      simp only [listNatWeight]
      rw [listNatWeight_add_local first second rest]
      omega

/-! ## 1. One normalized production row -/

/-- A supported target's actual production-kernel probability is bounded by
one power of the complete excitation activity for each two-spin raise above
the source's parity ground. -/
theorem physicalKernel_positivePhysicalSource_le_excitationActivity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    (physicalKernel S hfineCutoff hcoarseCoupling).kernel
        source.1 targetState ≤
      qpow
        (spinFourParityExcitationFullActivityRate S.coarse.coupling)
        (positivePhysicalSourceParityExcitationActivity
          S source targetState) := by
  let rowMass := positivePhysicalSourceTiltedGibbsRowMass S source
  let ratePower := qpow
    (spinFourParityExcitationFullActivityRate S.coarse.coupling)
    (positivePhysicalSourceParityExcitationActivity S source targetState)
  have hparts := (mem_spinFourLoweringTargets_iff S _ _).mp htarget
  have hrowPos : (0 : Q') < rowMass :=
    positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling source
  have hsummand :=
    spinFourLoweringMultiplicityProduct_mul_physicalTerm_le_parityGroundMass_mul_activity
      S hfineCutoff (Q'.le_of_lt hcoarseCoupling) hcoarse1
        source targetState htarget
  have hground := positivePhysicalSourceParityGroundMass_le_rowMass
    S hfineCutoff hcoarseCoupling source
  have hrate0 : (0 : Q') ≤
      spinFourParityExcitationFullActivityRate S.coarse.coupling :=
    spinFourParityExcitationFullActivityRate_nonnegative
      S.coarse.coupling (Q'.le_of_lt hcoarseCoupling)
  have hratePower0 : (0 : Q') ≤ ratePower :=
    qpow_nonneg _ hrate0 _
  have hgroundScaled :
      positivePhysicalSourceParityGroundMass S source * ratePower ≤
        ratePower * rowMass := by
    refine Q'.le_trans' _
      (ratePower * positivePhysicalSourceParityGroundMass S source) _
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ ratePower
      hground hratePower0
  have hnumerator :
      Q'.ofNat
          (spinFourLoweringMultiplicityProduct S
            (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
        S.coarse.physicalTerm targetState ≤ ratePower * rowMass :=
    Q'.le_trans' _ _ _ hsummand hgroundScaled
  have hratio :
      Q'.divPos
          (Q'.ofNat
              (spinFourLoweringMultiplicityProduct S
                (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
            S.coarse.physicalTerm targetState)
          rowMass hrowPos ≤ ratePower :=
    Q'.divPos_le_of_le_mul _ _ hrowPos hnumerator
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (physicalKernel_positivePhysicalSource_eqv_tiltedGibbs
        S hfineCutoff hcoarseCoupling source targetState hparts.1))
    hratio

/-! ## 2. Two rows on one connected target pair -/

/-- Two supported production rows pay the sum of their target excitation
masses with the same explicit complete activity. -/
theorem physicalKernel_positivePhysicalSource_pair_le_excitationActivity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (first second : PositivePhysicalSource S)
    (firstTarget secondTarget : EdgeLabelling)
    (hfirstTarget : firstTarget ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S first.1))
    (hsecondTarget : secondTarget ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S second.1)) :
    (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          first.1 firstTarget *
        (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          second.1 secondTarget ≤
      qpow
        (spinFourParityExcitationFullActivityRate S.coarse.coupling)
        (positivePhysicalSourceParityExcitationActivity
            S first firstTarget +
          positivePhysicalSourceParityExcitationActivity
            S second secondTarget) := by
  let rate := spinFourParityExcitationFullActivityRate S.coarse.coupling
  let firstPower := qpow rate
    (positivePhysicalSourceParityExcitationActivity S first firstTarget)
  let secondPower := qpow rate
    (positivePhysicalSourceParityExcitationActivity S second secondTarget)
  have hfirst :=
    physicalKernel_positivePhysicalSource_le_excitationActivity
      S hfineCutoff hcoarseCoupling hcoarse1 first firstTarget hfirstTarget
  have hsecond :=
    physicalKernel_positivePhysicalSource_le_excitationActivity
      S hfineCutoff hcoarseCoupling hcoarse1 second secondTarget hsecondTarget
  have hfirstTargetMem :=
    ((mem_spinFourLoweringTargets_iff S _ _).mp hfirstTarget).1
  have hsecondTargetMem :=
    ((mem_spinFourLoweringTargets_iff S _ _).mp hsecondTarget).1
  have hfirstKernel0 : (0 : Q') ≤
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel
        first.1 firstTarget :=
    (physicalKernel S hfineCutoff hcoarseCoupling).nonnegative
      first.1 firstTarget first.2.1 hfirstTargetMem
  have hsecondKernel0 : (0 : Q') ≤
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel
        second.1 secondTarget :=
    (physicalKernel S hfineCutoff hcoarseCoupling).nonnegative
      second.1 secondTarget second.2.1 hsecondTargetMem
  have hrate0 : (0 : Q') ≤ rate :=
    spinFourParityExcitationFullActivityRate_nonnegative
      S.coarse.coupling (Q'.le_of_lt hcoarseCoupling)
  have hfirstPower0 : (0 : Q') ≤ firstPower := qpow_nonneg _ hrate0 _
  have hstepFirst :
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel
            first.1 firstTarget *
          (physicalKernel S hfineCutoff hcoarseCoupling).kernel
            second.1 secondTarget ≤
        firstPower *
          (physicalKernel S hfineCutoff hcoarseCoupling).kernel
            second.1 secondTarget :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hfirst hsecondKernel0
  have hstepSecond :
      firstPower *
          (physicalKernel S hfineCutoff hcoarseCoupling).kernel
            second.1 secondTarget ≤
        firstPower * secondPower :=
    Q'.mul_le_mul_of_nonneg_left _ _ firstPower hsecond hfirstPower0
  have hpower : firstPower * secondPower ≤
      qpow rate
        (positivePhysicalSourceParityExcitationActivity S first firstTarget +
          positivePhysicalSourceParityExcitationActivity
            S second secondTarget) := by
    exact Q'.ge_of_eqv
      (qpow_add rate
        (positivePhysicalSourceParityExcitationActivity S first firstTarget)
        (positivePhysicalSourceParityExcitationActivity
          S second secondTarget))
  exact Q'.le_trans' _ _ _ hstepFirst
    (Q'.le_trans' _ _ _ hstepSecond hpower)

/-! ## 3. The oriented interface consumed by the connected carrier -/

/-- The product of the two actual production rows assigned by an envelope
orientation.  The definition keeps the orientation choice at the interface;
the source and target coordinates themselves remain unchanged. -/
def finePacketOrientedPhysicalKernelPairWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  match orientation with
  | .forward =>
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          first.1 pair.1 *
        (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          second.1 pair.2
  | .reverse =>
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          second.1 pair.1 *
        (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          first.1 pair.2

private theorem finePacketOrientedTotalTargetExcitationActivity_eq
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketOrientedTotalTargetExcitationActivity
        S orientation first.1 second.1 pair =
      match orientation with
      | .forward =>
          positivePhysicalSourceParityExcitationActivity S first pair.1 +
            positivePhysicalSourceParityExcitationActivity S second pair.2
      | .reverse =>
          positivePhysicalSourceParityExcitationActivity S second pair.1 +
            positivePhysicalSourceParityExcitationActivity S first pair.2 := by
  unfold finePacketOrientedTotalTargetExcitationActivity
    finePacketOrientedTargetExcitationActivityAt
  rw [listNatWeight_add_local]
  cases orientation <;>
    rfl

/-- An oriented supported target pair pays exactly the connected carrier's
total two-replica target-excitation activity. -/
theorem finePacketOrientedPhysicalKernelPairWeight_le_excitationActivity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedPhysicalKernelPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≤
      qpow
        (spinFourParityExcitationFullActivityRate S.coarse.coupling)
        (finePacketOrientedTotalTargetExcitationActivity
          S orientation first.1 second.1 pair) := by
  cases orientation with
  | forward =>
      rw [finePacketOrientedTotalTargetExcitationActivity_eq]
      exact physicalKernel_positivePhysicalSource_pair_le_excitationActivity
        S hfineCutoff hcoarseCoupling hcoarse1 first second pair.1 pair.2
          hlowering.1 hlowering.2
  | reverse =>
      rw [finePacketOrientedTotalTargetExcitationActivity_eq]
      exact physicalKernel_positivePhysicalSource_pair_le_excitationActivity
        S hfineCutoff hcoarseCoupling hcoarse1 second first pair.1 pair.2
          hlowering.1 hlowering.2

#print axioms physicalKernel_positivePhysicalSource_le_excitationActivity
#print axioms physicalKernel_positivePhysicalSource_pair_le_excitationActivity
#print axioms finePacketOrientedPhysicalKernelPairWeight_le_excitationActivity

end YMGap.Continuum.Z4DyadicBinarySourceParityExcitationKernelBound
