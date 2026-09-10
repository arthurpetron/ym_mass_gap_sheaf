/-
# Rebalance connected-component heat into decay and entropy

The first component budget assigned all three heat units per unit of
observable separation to the visible decay factor.  That leaves no payment
for the two minimal local replica states along a geodesic component.  The
right exact split is more economical.

If `D` is the distance floor, `S` the target-support component size, and `A`
the component activity, then `D <= S <= A` and

  `3 A = D + 2 S + (S - D) + 3 (A - S)`.

Thus one heat unit per distance step remains visible, two units per component
face pay the combined shape/local-state entropy, one further unit pays every
geometric detour face, and all local activity above its minimum retains the
previous three-unit payment.

At the explicit strong-coupling anchor `1/400`, the proved degree-24 rooted
animal carrier has base `625` and the complete local catalogue has base `72`.
Their combined one-face entropy times the two-unit payment is exactly

  `625 * 72 * (1/400)^2 = 9/32 < 1`.

This is a load-bearing SU(2) estimate: the three-unit component heat charge
comes from the cutoff-one source occupation and the SU(2) target Casimir
excess established upstream.  It is not a beta-uniform or continuum claim.

Constructive contract: exact natural arithmetic, rational powers, and closed
rational certificates only; no classical choice, proof hole, trusted
external computation, noncomputable declaration, enlarged heartbeat budget,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode
import YMGap.Continuum.Z4StrongCouplingParametricAnchor

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ExplicitSpinFoamBounds

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact `D + 2S + (S-D) + 3(A-S)` split -/

/-- One heat unit per unit of distance is retained as the visible decay. -/
def finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  finePacketGlobalNonzeroConnectedEntryDistance
    S orientation observableFaceId hobservableFace entry

/-- Two heat units per component face are reserved for shape and local-code
entropy. -/
def finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  2 * finePacketGlobalNonzeroConnectedEntryComponentSize
    S orientation observableFaceId entry

/-- After the visible distance and the two-unit site payment, each component
face beyond the distance floor retains one further heat unit. -/
def finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  finePacketGlobalNonzeroConnectedEntryComponentSize
      S orientation observableFaceId entry -
    finePacketGlobalNonzeroConnectedEntryDistance
      S orientation observableFaceId hobservableFace entry

/-- The full three-unit component charge is exactly visible decay, the
two-unit per-site entropy fund, residual detour heat, and local excess heat. -/
theorem finePacketGlobalNonzeroConnectedEntry_componentHeat_eq_rebalanced
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
        S orientation observableFaceId entry =
      finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
          S orientation observableFaceId hobservableFace entry +
        (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
            S orientation observableFaceId entry +
          (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
              S orientation observableFaceId hobservableFace entry +
            finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
              S orientation observableFaceId entry)) := by
  have hdistance :=
    finePacketGlobalNonzeroConnectedEntry_distance_le_componentSize
      S orientation observableFaceId hobservableFace entry
  have hactivity :=
    finePacketGlobalNonzeroConnectedEntry_componentSize_le_activity
      S hfineCutoff orientation observableFaceId hobservableFace entry
  unfold finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
    finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
    finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
    finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
    finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
  omega

/-- Rational-power form of the exact rebalanced component budget. -/
theorem finePacketGlobalNonzeroConnectedEntry_componentHeatPower_eqv_rebalanced
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
          S orientation observableFaceId entry) ≈
      qpow rate
          (finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
            S orientation observableFaceId hobservableFace entry) *
        (qpow rate
            (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
              S orientation observableFaceId entry) *
          (qpow rate
              (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
                S orientation observableFaceId hobservableFace entry) *
            qpow rate
              (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
                S orientation observableFaceId entry))) := by
  rw [finePacketGlobalNonzeroConnectedEntry_componentHeat_eq_rebalanced
    S hfineCutoff orientation observableFaceId hobservableFace entry]
  refine Q'.eqv_trans _
    (qpow rate
        (finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
          S orientation observableFaceId hobservableFace entry) *
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
            S orientation observableFaceId entry +
          (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
              S orientation observableFaceId hobservableFace entry +
            finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
              S orientation observableFaceId entry))) _
    (HeatKernelRGStep.qpow_add rate _ _) ?_
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _
    (qpow rate
        (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
          S orientation observableFaceId entry) *
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
            S orientation observableFaceId hobservableFace entry +
          finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
            S orientation observableFaceId entry)) _
    (HeatKernelRGStep.qpow_add rate _ _) ?_
  apply Q'.mul_eqv_congr_left
  exact HeatKernelRGStep.qpow_add rate _ _

/-! ## 2. The explicit shape/local-state entropy ratio -/

/-- Exact rooted Z4 plaquette-animal base times the complete local-code base. -/
def finePacketComponentShapeLocalEntropyBase : Nat := 625 * 72

theorem finePacketComponentShapeLocalEntropyBase_eq :
    finePacketComponentShapeLocalEntropyBase = 45000 := by
  decide

/-- One site's combined entropy multiplied by its two reserved heat units. -/
def finePacketComponentShapeLocalEntropyRatio (rate : Q') : Q' :=
  Q'.ofNat finePacketComponentShapeLocalEntropyBase * qpow rate 2

/-- At the explicit strong-coupling anchor the exact ratio is `9/32`. -/
theorem finePacketComponentShapeLocalEntropyRatio_anchor_eqv :
    finePacketComponentShapeLocalEntropyRatio anchorCoupling ≈
      Q'.mkPos 9 32 (by decide) := by
  unfold finePacketComponentShapeLocalEntropyRatio
    finePacketComponentShapeLocalEntropyBase anchorCoupling qpow
  decide

theorem finePacketComponentShapeLocalEntropyRatio_anchor_lt_one :
    finePacketComponentShapeLocalEntropyRatio anchorCoupling < (1 : Q') := by
  have hle : finePacketComponentShapeLocalEntropyRatio anchorCoupling ≤
      Q'.mkPos 9 32 (by decide) :=
    Q'.le_of_eqv finePacketComponentShapeLocalEntropyRatio_anchor_eqv
  have hlt : Q'.mkPos 9 32 (by decide) < (1 : Q') := by
    decide
  exact HeatKernelGap.lt_of_le_of_lt hle hlt

/-- The same strict entropy payment holds throughout the explicitly named
strong-coupling interval `0 <= rate <= 1/400`. -/
theorem finePacketComponentShapeLocalEntropyRatio_lt_one
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling) :
    finePacketComponentShapeLocalEntropyRatio rate < (1 : Q') := by
  have hpow : qpow rate 2 ≤ qpow anchorCoupling 2 :=
    HeatKernelGap.qpow_mono hrate0 hrateAnchor 2
  have hbase0 : (0 : Q') ≤
      Q'.ofNat finePacketComponentShapeLocalEntropyBase :=
    ClusterCount.ofNat_nonneg _
  have hratio : finePacketComponentShapeLocalEntropyRatio rate ≤
      finePacketComponentShapeLocalEntropyRatio anchorCoupling := by
    unfold finePacketComponentShapeLocalEntropyRatio
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpow hbase0
  exact HeatKernelGap.lt_of_le_of_lt hratio
    finePacketComponentShapeLocalEntropyRatio_anchor_lt_one

/-! ## 3. Axiom audit -/

#print axioms finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
#print axioms finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
#print axioms finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
#print axioms finePacketGlobalNonzeroConnectedEntry_componentHeat_eq_rebalanced
#print axioms finePacketGlobalNonzeroConnectedEntry_componentHeatPower_eqv_rebalanced
#print axioms finePacketComponentShapeLocalEntropyBase
#print axioms finePacketComponentShapeLocalEntropyBase_eq
#print axioms finePacketComponentShapeLocalEntropyRatio
#print axioms finePacketComponentShapeLocalEntropyRatio_anchor_eqv
#print axioms finePacketComponentShapeLocalEntropyRatio_anchor_lt_one
#print axioms finePacketComponentShapeLocalEntropyRatio_lt_one

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
