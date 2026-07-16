/-
# Explicit coefficient kernel for the production left-associated resolver

The production `fuseChain` syntax first fuses the first two physical legs and
then repeatedly fuses the accumulated channel with the next physical leg.
`leftAssociatedLinkPacket` is the packet-level version of exactly that
recursion.  This file exposes every coefficient as a literal pair of finite
sums.  The output-zero specialization is therefore a precise, identifier-free
target for the subsequent graph/Fubini rewrite.

No degree bound is needed for the coefficient identity: both sides use the
same finite auxiliary window.  The geometric degree bound is needed only when
the packet is identified with the untruncated character power.
-/

import YMGap.Continuum.Z4LeftAssociatedLinkFusion

namespace YMGap.Continuum.Z4LeftAssociatedExplicitKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4LeftAssociatedLinkFusion

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Literal coefficient recursion matching `leftAssociatedLinkPacket`.
The first summation variable is the accumulated channel and the second is
the newly attached physical face label. -/
def leftAssociatedExplicitKernel {K : Nat} (P : CharacterPacket K) :
    Nat → Nat → Q'
  | 0, output => if output = 0 then 1 else 0
  | degree + 1, output =>
      fsum (fun previous =>
        fsum (fun external =>
          fusionInd previous external output *
            (leftAssociatedExplicitKernel P degree previous *
              coeffAt (facePacketAtLinkCutoff P) external))
          (linkAuxiliaryCutoff K + 1))
        (linkAuxiliaryCutoff K + 1)

/-- Every in-window explicit coefficient is the corresponding coefficient of
the production-oriented left-associated packet. -/
theorem leftAssociatedExplicitKernel_eq_coeffAt {K : Nat}
    (P : CharacterPacket K) : ∀ degree output,
    output < linkAuxiliaryCutoff K + 1 →
      leftAssociatedExplicitKernel P degree output ≈
        coeffAt (leftAssociatedLinkPacket P degree) output
  | 0, output, _ => by
      rw [leftAssociatedExplicitKernel, leftAssociatedLinkPacket]
      rw [YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket]
      exact Q'.eqv_refl _
  | degree + 1, output, houtput => by
      rw [leftAssociatedLinkPacket, coeffAt_of_lt _ houtput]
      change leftAssociatedExplicitKernel P (degree + 1) output ≈
        fusionCoeff (leftAssociatedLinkPacket P degree)
          (facePacketAtLinkCutoff P) output
      unfold leftAssociatedExplicitKernel fusionCoeff fusionProduct
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
      intro previous hprevious
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro external
      exact Q'.mul_eqv_congr_left _ _ _
        (qmul_congr
          (leftAssociatedExplicitKernel_eq_coeffAt P degree previous hprevious)
          (Q'.eqv_refl _))

/-- The output-zero Cartesian kernel is literally the vacuum coefficient of
the production-oriented packet recursion. -/
theorem leftAssociatedExplicitKernel_zero_eq_channelSum
    {K degree : Nat} (P : CharacterPacket K) :
    leftAssociatedExplicitKernel P degree 0 ≈
      leftAssociatedLinkChannelSum P degree := by
  refine Q'.eqv_trans _
    (coeffAt (leftAssociatedLinkPacket P degree) 0) _
    (leftAssociatedExplicitKernel_eq_coeffAt P degree 0
      (Nat.succ_pos _)) ?_
  unfold leftAssociatedLinkChannelSum vacuumHaar
  rw [coeffAt_of_lt _ (Nat.succ_pos _)]
  exact Q'.eqv_refl _

/-- Through the geometric link-degree bound, the same literal kernel is the
ordinary local Haar moment. -/
theorem leftAssociatedExplicitKernel_zero_eq_bareHaar
    {K degree : Nat} (P : CharacterPacket K)
    (hdegree : degree ≤ linkIncidenceBound) :
    leftAssociatedExplicitKernel P degree 0 ≈
      YMGap.Continuum.SU2ClassPolynomialChebUniqueness.bareVacuumHaar
        (YMGap.Continuum.Z4UnitCubeHaarSectorBridge.characterPow
          (synthesis P) degree) := by
  exact Q'.eqv_trans _ (leftAssociatedLinkChannelSum P degree) _
    (leftAssociatedExplicitKernel_zero_eq_channelSum P)
    (leftAssociatedLinkChannelSum_eq_bareHaar P hdegree)

end YMGap.Continuum.Z4LeftAssociatedExplicitKernel

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4LeftAssociatedExplicitKernel.leftAssociatedExplicitKernel_eq_coeffAt
#print axioms YMGap.Continuum.Z4LeftAssociatedExplicitKernel.leftAssociatedExplicitKernel_zero_eq_channelSum
#print axioms YMGap.Continuum.Z4LeftAssociatedExplicitKernel.leftAssociatedExplicitKernel_zero_eq_bareHaar
