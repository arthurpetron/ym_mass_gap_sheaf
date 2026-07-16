/-
# An explicit recursive finite-sum kernel for sequential link fusion

The actual trivalent resolver is a chain, whereas `sequentialLinkPacket` is
defined by repeated truncated packet fusion.  This module exposes the packet
recursion as one literal finite-sum kernel.

At degree zero the kernel is the vacuum delta.  At each successor it sums an
external face label and the previous intermediate label through the enlarged
`6*K` window, weighted by the exact fusion indicator.  Induction proves that
every output coefficient is exactly the corresponding coefficient of
`sequentialLinkPacket`.  In particular the output-zero kernel is the
canonical local channel sum and, through degree six, the bare Haar moment.

Honest scope: this supplies the uniform coefficient target for all local
valences.  The remaining graph-interface theorem must rewrite each actual
`fuseLabels` Cartesian block into this recursive kernel and transport the
canonical identifiers to the box identifiers.
-/

import YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar

namespace YMGap.Continuum.Z4SequentialLinkExplicitKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Literal nested-sum recursion for the left-to-right fusion chain. -/
def explicitSequentialKernel {K : Nat} (P : CharacterPacket K) :
    Nat → Nat → Q'
  | 0, output => if output = 0 then 1 else 0
  | degree + 1, output =>
      fsum (fun external =>
        fsum (fun previous =>
          fusionInd external previous output *
            (coeffAt (facePacketAtLinkCutoff P) external *
              explicitSequentialKernel P degree previous))
          (linkAuxiliaryCutoff K + 1))
        (linkAuxiliaryCutoff K + 1)

/-- Every in-window coefficient of the explicit kernel is the corresponding
coefficient of the production sequential packet. -/
theorem explicitSequentialKernel_eq_coeffAt {K : Nat}
    (P : CharacterPacket K) : ∀ degree output,
    output < linkAuxiliaryCutoff K + 1 →
      explicitSequentialKernel P degree output ≈
        coeffAt (sequentialLinkPacket P degree) output
  | 0, output, _ => by
      rw [explicitSequentialKernel, sequentialLinkPacket]
      rw [YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket]
      exact Q'.eqv_refl _
  | degree + 1, output, houtput => by
      rw [sequentialLinkPacket, coeffAt_of_lt _ houtput]
      change explicitSequentialKernel P (degree + 1) output ≈
        fusionCoeff (facePacketAtLinkCutoff P)
          (sequentialLinkPacket P degree) output
      unfold explicitSequentialKernel fusionCoeff fusionProduct
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro external
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
      intro previous hprevious
      exact Q'.mul_eqv_congr_left _ _ _
        (qmul_congr (Q'.eqv_refl _)
          (explicitSequentialKernel_eq_coeffAt P degree previous hprevious))

/-- The output-zero kernel is exactly the canonical sequential local channel
sum, with no valence case split. -/
theorem explicitSequentialKernel_zero_eq_canonical {K degree : Nat}
    (P : CharacterPacket K) :
    explicitSequentialKernel P degree 0 ≈
      canonicalSequentialLinkChannelSum P degree := by
  refine Q'.eqv_trans _
    (coeffAt (sequentialLinkPacket P degree) 0) _
    (explicitSequentialKernel_eq_coeffAt P degree 0 (Nat.succ_pos _)) ?_
  unfold canonicalSequentialLinkChannelSum vacuumHaar
  rw [coeffAt_of_lt _ (Nat.succ_pos _)]
  exact Q'.eqv_refl _

/-- Through the geometric incidence bound, the same explicit recursive
kernel is the ordinary bare Haar moment. -/
theorem explicitSequentialKernel_zero_eq_bareHaar
    {K degree : Nat} (P : CharacterPacket K)
    (hdegree : degree ≤ linkIncidenceBound) :
    explicitSequentialKernel P degree 0 ≈
      YMGap.Continuum.SU2ClassPolynomialChebUniqueness.bareVacuumHaar
        (characterPow (synthesis P) degree) := by
  exact Q'.eqv_trans _ (canonicalSequentialLinkChannelSum P degree) _
    (explicitSequentialKernel_zero_eq_canonical P)
    (canonicalSequentialLinkChannelSum_eq_bareHaar P hdegree)

end YMGap.Continuum.Z4SequentialLinkExplicitKernel

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SequentialLinkExplicitKernel.explicitSequentialKernel_eq_coeffAt
#print axioms YMGap.Continuum.Z4SequentialLinkExplicitKernel.explicitSequentialKernel_zero_eq_canonical
#print axioms YMGap.Continuum.Z4SequentialLinkExplicitKernel.explicitSequentialKernel_zero_eq_bareHaar
