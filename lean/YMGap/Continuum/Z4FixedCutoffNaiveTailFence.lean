/-
# Fixed-cutoff additive character-tail fence on cofinal Z4 boxes

The elementary cube mode is exactly cutoff-stable because it samples only
spins zero and two.  A different argument is needed for the complete
finite-volume functional: summing one positive omitted heat-kernel coefficient
independently over all plaquettes cannot be volume-uniform.  This file records
that obstruction constructively, so subsequent tail work must use locality,
connected-cluster cancellation, or a cutoff growing with the volume/scale.
-/

import YMGap.Continuum.BalabanLargeFieldEntropy
import YMGap.Continuum.DirectSingleStepReconGap
import YMGap.Continuum.Z4UnitCubeCofinalModeLimit

namespace YMGap.Continuum.Z4FixedCutoffNaiveTailFence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BalabanLargeFieldEntropy
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.SU2PeterWeylWilsonBlock

/-- The first heat-kernel coefficient omitted above cutoff `K`. -/
def firstOmittedCoefficient (K : Nat) : Q' :=
  coeffW coupling (K + 1)

theorem firstOmittedCoefficient_pos (K : Nat) :
    (0 : Q') < firstOmittedCoefficient K := by
  exact DirectSingleStepReconGap.coeffW_pos (w := coupling)
    (by decide) K

/-- The naïve additive tail charge obtained by paying one first-omitted
coefficient independently for every plaquette. -/
def naiveFixedCutoffVolumeTail (K n : Nat) : Q' :=
  Q'.ofNat (plaquetteEdgeCount n) * firstOmittedCoefficient K

/-- At every fixed cutoff, the naïve additive volume tail exceeds every
rational ceiling on a sufficiently large cofinal box. -/
theorem naiveFixedCutoffVolumeTail_unbounded (K : Nat) (B : Q') :
    ∃ n : Nat, B < naiveFixedCutoffVolumeTail K n := by
  let c := firstOmittedCoefficient K
  have hc : (0 : Q') < c := firstOmittedCoefficient_pos K
  obtain ⟨N, hN⟩ := scaledGt c B hc
  obtain ⟨n, hn⟩ := boxPlaquetteCount_unbounded N
  have hcount : N ≤ plaquetteEdgeCount n := by
    unfold plaquetteEdgeCount
    exact hn
  have hnat : Q'.ofNat N ≤ Q'.ofNat (plaquetteEdgeCount n) :=
    Q'.ofNat_le_ofNat hcount
  have hmul : c * Q'.ofNat N ≤ c * Q'.ofNat (plaquetteEdgeCount n) :=
    Q'.mul_le_mul_of_nonneg_left _ _ c hnat (Q'.le_of_lt hc)
  refine ⟨n, ?_⟩
  unfold naiveFixedCutoffVolumeTail
  change B < Q'.ofNat (plaquetteEdgeCount n) * c
  have hb : B < c * Q'.ofNat (plaquetteEdgeCount n) :=
    ClusteringImpliesGap.lt_of_lt_of_le hN hmul
  exact ClusteringImpliesGap.lt_of_lt_of_le hb
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv c (Q'.ofNat (plaquetteEdgeCount n))))

/-- Hence no finite rational bound controls that additive tail uniformly in
volume.  This refutes the fixed-cutoff, independent-plaquette summation route;
it does not refute connected or normalized local tails. -/
theorem no_uniform_naiveFixedCutoffVolumeTail (K : Nat) :
    ¬ ∃ B : Q', ∀ n : Nat, naiveFixedCutoffVolumeTail K n ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := naiveFixedCutoffVolumeTail_unbounded K B
  exact Int.not_lt_of_ge (hB n) hn

#print axioms firstOmittedCoefficient_pos
#print axioms naiveFixedCutoffVolumeTail_unbounded
#print axioms no_uniform_naiveFixedCutoffVolumeTail

end YMGap.Continuum.Z4FixedCutoffNaiveTailFence
