import YMGap.Continuum.XiExceptionalGeneralLongArmGeometry
import YMGap.Continuum.XiExceptionalExternalReserveLimitFence

namespace YMGap.Continuum.XiExceptionalGeneralLongArmUnderdetermination

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGeometry
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence

def GammaSwap : List (Polymer TL) :=
  [V0, V1, V2, V3, V6, V5, V4, V7, V8, V9, V10, V11]

def pairSwap : MaskPair GammaSwap.length :=
  (bits12 false true false true false true false true false true false true,
    bits12 true false true false true false true false true false true false)

theorem pairSwap_mem :
    pairSwap ∈ exceptionalSourceCodes GammaSwap qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  exact ⟨maskPairs_complete pairSwap, rfl⟩

def entrySwap : ExceptionalSourceEntry GammaSwap qAll markV0 badV3 :=
  ⟨pairSwap, pairSwap_mem⟩

theorem GammaSwap_length : GammaSwap.length = ambientCount 1 := rfl

def labelOne : TL.Plaquette → Rep := fun _ => 1
def unitWeight : Q' := Q'.ofNat 1

theorem unitWeight_nonneg : (0 : Q') ≤ unitWeight := by decide

set_option maxRecDepth 1000000 in
theorem source_weight_at_unit :
    occurrencePairWeight unitWeight qAll markV0 badV3 GammaSwap
        labelOne pairSwap = Q'.ofNat 16777216 := by
  decide

set_option maxRecDepth 1000000 in
theorem canonical_block_weight_at_unit :
    qListSum
        (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3
          GammaSwap labelOne)
        (repairCarrierFamily GammaSwap 1 GammaSwap_length) =
      Q'.ofNat 4096 := by
  decide

theorem source_not_le_canonical_block_at_unit :
    ¬ occurrencePairWeight unitWeight qAll markV0 badV3 GammaSwap
          labelOne pairSwap ≤
        qListSum
          (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3
            GammaSwap labelOne)
          (repairCarrierFamily GammaSwap 1 GammaSwap_length) := by
  rw [source_weight_at_unit, canonical_block_weight_at_unit]
  decide

/-- Exceptional-source membership alone does not determine the canonical
long-arm normalization.  The same-side permutation `GammaSwap` remains an
actual exceptional source, but the fixed-index long words cease to be
incompatibility walks, so their block cannot pay the source. -/
theorem no_normalization_from_source_data :
    ¬ Nonempty
      (UniformLongArmNormalization qAll markV0 badV3 GammaSwap 1
        GammaSwap_length entrySwap) := by
  intro hexists
  obtain ⟨norm⟩ := hexists
  have hpay :=
    (uniformPaidResidualBlock norm).source_le unitWeight unitWeight_nonneg
      labelOne
  exact source_not_le_canonical_block_at_unit hpay

theorem no_canonical_ordered_ear_chart :
    ¬ Nonempty
      (CanonicalEarWordGeometry qAll markV0 badV3 GammaSwap 1
        GammaSwap_length entrySwap) := by
  intro hexists
  obtain ⟨geom⟩ := hexists
  exact no_normalization_from_source_data ⟨geom.normalization⟩

#print axioms pairSwap_mem
#print axioms source_weight_at_unit
#print axioms canonical_block_weight_at_unit
#print axioms source_not_le_canonical_block_at_unit
#print axioms no_normalization_from_source_data
#print axioms no_canonical_ordered_ear_chart

end YMGap.Continuum.XiExceptionalGeneralLongArmUnderdetermination
