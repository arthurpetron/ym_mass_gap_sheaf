/-
# Exact rational weights of the three-block pattern retune

The pattern-conditional counterterm has a simple pointwise form: every
target atom is multiplied by the ratio between the source and target masses
of its Boolean three-block cell.  This module proves that identity directly
from the finite pushforward and records exact cancellation and order facts
for the eight derived ratios.

No claim is made here that a physical fine law and a physical coarse law
already have equal cell masses.  Instead, the discrepancy is exposed as a
finite family of exact rational weights that subsequent estimates must
control.
-/

import YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw

namespace YMGap.Continuum.Z4ThreeBlockPatternRetuneRatio

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pushforward mass as a conditional times the source cell mass -/

theorem patternRetunedTargetMass_eqv_conditional_mul_sourcePatternMass
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    patternRetunedTargetMass sourceLaw targetLaw htargetPos target ≈
      targetThreeBlockFiberConditionalMass targetLaw htargetPos target *
        threeBlockPatternMass sourceLaw
          (threeBlockPattern targetLaw target) := by
  let pattern := threeBlockPattern targetLaw target
  let conditional := targetThreeBlockFiberConditionalMass
    targetLaw htargetPos target
  let filtered := fun source =>
    if threeBlockPattern sourceLaw source = pattern then
      sourceLaw.mass source else 0
  unfold patternRetunedTargetMass configurationPushforward
  refine Q'.eqv_trans _
    (listQSum (fun source => conditional * filtered source)
      sourceLaw.states) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    by_cases hpattern :
        threeBlockPattern targetLaw target =
          threeBlockPattern sourceLaw source
    · rw [threeBlockFiberConditionalKernel, if_pos hpattern]
      unfold filtered
      have hsourcePattern :
          threeBlockPattern sourceLaw source = pattern := by
        exact hpattern.symm
      rw [if_pos hsourcePattern]
      exact Q'.mul_comm_eqv (sourceLaw.mass source) conditional
    · rw [threeBlockFiberConditionalKernel, if_neg hpattern]
      unfold filtered
      have hsourcePattern :
          threeBlockPattern sourceLaw source ≠ pattern := by
        intro heq
        apply hpattern
        exact heq.symm
      rw [if_neg hsourcePattern]
      exact Q'.eqv_trans _ (0 : Q') _
        (Q'.mul_zero_eqv (sourceLaw.mass source))
        (Q'.eqv_symm (Q'.mul_zero_eqv conditional))
  refine Q'.eqv_trans _
    (conditional * listQSum filtered sourceLaw.states) _
    (listQSum_mul_left conditional filtered sourceLaw.states) ?_
  exact Q'.eqv_refl _

/-! ## 2. The exact per-pattern retune ratio -/

def patternRetuneRatio {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) : Q' :=
  Q'.divPos (threeBlockPatternMass sourceLaw pattern)
    (threeBlockPatternMass targetLaw pattern) (htargetPos pattern)

theorem patternRetuneRatio_nonnegative {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    (0 : Q') ≤ patternRetuneRatio
      sourceLaw targetLaw htargetPos pattern := by
  unfold patternRetuneRatio Q'.divPos
  exact Q'.mul_nonneg _ _
    (threeBlockPatternMass_nonnegative sourceLaw pattern)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem patternRetuneRatio_pos {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (hsourcePos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass sourceLaw pattern)
    (pattern : ThreeBlockPattern) :
    (0 : Q') < patternRetuneRatio
      sourceLaw targetLaw htargetPos pattern := by
  unfold patternRetuneRatio
  exact Q'.divPos_pos _ _ _ (hsourcePos pattern)

theorem patternRetuneRatio_mul_targetPatternMass {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    patternRetuneRatio sourceLaw targetLaw htargetPos pattern *
        threeBlockPatternMass targetLaw pattern ≈
      threeBlockPatternMass sourceLaw pattern := by
  unfold patternRetuneRatio
  exact Q'.divPos_mul_eqv _ _ _

/-! ## 3. Pointwise reweighting and the exact equality criterion -/

theorem patternRetunedTargetMass_eqv_targetMass_mul_ratio
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    patternRetunedTargetMass sourceLaw targetLaw htargetPos target ≈
      targetLaw.mass target *
        patternRetuneRatio sourceLaw targetLaw htargetPos
          (threeBlockPattern targetLaw target) := by
  refine Q'.eqv_trans _ _ _
    (patternRetunedTargetMass_eqv_conditional_mul_sourcePatternMass
      sourceLaw targetLaw htargetPos target) ?_
  unfold targetThreeBlockFiberConditionalMass patternRetuneRatio Q'.divPos
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)

/-- The same retuned mass written directly as an exact patternwise
Radon--Nikodym reweighting of the original target law. -/
def patternRatioWeightedTargetMass {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) : Q' :=
  targetLaw.mass target *
    patternRetuneRatio sourceLaw targetLaw htargetPos
      (threeBlockPattern targetLaw target)

theorem patternRatioWeightedTargetMass_eqv_retuned
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    patternRatioWeightedTargetMass
        sourceLaw targetLaw htargetPos target ≈
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target := by
  exact Q'.eqv_symm
    (patternRetunedTargetMass_eqv_targetMass_mul_ratio
      sourceLaw targetLaw htargetPos target)

theorem patternRatioWeightedTargetMass_nonnegative
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    (0 : Q') ≤ patternRatioWeightedTargetMass
      sourceLaw targetLaw htargetPos target := by
  unfold patternRatioWeightedTargetMass
  exact Q'.mul_nonneg _ _ (targetLaw.mass_nonnegative target)
    (patternRetuneRatio_nonnegative
      sourceLaw targetLaw htargetPos _)

theorem patternRatioWeightedTargetMass_normalized
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    listQSum
        (patternRatioWeightedTargetMass
          sourceLaw targetLaw htargetPos) targetLaw.states ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
      targetLaw.states) _ ?_
    (patternRetunedTargetMass_normalized
      sourceLaw targetLaw htargetPos)
  apply listQSum_congr_on
  intro target _
  exact patternRatioWeightedTargetMass_eqv_retuned
    sourceLaw targetLaw htargetPos target

theorem patternRatioWeightedTargetMass_patternMass
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    listQSum
        (fun target =>
          if threeBlockPattern targetLaw target = pattern then
            patternRatioWeightedTargetMass
              sourceLaw targetLaw htargetPos target
          else 0)
        targetLaw.states ≈
      threeBlockPatternMass sourceLaw pattern := by
  refine Q'.eqv_trans _
    (threeBlockPatternMass
      (patternRetunedTargetLaw sourceLaw targetLaw htargetPos) pattern) _
    ?_ (Q'.eqv_symm
      (patternRetunedTargetLaw_patternMass_eqv
        sourceLaw targetLaw htargetPos pattern))
  unfold threeBlockPatternMass
  apply listQSum_congr_on
  intro target _
  by_cases hpattern : threeBlockPattern targetLaw target = pattern
  · rw [if_pos hpattern]
    have hretuned :
        threeBlockPattern
            (patternRetunedTargetLaw sourceLaw targetLaw htargetPos) target =
          pattern := by
      exact hpattern
    rw [if_pos hretuned]
    change patternRatioWeightedTargetMass
        sourceLaw targetLaw htargetPos target ≈
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target
    exact patternRatioWeightedTargetMass_eqv_retuned
      sourceLaw targetLaw htargetPos target
  · rw [if_neg hpattern]
    have hretuned :
        threeBlockPattern
            (patternRetunedTargetLaw sourceLaw targetLaw htargetPos) target ≠
          pattern := by
      exact hpattern
    rw [if_neg hretuned]
    exact Q'.eqv_refl 0

theorem patternRetuneRatio_eqv_one_of_patternMass_eqv
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern)
    (hmatch : threeBlockPatternMass sourceLaw pattern ≈
      threeBlockPatternMass targetLaw pattern) :
    patternRetuneRatio sourceLaw targetLaw htargetPos pattern ≈ 1 := by
  unfold patternRetuneRatio Q'.divPos
  refine Q'.eqv_trans _
    (threeBlockPatternMass targetLaw pattern *
      Q'.recipPos (threeBlockPatternMass targetLaw pattern)
        (htargetPos pattern)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hmatch
  exact Q'.mul_recipPos_eqv _ _

theorem patternMass_eqv_of_patternRetuneRatio_eqv_one
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern)
    (hratio : patternRetuneRatio
      sourceLaw targetLaw htargetPos pattern ≈ 1) :
    threeBlockPatternMass sourceLaw pattern ≈
      threeBlockPatternMass targetLaw pattern := by
  refine Q'.eqv_trans _
    (patternRetuneRatio sourceLaw targetLaw htargetPos pattern *
      threeBlockPatternMass targetLaw pattern) _ ?_ ?_
  · exact Q'.eqv_symm
      (patternRetuneRatio_mul_targetPatternMass
        sourceLaw targetLaw htargetPos pattern)
  refine Q'.eqv_trans _
    (1 * threeBlockPatternMass targetLaw pattern) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hratio
  exact Q'.one_mul_eqv _

theorem patternRetuneRatio_eqv_one_iff_patternMass_eqv
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    patternRetuneRatio sourceLaw targetLaw htargetPos pattern ≈ 1 ↔
      threeBlockPatternMass sourceLaw pattern ≈
        threeBlockPatternMass targetLaw pattern := by
  constructor
  · exact patternMass_eqv_of_patternRetuneRatio_eqv_one
      sourceLaw targetLaw htargetPos pattern
  · exact patternRetuneRatio_eqv_one_of_patternMass_eqv
      sourceLaw targetLaw htargetPos pattern

theorem patternRetunedTargetMass_eqv_targetMass_of_patternMass_eqv
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target)
    (hmatch : threeBlockPatternMass sourceLaw
        (threeBlockPattern targetLaw target) ≈
      threeBlockPatternMass targetLaw
        (threeBlockPattern targetLaw target)) :
    patternRetunedTargetMass sourceLaw targetLaw htargetPos target ≈
      targetLaw.mass target := by
  refine Q'.eqv_trans _ _ _
    (patternRetunedTargetMass_eqv_targetMass_mul_ratio
      sourceLaw targetLaw htargetPos target) ?_
  refine Q'.eqv_trans _ (targetLaw.mass target * 1) _
    (Q'.mul_eqv_congr_left _ _ _
      (patternRetuneRatio_eqv_one_of_patternMass_eqv
        sourceLaw targetLaw htargetPos _ hmatch)) ?_
  exact Q'.mul_one_eqv _

/-! ## 4. Ratio order is exactly cell-mass order -/

theorem patternRetuneRatio_le_one_of_source_le_target
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern)
    (hle : threeBlockPatternMass sourceLaw pattern ≤
      threeBlockPatternMass targetLaw pattern) :
    patternRetuneRatio sourceLaw targetLaw htargetPos pattern ≤ 1 := by
  unfold patternRetuneRatio
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hle
    (Q'.le_of_eqv (Q'.eqv_symm
      (Q'.one_mul_eqv (threeBlockPatternMass targetLaw pattern))))

theorem one_le_patternRetuneRatio_of_target_le_source
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern)
    (hle : threeBlockPatternMass targetLaw pattern ≤
      threeBlockPatternMass sourceLaw pattern) :
    (1 : Q') ≤ patternRetuneRatio
      sourceLaw targetLaw htargetPos pattern := by
  unfold patternRetuneRatio
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.one_mul_eqv (threeBlockPatternMass targetLaw pattern))) hle

/-! ## 5. Exact weights against the derived outward coarse law -/

def outwardCoarsePatternRetuneRatio {Source : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (pattern : ThreeBlockPattern) : Q' :=
  patternRetuneRatio sourceLaw
    (outwardCoarseSubsupportLaw coupling hcoupling)
    (outwardCoarseSubsupportLaw_patternMass_pos coupling hcoupling)
    pattern

theorem outwardCoarsePatternRetuneRatio_nonnegative {Source : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (pattern : ThreeBlockPattern) :
    (0 : Q') ≤ outwardCoarsePatternRetuneRatio
      sourceLaw coupling hcoupling pattern := by
  exact patternRetuneRatio_nonnegative sourceLaw
    (outwardCoarseSubsupportLaw coupling hcoupling)
    (outwardCoarseSubsupportLaw_patternMass_pos coupling hcoupling)
    pattern

theorem outwardCoarsePatternRetuneRatio_pos {Source : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (hsourcePos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass sourceLaw pattern)
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (pattern : ThreeBlockPattern) :
    (0 : Q') < outwardCoarsePatternRetuneRatio
      sourceLaw coupling hcoupling pattern := by
  exact patternRetuneRatio_pos sourceLaw
    (outwardCoarseSubsupportLaw coupling hcoupling)
    (outwardCoarseSubsupportLaw_patternMass_pos coupling hcoupling)
    hsourcePos pattern

theorem outwardCoarsePatternRetuneRatio_mul_coarsePatternMass
    {Source : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (pattern : ThreeBlockPattern) :
    outwardCoarsePatternRetuneRatio
        sourceLaw coupling hcoupling pattern *
        threeBlockPatternMass
          (outwardCoarseSubsupportLaw coupling hcoupling) pattern ≈
      threeBlockPatternMass sourceLaw pattern := by
  exact patternRetuneRatio_mul_targetPatternMass sourceLaw
    (outwardCoarseSubsupportLaw coupling hcoupling)
    (outwardCoarseSubsupportLaw_patternMass_pos coupling hcoupling)
    pattern

theorem retunedToOutwardCoarseLaw_mass_eqv_coarseMass_mul_ratio
    {Source : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (target : EdgeLabelling) :
    (retunedToOutwardCoarseLaw sourceLaw coupling hcoupling).mass target ≈
      (outwardCoarseSubsupportLaw coupling hcoupling).mass target *
        outwardCoarsePatternRetuneRatio sourceLaw coupling hcoupling
          (threeBlockPattern
            (outwardCoarseSubsupportLaw coupling hcoupling) target) := by
  exact patternRetunedTargetMass_eqv_targetMass_mul_ratio sourceLaw
    (outwardCoarseSubsupportLaw coupling hcoupling)
    (outwardCoarseSubsupportLaw_patternMass_pos coupling hcoupling)
    target

theorem outwardCoarsePatternRetuneRatio_eqv_one_iff_patternMass_eqv
    {Source : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (pattern : ThreeBlockPattern) :
    outwardCoarsePatternRetuneRatio
        sourceLaw coupling hcoupling pattern ≈ 1 ↔
      threeBlockPatternMass sourceLaw pattern ≈
        threeBlockPatternMass
          (outwardCoarseSubsupportLaw coupling hcoupling) pattern := by
  exact patternRetuneRatio_eqv_one_iff_patternMass_eqv sourceLaw
    (outwardCoarseSubsupportLaw coupling hcoupling)
    (outwardCoarseSubsupportLaw_patternMass_pos coupling hcoupling)
    pattern

#print axioms patternRetunedTargetMass_eqv_conditional_mul_sourcePatternMass
#print axioms patternRetuneRatio_nonnegative
#print axioms patternRetuneRatio_pos
#print axioms patternRetuneRatio_mul_targetPatternMass
#print axioms patternRetunedTargetMass_eqv_targetMass_mul_ratio
#print axioms patternRatioWeightedTargetMass_eqv_retuned
#print axioms patternRatioWeightedTargetMass_normalized
#print axioms patternRatioWeightedTargetMass_patternMass
#print axioms patternRetuneRatio_eqv_one_iff_patternMass_eqv
#print axioms patternRetunedTargetMass_eqv_targetMass_of_patternMass_eqv
#print axioms patternRetuneRatio_le_one_of_source_le_target
#print axioms one_le_patternRetuneRatio_of_target_le_source
#print axioms outwardCoarsePatternRetuneRatio_pos
#print axioms outwardCoarsePatternRetuneRatio_mul_coarsePatternMass
#print axioms retunedToOutwardCoarseLaw_mass_eqv_coarseMass_mul_ratio
#print axioms outwardCoarsePatternRetuneRatio_eqv_one_iff_patternMass_eqv

end YMGap.Continuum.Z4ThreeBlockPatternRetuneRatio
