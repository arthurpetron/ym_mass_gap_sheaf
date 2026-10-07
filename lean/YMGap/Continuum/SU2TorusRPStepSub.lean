/-
# Torus RP (d4b): the selected-shear chain is a supported ring substitution

The concrete crossing split uses the existing Haar-invariant selected-shear chain
`applySelectedTranslationSteps` (Haar invariance: `applySelectedTranslationSteps_haar`, all degrees). Here:
* `prefix_pe`: prefix-equivalent supported polynomials are PE.
* `steps_ringSub`: the chain is a `RingSub` on `tailBlocks + 1` blocks (coefficient-level mul/add/smul/neg; `one`
  by the prefix lemma `applySteps_one_prefix`).
With `word_sub`/`TK_word_sub`, this lets the split act on concrete plaquette words.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPExtend
import YMGap.Continuum.SU2QuaternionTranslationWordComposition
import YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain

namespace YMGap.Continuum.SU2TorusRPStepSub

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE phi pe_refl)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2TorusRPSubst (RingSub)

theorem exp_sup {n : Nat} {e : List Nat} (h : e.length ≤ 4 * n) (i : Nat) (hi : 4 * n ≤ i) :
    exponentAt e i = 0 :=
  YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le _ _ (Nat.le_trans h hi)

theorem prefix_pe (n : Nat) : ∀ {X Y : RatPoly}, QuaternionPrefixPolynomialEqv n X Y →
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks n X →
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks n Y → PE n X Y
  | _, _, .nil, _, _ => pe_refl _ _
  | _, _, .cons (leftTerm := s) (rightTerm := t) hst hr, hX, hY => fun m => by
      have hs : s.1.length ≤ 4 * n := hX s (List.mem_cons_self ..)
      have ht : t.1.length ≤ 4 * n := hY t (List.mem_cons_self ..)
      have hrest := prefix_pe n hr (fun u hu => hX u (List.mem_cons_of_mem _ hu))
        (fun u hu => hY u (List.mem_cons_of_mem _ hu)) m
      change (s.2 * quaternionHaarMono n (monoMul m s.1) + phi n _ m).eqv
        (t.2 * quaternionHaarMono n (monoMul m t.1) + phi n _ m)
      have hmono : quaternionHaarMono n (monoMul m s.1) = quaternionHaarMono n (monoMul m t.1) :=
        YMGap.Continuum.SU2TorusRPCore.mono_congr n fun i => by
          rw [YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul,
            YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul]
          by_cases hi : i < 4 * n
          · rw [hst.exponent i hi]
          · rw [exp_sup hs i (by omega), exp_sup ht i (by omega)]
      rw [hmono]
      exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hst.coefficient) hrest

theorem steps_supported {tailBlocks : Nat} (hb : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks)) (p : RatPoly),
      YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks (tailBlocks + 1) p →
      YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks (tailBlocks + 1)
        (applySelectedTranslationSteps hb steps p)
  | [], _, h => h
  | step :: rest, p, _ => steps_supported hb rest _ (applySelectedTranslationStep_supported hb step p)

theorem one_supported (n : Nat) :
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks n polyOne := by
  intro t ht
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht; exact Nat.zero_le _

theorem steps_ringSub {tailBlocks : Nat} (hb : 0 < tailBlocks) (steps : List (SelectedTranslationStep tailBlocks)) :
    RingSub (tailBlocks + 1) (applySelectedTranslationSteps hb steps) where
  mul p q := YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff _ (applySelectedTranslationSteps_mul hb steps p q)
  add p q := by rw [applySelectedTranslationSteps_add]; exact pe_refl _ _
  smul c p := YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff _ (applySelectedTranslationSteps_smul hb steps c p)
  neg p := YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff _ (applySelectedTranslationSteps_neg hb steps p)
  one := prefix_pe _ (YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_one_prefix hb steps).scalar
    (steps_supported hb steps _ (one_supported _)) (one_supported _)

end YMGap.Continuum.SU2TorusRPStepSub

#print axioms YMGap.Continuum.SU2TorusRPStepSub.prefix_pe
#print axioms YMGap.Continuum.SU2TorusRPStepSub.steps_ringSub
