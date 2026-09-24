/-
# Shared-spectator pairing for one explicit head Gram channel
-/

import YMGap.Continuum.SU2QuaternionProductHeatGramChannels
import YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction

namespace YMGap.Continuum.SU2QuaternionSharedHeadGramPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem lifted_head_independent (p : RatPoly) :
    HeadQuaternionIndependent (liftHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  rfl

private theorem copy_head_prefix (tail : Nat) : ∀ (h : RatPoly),
    SupportedQuaternionBlocks 1 h →
    QuaternionPrefixPolynomialEqv (tail+2) (copy h) h
  | [], _ => .nil
  | t :: ts, hh => by
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact Q'.eqv_refl _
        · intro coordinate _
          have ht := hh t List.mem_cons_self
          rcases t with ⟨m, coefficient⟩
          change exponentAt (copyMonomial m) coordinate = exponentAt m coordinate
          rcases m with _ | ⟨a, m⟩
          · rcases coordinate with (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | k)))))))) <;>
              simp [copyMonomial, exponentAt]
          rcases m with _ | ⟨b, m⟩
          · rcases coordinate with (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | k)))))))) <;>
              simp [copyMonomial, exponentAt]
          rcases m with _ | ⟨c, m⟩
          · rcases coordinate with (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | k)))))))) <;>
              simp [copyMonomial, exponentAt]
          rcases m with _ | ⟨d, m⟩
          · rcases coordinate with (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | k)))))))) <;>
              simp [copyMonomial, exponentAt]
          rcases m with _ | ⟨e, m⟩
          · rcases coordinate with (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | k)))))))) <;>
              simp [copyMonomial, exponentAt]
          · simp only [List.length_cons] at ht
            omega
      · exact copy_head_prefix tail ts (fun s hs => hh s (List.mem_cons_of_mem t hs))

private theorem copy_head_carrier (tail : Nat) (h : RatPoly)
    (hh : SupportedQuaternionBlocks 1 h) :
    HaarCarrierEqv (tail+2) (copy h) h :=
  let hh' : SupportedQuaternionBlocks (tail+1) h :=
    fun t ht => Nat.le_trans (hh t ht) (Nat.mul_le_mul_left 4 (by omega))
  carrierOfPrefix (copy_supported (by omega) hh')
    (fun t ht => Nat.le_trans (hh t ht) (Nat.mul_le_mul_left 4 (by omega)))
    (copy_head_prefix tail h hh)

/-- Copying the product is the product of the copies on the full supported
shared-spectator carrier. -/
theorem copy_mul_carrier {blocks : Nat} (hb : 0 < blocks) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    HaarCarrierEqv (blocks+1) (copy (polyMul p q))
      (polyMul (copy p) (copy q)) := by
  let s := spareSwap blocks hb
  have hpref := carrierOfPrefix (reindex_supported s (liftHead p))
    (copy_supported hb hp) (copy_reindex_prefix blocks hb p)
  have hqref := carrierOfPrefix (reindex_supported s (liftHead q))
    (copy_supported hb hq) (copy_reindex_prefix blocks hb q)
  have hpqref := carrierOfPrefix
    (reindex_supported s (liftHead (polyMul p q)))
    (copy_supported hb (supported_polyMul hp hq))
    (copy_reindex_prefix blocks hb (polyMul p q))
  have halg : RatPolyCoeffEqv
      (reindexQuaternionPolynomial s (liftHead (polyMul p q)))
      (polyMul (reindexQuaternionPolynomial s (liftHead p))
        (reindexQuaternionPolynomial s (liftHead q))) := by
    rw [liftHead_mul, reindexQuaternionPolynomial_mul]
    exact .refl _
  exact hpqref.symm.trans ((RatPolyCoeffEqv.haarCarrier halg).trans
    (HaarCarrierEqv.mul hpref hqref))

/-- A copied lower polynomial paired with its retained-head lift is exactly
the square of its conditional head Haar projection. -/
theorem copy_lift_pair_eq_project_square (tail : Nat) (r : RatPoly)
    (_hr : SupportedQuaternionBlocks (tail+1) r) :
    quaternionHaar (tail+2) (polyMul (copy r) (liftHead r)) ≈
      quaternionHaar (tail+1) (polyMul (project 0 r) (project 0 r)) := by
  have hcopy := quaternionHaar_polyMul_headIndependent (tail+1)
    (copy r) (liftHead r) (lifted_head_independent r)
  rw [partial_copy, drop_liftHead] at hcopy
  have hleft : quaternionHaar (tail+1)
      (polyMul (liftHead (partialHaarHead r)) r) ≈
      quaternionHaar tail (polyMul (partialHaarHead r) (partialHaarHead r)) := by
    have h := quaternionHaar_polyMul_headIndependent tail r
      (liftHead (partialHaarHead r)) (lifted_head_independent _)
    rw [drop_liftHead] at h
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)) h
  have hright : quaternionHaar (tail+1)
      (polyMul (project 0 r) (project 0 r)) ≈
      quaternionHaar tail (polyMul (partialHaarHead r) (partialHaarHead r)) := by
    have hproject := quaternionHaar_polyMul_eq_after_integratingBlock
      (tail+1) 0 (by omega) (project 0 r) r (project_independent 0 r)
    have hindependent : HeadQuaternionIndependent (project 0 r) :=
      independent_has_degree_zero (project_independent 0 r)
    have hconditional := quaternionHaar_polyMul_headIndependent tail r
      (project 0 r) hindependent
    rw [drop_project_head] at hconditional
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hproject)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)) hconditional)
  exact Q'.eqv_trans _ _ _ hcopy
    (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright))

/-- One lower Gram channel, with all spectator variables shared, is the
conditional square of the corresponding channel-weighted input. -/
theorem sharedHead_channel_pairing (tail : Nat) (q h : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hh : SupportedQuaternionBlocks 1 h) :
    quaternionHaar (tail+2)
      (polyMul (polyMul h (liftHead h))
        (polyMul (copy q) (liftHead q))) ≈
      quaternionHaar (tail+1)
        (polyMul (project 0 (polyMul q h))
          (project 0 (polyMul q h))) := by
  have hqh : SupportedQuaternionBlocks (tail+1) (polyMul q h) :=
    supported_polyMul hq (fun t ht => Nat.le_trans (hh t ht)
      (Nat.mul_le_mul_left 4 (by omega)))
  have hcopy := copy_mul_carrier (by omega : 0 < tail+1) hq
    (fun t ht => Nat.le_trans (hh t ht) (Nat.mul_le_mul_left 4 (by omega)))
  have hhead := copy_head_carrier tail h hh
  have hlift : RatPolyCoeffEqv (liftHead (polyMul q h))
      (polyMul (liftHead q) (liftHead h)) := by
    rw [liftHead_mul]
    exact .refl _
  have hregroup : HaarCarrierEqv (tail+2)
      (polyMul (polyMul h (liftHead h)) (polyMul (copy q) (liftHead q)))
      (polyMul (copy (polyMul q h)) (liftHead (polyMul q h))) := by
    refine (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1))) (by decide)
      (fun | 0 => h | 1 => liftHead h | 2 => copy q | _ => liftHead q))).trans ?_
    have hfirst : HaarCarrierEqv (tail+2)
      (polyMul (copy q) h) (copy (polyMul q h)) :=
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ (copy q)) hhead.symm).trans
        hcopy.symm
    have hsecond : HaarCarrierEqv (tail+2)
        (polyMul (liftHead q) (liftHead h)) (liftHead (polyMul q h)) :=
      RatPolyCoeffEqv.haarCarrier hlift.symm
    exact HaarCarrierEqv.mul hfirst hsecond
  exact Q'.eqv_trans _ _ _ (haar_of_carrier hregroup)
    (copy_lift_pair_eq_project_square tail (polyMul q h) hqh)

end YMGap.Continuum.SU2QuaternionSharedHeadGramPairing

#print axioms YMGap.Continuum.SU2QuaternionSharedHeadGramPairing.copy_mul_carrier
#print axioms YMGap.Continuum.SU2QuaternionSharedHeadGramPairing.copy_lift_pair_eq_project_square
#print axioms YMGap.Continuum.SU2QuaternionSharedHeadGramPairing.sharedHead_channel_pairing
