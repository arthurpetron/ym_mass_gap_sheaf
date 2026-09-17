/-
# Finite signed algebra of actual spatial Wilson-loop characters

Each generator retains its original ordered, oriented, closed spatial loop
and its physical-link support. Different generators may lie at different
times. Finite sums, products and signed rational scales are evaluated on the
same original slab link polynomials.

Every temporal cut preserves the evaluated expression under every supported
spectator insertion. In the product case BOTH factors are transformed; the
first cancellation uses the transformed second factor in its spectator. Thus
no disjoint-link or independence premise is introduced. The resulting
expression passes through the existing common sweep of the complete selected
original action.

This is finite original-observable algebra and an exact action identity, not
full gauge-algebra density, an embedding into the face-generated spatial
union, an OS multiplier bound, a regulator limit or a mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
import YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep

namespace YMGap.Continuum.BF4ExactSlabSpatialWilsonAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (haar_of_coeff_eqv)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Each loop carries its own actual spatial slice; products need not share it. -/
inductive Expression (extent : Nat) : Type where
  | one : Expression extent
  | loop (slice : Nat) (value : SpatialLoop extent slice) (spin : Nat) : Expression extent
  | add : Expression extent → Expression extent → Expression extent
  | mul : Expression extent → Expression extent → Expression extent
  | smul : Q' → Expression extent → Expression extent

/-- Evaluation keeps each loop's ordered holonomy, not individual edge traces. -/
def evaluate {extent : Nat} : Expression extent → RatPoly
  | .one => polyOne
  | .loop _ value spin => character extent value.edges spin
  | .add e f => polyAdd (evaluate e) (evaluate f)
  | .mul e f => polyMul (evaluate e) (evaluate f)
  | .smul c e => polySmul c (evaluate e)

theorem evaluate_supported {extent : Nat} : ∀ e : Expression extent,
    SupportedQuaternionBlocks (B extent) (evaluate e)
  | .one => supported_one _
  | .loop _ value spin => character_supported extent value.edges spin
  | .add e f => supported_add (evaluate_supported e) (evaluate_supported f)
  | .mul e f => supported_polyMul (evaluate_supported e) (evaluate_supported f)
  | .smul c e => by
      intro term ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact evaluate_supported e s hs

private theorem haar_mul_add (blocks : Nat) (r p q : RatPoly) :
    quaternionHaar blocks (polyMul r (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul r p) + quaternionHaar blocks (polyMul r q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks (RatPolyCoeffEqv.mul_add_right r p q))
    (quaternionHaar_append blocks _ _)

private theorem insert_reorder (r p q : RatPoly) :
    RatPolyCoeffEqv (polyMul r (polyMul p q)) (polyMul (polyMul r q) p) :=
  ((RatPolyCoeffEqv.mul_comm p q).mul_left r).trans
    (RatPolyCoeffEqv.mul_assoc r q p).symm

/-- The entire algebra is invariant at every cut with its supported spectator
retained. Product cancellation uses the SAME jointly transformed polynomial. -/
theorem evaluate_ledger_invariant {extent : Nat} (cut : Nat) :
    ∀ (e : Expression extent) (r : RatPoly),
    SupportedQuaternionBlocks (B extent) r →
    quaternionHaar (B extent)
        (polyMul r (applyTemporalTranslationLedger extent cut (evaluate e))) ≈
      quaternionHaar (B extent) (polyMul r (evaluate e))
  | .one, r, hr => by
      have h : PaddedPolynomialCoeffEqv (B extent)
          (applyTemporalTranslationLedger extent cut polyOne) polyOne := by
        have hq := applySteps_one (temporalTailBlocks_pos extent)
          (temporalTranslationSteps extent cut)
        rw [temporalTotalBlocks_eq] at hq
        exact hq.scalar
      exact h.haar_insert
        (applyTemporalTranslationLedger_supported extent cut polyOne (supported_one _))
        (supported_one _) r hr
  | .loop _ value spin, r, hr => ledger_invariant value cut spin r hr
  | .add e f, r, hr => by
      change quaternionHaar (B extent)
        (polyMul r (applyTemporalTranslationLedger extent cut
          (polyAdd (evaluate e) (evaluate f)))) ≈ _
      have hmap : applyTemporalTranslationLedger extent cut (polyAdd (evaluate e) (evaluate f)) =
          polyAdd (applyTemporalTranslationLedger extent cut (evaluate e))
            (applyTemporalTranslationLedger extent cut (evaluate f)) :=
        applySelectedTranslationSteps_add (temporalTailBlocks_pos extent) _ _ _
      rw [hmap]
      exact Q'.eqv_trans _ _ _ (haar_mul_add (B extent) r _ _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
          (evaluate_ledger_invariant cut e r hr) (evaluate_ledger_invariant cut f r hr))
          (Q'.eqv_symm (haar_mul_add (B extent) r (evaluate e) (evaluate f))))
  | .mul e f, r, hr => by
      let p := evaluate e
      let q := evaluate f
      let tp := applyTemporalTranslationLedger extent cut p
      let tq := applyTemporalTranslationLedger extent cut q
      have hp : SupportedQuaternionBlocks (B extent) p := evaluate_supported e
      have hq : SupportedQuaternionBlocks (B extent) q := evaluate_supported f
      have htq : SupportedQuaternionBlocks (B extent) tq :=
        applyTemporalTranslationLedger_supported extent cut q hq
      have hmap : RatPolyCoeffEqv
          (applyTemporalTranslationLedger extent cut (polyMul p q)) (polyMul tp tq) :=
        applySelectedTranslationSteps_mul (temporalTailBlocks_pos extent) _ p q
      have h0 := haar_of_coeff_eqv (B extent) (hmap.mul_left r)
      have h1 := haar_of_coeff_eqv (B extent) (insert_reorder r tp tq)
      -- First cancellation retains the transformed second factor as spectator.
      have h2 := evaluate_ledger_invariant cut e (polyMul r tq) (supported_polyMul hr htq)
      have h3 := haar_of_coeff_eqv (B extent)
        ((insert_reorder r p tq).symm.trans (RatPolyCoeffEqv.mul_assoc r p tq).symm)
      -- The second cancellation retains the original first factor.
      have h4 := evaluate_ledger_invariant cut f (polyMul r p) (supported_polyMul hr hp)
      have h5 := haar_of_coeff_eqv (B extent) (RatPolyCoeffEqv.mul_assoc r p q)
      exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
        (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3
          (Q'.eqv_trans _ _ _ h4 h5))))
  | .smul c e, r, hr => by
      have hmap : RatPolyCoeffEqv
          (applyTemporalTranslationLedger extent cut (polySmul c (evaluate e)))
          (polySmul c (applyTemporalTranslationLedger extent cut (evaluate e))) :=
        applySelectedTranslationSteps_smul (temporalTailBlocks_pos extent) _ c (evaluate e)
      exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv (B extent) (hmap.mul_left r))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (B extent) c r _)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left c _ _ (evaluate_ledger_invariant cut e r hr))
            (Q'.eqv_symm (quaternionHaar_polyMul_smul_right (B extent) c r (evaluate e)))))

/-- The evaluated original Wilson expression is unchanged through the common
sweep of every selected action factor, with the same finite Haar carrier. -/
theorem original_chain_pairing (w : Q') (K extent width start steps : Nat)
    (e : Expression extent) :
    quaternionHaar (B extent)
        (polyMul (evaluate e) (originalChainAction w K extent width start steps)) ≈
      quaternionHaar (B extent)
        (polyMul (evaluate e) (ambientChain w K extent width start steps)) :=
  invariant_original_chain_pairing w K extent width start steps (evaluate e)
    (evaluate_supported e) (fun cut => evaluate_ledger_invariant cut e)

#print axioms Expression
#print axioms evaluate
#print axioms evaluate_supported
#print axioms evaluate_ledger_invariant
#print axioms original_chain_pairing

end YMGap.Continuum.BF4ExactSlabSpatialWilsonAlgebra
