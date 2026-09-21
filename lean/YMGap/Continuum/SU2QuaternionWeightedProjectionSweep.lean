/-
# Weighted conditional-projection sweeps

Each selected block is integrated only after multiplication by its own local
weight.  Pairwise locality lets the successive conditional projections be
moved through the other weights under the original product Haar functional.
This is a finite Fubini identity on one carrier; it does not identify the
sweep with a temporal transfer operator by itself.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockProjection
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

namespace YMGap.Continuum.SU2QuaternionWeightedProjectionSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Multiply by each selected local weight and conditionally integrate that
same block.  No unselected block is integrated by this definition. -/
def weightedSweep (W : Nat → RatPoly) : List Nat → RatPoly → RatPoly
  | [], p => p
  | i :: ids, p => project i (polyMul (W i) (weightedSweep W ids p))

/-- Support is preserved when every selected local weight has the same finite
carrier support. -/
theorem weightedSweep_supported {blocks : Nat} (W : Nat → RatPoly) :
    ∀ (ids : List Nat) {p : RatPoly},
      (∀ i, i ∈ ids → SupportedQuaternionBlocks blocks (W i)) →
      SupportedQuaternionBlocks blocks p →
      SupportedQuaternionBlocks blocks (weightedSweep W ids p)
  | [], _, _, hp => hp
  | i :: ids, _, hW, hp =>
      project_supported i (supported_polyMul (hW i List.mem_cons_self)
        (weightedSweep_supported W ids
          (fun j hj => hW j (List.mem_cons_of_mem i hj)) hp))

/-- A spectator absent from the input and every selected weight stays absent
through the complete sweep. -/
theorem weightedSweep_independent (block : Nat) (W : Nat → RatPoly) :
    ∀ (ids : List Nat) {p : RatPoly},
      (∀ i, i ∈ ids → QuaternionBlockIndependent block (W i)) →
      QuaternionBlockIndependent block p →
      QuaternionBlockIndependent block (weightedSweep W ids p)
  | [], _, _, hp => hp
  | i :: ids, _, hW, hp =>
      project_preserves_independent i
        (quaternionBlockIndependent_polyMul (hW i List.mem_cons_self)
          (weightedSweep_independent block W ids
            (fun j hj => hW j (List.mem_cons_of_mem i hj)) hp))

/-- Two weighted conditional updates commute when each weight is independent
of the other update's block.  The statement also covers equal indices when
both explicit independence premises are supplied. -/
theorem weightedUpdate_comm (i j : Nat) (A B p : RatPoly)
    (hAj : QuaternionBlockIndependent j A)
    (hBi : QuaternionBlockIndependent i B) :
    RatPolyCoeffEqv
      (project i (polyMul A (project j (polyMul B p))))
      (project j (polyMul B (project i (polyMul A p)))) := by
  have hreorder : RatPolyCoeffEqv (polyMul A (polyMul B p))
      (polyMul B (polyMul A p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => A | 1 => B | _ => p)
  exact (project_congr i (project_mul_of_independent j A (polyMul B p) hAj).symm).trans
    ((project_comm i j (polyMul A (polyMul B p))).trans
      (project_congr j ((project_congr i hreorder).trans
        (project_mul_of_independent i B (polyMul A p) hBi))))

private theorem move_head_weight (a s r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a s) r) (polyMul s (polyMul a r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => a | 1 => s | _ => r)

private theorem restore_product_order (a P p r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul P p) (polyMul a r))
      (polyMul (polyMul (polyMul a P) p) r) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
    (by decide) (fun | 0 => a | 1 => P | 2 => p | _ => r)

/-- Under a test independent of every swept block, the weighted conditional
sweep has exactly the pairing of multiplication by the full finite product.
Same-index weights may be arbitrary; only distinct selected blocks must be
independent. -/
theorem pairing (blocks : Nat) (W : Nat → RatPoly) :
    ∀ (ids : List Nat) (p r : RatPoly),
      ids.Nodup →
      (∀ i, i ∈ ids → i < blocks) →
      (∀ i, i ∈ ids → ∀ j, j ∈ ids → i ≠ j →
        QuaternionBlockIndependent j (W i)) →
      (∀ i, i ∈ ids → QuaternionBlockIndependent i r) →
      quaternionHaar blocks (polyMul (weightedSweep W ids p) r) ≈
        quaternionHaar blocks
          (polyMul (polyMul (polynomialProduct W ids) p) r)
  | [], p, r, _, _, _, _ =>
      haar_of_coeff ((RatPolyCoeffEqv.one_mul p).mul_right r).symm
  | i :: ids, p, r, hn, hi, hW, hr => by
      have hnodup := List.nodup_cons.mp hn
      have hii : i < blocks := hi i List.mem_cons_self
      have hri : QuaternionBlockIndependent i r := hr i List.mem_cons_self
      have hproject := project_selfAdjoint blocks i hii
        (polyMul (W i) (weightedSweep W ids p)) r
      have hfixed := project_fixed i r hri
      have hfirst : quaternionHaar blocks
          (polyMul (weightedSweep W (i :: ids) p) r) ≈
          quaternionHaar blocks
            (polyMul (weightedSweep W ids p) (polyMul (W i) r)) :=
        Q'.eqv_trans _ _ _ hproject
          (Q'.eqv_trans _ _ _
            (haar_of_coeff (hfixed.mul_left
              (polyMul (W i) (weightedSweep W ids p))))
            (haar_of_coeff (move_head_weight (W i) (weightedSweep W ids p) r)))
      have htest : ∀ j, j ∈ ids →
          QuaternionBlockIndependent j (polyMul (W i) r) := by
        intro j hj
        apply quaternionBlockIndependent_polyMul
        · exact hW i List.mem_cons_self j (List.mem_cons_of_mem i hj)
            (by intro hij; subst j; exact hnodup.1 hj)
        · exact hr j (List.mem_cons_of_mem i hj)
      have htail := pairing blocks W ids p (polyMul (W i) r) hnodup.2
        (fun j hj => hi j (List.mem_cons_of_mem i hj))
        (fun a ha b hb hab => hW a (List.mem_cons_of_mem i ha)
          b (List.mem_cons_of_mem i hb) hab)
        htest
      exact Q'.eqv_trans _ _ _ hfirst
        (Q'.eqv_trans _ _ _ htail
          (haar_of_coeff (restore_product_order (W i)
            (polynomialProduct W ids) p r)))

end YMGap.Continuum.SU2QuaternionWeightedProjectionSweep

#print axioms YMGap.Continuum.SU2QuaternionWeightedProjectionSweep.weightedSweep_supported
#print axioms YMGap.Continuum.SU2QuaternionWeightedProjectionSweep.weightedSweep_independent
#print axioms YMGap.Continuum.SU2QuaternionWeightedProjectionSweep.weightedUpdate_comm
#print axioms YMGap.Continuum.SU2QuaternionWeightedProjectionSweep.pairing
