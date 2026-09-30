/-
# A finite Haar family on the same spectator-weighted completion

The supplied certified weight omits every selected coordinate. The literal
family integration is a bounded map with explicit inherited Cauchy modulus.
Its completed fixed space contains every common coordinate fixed point.
This is an auxiliary reference construction, not an interacting conditional
projection or a spectral estimate. The consumer transfers it to the original
action to identify a block conditional's exact fixed space.
-/

import YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection

namespace YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionWeightedHaarBlockProjection
open YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem project_smul (i : Nat) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (project i (polySmul c f)) (polySmul c (project i f)) := by
  have h : RatPolyTermwiseEqv (project i (polySmul c f)) (polySmul c (project i f)) := by
    induction f with
    | nil => exact True.intro
    | cons t rest ih => exact ⟨rfl, Q'.mul_assoc_eqv _ _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight h

private theorem family_smul (ids : List Nat) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polySmul c f))
      (polySmul c (familyProject ids f)) := by
  induction ids generalizing f with
  | nil => exact .refl _
  | cons i ids ih =>
      exact (familyProject_congr ids (project_smul i c f)).trans (ih (project i f))

theorem family_square_contraction (blocks : Nat) (W : RatPoly)
    (H : Certificate blocks W) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks)
    (hW : ∀ i, i ∈ ids → QuaternionBlockIndependent i W)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    weightedPair blocks W (familyProject ids p) (familyProject ids p) ≤
      weightedPair blocks W p p := by
  induction ids generalizing p with
  | nil => exact Q'.le_of_eqv (Q'.eqv_refl _)
  | cons i ids ih =>
      exact Q'.le_trans' _ _ _
        (ih (fun j hj => hids j (List.mem_cons_of_mem i hj))
          (fun j hj => hW j (List.mem_cons_of_mem i hj))
          (project i p) (project_supported i hp))
        (weighted_project_square_contraction blocks i (hids i List.mem_cons_self)
          W p H (hW i List.mem_cons_self) hp)

variable (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)
  (ids : List Nat) (hids : ∀ i, i ∈ ids → i < blocks)
  (hW : ∀ i, i ∈ ids → QuaternionBlockIndependent i W)

local notation "D" => weightedGNSData blocks W H

/-- The reference is the literal finite family map, with squared norm cap one. -/
def familyMap : BoundedMap D (1 : Q') where
  toFun p := ⟨familyProject ids p.val, familyProject_supported ids p.property⟩
  nonnegative := by decide
  map_sub := by
    intro p q
    change RatPolyCoeffEqv
      (familyProject ids (polyAdd p.val (polySmul (-1) q.val)))
      (polyAdd (familyProject ids p.val) (polySmul (-1) (familyProject ids q.val)))
    rw [familyProject_add]
    exact (RatPolyCoeffEqv.refl _).add (family_smul ids (-1) q.val)
  norm_bound := by
    intro p
    exact Q'.le_trans' _ _ _ (family_square_contraction blocks W H ids hids hW p.val p.property)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 : Q')))
        (Q'.one_mul_eqv _))))

def familyProjection : GNSCompletionSpace D → GNSCompletionSpace D :=
  (familyMap blocks W H ids hids hW).completionMap

theorem familyProjection_mk (X : CauchyGNS D) :
    familyProjection blocks W H ids hids hW (Quotient.mk (cauchySetoid D) X) =
      Quotient.mk (cauchySetoid D) ((familyMap blocks W H ids hids hW).mapCauchy X) := rfl

theorem familyProjection_embed (p : (D).V) :
    familyProjection blocks W H ids hids hW (embedV D p) =
      embedV D ⟨familyProject ids p.val, familyProject_supported ids p.property⟩ := rfl

private theorem null_of_terms (X Y : CauchyGNS D)
    (h : ∀ n, (D).veq (X.seq n) (Y.seq n)) : CauchyNull D X Y := by
  intro epsilon he
  refine ⟨0, fun n _ => ?_⟩
  have hz : (D).rad (X.seq n) (Y.seq n) :=
    Q'.eqv_trans _ _ _ ((D).B_diag_congr
      ((D).add_congr (h n) ((D).veq_refl ((D).neg (Y.seq n))))) ((D).rad_refl _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) (Q'.le_of_lt he)

theorem familyProjection_fixed_cauchy (X : CauchyGNS D)
    (hX : ∀ n i, i ∈ ids → QuaternionBlockIndependent i (X.seq n).val) :
    familyProjection blocks W H ids hids hW (Quotient.mk (cauchySetoid D) X) =
      Quotient.mk (cauchySetoid D) X := by
  apply Quotient.sound
  apply null_of_terms
  intro n
  exact familyProject_fixed ids (X.seq n).val (hX n)

theorem familyProjection_nil (x : GNSCompletionSpace D) :
    familyProjection blocks W H [] (fun _ h => False.elim (List.not_mem_nil h))
      (fun _ h => False.elim (List.not_mem_nil h)) x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact null_of_terms blocks W H _ _ (fun _ => (D).veq_refl _)

/-- Composition follows the existing head-first polynomial schedule. -/
theorem familyProjection_cons (i : Nat)
    (hi : i < blocks) (hWi : QuaternionBlockIndependent i W)
    (x : GNSCompletionSpace D) :
    familyProjection blocks W H (i :: ids)
      (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ hi) (hids j))
      (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ hWi) (hW j)) x =
    familyProjection blocks W H ids hids hW (projection blocks W H i hi hWi x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact null_of_terms blocks W H _ _ (fun _ => (D).veq_refl _)

theorem familyProjection_singleton (i : Nat)
    (hi : i < blocks) (hWi : QuaternionBlockIndependent i W)
    (x : GNSCompletionSpace D) :
    familyProjection blocks W H [i]
      (fun j hj => (List.mem_singleton.mp hj) ▸ hi)
      (fun j hj => (List.mem_singleton.mp hj) ▸ hWi) x =
      projection blocks W H i hi hWi x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact null_of_terms blocks W H _ _ (fun _ => (D).veq_refl _)

/-- Every common coordinate fixed point is fixed by the whole family.
Repeated or empty coordinate lists require no additional hypotheses. -/
theorem familyProjection_fixed_of_singletons (x : GNSCompletionSpace D)
    (hx : ∀ i (hi : i ∈ ids),
      projection blocks W H i (hids i hi) (hW i hi) x = x) :
    familyProjection blocks W H ids hids hW x = x := by
  induction ids with
  | nil => exact familyProjection_nil blocks W H x
  | cons i ids ih =>
      let hb := fun j hj => hids j (List.mem_cons_of_mem i hj)
      let hw := fun j hj => hW j (List.mem_cons_of_mem i hj)
      rw [familyProjection_cons blocks W H ids hb hw i
        (hids i List.mem_cons_self) (hW i List.mem_cons_self) x,
        hx i List.mem_cons_self]
      exact ih hb hw (fun j hj => hx j (List.mem_cons_of_mem i hj))

#print axioms family_square_contraction
#print axioms familyMap
#print axioms familyProjection
#print axioms familyProjection_mk
#print axioms familyProjection_embed
#print axioms familyProjection_fixed_cauchy
#print axioms familyProjection_nil
#print axioms familyProjection_cons
#print axioms familyProjection_singleton
#print axioms familyProjection_fixed_of_singletons

end YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion
