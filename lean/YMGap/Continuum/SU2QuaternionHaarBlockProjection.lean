/-
# Orthogonal conditional projections on the ORIGINAL polynomial Haar carrier

Integrating one quaternion block is a concrete coefficient-retaining
projection. Its complement has zero conditional mean and is orthogonal to
every polynomial independent of that block. Exact Pythagoras follows on the
same full polynomial carrier, with no coefficient norm or diagonal surrogate.

The consumer is product-kinetic heat tensorization. This module proves only
the conditional projection algebra: no heat contraction, interacting weight,
physical OS comparison, or continuum gap is assumed or concluded.
-/

import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct

namespace YMGap.Continuum.SU2QuaternionHaarBlockProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Conditional Haar integration keeps all original coordinate positions. -/
def project (block : Nat) (f : RatPoly) : RatPoly := integrateQuaternionBlock block f

/-- The genuine conditionally centered complement, retaining every spectator. -/
def fluctuation (block : Nat) (f : RatPoly) : RatPoly :=
  polyAdd f (polyNeg (project block f))

theorem project_supported {blocks : Nat} (block : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (project block f) :=
  integrateQuaternionBlock_supported block hf

theorem fluctuation_supported {blocks : Nat} (block : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (fluctuation block f) := by
  apply supported_add hf
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact project_supported block hf s hs

theorem project_independent (block : Nat) (f : RatPoly) :
    QuaternionBlockIndependent block (project block f) :=
  integrateQuaternionBlock_independent block f

/-- Integrating one block preserves every exact degree in a distinct block. -/
theorem project_degree_of_ne {selected block degree : Nat} {f : RatPoly}
    (hne : block ≠ selected) (hf : HasQuaternionBlockDegree block degree f) :
    HasQuaternionBlockDegree block degree (project selected f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change exponentAt (clearQuaternionBlock selected s.1) (4*block+0) +
      exponentAt (clearQuaternionBlock selected s.1) (4*block+1) +
      exponentAt (clearQuaternionBlock selected s.1) (4*block+2) +
      exponentAt (clearQuaternionBlock selected s.1) (4*block+3) = degree
  rw [exponentAt_clearQuaternionBlock_of_ne s.1 hne (by decide : 0 < 4),
    exponentAt_clearQuaternionBlock_of_ne s.1 hne (by decide : 1 < 4),
    exponentAt_clearQuaternionBlock_of_ne s.1 hne (by decide : 2 < 4),
    exponentAt_clearQuaternionBlock_of_ne s.1 hne (by decide : 3 < 4)]
  exact hf s hs

/-- Conditional centering also preserves every spectator's exact degree. -/
theorem fluctuation_degree_of_ne {selected block degree : Nat} {f : RatPoly}
    (hne : block ≠ selected) (hf : HasQuaternionBlockDegree block degree f) :
    HasQuaternionBlockDegree block degree (fluctuation selected f) :=
  hf.add (HasQuaternionBlockDegree.neg (project_degree_of_ne hne hf))

/-- The output-independence premise needed when the head heat map is applied
to this module's actual conditionally centered complement. -/
theorem fluctuation_head_output_independent {f : RatPoly}
    (hf : HasQuaternionBlockDegree 1 0 f) :
    HasQuaternionBlockDegree 1 0 (fluctuation 0 f) :=
  fluctuation_degree_of_ne (by decide : 1 ≠ 0) hf

private theorem project_fixed_termwise (block : Nat) : ∀ f : RatPoly,
    QuaternionBlockIndependent block f → RatPolyTermwiseEqv (project block f) f
  | [], _ => True.intro
  | t::rest, hf => by
      have hm := hf t List.mem_cons_self
      have hmoment : quaternionBlockMoment block t.1 ≈ 1 := by
        have h := quaternionBlockMoment_clear_self t.1 block
        rw [hm] at h
        exact h
      exact ⟨hm,
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hmoment) (Q'.mul_one_eqv _),
        project_fixed_termwise block rest (fun s hs => hf s (List.mem_cons_of_mem t hs))⟩

/-- The projection fixes every polynomial independent of its selected block. -/
theorem project_fixed (block : Nat) (f : RatPoly)
    (hf : QuaternionBlockIndependent block f) : RatPolyCoeffEqv (project block f) f :=
  fun weight => ratWeightedSum_termwise_eqv weight (project_fixed_termwise block f hf)

/-- Idempotence is coefficientwise, before any other Haar integration. -/
theorem project_idempotent (block : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (project block (project block f)) (project block f) :=
  project_fixed block _ (project_independent block f)

theorem project_add (block : Nat) (f g : RatPoly) :
    project block (polyAdd f g) = polyAdd (project block f) (project block g) :=
  List.map_append

theorem project_neg (block : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (project block (polyNeg f)) (polyNeg (project block f)) := by
  have ht : RatPolyTermwiseEqv (project block (polyNeg f)) (polyNeg (project block f)) := by
    induction f with
    | nil => exact True.intro
    | cons t rest ih => exact ⟨rfl, Q'.neg_mul_eqv _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

/-- Distinct conditional integrations commute with every coefficient intact. -/
theorem project_comm (left right : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (project left (project right f)) (project right (project left f)) := by
  by_cases he : left = right
  · subst right
    exact .refl _
  have ht : RatPolyTermwiseEqv (project left (project right f)) (project right (project left f)) := by
    induction f with
    | nil => exact True.intro
    | cons t rest ih =>
      refine ⟨clearQuaternionBlock_comm left right t.1, ?_, ih⟩
      change (t.2 * quaternionBlockMoment right t.1) *
          quaternionBlockMoment left (clearQuaternionBlock right t.1) ≈
        (t.2 * quaternionBlockMoment left t.1) *
          quaternionBlockMoment right (clearQuaternionBlock left t.1)
      rw [quaternionBlockMoment_clear_of_ne t.1 he,
        quaternionBlockMoment_clear_of_ne t.1 (Ne.symm he)]
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => t.2 | 1 => quaternionBlockMoment right t.1
             | _ => quaternionBlockMoment left t.1)
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem add_neg_zero (f : RatPoly) :
    RatPolyCoeffEqv (polyAdd f (polyNeg f)) polyZero :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => f)).trans
      (RatPolyCoeffEqv.zero_smul polyOne)

/-- Exact conditional centering, stronger than a zero total mean. -/
theorem project_fluctuation_zero (block : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (project block (fluctuation block f)) polyZero := by
  unfold fluctuation
  rw [project_add]
  exact ((RatPolyCoeffEqv.refl _).add
    ((project_neg block _).trans (RatPolyCoeffEqv.neg (project_idempotent block f)))).trans
      (add_neg_zero (project block f))

/-- Removing the cleared head coordinates identifies the two existing
conditional integration conventions by literal polynomial equality. -/
theorem drop_project_head : ∀ f : RatPoly,
    dropHeadPolynomial (project 0 f) = partialHaarHead f
  | [] => rfl
  | t::rest => by
      change ((clearQuaternionBlock 0 t.1).drop 4,
          t.2 * quaternionBlockMoment 0 t.1) :: dropHeadPolynomial (project 0 rest) =
        (t.1.drop 4, t.2 * headQuaternionMoment t.1) :: partialHaarHead rest
      rw [clearQuaternionBlock_drop_of_lt t.1 (by decide : 0 < 1), drop_project_head rest]
      rfl

private theorem drop_congr {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (dropHeadPolynomial f) (dropHeadPolynomial g) := by
  intro weight
  have hp : ∀ p : RatPoly, ratWeightedSum weight (dropHeadPolynomial p) =
      ratWeightedSum (fun m => weight (m.drop 4)) p := by
    intro p
    induction p with
    | nil => rfl
    | cons t rest ih =>
      change t.2 * weight (t.1.drop 4) + ratWeightedSum weight (dropHeadPolynomial rest) = _
      rw [ih]
      rfl
  rw [hp f, hp g]
  exact h _

/-- The precise conditional-centering premise of the one-link heat estimate. -/
theorem partialHaarHead_fluctuation_zero (f : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (fluctuation 0 f)) polyZero := by
  rw [← drop_project_head]
  exact drop_congr (project_fluctuation_zero 0 f)

/-- No support premise is needed for the original functional's Fubini identity. -/
theorem project_mean (blocks block : Nat) (hb : block < blocks) (f : RatPoly) :
    quaternionHaar blocks (project block f) ≈ quaternionHaar blocks f :=
  Q'.eqv_trans _ _ _ (quaternionHaar_eq_finiteProductHaar blocks _)
    (Q'.eqv_trans _ _ _ (finiteProductHaar_integrateQuaternionBlock blocks block hb f)
      (Q'.eqv_symm (quaternionHaar_eq_finiteProductHaar blocks f)))

/-- Every independent test is orthogonal to the conditionally centered complement. -/
theorem fluctuation_orthogonal (blocks block : Nat) (hb : block < blocks)
    (f g : RatPoly) (hg : QuaternionBlockIndependent block g) :
    quaternionHaar blocks (polyMul g (fluctuation block f)) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_eq_after_integratingBlock blocks block hb g _ hg)
    (haar_of_coeff (((project_fluctuation_zero block f).mul_left g).trans
      (RatPolyCoeffEqv.mul_zero_right g)))

theorem project_fluctuation_orthogonal (blocks block : Nat) (hb : block < blocks)
    (f g : RatPoly) :
    quaternionHaar blocks (polyMul (project block g) (fluctuation block f)) ≈ 0 :=
  fluctuation_orthogonal blocks block hb f _ (project_independent block g)

/-- Conditional projection is self-adjoint for the actual full Haar pairing. -/
theorem project_selfAdjoint (blocks block : Nat) (hb : block < blocks) (f g : RatPoly) :
    quaternionHaar blocks (polyMul (project block f) g) ≈
      quaternionHaar blocks (polyMul f (project block g)) := by
  have hleft := quaternionHaar_polyMul_eq_after_integratingBlock blocks block hb
    (project block f) g (project_independent block f)
  have hright : quaternionHaar blocks (polyMul f (project block g)) ≈
      quaternionHaar blocks (polyMul (project block f) (project block g)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_eq_after_integratingBlock blocks block hb
          (project block g) f (project_independent block g))
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

/-- Exact Pythagoras: no dimension factor and no triangle-inequality loss. -/
theorem square_decomposition (blocks block : Nat) (hb : block < blocks) (f : RatPoly) :
    quaternionHaar blocks (polyMul f f) ≈
      quaternionHaar blocks (polyMul (project block f) (project block f)) +
        quaternionHaar blocks (polyMul (fluctuation block f) (fluctuation block f)) := by
  let p := project block f
  let q := fluctuation block f
  have hc : quaternionHaar blocks (polyMul p q) ≈ 0 :=
    project_fluctuation_orthogonal blocks block hb f f
  have halg : RatPolyCoeffEqv (polyMul f f)
      (polyAdd (polyMul p p) (polyAdd (polyMul q q)
        (polyAdd (polyMul p q) (polyMul p q)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
          (.add
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1)))))))
      (by decide) (fun | 0 => f | _ => p)
  have hz : quaternionHaar blocks (polyAdd (polyMul p q) (polyMul p q)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc hc) (by decide : (0 : Q') + 0 ≈ 0))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff halg)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))))))

/-- Conditional Haar projection is contractive on the full supported carrier. -/
theorem project_square_contraction (blocks block : Nat) (hb : block < blocks)
    (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks (polyMul (project block f) (project block f)) ≤
      quaternionHaar blocks (polyMul f f) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (Certificate.haar_nonnegative (.square (fluctuation block f) (fluctuation_supported block hf))))
    (Q'.ge_of_eqv (square_decomposition blocks block hb f))

end YMGap.Continuum.SU2QuaternionHaarBlockProjection

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.fluctuation
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.fluctuation_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_independent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_degree_of_ne
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.fluctuation_degree_of_ne
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.fluctuation_head_output_independent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_fixed
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_idempotent
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_add
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_neg
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_comm
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_fluctuation_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.drop_project_head
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.partialHaarHead_fluctuation_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_mean
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.fluctuation_orthogonal
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_fluctuation_orthogonal
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_selfAdjoint
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.square_decomposition
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockProjection.project_square_contraction
