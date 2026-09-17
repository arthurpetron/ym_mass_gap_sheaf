/-
# Finite families of original-coordinate Haar projections

The family projection is the existing finite integration schedule, not a
new carrier. It preserves coefficients, support, and every independent
spectator, and its output is independent of every selected coordinate.
Repeated indices are allowed.

The division-free weighted residual (P_F a)*f-P_F(a*f) is exactly centered
against the complete supplied weight a. Its Haar pairing with any
F-independent test vanishes. No positivity, transfer estimate, or uniform
spectral conclusion is assumed or proved. The consumer groups all inactive
kinetic coordinates while retaining the original spatial action.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

namespace YMGap.Continuum.SU2QuaternionHaarFamilyProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Apply the original in-place conditional integrations in list order. -/
abbrev familyProject (ids : List Nat) (f : RatPoly) : RatPoly :=
  integrateQuaternionBlocks ids f

theorem familyProject_congr (ids : List Nat) {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (familyProject ids f) (familyProject ids g) := by
  induction ids generalizing f g with
  | nil => exact h
  | cons i ids ih => exact ih (project_congr i h)

theorem familyProject_add (ids : List Nat) (f g : RatPoly) :
    familyProject ids (polyAdd f g) = polyAdd (familyProject ids f) (familyProject ids g) := by
  induction ids generalizing f g with
  | nil => rfl
  | cons i ids ih =>
      change familyProject ids (project i (polyAdd f g)) =
        polyAdd (familyProject ids (project i f)) (familyProject ids (project i g))
      rw [project_add]
      exact ih _ _

theorem familyProject_neg (ids : List Nat) (f : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polyNeg f)) (polyNeg (familyProject ids f)) := by
  induction ids generalizing f with
  | nil => exact .refl _
  | cons i ids ih =>
      exact (familyProject_congr ids (project_neg i f)).trans (ih (project i f))

theorem familyProject_supported {blocks : Nat} (ids : List Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (familyProject ids f) :=
  integrateBlocks_supported ids hf

/-- Integrating the family preserves independence of any spectator slot. -/
theorem familyProject_preserves_independent (ids : List Nat) {block : Nat} {f : RatPoly}
    (hf : QuaternionBlockIndependent block f) :
    QuaternionBlockIndependent block (familyProject ids f) := by
  induction ids generalizing f with
  | nil => exact hf
  | cons i ids ih => exact ih (project_preserves_independent i hf)

/-- Every selected coordinate is absent from the output, including for
schedules with repetitions. No coordinate-bound premise is needed. -/
theorem familyProject_independent (ids : List Nat) (f : RatPoly) (block : Nat)
    (hb : block ∈ ids) : QuaternionBlockIndependent block (familyProject ids f) := by
  induction ids generalizing f with
  | nil => exact False.elim (List.not_mem_nil hb)
  | cons i ids ih =>
      rcases List.mem_cons.mp hb with he | hb
      · subst block
        exact familyProject_preserves_independent ids (project_independent i f)
      · exact ih (project i f) hb

theorem familyProject_fixed (ids : List Nat) (f : RatPoly)
    (hf : ∀ i, i ∈ ids → QuaternionBlockIndependent i f) :
    RatPolyCoeffEqv (familyProject ids f) f := by
  induction ids generalizing f with
  | nil => exact .refl _
  | cons i ids ih =>
      exact (familyProject_congr ids (project_fixed i f (hf i List.mem_cons_self))).trans
        (ih f (fun j hj => hf j (List.mem_cons_of_mem i hj)))

theorem familyProject_idempotent (ids : List Nat) (f : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (familyProject ids f)) (familyProject ids f) :=
  familyProject_fixed ids _ (familyProject_independent ids f)

/-- Pull an explicitly family-independent factor through the complete
schedule. No factor involving a selected coordinate is dropped. -/
theorem familyProject_mul_of_independent (ids : List Nat) (r f : RatPoly)
    (hr : ∀ i, i ∈ ids → QuaternionBlockIndependent i r) :
    RatPolyCoeffEqv (familyProject ids (polyMul r f)) (polyMul r (familyProject ids f)) := by
  induction ids generalizing f with
  | nil => exact .refl _
  | cons i ids ih =>
      exact (familyProject_congr ids
        (project_mul_of_independent i r f (hr i List.mem_cons_self))).trans
        (ih (project i f) (fun j hj => hr j (List.mem_cons_of_mem i hj)))

/-- Original full Haar is unchanged by any in-range schedule. This is the
existing finite Fubini theorem with its original-functional identification. -/
theorem familyProject_mean (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (f : RatPoly) :
    quaternionHaar blocks (familyProject ids f) ≈ quaternionHaar blocks f :=
  Q'.eqv_trans _ _ _ (quaternionHaar_eq_finiteProductHaar blocks _)
    (Q'.eqv_trans _ _ _ (finiteProductHaar_integrateQuaternionBlocks blocks ids f hids)
      (Q'.eqv_symm (quaternionHaar_eq_finiteProductHaar blocks f)))

/-- Exact polynomial family centering without a reciprocal of P_F a. -/
def familyWeightedResidual (ids : List Nat) (a f : RatPoly) : RatPoly :=
  polyAdd (polyMul (familyProject ids a) f)
    (polyNeg (familyProject ids (polyMul a f)))

theorem familyWeightedResidual_supported {blocks : Nat} (ids : List Nat) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks blocks a) (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (familyWeightedResidual ids a f) := by
  apply supported_add (supported_polyMul (familyProject_supported ids ha) hf)
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact familyProject_supported ids (supported_polyMul ha hf) s hs

private theorem familyProject_sub (ids : List Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polyAdd p (polyNeg q)))
      (polyAdd (familyProject ids p) (polyNeg (familyProject ids q))) := by
  rw [familyProject_add]
  exact (RatPolyCoeffEqv.refl _).add (familyProject_neg ids q)

private theorem sub_self (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd p (polyNeg p)) polyZero :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => p)).trans
      (RatPolyCoeffEqv.zero_smul polyOne)

/-- Conditional zero against the full weight, at coefficient equality and
without support, positivity, or coordinate-bound hypotheses. -/
theorem familyProject_weightedResidual_zero (ids : List Nat) (a f : RatPoly) :
    RatPolyCoeffEqv
      (familyProject ids (polyMul a (familyWeightedResidual ids a f))) polyZero := by
  let A := familyProject ids a
  let M := familyProject ids (polyMul a f)
  have hraw : RatPolyCoeffEqv (polyMul a (familyWeightedResidual ids a f))
      (polyAdd (polyMul A (polyMul a f)) (polyNeg (polyMul M a))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.mul (.var 2) (.var 1)) (.neg (.var 3))))
      (.add (.mul (.var 2) (.mul (.var 0) (.var 1)))
        (.neg (.mul (.var 3) (.var 0)))) (by decide)
      (fun | 0 => a | 1 => f | 2 => A | _ => M)
  exact (familyProject_congr ids hraw).trans
    ((familyProject_sub ids _ _).trans
      (((familyProject_mul_of_independent ids A (polyMul a f)
        (familyProject_independent ids a)).add
        (RatPolyCoeffEqv.neg
          ((familyProject_mul_of_independent ids M a
            (familyProject_independent ids (polyMul a f))).trans
              (RatPolyCoeffEqv.mul_comm M A)))).trans (sub_self (polyMul A M))))

/-- Every family-independent test is orthogonal to the actual full-weight
residual. The weight a itself need not be independent or nonnegative. -/
theorem familyWeightedResidual_orthogonal {blocks : Nat} (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (a f b : RatPoly)
    (hb : ∀ i, i ∈ ids → QuaternionBlockIndependent i b) :
    quaternionHaar blocks (polyMul a (polyMul (familyWeightedResidual ids a f) b)) ≈ 0 := by
  have hr : RatPolyCoeffEqv (polyMul a (polyMul (familyWeightedResidual ids a f) b))
      (polyMul b (polyMul a (familyWeightedResidual ids a f))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => a | 1 => familyWeightedResidual ids a f | _ => b)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_eq_after_integratingBlocks blocks ids b
        (polyMul a (familyWeightedResidual ids a f)) hids hb)
      (haar_of_coeff (((familyProject_weightedResidual_zero ids a f).mul_left b).trans
        (RatPolyCoeffEqv.mul_zero_right b))))

#print axioms familyProject
#print axioms familyProject_congr
#print axioms familyProject_add
#print axioms familyProject_neg
#print axioms familyProject_supported
#print axioms familyProject_preserves_independent
#print axioms familyProject_independent
#print axioms familyProject_fixed
#print axioms familyProject_idempotent
#print axioms familyProject_mul_of_independent
#print axioms familyProject_mean
#print axioms familyWeightedResidual
#print axioms familyWeightedResidual_supported
#print axioms familyProject_weightedResidual_zero
#print axioms familyWeightedResidual_orthogonal

end YMGap.Continuum.SU2QuaternionHaarFamilyProjection
