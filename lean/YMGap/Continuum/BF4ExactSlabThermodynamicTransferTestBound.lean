/-
# A transfer-relative test bound on the ORIGINAL thermodynamic completion

Full-action site Cauchy--Schwarz uses the constructed inward test. Its
mixed term is the original zero-lag pairing; its first-state diagonal is
the actual geometric one-step form; its test diagonal has the unchanged
source-only cap. The SAME original partition and volume limits give

    B(f,x)^2 <= bound(f) * B(T1 x,x).

Common-base transport preserves the fixed test's cap. The existing pairing
limits therefore extend x to the ENTIRE original completion, with f a
fixed original presentation. There is no inverse-heat premise, substituted
carrier, supplied dual-functional bound or newly chosen thermodynamic law.

The finite inequality has explicit small-nome guards. The thermodynamic
and completed forms use SU(2), nome 1/1024, fixed spacing. The arbitrary-state
residual modulus, full-space time zero and continuum/all-group Clay target
are not claimed by this estimate alone.
-/

import YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz
import YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm
import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound (bound bound_bulkAtTime)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression (fromLower)
open YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison
open YMGap.Continuum.BF4ExactSlabSiteInwardTest
open YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm
open YMGap.Continuum.BF4ExactSlabSiteOneStepForm
open YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz
open YMGap.Continuum.BF4ExactSlabSiteExpectation
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm (formLimit)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local notation "B" => completedInner

private theorem mul_bound_right {a b c : CReal} (ha : leEv czero a) (hbc : leEv b c) :
    leEv (CReal.mul b a) (CReal.mul c a) :=
  (leEv_congr (CRealAlg.cmul_comm a b) (CRealAlg.cmul_comm a c)).mp (leEv_mul_nonneg_left ha hbc)

theorem even_transfer_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    {base : Nat} (margin : Nat) (e f : PlaquetteExpression base) :
    let M := expectation w hw0 hw1 hsmall hd (adjacentEvenExtent (base+1+margin))
      (slabPhysicalFaceEdges (adjacentEvenExtent (base+1+margin))) (fun _ hi => hi) (mixedInsertion margin e f)
    leEv (CReal.mul M M) (CReal.mul (ofQ' (bound f)) (evenMean w hw0 hw1 hsmall hd (oneStepExpression e) margin)) := by
  have hcs := expectation_cauchySchwarz w hw0 hw1 hsmall hd (base+1+margin)
    (evenEvaluate margin (inward f)) (evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e)))
    (inward_oneSided margin f) (lower_oneSided margin _)
    (inwardSquareBound margin f).support (evenSquareBound margin _).support
  have hnorm := site_diagonal_bound w hw0 hw1 hsmall hd margin f
  have hpos := site_nonnegative w hw0 hw1 hsmall hd (base+1+margin)
    (evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e)))
    (lower_oneSided margin _) (evenSquareBound margin _).support
  exact leEv_trans hcs (leEv_trans (mul_bound_right hpos hnorm)
    (leEv_of_equiv (Pivot2.mul_congr_right (site_expectation_pin w hw0 hw1 hsmall hd margin e))))

/-- Same original thermodynamic form; only the fixed test determines the cap. -/
theorem form_transfer_bound {base : Nat} (e f : PlaquetteExpression base) :
    leEv (CReal.mul (formLimit (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e))
      (formLimit (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e)))
      (CReal.mul (ofQ' (bound f)) (formLimit (bulkAtTime 1 ⟨1, by decide⟩ e) (bulkAtTime 1 ⟨0, by decide⟩ e))) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (mixed_thermodynamic_converges e f) (mixed_thermodynamic_converges e f))
    (convergesTo_const_mul (ofQ' (bound f)) (evenSequence_converges (oneStepExpression e)))
    (fun margin => even_transfer_bound nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2 margin e f)

private theorem sameBase_bound {base : Nat} (e f : PlaquetteExpression base) :
    RCle (RCmul (B (timeState 0 ⟨base,f⟩) (timeState 0 ⟨base,e⟩)) (B (timeState 0 ⟨base,f⟩) (timeState 0 ⟨base,e⟩)))
      (RCmul (Quotient.mk crealSetoid (ofQ' (bound f))) (B (timeState 1 ⟨base,e⟩) (timeState 0 ⟨base,e⟩))) := by
  rw [time_inner_bulk 1 ⟨0, by decide⟩ ⟨0, by decide⟩ f e,
    time_inner_bulk 1 ⟨1, by decide⟩ ⟨0, by decide⟩ e e]
  exact form_transfer_bound e f

private theorem bound_transport {a b : Nat} (h : a=b) (e : PlaquetteExpression a) :
    bound (transport h e) = bound e := by cases h; rfl

private theorem bound_atBase (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    bound (atBase p target hp) = bound p.expression := by
  unfold atBase
  rw [bound_transport]
  exact bound_bulkAtTime _ _ _

/-- All base sizes; rebasing the fixed test incurs NO cap loss. -/
theorem presented_bound (p f : Presentation) :
    leEv (CReal.mul (presentedForm f p) (presentedForm f p))
      (CReal.mul (ofQ' (diagonalCeiling f)) (presentedForm (translate 1 p) p)) := by
  have h := sameBase_bound (atBase p (p.base+f.base) (Nat.le_add_right _ _))
    (atBase f (p.base+f.base) (Nat.le_add_left _ _))
  simp only [timeState_rebase, bound_atBase] at h
  rw [timeState_zero, timeState_zero, timeState_pin, completedInner_embedPresentation,
    completedInner_embedPresentation] at h
  exact h

/-- The state varies, while the ORIGINAL test and its cap remain fixed. -/
theorem representative_bound (X : seminorm.Cauchy) (f : Presentation) :
    leEv (CReal.mul (representativeInner (seminorm.constant f) X) (representativeInner (seminorm.constant f) X))
      (CReal.mul (ofQ' (diagonalCeiling f)) (representativeInner (timeCauchy 1 X) X)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges (seminorm.constant f) X) (pairSequence_converges (seminorm.constant f) X))
    (convergesTo_const_mul (ofQ' (diagonalCeiling f)) (pairSequence_converges (timeCauchy 1 X) X))
    (fun n => presented_bound (X.seq n) f)

/-- Actual geometric T1, ENTIRE original completion, and original embedded test. -/
theorem completed_bound (x : Completion) (f : Presentation) :
    RCle (RCmul (B (embedPresentation f) x) (B (embedPresentation f) x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (diagonalCeiling f))) (B (completedTime 1 x) x)) := by
  refine Quotient.inductionOn x ?_
  exact fun X => representative_bound X f

end YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound.even_transfer_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound.form_transfer_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound.presented_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound.representative_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound.completed_bound
