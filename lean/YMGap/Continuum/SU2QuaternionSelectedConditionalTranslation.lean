/-
# Conditional Haar cancellation for an original selected-link translation

Expose the original selected/multiplier pair, use the proved conditional
head identity, and restore every original coordinate. The result is equality
under arbitrary insertions for the EXISTING selected left/right shears.
No weight is dropped and no independence assumption is imposed on the input.

This is a finite gauge-covariance prerequisite. It supplies neither the full
vertex-ledger/completed invariant-sector join nor a strict covariance bound.
-/

import YMGap.Continuum.SU2QuaternionConditionalHaarTranslation
import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionTranslationSpectatorProjection

namespace YMGap.Continuum.SU2QuaternionSelectedConditionalTranslation

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
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionConditionalHaarTranslation
open YMGap.Continuum.SU2QuaternionTranslationSpectatorProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

variable (tailBlocks selected multiplier : Nat) (hb : 0 < tailBlocks)
  (hs : selected < tailBlocks+1) (hm : multiplier < tailBlocks+1)
  (hne : selected ≠ multiplier)

local notation "E" => exposeTranslationPairPolynomial (tailBlocks+1) selected multiplier
  (by omega) hs hm
local notation "R" => restoreTranslationPairPolynomial (tailBlocks+1) selected multiplier
  (by omega) hs hm

private theorem restored_pair (r p : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    quaternionHaar (tailBlocks+1) (polyMul r (R p)) ≈
      quaternionHaar (tailBlocks+1) (polyMul (E r) p) :=
  Q'.eqv_trans _ _ _
    (reindex_pair (translationPairHeadPermutation (tailBlocks+1) selected hs)
      r _ hr (reindex_supported _ p))
    (reindex_pair (translationPairTailPermutation (tailBlocks+1) selected multiplier
      (by omega) hs hm) _ p (reindex_supported _ r) hp)

include hne in
private theorem selected_project (right : Bool) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1)
      (project selected (R (translatedHeadPolynomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) (E p))))
      (project selected p) := by
  let T := translatedHeadPolynomial
    (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
  have hEp : SupportedQuaternionBlocks (tailBlocks+1) (E p) :=
    exposeTranslationPairPolynomial_supported _ _ _ _ _ _ p
  have hT : SupportedQuaternionBlocks (tailBlocks+1) (T (E p)) := by
    cases right
    · exact leftTranslatedHeadPolynomial_supported tailBlocks hb (E p) hEp
    · exact rightTranslatedHeadPolynomial_supported tailBlocks hb (E p) hEp
  apply carrier_of_supported
    (project_supported selected
      (restoreTranslationPairPolynomial_supported _ _ _ _ _ _ _))
    (project_supported selected hp)
  intro r hr
  have hE := exposeTranslationPair_project (tailBlocks+1) selected multiplier
    (by omega) hs hm hne r
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (project_selfAdjoint (tailBlocks+1) selected hs r (R (T (E p)))))
    (Q'.eqv_trans _ _ _
      (restored_pair tailBlocks selected multiplier hb hs hm
        (project selected r) (T (E p)) (project_supported selected hr) hT)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hE.mul_right (T (E p))))
        (Q'.eqv_trans _ _ _
          (project_selfAdjoint (tailBlocks+1) 0 (by omega) (E r) (T (E p)))
          (Q'.eqv_trans _ _ _ (project_head_translated right tailBlocks hb (E p) (E r))
            (Q'.eqv_trans _ _ _
              (Q'.eqv_symm (project_selfAdjoint (tailBlocks+1) 0 (by omega) (E r) (E p)))
              (Q'.eqv_trans _ _ _
                (exposeTranslationPair_project_pairing (tailBlocks+1) selected multiplier
                  (by omega) hs hm hne r p hr hp)
                (project_selfAdjoint (tailBlocks+1) selected hs r p)))))))

/-- Integrating the original selected block cancels its actual left shear,
with every remaining polynomial insertion retained. -/
theorem project_selectedLeft (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1)
      (project selected (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne p)) (project selected p) :=
  selected_project tailBlocks selected multiplier hb hs hm hne false p hp

/-- The same statement for the original right Hamilton order. -/
theorem project_selectedRight (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1)
      (project selected (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne p)) (project selected p) :=
  selected_project tailBlocks selected multiplier hb hs hm hne true p hp

include hne in
private theorem selected_spectator (right : Bool) (block : Nat)
    (hk : block < tailBlocks+1) (hks : block ≠ selected) (hkm : block ≠ multiplier)
    (p : RatPoly) :
    RatPolyCoeffEqv
      (project block (R (translatedHeadPolynomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) (E p))))
      (R (translatedHeadPolynomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
        (E (project block p)))) := by
  let head := translationPairHeadPermutation (tailBlocks+1) selected hs
  let tail := translationPairTailPermutation (tailBlocks+1) selected multiplier (by omega) hs hm
  let k := tail.map (head.map block)
  have hhead : head.map block < tailBlocks+1 := head.map_lt block hk
  have htail : k < tailBlocks+1 := tail.map_lt _ hhead
  have hsource : head.map (tail.map k) = block := by
    dsimp only [k]
    rw [tail.involutive _ hhead, head.involutive _ hk]
  have hk0 : k ≠ 0 := by
    intro he
    rw [he] at hsource
    have hz := exposedTranslationPair_source_zero (tailBlocks+1) selected multiplier
      (by omega) hs hm hne
    exact hks (hsource.symm.trans hz)
  have hk1 : k ≠ 1 := by
    intro he
    rw [he] at hsource
    have hz := exposedTranslationPair_source_one (tailBlocks+1) selected multiplier
      (by omega) hs hm
    exact hkm (hsource.symm.trans hz)
  have hexpose : RatPolyCoeffEqv (E (project block p)) (project k (E p)) :=
    (RatPolyCoeffEqv.reindex tail (reindex_integrateQuaternionBlock head block hk p)).trans
      (reindex_integrateQuaternionBlock tail (head.map block) hhead
        (reindexQuaternionPolynomial head p))
  have hrestore (q : RatPoly) :
      RatPolyCoeffEqv (R (project k q)) (project block (R q)) := by
    have h := (RatPolyCoeffEqv.reindex head (reindex_integrateQuaternionBlock tail k htail q)).trans
      (reindex_integrateQuaternionBlock head (tail.map k) (tail.map_lt k htail)
        (reindexQuaternionPolynomial tail q))
    simpa only [hsource] using h
  refine (hrestore _).symm.trans ?_
  apply RatPolyCoeffEqv.reindex head
  apply RatPolyCoeffEqv.reindex tail
  exact (project_translatedHeadPolynomial right k (by omega) (E p)).trans
    (translatedHeadPolynomial_coeffEqv _ hexpose.symm)

/-- A distinct original spectator integration commutes coefficientwise with
the actual selected left shear. The gauge multiplier itself is excluded. -/
theorem project_spectator_selectedLeft (block : Nat)
    (hk : block < tailBlocks+1) (hks : block ≠ selected) (hkm : block ≠ multiplier)
    (p : RatPoly) :
    RatPolyCoeffEqv
      (project block (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne p))
      (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne (project block p)) :=
  selected_spectator tailBlocks selected multiplier hb hs hm hne false block hk hks hkm p

/-- Original-coordinate companion for the right Hamilton order. -/
theorem project_spectator_selectedRight (block : Nat)
    (hk : block < tailBlocks+1) (hks : block ≠ selected) (hkm : block ≠ multiplier)
    (p : RatPoly) :
    RatPolyCoeffEqv
      (project block (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne p))
      (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne (project block p)) :=
  selected_spectator tailBlocks selected multiplier hb hs hm hne true block hk hks hkm p

#print axioms project_selectedLeft
#print axioms project_selectedRight
#print axioms project_spectator_selectedLeft
#print axioms project_spectator_selectedRight

end YMGap.Continuum.SU2QuaternionSelectedConditionalTranslation
