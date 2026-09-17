/-
# The original width-one terminal marginal and an actual fringe source test

At depth zero the original terminal T1 equals one under every supported
Haar test. Consequently the original odd marginal agrees with the FULL
three-face spatial weight, not with Haar, under arbitrary supported tests.
The active coordinate probe has original mean zero and squared norm 1/4.

Move the two preceding projections and the fringe fluctuation onto an
adapted tester. Its actual source pairing then becomes a single full-action
moment. No conditional density, inverse polynomial, heat factor or source
is replaced coefficientwise. The coordinate probe is not gauge-invariant;
these are finite tests of the existing arbitrary-supported-polynomial
producer, not a physical spectral-gap or continuum result.
-/

import YMGap.Continuum.BF4ExactSlabWidthOneGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope

namespace YMGap.Continuum.BF4ExactSlabWidthOneSource

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt activeBlocks_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight
  (activeSpatialWeight activeSpatialFaces spatialWeight_haar_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer (activeTransfer original_transfer_haar_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
  (mass centeredObservable centeredObservable_supported source piece)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul
    quaternionBlockIndependent_polyVar_of_distinctBlock)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productMap productMap_congr productMap_pairing productHeat_upper_marginal)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
  (project fluctuation project_fixed project_selfAdjoint)
open YMGap.Continuum.SU2QuaternionHaarBlockTelescope (term)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

local notation "N" => List.length (baseLinks 1)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight

private theorem coeff_haar {blocks : Nat} {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    SupportedHaarEqv blocks p q := fun i _ => haar_of_coeff (h.mul_left i)

private theorem independent_one (i : Nat) : QuaternionBlockIndependent i polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  rfl

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem subtract_zero {A B : Q'} (h : B ≈ 0) : A + -B ≈ A :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ h))
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0)
      (by decide) (fun _ => A))

/-- The scalar of the original origin x2 link (numeric block four). -/
def probe : RatPoly := polyVar 16

theorem probe_supported : SupportedQuaternionBlocks N probe :=
  (QuaternionHaarUnitScalarSquare.Supported.coordinate (blocks := N) (block := 4)
    (by rw [baseLinks_length]; decide)).scalar

theorem probe_independent (i : Nat) (hi : i ≠ 4) : QuaternionBlockIndependent i probe :=
  quaternionBlockIndependent_polyVar_of_distinctBlock (source := 4) (target := i)
    (component := 0) (Ne.symm hi) (by decide)

theorem probe_fringe_independent (i : Nat) (hi : i ∈ fringeBlocks 1) :
    QuaternionBlockIndependent i probe := by
  apply probe_independent i
  intro he
  exact ((fringeBlocks_mem_iff 1 i).mp hi).2 (he.symm ▸ probe_active)

theorem probe_haar : quaternionHaar N probe ≈ 0 := by
  rw [baseLinks_length]
  decide

theorem probe_haar_square : quaternionHaar N (polyMul probe probe) ≈ Q'.mkPos 1 4 (by decide) := by
  rw [baseLinks_length]
  decide

variable (w : Q') (K : Nat)

theorem active_weight_one : activeSpatialWeight w K 1 = polyOne := by
  unfold activeSpatialWeight
  rw [activeSpatialFaces_one]
  rfl

/-- The original one-step terminal is one under every supported test.
This does not identify its free-polynomial coefficients with one. -/
theorem terminal_one : SupportedHaarEqv N (terminalMessage w K 1 1) polyOne := by
  rw [← terminalMessage_next w K 1 0]
  change SupportedHaarEqv N (transferStep w K 1 polyOne) polyOne
  intro p hp
  have hactive : RatPolyCoeffEqv (activeTransfer w K 1 polyOne)
      (productMap N w K (activeBlocks 1) polyOne) := by
    unfold activeTransfer
    rw [active_weight_one]
    exact productMap_congr N w K (activeBlocks 1) (RatPolyCoeffEqv.one_mul polyOne)
  have hm := productHeat_upper_marginal N w K (activeBlocks 1)
    (activeBlocks_nodup 1) (activeBlocks_lt 1) p hp
  exact Q'.eqv_trans _ _ _
    (original_transfer_haar_active w K 1 (supported_one N) (fun i _ => independent_one i) hp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hactive.mul_left p))
      (Q'.eqv_trans _ _ _ (productMap_pairing N w K (activeBlocks 1) polyOne p)
        (Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.one_mul (liftBoundary N p)).mul_left _))
          (Q'.eqv_trans _ _ _ hm (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))))))

/-- The FULL original three-face action remains in every depth-zero pairing. -/
theorem marginal_haar : SupportedHaarEqv N (marginalWeight w K 1 0) (spatialWeight w K 1) := by
  have hleft : RatPolyCoeffEqv (marginalWeight w K 1 0)
      (polyMul (spatialWeight w K 1) (terminalMessage w K 1 1)) :=
    (RatPolyCoeffEqv.mul_one (spatialWeight w K 1)).mul_right _
  exact (coeff_haar hleft).trans
    (((SupportedHaarEqv.refl N (spatialWeight w K 1)).mul (terminal_one w K)
      (by exact BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_supported w K 1 1)
      (spatialWeight_supported w K 1)).trans (coeff_haar (RatPolyCoeffEqv.mul_one _)))

/-- Only active insertions admit the further removal of the spatial packet. -/
theorem marginal_mean_active {f : RatPoly} (hf : SupportedQuaternionBlocks N f)
    (hi : ∀ i, i ∈ fringeBlocks 1 → QuaternionBlockIndependent i f) :
    quaternionHaar N (polyMul (marginalWeight w K 1 0) f) ≈ quaternionHaar N f := by
  have h := spatialWeight_haar_active w K 1 f hf hi
  rw [active_weight_one] at h
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (marginal_haar w K f hf)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _ h (haar_of_coeff (RatPolyCoeffEqv.one_mul f)))))

theorem mass_one : mass w K 1 0 ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
    (Q'.eqv_trans _ _ _
      (marginal_mean_active w K (supported_one N) (fun i _ => independent_one i)) (haar_one N))

theorem probe_mean_zero : quaternionHaar N (polyMul (marginalWeight w K 1 0) probe) ≈ 0 :=
  Q'.eqv_trans _ _ _ (marginal_mean_active w K probe_supported probe_fringe_independent) probe_haar

theorem probe_norm : marginalPair w K 1 0 probe probe ≈ Q'.mkPos 1 4 (by decide) :=
  Q'.eqv_trans _ _ _ (marginal_mean_active w K (supported_polyMul probe_supported probe_supported)
    (fun i hi => quaternionBlockIndependent_polyMul
      (probe_fringe_independent i hi) (probe_fringe_independent i hi))) probe_haar_square

/-- Original partition-cleared centering fixes this actual zero-mean probe. -/
theorem centered_probe : RatPolyCoeffEqv (centeredObservable w K 1 0 probe) probe := by
  have hm := (RatPolyCoeffEqv.smul_coefficient (mass_one w K) probe).trans (RatPolyCoeffEqv.one_smul probe)
  have hz : RatPolyCoeffEqv (cap (quaternionHaar N (polyMul (marginalWeight w K 1 0) probe))) polyZero :=
    (RatPolyCoeffEqv.smul_coefficient (probe_mean_zero w K) polyOne).trans (RatPolyCoeffEqv.zero_smul polyOne)
  exact (hm.add (RatPolyCoeffEqv.neg hz)).trans (RatPolyCoeffEqv.add_zero probe)

theorem source_haar : SupportedHaarEqv N (source w K 1 0 probe) (polyMul (spatialWeight w K 1) probe) :=
  (marginal_haar w K).mul (coeff_haar (centered_probe w K))
    (centeredObservable_supported w K 1 0 probe_supported) (spatialWeight_supported w K 1)

private theorem term_two_test (blocks : Nat) (hb : 2 < blocks) (s r : RatPoly)
    (h0 : QuaternionBlockIndependent 0 r) (h1 : QuaternionBlockIndependent 1 r)
    (h2 : RatPolyCoeffEqv (project 2 r) polyZero) :
    quaternionHaar blocks (polyMul (term 2 s) r) ≈ quaternionHaar blocks (polyMul s r) := by
  let u := project 1 (project 0 s)
  have hp (i : Nat) (hi : i < blocks) (a : RatPoly) (h : QuaternionBlockIndependent i r) :
      quaternionHaar blocks (polyMul (project i a) r) ≈ quaternionHaar blocks (polyMul a r) :=
    Q'.eqv_trans _ _ _ (project_selfAdjoint blocks i hi a r)
      (haar_of_coeff ((project_fixed i r h).mul_left a))
  have hz : quaternionHaar blocks (polyMul (project 2 u) r) ≈ 0 :=
    Q'.eqv_trans _ _ _ (project_selfAdjoint blocks 2 hb u r)
      (haar_of_coeff ((h2.mul_left u).trans (RatPolyCoeffEqv.mul_zero_right u)))
  have he : RatPolyCoeffEqv (polyMul (term 2 s) r)
      (polyAdd (polyMul u r) (polyNeg (polyMul (project 2 u) r))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) (by decide)
      (fun | 0 => u | 1 => project 2 u | _ => r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks _))
        (Q'.eqv_trans _ _ _ (subtract_zero hz)
          (Q'.eqv_trans _ _ _ (hp 1 (by omega) (project 0 s) h1) (hp 0 (by omega) s h0)))))

/-- An adapted tester sees the actual early fringe source through ONE
full-action moment; there is no need to construct its conditional density. -/
theorem piece_test (r : RatPoly) (hr : SupportedQuaternionBlocks N r)
    (h0 : QuaternionBlockIndependent 0 r) (h1 : QuaternionBlockIndependent 1 r)
    (h2 : RatPolyCoeffEqv (project 2 r) polyZero) :
    quaternionHaar N (polyMul (piece w K 1 0 2 probe) r) ≈
      quaternionHaar N (polyMul (polyMul (spatialWeight w K 1) probe) r) :=
  Q'.eqv_trans _ _ _ (term_two_test N (by rw [baseLinks_length]; decide) _ r h0 h1 h2)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (source_haar w K r hr) (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

end YMGap.Continuum.BF4ExactSlabWidthOneSource

#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe_supported
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe_independent
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe_fringe_independent
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe_haar
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe_haar_square
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.active_weight_one
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.terminal_one
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.marginal_haar
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.marginal_mean_active
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.mass_one
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.probe_norm
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.centered_probe
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.source_haar
#print axioms YMGap.Continuum.BF4ExactSlabWidthOneSource.piece_test
