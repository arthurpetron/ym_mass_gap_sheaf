/-
# Whole signed-family response versus the SAME original variance

One common spectator band gives a strictly positive response fraction for
the complete signed plaquette family, including every cross term. The source
is the original unprojected V*u_(n+1), and its odd marginal is at depth n+1.
The fraction depends only on nome and family-list size, not width, late
cutoff, positive terminal depth or signed coefficients.

This is finite SAME-variance control, not a spacing-small energy ceiling:
the local floor can deteriorate as the nome approaches one. No justified
physical trajectory, continuum survival or physical mass claim follows.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalBand
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
import YMGap.Continuum.SU2QuaternionProductHeatBandResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
import YMGap.Continuum.SU2QuaternionProductHeatSourceCentering

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages (PaddedPolynomialCoeffEqv)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment sourceEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatBandResponse
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (terminalMessage_next oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
  (energy energy_identity edgeDensity edgeDensity_supported jump jump_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (energy_source_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalBand
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage energy edgeDensity

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ k : Nat, (0 : Q') < qpow w k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos (qpow_positive hw k) hw

/-- No fringe projection or independence premise is needed for this original
endpoint moment identity. The insertion and full terminal messages are kept. -/
theorem oddMoment_unprojected_source (w : Q') (K width depth : Nat) (p : RatPoly) :
    H width (polyMul (marginalWeight w K width depth) p) ≈
      sourceMoment (N width) w K (activeBlocks width)
        (endpointSource w K width (terminalMessage w K width depth)) p := by
  have ht : productMap (N width) w K (activeBlocks width)
      (endpointSource w K width (terminalMessage w K width depth)) =
      terminalMessage w K width (depth+1) :=
    (transferStep_eq_productMap w K width (terminalMessage w K width depth)).symm.trans
      (terminalMessage_next w K width depth)
  unfold sourceMoment
  rw [ht]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => endpointSource w K width (terminalMessage w K width depth)
         | 1 => terminalMessage w K width (depth+1) | _ => p))

/-- Original active-source centered moment, with the actual marginal mean. -/
theorem centered_unprojected_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let q := endpointSource w K width (terminalMessage w K width depth)
    let psi := oddCentered hw0 hw1 K width hK depth f
    sourceMoment (N width) w K (activeBlocks width) q (polyMul psi psi) ≈
      oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  let W := marginalWeight w K width depth
  let z := H width W
  let hz := marginalMass_positive hw0 hw1 K width hK depth
  let r := Q'.recipPos z hz
  let psi := oddCentered hw0 hw1 K width hK depth f
  let v := oddVariance hw0 hw1 K width hK depth f
  let A := H width (polyMul W (polyMul psi psi))
  have hpin := oddMoment_unprojected_source w K width depth (polyMul psi psi)
  have hown : A*r ≈ v := Q'.eqv_trans _ _ _
    (own_mean_pin (marginalCertificate hw0 hw1 K width hK depth) hf hz)
    (marginalVariance_pin hw0 hw1 K width hK depth f)
  have hcancel : (A*r)*z ≈ A :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A r z)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_comm_eqv r z))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv z hz))
          (Q'.mul_one_eqv A)))
  have hraw : A ≈ z*v :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z hown)
        (Q'.mul_comm_eqv v z))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hpin)
    (Q'.eqv_trans _ _ _ hraw
      (Q'.mul_eqv_congr_right _ _ v (marginalMass_pin w K width depth)))

/-- Centering leaves the original temporal energy unchanged. Its two-slice
jump is compared on the same padded Haar carrier, without dropping factors. -/
theorem energy_shifted (w : Q') (K width : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (c : Q') :
    energy w K width g (shifted f c) ≈ energy w K width g f := by
  have hs := shifted_supported hf c
  have hj : PaddedPolynomialCoeffEqv (N width+N width)
      (jump width (shifted f c)) (jump width f) :=
    SU2QuaternionProductHeatSourceCentering.jump_shifted (N width) f c
  have hboth : PaddedPolynomialCoeffEqv (N width+N width)
      (polyMul (jump width (shifted f c)) (jump width (shifted f c)))
      (polyMul (jump width f) (jump width f)) := hj.mul hj
  have hjump : quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g)
        (polyMul (jump width (shifted f c)) (jump width (shifted f c)))) ≈
      quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width g) (polyMul (jump width f) (jump width f))) :=
    hboth.haar_insert
      (supported_polyMul (jump_supported width hs) (jump_supported width hs))
      (supported_polyMul (jump_supported width hf) (jump_supported width hf))
      (edgeDensity w K width g) (edgeDensity_supported w K width hg)
  have h2 : (2 : Q')*energy w K width g (shifted f c) ≈
      (2 : Q')*energy w K width g f :=
    Q'.eqv_trans _ _ _ (energy_identity w K width hg hs)
    (Q'.eqv_trans _ _ _ hjump (Q'.eqv_symm (energy_identity w K width hg hf)))
  let half := Q'.mkPos 1 2 (by decide)
  have hhalf : half*(2 : Q') ≈ 1 := by decide
  have half_two (a : Q') : half * ((2 : Q')*a) ≈ a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half 2 a))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a hhalf) (Q'.one_mul_eqv a))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (half_two _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.mkPos 1 2 (by decide)) _ _ h2)
      (half_two _))

/-- Positive response coefficient. This is explicit finite data depending
only on nome and the family list size, not an asserted physical rate. -/
def familyResponseFraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) : Q' :=
  (qpow w 12 * (localLower w (4*size) * localLower w (4*size))) *
    Q'.recipPos (localUpper w (4*size) * localUpper w (4*size))
      (Q'.mul_pos (localUpper_positive hw0 hw1 _) (localUpper_positive hw0 hw1 _))

theorem familyResponseFraction_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < familyResponseFraction hw0 hw1 size :=
  Q'.mul_pos (Q'.mul_pos (qpow_positive hw0 12)
    (Q'.mul_pos (localLower_positive hw0 hw1 _) (localLower_positive hw0 hw1 _)))
    (Q'.recipPos_pos _ _)

/-- Cleared SAME-variance ceiling for the entire signed family. Both scalar
coefficients are independent of width, late cutoff and positive depth. -/
theorem padded_family_energy_band_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K)
    {base width : Nat} (hwidth : base < width) (n : Nat)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (c : Z4Plaq → Q') :
    let f := spatialSpan width c qs
    let M := oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f
    let l := localLower w (4*qs.length)
    let u := localUpper w (4*qs.length)
    (u*u)*energy w K width (terminalMessage w K width (n+1)) f +
      (qpow w 12*(l*l))*M ≤ (u*u)*M := by
  dsimp only
  let f := spatialSpan width c qs
  let g := terminalMessage w K width (n+1)
  let q := endpointSource w K width g
  let R := familySpectator w K width n qs
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  let center := normalizedMoment (N width) (marginalWeight w K width (n+1)) f
    (marginalMass_positive hw0 hw1 K width hK (n+1))
  let psi := shifted f center
  let A := sourceMoment (N width) w K (activeBlocks width) q (polyMul psi psi)
  let B := kineticPair (N width) w K (activeBlocks width) (polyMul q psi) (polyMul q psi)
  let M := oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f
  have hf := spatialSpan_supported width c qs
  have hg := terminalMessage_supported w K width (n+1)
  have hq := supported_polyMul (spatialWeight_supported w K width) hg
  have Q := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK (n+1))
  have hsize : (familyLinks qs).length ≤ 4*qs.length :=
    Nat.le_of_eq (familyLinks_length qs)
  have hr := response_band_cleared hw0 hw1 K hK (activeBlocks width)
    (activeBlocks_lt width) hq (familySpectator_supported w K width n qs) hf Q
    (familySpectator_certificate hw0 hw1 K width hK n qs) (qpow w 12) l u center
    (qpow_positive hw0 12)
    (HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 12)
    (Q'.le_of_lt (localLower_positive hw0 hw1 _))
    (Q'.le_of_lt (localUpper_positive hw0 hw1 _))
    (endpoint_localLowerCertificate hw0 hw1 K width hK n (familyLinks qs) _ hsize)
    (endpoint_localUpperCertificate hw0 hw1 K width hK n (familyLinks qs) _ hsize)
    (family_spectator_kinetic hwidth qs hqs c w K hK1 n)
    (family_spectator_zero hwidth qs hqs c w K n)
  have hpin : A ≈ M := centered_unprojected_square hw0 hw1 K width hK (n+1) hf
  have hE : energy w K width g f ≈ A + -B :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (energy_shifted w K width hg hf center))
      (energy_source_pin w K width g psi)
  have hclear : (u*u)*(A + -B) + (qpow w 12*(l*l))*A ≤ (u*u)*A := by
    have h := Q'.add_le_add_left ((u*u)*(A + -B)) _ _ hr
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (.mul (.var 0) (.var 2)))
        (.mul (.var 0) (.var 1)) (by decide)
        (fun | 0 => u*u | 1 => A | _ => B)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (u*u) _ _ hE)
      (Q'.mul_eqv_congr_left (qpow w 12*(l*l)) _ _ (Q'.eqv_symm hpin))))
    (Q'.le_trans' _ _ _ hclear (Q'.le_of_eqv (Q'.mul_eqv_congr_left (u*u) _ _ hpin)))

/-- Divide only by the explicit positive scalar band cap, never by a source
or its variance. This coefficient is below one but need not tend to zero on
any physical scaling trajectory. -/
theorem padded_family_energy_band {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K)
    {base width : Nat} (hwidth : base < width) (n : Nat)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (c : Z4Plaq → Q') :
    let f := spatialSpan width c qs
    energy w K width (terminalMessage w K width (n+1)) f ≤
      (1-familyResponseFraction hw0 hw1 qs.length) *
        (oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let f := spatialSpan width c qs
  let E := energy w K width (terminalMessage w K width (n+1)) f
  let M := oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  let A := qpow w 12*(l*l)
  let U := u*u
  let hU := Q'.mul_pos (localUpper_positive hw0 hw1 (4*qs.length))
    (localUpper_positive hw0 hw1 (4*qs.length))
  let r := Q'.recipPos U hU
  let delta := A*r
  have hUr : r*U ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv r U)
    (Q'.mul_recipPos_eqv U hU)
  have hclear : U*E+A*M ≤ U*M :=
    padded_family_energy_band_cleared hw0 hw1 K hK hK1 hwidth n qs hqs c
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ r hclear
    (Q'.le_of_lt (Q'.recipPos_pos U hU))
  have hleft : r*(U*E+A*M) ≈ E+delta*M :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 3) (.var 0)) (.var 4)))
      (by decide) (fun | 0 => r | 1 => U | 2 => E | 3 => A | _ => M))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ E hUr) (Q'.one_mul_eqv E))
        (Q'.eqv_refl _))
  have hright : r*(U*M) ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r U M))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ M hUr) (Q'.one_mul_eqv M))
  have hbudget : E+delta*M ≤ M :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  have hnonneg := Q'.sub_nonneg_of_le hbudget
  have he : M + -(E+delta*M) ≈ (1-delta)*M + -E :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.mul (.var 2) (.var 0)))))
      (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0)) (.neg (.var 1)))
      (by decide) (fun | 0 => M | 1 => E | _ => delta)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv he))

#print axioms oddMoment_unprojected_source
#print axioms centered_unprojected_square
#print axioms energy_shifted
#print axioms familyResponseFraction
#print axioms familyResponseFraction_positive
#print axioms padded_family_energy_band_cleared
#print axioms padded_family_energy_band

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
