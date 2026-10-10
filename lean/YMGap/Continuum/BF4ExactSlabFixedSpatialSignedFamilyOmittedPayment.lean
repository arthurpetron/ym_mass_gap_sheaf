/-
# Signed omitted payment for ORIGINAL spatial plaquette families

The actual whole-family square cap and the SAME interacting variance floor
share the original predecessor mass square. Scaled substitution proves a
division-free comparison, including zero/repeated/signed families. Only a
produced positive bare norm is inverted in the explicit cutoff consumer.
The padded ALL-face unit family supplies that norm from its exact Haar Gram.

The cutoff depends on nome, full width, coefficients and literal family;
it is uniform only in positive terminal depth after these are fixed. The
finite square budget is deliberately coarse, NOT volume-uniform. This pays
the signed omitted term, not cubic/curvature debt, temporal smoothing,
changing-spacing survival, the completed gap or the Clay target.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialRawSourceMassBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect
import YMGap.Continuum.QuaternionHaarFiniteSquareBudget
import YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted
import YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyOmittedPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul channelSource_supported)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_le)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceOmitted)
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm (omittedRate)
open YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted
  (neg_sourceOmitted_le_squareBound)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (SquareBound)
open YMGap.Continuum.QuaternionHaarFiniteSquareBudget (sumCap sumSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect (plaquetteSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergy (signedFamilyOmitted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareGram
  (padded_all_faces_square_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds (predecessorMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
  (sourceFloorScale sourceCapScale sourceFloorScale_positive sourceCapScale_positive
    family_variance_bare_floor)
open YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain (rawSourceMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRawSourceMassBound (rawSourceMass_le_capSquare)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound (rg_qpow_eqv_pow)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks terminalMessage

/-- The existing finite sum compiler retains coefficients, signs and repeats.
This cap is independent of nome/depth/cutoff, NOT of the family size. -/
def familySquareCap (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  sumCap (fun p => (c p*c p)*4) qs

private theorem finite_sum_eq {A : Type} (f : A → RatPoly) :
    ∀ xs : List A, finitePolySum f xs = polySum (xs.map f)
  | [] => rfl
  | a::xs => congrArg (polyAdd (f a)) (finite_sum_eq f xs)

/-- A constructed whole-family square certificate, not an analytic input. -/
def familySquareBound (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    SquareBound (N width) (spatialSpan width c qs) (familySquareCap c qs) := by
  unfold spatialSpan
  rw [finite_sum_eq]
  exact sumSquareBound _ _ qs (fun p _ => (plaquetteSquareBound width p).smul (c p))

theorem familySquareCap_nonnegative (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) : (0 : Q') ≤ familySquareCap c qs :=
  (familySquareBound width c qs).nonnegative

/-- Actual original full-carrier bare norm, NOT the interacting variance. -/
def familyBareNorm (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  H (N width) (polyMul (spatialSpan width c qs) (spatialSpan width c qs))

theorem familyBareNorm_nonnegative (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) : (0 : Q') ≤ familyBareNorm width c qs :=
  (Certificate.square (spatialSpan width c qs) (spatialSpan_supported width c qs)).haar_nonnegative

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width depth : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))

private theorem channelSum_neg (value : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun z => -(value z)) ≈ -(channelSum cs value) :=
  Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => (-1)*value z) cs (fun z _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => value z.2)))
    (Q'.eqv_trans _ _ _ (channelSum_smul value (-1) cs)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => channelSum cs value)))

/-- The signed loss uses the ACTUAL complete family channels, not a sum of
absolute leaf errors or a Wilson-square constant. Includes terminal depth 0. -/
theorem signedFamilyOmitted_le_rawMass {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    -signedFamilyOmitted w K width depth c qs ≤
      (familySquareCap c qs*omittedRate w K)*rawSourceMass w K width depth := by
  let ids := familySpectatorBlocks width qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let cs := productChannels (N width) w K ids
  let value := fun z => H (N width)
    (polyMul (channelSource ids q z) (channelSource ids q z))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq := source_supported w K width depth
  have hs := channelSum_le
    (fun z => -(sourceOmitted (N width-1) w K (channelSource ids q z) f))
    (fun z => (familySquareCap c qs*omittedRate w K)*value z) cs
    (productChannels_nonnegative (N width) hw0 K ids)
    (fun z hz => by
      have hb := channelSource_supported (N width) w K ids
        (familySpectatorBlocks_lt width qs) hq z hz
      have hp := neg_sourceOmitted_le_squareBound (N width-1) hw0 hw1 K
        (channelSource ids q z.2) f (by simpa only [hN] using hb)
        (by simpa only [hN] using familySquareBound width c qs)
      simpa only [hN, value] using hp)
  have he := channelSum_smul value (familySquareCap c qs*omittedRate w K) cs
  have hn := productChannels_familyProject_square_le (N width) hw0 hw1 K ids
    (familySpectatorBlocks_nodup width qs) (familySpectatorBlocks_lt width qs) q hq
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (familySquareCap c qs*omittedRate w K) hn
    (Q'.mul_nonneg _ _ (familySquareCap_nonnegative width c qs)
      (RGTransport.qpow_nonneg w hw0 _))
  have hneg := channelSum_neg
    (fun z => sourceOmitted (N width-1) w K (channelSource ids q z) f) cs
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hneg)
    (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hm))

/-- Shared-predecessor substitution, with NO inverse of source, variance or
bare norm. The zero bare-norm case is only this cleared inequality. -/
theorem signedFamilyOmitted_variance_cleared {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    (sourceFloorScale w width*familyBareNorm width c qs)*
        (-signedFamilyOmitted w K width (n+1) c qs) ≤
      (familySquareCap c qs*sourceCapScale w width*omittedRate w K)*
        (oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1)
          (spatialSpan width c qs)) := by
  let L := sourceFloorScale w width
  let U := sourceCapScale w width
  let B := familyBareNorm width c qs
  let M := familySquareCap c qs
  let rho := omittedRate w K
  let P := predecessorMass w K width n*predecessorMass w K width n
  have hM := familySquareCap_nonnegative width c qs
  have hB := familyBareNorm_nonnegative width c qs
  have hrho : (0 : Q') ≤ rho := RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hL := Q'.le_of_lt (sourceFloorScale_positive hw0 hw1 width)
  have hU := Q'.le_of_lt (sourceCapScale_positive hw0 hw1 width)
  have hraw := Q'.le_trans' _ _ _
    (signedFamilyOmitted_le_rawMass (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K width (n+1) c qs)
    (Q'.mul_le_mul_of_nonneg_left _ _ (M*rho)
      (rawSourceMass_le_capSquare hw0 hw1 K width hK n) (Q'.mul_nonneg _ _ hM hrho))
  have ha := Q'.mul_le_mul_of_nonneg_left _ _ (L*B) hraw (Q'.mul_nonneg _ _ hL hB)
  have hv := Q'.mul_le_mul_of_nonneg_left _ _ (M*U*rho)
    (family_variance_bare_floor hw0 hw1 K width hK n c qs hqs)
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hM hU) hrho)
  have he : (L*B)*((M*rho)*(U*P)) ≈ (M*U*rho)*((L*P)*B) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5))))
      (.mul (.mul (.mul (.var 2) (.var 4)) (.var 3))
        (.mul (.mul (.var 0) (.var 5)) (.var 1))) (by decide)
      (fun | 0 => L | 1 => B | 2 => M | 3 => rho | 4 => U | _ => P)
  exact Q'.le_trans' _ _ _ ha (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hv)

/-- Explicit coefficient; invert only a positive computed bare norm times
the produced floor. No interacting variance or predecessor inverse occurs. -/
def omittedPaymentConstant {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hB : (0 : Q') < familyBareNorm width c qs) : Q' :=
  (familySquareCap c qs*sourceCapScale w width)*
    Q'.recipPos (sourceFloorScale w width*familyBareNorm width c qs)
      (Q'.mul_pos (sourceFloorScale_positive hw0 hw1 width) hB)

theorem omittedPaymentConstant_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hB : (0 : Q') < familyBareNorm width c qs) :
    (0 : Q') ≤ omittedPaymentConstant hw0 hw1 width c qs hB :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (familySquareCap_nonnegative width c qs)
      (Q'.le_of_lt (sourceCapScale_positive hw0 hw1 width)))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem signedFamilyOmitted_le_constant {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)
    (hB : (0 : Q') < familyBareNorm width c qs) :
    -signedFamilyOmitted w K width (n+1) c qs ≤
      (omittedRate w K*omittedPaymentConstant hw0 hw1 width c qs hB)*
        (oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1)
          (spatialSpan width c qs)) := by
  let LB := sourceFloorScale w width*familyBareNorm width c qs
  let a := Q'.recipPos LB (Q'.mul_pos (sourceFloorScale_positive hw0 hw1 width) hB)
  let A := -signedFamilyOmitted w K width (n+1) c qs
  let S := oddMass w K width (n+1)*
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width c qs)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ a
    (signedFamilyOmitted_variance_cleared hw0 hw1 K width hK n c qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hl : (LB*A)*a ≈ A := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ a (Q'.mul_comm_eqv LB A))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A LB a)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv LB _))
        (Q'.mul_one_eqv A)))
  have hr : ((familySquareCap c qs*sourceCapScale w width*omittedRate w K)*S)*a ≈
      (omittedRate w K*omittedPaymentConstant hw0 hw1 width c qs hB)*S :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
      (.mul (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 4))) (.var 3))
      (by decide) (fun
        | 0 => familySquareCap c qs
        | 1 => sourceCapScale w width
        | 2 => omittedRate w K
        | 3 => S
        | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

/-- Explicit cutoff for this fixed original family. No positive-depth argument. -/
def omittedPaymentCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hB : (0 : Q') < familyBareNorm width c qs) (delta : Q') : Nat :=
  max (headCutoff w) (PositiveContractionResidual.geometricCutoff w
    (omittedPaymentConstant hw0 hw1 width c qs hB) delta)

theorem headCutoff_le_omittedPaymentCutoff {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hB : (0 : Q') < familyBareNorm width c qs) (delta : Q') :
    headCutoff w ≤ omittedPaymentCutoff hw0 hw1 width c qs hB delta := Nat.le_max_left _ _

/-- The actual signed omitted loss is paid relative to the SAME interacting
law, at every positive depth using ONE fixed-family cutoff. -/
theorem signedFamilyOmitted_le_variance {w delta : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta) (width : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)
    (hB : (0 : Q') < familyBareNorm width c qs) (K : Nat)
    (hK : omittedPaymentCutoff hw0 hw1 width c qs hB delta ≤ K) (n : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
    (-signedFamilyOmitted w K width (n+1) c qs) ≤
      delta*(oddMass w K width (n+1)*oddVariance hw0 hw1 K width hhead (n+1)
        (spatialSpan width c qs)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
  let D := omittedPaymentConstant hw0 hw1 width c qs hB
  let S := oddMass w K width (n+1)*
    oddVariance hw0 hw1 K width hhead (n+1) (spatialSpan width c qs)
  have hD := omittedPaymentConstant_nonnegative hw0 hw1 width c qs hB
  have hS : (0 : Q') ≤ S := Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (sourceFloorScale_positive hw0 hw1 width))
        (SumOfSquares.q_mul_self_nonneg (predecessorMass w K width n)))
      (familyBareNorm_nonnegative width c qs))
    (family_variance_bare_floor hw0 hw1 K width hhead n c qs hqs)
  have hexp : K ≤ (K+1)*(K+3) := Nat.le_trans (Nat.le_succ K)
    (by simpa using Nat.mul_le_mul_left (K+1) (by omega : 1 ≤ K+3))
  have hp : omittedRate w K ≤ w^K := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (rg_qpow_eqv_pow w _))
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hexp)
  have ht := PositiveContractionResidual.geometric_bound (Q'.le_of_lt hw0) hw1
    hD hdelta K (Nat.le_trans (Nat.le_max_right _ _) hK)
  have hpay := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ D hp hD) ht
  exact Q'.le_trans' _ _ _
    (signedFamilyOmitted_le_constant hw0 hw1 K width hhead n c qs hqs hB)
    (Q'.mul_le_mul_of_nonneg_right _ _ S hpay hS)

attribute [local irreducible] oddMass oddVariance signedFamilyOmitted

/-- Normalize by the SAME positive original odd partition, never by variance. -/
theorem normalized_signedFamilyOmitted_le_variance {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)
    (hB : (0 : Q') < familyBareNorm width c qs) (K : Nat)
    (hK : omittedPaymentCutoff hw0 hw1 width c qs hB delta ≤ K) (n : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
    (-signedFamilyOmitted w K width (n+1) c qs)*
        Q'.recipPos (oddMass w K width (n+1)) (oddMass_positive hw0 hw1 K width hhead (n+1)) ≤
      delta*oddVariance hw0 hw1 K width hhead (n+1) (spatialSpan width c qs) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
  let Z := oddMass w K width (n+1)
  let hZ := oddMass_positive hw0 hw1 K width hhead (n+1)
  let a := Q'.recipPos Z hZ
  let V := oddVariance hw0 hw1 K width hhead (n+1) (spatialSpan width c qs)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ a
    (signedFamilyOmitted_le_variance hw0 hw1 hdelta width c qs hqs hB K hK n)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have he : (delta*(Z*V))*a ≈ delta*V := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
      (fun | 0 => delta | 1 => Z | 2 => V | _ => a))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he)

/-- The actual padded ALL-face candidate produces the nonzero bare norm;
no nonzero-coefficient, interacting-norm or survival hypothesis is added. -/
def allFacesPaymentCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base width : Nat) (hbase : 0 < base) (hwidth : base < width) (delta : Q') : Nat :=
  omittedPaymentCutoff hw0 hw1 width (fun _ => 1) (spatialFaces base)
    (padded_all_faces_square_positive base width hbase (Nat.le_of_lt hwidth)) delta

theorem allFaces_signedFamilyOmitted_le_variance {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    (base width : Nat) (hbase : 0 < base) (hwidth : base < width) (K : Nat)
    (hK : allFacesPaymentCutoff hw0 hw1 base width hbase hwidth delta ≤ K) (n : Nat) :
    let hhead : headCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
    (-signedFamilyOmitted w K width (n+1) (fun _ => 1) (spatialFaces base)) ≤
      delta*(oddMass w K width (n+1)*oddVariance hw0 hw1 K width hhead (n+1)
        (spatialSpan width (fun _ => 1) (spatialFaces base))) :=
  signedFamilyOmitted_le_variance hw0 hw1 hdelta width (fun _ => 1) (spatialFaces base)
    (fun _ hp => spatialFaces_mono (Nat.le_of_lt hwidth) hp)
    (padded_all_faces_square_positive base width hbase (Nat.le_of_lt hwidth)) K hK n

#print axioms familySquareCap
#print axioms familySquareBound
#print axioms familySquareCap_nonnegative
#print axioms familyBareNorm
#print axioms familyBareNorm_nonnegative
#print axioms signedFamilyOmitted_le_rawMass
#print axioms signedFamilyOmitted_variance_cleared
#print axioms omittedPaymentConstant
#print axioms omittedPaymentConstant_nonnegative
#print axioms omittedPaymentCutoff
#print axioms headCutoff_le_omittedPaymentCutoff
#print axioms signedFamilyOmitted_le_variance
#print axioms normalized_signedFamilyOmitted_le_variance
#print axioms allFacesPaymentCutoff
#print axioms allFaces_signedFamilyOmitted_le_variance

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyOmittedPayment
