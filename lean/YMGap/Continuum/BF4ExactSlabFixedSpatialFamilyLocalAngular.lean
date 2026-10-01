/-
# Local angular cost of a complete signed spatial family

Distinct literal faces meet each physical link at most six times. Local
finite Cauchy therefore pays coefficient squares, not the whole family size.
The SAME arbitrary positive Haar weight remains in every cross term. For
the original odd marginal the four-link Gamma identity makes the budget
24*sum c_p^2*(4-E_odd[f_p^2]). The actual Taylor energy consumes this bound
with its COMPLETE signed remainder, including the angular-weight defect.

This is not a comparison with the signed family's interacting variance,
a sign bound on that remainder, or a physical continuum scaling estimate.
Repeated faces require consolidation before applying the Nodup statement.
-/

import YMGap.Continuum.QuaternionHaarLocalAngularFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
import YMGap.Continuum.QuaternionHaarNormalizedMomentLinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalAngular

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma blockGamma)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_smul)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence (normalizedMoment_congr)
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarLocalAngularFamily
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature (plaquette_gamma)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar (weighted_gamma_finSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks plaquette marginalWeight

private theorem six_congr {a b : Nat → Nat → RatPoly}
    (h : ∀ i j, RatPolyCoeffEqv (a i j) (b i j)) :
    RatPolyCoeffEqv (six a) (six b) := by
  unfold six
  exact (h 0 1).add ((h 0 2).add ((h 0 3).add
    ((h 1 2).add ((h 1 3).add (h 2 3)))))

private theorem gamma_smul (active : List Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (activeGamma active (polySmul c p) (polySmul c p))
      (polySmul (c*c) (activeGamma active p p)) := by
  have hb (b : Nat) :
      RatPolyCoeffEqv (blockGamma b (polySmul c p) (polySmul c p))
        (polySmul (c*c) (blockGamma b p p)) := by
    unfold blockGamma
    apply RatPolyCoeffEqv.trans (six_congr (fun i j => ?_)) (six_smul _ _)
    have hd := angularDerivative_smul (4*b+i) (4*b+j) c p
    exact (hd.mul hd).trans
      ((RatPolyCoeffEqv.polyMul_smul_left c _ _).trans
        (((RatPolyCoeffEqv.polyMul_smul_right c _ _).smul c).trans
          (RatPolyCoeffEqv.smul_assoc c c _)))
  induction active with
  | nil => exact (RatPolyCoeffEqv.smul_zero (c*c)).symm
  | cons b rest ih =>
      exact ((hb b).add ih).trans (RatPolyCoeffEqv.smul_add (c*c) _ _).symm

private theorem qsum_times {I : Type} (xs : List I) (f : I → Q') (r : Q') :
    qListSum (xs.map f)*r ≈ qListSum (xs.map fun i => f i*r) := by
  induction xs with
  | nil => exact Q'.zero_mul_eqv r
  | cons i rest ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)

private theorem normalized_carrier {n : Nat} {W p q : RatPoly}
    (hW : (0 : Q') < quaternionHaar n W) (h : HaarCarrierEqv n p q) :
    normalizedMoment n W p hW ≈ normalizedMoment n W q hW :=
  Q'.mul_eqv_congr_right _ _ _ (h W)

/-- Local row Cauchy under ONE arbitrary positive weight. The complete signed
Gamma remains on the left, including every overlapping-face cross term. -/
theorem weighted_spatial_family_angular (width : Nat) (W : RatPoly)
    (R : Certificate (N width) W) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hnd : qs.Nodup) :
    quaternionHaar (N width) (polyMul W
      (activeGamma (List.range (N width)) (spatialSpan width c qs) (spatialSpan width c qs))) ≤
      6*qListSum (qs.map fun p => quaternionHaar (N width) (polyMul W
        (activeGamma (List.range (N width))
          (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1))
          (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1))))) := by
  apply weighted_finitePolySum_activeGamma_local_family
    (N width) 6 W R (List.range (N width))
    (fun b hb => List.mem_range.mp hb) qs
    (fun p => polySmul (c p) (characterPolynomial (plaquette width p).scalar 1))
    (blockRow width)
  · intro p _
    exact supported_smul
      (character_supported (plaquette_supported width (N width) (Nat.le_refl _) p).scalar 1) (c p)
  · intro b _
    exact blockRowFaces_length_le_six width b qs hnd
  · intro b hb p _ hoff i j hi hj
    exact (angularDerivative_smul (4*b+i) (4*b+j) (c p) _).trans
      (((blockRow_derivative_zero width b p (List.mem_range.mp hb) hoff hi hj).smul (c p)).trans
        (RatPolyCoeffEqv.smul_zero (c p)))

private theorem scaled_face_moment (width : Nat) (W : RatPoly)
    (hW : (0 : Q') < quaternionHaar (N width) W)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) (c : Q') :
    normalizedMoment (N width) W
      (activeGamma (List.range (N width))
        (polySmul c (characterPolynomial (plaquette width p).scalar 1))
        (polySmul c (characterPolynomial (plaquette width p).scalar 1))) hW ≈
      4*(c*c*normalizedMoment (N width) W
        (polyAdd (cap 4) (polyNeg (polyMul
          (characterPolynomial (plaquette width p).scalar 1)
          (characterPolynomial (plaquette width p).scalar 1)))) hW) := by
  let f := characterPolynomial (plaquette width p).scalar 1
  let gap := polyAdd (cap 4) (polyNeg (polyMul f f))
  have hpoly : HaarCarrierEqv (N width)
      (activeGamma (List.range (N width)) (polySmul c f) (polySmul c f))
      (polySmul (c*c*4) gap) :=
    (RatPolyCoeffEqv.haarCarrier (gamma_smul _ c f)).trans
      ((HaarCarrierEqv.smul (c*c) (plaquette_gamma width p hp)).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_assoc (c*c) 4 gap)))
  exact Q'.eqv_trans _ _ _ (normalized_carrier hW hpoly)
    (Q'.eqv_trans _ _ _ (normalizedMoment_smul hW)
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 0)) (.const 4)) (.var 1))
        (.mul (.const 4) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
        (by decide) (fun | 0 => c | _ => normalizedMoment (N width) W gap hW)))

/-- The local bound retains the SAME interacting weight and the actual
individual face deficits. Its constant is independent of family size and width. -/
theorem normalized_spatial_family_angular (width : Nat) (W : RatPoly)
    (R : Certificate (N width) W) (hW : (0 : Q') < quaternionHaar (N width) W)
    (qs : List Z4Plaq) (c : Z4Plaq → Q') (hnd : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    normalizedMoment (N width) W
      (activeGamma (List.range (N width)) (spatialSpan width c qs) (spatialSpan width c qs)) hW ≤
      24*qListSum (qs.map fun p => c p*c p*normalizedMoment (N width) W
        (polyAdd (cap 4) (polyNeg (polyMul
          (characterPolynomial (plaquette width p).scalar 1)
          (characterPolynomial (plaquette width p).scalar 1)))) hW) := by
  let M := fun p => quaternionHaar (N width) (polyMul W
    (activeGamma (List.range (N width))
      (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1))
      (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1))))
  let D := fun p => c p*c p*normalizedMoment (N width) W
    (polyAdd (cap 4) (polyNeg (polyMul
      (characterPolynomial (plaquette width p).scalar 1)
      (characterPolynomial (plaquette width p).scalar 1)))) hW
  let r := Q'.recipPos (quaternionHaar (N width) W) hW
  have h := Q'.mul_le_mul_of_nonneg_right _ _ r
    (weighted_spatial_family_angular width W R qs c hnd)
    (Q'.le_of_lt (Q'.recipPos_pos _ hW))
  have hs : qListSum (qs.map fun p => M p*r) ≈ qListSum (qs.map fun p => 4*D p) :=
    qListSum_congr qs _ _ (fun p hp => scaled_face_moment width W hW p (hqs p hp) (c p))
  have hright : (6*qListSum (qs.map M))*r ≈ 24*qListSum (qs.map D) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (qsum_times qs M r)
          (Q'.eqv_trans _ _ _ hs (qListSum_scale qs D 4))))
        (poly_identity_of_normal_eq (.mul (.const 6) (.mul (.const 4) (.var 0)))
          (.mul (.const 24) (.var 0)) (by decide) (fun _ => qListSum (qs.map D))))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright)

/-- Explicit original odd-law budget; no beta, spacing or source convergence
is hidden in the number 24 or in a supplied constant. -/
def localAngularBudget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q') : Q' :=
  24*qListSum (qs.map fun p => c p*c p*(4+
    -(middleRatio hw0 hw1 K width hK (n+1) n (polyMul
      (characterPolynomial (plaquette width p).scalar 1)
      (characterPolynomial (plaquette width p).scalar 1)))))

private theorem marginal_gap_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    normalizedMoment (N width) (marginalWeight w K width n)
      (polyAdd (cap 4) (polyNeg (polyMul f f)))
      (marginalMass_positive hw0 hw1 K width hK n) ≈
      4+ -(middleRatio hw0 hw1 K width hK (n+1) n (polyMul f f)) := by
  let hW := marginalMass_positive hw0 hw1 K width hK n
  have hcap : normalizedMoment (N width) (marginalWeight w K width n) (cap 4) hW ≈ 4 :=
    Q'.eqv_trans _ _ _ (normalizedMoment_smul hW)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (normalizedMoment_one hW))
        (Q'.mul_one_eqv _))
  have hneg : normalizedMoment (N width) (marginalWeight w K width n)
      (polyNeg (polyMul f f)) hW ≈
      -(middleRatio hw0 hw1 K width hK (n+1) n (polyMul f f)) :=
    Q'.eqv_trans _ _ _ (normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl _)
      (neg_smul (polyMul f f)))
      (Q'.eqv_trans _ _ _ (normalizedMoment_smul hW)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (marginalMoment_pin hw0 hw1 K width hK n (polyMul f f)))
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
            (.neg (.var 0)) (by decide) (fun _ =>
              middleRatio hw0 hw1 K width hK (n+1) n (polyMul f f)))))
  exact Q'.eqv_trans _ _ _ (normalizedMoment_add hW) (Q'.add_eqv_congr' hcap hneg)

/-- Actual original-marginal instance, not a supplied source comparison.
No inverse source floor, exterior-volume cap, or mean approximation appears. -/
theorem family_normalized_angular_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hnd : qs.Nodup) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    normalizedAngular hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      localAngularBudget hw0 hw1 K width hK n qs c := by
  let W := marginalWeight w K width n
  let f := spatialSpan width c qs
  let hW := marginalMass_positive hw0 hw1 K width hK n
  have h := normalized_spatial_family_angular width W
    (marginalCertificate hw0 hw1 K width hK n) hW qs c hnd hqs
  have hleft : normalizedMoment (N width) W
      (activeGamma (List.range (N width)) f f) hW ≈
      normalizedAngular hw0 hw1 K width hK n f :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (weighted_gamma_finSum (N width) W f))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _ hW
        (oddMass_positive hw0 hw1 K width hK n) (marginalMass_pin w K width n)))
  have hright :
      24*qListSum (qs.map fun p => c p*c p*normalizedMoment (N width) W
        (polyAdd (cap 4) (polyNeg (polyMul
          (characterPolynomial (plaquette width p).scalar 1)
          (characterPolynomial (plaquette width p).scalar 1)))) hW) ≈
        localAngularBudget hw0 hw1 K width hK n qs c := Q'.mul_eqv_congr_left 24 _ _
    (qListSum_congr qs _ _ (fun p _ => Q'.mul_eqv_congr_left _ _ _
      (marginal_gap_pin hw0 hw1 K width hK n
        (characterPolynomial (plaquette width p).scalar 1))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

/-- The SAME-variance Ward identity retains its signed correction. This is
a lower comparison with the local budget, not an assertion of either sign. -/
theorem family_ward_local_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hnd : qs.Nodup) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    12*oddVariance hw0 hw1 K width hK n (spatialSpan width c qs) +
        -(localAngularBudget hw0 hw1 K width hK n qs c) ≤
      normalizedWardResidual hw0 hw1 K width hK n (spatialSpan width c qs) := by
  let A := normalizedAngular hw0 hw1 K width hK n (spatialSpan width c qs)
  let R := normalizedWardResidual hw0 hw1 K width hK n (spatialSpan width c qs)
  let C := localAngularBudget hw0 hw1 K width hK n qs c
  have h := Q'.add_le_add
    (Q'.add_le_add (family_normalized_angular_le hw0 hw1 K width hK n qs c hnd hqs)
      (Q'.le_of_eqv (Q'.eqv_refl R))) (Q'.le_of_eqv (Q'.eqv_refl (-C)))
  have hleft := Q'.add_eqv_congr'
    (family_normalized_ward hw0 hw1 K width hK n qs c hqs) (Q'.eqv_refl (-C))
  have hright : (C+R)+ -C ≈ R :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => C | _ => R)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

/-- Causal consumer on the unchanged ORIGINAL temporal energy. Every signed
Taylor term and the angular-weight change remain in normalizedRemainder. -/
theorem padded_family_energy_local_angular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q') (hnd : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      ((1 : Q')-w)*localAngularBudget hw0 hw1 K width hK n qs c +
        normalizedRemainder hw0 hw1 K width hK n (spatialSpan width c qs) := by
  have hb := family_normalized_angular_le hw0 hw1 K width hK n qs c hnd
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hh : (0 : Q') ≤ (1 : Q')-w := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (padded_family_normalized_taylor hw0 hw1 K hwidth hK n qs c hqs))
    (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ _ hb hh)
      (Q'.le_of_eqv (Q'.eqv_refl _)))

#print axioms weighted_spatial_family_angular
#print axioms normalized_spatial_family_angular
#print axioms localAngularBudget
#print axioms family_normalized_angular_le
#print axioms family_ward_local_budget
#print axioms padded_family_energy_local_angular

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalAngular
