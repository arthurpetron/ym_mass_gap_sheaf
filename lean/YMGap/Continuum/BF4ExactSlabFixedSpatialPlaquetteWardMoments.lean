/-
# Original one-plaquette Ward residual as two character moments

The weight is the COMPLETE original odd marginal V*g_n*g_(n+1), at its
OWN center and original partition. The literal SU(2) curvature and fusion
identities express its differentiated-weight Ward residual exactly:

  variance = 1 + m2 - m1*m1,
  angular  = 4*(3 - m2),
  Ward     = 16*m2 - 12*(m1*m1).

Here m1 and m2 are actual original label-one and label-two character moments,
not bare Haar moments or a replacement heat law. Strictly padded temporal
energy still retains the complete SIGNED Taylor remainder. No moment rate,
remainder bound, scaling family, continuum survival or mass gap is proved.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteWardMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma blockGamma)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularSquare)
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.SU2QuaternionWeightedCasimirWard
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (marginalAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor (varianceRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature (plaquette_gamma)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (plaquette_casimir)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks plaquette marginalWeight

/-- Literal original odd-chain character moment, retaining both terminal
messages and their actual positive partition. -/
def plaquetteMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    (label : Nat) : Q' :=
  middleRatio hw0 hw1 K width hK (n+1) n
    (characterPolynomial (plaquette width face).scalar label)

attribute [local irreducible] oddMass oddVariance

private theorem moment_add {blocks : Nat} (W p q : RatPoly)
    (hZ : (0 : Q') < H blocks W) :
    normalizedMoment blocks W (polyAdd p q) hZ ≈
      normalizedMoment blocks W p hZ + normalizedMoment blocks W q hZ :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (haar_weighted_add blocks W p q))
    (Q'.add_mul_eqv _ _ _)

private theorem moment_smul {blocks : Nat} (W p : RatPoly) (a : Q')
    (hZ : (0 : Q') < H blocks W) :
    normalizedMoment blocks W (polySmul a p) hZ ≈
      a*normalizedMoment blocks W p hZ :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right a W p))
      (quaternionHaar_polySmul blocks a _))) (Q'.mul_assoc_eqv _ _ _)

private theorem moment_neg {blocks : Nat} (W p : RatPoly)
    (hZ : (0 : Q') < H blocks W) :
    normalizedMoment blocks W (polyNeg p) hZ ≈
      -(normalizedMoment blocks W p hZ) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff ((neg_smul p).mul_left W)))
    (Q'.eqv_trans _ _ _ (moment_smul W p (-1) hZ)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => normalizedMoment blocks W p hZ)))

private theorem moment_one {blocks : Nat} (W : RatPoly)
    (hZ : (0 : Q') < H blocks W) :
    normalizedMoment blocks W polyOne hZ ≈ 1 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one W)))
    (Q'.mul_recipPos_eqv _ hZ)

private theorem moment_cap {blocks : Nat} (W : RatPoly) (a : Q')
    (hZ : (0 : Q') < H blocks W) :
    normalizedMoment blocks W (cap a) hZ ≈ a :=
  Q'.eqv_trans _ _ _ (moment_smul W polyOne a hZ)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (moment_one W hZ))
      (Q'.mul_one_eqv a))

private theorem angular_gamma (blocks : Nat) (W f : RatPoly) :
    finSum (fun i => H blocks (polyMul W (blockAngularSquare i f))) blocks ≈
      H blocks (polyMul W (activeGamma (List.range blocks) f f)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (totalEnergy_finSum blocks W f))
    (Q'.eqv_symm (haar_weighted_sum_indexed blocks W
      (fun i => blockGamma i f f) (List.range blocks)))

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private abbrev fundamental (width : Nat) (face : Z4Plaq) : RatPoly :=
  characterPolynomial (plaquette width face).scalar 1

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq)

local notation "f" => fundamental width face
local notation "m1" => plaquetteMoment hw0 hw1 K width hK n face 1
local notation "m2" => plaquetteMoment hw0 hw1 K width hK n face 2

/-- Exact OWN interacting variance; fusion is polynomial algebra, not a
bare-Haar orthogonality replacement. -/
theorem plaquette_variance :
    oddVariance hw0 hw1 K width hK n f ≈ 1+m2+ -(m1*m1) := by
  let W := marginalWeight w K width n
  let hZ := marginalMass_positive hw0 hw1 K width hK n
  have hs : normalizedMoment (N width) W (polyMul f f) hZ ≈ 1+m2 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff
        ((first_character_square (plaquette width face).scalar).mul_left W)))
      (Q'.eqv_trans _ _ _ (moment_add W polyOne
        (characterPolynomial (plaquette width face).scalar 2) hZ)
        (Q'.add_eqv_congr' (moment_one W hZ)
          (marginalMoment_pin hw0 hw1 K width hK n _)))
  have hm := marginalMoment_pin hw0 hw1 K width hK n f
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (marginalVariance_pin hw0 hw1 K width hK n f))
    (Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
        (Q'.mul_eqv_congr_left _ _ _ hm))))

/-- Original angular cost is the label-two character deficit. -/
theorem plaquette_angular (hf : face ∈ spatialFaces width) :
    normalizedAngular hw0 hw1 K width hK n f ≈ 4*(3-m2) := by
  let W := marginalWeight w K width n
  let hZ := marginalMass_positive hw0 hw1 K width hK n
  have hs : normalizedMoment (N width) W (polyMul f f) hZ ≈ 1+m2 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff
        ((first_character_square (plaquette width face).scalar).mul_left W)))
      (Q'.eqv_trans _ _ _ (moment_add W polyOne
        (characterPolynomial (plaquette width face).scalar 2) hZ)
        (Q'.add_eqv_congr' (moment_one W hZ)
          (marginalMoment_pin hw0 hw1 K width hK n _)))
  have hr : normalizedMoment (N width) W
      (activeGamma (List.range (N width)) f f) hZ ≈ 4*(3-m2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (plaquette_gamma width face hf W))
      (Q'.eqv_trans _ _ _ (moment_smul W _ 4 hZ)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _
          (Q'.eqv_trans _ _ _ (moment_add W (cap 4) (polyNeg (polyMul f f)) hZ)
            (Q'.add_eqv_congr' (moment_cap W 4 hZ)
              (Q'.eqv_trans _ _ _ (moment_neg W (polyMul f f) hZ)
                (Q'.neg_eqv_congr _ _ hs)))))
          (poly_identity_of_normal_eq
            (.mul (.const 4) (.add (.const 4) (.neg (.add (.const 1) (.var 0)))))
            (.mul (.const 4) (.add (.const 3) (.neg (.var 0))))
            (by decide) (fun _ => m2))))
  have ha : marginalAngular w K width n f ≈
      H (N width) (polyMul W (activeGamma (List.range (N width)) f f)) :=
    angular_gamma (N width) W f
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.recipPos_eqv_congr _ _ (oddMass_positive hw0 hw1 K width hK n)
        hZ (marginalMass_pin w K width n).symm)) hr)

/-- The COMPLETE differentiated-weight residual is exactly determined by
two original moments. Its sign is not assumed. -/
theorem plaquette_ward (hf : face ∈ spatialFaces width) :
    normalizedWardResidual hw0 hw1 K width hK n f ≈
      16*m2+ -(12*(m1*m1)) := by
  let W := marginalWeight w K width n
  let hZ := marginalMass_positive hw0 hw1 K width hK n
  let z := oddMass w K width n
  let r := Q'.recipPos z (oddMass_positive hw0 hw1 K width hK n)
  have hraw := complete_ward_own_mean (baseLinks_positive width) W f hZ 12
    (plaquette_casimir width face hf)
  have ha : totalEnergy (N width) W f ≈ marginalAngular w K width n f :=
    totalEnergy_finSum (N width) W f
  have hnorm : normalizedAngular hw0 hw1 K width hK n f +
      normalizedWardResidual hw0 hw1 K width hK n f ≈
        12*oddVariance hw0 hw1 K width hK n f := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ r)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha.symm (Q'.eqv_refl _)) hraw)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left 12 _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (marginalMass_pin w K width n))
        (Q'.mul_eqv_congr_left _ _ _ (marginalVariance_pin hw0 hw1 K width hK n f))))) ?_
    exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.const 12) (.mul (.var 0) (.var 1))) (.var 2))
      (.mul (.mul (.const 12) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => z | 1 => oddVariance hw0 hw1 K width hK n f | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv z (oddMass_positive hw0 hw1 K width hK n)))
        (Q'.mul_one_eqv _))
  have hs : 4*(3-m2)+normalizedWardResidual hw0 hw1 K width hK n f ≈
      12*(1+m2+ -(m1*m1)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (plaquette_angular hw0 hw1 K width hK n face hf).symm
        (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ hnorm
        (Q'.mul_eqv_congr_left 12 _ _ (plaquette_variance hw0 hw1 K width hK n face)))
  have hsub := Q'.add_eqv_congr_right _ _ (-(4*(3-m2))) hs
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (poly_identity_of_normal_eq
    (.add (.add (.mul (.const 4) (.add (.const 3) (.neg (.var 0)))) (.var 1))
      (.neg (.mul (.const 4) (.add (.const 3) (.neg (.var 0)))))) (.var 1)
    (by decide) (fun | 0 => m2 | _ => normalizedWardResidual hw0 hw1 K width hK n f)))
    (Q'.eqv_trans _ _ _ hsub (poly_identity_of_normal_eq
      (.add (.mul (.const 12) (.add (.add (.const 1) (.var 0))
        (.neg (.mul (.var 1) (.var 1)))))
        (.neg (.mul (.const 4) (.add (.const 3) (.neg (.var 0))))))
      (.add (.mul (.const 16) (.var 0))
        (.neg (.mul (.const 12) (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => m2 | _ => m1)))

/-- Strict padding puts this two-moment calculation on the actual temporal
energy. The SAME signed Taylor remainder is retained, not estimated. -/
theorem padded_plaquette_energy {base : Nat} (hwidth : base < width)
    (hf : face ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n f ≈
      ((1 : Q')-w)*(4*(3-m2)) + normalizedRemainder hw0 hw1 K width hK n f := by
  have hp : SupportedQuaternionBlocks (N width) f :=
    SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  exact Q'.eqv_trans _ _ _
    (normalizedEnergy_taylor hw0 hw1 K width hK n f hp (baseLinks_positive width)
      (plaquette_fringe_independent_after_padding hwidth face hf))
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _
      (plaquette_angular hw0 hw1 K width hK n face
        (spatialFaces_mono (Nat.le_of_lt hwidth) hf))) (Q'.eqv_refl _))

/-- The variance-rebased correction likewise has no unevaluated weight
derivative left. This is an equality, not a smallness or sign assertion. -/
theorem plaquette_variance_remainder (hf : face ∈ spatialFaces width) :
    varianceRemainder hw0 hw1 K width hK n f ≈
      normalizedRemainder hw0 hw1 K width hK n f +
        -(((1 : Q')-w)*(16*m2+ -(12*(m1*m1)))) :=
  Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
      (plaquette_ward hw0 hw1 K width hK n face hf)))

#print axioms plaquetteMoment
#print axioms plaquette_variance
#print axioms plaquette_angular
#print axioms plaquette_ward
#print axioms padded_plaquette_energy
#print axioms plaquette_variance_remainder

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteWardMoments
