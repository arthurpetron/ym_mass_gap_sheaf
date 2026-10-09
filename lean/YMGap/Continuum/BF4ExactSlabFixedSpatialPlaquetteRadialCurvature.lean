/-
# Frozen radial curvature on the literal ORIGINAL spatial plaquette

The selected physical link, original oriented word and all nine ordered
jets are retained. The actual first-gradient norm and frozen Hessian turn
the existing radial and log-discriminant certificates into the full frozen
quadratic form. Its transverse complement is an explicit cross-product
square sum, without division or differentiation of frozen coefficients.

This is the finite Jacobi approximant, NOT the original character prefix.
The latter still needs its actual value/first/mixed deficit and floor budget.
There is no complete spatial-weight, conditional variance or scaling claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteGradient
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.QPolyHaarPairedAtFrozenChain
import YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteGradient
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt pairedDerivativeAt_supported)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain
open YMGap.Continuum.JacobiShiftedPositiveCoefficients (heat)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (SquareBound cap)
open YMGap.Continuum.JacobiHeatRadialProducedBound (nearFlatRadialCap)
open YMGap.Continuum.JacobiProductRadialSignedTail (eighth)

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def crossProduct (u v : Fin 3 → RatPoly) (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd (polyMul (u 1) (v 2)) (polyNeg (polyMul (u 2) (v 1)))
  | 1 => polyAdd (polyMul (u 2) (v 0)) (polyNeg (polyMul (u 0) (v 2)))
  | _ => polyAdd (polyMul (u 0) (v 1)) (polyNeg (polyMul (u 1) (v 0)))

private def sq (e : PolyExpr) : PolyExpr := .mul e e
private def add3 (a b c : PolyExpr) : PolyExpr := .add a (.add b c)
private def sumSq (a b c : PolyExpr) : PolyExpr := add3 (sq a) (sq b) (sq c)
private def dot (a b c x y z : PolyExpr) : PolyExpr := add3 (.mul a x) (.mul b y) (.mul c z)
private def cross (a b : PolyExpr) : PolyExpr := .add a (.neg b)

private theorem lagrange_pin (u v : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (threeSquare u) (threeSquare v))
        (polyNeg (polyMul (threeSum (fun i => polyMul (u i) (v i)))
          (threeSum (fun i => polyMul (u i) (v i))))))
      (threeSquare (crossProduct u v)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (sumSq (.var 0) (.var 1) (.var 2)) (sumSq (.var 3) (.var 4) (.var 5)))
      (.neg (sq (dot (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)))))
    (sumSq (cross (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 4)))
      (cross (.mul (.var 2) (.var 3)) (.mul (.var 0) (.var 5)))
      (cross (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))))
    (by decide) (fun
      | 0 => u 0
      | 1 => u 1
      | 2 => u 2
      | 3 => v 0
      | 4 => v 1
      | _ => v 2)

private theorem cross_supported {blocks : Nat} (u v : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (hv : ∀ i, SupportedQuaternionBlocks blocks (v i))
    (i : Fin 3) : SupportedQuaternionBlocks blocks (crossProduct u v i) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact supported_add (supported_polyMul (hu 1) (hv 2))
      (supported_neg (supported_polyMul (hu 2) (hv 1)))
  · exact supported_add (supported_polyMul (hu 2) (hv 0))
      (supported_neg (supported_polyMul (hu 0) (hv 2)))
  · exact supported_add (supported_polyMul (hu 0) (hv 1))
      (supported_neg (supported_polyMul (hu 1) (hv 0)))

def frozenComplementAt (block : Nat) (u : Fin 3 → RatPoly) (X : RatPoly) : RatPoly :=
  polyAdd (polyMul (threeSquare u) (polyAdd polyOne (polyNeg (polyMul X X))))
    (polyNeg (polyMul (frozenFirstAt block u X) (frozenFirstAt block u X)))

/-- The actual selected-link first jets give the explicit Lagrange complement
on the original face carrier, with arbitrary frozen supported coefficients. -/
def plaquette_frozen_complement_certificate {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (u : Fin 3 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i)) :
    Certificate (N width) (frozenComplementAt ((baseLinks width).idxOf l) u
      (plaquette width face).scalar) := by
  let block := (baseLinks width).idxOf l
  let X := (plaquette width face).scalar
  let v := fun i => pairedDerivativeAt block i X
  have hb : block < N width := List.idxOf_lt_length_of_mem (face_link_mem_base hf hl)
  have hv (i : Fin 3) : SupportedQuaternionBlocks (N width) (v i) :=
    pairedDerivativeAt_supported hb i (plaquette_supported width (N width) (Nat.le_refl _) face).scalar
  have hg : HaarCarrierEqv (N width)
      (polyAdd polyOne (polyNeg (polyMul X X))) (threeSquare v) :=
    (plaquette_paired_gradient_square width face hf l hl).symm
  have hp : HaarCarrierEqv (N width)
      (frozenComplementAt block u X)
      (threeSquare (crossProduct u v)) :=
    (HaarCarrierEqv.add (hg.mul_left (threeSquare u)) (HaarCarrierEqv.refl _ _)).trans
      (RatPolyCoeffEqv.haarCarrier (lagrange_pin u v))
  exact Certificate.transport hp
    ((Certificate.square _ (cross_supported u v hu hv 0)).add
      ((Certificate.square _ (cross_supported u v hu hv 1)).add
        (Certificate.square _ (cross_supported u v hu hv 2))))

/-- Finite Jacobi heat evaluated on the actual oriented plaquette scalar. -/
def plaquetteJacobiHeat (width : Nat) (face : Z4Plaq) (w : Q') (K : Nat) : RatPoly :=
  subst (polyAdd polyOne (plaquette width face).scalar) (heat w K)

def frozenJacobiCurvature (width : Nat) (face : Z4Plaq) (l : Z4Link)
    (w C : Q') (K : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  let h := plaquetteJacobiHeat width face w K
  let block := (baseLinks width).idxOf l
  polyAdd (polyMul (cap C) (polyMul (threeSquare u) (polyMul h h)))
    (polyAdd (polyMul h (frozenSecondAt block u h))
      (polyNeg (polyMul (frozenFirstAt block u h) (frozenFirstAt block u h))))

theorem plaquetteJacobi_first_pin (width : Nat) (face : Z4Plaq) (l : Z4Link)
    (w : Q') (K : Nat) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (frozenFirstAt ((baseLinks width).idxOf l) u (plaquetteJacobiHeat width face w K))
      (polyMul (subst (polyAdd polyOne (plaquette width face).scalar) (pderiv (heat w K)))
        (frozenFirstAt ((baseLinks width).idxOf l) u (plaquette width face).scalar)) :=
  frozenAt_subst_one_add_first _ u _ _

theorem plaquetteJacobi_second_pin {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (w : Q') (K : Nat) (u : Fin 3 → RatPoly) :
    let X := (plaquette width face).scalar
    let hx := subst (polyAdd polyOne X) (pderiv (heat w K))
    let hxx := subst (polyAdd polyOne X) (pderiv (pderiv (heat w K)))
    let d := frozenFirstAt ((baseLinks width).idxOf l) u X
    HaarCarrierEqv (N width)
      (frozenSecondAt ((baseLinks width).idxOf l) u (plaquetteJacobiHeat width face w K))
      (polyAdd (polyMul hxx (polyMul d d))
        (polyNeg (polyMul hx (polyMul (threeSquare u) X)))) := by
  dsimp only
  refine (RatPolyCoeffEqv.haarCarrier (frozenAt_subst_one_add_second _ u _ _)).trans ?_
  refine (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
    ((plaquette_frozen_hessian hf l hl u).mul_left _)).trans ?_
  exact RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1))) (by decide) (fun
        | 0 => subst (polyAdd polyOne (plaquette width face).scalar) (pderiv (heat w K))
        | _ => polyMul (threeSquare u) (plaquette width face).scalar)))

private def curvature_of_radial_certificate {width : Nat} {face : Z4Plaq} {w : Q'}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (C : Q') (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    (radial : Certificate (N width) (subst (plaquette width face).scalar
      (JacobiHeatRadialHaarCertificate.radialPolynomial w K C))) :
    Certificate (N width) (frozenJacobiCurvature width face l w C K u) := by
  let X := (plaquette width face).scalar
  let h := plaquetteJacobiHeat width face w K
  let hx := subst (polyAdd polyOne X) (pderiv (heat w K))
  let hxx := subst (polyAdd polyOne X) (pderiv (pderiv (heat w K)))
  let d := frozenFirstAt ((baseLinks width).idxOf l) u X
  let R := threeSquare u
  let radial' := Certificate.ofCoeff
    (JacobiHeatRadialSubstitutionPin.radial_substitution_pin X w C K).symm radial
  let direction : Certificate (N width) R :=
    (Certificate.square (u 0) (hu 0)).add
      ((Certificate.square (u 1) (hu 1)).add (Certificate.square (u 2) (hu 2)))
  let SX := SquareBound.scalar (plaquette_supported width (N width) (Nat.le_refl _) face)
    (plaquette_unit width (N width) (Nat.le_refl _) face)
  let discriminant := JacobiHeatLogConcavity.heat_logConcavity_certificate hw0 hw1
    (QuaternionHaarSharpCharacterInterval.unitSquareInterval SX) K
  let complement := plaquette_frozen_complement_certificate hf l hl u hu
  have hp := plaquetteJacobi_first_pin width face l w K u
  have hs := plaquetteJacobi_second_pin hf l hl w K u
  have hjet : HaarCarrierEqv (N width) (frozenJacobiCurvature width face l w C K u)
      (polyAdd (polyMul (cap C) (polyMul R (polyMul h h)))
        (polyAdd (polyMul h (polyAdd (polyMul hxx (polyMul d d))
          (polyNeg (polyMul hx (polyMul R X)))))
          (polyNeg (polyMul (polyMul hx d) (polyMul hx d))))) :=
    HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.add (hs.mul_left h)
        (HaarCarrierEqv.neg (RatPolyCoeffEqv.haarCarrier (hp.mul hp))))
  apply Certificate.transport hjet
  exact Certificate.ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 6) (.mul (.var 1) (.var 1))))
        (.add
          (.mul (.var 1) (.add (.mul (.var 3) (.mul (.var 4) (.var 4)))
            (.neg (.mul (.var 2) (.mul (.var 6) (.var 5))))))
          (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 2) (.var 4))))))
      (.add
        (.mul (.var 6)
          (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
            (.add
              (.mul (.add (.const 1) (.neg (.mul (.var 5) (.var 5))))
                (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 2) (.var 2)))))
              (.neg (.mul (.var 5) (.mul (.var 1) (.var 2)))))))
        (.mul
          (.add (.mul (.var 6) (.add (.const 1) (.neg (.mul (.var 5) (.var 5)))))
            (.neg (.mul (.var 4) (.var 4))))
          (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 1) (.var 3))))))
      (by decide) (fun
        | 0 => cap C
        | 1 => h
        | 2 => hx
        | 3 => hxx
        | 4 => d
        | 5 => X
        | _ => R))
    ((direction.mul radial').add (complement.mul discriminant))

/-- Produced full frozen curvature on the SAME original spatial plaquette.
The cost has no width or direction factor, but depends on strict nome and
finite Jacobi cutoff. This is not yet the original character heat prefix. -/
def plaquetteJacobi_frozen_curvature_nearFlat_certificate
    {width : Nat} {face : Z4Plaq} {w delta : Q'}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK1 : 1 ≤ K) (hsmall : HKPos.geoAmp w K ≤ eighth)
    (hdelta : (0 : Q') < delta) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i)) :
    Certificate (N width)
      (frozenJacobiCurvature width face l w (nearFlatRadialCap w K+delta) K u) :=
  curvature_of_radial_certificate hf l hl hw0 hw1 K (nearFlatRadialCap w K+delta) u hu
    (JacobiHeatRadialHaarCertificate.nearFlatRadialCertificate hw0 hw1
      (SquareBound.scalar (plaquette_supported width (N width) (Nat.le_refl _) face)
        (plaquette_unit width (N width) (Nat.le_refl _) face)) K hK1 hsmall hdelta)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature.plaquette_frozen_complement_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature.plaquetteJacobi_first_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature.plaquetteJacobi_second_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature.plaquetteJacobi_frozen_curvature_nearFlat_certificate
