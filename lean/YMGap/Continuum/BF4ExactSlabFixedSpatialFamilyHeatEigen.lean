/-
# Full-heat eigenimage of an actual signed plaquette family

Every member uses the same fundamental four-link eigenvalue. Finite signed
linearity therefore preserves that eigenvalue for the literal spatial span,
including an empty family and coefficients of either sign.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare (plaquette_fullRange)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap productMap_add productMap_congr)
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- The full original product heat acts by `w^12` on every finite signed
spatial plaquette family whose faces belong to this width. -/
theorem spatialSpan_fullRange (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)
    (w : Q') (K : Nat) (hK : 1 ≤ K) :
    SupportedHaarEqv (N width)
      (productMap (N width) w K (List.range (N width)) (spatialSpan width c qs))
      (polySmul (qpow w 12) (spatialSpan width c qs)) := by
  let P := productMap (N width) w K (List.range (N width))
  let lambda := qpow w 12
  induction qs with
  | nil =>
      change SupportedHaarEqv (N width) (P polyZero) (polySmul lambda polyZero)
      have hz : RatPolyCoeffEqv (P polyZero) polyZero :=
        (productMap_congr (N width) w K (List.range (N width))
          (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
          ((productMap_smul (N width) w K (List.range (N width)) 0 polyOne).trans
            (RatPolyCoeffEqv.zero_smul _))
      exact SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hz)
  | cons p rest ih =>
      let f := characterPolynomial (plaquette width p).scalar 1
      let s := spatialSpan width c rest
      have hp := hqs p List.mem_cons_self
      have hrest : ∀ a, a ∈ rest → a ∈ spatialFaces width :=
        fun a ha => hqs a (List.mem_cons_of_mem p ha)
      have he := plaquette_fullRange width p hp w K hK
      have ht := ih hrest
      have hmap : RatPolyCoeffEqv (P (spatialSpan width c (p::rest)))
          (polyAdd (polySmul (c p) (P f)) (P s)) := by
        change RatPolyCoeffEqv (P (polyAdd (polySmul (c p) f) s)) _
        exact (productMap_add (N width) w K (List.range (N width)) _ _).trans
          ((productMap_smul (N width) w K (List.range (N width)) (c p) f).add
            (RatPolyCoeffEqv.refl _))
      have hleft : SupportedHaarEqv (N width)
          (P (spatialSpan width c (p::rest)))
          (polyAdd (polySmul (c p) (polySmul lambda f)) (polySmul lambda s)) :=
        (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hmap)).trans
          ((he.smul (c p)).add ht)
      have hcomm : RatPolyCoeffEqv
          (polySmul (c p) (polySmul lambda f))
          (polySmul lambda (polySmul (c p) f)) :=
        (RatPolyCoeffEqv.smul_assoc (c p) lambda f).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (c p) lambda) f).trans
            (RatPolyCoeffEqv.smul_assoc lambda (c p) f).symm)
      have hright : RatPolyCoeffEqv
          (polyAdd (polySmul (c p) (polySmul lambda f)) (polySmul lambda s))
          (polySmul lambda (spatialSpan width c (p::rest))) := by
        change RatPolyCoeffEqv _ (polySmul lambda (polyAdd (polySmul (c p) f) s))
        exact (hcomm.add (RatPolyCoeffEqv.refl _)).trans
          (RatPolyCoeffEqv.smul_add lambda (polySmul (c p) f) s).symm
      exact hleft.trans
        (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hright))

#print axioms spatialSpan_fullRange

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen
