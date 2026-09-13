/-
# ORIGINAL finite boundary decay as the smaller slab grows around the probe

The proved exterior separation and actual-core size floor are substituted
into the original summed boundary determinant estimate. A single plaquette
probe has a fully constructed carrier, yielding

  |D_K| <= 2*c*amplitude(w)*s(w)^margin * F_K(1)*I_K(1),

where s(w)=625*rho(w)<1. Both amplitude and rate are explicit rational data
with no cutoff, smaller-slab size, outer padding or position parameter.
At w=1/1024 every coupling guard is supplied by a proved certificate.

The shrinking coefficient is for the existing determinant with its two
ORIGINAL unit moments still multiplied in. No transport of this inequality
to normalized CReal limits, thermodynamic completion, stationary transfer,
physical spectral gap or continuum theory is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
import YMGap.Continuum.BF4ExactSlabUniformCoreBudget

namespace YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabActiveCoreCount
open YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def singlePlaquetteBudget (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (margin : Nat) : Q' :=
  probePrefactor w hd 4 * tailBudget 1250 625 margin (adjustedCoreRate w hd) hs

def singlePlaquetteAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) : Q' :=
  (probePrefactor w hd 4 * Q'.ofNat 1250) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs)

theorem singleton_budget_pin (q : Z4Plaq) (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (margin : Nat) :
    summedBoundaryBudget (singletonCarrier q) w hd hs margin = singlePlaquetteBudget w hd hs margin := by
  have he : (edgesOf q).length = 4 := rfl
  have hc : countPrefactor (singletonCarrier q) = 1250 := by
    change 2^1 * 625^1 = 1250
    decide
  unfold summedBoundaryBudget singlePlaquetteBudget
  rw [he, hc]

theorem singlePlaquetteBudget_factor (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (margin : Nat) :
    singlePlaquetteBudget w hd hs margin ≈
      singlePlaquetteAmplitude w hd hs * (entropyRate 625 (adjustedCoreRate w hd))^margin := by
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun i => if i = 0 then probePrefactor w hd 4 else if i = 1 then Q'.ofNat 1250
      else if i = 2 then (entropyRate 625 (adjustedCoreRate w hd))^margin
      else Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs))

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
include hw0 hw1 hsmall hd hs

theorem protected_boundary_bound (K half padding margin : Nat) (observable : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length observable c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal (centralExtent (half+padding)) links observable)
    (hr : ProtectedRoot half padding margin probe.animal.root) :
    Q'.abs (boundaryNumerator w half padding observable K) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs (margin+1-probe.animal.support.length)) *
        (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  boundaryNumerator_tail_bound hw0 hw1 hsmall hd hs K half padding observable c P links probe hl _
    (fun _ ha => protected_root_core_size_floor probe hr ha)

theorem shifted_base_boundary_bound (K base margin padding : Nat) (baseFace : Z4Plaq)
    (hp : baseFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (observable : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length observable c)
    (links : List Z4Link) (probe : ProbeCarrier links)
    (hl : LinkLocal (centralExtent ((base+margin)+padding)) links observable)
    (hroot : probe.animal.root = shiftFace (margin+padding) (margin+padding) baseFace) :
    Q'.abs (boundaryNumerator w (base+margin) padding observable K) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs (margin+1-probe.animal.support.length)) *
        (fullMoment w K (base+margin) padding polyOne * interiorSequence w (base+margin) padding polyOne K) :=
  protected_boundary_bound hw0 hw1 hsmall hd hs K (base+margin) padding margin observable c P links probe hl
    (hroot.symm ▸ shifted_base_protected hp margin padding)

/-- Fully constructed singleton carrier: no geometric hypothesis remains beyond physical placement. -/
theorem singlePlaquette_boundary_bound (K base margin padding : Nat) (baseFace : Z4Plaq)
    (hp : baseFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (observable : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length observable c)
    (hl : LinkLocal (centralExtent ((base+margin)+padding))
      (edgesOf (shiftFace (margin+padding) (margin+padding) baseFace)) observable) :
    Q'.abs (boundaryNumerator w (base+margin) padding observable K) ≤
      ((c+c)*singlePlaquetteBudget w hd hs margin) *
        (fullMoment w K (base+margin) padding polyOne * interiorSequence w (base+margin) padding polyOne K) := by
  let q := shiftFace (margin+padding) (margin+padding) baseFace
  have h := shifted_base_boundary_bound hw0 hw1 hsmall hd hs K base margin padding baseFace hp observable c P
    (edgesOf q) (singletonCarrier q) hl rfl
  have hm : margin+1-(singletonCarrier q).animal.support.length = margin := Nat.add_sub_cancel margin 1
  rw [hm, singleton_budget_pin] at h
  exact h

/-- Explicit geometric coefficient, uniform in K, base size, position and outer padding. -/
theorem singlePlaquette_boundary_geometric_bound (K base margin padding : Nat) (baseFace : Z4Plaq)
    (hp : baseFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (observable : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length observable c)
    (hl : LinkLocal (centralExtent ((base+margin)+padding))
      (edgesOf (shiftFace (margin+padding) (margin+padding) baseFace)) observable) :
    Q'.abs (boundaryNumerator w (base+margin) padding observable K) ≤
      (((c+c)*singlePlaquetteAmplitude w hd hs) * (entropyRate 625 (adjustedCoreRate w hd))^margin) *
        (fullMoment w K (base+margin) padding polyOne * interiorSequence w (base+margin) padding polyOne K) :=
  Q'.le_trans' _ _ _ (singlePlaquette_boundary_bound hw0 hw1 hsmall hd hs K base margin padding baseFace hp observable c P hl)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c+c) _ _ (singlePlaquetteBudget_factor w hd hs margin))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

end SmallNome

theorem existingNome_singlePlaquette_boundary_bound (K base margin padding : Nat) (baseFace : Z4Plaq)
    (hp : baseFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (observable : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length observable c)
    (hl : LinkLocal (centralExtent ((base+margin)+padding))
      (edgesOf (shiftFace (margin+padding) (margin+padding) baseFace)) observable) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    Q'.abs (boundaryNumerator w (base+margin) padding observable K) ≤
      (((c+c)*singlePlaquetteAmplitude w hd hs) * (entropyRate 625 (adjustedCoreRate w hd))^margin) *
        (fullMoment w K (base+margin) padding polyOne * interiorSequence w (base+margin) padding polyOne K) :=
  singlePlaquette_boundary_geometric_bound (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos)
    (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one)
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2 K base margin padding baseFace hp observable c P hl

end YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay

#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.singlePlaquetteBudget
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.singlePlaquetteAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.singleton_budget_pin
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.singlePlaquetteBudget_factor
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.protected_boundary_bound
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.shifted_base_boundary_bound
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.singlePlaquette_boundary_bound
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.singlePlaquette_boundary_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay.existingNome_singlePlaquette_boundary_bound
