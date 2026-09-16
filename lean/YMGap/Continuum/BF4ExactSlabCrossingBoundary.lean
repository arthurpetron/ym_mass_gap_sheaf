/-
# The literal crossing-link boundary of the original signed slab form

Retain the lower spatial link of every actual crossing face and its literal
reflected link. The relative heat interface is local to precisely this
displayed boundary list; repeated links do not impose independence.
The original signed bilinear is pinned to this interface with both complete
heat-dressed observables retained. No interior marginal, time composition,
centered contraction or continuum limit is assumed here.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
import YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate

namespace YMGap.Continuum.BF4ExactSlabCrossingBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (lowerObservable)
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity (interfacePolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (haar_of_carrier)
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))
local infix:50 " ≈ " => Q'.eqv

/-- Actual link list, independent of the heat cutoff or observable. -/
def boundaryLinks (half : Nat) : List Z4Link :=
  (centralFixedFaceIds half).flatMap fun id =>
    let link := faceLinkA (slabPlaquetteAt (centralExtent half) id)
    [link, timeReflectLink (centralExtent half) link]

def BoundaryBlock (half block : Nat) : Prop :=
  correctedSlabLinkAt (centralExtent half) block ∈ boundaryLinks half

def BoundaryLocal (half : Nat) (p : RatPoly) : Prop :=
  BlockLocal (blocks half) (BoundaryBlock half) p

private structure LocalQuaternion (half : Nat) (p : PolyQuaternion) : Prop where
  scalar : BoundaryLocal half p.scalar
  iPart : BoundaryLocal half p.iPart
  jPart : BoundaryLocal half p.jPart
  kPart : BoundaryLocal half p.kPart

private theorem quaternion_one (half : Nat) : LocalQuaternion half PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LocalQuaternion.conj {half : Nat} {p : PolyQuaternion} (h : LocalQuaternion half p) :
    LocalQuaternion half (PolyQuaternion.conj p) := ⟨h.scalar, h.iPart.neg, h.jPart.neg, h.kPart.neg⟩

private theorem LocalQuaternion.mul {half : Nat} {p q : PolyQuaternion}
    (hp : LocalQuaternion half p) (hq : LocalQuaternion half q) : LocalQuaternion half (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem link_local {half : Nat} {link : Z4Link} (hb : link ∈ boundaryLinks half) :
    LocalQuaternion half (correctedSlabLinkPolynomial (centralExtent half) link) := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks (centralExtent half)
  · have hc (c : Nat) (h : c < 4) : BoundaryLocal half
        (polyVar (4 * (boundaryCompleteSlabLinks (centralExtent half)).idxOf link + c)) := by
      apply BlockLocal.coordinate
      unfold BoundaryBlock
      rw [show (4 * (boundaryCompleteSlabLinks (centralExtent half)).idxOf link + c) / 4 =
        (boundaryCompleteSlabLinks (centralExtent half)).idxOf link by omega, correctedSlabLinkAt_idxOf hl]
      exact hb
    rw [correctedSlabLinkPolynomial_of_mem hl]
    exact ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    exact quaternion_one half

theorem crossing_links_mem {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    faceLinkA (slabPlaquetteAt (centralExtent half) id) ∈ boundaryLinks half ∧
    timeReflectLink (centralExtent half) (faceLinkA (slabPlaquetteAt (centralExtent half) id)) ∈ boundaryLinks half := by
  constructor <;> apply List.mem_flatMap.mpr
  · exact ⟨id, hi, by simp⟩
  · exact ⟨id, hi, by simp⟩

def relativeFaceHeat (w : Q') (K half id : Nat) : RatPoly :=
  heatPrefix w K (spatialWord (centralExtent half)
    (faceLinkA (slabPlaquetteAt (centralExtent half) id))).scalar

def relativeInterface (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (relativeFaceHeat w K half) (centralFixedFaceIds half)

theorem relativeFace_local (w : Q') (K : Nat) {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    BoundaryLocal half (relativeFaceHeat w K half id) := by
  have hm := crossing_links_mem hi
  have hs := (LocalQuaternion.mul (link_local hm.1) (link_local hm.2).conj).scalar
  apply BlockLocal.finiteSum
  intro spin _
  exact (hs.character spin).smul _

theorem relativeInterface_local (w : Q') (K half : Nat) :
    BoundaryLocal half (relativeInterface w K half) :=
  BlockLocal.fold _ _ (fun _ hi => relativeFace_local w K hi)

private theorem product_pin (w : Q') (K half : Nat) : ∀ ids : List Nat,
    HaarCarrierEqv (blocks half)
      (polynomialProduct (BF4ExactSlabAllExtentSpatialGramPositivity.faceHeatPolynomial w K half) ids)
      (polynomialProduct (relativeFaceHeat w K half) ids)
  | [] => .refl _ _
  | id::ids => QuaternionHaarCarrierEqv.mul (faceHeat_pin w K half id) (product_pin w K half ids)

/-- Equality under every Haar insertion, not just equality of partition values. -/
theorem interface_relative_pin (w : Q') (K half : Nat) :
    HaarCarrierEqv (blocks half) (interfacePolynomial w K half) (relativeInterface w K half) :=
  product_pin w K half (centralFixedFaceIds half)

/-- The SAME original signed bilinear on literal boundary coordinates. -/
theorem exact_bilinear_eq_relativeHaar {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (blocks half)
        (polyMul (lowerObservable w K half left)
          (polyMul (relativeInterface w K half)
            (reflectCorrectedSlabPolynomial (centralExtent half) (lowerObservable w K half right)))) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_reflectedHaar hw K half left right)
    (haar_of_carrier (QuaternionHaarCarrierEqv.mul (.refl _ _)
      (QuaternionHaarCarrierEqv.mul (interface_relative_pin w K half) (.refl _ _))))

end YMGap.Continuum.BF4ExactSlabCrossingBoundary

#print axioms YMGap.Continuum.BF4ExactSlabCrossingBoundary.boundaryLinks
#print axioms YMGap.Continuum.BF4ExactSlabCrossingBoundary.crossing_links_mem
#print axioms YMGap.Continuum.BF4ExactSlabCrossingBoundary.relativeFace_local
#print axioms YMGap.Continuum.BF4ExactSlabCrossingBoundary.relativeInterface_local
#print axioms YMGap.Continuum.BF4ExactSlabCrossingBoundary.interface_relative_pin
#print axioms YMGap.Continuum.BF4ExactSlabCrossingBoundary.exact_bilinear_eq_relativeHaar
