/-
# Original signed slab form on its retained crossing-link boundary

Integrate only the interior links of each complete heat-dressed observable.
The explicit schedules keep the original coordinate numbering. The remaining
polynomials are supported on the same carrier and depend only on the actual
crossing-link boundary. The SAME original signed bilinear is their Haar
pairing against the literal relative heat interface.

This finite identity neither identifies these auxiliary polynomials as
original observables nor constructs time composition, normalization,
vacuum stationarity, centered decay, or a physical spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabCrossingBoundary
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal

namespace YMGap.Continuum.BF4ExactSlabBoundaryMarginal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (lowerObservable)
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (lowerObservable_support)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (haar_of_coeff_eqv)
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity (lowerObservable_local)
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabCrossingBoundary
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (integrateQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))
local infix:50 " ≈ " => Q'.eqv

/-- The finite list of nonboundary blocks on a specified literal slab side. -/
def interiorSchedule (half : Nat) (side : CrossPlaneSide) : List Nat :=
  (List.range (blocks half)).filter fun b => decide
    (linkHalfSide half (correctedSlabLinkAt (centralExtent half) b) = side ∧
      correctedSlabLinkAt (centralExtent half) b ∉ boundaryLinks half)

theorem mem_interiorSchedule (half b : Nat) (side : CrossPlaneSide) :
    b ∈ interiorSchedule half side ↔ b < (blocks half) ∧
      linkHalfSide half (correctedSlabLinkAt (centralExtent half) b) = side ∧
      ¬ BoundaryBlock half b := by
  simp only [interiorSchedule, List.mem_filter, List.mem_range, decide_eq_true_eq, BoundaryBlock]

def lowerMarginal (w : Q') (K half : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  integrateQuaternionBlocks (interiorSchedule half .lower) (lowerObservable w K half c)

def upperMarginal (w : Q') (K half : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  integrateQuaternionBlocks (interiorSchedule half .upper)
    (reflectCorrectedSlabPolynomial (centralExtent half) (lowerObservable w K half c))

private theorem local_mono {n : Nat} {a b : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal n a p) (h : ∀ i, a i → b i) : BlockLocal n b p :=
  fun t ht i hi hn => hp t ht i hi (fun ha => hn (h i ha))

private theorem marginal_local {half : Nat} {side : CrossPlaneSide} {p : RatPoly}
    (hp : BlockLocal (blocks half)
      (fun b => linkHalfSide half (correctedSlabLinkAt (centralExtent half) b) = side) p) :
    BoundaryLocal half (integrateQuaternionBlocks (interiorSchedule half side) p) := by
  have h := integrateBlocks_local (interiorSchedule half side) hp
  intro t ht b hb hn
  exact h t ht b hb (fun ha => ha.2 ((mem_interiorSchedule half b side).mpr ⟨hb, ha.1, hn⟩))

theorem lowerMarginal_local (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    BoundaryLocal half (lowerMarginal w K half c) :=
  marginal_local (lowerObservable_local w K half c)

theorem upperMarginal_local (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    BoundaryLocal half (upperMarginal w K half c) :=
  marginal_local (lower_reflection_upper (lowerObservable_local w K half c))

theorem lowerMarginal_supported (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    SupportedQuaternionBlocks (blocks half) (lowerMarginal w K half c) :=
  integrateBlocks_supported _ (lowerObservable_support w K half c)

theorem upperMarginal_supported (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    SupportedQuaternionBlocks (blocks half) (upperMarginal w K half c) :=
  integrateBlocks_supported _ (reflectCorrectedSlabPolynomial_support (centralExtent half) _)

/-- Both full observables are marginalized only where the OTHER factors are
proved independent. In particular, the interface is never omitted. -/
theorem exact_bilinear_eq_boundaryHaar {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right
      (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (blocks half)
        (polyMul (lowerMarginal w K half left)
          (polyMul (relativeInterface w K half) (upperMarginal w K half right))) := by
  let L := lowerObservable w K half left
  let R := reflectCorrectedSlabPolynomial (centralExtent half) (lowerObservable w K half right)
  let I := relativeInterface w K half
  let LM := lowerMarginal w K half left
  let RM := upperMarginal w K half right
  have hi : BoundaryLocal half I := relativeInterface_local w K half
  have hr : BlockLocal (blocks half) (UpperBlock half) R :=
    lower_reflection_upper (lowerObservable_local w K half right)
  have hIR : BlockLocal (blocks half) (fun b => BoundaryBlock half b ∨ UpperBlock half b)
      (polyMul I R) :=
    (local_mono hi (fun _ => Or.inl)).mul (local_mono hr (fun _ => Or.inr))
  have hleft : quaternionHaar (blocks half) (polyMul (polyMul I R) L) ≈
      quaternionHaar (blocks half) (polyMul (polyMul I R) LM) := by
    apply quaternionHaar_polyMul_eq_after_integratingBlocks_of_local hIR
    intro b hb
    have hs := (mem_interiorSchedule half b .lower).mp hb
    refine ⟨hs.1, ?_⟩
    intro ha
    rcases ha with ha | ha
    · exact hs.2.2 ha
    · change linkHalfSide half (correctedSlabLinkAt (centralExtent half) b) = .upper at ha
      have he := hs.2.1.symm.trans ha
      cases he
  have hright : quaternionHaar (blocks half) (polyMul (polyMul LM I) R) ≈
      quaternionHaar (blocks half) (polyMul (polyMul LM I) RM) := by
    apply quaternionHaar_polyMul_eq_after_integratingBlocks_of_local
      ((lowerMarginal_local w K half left).mul hi)
    intro b hb
    have hs := (mem_interiorSchedule half b .upper).mp hb
    exact ⟨hs.1, hs.2.2⟩
  exact Q'.eqv_trans _ _ _ (exact_bilinear_eq_relativeHaar hw K half left right)
    (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (RatPolyCoeffEqv.mul_comm L (polyMul I R)))
      (Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
          ((RatPolyCoeffEqv.mul_comm (polyMul I R) LM).trans
            (RatPolyCoeffEqv.mul_assoc LM I R).symm))
          (Q'.eqv_trans _ _ _ hright
            (haar_of_coeff_eqv _ (RatPolyCoeffEqv.mul_assoc LM I RM))))))

end YMGap.Continuum.BF4ExactSlabBoundaryMarginal

#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.interiorSchedule
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.mem_interiorSchedule
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.lowerMarginal
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.upperMarginal
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.lowerMarginal_local
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.upperMarginal_local
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.lowerMarginal_supported
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.upperMarginal_supported
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryMarginal.exact_bilinear_eq_boundaryHaar
