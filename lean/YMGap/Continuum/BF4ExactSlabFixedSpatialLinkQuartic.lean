/-
# Quartic chordal moment of an original active physical link

The selected heat-prefix quartic estimate is transported to the literal
lower/upper quaternion link difference in the unchanged original edge
density. Both endpoint sources, all spectator heat factors, and the odd
partition remain the same. This is a one-link estimate; no word-level
quartic or interacting variance bound follows by itself.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialQuarticMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion OrientedBF4Link)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison (selectedInsertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialQuarticMoment
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt heatAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (edgeWeight eraseIndex select_perm heatAt_eq_prefix)
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion (defect)
open YMGap.Continuum.SU2QuaternionHeatQuarticBound (quarticBudget)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarChordalDifference
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarWordDifference (difference)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
  (haarNorm_coordinate polyQuaternionNorm_conj)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks

/-- A physical lower oriented edge is supported on the doubled original
slice carrier. -/
theorem lower_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    Supported (N width+N width) (orientedLink width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width)
      (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf e.link)) :=
    Supported.coordinate (by omega)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact hs.conj
  · exact hs

/-- The corresponding upper oriented edge is supported on the same carrier. -/
theorem upper_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    Supported (N width+N width) (upperOriented width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width)
      (PolyQuaternion.coordinateVariable (N width+(baseLinks width).idxOf e.link)) :=
    Supported.coordinate (by omega)
  unfold upperOriented
  split
  · exact hs.conj
  · exact hs

/-- The actual lower link has unit quaternion norm on the Haar carrier. -/
theorem lower_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (orientedLink width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : (baseLinks width).idxOf e.link < N width+N width)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

/-- The actual upper link has unit quaternion norm on the Haar carrier. -/
theorem upper_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (upperOriented width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : N width+(baseLinks width).idxOf e.link < N width+N width)
  unfold upperOriented
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

private theorem chordal_defect {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width)
      (polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e)))
      (defect (scalarAt (N width+(baseLinks width).idxOf e.link)
        ((baseLinks width).idxOf e.link))) := by
  let i := (baseLinks width).idxOf e.link
  have hi := List.idxOf_lt_length_of_mem he
  have hl := haarNorm_coordinate (by omega : i < N width+N width)
  have hu := haarNorm_coordinate (by omega : N width+i < N width+N width)
  have hbase := norm_difference_character hl hu
  unfold orientedLink link upperOriented
  rw [if_pos he]
  split
  · have hc := RatPolyCoeffEqv.haarCarrier (blocks := N width+N width)
      (norm_difference_conj (PolyQuaternion.coordinateVariable i)
        (PolyQuaternion.coordinateVariable (N width+i)))
    exact hc.trans hbase
  · exact hbase

private theorem selected_edge_pin (w : Q') (K width depth i : Nat)
    (hi : i ∈ activeBlocks width) (p : RatPoly) :
    selectedInsertion w K width depth i
      (polyMul p (heatPrefix w K (scalarAt (N width+i) i))) ≈
      quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width (terminalMessage w K width depth)) p) := by
  let a := endpointSource w K width (terminalMessage w K width depth)
  let W := productHeat (N width) w K (eraseIndex i (activeBlocks width))
  let H := heatPrefix w K (scalarAt (N width+i) i)
  have hprod : RatPolyCoeffEqv (productHeat (N width) w K (activeBlocks width))
      (polyMul H W) := by
    have hp := polynomialProduct_perm (fun j => heatAt j (N width+j) w K) (select_perm i hi)
    have hh := (heatAt_symm i (N width+i) w K).mul_right W
    rw [heatAt_eq_prefix (N width+i) i w K] at hh
    exact hp.trans hh
  have hedge : RatPolyCoeffEqv (edgeWeight (N width) w K (activeBlocks width) a)
      (polyMul (polyMul W (polyMul a (liftBoundary (N width) a))) H) :=
    ((hprod.mul_right a).mul_right (liftBoundary (N width) a)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 3))) (.var 0)) (by decide)
        (fun | 0 => H | 1 => W | 2 => a | _ => liftBoundary (N width) a))
  have hp : edgeWeight (N width) w K (activeBlocks width) a =
      edgeDensity w K width (terminalMessage w K width depth) := by
    unfold edgeWeight edgeDensity productHeat
    rw [kineticWeight_eq_indexedProduct]
    rfl
  rw [hp] at hedge
  have hcomm : RatPolyCoeffEqv
      (polyMul (polyMul W (polyMul a (liftBoundary (N width) a))) (polyMul p H))
      (polyMul (polyMul (polyMul W (polyMul a (liftBoundary (N width) a))) H) p) :=
    ((RatPolyCoeffEqv.mul_comm p H).mul_left _).trans
      ((RatPolyCoeffEqv.mul_assoc _ H p).symm)
  -- The selected heat factor is reinserted into the original edge density.
  unfold selectedInsertion
  change quaternionHaar (N width+N width)
    (polyMul (polyMul W (polyMul a (liftBoundary (N width) a))) (polyMul p H)) ≈ _
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hcomm)
    (haar_of_coeff (hedge.symm.mul_right p))

/-- The literal original-edge quartic chordal moment of any active physical
link is paid by the SAME odd partition. Every finite-cutoff guard is explicit. -/
theorem selected_quartic_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S K width depth : Nat) (hS : 1 ≤ S) (hK : S+3 ≤ K)
    (hhead : headCutoff w ≤ K)
    (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide))
    (e : OrientedBF4Link) (he : e.link ∈ baseLinks width)
    (hi : (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (polyMul
          (polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e)))
          (polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e))))) ≤
      quarticBudget w S * oddMass w K width depth := by
  let i := (baseLinks width).idxOf e.link
  let D := polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e))
  let d := defect (scalarAt (N width+i) i)
  let H := heatPrefix w K (scalarAt (N width+i) i)
  have hc : HaarCarrierEqv (N width+N width) D d := chordal_defect he
  have hmass := BF4ExactSlabFixedSpatialQuarticMoment.selected_quartic_bound
    hw0 hw1 S K width depth i hS hK hhead hi hhalf hq
  have hpin := selected_edge_pin w K width depth i hi (polyMul d d)
  have hreplace : HaarCarrierEqv (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth)) (polyMul D D))
      (polyMul (edgeDensity w K width (terminalMessage w K width depth)) (polyMul d d)) :=
    HaarCarrierEqv.mul_left _ (HaarCarrierEqv.mul hc hc)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (haar_of_carrier hreplace) (Q'.eqv_symm hpin))) hmass

#print axioms lower_supported
#print axioms upper_supported
#print axioms lower_unit
#print axioms upper_unit
#print axioms selected_quartic_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
