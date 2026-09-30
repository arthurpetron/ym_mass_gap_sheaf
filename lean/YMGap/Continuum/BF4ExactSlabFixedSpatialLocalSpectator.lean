/-
# A local spectator for the ORIGINAL interacting terminal endpoint

Only the spatial faces touching a supplied link list and the matching final
kinetic factors are separated. The entire previous terminal input, all
exterior heat factors and all shared coordinates are retained. The resulting
explicit spectator is independent of the selected links. Lower and upper
certificates compare V*u_(n+1) to this SAME spectator.

The number of compared factors is at most seven times the selected-link
count (at most 28 for a plaquette), not the spatial volume or terminal depth.
The heat floor and cap remain nome-dependent. This is an actual local-band
producer, not yet a positive-time response bound, spatial limit or mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalCollarGeometry
import YMGap.Continuum.SU2QuaternionProductHeatLocalBand
import YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalCollarGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight activeBlocks terminalMessage

def spatialProduct (w : Q') (K width : Nat) (faces : List Z4Plaq) : RatPoly :=
  polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces

private def productCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (faces : List Z4Plaq) → Certificate (N width) (spatialProduct w K width faces)
  | [] => .one _
  | face::faces => (faceCertificate hw0 hw1 K width (N width) (Nat.le_refl _) face hK).mul
      (productCertificate hw0 hw1 K width hK faces)

private def productFloor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (faces : List Z4Plaq) → Certificate (N width)
      (polyAdd (spatialProduct w K width faces) (polyNeg (cap ((headFloor w)^faces.length))))
  | [] => .ofCoeff
      (((RatPolyCoeffEqv.one_smul polyOne).symm.add (.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
          (by decide) (fun _ => cap 1))) (.constant _ 0 (Q'.le_refl' _))
  | face::faces => by
      let c := headFloor w
      let p := heatPrefix w K (plaquette width face).scalar
      let q := spatialProduct w K width faces
      have L : Certificate (N width) (polyAdd p (polyNeg (cap c))) :=
        QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
          (plaquette_supported width (N width) (Nat.le_refl _) face)
          (plaquette_unit width (N width) (Nat.le_refl _) face) K hK
      exact .ofCoeff
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul c (c^faces.length)).symm)).trans
          ((coeffEvalExpr_eqv_of_normalize_eq
            (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
            (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
              (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
            (by decide) (fun | 0 => p | 1 => q | 2 => cap c | _ => cap (c^faces.length))).trans
              ((RatPolyCoeffEqv.refl _).add (cap_mul_left c _))))
        ((L.mul (productCertificate hw0 hw1 K width hK faces)).add
          (.smul c (Q'.le_of_lt (headFloor_positive hw0 hw1)) (productFloor hw0 hw1 K width hK faces)))

/-- The literal original spatial action, split without changing its factors. -/
theorem spatial_partition (w : Q') (K width : Nat) (selected : List Z4Link) :
    RatPolyCoeffEqv (spatialWeight w K width)
      (polyMul (spatialProduct w K width (spatialCollarFaces width selected))
        (spatialProduct w K width (spatialCollarComplementFaces width selected))) := by
  unfold spatialWeight spatialProduct
  exact (polynomialProduct_perm _ (spatialCollar_partition width selected).symm).trans
    (polynomialProduct_append _ _ _)

def localBlocks (width : Nat) (selected : List Z4Link) : List Nat :=
  (activeBlocks width).filter (fun i => decide (i ∈ selected.map (fun l => (baseLinks width).idxOf l)))

def restBlocks (width : Nat) (selected : List Z4Link) : List Nat :=
  (activeBlocks width).filter (fun i => !(decide (i ∈ selected.map (fun l => (baseLinks width).idxOf l))))

theorem block_partition (width : Nat) (selected : List Z4Link) :
    (localBlocks width selected ++ restBlocks width selected).Perm (activeBlocks width) :=
  List.filter_append_perm _ _

theorem localBlocks_length_le (width : Nat) (selected : List Z4Link) :
    (localBlocks width selected).length ≤ selected.length := by
  have h := CayleyPruferInjection.nodup_subset_length_le (localBlocks width selected)
    (selected.map (fun l => (baseLinks width).idxOf l))
    (List.filter_sublist.nodup (activeBlocks_nodup width))
    (fun _ hi => of_decide_eq_true (List.mem_filter.mp hi).2)
  simpa only [List.length_map] using h

private theorem local_lt (width : Nat) (selected : List Z4Link) (i : Nat)
    (hi : i ∈ localBlocks width selected) : i < N width :=
  activeBlocks_lt width i (List.mem_filter.mp hi).1

private theorem rest_lt (width : Nat) (selected : List Z4Link) (i : Nat)
    (hi : i ∈ restBlocks width selected) : i < N width :=
  activeBlocks_lt width i (List.mem_filter.mp hi).1

def erasedTerminal (w : Q') (K width n : Nat) (selected : List Z4Link) : RatPoly :=
  productMap (N width) w K (restBlocks width selected)
    (polyMul (spatialWeight w K width) (terminalMessage w K width n))

/-- The full old terminal input is kept, not replaced by a smaller action. -/
def spectator (w : Q') (K width n : Nat) (selected : List Z4Link) : RatPoly :=
  polyMul (spatialProduct w K width (spatialCollarComplementFaces width selected))
    (erasedTerminal w K width n selected)

theorem spectator_supported (w : Q') (K width n : Nat) (selected : List Z4Link) :
    SupportedQuaternionBlocks (N width) (spectator w K width n selected) :=
  supported_polyMul (heatProduct_supported w K width _)
    (productMap_supported _ w K _ (rest_lt width selected)
      (supported_polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_supported w K width)
        (terminalMessage_supported w K width n)))

theorem spectator_independent (w : Q') (K width n : Nat) (selected : List Z4Link)
    (l : Z4Link) (hl : l ∈ selected) (hbase : l ∈ baseLinks width) :
    QuaternionBlockIndependent ((baseLinks width).idxOf l) (spectator w K width n selected) := by
  have hnot : (baseLinks width).idxOf l ∉ restBlocks width selected := by
    intro hi
    have h := (List.mem_filter.mp hi).2
    have hm : (baseLinks width).idxOf l ∈ selected.map (fun l => (baseLinks width).idxOf l) :=
      List.mem_map.mpr ⟨l, hl, rfl⟩
    simp [hm] at h
  exact quaternionBlockIndependent_polyMul
    (heatProduct_independent w K hbase _ (fun _ hf => spatialCollarComplement_omits width selected hf hl))
    (productMap_independent_of_not_mem _ w K _ (rest_lt width selected) _
      (List.idxOf_lt_length_of_mem hbase) hnot _
      (supported_polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_supported w K width)
        (terminalMessage_supported w K width n)))

private theorem terminal_pin (w : Q') (K width n : Nat) (selected : List Z4Link) :
    RatPolyCoeffEqv (terminalMessage w K width (n+1))
      (productMap (N width) w K (localBlocks width selected ++ restBlocks width selected)
        (polyMul (spatialWeight w K width) (terminalMessage w K width n))) := by
  rw [← terminalMessage_next]
  unfold transferStep step
  rw [kineticWeight_eq_indexedProduct]
  exact partialHaarHeads_congr (N width)
    ((polynomialProduct_perm _ (block_partition width selected).symm).mul_right _)

def lowerFactor (w : Q') (width : Nat) (selected : List Z4Link) : Q' :=
  (headFloor w)^(spatialCollarFaces width selected).length *
    (headFloor w)^(localBlocks width selected).length

def upperFactor (w : Q') (width : Nat) (selected : List Z4Link) : Q' :=
  (prefixCap w)^(spatialCollarFaces width selected).length *
    (prefixCap w)^(localBlocks width selected).length

private def combine_lower {blocks : Nat} {C R g r : RatPoly} {c d : Q'}
    (hc : (0 : Q') ≤ c) (CR : Certificate blocks R) (G : Certificate blocks g)
    (L : Certificate blocks (polyAdd C (polyNeg (cap c))))
    (M : Certificate blocks (polyAdd g (polyNeg (polySmul d r)))) :
    Certificate blocks (polyAdd (polyMul (polyMul C R) g)
      (polyNeg (polySmul (c*d) (polyMul R r)))) := by
  have e := (cap_mul_left (c*d) (polyMul R r)).symm.trans
    ((cap_mul c d).symm.mul_right (polyMul R r))
  have ering : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul C R) g)
        (polyNeg (polyMul (polyMul (cap c) (cap d)) (polyMul R r))))
      (polyMul R (polyAdd (polyMul (polyAdd C (polyNeg (cap c))) g)
        (polyMul (cap c) (polyAdd g (polyNeg (polyMul (cap d) r)))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.mul (.var 4) (.var 5)) (.mul (.var 1) (.var 3)))))
      (.mul (.var 1)
        (.add (.mul (.add (.var 0) (.neg (.var 4))) (.var 2))
          (.mul (.var 4) (.add (.var 2) (.neg (.mul (.var 5) (.var 3)))))))
      (by decide) (fun | 0 => C | 1 => R | 2 => g | 3 => r | 4 => cap c | _ => cap d)
  have escale := (((RatPolyCoeffEqv.refl g).add (RatPolyCoeffEqv.neg (cap_mul_left d r))).mul_left (cap c)).trans
    (cap_mul_left c _)
  exact .ofCoeff (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg e)).trans
    (ering.trans (((RatPolyCoeffEqv.refl _).add escale).mul_left R)))
    (CR.mul ((L.mul G).add (.smul c hc M)))

private def combine_upper {blocks : Nat} {C R g r : RatPoly} {c d : Q'}
    (hc : (0 : Q') ≤ c) (CR : Certificate blocks R) (G : Certificate blocks g)
    (L : Certificate blocks (polyAdd (cap c) (polyNeg C)))
    (M : Certificate blocks (polyAdd (polySmul d r) (polyNeg g))) :
    Certificate blocks (polyAdd (polySmul (c*d) (polyMul R r))
      (polyNeg (polyMul (polyMul C R) g))) := by
  have e := (cap_mul_left (c*d) (polyMul R r)).symm.trans
    ((cap_mul c d).symm.mul_right (polyMul R r))
  have ering : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul (cap c) (cap d)) (polyMul R r))
        (polyNeg (polyMul (polyMul C R) g)))
      (polyMul R (polyAdd (polyMul (polyAdd (cap c) (polyNeg C)) g)
        (polyMul (cap c) (polyAdd (polyMul (cap d) r) (polyNeg g))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 4) (.var 5)) (.mul (.var 1) (.var 3)))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
      (.mul (.var 1)
        (.add (.mul (.add (.var 4) (.neg (.var 0))) (.var 2))
          (.mul (.var 4) (.add (.mul (.var 5) (.var 3)) (.neg (.var 2))))))
      (by decide) (fun | 0 => C | 1 => R | 2 => g | 3 => r | 4 => cap c | _ => cap d)
  have escale := (((cap_mul_left d r).add (RatPolyCoeffEqv.refl (polyNeg g))).mul_left (cap c)).trans
    (cap_mul_left c _)
  exact .ofCoeff ((e.add (.refl _)).trans
    (ering.trans (((RatPolyCoeffEqv.refl _).add escale).mul_left R)))
    (CR.mul ((L.mul G).add (.smul c hc M)))

/-- Positivity is constructed from the original full terminal input. -/
def spectator_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (selected : List Z4Link) :
    Certificate (N width) (spectator w K width n selected) :=
  (productCertificate hw0 hw1 K width hK _).mul
    (erasedCertificate _ hw0 hw1 K hK _ (rest_lt width selected)
      (supported_polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_supported w K width)
        (terminalMessage_supported w K width n))
      ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
        (terminalMessage_certificate hw0 hw1 K width hK n)))

/-- Actual endpoint LOWER band, including the spatial potential and every
earlier terminal step; no band is supplied as an analytic hypothesis. -/
def endpoint_lowerCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (selected : List Z4Link) :
    Certificate (N width)
      (polyAdd (polyMul (spatialWeight w K width) (terminalMessage w K width (n+1)))
        (polyNeg (polySmul (lowerFactor w width selected) (spectator w K width n selected)))) := by
  have M : Certificate (N width)
      (polyAdd (terminalMessage w K width (n+1))
        (polyNeg (polySmul ((headFloor w)^(localBlocks width selected).length)
          (erasedTerminal w K width n selected)))) :=
    .ofCoeff ((terminal_pin w K width n selected).add (.refl _))
      (productMap_localFloorCertificate _ hw0 hw1 K hK _ _
        (local_lt width selected) (rest_lt width selected)
        (supported_polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_supported w K width)
          (terminalMessage_supported w K width n))
        ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
          (terminalMessage_certificate hw0 hw1 K width hK n)))
  exact .ofCoeff (((spatial_partition w K width selected).mul_right _).add (.refl _))
    (combine_lower (Q'.pow_nonneg _ (Q'.le_of_lt (headFloor_positive hw0 hw1)) _)
      (productCertificate hw0 hw1 K width hK _)
      (terminalMessage_certificate hw0 hw1 K width hK (n+1))
      (productFloor hw0 hw1 K width hK _) M)

/-- Matching actual endpoint UPPER band against exactly the same spectator. -/
def endpoint_upperCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (selected : List Z4Link) :
    Certificate (N width)
      (polyAdd (polySmul (upperFactor w width selected) (spectator w K width n selected))
        (polyNeg (polyMul (spatialWeight w K width) (terminalMessage w K width (n+1))))) := by
  have M : Certificate (N width)
      (polyAdd (polySmul ((prefixCap w)^(localBlocks width selected).length)
          (erasedTerminal w K width n selected))
        (polyNeg (terminalMessage w K width (n+1)))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (terminal_pin w K width n selected)))
      (productMap_localCapCertificate _ hw0 hw1 K hK _ _
        (local_lt width selected) (rest_lt width selected)
        (supported_polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_supported w K width)
          (terminalMessage_supported w K width n))
        ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
          (terminalMessage_certificate hw0 hw1 K width hK n)))
  exact .ofCoeff ((RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.neg ((spatial_partition w K width selected).mul_right _)))
    (combine_upper (Q'.pow_nonneg _ (prefixCap_nonnegative hw0) _)
      (productCertificate hw0 hw1 K width hK _)
      (terminalMessage_certificate hw0 hw1 K width hK (n+1))
      (Interval.productUniform _ (prefixCap w) (spatialCollarFaces width selected)
        (fun face _ => faceInterval hw0 hw1 K width (N width) (Nat.le_refl _) face)).upper M)

/-- A width-independent bound on the number of factors paid in BOTH bands. -/
theorem comparison_count_le (width : Nat) (selected : List Z4Link) :
    (spatialCollarFaces width selected).length + (localBlocks width selected).length ≤
      7 * selected.length := by
  have hc := spatialCollarFaces_length_le width selected
  have hk := localBlocks_length_le width selected
  omega

theorem plaquette_comparison_count_le (width : Nat) (face : Z4Plaq) :
    (spatialCollarFaces width (edgesOf face)).length +
      (localBlocks width (edgesOf face)).length ≤ 28 := by
  have h := comparison_count_le width (edgesOf face)
  simpa only [edgesOf, List.length_cons, List.length_nil] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.spatialProduct
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.spatial_partition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.localBlocks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.restBlocks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.block_partition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.localBlocks_length_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.erasedTerminal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.spectator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.spectator_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.spectator_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.lowerFactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.upperFactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.spectator_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.endpoint_lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.endpoint_upperCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.comparison_count_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.plaquette_comparison_count_le
