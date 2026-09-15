/-
# Exact added-action response of the ORIGINAL growing channel amplitude

The larger lower-face list is partitioned into the actual embedded source
list and its complement. The original full enlarged lower action is exactly
the interior action dressed by all added lower-face heat factors. Shared
links are retained. For the actual translated channel-observable insertion,
the amplitude difference is I(p W) - I(p), with no independence premise.

The SAME-cutoff difference has an explicit QCauchy modulus and a limit
identified with the difference of the original coefficient limits. This is
an exact response, not a smallness theorem. Its cutoff may depend on both
volumes; no decay in padding, normalization bound, thermodynamic coefficient
separation, full-spectator packet floor or physical mass gap follows here.
-/

import YMGap.Continuum.BF4ExactSlabGrowingChannelInterior

namespace YMGap.Continuum.BF4ExactSlabGrowingChannelExterior

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial
open YMGap.Continuum.BF4ExactSlabGrowingChannelInterior
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def interiorIds (half padding : Nat) : List Nat :=
  (centralLowerFaceIds (half+padding)).filter (fun id => decide (id ∈ embeddedLowerIds half padding))

def exteriorIds (half padding : Nat) : List Nat :=
  (centralLowerFaceIds (half+padding)).filter (fun id => !(decide (id ∈ embeddedLowerIds half padding)))

theorem embeddedLowerIds_nodup (half padding : Nat) : (embeddedLowerIds half padding).Nodup :=
  nodup_map_of_injOn _ _ (lowerFaceIds_nodup half) (fun i hi j hj h =>
    shiftFaceId_injective (central_room (by omega)) (central_room (by omega))
      (mem_centralLowerFaceIds.mp hi).1 (mem_centralLowerFaceIds.mp hj).1 h)

theorem interiorIds_perm (half padding : Nat) : (interiorIds half padding).Perm (embeddedLowerIds half padding) := by
  apply perm_of_nodup_mem_iff _ _ (List.filter_sublist.nodup (lowerFaceIds_nodup _)) (embeddedLowerIds_nodup half padding)
  intro id
  constructor
  · intro hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  · intro hi
    exact List.mem_filter.mpr ⟨embeddedLowerIds_lower hi, decide_eq_true hi⟩

theorem lowerFace_partition (half padding : Nat) :
    (interiorIds half padding ++ exteriorIds half padding).Perm (centralLowerFaceIds (half+padding)) :=
  List.filter_append_perm (fun id => decide (id ∈ embeddedLowerIds half padding)) _

def exteriorHeat (w : Q') (K half padding : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent (half+padding))) (exteriorIds half padding)

theorem lowerHeat_dressing (w : Q') (K half padding : Nat) :
    RatPolyCoeffEqv (lowerHeatProduct w K (half+padding))
      (polyMul (polynomialProduct (faceHeatPolynomial w K (centralExtent (half+padding))) (embeddedLowerIds half padding))
        (exteriorHeat w K half padding)) :=
  (polynomialProduct_perm _ (lowerFace_partition half padding).symm).trans
    ((polynomialProduct_append _ _ _).trans
      ((polynomialProduct_perm _ (interiorIds_perm half padding)).mul (RatPolyCoeffEqv.refl _)))

/-- Every added heat factor remains in the amplitude on the SAME target links. -/
theorem lowerMoment_dressed (w : Q') (K half padding : Nat) (p : RatPoly) :
    Q'.eqv (lowerMoment w K (half+padding) p)
      (interiorSequence w half padding (polyMul p (exteriorHeat w K half padding)) K) :=
  haar_of_coeff_eqv _ (((lowerHeat_dressing w K half padding).mul_left p).trans
    (((RatPolyCoeffEqv.mul_comm _ _).mul_left p).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm))

variable (w : Q') {half id : Nat} (padding : Nat) (e : PlaquetteExpression half) (c : SpinChannel half id)

local notation "P" => insertion (bulkAtTime padding (Fin.mk 0 (Nat.zero_lt_succ padding)) e) (shiftedChannel padding c)
local notation "F" => (fun K : Nat => lowerMoment w K (half+padding) P)
local notation "S" => (fun K : Nat => lowerMoment w K half (insertion e c))

def responseSequence (K : Nat) : Q' := F K + -(S K)

theorem responseSequence_exterior (hi : id ∈ centralFixedFaceIds half) (K : Nat) :
    Q'.eqv (responseSequence w padding e c K)
      (interiorSequence w half padding (polyMul P (exteriorHeat w K half padding)) K +
        -(interiorSequence w half padding P K)) :=
  Q'.add_eqv_congr' (lowerMoment_dressed w K half padding P)
    (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (interiorSequence_selected w hi padding e c K)))

variable (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

private def streamReal (r : Nat → Q') (h : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨h.M epsilon, h.bound epsilon he⟩

private theorem streamReal_pin (r : Nat → Q') (h : QCauchy r) : Equiv (streamReal r h) (ofQ'CauchySeq r h) :=
  fun epsilon he => ⟨h.M epsilon, fun n hn => h.bound epsilon he n _ hn (Nat.le_trans hn (self_le_QMhat r h n))⟩

private def differenceCauchy (r s : Nat → Q') (hr : QCauchy r) (hs : QCauchy s) :
    QCauchy (fun K => r K + -(s K)) :=
  scalarAddCauchy (streamReal r hr) (CReal.neg (streamReal s hs)) hr (scalarNegCauchy _ hs)

private theorem differenceLimit_pin (r s : Nat → Q') (hr : QCauchy r) (hs : QCauchy s) :
    Equiv (ofQ'CauchySeq _ (differenceCauchy r s hr hs)) (CReal.sub (ofQ'CauchySeq r hr) (ofQ'CauchySeq s hs)) := by
  have hraw : Equiv (streamReal (fun K => r K + -(s K)) (differenceCauchy r s hr hs))
      (CReal.sub (streamReal r hr) (streamReal s hs)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  have hleft := CReal.sub_congr_left (y := streamReal s hs) (streamReal_pin r hr)
  have hright := CReal.sub_congr_right (x := ofQ'CauchySeq r hr) (streamReal_pin s hs)
  exact (streamReal_pin _ (differenceCauchy r s hr hs)).symm.trans (hraw.trans (hleft.trans hright))

private def fullCauchy : QCauchy F := numeratorCauchy w hw0 hw1 _ _ _ P
private def sourceCauchy : QCauchy S := numeratorCauchy w hw0 hw1 _ _ _ (insertion e c)

def responseSequenceCauchy : QCauchy (responseSequence w padding e c) :=
  differenceCauchy F S (fullCauchy w padding e c hw0 hw1) (sourceCauchy w e c hw0 hw1)

def responseLimit : CReal := ofQ'CauchySeq _ (responseSequenceCauchy w padding e c hw0 hw1)

def responseLimitCauchy : QCauchy (responseLimit w padding e c hw0 hw1).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _ (responseSequenceCauchy w padding e c hw0 hw1)

/-- The limit is pinned to the actual original lower-action coefficient limits. -/
theorem responseLimit_pin : Equiv (responseLimit w padding e c hw0 hw1)
    (CReal.sub (coefficientLimit w hw0 hw1 (half+padding) P) (coefficientLimit w hw0 hw1 half (insertion e c))) :=
  differenceLimit_pin F S (fullCauchy w padding e c hw0 hw1) (sourceCauchy w e c hw0 hw1)

/-- Numerical cutoff at fixed source/target volumes; NOT a padding-decay modulus. -/
def responseCutoff (epsilon : Q') : Nat := (responseSequenceCauchy w padding e c hw0 hw1).M epsilon

theorem response_approx_close (epsilon : Q') (he : (0 : Q') < epsilon) (K n : Nat)
    (hK : responseCutoff w padding e c hw0 hw1 epsilon ≤ K)
    (hn : responseCutoff w padding e c hw0 hw1 epsilon ≤ n) :
    responseSequence w padding e c K ≤ (responseLimit w padding e c hw0 hw1).approx n + epsilon ∧
    (responseLimit w padding e c hw0 hw1).approx n ≤ responseSequence w padding e c K + epsilon :=
  (responseSequenceCauchy w padding e c hw0 hw1).bound epsilon he K _ hK
    (Nat.le_trans hn (self_le_QMhat _ _ n))

end YMGap.Continuum.BF4ExactSlabGrowingChannelExterior

#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.interiorIds
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.exteriorIds
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.embeddedLowerIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.interiorIds_perm
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.lowerFace_partition
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.exteriorHeat
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.lowerHeat_dressing
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.lowerMoment_dressed
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.responseSequence
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.responseSequence_exterior
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.responseSequenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.responseLimit
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.responseLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.responseLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.responseCutoff
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelExterior.response_approx_close
