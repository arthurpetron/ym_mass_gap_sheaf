/-
# Coherent signed-family rows in the COMPLETE original energy

Every original link is retained. At a row, weighted quaternion tails are
summed BEFORE their norm is taken; neither repetitions nor cross-plane terms
are removed. The exact row-square subtraction is inserted under every actual
passive channel-source square. BOTH original Taylor remainders remain.

This computes the full family energy's coherent density. It does not estimate
its norm moment or signed debt against SAME surviving variance, supply a
chronological window bound, or identify a physical scaling limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound (familyChannelFirstOrder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentTail
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage

/-- Total computed index selection. The fallback is never used at a row in
the original range; the two lemmas below prove the actual physical pin. -/
def selectedLink (width b : Nat) : Z4Link :=
  (baseLinks width).getD b ((0,0,0,0), .x0)

private theorem selectedLink_eq (width b : Nat) (hb : b < N width) :
    selectedLink width b = (baseLinks width)[b] :=
  (List.getElem_eq_getD (h := hb) ((0,0,0,0), Dir4.x0)).symm

theorem selectedLink_mem (width b : Nat) (hb : b < N width) :
    selectedLink width b ∈ baseLinks width := by
  rw [selectedLink_eq width b hb]
  exact List.getElem_mem hb

theorem selectedLink_idxOf (width b : Nat) (hb : b < N width) :
    (baseLinks width).idxOf (selectedLink width b) = b := by
  rw [selectedLink_eq width b hb]
  let l : Z4Link := (baseLinks width)[b]
  have hl : l ∈ baseLinks width := List.getElem_mem hb
  have hget : (baseLinks width)[(baseLinks width).idxOf l]'
      (List.idxOf_lt_length_of_mem hl) = l :=
    LawfulBEq.eq_of_beq (List.findIdx_getElem (w := List.idxOf_lt_length_of_mem hl))
  exact List.getElem?_inj (List.idxOf_lt_length_of_mem hl) (baseLinks_nodup width)
    (by rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hl),
      List.getElem?_eq_getElem hb]; exact congrArg some hget)

/-- Norms of aggregate tails, not sums of individual-face norms. -/
def coherentNormRows (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : List Nat → RatPoly
  | [] => polyZero
  | b::bs => polyAdd
      (polyQuaternionNorm (aggregateCoherentTail width (selectedLink width b) c qs))
      (coherentNormRows width c qs bs)

/-- Actual incident-family squares; a face may occur in several different
rows, exactly as in the original angular operator. -/
def coherentSquareRows (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : List Nat → RatPoly
  | [] => polyZero
  | b::bs =>
      let f := incidentSpan width (selectedLink width b) c qs
      polyAdd (polyMul f f) (coherentSquareRows width c qs bs)

private theorem row_paid (width b : Nat) (hb : b < N width)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ face, face ∈ qs → face ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    let r := incidentSpan width (selectedLink width b) c qs
    HaarCarrierEqv (N width) (polyAdd (blockGamma b f f) (polyMul r r))
      (polySmul 4 (polyQuaternionNorm
        (aggregateCoherentTail width (selectedLink width b) c qs))) := by
  dsimp only
  have hr := family_coherent_row width (selectedLink width b)
    (selectedLink_mem width b hb) c qs hqs
  rw [selectedLink_idxOf width b hb] at hr
  have he := HaarCarrierEqv.add hr
    (HaarCarrierEqv.refl (N width)
      (polyMul (incidentSpan width (selectedLink width b) c qs)
        (incidentSpan width (selectedLink width b) c qs)))
  exact he.trans (RatPolyCoeffEqv.haarCarrier
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun
        | 0 => polySmul 4 (polyQuaternionNorm
            (aggregateCoherentTail width (selectedLink width b) c qs))
        | _ => polyMul (incidentSpan width (selectedLink width b) c qs)
            (incidentSpan width (selectedLink width b) c qs))))

private theorem rows_paid (width : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ face, face ∈ qs → face ∈ spatialFaces width) :
    ∀ ids : List Nat, (∀ b, b ∈ ids → b < N width) →
      HaarCarrierEqv (N width)
        (polyAdd (activeGamma ids (spatialSpan width c qs) (spatialSpan width c qs))
          (coherentSquareRows width c qs ids))
        (polySmul 4 (coherentNormRows width c qs ids))
  | [], _ => RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.add_zero polyZero).trans (RatPolyCoeffEqv.smul_zero 4).symm)
  | b::bs, hids => by
      have hb := hids b List.mem_cons_self
      have ih := rows_paid width c qs hqs bs
        (fun i hi => hids i (List.mem_cons_of_mem b hi))
      have he := HaarCarrierEqv.add (row_paid width b hb c qs hqs) ih
      have hp : RatPolyCoeffEqv
          (polyAdd (activeGamma (b::bs) (spatialSpan width c qs) (spatialSpan width c qs))
            (coherentSquareRows width c qs (b::bs)))
          (polyAdd
            (polyAdd (blockGamma b (spatialSpan width c qs) (spatialSpan width c qs))
              (polyMul (incidentSpan width (selectedLink width b) c qs)
                (incidentSpan width (selectedLink width b) c qs)))
            (polyAdd (activeGamma bs (spatialSpan width c qs) (spatialSpan width c qs))
              (coherentSquareRows width c qs bs))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide) (fun
            | 0 => blockGamma b (spatialSpan width c qs) (spatialSpan width c qs)
            | 1 => activeGamma bs (spatialSpan width c qs) (spatialSpan width c qs)
            | 2 => polyMul (incidentSpan width (selectedLink width b) c qs)
                (incidentSpan width (selectedLink width b) c qs)
            | _ => coherentSquareRows width c qs bs)
      exact (RatPolyCoeffEqv.haarCarrier hp).trans
        (he.trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_add 4 _ _).symm))

/-- ALL original angular blocks, arbitrary signs and repeated literal faces.
Every Haar insertion retains every cross-plane and boundary contribution. -/
theorem family_coherent_full_angular (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ face, face ∈ qs → face ∈ spatialFaces width) :
    HaarCarrierEqv (N width)
      (polyAdd (activeGamma (List.range (N width)) (spatialSpan width c qs) (spatialSpan width c qs))
        (coherentSquareRows width c qs (List.range (N width))))
      (polySmul 4 (coherentNormRows width c qs (List.range (N width)))) :=
  rows_paid width c qs hqs _ (fun _ hb => List.mem_range.mp hb)

/-- The unchanged family spectator schedule and projected V*g_depth source. -/
def coherentChannelMoment (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (insertion : RatPoly) : Q' :=
  channelSquare (N width) w K (familySpectatorBlocks width qs)
    (projectedEndpointSource w K width (terminalMessage w K width depth)) insertion

def coherentRetainedSquare (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  coherentChannelMoment w K width depth qs
    (coherentSquareRows width c qs (List.range (N width)))

def coherentPaidMoment (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  coherentChannelMoment w K width depth qs
    (polySmul 4 (coherentNormRows width c qs (List.range (N width))))

private theorem sum_add (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun z => left z+right z) ≈ channelSum cs left+channelSum cs right
  | [] => by change (0 : Q') ≈ 0+0; decide
  | a::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (sum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun
          | 0 => a.1*left a.2 | 1 => a.1*right a.2
          | 2 => channelSum cs left | _ => channelSum cs right))

theorem family_coherent_channel_cancellation (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ face, face ∈ qs → face ∈ spatialFaces width) :
    familyChannelFirstOrder w K width depth c qs +
      coherentRetainedSquare w K width depth c qs ≈ coherentPaidMoment w K width depth c qs := by
  let ids := familySpectatorBlocks width qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let cs := productChannels (N width) w K ids
  let W := fun z => polyMul (channelSource ids q z) (channelSource ids q z)
  let G := activeGamma (List.range (N width)) (spatialSpan width c qs) (spatialSpan width c qs)
  let S := coherentSquareRows width c qs (List.range (N width))
  let P := polySmul 4 (coherentNormRows width c qs (List.range (N width)))
  change channelSum cs (fun z => H (N width) (polyMul (W z) G)) +
    channelSum cs (fun z => H (N width) (polyMul (W z) S)) ≈
      channelSum cs (fun z => H (N width) (polyMul (W z) P))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (sum_add _ _ cs)) ?_
  apply channelSum_congr
  intro a _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_add_right (W a.2) G S))
      (quaternionHaar_append (N width) _ _)))
    (family_coherent_full_angular width c qs hqs (W a.2))

private def rowSquareCertificate (width : Nat) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) : ∀ ids : List Nat,
    Certificate (N width) (coherentSquareRows width c qs ids)
  | [] => Certificate.square polyZero (by
      intro t ht
      exact False.elim (List.not_mem_nil ht))
  | b::bs => (Certificate.square _ (spatialSpan_supported width c
      (BF4ExactSlabFixedSpatialFamilyIncidence.blockRowFaces width
        ((baseLinks width).idxOf (selectedLink width b)) qs))).add
      (rowSquareCertificate width c qs bs)

private theorem sum_nonnegative (value : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ a, a ∈ cs → (0 : Q') ≤ a.1) →
    (∀ a, a ∈ cs → (0 : Q') ≤ value a.2) → (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | a::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw a List.mem_cons_self) (hv a List.mem_cons_self))
      (sum_nonnegative value cs (fun b hb => hw b (List.mem_cons_of_mem a hb))
        (fun b hb => hv b (List.mem_cons_of_mem a hb)))

/-- Constructed positivity of the ACTUAL retained channel row squares. -/
theorem family_coherent_retained_square_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    (0 : Q') ≤ coherentRetainedSquare w K width depth c qs := by
  let ids := familySpectatorBlocks width qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  apply sum_nonnegative
  · exact productChannels_nonnegative (N width) hw0 K ids
  · intro a ha
    have hsource := channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width qs) hq a ha
    exact ((Certificate.square _ hsource).mul
      (rowSquareCertificate width c qs _)).haar_nonnegative

/-- Exact COMPLETE original temporal energy for any strictly padded literal
family. Both signed Taylor debts are unchanged; no scaling bound is inferred. -/
theorem family_coherent_energy_retained_square (w : Q') (K : Nat)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ face, face ∈ qs → face ∈ spatialFaces base) :
    energy w K width (terminalMessage w K width depth) (spatialSpan width c qs) +
      ((1 : Q')-w)*coherentRetainedSquare w K width depth c qs ≈
      ((1 : Q')-w)*coherentPaidMoment w K width depth c qs +
        familyChannelTaylorDebt w K width depth c qs := by
  have he := padded_family_channel_energy_taylor w K hwidth depth c qs hqs
  have hc := family_coherent_channel_cancellation w K width depth c qs
    (fun face hf => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs face hf))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.var 3)))
        (.add (.mul (.var 0) (.add (.var 1) (.var 3))) (.var 2))
        (by decide) (fun
          | 0 => (1 : Q')-w
          | 1 => familyChannelFirstOrder w K width depth c qs
          | 2 => familyChannelTaylorDebt w K width depth c qs
          | _ => coherentRetainedSquare w K width depth c qs))
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hc) (Q'.eqv_refl _)))

#print axioms selectedLink
#print axioms selectedLink_mem
#print axioms selectedLink_idxOf
#print axioms coherentNormRows
#print axioms coherentSquareRows
#print axioms family_coherent_full_angular
#print axioms family_coherent_channel_cancellation
#print axioms family_coherent_retained_square_nonnegative
#print axioms family_coherent_energy_retained_square

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCoherentEnergy
