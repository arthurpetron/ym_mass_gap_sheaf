/-
# Footprint first order in the ORIGINAL signed channel Taylor energy

The exact original passive-channel expansion supplies its own signed remainder,
not an assumed small analytic field. The proved footprint-only first-order
comparison gives an energy ceiling against the SAME original odd variance.
Both endpoints, original channel weights, cutoff, source and mean are retained.

The signed remainder is NOT asserted small or of helpful sign. In particular,
it includes omitted finite-cutoff modes. The band coefficient can deteriorate
with nome and family size, so this is not a physical scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
import YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar (weighted_gamma_finSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyPassiveCancellation
  (padded_family_energy_eq_channels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy)
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage
  oddMass oddVariance channelFirstOrderVarianceConstant

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem channelSum_add (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => left c + right c) ≈
        channelSum cs left + channelSum cs right
  | [] => by change (0 : Q') ≈ 0+0; decide
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun
          | 0 => c.1*left c.2
          | 1 => c.1*right c.2
          | 2 => channelSum cs left
          | _ => channelSum cs right))

/-- Exact pin of the channel angular cost; no coefficient absolute values. -/
theorem familyChannelFirstOrder_eq_angular (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := spatialSpan width c qs
    let ids := familySpectatorBlocks width qs
    familyChannelFirstOrder w K width depth c qs ≈
      channelSum (productChannels (N width) w K ids) (fun z =>
        weightedAngularEnergy (N width-1) (channelSource ids q z) f) := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  apply channelSum_congr
  intro z _
  simpa only [weightedAngularEnergy, hn] using
    weighted_gamma_finSum (N width) (polyMul (channelSource ids q z.2)
      (channelSource ids q z.2)) f

/-- Both computed remainders retain their signs and actual cutoff. This
definition changes neither source nor channel weights and claims no smallness. -/
def familyChannelTaylorDebt (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids) (fun z =>
    let a := channelSource ids q z
    pairRemainder (N width-1) w K a (polyMul a (polyMul f f)) +
      -(pairRemainder (N width-1) w K (polyMul a f) (polyMul a f)))

/-- Exact original energy identity. No upper-bound surrogate replaces the
signed Taylor debt, and no infinite-cutoff operator is substituted. -/
theorem padded_family_channel_energy_taylor (w : Q') (K : Nat)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    energy w K width (terminalMessage w K width depth) (spatialSpan width c qs) ≈
      ((1 : Q')-w)*familyChannelFirstOrder w K width depth c qs +
        familyChannelTaylorDebt w K width depth c qs := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  let cs := productChannels (N width) w K ids
  let a := fun z => channelSource ids q z
  let D := fun z => pairRemainder (N width-1) w K (a z) (polyMul (a z) (polyMul f f)) +
    -(pairRemainder (N width-1) w K (polyMul (a z) f) (polyMul (a z) f))
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf := spatialSpan_supported width c qs
  have hterm := channelSum_congr
    (fun z => sourceEnergy (N width) w K (List.range (N width)) (a z) f)
    (fun z => ((1 : Q')-w)*weightedAngularEnergy (N width-1) (a z) f + D z) cs (by
      intro z hz
      have ha := channelSource_supported (N width) w K ids
        (familySpectatorBlocks_lt width qs) hq z hz
      have ht := sourceEnergy_taylor (N width-1) w K (a z.2) f
        (by simpa only [hn] using ha) (by simpa only [hn] using hf)
      have hfirst := sourceFirstOrder_eq_weightedAngularEnergy (N width-1) (a z.2) f
        (by simpa only [hn] using ha) (by simpa only [hn] using hf)
      exact Q'.eqv_trans _ _ _ (by simpa only [hn] using ht)
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hfirst) (Q'.eqv_refl _)))
  have hsum := channelSum_add
    (fun z => ((1 : Q')-w)*weightedAngularEnergy (N width-1) (a z) f) D cs
  have hlead := channelSum_smul (fun z => weightedAngularEnergy (N width-1) (a z) f)
    ((1 : Q')-w) cs
  exact Q'.eqv_trans _ _ _
    (padded_family_energy_eq_channels w K hwidth _
      (terminalMessage_supported w K width depth) c qs hqs)
    (Q'.eqv_trans _ _ _ hterm
      (Q'.eqv_trans _ _ _ hsum
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ hlead
            (Q'.mul_eqv_congr_left _ _ _ (familyChannelFirstOrder_eq_angular w K width depth c qs).symm))
          (Q'.eqv_refl _))))

/-- Actual original energy consumer of the proved first-order bound. The
complete signed debt still needs useful control on a justified scaling family. -/
theorem padded_family_energy_le_channelVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    energy w K width (terminalMessage w K width (n+1)) (spatialSpan width c qs) ≤
      (((1 : Q')-w)*channelFirstOrderVarianceConstant hw0 hw1 qs.length) *
        (oddMass w K width (n+1) *
          oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width c qs)) +
      familyChannelTaylorDebt w K width (n+1) c qs := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ ((1 : Q')-w)
    (family_channel_firstOrder_variance_bound hw0 hw1 K hK hwidth n c qs hqs)
    (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  have h' := Q'.add_le_add_right _ _ (familyChannelTaylorDebt w K width (n+1) c qs) h
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (padded_family_channel_energy_taylor w K hwidth (n+1) c qs hqs))
    (Q'.le_trans' _ _ _ h'
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_refl _))))

/-- Normalize only by the SAME already-proved positive partition. The
remainder is still its signed value, not an independently assumed budget. -/
theorem padded_family_normalizedEnergy_le_channelVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK (n+1) (spatialSpan width c qs) ≤
      (((1 : Q')-w)*channelFirstOrderVarianceConstant hw0 hw1 qs.length) *
        oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width c qs) +
      familyChannelTaylorDebt w K width (n+1) c qs *
        Q'.recipPos (oddMass w K width (n+1))
          (oddMass_positive hw0 hw1 K width hK (n+1)) := by
  let Z := oddMass w K width (n+1)
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK (n+1))
  let C := ((1 : Q')-w)*channelFirstOrderVarianceConstant hw0 hw1 qs.length
  let v := oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width c qs)
  let D := familyChannelTaylorDebt w K width (n+1) c qs
  have h := Q'.mul_le_mul_of_nonneg_right _ _ r
    (padded_family_energy_le_channelVariance hw0 hw1 K hK hwidth n c qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hright : (C*(Z*v)+D)*r ≈ C*v+D*r :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.var 4))
        (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 4)) (.var 2)))
          (.mul (.var 3) (.var 4))) (by decide)
        (fun | 0 => C | 1 => Z | 2 => v | 3 => D | _ => r))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left C _ _
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ v (Q'.mul_recipPos_eqv Z
              (oddMass_positive hw0 hw1 K width hK (n+1))))
            (Q'.one_mul_eqv v)))
        (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright)

#print axioms familyChannelFirstOrder_eq_angular
#print axioms familyChannelTaylorDebt
#print axioms padded_family_channel_energy_taylor
#print axioms padded_family_energy_le_channelVariance
#print axioms padded_family_normalizedEnergy_le_channelVariance

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance
