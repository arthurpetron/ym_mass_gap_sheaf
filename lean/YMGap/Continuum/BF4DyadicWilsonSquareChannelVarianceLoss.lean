/-
# Original channel variance mismatch in the actual heat mass loss

The same original spectator channels have nonnegative mass loss M-Z.
Their raw square at the OWN interacting center satisfies
  (A-Z*OWNVar)^2 <= 16*(M-Z)*A.
The finite weighted positive form gives coefficient-one Cauchy--Schwarz:
no channel count, source sign, factorization or substitute mean is used.
This does not supply a changing-family bound on M-Z relative to OWNVar,
nor a continuum or transfer-norm conclusion.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMomentDefect
import YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment
import YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
import YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels (channelSum)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
  (channelSum_add channelSum_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (oddMoment_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported oddCentered_independent centered_source_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (mass_oddMass)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
open YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage

private theorem qmul {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem sum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) →
      (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (hv c List.mem_cons_self))
      (sum_nonnegative value cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => hv d (List.mem_cons_of_mem c hd)))

private theorem sum_sub (cs : List GramChannel) (u v : RatPoly → Q') :
    channelSum cs (fun z => u z-v z) ≈ channelSum cs u-channelSum cs v := by
  have hn : channelSum cs (fun z => -v z) ≈ -(channelSum cs v) :=
    Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => (-1)*v z) cs (fun z _ =>
      poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
        (by decide) (fun _ => v z.2)))
      (Q'.eqv_trans _ _ _ (channelSum_smul v (-1) cs)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => channelSum cs v)))
  exact Q'.eqv_trans _ _ _ (channelSum_add u (fun z => -v z) cs)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) hn)

private theorem zero_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 0 polyOne) p) p :=
  ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl p)).trans
    (RatPolyCoeffEqv.zero_add p)

private theorem neg_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul (-1) p) p) (polySmul 0 polyOne) :=
  (RatPolyCoeffEqv.add_comm _ _).trans
    ((RatPolyCoeffEqv.add_neg_smul p).trans (RatPolyCoeffEqv.zero_smul polyOne).symm)

/-- A finite positive weighted form on functions. Support is required only
at the actual channel entries; its positivity is derived from the certificate. -/
private def channelWeightedGNSData (blocks : Nat) (W : RatPoly)
    (P : Certificate blocks W) (cs : List GramChannel)
    (hw : ∀ c, c ∈ cs → (0 : Q') ≤ c.1) : GNSData where
  V := {u : RatPoly → RatPoly // ∀ c, c ∈ cs → SupportedQuaternionBlocks blocks (u c.2)}
  veq := fun u v => ∀ z, RatPolyCoeffEqv (u.val z) (v.val z)
  veq_refl := fun _ _ => .refl _
  veq_symm := fun h z => (h z).symm
  veq_trans := fun h k z => (h z).trans (k z)
  zero := ⟨fun _ => polySmul 0 polyOne, fun _ _ => polySmul_supported (supported_one blocks) 0⟩
  add := fun u v => ⟨fun z => polyAdd (u.val z) (v.val z),
    fun c hc => supported_add (u.property c hc) (v.property c hc)⟩
  neg := fun u => ⟨fun z => polySmul (-1) (u.val z),
    fun c hc => polySmul_supported (u.property c hc) (-1)⟩
  smul := fun a u => ⟨fun z => polySmul a (u.val z),
    fun c hc => polySmul_supported (u.property c hc) a⟩
  add_congr := fun h k z => (h z).add (k z)
  neg_congr := fun h z => (h z).smul (-1)
  smul_congr := fun a {_ _} h z => (h z).smul a
  add_assoc := fun _ _ _ _ => .add_assoc _ _ _
  add_comm := fun _ _ _ => .add_comm _ _
  zero_add := fun u z => zero_add (u.val z)
  neg_add := fun u z => neg_add (u.val z)
  B := fun u v => channelSum cs (fun z => weightedPair blocks W (u.val z) (v.val z))
  B_congr_left := fun v h => channelSum_congr _ _ cs (fun c _ =>
    haar_of_coeff (((h c.2).mul_right (v.val c.2)).mul_right W))
  B_add_left := fun u v r => Q'.eqv_trans _ _ _
    (channelSum_congr _ _ cs (fun c _ => weighted_add_left blocks W _ _ _))
    (channelSum_add _ _ cs)
  B_smul_left := fun a u v => Q'.eqv_trans _ _ _
    (channelSum_congr _ _ cs (fun c _ => weighted_smul_left blocks W a _ _))
    (channelSum_smul _ a cs)
  B_symm := fun u v => channelSum_congr _ _ cs (fun c _ => weighted_symm blocks W _ _)
  self_nonneg := fun u => sum_nonnegative _ cs hw
    (fun c hc => P.square_insertion_nonnegative (u.val c.2) (u.property c hc))

private theorem summed_loss_cs (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (cs : List GramChannel)
    (hcw : ∀ c, c ∈ cs → (0 : Q') ≤ c.1)
    (u v : RatPoly → RatPoly)
    (hu : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (u c.2))
    (hv : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (v c.2)) :
    let B := fun (a b : RatPoly → RatPoly) => channelSum cs (fun z =>
      heatLossPair n w K (List.range n) (a z) (b z))
    B u v*B u v ≤ B u u*B v v := by
  dsimp only
  let P := productHeatCertificate n hw0 hw1 K hK (List.range n)
    (fun i hi => List.mem_range.mp hi)
  let D := channelWeightedGNSData (n+n) (productHeat n w K (List.range n)) P cs hcw
  let U : D.V := ⟨fun z => jump n (u z), fun c hc => jump_supported (hu c hc)⟩
  let V : D.V := ⟨fun z => jump n (v z), fun c hc => jump_supported (hv c hc)⟩
  let B := fun (a b : RatPoly → RatPoly) => channelSum cs (fun z =>
    heatLossPair n w K (List.range n) (a z) (b z))
  have pin (a b : RatPoly → RatPoly)
      (ha : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (a c.2))
      (hb : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (b c.2)) :
      channelSum cs (fun z => weightedPair (n+n) (productHeat n w K (List.range n))
        (jump n (a z)) (jump n (b z))) ≈ 2*B a b :=
    Q'.eqv_trans _ _ _ (channelSum_congr _ _ cs (fun c hc =>
      jump_heatLoss_pin n w K (List.range n) (CayleyParentInj.range_nodup n)
        (fun i hi => List.mem_range.mp hi) _ _ (ha c hc) (hb c hc)))
      (channelSum_smul _ 2 cs)
  have hc := D.cauchy_schwarz U V
  have hl := Q'.eqv_trans _ _ _ (qmul (pin u v hu hv) (pin u v hu hv))
    (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.const 4) (.mul (.var 0) (.var 0))) (by decide) (fun _ => B u v))
  have hr := Q'.eqv_trans _ _ _ (qmul (pin u u hu hu) (pin v v hv hv))
    (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
      (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => B u u | _ => B v v))
  apply Q'.le_of_mul_le_mul_left (c := 4) _ (by decide)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv hr))

private theorem summed_raw_mismatch (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (cs : List GramChannel)
    (hcw : ∀ c, c ∈ cs → (0 : Q') ≤ c.1) (b : RatPoly → RatPoly)
    (hb : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (b c.2))
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    let R := channelSum cs (fun z => rawSourceMoment n (b z) p)
    let S := channelSum cs (fun z => sourceMoment n w K (List.range n) (b z) p)
    let L := channelSum cs (fun z => heatLossPair n w K (List.range n) (b z) (b z))
    (R-S)*(R-S) ≤ L*channelSum cs (fun z => H n
      (polyMul (polyMul (b z) p) (polyMul (b z) p))) := by
  dsimp only
  let v := fun z => polyMul (b z) p
  let L := channelSum cs (fun z => heatLossPair n w K (List.range n) (b z) (b z))
  have hv : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (v c.2) :=
    fun c hc => supported_polyMul (hb c hc) hp
  have hl : (0 : Q') ≤ L := sum_nonnegative _ cs hcw (fun c hc =>
    heatLossPair_nonnegative n hw0 hw1 K hK (List.range n) (CayleyParentInj.range_nodup n)
      (fun i hi => List.mem_range.mp hi) _ (hb c hc))
  have hpin :
      channelSum cs (fun z => rawSourceMoment n (b z) p)-
        channelSum cs (fun z => sourceMoment n w K (List.range n) (b z) p) ≈
      channelSum cs (fun z => heatLossPair n w K (List.range n) (b z) (v z)) :=
    Q'.eqv_trans _ _ _
      (sum_sub cs (fun z => rawSourceMoment n (b z) p)
        (fun z => sourceMoment n w K (List.range n) (b z) p)).symm
      (channelSum_congr _ _ cs (fun c hc => rawMoment_difference_pin n w K (List.range n)
        (fun i hi => List.mem_range.mp hi) (b c.2) p (hb c hc) hp))
  have hc := summed_loss_cs n hw0 hw1 K hK cs hcw b v hb hv
  have hd : channelSum cs (fun z => heatLossPair n w K (List.range n) (v z) (v z)) ≤
      channelSum cs (fun z => H n (polyMul (v z) (v z))) :=
    channelSum_le _ _ cs hcw (fun c hc =>
      heatLossPair_le_haar n w (Q'.le_of_lt hw0) K (List.range n)
        (fun i hi => List.mem_range.mp hi) (v c.2) (hv c hc))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (qmul hpin hpin))
    (Q'.le_trans' _ _ _ hc (Q'.mul_le_mul_of_nonneg_left _ _ L hd hl))

/-- Raw centered square in the SAME actual original channels; the center is
the original interacting mean, not a channel or raw-source mean. -/
def centeredChannelSquare {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let psi := oddCentered hw0 hw1 K width hK depth f
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun c => rawSourceMoment (N width)
      (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) c)
      (polyMul psi psi))

/-- Original raw channel mass minus the SAME original partition. -/
def channelHeatLoss (w : Q') (K width depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  squareChannelMass w K scale width hwidth (terminalMessage w K width depth)-
    oddMass w K width depth

private theorem mass_loss_pin (w : Q') (K width depth scale : Nat)
    (hwidth : side scale < width) :
    channelHeatLoss w K width depth scale hwidth ≈
      channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
        (fun z => heatLossPair (N width) w K (List.range (N width))
          (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) z)
          (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) z)) := by
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth (terminalMessage w K width depth)
  have hb (c : GramChannel) (hc : c ∈ cs) := squareChannelSource_supported w K scale width
    hwidth _ (terminalMessage_supported w K width depth) c hc
  have hm : channelSum cs (fun z => rawSourceMoment (N width) (b z) polyOne) ≈
      squareChannelMass w K scale width hwidth (terminalMessage w K width depth) :=
    channelSum_congr _ _ cs (fun c _ => haar_of_coeff (RatPolyCoeffEqv.mul_one _))
  have hz : channelSum cs (fun z => sourceMoment (N width) w K (List.range (N width))
      (b z) polyOne) ≈ oddMass w K width depth :=
    Q'.eqv_trans _ _ _
      (oddMoment_eq_square_channels scale width hwidth w K depth polyOne (supported_one _)
        (fun i _ => quaternionBlockIndependent_polyOne i)
        (fun i _ => quaternionBlockIndependent_polyOne i)).symm
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _))
        (mass_oddMass w K width depth))
  have hpair : channelSum cs (fun z =>
      rawSourceMoment (N width) (b z) polyOne-
        sourceMoment (N width) w K (List.range (N width)) (b z) polyOne) ≈
      channelSum cs (fun z => heatLossPair (N width) w K (List.range (N width))
        (b z) (b z)) := channelSum_congr _ _ cs (fun c hc =>
    Q'.eqv_trans _ _ _ (rawMoment_difference_pin (N width) w K (List.range (N width))
      (fun i hi => List.mem_range.mp hi) (b c.2) polyOne (hb c hc) (supported_one _))
      (Q'.add_eqv_congr' (haar_of_coeff (blocks := N width)
        ((RatPolyCoeffEqv.mul_one (b c.2)).mul_left (b c.2)))
        (Q'.neg_eqv_congr _ _ (haar_of_coeff (blocks := N width)
          ((productMap_congr (N width) w K (List.range (N width))
            (RatPolyCoeffEqv.mul_one (b c.2))).mul_left (b c.2))))))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hm.symm (Q'.neg_eqv_congr _ _ hz.symm))
    (Q'.eqv_trans _ _ _ (sum_sub cs _ _).symm hpair)

/-- Nonnegativity is proved on the actual full heat of each original channel. -/
theorem paddedSquare_channel_heatLoss_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    (0 : Q') ≤ channelHeatLoss w K width depth scale hwidth := by
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth (terminalMessage w K width depth)
  have h : (0 : Q') ≤ channelSum cs (fun z =>
      heatLossPair (N width) w K (List.range (N width)) (b z) (b z)) :=
    sum_nonnegative
    (fun z => heatLossPair (N width) w K (List.range (N width)) (b z) (b z)) cs
    (productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K
      (spectatorBlocks scale width hwidth))
    (fun c hc => heatLossPair_nonnegative (N width) hw0 hw1 K hK (List.range (N width))
      (CayleyParentInj.range_nodup (N width)) (fun i hi => List.mem_range.mp hi) _
      (squareChannelSource_supported w K scale width hwidth _
        (terminalMessage_supported w K width depth) c hc))
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (mass_loss_pin w K width depth scale hwidth))

/-- The actual raw-channel / OWN-variance mismatch is bounded in the smaller
active heat mass loss, with the perimeter-independent cap sixteen. -/
theorem paddedSquare_channel_variance_loss_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let A := centeredChannelSquare hw0 hw1 K width hK depth scale hwidth
    let V := oddMass w K width depth*oddVariance hw0 hw1 K width hK depth f
    (A-V)*(A-V) ≤ 16*channelHeatLoss w K width depth scale hwidth*A := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let psi := oddCentered hw0 hw1 K width hK depth f
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth (terminalMessage w K width depth)
  let A := centeredChannelSquare hw0 hw1 K width hK depth scale hwidth
  let L := channelHeatLoss w K width depth scale hwidth
  let V := oddMass w K width depth*oddVariance hw0 hw1 K width hK depth f
  have hf := (paddedSquareSquareBound scale width hwidth).support
  have hp := oddCentered_supported hw0 hw1 K width hK depth hf
  have hfr : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i psi :=
    fun i hi => oddCentered_independent hw0 hw1 K width hK depth i
      (paddedSquare_fringe_independent scale width hwidth i hi)
  have hsp : ∀ i, i ∈ spectatorBlocks scale width hwidth → QuaternionBlockIndependent i psi :=
    fun i hi => oddCentered_independent hw0 hw1 K width hK depth i
      (sourceCharacter_spectator_independent_allSpin scale width hwidth i hi 1)
  have hb (c : GramChannel) (hc : c ∈ cs) := squareChannelSource_supported w K scale width
    hwidth _ (terminalMessage_supported w K width depth) c hc
  have hs : channelSum cs (fun z => sourceMoment (N width) w K (List.range (N width))
      (b z) (polyMul psi psi)) ≈ V :=
    Q'.eqv_trans _ _ _
      (oddMoment_eq_square_channels scale width hwidth w K depth (polyMul psi psi)
        (supported_polyMul hp hp)
        (fun i hi => quaternionBlockIndependent_polyMul (hfr i hi) (hfr i hi))
        (fun i hi => quaternionBlockIndependent_polyMul (hsp i hi) (hsp i hi))).symm
      (Q'.eqv_trans _ _ _
        (oddMoment_projected_source w K width depth (polyMul psi psi)
          (supported_polyMul hp hp)
          (fun i hi => quaternionBlockIndependent_polyMul (hfr i hi) (hfr i hi)))
        (centered_source_square hw0 hw1 K width hK depth hf
          (paddedSquare_fringe_independent scale width hwidth)))
  have hw := productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K
    (spectatorBlocks scale width hwidth)
  have hc := summed_raw_mismatch (N width) hw0 hw1 K hK cs hw b hb
    (polyMul psi psi) (supported_polyMul hp hp)
  have hfour : channelSum cs (fun z => H (N width)
      (polyMul (polyMul (b z) (polyMul psi psi))
        (polyMul (b z) (polyMul psi psi)))) ≤
      channelSum cs (fun z => 16*H (N width)
        (polyMul (polyMul (b z) psi) (polyMul (b z) psi))) :=
    channelSum_le _ _ cs hw (fun c hc =>
      paddedSquare_centered_fourth_le_sixteen_second hw0 hw1 K width hK depth scale hwidth
        (b c.2) (hb c hc))
  have hsecond : channelSum cs (fun z => H (N width)
      (polyMul (polyMul (b z) psi) (polyMul (b z) psi))) ≈ A :=
    channelSum_congr _ _ cs (fun c _ => haar_of_coeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => b c.2 | _ => psi)))
  have hcap : channelSum cs (fun z => H (N width)
      (polyMul (polyMul (b z) (polyMul psi psi))
        (polyMul (b z) (polyMul psi psi)))) ≤ 16*A :=
    Q'.le_trans' _ _ _ hfour (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (channelSum_smul _ 16 cs) (Q'.mul_eqv_congr_left 16 _ _ hsecond)))
  have hL := mass_loss_pin w K width depth scale hwidth
  have hln := paddedSquare_channel_heatLoss_nonnegative hw0 hw1 K width hK depth scale hwidth
  have hleft := qmul (Q'.add_eqv_congr' (Q'.eqv_refl A) (Q'.neg_eqv_congr _ _ hs.symm))
    (Q'.add_eqv_congr' (Q'.eqv_refl A) (Q'.neg_eqv_congr _ _ hs.symm))
  have hright : L*(16*A) ≈ 16*L*A :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 16) (.var 1)))
      (.mul (.mul (.const 16) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => L | _ => A)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hc (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hL.symm))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ L hcap hln)
        (Q'.le_of_eqv hright))))

#print axioms centeredChannelSquare
#print axioms channelHeatLoss
#print axioms paddedSquare_channel_heatLoss_nonnegative
#print axioms paddedSquare_channel_variance_loss_bound

end YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss
