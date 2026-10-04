/-
# Linear passive-channel credit for the ACTUAL padded Wilson square

The original fundamental long Wilson word, not a spatial-face surrogate, is
inserted in the actual passive channel moment.  The late endpoint source is
compared to one fringe-projected local spectator.  Its lower and upper bands
share the same selected-link list and the same original terminal message.
The primary estimate concerns the raw second moment; OWN odd variance follows
without changing the original law or center.  This is a fixed-parameter
finite statement, not a scaling or chronological-window estimate.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
import YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
  (spectator spectator_supported spectator_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
  (localLower localUpper localLower_positive localUpper_positive
    endpoint_localLowerCertificate endpoint_localUpperCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds
  (projectedSource_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
  (original_variance_le_projected_square channelObservableSquareLinearVarianceCredit)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
  (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polySmul
    quaternionBlockIndependent_polyOne)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels (channelSource)
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization (channelSquare)
open YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand
  (channelSquare_sourceMoment_linear_band)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass oddVariance

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private theorem project_smul (ids : List Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polySmul c p))
      (polySmul c (familyProject ids p)) :=
  (familyProject_congr ids (cap_mul_left c p).symm).trans
    ((familyProject_mul_of_independent ids (cap c) p
      (fun i _ => quaternionBlockIndependent_polySmul c
        (quaternionBlockIndependent_polyOne i))).trans (cap_mul_left c _))

private def selectedLinks (scale width : Nat) (hwidth : side scale < width) :=
  (paddedSquare scale width hwidth).edges.map (fun e => e.link)

private def projectedSpectator (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (n : Nat) : RatPoly :=
  familyProject (fringeBlocks width)
    (spectator w K width n (selectedLinks scale width hwidth))

private theorem selectedLinks_length (scale width : Nat)
    (hwidth : side scale < width) :
    (selectedLinks scale width hwidth).length = 4*side scale := by
  unfold selectedLinks
  rw [List.length_map, paddedSquare_edges, square_length]

private theorem projectedSpectator_supported (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedSpectator w K scale width hwidth n) :=
  familyProject_supported (fringeBlocks width)
    (spectator_supported w K width n (selectedLinks scale width hwidth))

private theorem projectedSpectator_outside_passive (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (n i : Nat)
    (hi : i < N width) (hnot : i ∉ spectatorBlocks scale width hwidth) :
    QuaternionBlockIndependent i (projectedSpectator w K scale width hwidth n) := by
  have hcover := spectator_observable_cover scale width hwidth
  have hactive : i ∈ observableBlocks scale width hwidth :=
    (List.mem_append.mp (hcover.mem_iff.mpr (List.mem_range.mpr hi))).resolve_left hnot
  have hslot : i ∈ loopSlots scale width hwidth :=
    of_decide_eq_true (List.mem_filter.mp hactive).2
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hslot
  subst i
  have hselected : e.link ∈ selectedLinks scale width hwidth :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  have hphysical : e.link ∈ baseLinks width :=
    (paddedSquare scale width hwidth).physical e he
  exact familyProject_preserves_independent (fringeBlocks width)
    (spectator_independent w K width n (selectedLinks scale width hwidth)
      e.link hselected hphysical)

private def projected_lowerCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K scale width : Nat)
    (hK : headCutoff w ≤ K) (hwidth : side scale < width) (n : Nat) :
    Certificate (N width) (polyAdd
      (projectedEndpointSource w K width (terminalMessage w K width (n+1)))
      (polyNeg (polySmul (localLower w (4*side scale))
        (projectedSpectator w K scale width hwidth n)))) := by
  let selected := selectedLinks scale width hwidth
  let a := polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width)
    (terminalMessage w K width (n+1))
  let R := spectator w K width n selected
  let l := localLower w (4*side scale)
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1))
  have hR := spectator_supported w K width n selected
  have C := endpoint_localLowerCertificate hw0 hw1 K width hK n selected
    (4*side scale) (Nat.le_of_eq (selectedLinks_length scale width hwidth))
  have CP := familyProject_certificate (N width) (fringeBlocks width)
    (fringeBlocks_lt width)
    (supported_add ha (support_neg (polySmul_supported hR l))) C
  have he : RatPolyCoeffEqv
      (familyProject (fringeBlocks width) (polyAdd a (polyNeg (polySmul l R))))
      (polyAdd (familyProject (fringeBlocks width) a)
        (polyNeg (polySmul l (familyProject (fringeBlocks width) R)))) := by
    rw [familyProject_add]
    exact (RatPolyCoeffEqv.refl _).add ((familyProject_neg _ _).trans
      (RatPolyCoeffEqv.neg (project_smul _ l R)))
  exact .ofCoeff he.symm CP

private def projected_upperCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K scale width : Nat)
    (hK : headCutoff w ≤ K) (hwidth : side scale < width) (n : Nat) :
    Certificate (N width) (polyAdd
      (polySmul (localUpper w (4*side scale))
        (projectedSpectator w K scale width hwidth n))
      (polyNeg (projectedEndpointSource w K width (terminalMessage w K width (n+1))))) := by
  let selected := selectedLinks scale width hwidth
  let a := polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width)
    (terminalMessage w K width (n+1))
  let R := spectator w K width n selected
  let u := localUpper w (4*side scale)
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1))
  have hR := spectator_supported w K width n selected
  have C := endpoint_localUpperCertificate hw0 hw1 K width hK n selected
    (4*side scale) (Nat.le_of_eq (selectedLinks_length scale width hwidth))
  have CP := familyProject_certificate (N width) (fringeBlocks width)
    (fringeBlocks_lt width)
    (supported_add (polySmul_supported hR u) (support_neg ha)) C
  have he : RatPolyCoeffEqv
      (familyProject (fringeBlocks width) (polyAdd (polySmul u R) (polyNeg a)))
      (polyAdd (polySmul u (familyProject (fringeBlocks width) R))
        (polyNeg (familyProject (fringeBlocks width) a))) := by
    rw [familyProject_add]
    exact (project_smul _ u R).add (familyProject_neg _ a)
  exact .ofCoeff he.symm CP

/-- The original long square's raw second moment pays its own passive
channel moment with just one factor from each actual endpoint band. -/
theorem paddedSquare_channelMoment_rawSecond_linear {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (scale width : Nat)
    (hwidth : side scale < width) (n : Nat) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
    let l := localLower w (4*side scale)
    let u := localUpper w (4*side scale)
    l*sourceMoment (N width) w K (List.range (N width)) q (polyMul f f) ≤
      u*squareChannelMoment w K scale width hwidth (terminalMessage w K width (n+1)) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  let R := projectedSpectator w K scale width hwidth n
  let passive := spectatorBlocks scale width hwidth
  let active := observableBlocks scale width hwidth
  let l := localLower w (4*side scale)
  let u := localUpper w (4*side scale)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width (n+1)))
  have hR := projectedSpectator_supported w K scale width hwidth n
  have CQ := projectedSource_certificate hw0 hw1 K width hK n
  have hl : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hu : (0 : Q') ≤ u := Q'.le_of_lt (localUpper_positive hw0 hw1 _)
  have hband := channelSquare_sourceMoment_linear_band hw0 hw1 K hK active passive
    (spectatorBlocks_nodup scale width hwidth)
    (spectatorBlocks_lt scale width hwidth)
    (spectator_observable_cover scale width hwidth)
    q R f hq hR hf CQ l u hl hu
    (projected_lowerCertificate hw0 hw1 K scale width hK hwidth n)
    (projected_upperCertificate hw0 hw1 K scale width hK hwidth n)
    (projectedSpectator_outside_passive w K scale width hwidth n)
    (fun i hi => sourceCharacter_spectator_independent scale width hwidth i hi)
  have hpin : squareChannelMoment w K scale width hwidth
      (terminalMessage w K width (n+1)) ≈
      channelSquare (N width) w K passive q (polyMul f f) := by
    unfold squareChannelMoment channelSquare squareChannelSource channelSource
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hband
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left u _ _ hpin.symm))

/-- The original OWN odd variance is bounded by its uncentered raw second
moment. This form is convenient for the chronological energy consumer. -/
theorem paddedSquare_channelMoment_oddVariance_linear_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (scale width : Nat)
    (hwidth : side scale < width) (n : Nat) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let l := localLower w (4*side scale)
    let u := localUpper w (4*side scale)
    l*(oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f) ≤
      u*squareChannelMoment w K scale width hwidth (terminalMessage w K width (n+1)) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let l := localLower w (4*side scale)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hvar := original_variance_le_projected_square hw0 hw1 K width hK
    (n+1) f hf (paddedSquare_fringe_independent scale width hwidth)
  have hl : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ l hvar hl)
    (paddedSquare_channelMoment_rawSecond_linear hw0 hw1 K hK scale width hwidth n)

/-- The existing computed linear scalar pays a portion of the SAME original
odd partition times OWN variance. No interacting moment is inverted. -/
theorem paddedSquare_channelMoment_oddVariance_credit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (scale width : Nat)
    (hwidth : side scale < width) (n : Nat) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale) *
      (oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f) ≤
      squareChannelMoment w K scale width hwidth (terminalMessage w K width (n+1)) := by
  dsimp only
  let l := localLower w (4*side scale)
  let u := localUpper w (4*side scale)
  let V := oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1)
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let Q := squareChannelMoment w K scale width hwidth (terminalMessage w K width (n+1))
  have hu : (0 : Q') < u := localUpper_positive hw0 hw1 _
  let r := Q'.recipPos u hu
  have h := Q'.mul_le_mul_of_nonneg_right _ _ r
    (paddedSquare_channelMoment_oddVariance_linear_cleared
      hw0 hw1 K hK scale width hwidth n)
    (Q'.le_of_lt (Q'.recipPos_pos u hu))
  have hleft : (l*V)*r ≈ channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale)*V :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => l | 1 => V | _ => r)
  have hright : (u*Q)*r ≈ Q := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => u | 1 => Q | _ => r))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ Q (Q'.mul_recipPos_eqv u hu))
      (Q'.one_mul_eqv Q))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

end YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit.paddedSquare_channelMoment_rawSecond_linear
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit.paddedSquare_channelMoment_oddVariance_linear_cleared
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit.paddedSquare_channelMoment_oddVariance_credit
