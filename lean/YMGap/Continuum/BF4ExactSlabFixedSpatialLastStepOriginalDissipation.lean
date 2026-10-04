/-
# Last-step innovation versus the ACTUAL source's variance decrement

The constructed incoming ratio and its error are joined to the original
source b=T c, not a substituted source T(a*phi_k). Both chronological
partitions and the nonnegative last-step innovation are retained:

 Zi*((1+delta)*ell(N_k)+ell(b^2))
 <= ((1+delta)*(1+eta)*Zo +
     (1+1/delta)*rho^(2k)*stepCap^2*Zi)*ell(c^2).

The same inequality pays the ACTUAL projected noise H[Vbar^2*N_k] with
the explicit spatialCeiling, never an identification Vbar^2=V.
Only the additional positive scalar delta is inverted in this comparison;
the constructed positive-window reciprocal is retained. The source may
be signed or have zero norm; its supplied center remains unchanged.
Zo=ell[(Ta)^2] is NOT the outgoing
Rayleigh denominator ell[(Ta)*T(Ta)]. This is finite norm-loss currency,
not a small loss rate, signed Taylor cancellation or continuum survival.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate spatialInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepCap transferStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle (weighted_square_add_le)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks kineticWeight spatialWeight weightedMass

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Exact reconstruction of the SAME original source, before the final T. -/
theorem incoming_source_reconstruction_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) :
    let a := terminalMessage w K width (n+r)
    let c := incomingNumerator w K width n r psi
    let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
    let e := incomingRatioError hw0 hw1 K width hK n r psi k
    RatPolyCoeffEqv c (polyAdd (polyMul a phi) e) :=
  coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.mul (.var 1) (.var 2))
      (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))))
    (by decide) (fun
      | 0 => incomingNumerator w K width n r psi
      | 1 => terminalMessage w K width (n+r)
      | _ => blockConditionalRatio hw0 hw1 K width hK n r psi k)

/-- Exact original outgoing source, with both finite reconstruction parts. -/
theorem outgoing_source_reconstruction_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) :
    let a := terminalMessage w K width (n+r)
    let c := incomingNumerator w K width n r psi
    let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
    let e := incomingRatioError hw0 hw1 K width hK n r psi k
    RatPolyCoeffEqv (transferStep w K width c)
      (polyAdd (transferStep w K width (polyMul a phi)) (transferStep w K width e)) :=
  (partialHaarHeads_congr (N width)
    (((incoming_source_reconstruction_pin hw0 hw1 K width hK n r psi k).mul_left
      (spatialWeight w K width)).mul_left (kineticWeight w K width))).trans
    (transferStep_add w K width _ _)

/-- A constructed inequality with the ACTUAL outgoing b=T c. The positive
last innovation is retained on the left, not discarded by a norm-only cap. -/
theorem original_lastStep_noise_variance_loss_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi)
    (k : Nat) (delta : Q') (hdelta : (0 : Q') < delta) :
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let c := incomingNumerator w K width n r psi
    let b := transferStep w K width c
    let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
    let Zi := weightedMass w K width (polyMul a a)
    let Zo := weightedMass w K width (polyMul A A)
    let eta := comparisonEta hw0 hw1 width (n+r-1)
    let v := (mixRate hw0 hw1 width)^(2*k)*(stepCap w width*stepCap w width)
    Zi*((1+delta)*weightedMass w K width (lastStepRatioNoise w K width (n+r) phi)+
        weightedMass w K width (polyMul b b)) ≤
      (((1+delta)*(1+eta))*Zo + (1+Q'.recipPos delta hdelta)*v*Zi)*
        weightedMass w K width (polyMul c c) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let c := incomingNumerator w K width n r psi
  let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
  let e := incomingRatioError hw0 hw1 K width hK n r psi k
  let bphi := transferStep w K width (polyMul a phi)
  let E := transferStep w K width e
  let Zi := weightedMass w K width (polyMul a a)
  let Zo := weightedMass w K width (polyMul A A)
  let B := weightedMass w K width (polyMul c c)
  let Bphi := weightedMass w K width (polyMul bphi bphi)
  let Bout := weightedMass w K width
    (polyMul (transferStep w K width c) (transferStep w K width c))
  let No := weightedMass w K width (lastStepRatioNoise w K width (n+r) phi)
  let F := (1 : Q')+delta
  let R := (1 : Q')+Q'.recipPos delta hdelta
  let H := (1 : Q')+comparisonEta hw0 hw1 width (n+r-1)
  let v := (mixRate hw0 hw1 width)^(2*k)*(stepCap w width*stepCap w width)
  have ha := terminalMessage_supported w K width (n+r)
  have hc : SupportedQuaternionBlocks (N width) c :=
    iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
      r (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have hp := blockConditionalRatio_supported hw0 hw1 K width hK n r hpsi k
  have he : SupportedQuaternionBlocks (N width) e :=
    supported_add hc (support_neg (supported_polyMul ha hp))
  have hZi : (0 : Q') ≤ Zi := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square a ha)
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt hdelta)
  have hR : (0 : Q') ≤ R := Q'.zero_le_add _ _ Q'.zero_le_one
    (Q'.le_of_lt (Q'.recipPos_pos delta hdelta))
  have hpin := outgoing_source_reconstruction_pin hw0 hw1 K width hK n r psi k
  have htri := weighted_square_add_le delta hdelta
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
    (transferStep_supported w K width (supported_polyMul ha hp))
    (transferStep_supported w K width he)
  have htri' : weightedMass w K width (polyMul (polyAdd bphi E) (polyAdd bphi E)) ≤
      F*Bphi+R*weightedMass w K width (polyMul E E) := by
    simpa only [weightedMass, bphi, E, F, R, Bphi] using htri
  have herr := incomingRatioError_transferred_square_le hw0 hw1 K width hK n r hdepth hpsi k
  have hBout : Bout ≤ F*Bphi+R*(v*B) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (weightedMass_congr w K width (hpin.mul hpin)))
      (Q'.le_trans' _ _ _ htri'
        (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ R herr hR)))
  have hsum := Q'.mul_le_mul_of_nonneg_left _ _ Zi
    (Q'.add_le_add_left (F*No) _ _ hBout) hZi
  have hnoise := Q'.mul_le_mul_of_nonneg_left _ _ F
    (lastStepRatioNoise_dissipation_cleared hw0 hw1 K width hK n r hdepth hpsi k) hF
  have heL : Zi*(F*No+(F*Bphi+R*(v*B))) ≈
      F*(Zi*(No+Bphi))+(R*v*Zi)*B :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
        (.add (.mul (.var 1) (.var 3)) (.mul (.var 4) (.mul (.var 5) (.var 6))))))
      (.add (.mul (.var 1) (.mul (.var 0) (.add (.var 2) (.var 3))))
        (.mul (.mul (.mul (.var 4) (.var 5)) (.var 0)) (.var 6)))
      (by decide) (fun | 0 => Zi | 1 => F | 2 => No | 3 => Bphi | 4 => R | 5 => v | _ => B)
  have heR : F*(H*(Zo*B))+(R*v*Zi)*B ≈ ((F*H)*Zo+R*v*Zi)*B :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.mul (.mul (.var 4) (.var 5)) (.var 6)) (.var 3)))
      (.mul (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 4) (.var 5)) (.var 6))) (.var 3))
      (by decide) (fun | 0 => F | 1 => H | 2 => Zo | 3 => B | 4 => R | 5 => v | _ => Zi)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv heL)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hnoise) (Q'.le_of_eqv heR)))

/-- SAME actual projected noise, paid through the original spatial ceiling.
Its original source and distinct chronological partitions are unchanged. -/
theorem original_lastStep_projected_noise_variance_loss_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi)
    (k : Nat) (delta : Q') (hdelta : (0 : Q') < delta) :
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let c := incomingNumerator w K width n r psi
    let b := transferStep w K width c
    let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
    let Zi := weightedMass w K width (polyMul a a)
    let Zo := weightedMass w K width (polyMul A A)
    let eta := comparisonEta hw0 hw1 width (n+r-1)
    let v := (mixRate hw0 hw1 width)^(2*k)*(stepCap w width*stepCap w width)
    let C := spatialCeiling w width
    let Vbar := spatialFringeMass w K width
    Zi*((1+delta)*quaternionHaar (N width) (polyMul (polyMul Vbar Vbar)
          (lastStepRatioNoise w K width (n+r) phi))+
        C*weightedMass w K width (polyMul b b)) ≤
      C*((((1+delta)*(1+eta))*Zo+(1+Q'.recipPos delta hdelta)*v*Zi)*
        weightedMass w K width (polyMul c c)) := by
  dsimp only
  let C := spatialCeiling w width
  let F := (1 : Q')+delta
  let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
  let Zi := weightedMass w K width
    (polyMul (terminalMessage w K width (n+r)) (terminalMessage w K width (n+r)))
  let No := weightedMass w K width (lastStepRatioNoise w K width (n+r) phi)
  let Bout := weightedMass w K width
    (polyMul (transferStep w K width (incomingNumerator w K width n r psi))
      (transferStep w K width (incomingNumerator w K width n r psi)))
  have hZi : (0 : Q') ≤ Zi := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square _ (terminalMessage_supported w K width (n+r)))
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt hdelta)
  have hC : (0 : Q') ≤ C :=
    (spatialInterval hw0 hw1 0 width (N width) (Nat.le_refl _)).nonnegative
  have hn := lastStepRatioNoise_projected_weight_le hw0 hw1 K width hK (n+r)
    (blockConditionalRatio_supported hw0 hw1 K width hK n r hpsi k)
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ Zi
    (Q'.add_le_add_right _ _ (C*Bout)
      (Q'.mul_le_mul_of_nonneg_left _ _ F hn hF)) hZi
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ C
    (original_lastStep_noise_variance_loss_le hw0 hw1 K width hK n r hdepth hpsi k delta hdelta) hC
  have he : Zi*(F*(C*No)+C*Bout) ≈ C*(Zi*(F*No+Bout)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 2) (.var 3)))
        (.mul (.var 2) (.var 4))))
      (.mul (.var 2) (.mul (.var 0) (.add (.mul (.var 1) (.var 3)) (.var 4))))
      (by decide) (fun | 0 => Zi | 1 => F | 2 => C | 3 => No | _ => Bout)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) h2)

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation.incoming_source_reconstruction_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation.outgoing_source_reconstruction_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation.original_lastStep_noise_variance_loss_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation.original_lastStep_projected_noise_variance_loss_le
