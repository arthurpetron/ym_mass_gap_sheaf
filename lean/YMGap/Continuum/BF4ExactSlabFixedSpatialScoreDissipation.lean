/-
# ORIGINAL finite score versus chronological normalized square loss

The literal Vbar^2*Gout^2-weighted conditional score is controlled by the
SAME original incoming and outgoing V-weighted squares. The auxiliary
incoming reciprocal degree and positive Young parameter are eliminated by
constructive rational order closure. The actual terminal mismatch remains:

 Zi*score + L*spatialCeiling*Zi*Bout
 <= L*spatialCeiling*(1+comparisonEta)*Zo*C.

Here L=relativeCap^2, C=ell[c^2], Bout=ell[(T c)^2], Zi=ell[a^2],
Zo=ell[(T a)^2]. No source norm or partition is divided. Outgoing degree
is arbitrary. This is an ordinary finite marginal estimate, not a bound
on the complete signed Taylor energy, an OS-form comparison, an RG map,
AF-uniform estimate or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation
import YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialScoreDissipation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection (spatialFringeMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
  (comparisonEta comparisonEta_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement (incomingNumerator)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise (lastStepRatioNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepOriginalDissipation
  (original_lastStep_projected_noise_variance_loss_le)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
  (costTolerance costTolerance_pos costTolerance_pays)
open YMGap.Constructive.RationalTail (finSum finSum_mul_const finSum_eqv_congr const_mul_finSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exactScoreAngularBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost (exactScoreSignedBulk)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
  (sixValue sixValue_mul_left sixValue_mono)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass

/-- One computed incoming degree pays both geometric errors. Its inputs
are nome, width and a positive scalar tolerance, never a source inverse. -/
def scoreDissipationCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) (d : Q') (hd : (0 : Q') < d) : Nat :=
  max (incomingScoreRelativeCutoff hw0 hw1 width d hd d)
    (PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
      ((1+Q'.recipPos d hd)*(stepCap w width*stepCap w width)) d)

private theorem score_loss_with_error (Zi Zo C Bout L V xi score noise d err : Q')
    (hZi : (0 : Q') ≤ Zi) (hL : (0 : Q') ≤ L)
    (hV : (0 : Q') ≤ V) (hC : (0 : Q') ≤ C)
    (hscore : score ≤ (1+d)*(L*noise)+d*C)
    (hloss : Zi*((1+d)*noise+V*Bout) ≤
      V*((((1+d)*(1+xi))*Zo+err*Zi)*C))
    (herr : err ≤ d) :
    Zi*score+L*V*Zi*Bout ≤
      L*V*(1+xi)*Zo*C+d*(L*V*(1+xi)*Zo*C+(L*V+1)*Zi*C) := by
  have herror := Q'.mul_le_mul_of_nonneg_right _ _ Zi herr hZi
  have herror' := Q'.add_le_add_left (((1+d)*(1+xi))*Zo) _ _ herror
  have hloss' := Q'.le_trans' _ _ _ hloss
    (Q'.mul_le_mul_of_nonneg_left _ _ V
      (Q'.mul_le_mul_of_nonneg_right _ _ C herror' hC) hV)
  have h1 := Q'.add_le_add_right _ _ (L*V*Zi*Bout)
    (Q'.mul_le_mul_of_nonneg_left _ _ Zi hscore hZi)
  have h2 := Q'.add_le_add_right _ _ (d*Zi*C)
    (Q'.mul_le_mul_of_nonneg_left _ _ L hloss' hL)
  have hleft : Zi*((1+d)*(L*noise)+d*C)+L*V*Zi*Bout ≈
      L*(Zi*((1+d)*noise+V*Bout))+d*Zi*C :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.add (.const 1) (.var 1))
        (.mul (.var 2) (.var 3))) (.mul (.var 1) (.var 4))))
        (.mul (.mul (.mul (.var 2) (.var 5)) (.var 0)) (.var 6)))
      (.add (.mul (.var 2) (.mul (.var 0)
        (.add (.mul (.add (.const 1) (.var 1)) (.var 3))
          (.mul (.var 5) (.var 6))))) (.mul (.mul (.var 1) (.var 0)) (.var 4)))
      (by decide) (fun
        | 0 => Zi | 1 => d | 2 => L | 3 => noise | 4 => C | 5 => V | _ => Bout)
  have hright : L*(V*((((1+d)*(1+xi))*Zo+d*Zi)*C))+d*Zi*C ≈
      L*V*(1+xi)*Zo*C+d*(L*V*(1+xi)*Zo*C+(L*V+1)*Zi*C) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1)
        (.mul (.add (.mul (.mul (.add (.const 1) (.var 2))
          (.add (.const 1) (.var 3))) (.var 4)) (.mul (.var 2) (.var 5))) (.var 6))))
        (.mul (.mul (.var 2) (.var 5)) (.var 6)))
      (.add (.mul (.mul (.mul (.mul (.var 0) (.var 1))
        (.add (.const 1) (.var 3))) (.var 4)) (.var 6))
        (.mul (.var 2) (.add
          (.mul (.mul (.mul (.mul (.var 0) (.var 1))
            (.add (.const 1) (.var 3))) (.var 4)) (.var 6))
          (.mul (.mul (.add (.mul (.var 0) (.var 1)) (.const 1)) (.var 5)) (.var 6)))))
      (by decide) (fun
        | 0 => L | 1 => V | 2 => d | 3 => xi | 4 => Zo | 5 => Zi | _ => C)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hright)))

/-- The literal ORIGINAL output score is paid by chronological normalized
square loss, retaining the constructed terminal mismatch. Incoming degree
and Young overhead are absent, and outgoing reciprocal degree is arbitrary.
This does not estimate either signed Taylor remainder or an OS norm. -/
theorem original_lastStep_score_dissipation_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    (s : Nat) (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (l : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let c := incomingNumerator w K width n r psi
    let b := transferStep w K width c
    let Zi := weightedMass w K width (polyMul a a)
    let Zo := weightedMass w K width (polyMul A A)
    let C := weightedMass w K width (polyMul c c)
    let Bout := weightedMass w K width (polyMul b b)
    let L := relativeCap w 32*relativeCap w 32
    let V := spatialCeiling w width
    let xi := comparisonEta hw0 hw1 width (n+r-1)
    let Vbar := spatialFringeMass w K width
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
    let S := conditionalScore (4*s+i) (4*s+j) A b
    Zi*quaternionHaar (N width)
        (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G)) (polyMul S S))+
      L*V*Zi*Bout ≤ L*V*(1+xi)*Zo*C := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let c := incomingNumerator w K width n r psi
  let b := transferStep w K width c
  let Zi := weightedMass w K width (polyMul a a)
  let Zo := weightedMass w K width (polyMul A A)
  let C := weightedMass w K width (polyMul c c)
  let Bout := weightedMass w K width (polyMul b b)
  let L := relativeCap w 32*relativeCap w 32
  let V := spatialCeiling w width
  let xi := comparisonEta hw0 hw1 width (n+r-1)
  let Vbar := spatialFringeMass w K width
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
  let S := conditionalScore (4*s+i) (4*s+j) A b
  let score := quaternionHaar (N width)
    (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G)) (polyMul S S))
  have ha : SupportedQuaternionBlocks (N width) a := terminalMessage_supported w K width (n+r)
  have hA : SupportedQuaternionBlocks (N width) A :=
    transferStep_supported w K width ha
  have hc : SupportedQuaternionBlocks (N width) c :=
    iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
      r (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have hZi : (0 : Q') ≤ Zi := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square a ha)
  have hZo : (0 : Q') ≤ Zo := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square A hA)
  have hC : (0 : Q') ≤ C := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square c hc)
  have hL : (0 : Q') ≤ L := SumOfSquares.q_mul_self_nonneg (relativeCap w 32)
  have hV : (0 : Q') ≤ V :=
    (spatialInterval hw0 hw1 0 width (N width) (Nat.le_refl _)).nonnegative
  have hxi : (0 : Q') ≤ 1+xi :=
    Q'.zero_le_add _ _ Q'.zero_le_one (comparisonEta_nonnegative hw0 hw1 width (n+r-1))
  let target := L*V*(1+xi)*Zo*C
  have htarget : (0 : Q') ≤ target := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hL hV) hxi) hZo) hC
  let cost := target+(L*V+1)*Zi*C
  have hcost : (0 : Q') ≤ cost := Q'.zero_le_add _ _ htarget
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hL hV) Q'.zero_le_one) hZi) hC)
  change Zi*score+L*V*Zi*Bout ≤ target
  apply Q'.le_of_le_add_mul_invSucc _ _ 1
  intro precision
  let epsilon := Q'.invSucc precision
  let d := costTolerance cost hcost epsilon
  have hd : (0 : Q') < d := costTolerance_pos cost hcost epsilon (Q'.invSucc_pos precision)
  let k := scoreDissipationCutoff hw0 hw1 width d hd
  have hkin : incomingScoreRelativeCutoff hw0 hw1 width d hd d ≤ k :=
    Nat.le_max_left _ _
  have hkgeo : PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
      ((1+Q'.recipPos d hd)*(stepCap w width*stepCap w width)) d ≤ 2*k := by
    have hmax : PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
        ((1+Q'.recipPos d hd)*(stepCap w width*stepCap w width)) d ≤ k :=
      Nat.le_max_right _ _
    omega
  let noise := quaternionHaar (N width) (polyMul (polyMul Vbar Vbar)
    (lastStepRatioNoise w K width (n+r)
      (blockConditionalRatio hw0 hw1 K width hhead n r psi k)))
  have hscore : score ≤ (1+d)*(L*noise)+d*C :=
    original_lastStep_incomingRatio_relative_score_tolerance hw0 hw1 K width hK
      n r hdepth s hs hi hj hpsi d hd d hd k l hkin
  let err := (1+Q'.recipPos d hd)*
    ((mixRate hw0 hw1 width)^(2*k)*(stepCap w width*stepCap w width))
  have hloss : Zi*((1+d)*noise+V*Bout) ≤
      V*((((1+d)*(1+xi))*Zo+err*Zi)*C) :=
    original_lastStep_projected_noise_variance_loss_le hw0 hw1 K width hhead
      n r hdepth hpsi k d hd
  have hgeo := PositiveContractionResidual.geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    (Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt (Q'.recipPos_pos d hd)))
      (SumOfSquares.q_mul_self_nonneg (stepCap w width))) hd (2*k) hkgeo
  have herr : err ≤ d := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => 1+Q'.recipPos d hd
           | 1 => (mixRate hw0 hw1 width)^(2*k)
           | _ => stepCap w width*stepCap w width))) hgeo
  have h := score_loss_with_error Zi Zo C Bout L V xi score noise d err
    hZi hL hV hC hscore hloss herr
  have hpay : d*cost ≤ epsilon :=
    costTolerance_pays cost hcost epsilon (Q'.le_of_lt (Q'.invSucc_pos precision))
  exact Q'.le_trans' _ _ _ h (Q'.add_le_add_left target _ _
    (Q'.le_trans' _ _ _ hpay (Q'.ge_of_eqv (Q'.one_mul_eqv epsilon))))

/-- Literal six planes for each actual active block, not the total number
of coordinates and not a hidden volume-independent constant. -/
def activePlaneCount (width : Nat) : Q' :=
  finSum (fun s => if s ∈ activeBlocks width then (6 : Q') else 0) (N width)

private theorem six_constant (c : Q') : sixValue (fun _ _ => c) ≈ 6*c := by
  unfold sixValue
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 0) (.add (.var 0) (.add (.var 0) (.add (.var 0) (.var 0))))))
    (.mul (.const 6) (.var 0)) (by decide) (fun _ => c)

private theorem fin_mono (f g : Nat → Q') (h : ∀ s, f s ≤ g s) :
    ∀ m, finSum f m ≤ finSum g m
  | 0 => Q'.le_refl' _
  | m+1 => Q'.add_le_add (fin_mono f g h m) (h m)

private theorem terminal_output (w : Q') (K width n r : Nat) :
    transferStep w K width (terminalMessage w K width (n+r)) =
      terminalMessage w K width (n+(r+1)) :=
  (terminalMessage_next w K width (n+r)).trans
    (congrArg (terminalMessage w K width) (by omega))

private theorem source_output (w : Q') (K width n r : Nat) (psi : RatPoly) :
    transferStep w K width (incomingNumerator w K width n r psi) =
      originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi) := by
  simpa only [incomingNumerator, originalBlockTransfer, transferStep,
    SU2QuaternionHeadChainComposition.iterateStep] using
    (BF4ExactSlabFixedSpatialMiddlePairing.iterateStep_add (N width)
      (BF4ExactSlabFixedSpatialKineticHeat.kineticWeight w K width)
      (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width) r 1
      (polyMul (terminalMessage w K width n) psi)).symm

/-- The actual complete score budget is controlled in corrected original
norm-loss units. Six planes, actual active blocks and (1+sigma) remain.
Neither the raw norm loss nor a signed Taylor remainder is assumed positive. -/
theorem exactScoreAngularBudget_dissipation_le (sigma : Q')
    (hsigma : (0 : Q') ≤ sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (l : Nat) :
    let a := terminalMessage w K width (n+r)
    let A := terminalMessage w K width (n+(r+1))
    let c := incomingNumerator w K width n r psi
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let Zi := weightedMass w K width (polyMul a a)
    let Zo := weightedMass w K width (polyMul A A)
    let Cin := weightedMass w K width (polyMul c c)
    let Bout := weightedMass w K width (polyMul b b)
    let H := (relativeCap w 32*relativeCap w 32)*spatialCeiling w width
    let D := H*(1+comparisonEta hw0 hw1 width (n+r-1))*Zo*Cin + -(H*Zi*Bout)
    Zi*exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi l ≤
      activePlaneCount width*((1+sigma)*D) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let A := terminalMessage w K width (n+(r+1))
  let c := incomingNumerator w K width n r psi
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let Zi := weightedMass w K width (polyMul a a)
  let Zo := weightedMass w K width (polyMul A A)
  let Cin := weightedMass w K width (polyMul c c)
  let Bout := weightedMass w K width (polyMul b b)
  let H := (relativeCap w 32*relativeCap w 32)*spatialCeiling w width
  let D := H*(1+comparisonEta hw0 hw1 width (n+r-1))*Zo*Cin + -(H*Zi*Bout)
  let Vbar := spatialFringeMass w K width
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
  let F := 1+sigma
  let Q := fun s i j => quaternionHaar (N width)
    (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
      (polyMul (conditionalScore (4*s+i) (4*s+j) A b)
        (conditionalScore (4*s+i) (4*s+j) A b)))
  let row := fun s => if s ∈ activeBlocks width then sixValue (fun i j => F*Q s i j) else 0
  let count := fun s => if s ∈ activeBlocks width then (6 : Q') else 0
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one hsigma
  have hrow : ∀ s, Zi*row s ≤ count s*(F*D) := by
    intro s
    by_cases hs : s ∈ activeBlocks width
    · change Zi*(if s ∈ activeBlocks width then sixValue (fun i j => F*Q s i j) else 0) ≤
        (if s ∈ activeBlocks width then (6 : Q') else 0)*(F*D)
      simp only [if_pos hs]
      have hp : ∀ i j, i < 4 → j < 4 → Zi*(F*Q s i j) ≤ F*D := by
        intro i j hi hj
        have h := original_lastStep_score_dissipation_le hw0 hw1 K width hK
          n r hdepth s hs hi hj hpsi l
        dsimp only at h
        rw [terminal_output w K width n r, source_output w K width n r psi] at h
        have hraw : Zi*Q s i j ≤ D := by
          have hadd := Q'.add_le_add_right _ _ (-(H*Zi*Bout)) h
          have hcanc : (Zi*Q s i j+H*Zi*Bout)+ -(H*Zi*Bout) ≈ Zi*Q s i j :=
            poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
              (.var 0) (by decide) (fun | 0 => Zi*Q s i j | _ => H*Zi*Bout)
          exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcanc) hadd
        have hm := Q'.mul_le_mul_of_nonneg_left _ _ F hraw hF
        have hid : Zi*(F*Q s i j) ≈ F*(Zi*Q s i j) :=
          poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
            (fun | 0 => Zi | 1 => F | _ => Q s i j)
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) hm
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (sixValue_mul_left Zi _))
        (Q'.le_trans' _ _ _ (sixValue_mono _ _ hp) (Q'.le_of_eqv (six_constant (F*D))))
    · simp only [row, count, if_neg hs]
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv Zi))
        (Q'.ge_of_eqv (Q'.zero_mul_eqv (F*D)))
  have hsum := fin_mono (fun s => Zi*row s) (fun s => count s*(F*D)) hrow (N width)
  change Zi*finSum row (N width) ≤ finSum count (N width)*(F*D)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (const_mul_finSum row Zi (N width)))
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (finSum_mul_const count (F*D) (N width))))

/-- Actual SAME signed bulk consumer. The paired Taylor remainder remains
LITERAL and SIGNED; no smallness or sign is asserted for it. Its outer Zo
and the incoming Zi are retained, not identified with a Rayleigh denominator. -/
theorem exactScoreSignedBulk_dissipation_le (sigma : Q')
    (hsigma : (0 : Q') ≤ sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (l : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := terminalMessage w K width (n+(r+1))
    let c := incomingNumerator w K width n r psi
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let Zi := weightedMass w K width (polyMul a a)
    let Zo := weightedMass w K width (polyMul A A)
    let Cin := weightedMass w K width (polyMul c c)
    let Bout := weightedMass w K width (polyMul b b)
    let H := (relativeCap w 32*relativeCap w 32)*spatialCeiling w width
    let D := H*(1+comparisonEta hw0 hw1 width (n+r-1))*Zo*Cin + -(H*Zi*Bout)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi l
    let q := projectedEndpointSource w K width A
    let R := pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
      -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))
    Zi*exactScoreSignedBulk sigma hw0 hw1 K width hK n r psi l ≤
      Zo*((1-w)*(activePlaneCount width*((1+sigma)*D))+Zi*R) := by
  dsimp only
  let Zi := weightedMass w K width
    (polyMul (terminalMessage w K width (n+r)) (terminalMessage w K width (n+r)))
  let Zo := weightedMass w K width
    (polyMul (terminalMessage w K width (n+(r+1))) (terminalMessage w K width (n+(r+1))))
  have hZo : (0 : Q') ≤ Zo := weightedMass_nonnegative hw0 hw1 K width
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK)
    (Certificate.square _ (terminalMessage_supported w K width (n+(r+1))))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (1-w)
    (exactScoreAngularBudget_dissipation_le sigma hsigma hw0 hw1 K width hK
      n r hdepth hpsi l) (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  unfold exactScoreSignedBulk
  have hid (B R : Q') : Zi*(Zo*((1-w)*B+R)) ≈ Zo*((1-w)*(Zi*B)+Zi*R) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 2) (.var 3)) (.var 4))))
      (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 0) (.var 3))) (.mul (.var 0) (.var 4))))
      (by decide) (fun | 0 => Zi | 1 => Zo | 2 => 1-w | 3 => B | _ => R)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (hid _ _))
    (Q'.mul_le_mul_of_nonneg_left _ _ Zo (Q'.add_le_add_right _ _ _ h) hZo)

end YMGap.Continuum.BF4ExactSlabFixedSpatialScoreDissipation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialScoreDissipation.scoreDissipationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialScoreDissipation.original_lastStep_score_dissipation_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialScoreDissipation.activePlaneCount
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialScoreDissipation.exactScoreAngularBudget_dissipation_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialScoreDissipation.exactScoreSignedBulk_dissipation_le
