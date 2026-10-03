/-
# Actual projected-action angular bound for the finite block ratio

The original terminal fringe independence pins qbar=P_F(V*A) to Vbar*A.
The literal polynomial phi_k=G_k*b then has angular energy bounded by the
two actual Vbar^2-weighted derivative costs of b and A. All original blocks
and all six planes are summed. The constant is uniform in reciprocal degree
only: no replacement of Vbar^2 by V, variance comparison, useful changing-
family budget, boundary-drift sign, or survival conclusion is asserted.
-/

import YMGap.Continuum.QuaternionHaarReciprocalRatioGradientBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported step)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productMap productMap_independent_of_not_mem)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularSquare blockAngularDerivative)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap sumBound)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarReciprocalRatioGradientBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal remainder scale)
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse (corrector_independent)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairBudget)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage

/-- Exact projected ORIGINAL endpoint source, not a pointwise action replacement. -/
theorem projected_terminal_source_pin (w : Q') (K width depth : Nat) :
    RatPolyCoeffEqv
      (projectedEndpointSource w K width (terminalMessage w K width depth))
      (polyMul (spatialFringeMass w K width) (terminalMessage w K width depth)) := by
  unfold projectedEndpointSource endpointSource
  exact (familyProject_congr (fringeBlocks width)
    (RatPolyCoeffEqv.mul_comm _ _)).trans
    ((familyProject_mul_of_independent _ _ _ (terminal_fringe_independent w K width depth)).trans
      (RatPolyCoeffEqv.mul_comm _ _))

private theorem source_supported (w : Q') (K width n t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    t (supported_polyMul (terminalMessage_supported w K width n) hp)

private theorem projected_square_pin (w : Q') (K width depth : Nat) (d : RatPoly) :
    quaternionHaar (N width) (polyMul
      (polyMul (projectedEndpointSource w K width (terminalMessage w K width depth))
        (projectedEndpointSource w K width (terminalMessage w K width depth))) (polyMul d d)) ≈
    quaternionHaar (N width) (polyMul
      (polyMul (spatialFringeMass w K width) (spatialFringeMass w K width))
      (polyMul (polyMul (terminalMessage w K width depth) d)
        (polyMul (terminalMessage w K width depth) d))) := by
  have h := projected_terminal_source_pin w K width depth
  exact haar_of_coeff (((h.mul h).mul_right _).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (by decide) (fun
        | 0 => spatialFringeMass w K width
        | 1 => terminalMessage w K width depth
        | _ => d)))

/-- One original angular plane, with the SAME projected action squared on
both derivative costs; the reciprocal lower floor is absent from the bound. -/
theorem blockConditionalRatio_plane_gradient_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} {C : Q'} (I : Interval (N width) psi C)
    (i j : Nat) (hi : i < 4*N width) (hj : j < 4*N width) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let Vbar := spatialFringeMass w K width
    let qbar := projectedEndpointSource w K width A
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    quaternionHaar (N width) (polyMul (polyMul qbar qbar)
      (polyMul (angularDerivative i j phi) (angularDerivative i j phi))) ≤
      2*quaternionHaar (N width) (polyMul (polyMul Vbar Vbar)
        (polyMul (angularDerivative i j b) (angularDerivative i j b))) +
      (2*(C*C))*quaternionHaar (N width) (polyMul (polyMul Vbar Vbar)
        (polyMul (angularDerivative i j A) (angularDerivative i j A))) := by
  dsimp only
  have hb := source_supported w K width n t I.support
  have hwindow := blockWindowCertificates hw0 hw1 K width hK n t hdepth
  have hrelative := blockRelativeCertificates hw0 hw1 K width hK n t I
  have hbound := reciprocal_ratio_cleared_gradient_square_le hi hj
    (Certificate.square _ (spatialFringeMass_supported w K width))
    (terminalMessage_supported w K width (n+t)) hb
    (blockWindowUpper_positive hw0 hw1 K width hK n t)
    I.nonnegative (terminalMessage_certificate hw0 hw1 K width hK (n+t))
    hwindow.2 hrelative.1 hrelative.2 k
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (projected_square_pin w K width (n+t)
      (angularDerivative i j (blockConditionalRatio hw0 hw1 K width hK n t psi k)))) ?_
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0))
        (.add (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1))))
      (.add (.mul (.const 2) (.var 0)) (.mul (.mul (.const 2) (.var 2)) (.var 1)))
      (by decide) (fun
        | 0 => quaternionHaar (N width) (polyMul
            (polyMul (spatialFringeMass w K width) (spatialFringeMass w K width))
            (polyMul (angularDerivative i j
                (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)))
              (angularDerivative i j
                (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)))))
        | 1 => quaternionHaar (N width) (polyMul
            (polyMul (spatialFringeMass w K width) (spatialFringeMass w K width))
            (polyMul (angularDerivative i j (terminalMessage w K width (n+t)))
              (angularDerivative i j (terminalMessage w K width (n+t)))))
        | _ => C*C)))

private theorem sixValue_linear (a c : Q') (f g : Nat → Nat → Q') :
    sixValue (fun i j => a*f i j+c*g i j) ≈ a*sixValue f+c*sixValue g := by
  have hadd : sixValue (fun i j => a*f i j+c*g i j) ≈
      sixValue (fun i j => a*f i j)+sixValue (fun i j => c*g i j) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 6)) (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8)) (.add (.add (.var 3) (.var 9))
          (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
      (.add (.add (.var 0) (.add (.var 1) (.add (.var 2) (.add (.var 3) (.add (.var 4) (.var 5))))))
        (.add (.var 6) (.add (.var 7) (.add (.var 8) (.add (.var 9) (.add (.var 10) (.var 11)))))))
      (by decide) (fun
        | 0 => a*f 0 1 | 1 => a*f 0 2 | 2 => a*f 0 3
        | 3 => a*f 1 2 | 4 => a*f 1 3 | 5 => a*f 2 3
        | 6 => c*g 0 1 | 7 => c*g 0 2 | 8 => c*g 0 3
        | 9 => c*g 1 2 | 10 => c*g 1 3 | _ => c*g 2 3)
  exact Q'.eqv_trans _ _ _ hadd
    (Q'.add_eqv_congr' (Q'.eqv_symm (sixValue_mul_left a f))
      (Q'.eqv_symm (sixValue_mul_left c g)))

private theorem sum_linear_le (a c : Q') (f g v : Nat → Q') :
    (m : Nat) → (∀ i, i < m → v i ≤ a*f i+c*g i) →
      finSum v m ≤ a*finSum f m+c*finSum g m
  | 0, _ => by
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_zero_eqv a) (Q'.mul_zero_eqv c))
        (by decide : (0 : Q')+0 ≈ 0)))
  | m+1, h => by
      have hh := Q'.add_le_add
        (sum_linear_le a c f g v m (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self m))))
        (h m (Nat.lt_succ_self m))
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.add (.mul (.var 0) (.var 4)) (.mul (.var 2) (.var 5))))
          (.add (.mul (.var 0) (.add (.var 1) (.var 4)))
            (.mul (.var 2) (.add (.var 3) (.var 5))))
          (by decide) (fun
            | 0 => a | 1 => finSum f m | 2 => c | 3 => finSum g m
            | 4 => f m | _ => g m)))

/-- Full original angular sum; every block and all six planes are retained.
Only reciprocal degree is absent from the computed right-hand costs. -/
theorem blockConditionalRatio_weightedAngularEnergy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    (hN : 0 < N width) {psi : RatPoly} {C : Q'}
    (I : Interval (N width) psi C) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let Vbar := spatialFringeMass w K width
    let qbar := projectedEndpointSource w K width A
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    weightedAngularEnergy (N width-1) qbar phi ≤
      2*weightedAngularEnergy (N width-1) Vbar b+
        (2*(C*C))*weightedAngularEnergy (N width-1) Vbar A := by
  dsimp only
  have hn : N width-1+1 = N width := Nat.sub_add_cancel hN
  unfold weightedAngularEnergy
  simp only [hn]
  apply sum_linear_le
  intro block hblock
  let qbar := projectedEndpointSource w K width (terminalMessage w K width (n+t))
  let Vbar := spatialFringeMass w K width
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let A := terminalMessage w K width (n+t)
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let F := fun i j => quaternionHaar (N width) (polyMul (polyMul Vbar Vbar)
    (polyMul (blockAngularDerivative block i j b) (blockAngularDerivative block i j b)))
  let G := fun i j => quaternionHaar (N width) (polyMul (polyMul Vbar Vbar)
    (polyMul (blockAngularDerivative block i j A) (blockAngularDerivative block i j A)))
  have hm := sixValue_mono _ _ (fun i j hi hj =>
    blockConditionalRatio_plane_gradient_bound hw0 hw1 K width hK n t hdepth I
      (4*block+i) (4*block+j) (by omega) (by omega) k)
  have hp (a p : RatPoly) :
      quaternionHaar (N width) (polyMul (polyMul a a) (blockAngularSquare block p)) ≈
        sixValue (fun i j => quaternionHaar (N width) (polyMul (polyMul a a)
          (polyMul (blockAngularDerivative block i j p) (blockAngularDerivative block i j p)))) :=
    haar_six (N width) (polyMul a a) _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (hp qbar phi))
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (sixValue_linear 2 (2*(C*C)) F G)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm (hp Vbar b)))
          (Q'.mul_eqv_congr_left (2*(C*C)) _ _ (Q'.eqv_symm (hp Vbar A)))))))

private theorem block_next (w : Q') (K width t : Nat) (p : RatPoly) :
    originalBlockTransfer w K width (t+1) p =
      transferStep w K width (originalBlockTransfer w K width t p) := by
  simpa only [originalBlockTransfer, iterateStep, transferStep] using
    iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 p

private theorem transfer_product (w : Q') (K width : Nat) (p : RatPoly) :
    transferStep w K width p = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) p) := by
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

theorem block_source_fringe_independent (w : Q') (K width n t : Nat)
    (ht : 1 ≤ t) {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)) := by
  have htime : t-1+1 = t := Nat.sub_add_cancel ht
  have hnext := block_next w K width (t-1) (polyMul (terminalMessage w K width n) psi)
  rw [htime, transfer_product] at hnext
  rw [hnext]
  have hfringe := (fringeBlocks_mem_iff width i).mp hi
  exact productMap_independent_of_not_mem (N width) w K (activeBlocks width)
    (activeBlocks_lt width) i hfringe.1 hfringe.2 _
    (supported_polyMul (spatialWeight_supported w K width)
      (source_supported w K width n (t-1) hp))

private theorem reciprocal_independent {i : Nat} {A : RatPoly}
    (hA : QuaternionBlockIndependent i A) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    QuaternionBlockIndependent i (reciprocal A u hu k) := by
  have hR : QuaternionBlockIndependent i (remainder A u hu) := by
    change QuaternionBlockIndependent i
      (polyAdd (polySmul (scale u hu) A) (polyNeg polyOne))
    exact quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polySmul _ hA)
      (quaternionBlockIndependent_polyNeg (quaternionBlockIndependent_polyOne i))
  exact quaternionBlockIndependent_polySmul _ (corrector_independent hR k)

/-- After a genuine original transfer step, the ratio has no fringe output
coordinate. No locality assumption on the initial signed observable is used. -/
theorem blockConditionalRatio_fringe_independent {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (ht : 1 ≤ t)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k i : Nat)
    (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (blockConditionalRatio hw0 hw1 K width hK n t psi k) := by
  unfold blockConditionalRatio blockReciprocal
  exact quaternionBlockIndependent_polyMul
    (reciprocal_independent (terminal_fringe_independent w K width (n+t) i hi) _ _ k)
    (block_source_fringe_independent w K width n t ht hp i hi)

/-- Actual original energy consumption. The mixed quadratic budget and its
heat-gap square remain literal; only reciprocal degree is removed from the
angular costs. This is not a SAME-variance or changing-family estimate. -/
theorem blockConditionalRatio_energy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (hkin : sufficientCutoff w ≤ K)
    (n t : Nat) (ht : 1 ≤ t) (hN : 0 < N width)
    {psi : RatPoly} {C : Q'} (I : Interval (N width) psi C) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let Vbar := spatialFringeMass w K width
    let qbar := projectedEndpointSource w K width A
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    energy w K width A phi ≤
      (1-w)*(2*weightedAngularEnergy (N width-1) Vbar b+
        (2*(C*C))*weightedAngularEnergy (N width-1) Vbar A)+
      ((1-w)*(1-w))*pairBudget (N width-1) qbar (polyMul qbar (polyMul phi phi)) := by
  dsimp only
  have hsource := BF4ExactSlabFixedSpatialSourceTaylor.energy_le_angular_add_mixed_quadratic
    (Q'.le_of_lt hw0) hw1 K width hkin (terminalMessage w K width (n+t))
    (blockConditionalRatio hw0 hw1 K width hK n t psi k)
    (terminalMessage_supported w K width (n+t))
    (blockConditionalRatio_supported hw0 hw1 K width hK n t I.support k) hN
    (fun i hi => blockConditionalRatio_fringe_independent hw0 hw1 K width hK n t ht I.support k i hi)
  have hang := blockConditionalRatio_weightedAngularEnergy_le hw0 hw1 K width hK n t
    (by omega) hN I k
  exact Q'.le_trans' _ _ _ hsource
    (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hang
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))))

#print axioms projected_terminal_source_pin
#print axioms blockConditionalRatio_plane_gradient_bound
#print axioms blockConditionalRatio_weightedAngularEnergy_le
#print axioms blockConditionalRatio_fringe_independent
#print axioms block_source_fringe_independent
#print axioms blockConditionalRatio_energy_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
