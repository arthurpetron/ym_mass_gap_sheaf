/-
# Quantitative residual damping for the ORIGINAL signed cost

The literal residual pairs with its SAME incoming source to give the
complete signed cost. Original weighted Cauchy--Schwarz therefore supplies
p*Di^2 <= C*R. This pays a quadratic part of the retained residual without
assuming Di>=0 or dividing by C (which may vanish). The consecutive-cost
upper bound retains that quadratic subtraction and the distinct ground
partitions. It is not a useful aggregate survival/scaling bound: the
remaining ground mismatch and surviving-norm comparison are still OPEN.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_quadratic_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair weighted_cauchySchwarz)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks weightedMass terminalMessage transferStep

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem support_smul {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c f) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hf u hu

/-- The original signed residual remains on the original slice. -/
theorem costTransportResidual_supported (w : Q') (K width : Nat) (a : RatPoly)
    {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    SupportedQuaternionBlocks (N width) (costTransportResidual w K width a c) :=
  supported_add (support_smul hc _) (support_smul (transferStep_supported w K width hc) _)

/-- Exact dual pairing with the SAME source gives the COMPLETE cost. -/
theorem costTransportResidual_pair_pin (w : Q') (K width : Nat) (a c : RatPoly) :
    weightedMass w K width (polyMul c (costTransportResidual w K width a c)) ≈
      clearedRayleighCost w K width a c := by
  let p := weightedMass w K width (polyMul a (transferStep w K width a))
  let z := weightedMass w K width (polyMul a a)
  let b := transferStep w K width c
  change weightedMass w K width (polyMul c (polyAdd (polySmul p c) (polySmul (-z) b))) ≈
    p*weightedMass w K width (polyMul c c) + -(z*weightedMass w K width (polyMul c b))
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right c _ _))
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right p c c))
          (weightedMass_smul w K width p _))
        (Q'.eqv_trans _ _ _
          (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right (-z) c b))
          (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-z) _)
            (Q'.neg_mul_eqv _ _)))))

private theorem original_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    {f g : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    weightedMass w K width (polyMul f g)*weightedMass w K width (polyMul f g) ≤
      weightedMass w K width (polyMul f f)*weightedMass w K width (polyMul g g) := by
  have pin (r s : RatPoly) : weightedPair (N width) (spatialWeight w K width) r s ≈
      weightedMass w K width (polyMul r s) := by
    unfold weightedPair weightedMass
    exact haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul r s) (spatialWeight w K width))
  have h := weighted_cauchySchwarz (N width) (spatialWeight w K width) f g
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK) hf hg
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul (pin f g) (pin f g)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (qmul (pin f f) (pin g g))))

/-- An UNCONDITIONAL quantitative lower payment for the retained residual.
No incoming-cost sign or nonzero source norm is required; a is arbitrary. -/
theorem costTransportRemainder_cost_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    weightedMass w K width (polyMul a (transferStep w K width a))*
        (clearedRayleighCost w K width a c*clearedRayleighCost w K width a c) ≤
      weightedMass w K width (polyMul c c)*costTransportRemainder w K width a c := by
  let p := weightedMass w K width (polyMul a (transferStep w K width a))
  let z := weightedMass w K width (polyMul a a)
  let C := weightedMass w K width (polyMul c c)
  let y := costTransportResidual w K width a c
  let Y := weightedMass w K width (polyMul y y)
  let L := weightedMass w K width (polyMul y (transferStep w K width y))
  let D := clearedRayleighCost w K width a c
  have hy := costTransportResidual_supported w K width a hc
  have hp : (0 : Q') ≤ p := transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width a ha
  have hz : (0 : Q') ≤ z := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square a ha)
  have hC : (0 : Q') ≤ C := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square c hc)
  have hL : (0 : Q') ≤ L := transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width y hy
  have hpin := costTransportResidual_pair_pin w K width a c
  have hcs : D*D ≤ C*Y := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (qmul hpin hpin)) (original_cauchySchwarz hw0 hw1 K width hK hc hy)
  have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ p hcs hp
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ C
    (Q'.add_le_self_of_nonneg (p*Y) (z*L) (Q'.mul_nonneg _ _ hz hL)) hC
  change p*(D*D) ≤ C*(p*Y+z*L)
  exact Q'.le_trans' _ _ _ hfirst (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => p | 1 => C | _ => Y))) hsecond)

/-- The actual finite cost recurrence now retains QUADRATIC damping, not
just residual nonnegativity. Ground mismatch is still paid at fixed nome/width. -/
theorem terminal_clearedRayleighCost_quadratic_damping {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s : Nat) {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    let a := terminalMessage w K width (s+1)
    let A := transferStep w K width a
    let b := transferStep w K width c
    let z := weightedMass w K width (polyMul a a)
    let p := weightedMass w K width (polyMul a A)
    let v := weightedMass w K width (polyMul A A)
    let C := weightedMass w K width (polyMul c c)
    let B := weightedMass w K width (polyMul b b)
    let Di := clearedRayleighCost w K width a c
    let Do := clearedRayleighCost w K width A b
    C*((z*z*z)*Do)+(p*v)*(Di*Di) ≤
      (v*(p*p))*(C*Di)+((z*z)*(comparisonEta hw0 hw1 width s*(p*v)))*(C*B) := by
  dsimp only
  let a := terminalMessage w K width (s+1)
  let A := transferStep w K width a
  let b := transferStep w K width c
  let z := weightedMass w K width (polyMul a a)
  let p := weightedMass w K width (polyMul a A)
  let v := weightedMass w K width (polyMul A A)
  let C := weightedMass w K width (polyMul c c)
  let B := weightedMass w K width (polyMul b b)
  let Di := clearedRayleighCost w K width a c
  let Do := clearedRayleighCost w K width A b
  let R := costTransportRemainder w K width a c
  let e := comparisonEta hw0 hw1 width s
  have hC : (0 : Q') ≤ C := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square c hc)
  have hv : (0 : Q') ≤ v := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square A (transferStep_supported w K width (terminalMessage_supported w K width (s+1))))
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ v
    (costTransportRemainder_cost_square_le hw0 hw1 K width hK
      (terminalMessage_supported w K width (s+1)) hc) hv
  have hbase := Q'.mul_le_mul_of_nonneg_left _ _ C
    (terminal_clearedRayleighCost_transport_le hw0 hw1 K width hK s hc) hC
  have hquad' : (p*v)*(Di*Di) ≤ C*(v*R) := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => p | 1 => v | _ => Di*Di)))
    (Q'.le_trans' _ _ _ hquad (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => v | 1 => C | _ => R))))
  have hstart := Q'.add_le_add_left (C*((z*z*z)*Do)) _ _ hquad'
  have hjoin : C*((z*z*z)*Do)+C*(v*R) ≈ C*((z*z*z)*Do+v*R) :=
    Q'.eqv_symm (Q'.mul_add_eqv C _ _)
  have hend : C*((v*(p*p))*Di+((z*z)*(e*(p*v)))*B) ≈
      (v*(p*p))*(C*Di)+((z*z)*(e*(p*v)))*(C*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
      (.add (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (.mul (.var 3) (.mul (.var 0) (.var 4)))) (by decide)
      (fun | 0 => C | 1 => v*(p*p) | 2 => Di | 3 => (z*z)*(e*(p*v)) | _ => B)
  exact Q'.le_trans' _ _ _ hstart (Q'.le_trans' _ _ _ (Q'.le_of_eqv hjoin)
    (Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv hend)))

/-- Consecutive ORIGINAL block sources, with the SAME fixed input psi.
The incoming filtered norm C is retained, not replaced by initial variance.
In particular the stage OWN mean is not recomputed at the next lag. -/
theorem original_block_clearedRayleighCost_quadratic_damping {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    let input := polyMul (terminalMessage w K width n) psi
    let a := terminalMessage w K width (n+t)
    let c := originalBlockTransfer w K width t input
    let A := terminalMessage w K width (n+(t+1))
    let b := originalBlockTransfer w K width (t+1) input
    let z := weightedMass w K width (polyMul a a)
    let p := weightedMass w K width (polyMul a A)
    let v := weightedMass w K width (polyMul A A)
    let C := weightedMass w K width (polyMul c c)
    let B := weightedMass w K width (polyMul b b)
    let Di := clearedRayleighCost w K width a c
    let Do := clearedRayleighCost w K width A b
    C*((z*z*z)*Do)+(p*v)*(Di*Di) ≤
      (v*(p*p))*(C*Di)+((z*z)*(comparisonEta hw0 hw1 width (n+t-1)*(p*v)))*(C*B) := by
  dsimp only
  let input := polyMul (terminalMessage w K width n) psi
  have hc := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have h := terminal_clearedRayleighCost_quadratic_damping hw0 hw1 K width hK (n+t-1) hc
  have hg : n+t-1+1 = n+t := Nat.sub_add_cancel hdepth
  have hnext : originalBlockTransfer w K width (t+1) input =
      transferStep w K width (originalBlockTransfer w K width t input) := by
    simpa only [originalBlockTransfer, iterateStep, transferStep] using
      iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 input
  rw [hg] at h
  simpa only [input, hnext, terminalMessage_next, Nat.add_assoc] using h

/-- Both payments are retained at once: quadratic incoming-cost damping
and SECOND-order original vacuum mismatch. No Di sign or source inverse
is required. The factor four clears the computed quarter coefficient. -/
theorem terminal_clearedRayleighCost_quadratic_vacuum_damping {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s : Nat) {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    let a := terminalMessage w K width (s+1)
    let A := transferStep w K width a
    let b := transferStep w K width c
    let z := weightedMass w K width (polyMul a a)
    let p := weightedMass w K width (polyMul a A)
    let v := weightedMass w K width (polyMul A A)
    let C := weightedMass w K width (polyMul c c)
    let B := weightedMass w K width (polyMul b b)
    let Di := clearedRayleighCost w K width a c
    let Do := clearedRayleighCost w K width A b
    let e := comparisonEta hw0 hw1 width s
    4*(C*((z*z*z)*Do)+(p*v)*(Di*Di)) ≤
      4*((v*(p*p))*(C*Di))+((z*z)*(((2+e)*(e*e))*(p*v)))*(C*B) := by
  dsimp only
  let a := terminalMessage w K width (s+1)
  let A := transferStep w K width a
  let b := transferStep w K width c
  let z := weightedMass w K width (polyMul a a)
  let p := weightedMass w K width (polyMul a A)
  let v := weightedMass w K width (polyMul A A)
  let C := weightedMass w K width (polyMul c c)
  let B := weightedMass w K width (polyMul b b)
  let Di := clearedRayleighCost w K width a c
  let Do := clearedRayleighCost w K width A b
  let R := costTransportRemainder w K width a c
  let e := comparisonEta hw0 hw1 width s
  have hC : (0 : Q') ≤ C := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square c hc)
  have hv : (0 : Q') ≤ v := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square A (transferStep_supported w K width (terminalMessage_supported w K width (s+1))))
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ v
    (costTransportRemainder_cost_square_le hw0 hw1 K width hK
      (terminalMessage_supported w K width (s+1)) hc) hv
  have hquad' : (p*v)*(Di*Di) ≤ C*(v*R) := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => p | 1 => v | _ => Di*Di)))
    (Q'.le_trans' _ _ _ hquad (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => v | 1 => C | _ => R))))
  have hstart := Q'.mul_le_mul_of_nonneg_left _ _ 4
    (Q'.add_le_add_left (C*((z*z*z)*Do)) _ _ hquad') (by decide)
  have hbase := Q'.mul_le_mul_of_nonneg_left _ _ C
    (terminal_clearedRayleighCost_quadratic_vacuum_transport hw0 hw1 K width hK s hc) hC
  have hjoin : 4*(C*((z*z*z)*Do)+C*(v*R)) ≈ C*(4*((z*z*z)*Do+v*R)) :=
    poly_identity_of_normal_eq
      (.mul (.const 4) (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))))
      (.mul (.var 0) (.mul (.const 4) (.add (.var 1) (.var 2))))
      (by decide) (fun | 0 => C | 1 => (z*z*z)*Do | _ => v*R)
  have hend : C*(4*((v*(p*p))*Di)+((z*z)*(((2+e)*(e*e))*(p*v)))*B) ≈
      4*((v*(p*p))*(C*Di))+((z*z)*(((2+e)*(e*e))*(p*v)))*(C*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.const 4) (.mul (.var 1) (.var 2)))
        (.mul (.var 3) (.var 4))))
      (.add (.mul (.const 4) (.mul (.var 1) (.mul (.var 0) (.var 2))))
        (.mul (.var 3) (.mul (.var 0) (.var 4)))) (by decide)
      (fun | 0 => C | 1 => v*(p*p) | 2 => Di | 3 => (z*z)*(((2+e)*(e*e))*(p*v)) | _ => B)
  exact Q'.le_trans' _ _ _ hstart (Q'.le_trans' _ _ _ (Q'.le_of_eqv hjoin)
    (Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv hend)))

/-- The simultaneous second-order payments on the ACTUAL original block
orbit. psi is fixed, including its initial OWN center, at both lags. -/
theorem original_block_clearedRayleighCost_quadratic_vacuum_damping {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    let input := polyMul (terminalMessage w K width n) psi
    let a := terminalMessage w K width (n+t)
    let c := originalBlockTransfer w K width t input
    let A := terminalMessage w K width (n+(t+1))
    let b := originalBlockTransfer w K width (t+1) input
    let z := weightedMass w K width (polyMul a a)
    let p := weightedMass w K width (polyMul a A)
    let v := weightedMass w K width (polyMul A A)
    let C := weightedMass w K width (polyMul c c)
    let B := weightedMass w K width (polyMul b b)
    let Di := clearedRayleighCost w K width a c
    let Do := clearedRayleighCost w K width A b
    let e := comparisonEta hw0 hw1 width (n+t-1)
    4*(C*((z*z*z)*Do)+(p*v)*(Di*Di)) ≤
      4*((v*(p*p))*(C*Di))+((z*z)*(((2+e)*(e*e))*(p*v)))*(C*B) := by
  dsimp only
  let input := polyMul (terminalMessage w K width n) psi
  have hc := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have h := terminal_clearedRayleighCost_quadratic_vacuum_damping
    hw0 hw1 K width hK (n+t-1) hc
  have hg : n+t-1+1 = n+t := Nat.sub_add_cancel hdepth
  have hnext : originalBlockTransfer w K width (t+1) input =
      transferStep w K width (originalBlockTransfer w K width t input) := by
    simpa only [originalBlockTransfer, iterateStep, transferStep] using
      iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 input
  rw [hg] at h
  simpa only [input, hnext, terminalMessage_next, Nat.add_assoc] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity.costTransportResidual_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity.costTransportResidual_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity.costTransportRemainder_cost_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity.terminal_clearedRayleighCost_quadratic_damping
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity.original_block_clearedRayleighCost_quadratic_damping
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity.terminal_clearedRayleighCost_quadratic_vacuum_damping
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostCoercivity.original_block_clearedRayleighCost_quadratic_vacuum_damping
