/-
# Signed cost transport for the ORIGINAL finite transfer

The complete next-step cleared cost is transported with a retained NEGATIVE
residual bracket. The vacuum mismatch is paid by the actual terminal
same-gap bracket, without an eigenpin, a source inverse or a sign premise
on the incoming cost. One V remains in every weighted pairing and the
original T=P M_V remains unchanged. This supplies a finite signed-window
identity and upper bound, not useful changing-family survival: quantitative
source-specific cancellation of the retained residual is still OPEN.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_quadratic_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (Bracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks weightedMass terminalMessage transferStep

private def pair (w : Q') (K width : Nat) (f g : RatPoly) : Q' :=
  weightedMass w K width (polyMul f g)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem support_smul {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c f) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hf u hu

private theorem pair_add_left (w : Q') (K width : Nat) (f g h : RatPoly) :
    pair w K width (polyAdd f g) h ≈ pair w K width f h + pair w K width g h := by
  unfold pair
  rw [polyMul_add_left_exact]
  exact weightedMass_add w K width _ _

private theorem pair_add_right (w : Q') (K width : Nat) (f g h : RatPoly) :
    pair w K width f (polyAdd g h) ≈ pair w K width f g + pair w K width f h :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right f g h))
    (weightedMass_add w K width _ _)

private theorem pair_smul_left (w : Q') (K width : Nat) (a : Q') (f g : RatPoly) :
    pair w K width (polySmul a f) g ≈ a*pair w K width f g :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_left a f g))
    (weightedMass_smul w K width a _)

private theorem pair_smul_right (w : Q') (K width : Nat) (a : Q') (f g : RatPoly) :
    pair w K width f (polySmul a g) ≈ a*pair w K width f g :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right a f g))
    (weightedMass_smul w K width a _)

private theorem combination_pair (w : Q') (K width : Nat) (a b : Q')
    (f g u v : RatPoly) :
    pair w K width (polyAdd (polySmul a f) (polySmul b g))
      (polyAdd (polySmul a u) (polySmul b v)) ≈
      a*a*pair w K width f u + a*b*(pair w K width f v + pair w K width g u) +
        b*b*pair w K width g v := by
  have left (c : Q') (p : RatPoly) :
      pair w K width (polySmul c p) (polyAdd (polySmul a u) (polySmul b v)) ≈
        c*(a*pair w K width p u + b*pair w K width p v) :=
    Q'.eqv_trans _ _ _ (pair_smul_left w K width c _ _)
      (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_trans _ _ _ (pair_add_right w K width _ _ _)
        (Q'.add_eqv_congr' (pair_smul_right w K width a _ _)
          (pair_smul_right w K width b _ _))))
  exact Q'.eqv_trans _ _ _ (pair_add_left w K width _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (left a f) (left b g))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
          (.mul (.var 1) (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))))
        (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.mul (.mul (.var 0) (.var 1)) (.add (.var 3) (.var 4))))
          (.mul (.mul (.var 1) (.var 1)) (.var 5)))
        (by decide) (fun
          | 0 => a | 1 => b | 2 => pair w K width f u | 3 => pair w K width f v
          | 4 => pair w K width g u | _ => pair w K width g v)))

/-- Literal cleared residual; its scalar is the actual incoming vacuum quotient numerator. -/
def costTransportResidual (w : Q') (K width : Nat) (a c : RatPoly) : RatPoly :=
  polyAdd (polySmul (pair w K width a (transferStep w K width a)) c)
    (polySmul (-(pair w K width a a)) (transferStep w K width c))

/-- The complete residual bracket, including its positive transfer quadratic. -/
def costTransportRemainder (w : Q') (K width : Nat) (a c : RatPoly) : Q' :=
  let y := costTransportResidual w K width a c
  pair w K width a (transferStep w K width a)*pair w K width y y +
    pair w K width a a*pair w K width y (transferStep w K width y)

private theorem remainder_expansion (w : Q') (K width : Nat) (a : RatPoly)
    {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    let z := pair w K width a a
    let p := pair w K width a (transferStep w K width a)
    let b := transferStep w K width c
    let C := pair w K width c c
    let Q := pair w K width c b
    let B := pair w K width b b
    let R := pair w K width b (transferStep w K width b)
    costTransportRemainder w K width a c ≈
      p*(p*p*C + p*(-z)*(Q+Q) + (-z)*(-z)*B) +
        z*(p*p*Q + p*(-z)*(B+B) + (-z)*(-z)*R) := by
  dsimp only
  let z := pair w K width a a
  let p := pair w K width a (transferStep w K width a)
  let b := transferStep w K width c
  let y := costTransportResidual w K width a c
  have hb := transferStep_supported w K width hc
  have hcomm : pair w K width b c ≈ pair w K width c b :=
    weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm b c)
  have hnorm := combination_pair w K width p (-z) c b c b
  have hnorm' := Q'.eqv_trans _ _ _ hnorm (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _ hcomm))) (Q'.eqv_refl _))
  have ht : RatPolyCoeffEqv (transferStep w K width y)
      (polyAdd (polySmul p b) (polySmul (-z) (transferStep w K width b))) :=
    (transferStep_add w K width _ _).trans
      ((transferStep_smul w K width p c).add (transferStep_smul w K width (-z) b))
  have hcross : pair w K width c (transferStep w K width b) ≈ pair w K width b b :=
    Q'.eqv_symm (transferStep_weighted_symmetric w K width hc hb)
  have hquad := Q'.eqv_trans _ _ _
    (weightedMass_congr w K width ((RatPolyCoeffEqv.refl y).mul ht))
    (combination_pair w K width p (-z) c b b (transferStep w K width b))
  have hquad' := Q'.eqv_trans _ _ _ hquad (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' hcross (Q'.eqv_refl _)))) (Q'.eqv_refl _))
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_left p _ _ hnorm')
    (Q'.mul_eqv_congr_left z _ _ hquad')

/-- Exact finite signed cost transport. The retained remainder is SUBTRACTED
when solving for the outgoing cost; all four chronological vacuum masses remain. -/
theorem clearedRayleighCost_transport_identity (w : Q') (K width : Nat) (a : RatPoly)
    {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    let A := transferStep w K width a
    let b := transferStep w K width c
    let z := weightedMass w K width (polyMul a a)
    let p := weightedMass w K width (polyMul a A)
    let v := weightedMass w K width (polyMul A A)
    let q := weightedMass w K width (polyMul A (transferStep w K width A))
    (z*z*z)*clearedRayleighCost w K width A b +
        v*costTransportRemainder w K width a c ≈
      (v*(p*p))*clearedRayleighCost w K width a c +
        ((z*z)*(z*q-v*p))*weightedMass w K width (polyMul b b) := by
  dsimp only
  let z := pair w K width a a
  let p := pair w K width a (transferStep w K width a)
  let A := transferStep w K width a
  let b := transferStep w K width c
  let v := pair w K width A A
  let q := pair w K width A (transferStep w K width A)
  let C := pair w K width c c
  let Q := pair w K width c b
  let B := pair w K width b b
  let R := pair w K width b (transferStep w K width b)
  have he := remainder_expansion w K width a hc
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left v _ _ he)) ?_
  change (z*z*z)*(q*B + -(v*R)) +
      v*(p*(p*p*C + p*(-z)*(Q+Q) + (-z)*(-z)*B) +
        z*(p*p*Q + p*(-z)*(B+B) + (-z)*(-z)*R)) ≈
    (v*(p*p))*(p*C + -(z*Q)) + ((z*z)*(z*q-v*p))*B
  let Z : PolyExpr := .var 0
  let P : PolyExpr := .var 1
  let V : PolyExpr := .var 2
  let Qv : PolyExpr := .var 3
  let Cv : PolyExpr := .var 4
  let Qc : PolyExpr := .var 5
  let Bv : PolyExpr := .var 6
  let Rv : PolyExpr := .var 7
  let square : PolyExpr := .add (.add (.mul (.mul P P) Cv)
    (.mul (.mul P (.neg Z)) (.add Qc Qc))) (.mul (.mul (.neg Z) (.neg Z)) Bv)
  let quadratic : PolyExpr := .add (.add (.mul (.mul P P) Qc)
    (.mul (.mul P (.neg Z)) (.add Bv Bv))) (.mul (.mul (.neg Z) (.neg Z)) Rv)
  exact poly_identity_of_normal_eq
    (.add (.mul (.mul (.mul Z Z) Z) (.add (.mul Qv Bv) (.neg (.mul V Rv))))
      (.mul V (.add (.mul P square) (.mul Z quadratic))))
    (.add (.mul (.mul V (.mul P P)) (.add (.mul P Cv) (.neg (.mul Z Qc))))
      (.mul (.mul (.mul Z Z) (.add (.mul Z Qv) (.neg (.mul V P)))) Bv))
    (by decide) (fun | 0 => z | 1 => p | 2 => v | 3 => q | 4 => C | 5 => Q | 6 => B | _ => R)

/-- Nonnegative residual for the actual terminal source and an arbitrary
signed incoming polynomial, including its zero-norm case. -/
theorem costTransportRemainder_terminal_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s : Nat) {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    (0 : Q') ≤ costTransportRemainder w K width (terminalMessage w K width (s+1)) c := by
  let a := terminalMessage w K width (s+1)
  let y := costTransportResidual w K width a c
  have hy : SupportedQuaternionBlocks (N width) y :=
    supported_add (support_smul hc _) (support_smul (transferStep_supported w K width hc) _)
  have hz := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK (s+1) (s+1))
  have hp : (0 : Q') ≤ pair w K width a (transferStep w K width a) :=
    transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width a
      (terminalMessage_supported w K width (s+1))
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ hp (weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square y hy)))
    (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ hz
      (transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width y hy)))

private theorem bracket_mass {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly} (B : Bracket width f g) :
    B.lower*weightedMass w K width g ≤ weightedMass w K width f ∧
      weightedMass w K width f ≤ B.upper*weightedMass w K width g := by
  have hl := weightedMass_nonnegative hw0 hw1 K width hK B.lowerCertificate
  have hu := weightedMass_nonnegative hw0 hw1 K width hK B.upperCertificate
  have lower_eq : weightedMass w K width (polyAdd f (polySmul (-B.lower) g)) ≈
      weightedMass w K width f + -(B.lower*weightedMass w K width g) :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (weightedMass_smul w K width _ _) (Q'.neg_mul_eqv _ _)))
  have upper_eq : weightedMass w K width (polyAdd (polySmul B.upper g) (polySmul (-1) f)) ≈
      B.upper*weightedMass w K width g + -(weightedMass w K width f) :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (weightedMass_smul w K width _ _)
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width _ _)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))
  exact ⟨Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hl (Q'.le_of_eqv lower_eq)),
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hu (Q'.le_of_eqv upper_eq))⟩

private def transfer_bracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (B : Bracket width f g) : Bracket width (transferStep w K width f) (transferStep w K width g) where
  lower := B.lower
  upper := B.upper
  lowerCertificate := Certificate.ofCoeff
    ((transferStep_add w K width _ _).trans
      ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width _ _))).symm
    (transferStep_certificate hw0 hw1 K width hK (supported_add hf (support_smul hg _)) B.lowerCertificate)
  upperCertificate := Certificate.ofCoeff
    ((transferStep_add w K width _ _).trans
      ((transferStep_smul w K width _ _).add (transferStep_smul w K width _ _))).symm
    (transferStep_certificate hw0 hw1 K width hK
      (supported_add (support_smul hg _) (support_smul hf _)) B.upperCertificate)

/-- Only the original vacuum mismatch is enlarged. The coefficient is
cutoff/source independent, but depends on the fixed nome, width and depth. -/
theorem terminal_vacuum_mismatch_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) :
    let a := terminalMessage w K width (s+1)
    let A := transferStep w K width a
    let z := weightedMass w K width (polyMul a a)
    let p := weightedMass w K width (polyMul a A)
    let v := weightedMass w K width (polyMul A A)
    let q := weightedMass w K width (polyMul A (transferStep w K width A))
    z*q-v*p ≤ comparisonEta hw0 hw1 width s*(p*v) := by
  dsimp only
  let a := terminalMessage w K width (s+1)
  let A := transferStep w K width a
  let z := pair w K width a a
  let p := pair w K width a A
  let v := pair w K width A A
  let q := pair w K width A (transferStep w K width A)
  let B0 := terminalComparison hw0 hw1 K width hK s 1 0
  let J : Bracket width A a := {
    lower := B0.lower
    upper := B0.upper
    lowerCertificate := by
      simpa only [A, a, terminalMessage_next, Nat.add_zero] using B0.lowerCertificate
    upperCertificate := by
      simpa only [A, a, terminalMessage_next, Nat.add_zero] using B0.upperCertificate }
  let J1 := transfer_bracket hw0 hw1 K width hK
    (transferStep_supported w K width (terminalMessage_supported w K width (s+1)))
    (terminalMessage_supported w K width (s+1)) J
  have hz : (0 : Q') ≤ z := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK (s+1) (s+1))
  have hv : (0 : Q') ≤ v := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square A (transferStep_supported w K width (terminalMessage_supported w K width (s+1))))
  have ha := terminalMessage_certificate hw0 hw1 K width hK (s+1)
  have hA := transferStep_certificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (s+1)) ha
  have hzp := bracket_mass hw0 hw1 K width hK (multiplyBracket J ha)
  have hvq := bracket_mass hw0 hw1 K width hK (multiplyBracket J1 hA)
  have hraw := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ z hvq.2 hz)
    (Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg_left _ _ v hzp.1 hv))
  have hraw' : z*q-v*p ≤ (J.upper + -J.lower)*z*v := Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 3) (.var 1)))
        (.neg (.mul (.var 1) (.mul (.var 2) (.var 0)))))
      (.mul (.mul (.add (.var 3) (.neg (.var 2))) (.var 0)) (.var 1))
      (by decide) (fun | 0 => z | 1 => v | 2 => J.lower | _ => J.upper)))
  have he := comparisonEta_nonnegative hw0 hw1 width s
  have hwidth := terminalComparison_relative_width hw0 hw1 K width hK s 1 0
  have hpaid := Q'.mul_le_mul_of_nonneg_right _ _ v
    (Q'.mul_le_mul_of_nonneg_right _ _ z hwidth hz) hv
  have hpaid' : ((comparisonEta hw0 hw1 width s*J.lower)*z)*v ≈
      comparisonEta hw0 hw1 width s*((J.lower*z)*v) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => comparisonEta hw0 hw1 width s | 1 => J.lower | 2 => z | _ => v)
  exact Q'.le_trans' _ _ _ hraw' (Q'.le_trans' _ _ _ hpaid
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpaid')
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ v hzp.1 hv) he)))

/-- A genuine finite upper bound retaining the favorable residual, without
assuming the incoming cost is nonnegative or discarding either original partition. -/
theorem terminal_clearedRayleighCost_transport_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (s : Nat) {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    let a := terminalMessage w K width (s+1)
    let A := transferStep w K width a
    let b := transferStep w K width c
    let z := weightedMass w K width (polyMul a a)
    let p := weightedMass w K width (polyMul a A)
    let v := weightedMass w K width (polyMul A A)
    (z*z*z)*clearedRayleighCost w K width A b + v*costTransportRemainder w K width a c ≤
      (v*(p*p))*clearedRayleighCost w K width a c +
        ((z*z)*(comparisonEta hw0 hw1 width s*(p*v)))*weightedMass w K width (polyMul b b) := by
  dsimp only
  let a := terminalMessage w K width (s+1)
  let z := weightedMass w K width (polyMul a a)
  let b := transferStep w K width c
  have hB := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square b (transferStep_supported w K width hc))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (clearedRayleighCost_transport_identity w K width a hc))
    (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (terminal_vacuum_mismatch_upper hw0 hw1 K width hK s)
        (SumOfSquares.q_mul_self_nonneg z)) hB))

/-- Consecutive ACTUAL original block costs. The same input psi occurs in
both blocks; in particular its stage OWN center is not recomputed at t+1.
Only positive terminal depth is required, not a sign or lower norm of psi. -/
theorem original_block_clearedRayleighCost_transport_le {w : Q'}
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
    (z*z*z)*clearedRayleighCost w K width A b + v*costTransportRemainder w K width a c ≤
      (v*(p*p))*clearedRayleighCost w K width a c +
        ((z*z)*(comparisonEta hw0 hw1 width (n+t-1)*(p*v)))*weightedMass w K width (polyMul b b) := by
  dsimp only
  let input := polyMul (terminalMessage w K width n) psi
  have hc := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have h := terminal_clearedRayleighCost_transport_le hw0 hw1 K width hK (n+t-1) hc
  have hg : n+t-1+1 = n+t := Nat.sub_add_cancel hdepth
  have hnext : originalBlockTransfer w K width (t+1) input =
      transferStep w K width (originalBlockTransfer w K width t input) := by
    simpa only [originalBlockTransfer, iterateStep, transferStep] using
      iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 input
  rw [hg] at h
  simpa only [input, hnext, terminalMessage_next, Nat.add_assoc] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport.costTransportResidual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport.costTransportRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport.clearedRayleighCost_transport_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport.costTransportRemainder_terminal_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport.terminal_vacuum_mismatch_upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport.terminal_clearedRayleighCost_transport_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRayleighCostTransport.original_block_clearedRayleighCost_transport_le
