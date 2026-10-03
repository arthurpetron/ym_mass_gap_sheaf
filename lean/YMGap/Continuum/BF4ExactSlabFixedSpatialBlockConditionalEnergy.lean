/-
# The actual finite conditional ratio joins the ORIGINAL signed energy split

For A=g_(n+t), b=T^t(g_n*psi) and phi_k=G_k*b, the multiplier certificate
gives ||A*phi_k||_V^2 <= ||b||_V^2. SAME-weight Cauchy--Schwarz and the
original transfer continuity bound therefore control the COMPLETE signed
multiplication remainder by

  2*rho^k*(Z1 + Z0*C)*||b||_V^2,
  C=kineticCap*H[V], rho=mixRate(w,width).

The exact energy split only requires support, not b=A*phi. Inserting this
actual finite phi gives an explicit error and a computed tolerance modulus.
All partitions, action factors and terminal messages are retained. This
joins finite reconstruction to the signed split; it does not bound the
remaining energy/drift below or uniformly control a changing scaling family.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound
import YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_quadratic_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight weightedMass

private theorem source_supported (w : Q') (K width n t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    t (supported_polyMul (terminalMessage_supported w K width n) hp)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem abs_square (a : Q') : Q'.abs a*Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
      (by decide) (fun _ => a)

private theorem abs_le_square {x c : Q'} (hc : (0 : Q') ≤ c)
    (h : x*x ≤ c*c) : Q'.abs x ≤ c := by
  have hs := Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square x)) h
  show (Q'.abs x).num * (c.den : Int) ≤ c.num * ((Q'.abs x).den : Int)
  apply Int.not_lt.mp
  intro hcx
  have hcx' : c < Q'.abs x := hcx
  have hx := Q'.lt_of_le_of_lt hc hcx'
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hcx') hc
  have h2 := Q'.mul_lt_mul_of_pos_left hx hcx'
  exact (Int.not_lt.mpr hs) (Q'.lt_of_le_of_lt h1 h2)

private theorem weighted_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -weightedMass w K width p :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => weightedMass w K width p)))

private theorem multiplier_norm_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {m b u : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (C : Certificate (N width) (polyAdd polyOne (polyNeg (polyMul m m))))
    (hu : RatPolyCoeffEqv u (polyMul m b)) :
    weightedMass w K width (polyMul u u) ≤ weightedMass w K width (polyMul b b) := by
  have hn := weightedMass_nonnegative hw0 hw1 K width hK ((Certificate.square b hb).mul C)
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul b b) (polyAdd polyOne (polyNeg (polyMul m m))))
      (polyAdd (polyMul b b) (polyNeg (polyMul u u))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0)) (.add (.const 1) (.neg (.mul (.var 1) (.var 1)))))
      (.add (.mul (.var 0) (.var 0))
        (.neg (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))))
      (by decide) (fun | 0 => b | _ => m)).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (hu.mul hu).symm))
  have he := Q'.eqv_trans _ _ _ (weightedMass_congr w K width hp)
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (weighted_neg w K width _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

private theorem window_order {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    blockWindowLower w K width n t ≤ blockWindowUpper w K width n t :=
  Q'.mul_le_mul_of_nonneg_right _ _ _
    (BF4ExactSlabFixedSpatialTransferMixingRate.kineticFloor_le_cap hw0 hw1 width)
    (Q'.le_of_lt (BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_mass_positive
      hw0 hw1 K width hK (n+t-1)))

private theorem norm_sum_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {b u : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b) (hu : SupportedQuaternionBlocks (N width) u)
    (hnu : weightedMass w K width (polyMul u u) ≤ weightedMass w K width (polyMul b b)) :
    weightedMass w K width (polyMul (polyAdd b u) (polyAdd b u)) ≤
      4*weightedMass w K width (polyMul b b) := by
  have ht : weightedMass w K width (polyMul (polyAdd b u) (polyAdd b u)) ≤
      (weightedMass w K width (polyMul b b) + weightedMass w K width (polyMul b b)) +
        (weightedMass w K width (polyMul u u) + weightedMass w K width (polyMul u u)) := by
    simpa only [weightedMass] using (weighted_square_add_le
      (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK) hb hu)
  exact Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.le_refl' _) (Q'.add_le_add hnu hnu))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (.mul (.const 4) (.var 0)) (by decide)
      (fun _ => weightedMass w K width (polyMul b b)))))

private theorem mixed_budget {x delta B c a d : Q'}
    (hdelta : (0 : Q') ≤ delta) (hB : (0 : Q') ≤ B) (hc : (0 : Q') ≤ c)
    (ha : (0 : Q') ≤ a) (hd : (0 : Q') ≤ d)
    (haB : a ≤ (delta*delta)*B) (hdB : d ≤ 4*B)
    (h : x*x ≤ (c*c)*(a*d)) : Q'.abs x ≤ 2*delta*c*B := by
  have hcc := Q'.mul_nonneg _ _ hc hc
  have haB0 := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hdelta hdelta) hB
  have had := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ haB hd)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hdB haB0)
  have hbound := Q'.le_trans' _ _ _ h
    (Q'.mul_le_mul_of_nonneg_left _ _ _ had hcc)
  apply abs_le_square
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hdelta) hc) hB)
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0))
      (.mul (.mul (.mul (.var 1) (.var 1)) (.var 2)) (.mul (.const 4) (.var 2))))
    (.mul (.mul (.mul (.mul (.const 2) (.var 1)) (.var 0)) (.var 2))
      (.mul (.mul (.mul (.const 2) (.var 1)) (.var 0)) (.var 2)))
    (by decide) (fun | 0 => c | 1 => delta | _ => B)))

/-- Actual original partitions and norm determine the finite error coefficient. -/
def blockEnergyErrorCoefficient (w : Q') (K width n t : Nat) (psi : RatPoly) : Q' :=
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  2 * (weightedMass w K width (polyMul A (transferStep w K width A)) +
    weightedMass w K width (polyMul A A) * transferWeightedCap w K width) *
    weightedMass w K width (polyMul b b)

theorem blockEnergyErrorCoefficient_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) :
    (0 : Q') ≤ blockEnergyErrorCoefficient w K width n t psi :=
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let hA := terminalMessage_supported w K width (n+t)
  let hb := source_supported w K width n t hp
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
      (Q'.zero_le_add _ _
        (transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width A hA)
        (Q'.mul_nonneg _ _
          (weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square A hA))
          (transferWeightedCap_nonnegative hw0 hw1 K width hK))))
    (weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square b hb))

/-- The COMPLETE signed remainder vanishes with explicit relative rate.
Zero norms/rates are included; no favorable sign of this remainder is assumed. -/
theorem blockConditionalRatio_signedCost_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    Q'.abs (signedMultiplicationCost w K width A b
      (blockConditionalRatio hw0 hw1 K width hK n t psi k)) ≤
      (mixRate hw0 hw1 width)^k * blockEnergyErrorCoefficient w K width n t psi := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let u := polyMul A phi
  let e := polyAdd b (polySmul (-1) u)
  let s := polyAdd b u
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  let c := transferWeightedCap w K width
  let delta := (mixRate hw0 hw1 width)^k
  let x := weightedMass w K width (polyMul e s)
  let y := weightedMass w K width (polyMul e (transferStep w K width s))
  have hA := terminalMessage_supported w K width (n+t)
  have hb := source_supported w K width n t hp
  have hphi := blockConditionalRatio_supported hw0 hw1 K width hK n t hp k
  have hu := supported_polyMul hA hphi
  have he := supported_add hb (support_smul hu (-1))
  have hs := supported_add hb hu
  have hB := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square b hb)
  have hc := transferWeightedCap_nonnegative hw0 hw1 K width hK
  have hZ0 := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square A hA)
  have hZ1 := transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width A hA
  have hd := Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) k
  have hW := blockWindowCertificates hw0 hw1 K width hK n t hdepth
  have hM := multiplierSquareCertificate hA
    (blockWindowLower_positive hw0 hw1 K width hK n t)
    (blockWindowUpper_positive hw0 hw1 K width hK n t)
    (window_order hw0 hw1 K width hK n t) hW.1 hW.2 k
  have hup : RatPolyCoeffEqv u (polyMul (polyMul A (blockReciprocal hw0 hw1 K width hK n t k)) b) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  have hnu := multiplier_norm_le hw0 hw1 K width hK hb hM hup
  have hsn := norm_sum_le hw0 hw1 K width hK hb hu hnu
  have hep : RatPolyCoeffEqv e (polyAdd b (polyNeg u)) :=
    (RatPolyCoeffEqv.refl _).add (neg_smul u).symm
  have heraw := blockConditionalRatio_reconstruction hw0 hw1 K width hK n t hdepth hp k
  have heB : weightedMass w K width (polyMul e e) ≤ (delta*delta)*B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (weightedMass_congr w K width (hep.mul hep)))
      (Q'.le_trans' _ _ _ heraw (Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _ _ (by
          simpa only [Nat.two_mul] using (Q'.pow_add_eqv (mixRate hw0 hw1 width) k k)))))
  have hen := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square e he)
  have hsn0 := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square s hs)
  have hxcs := weightedMass_pair_square_le hw0 hw1 K width hK he hs
  have hx : Q'.abs x ≤ 2*delta*B := by
    have h : x*x ≤ ((1 : Q')*1) *
        (weightedMass w K width (polyMul e e) * weightedMass w K width (polyMul s s)) :=
      Q'.le_trans' _ _ _ hxcs (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 : Q')))
        (Q'.one_mul_eqv _)))
    exact Q'.le_trans' _ _ _ (mixed_budget hd hB Q'.zero_le_one hen hsn0 heB hsn h)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.const 2) (.var 0)) (.const 1)) (.var 1))
        (.mul (.mul (.const 2) (.var 0)) (.var 1)) (by decide)
        (fun | 0 => delta | _ => B)))
  have hy : Q'.abs y ≤ 2*delta*c*B := mixed_budget hd hB hc hen hsn0 heB hsn
    (transferStep_weighted_mixed_square_le hw0 hw1 K width hK he hs)
  have hpin : signedMultiplicationCost w K width A b phi ≈ Z1*x + -(Z0*y) := by
    unfold signedMultiplicationCost
    change weightedMass w K width
      (polyMul e (polyAdd (polySmul Z1 s) (polySmul (-Z0) (transferStep w K width s)))) ≈ _
    exact Q'.eqv_trans _ _ _
      (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right _ _ _))
      (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right Z1 e s))
            (weightedMass_smul w K width Z1 _))
          (Q'.eqv_trans _ _ _
            (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right (-Z0) e _))
            (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-Z0) _)
              (Q'.neg_mul_eqv Z0 y)))))
  have hab : Q'.abs (Z1*x + -(Z0*y)) ≤ Z1*(2*delta*B) + Z0*(2*delta*c*B) := by
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
    apply Q'.add_le_add
    · refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_
      rw [ExpNeg.abs_of_nonneg hZ1]
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ hx hZ1
    · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) ?_
      refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_
      rw [ExpNeg.abs_of_nonneg hZ0]
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ hy hZ0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ hab (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.mul (.const 2) (.var 2)) (.var 4)))
        (.mul (.var 1) (.mul (.mul (.mul (.const 2) (.var 2)) (.var 3)) (.var 4))))
      (.mul (.var 2) (.mul (.mul (.const 2)
        (.add (.var 0) (.mul (.var 1) (.var 3)))) (.var 4))) (by decide)
      (fun | 0 => Z1 | 1 => Z0 | 2 => delta | 3 => c | _ => B))))

/-- Finite reconstruction now meets the exact original energy split.
Neither the energy nor the boundary drift is removed or renamed. -/
theorem blockConditionalRatio_energy_error_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    Q'.abs (clearedRayleighCost w K width A b +
      -(weightedMass w K width (polyMul A A) * energy w K width A phi +
        boundaryDrift w K width A phi)) ≤
      (mixRate hw0 hw1 width)^k * blockEnergyErrorCoefficient w K width n t psi := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let F := weightedMass w K width (polyMul A A) * energy w K width A phi +
    boundaryDrift w K width A phi
  let M := signedMultiplicationCost w K width A b phi
  have hs := clearedRayleighCost_split w K width (source_supported w K width n t hp)
    (supported_polyMul (terminalMessage_supported w K width (n+t))
      (blockConditionalRatio_supported hw0 hw1 K width hK n t hp k))
  have he : clearedRayleighCost w K width A b + -F ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hs (Q'.eqv_refl (-F)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide) (fun | 0 => F | _ => M))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr he))
    (blockConditionalRatio_signedCost_abs_le hw0 hw1 K width hK n t hdepth hp k)

/-- Explicit cutoff for the absolute original signed-energy error. -/
def blockEnergyErrorCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width n t : Nat) (psi : RatPoly) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
    (blockEnergyErrorCoefficient w K width n t psi) epsilon

/-- A computed absolute tolerance on the SAME original signed-energy split,
including zero source norm and zero contraction rate. -/
theorem blockConditionalRatio_energy_error_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : blockEnergyErrorCutoff hw0 hw1 K width n t psi epsilon ≤ k) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    Q'.abs (clearedRayleighCost w K width A b +
      -(weightedMass w K width (polyMul A A) * energy w K width A phi +
        boundaryDrift w K width A phi)) ≤ epsilon :=
  Q'.le_trans' _ _ _
    (blockConditionalRatio_energy_error_abs_le hw0 hw1 K width hK n t hdepth hp k)
    (PositiveContractionResidual.geometric_bound
      (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
      (blockEnergyErrorCoefficient_nonnegative hw0 hw1 K width hK n t hp)
      hepsilon k hk)

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy.blockEnergyErrorCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy.blockEnergyErrorCoefficient_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy.blockConditionalRatio_signedCost_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy.blockConditionalRatio_energy_error_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy.blockEnergyErrorCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy.blockConditionalRatio_energy_error_tolerance
