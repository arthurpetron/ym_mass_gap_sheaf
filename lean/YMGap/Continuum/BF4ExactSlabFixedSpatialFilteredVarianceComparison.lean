/-
# Finite terminal-depth comparison of the SAME filtered variance

The constructed terminal bracket and the sharp original Schur closure
compare b_u=T^u(g_n*psi) with b_(u+d), retaining their distinct partitions.
The cleared bound contains (1+comparisonEta(n+u-1))^2, independent of d.
There is no inverse surviving norm, finite stationarity or terminal
eigenpin.  This pays finite window approximation errors; it is not a
macroscopic survival lower bound or a changing-family estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurClosure
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (Bracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurClosure
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage weightedMass

private theorem mass_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -(weightedMass w K width p) :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

private theorem mass_difference (w : Q') (K width : Nat) (p q : RatPoly) :
    weightedMass w K width (polyAdd p (polyNeg q)) ≈
      weightedMass w K width p + -(weightedMass w K width q) :=
  Q'.eqv_trans _ _ _ (weightedMass_add w K width p (polyNeg q))
    (Q'.add_eqv_congr_left _ _ _ (mass_neg w K width q))

private theorem negative_scale (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-c) p) (polyNeg (polySmul c p)) :=
  ((neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) c p).trans
    (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 c)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv c))) p))).symm

private theorem terminal_block (w : Q') (K width m d : Nat) :
    originalBlockTransfer w K width d (terminalMessage w K width m) =
      terminalMessage w K width (m+d) := by
  unfold originalBlockTransfer terminalMessage
  exact (iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) m d polyOne).symm

private theorem source_block (w : Q') (K width u d : Nat) (p : RatPoly) :
    originalBlockTransfer w K width d (originalBlockTransfer w K width u p) =
      originalBlockTransfer w K width (u+d) p :=
  (iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) u d p).symm

/-- Literal future/current terminal bracket, with the constructed original
endpoints retained as data.  Its relative width is controlled at n+u-1. -/
def filteredTerminalBracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n u d : Nat) (hdepth : 1 ≤ n+u) :
    Bracket width (terminalMessage w K width (n+u+d)) (terminalMessage w K width (n+u)) :=
  let B := terminalComparison hw0 hw1 K width hK (n+u-1) d 0
  { lower := B.lower
    upper := B.upper
    lowerCertificate := by
      have h0 : n+u-1+1+0 = n+u := by omega
      have h1 : n+u-1+1+d = n+u+d := by omega
      simpa only [h0, h1] using B.lowerCertificate
    upperCertificate := by
      have h0 : n+u-1+1+0 = n+u := by omega
      have h1 : n+u-1+1+d = n+u+d := by omega
      simpa only [h0, h1] using B.upperCertificate }

private theorem bracket_upper_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n u d : Nat) (hdepth : 1 ≤ n+u) :
    (0 : Q') ≤ (filteredTerminalBracket hw0 hw1 K width hK n u d hdepth).upper := by
  let J := filteredTerminalBracket hw0 hw1 K width hK n u d hdepth
  let A := terminalMessage w K width (n+u)
  let F := terminalMessage w K width (n+u+d)
  let a := weightedMass w K width A
  have ha : (0 : Q') < a := terminalMessage_mass_positive hw0 hw1 K width hK (n+u)
  have hF := Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+u+d))
  have hn := weightedMass_nonnegative hw0 hw1 K width hK J.upperCertificate
  have he : weightedMass w K width (polyAdd (polySmul J.upper A) (polySmul (-1) F)) ≈
      J.upper*a + -(weightedMass w K width F) :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr'
        (weightedMass_smul w K width J.upper A)
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) F)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))
  have hu := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))
  exact Q'.nonneg_of_mul_pos ha (Q'.le_trans' _ _ _ hF
    (Q'.le_trans' _ _ _ hu (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-- Squaring the ACTUAL positive lower terminal comparison supplies the
lower chronological partition comparison, without dividing by a mass. -/
theorem filtered_terminal_partition_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n u d : Nat) (hdepth : 1 ≤ n+u) :
    let l := (filteredTerminalBracket hw0 hw1 K width hK n u d hdepth).lower
    (l*l)*weightedMass w K width (polyMul (terminalMessage w K width (n+u))
      (terminalMessage w K width (n+u))) ≤
    weightedMass w K width (polyMul (terminalMessage w K width (n+u+d))
      (terminalMessage w K width (n+u+d))) := by
  dsimp only
  let J := filteredTerminalBracket hw0 hw1 K width hK n u d hdepth
  let A := terminalMessage w K width (n+u)
  let F := terminalMessage w K width (n+u+d)
  let l := J.lower
  have hl : (0 : Q') ≤ l := Q'.le_of_lt
    (terminalComparison_lower_positive hw0 hw1 K width hK (n+u-1) d 0)
  have Psum : Certificate (N width) (polyAdd F (polySmul l A)) :=
    (terminalMessage_certificate hw0 hw1 K width hK (n+u+d)).add
      (.smul l hl (terminalMessage_certificate hw0 hw1 K width hK (n+u)))
  have hid : RatPolyCoeffEqv
      (polyMul (polyAdd F (polySmul (-l) A)) (polyAdd F (polySmul l A)))
      (polyAdd (polyMul F F) (polyNeg (polySmul (l*l) (polyMul A A)))) :=
    (((RatPolyCoeffEqv.refl F).add
        ((negative_scale l A).trans (RatPolyCoeffEqv.neg (cap_mul_left l A).symm))).mul
      ((RatPolyCoeffEqv.refl F).add (cap_mul_left l A).symm)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.neg (.mul (.var 2) (.var 1))))
          (.add (.var 0) (.mul (.var 2) (.var 1))))
        (.add (.mul (.var 0) (.var 0))
          (.neg (.mul (.mul (.var 2) (.var 2)) (.mul (.var 1) (.var 1)))))
        (by decide) (fun | 0 => F | 1 => A | _ => cap l)).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
          (((cap_mul l l).mul_right (polyMul A A)).trans (cap_mul_left (l*l) (polyMul A A))))))
  have hn := weightedMass_nonnegative hw0 hw1 K width hK (J.lowerCertificate.mul Psum)
  have he := Q'.eqv_trans _ _ _ (weightedMass_congr w K width hid)
    (Q'.eqv_trans _ _ _ (mass_difference w K width (polyMul F F) (polySmul (l*l) (polyMul A A)))
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (weightedMass_smul w K width (l*l) (polyMul A A)))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- The finite normalized variance comparison, CLEARED against its two
different positive chronological partitions.  Signed psi and zero filtered
norm are included.  No stationary or useful survival hypothesis appears. -/
theorem filtered_variance_cleared_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n u d : Nat) (hdepth : 1 ≤ n+u)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) :
    let Au := terminalMessage w K width (n+u)
    let At := terminalMessage w K width (n+u+d)
    let bu := originalBlockTransfer w K width u (polyMul (terminalMessage w K width n) psi)
    let bt := originalBlockTransfer w K width (u+d) (polyMul (terminalMessage w K width n) psi)
    let eta := comparisonEta hw0 hw1 width (n+u-1)
    weightedMass w K width (polyMul Au Au)*weightedMass w K width (polyMul bt bt) ≤
      ((1+eta)*(1+eta))*(weightedMass w K width (polyMul At At)*
        weightedMass w K width (polyMul bu bu)) := by
  dsimp only
  let Au := terminalMessage w K width (n+u)
  let At := terminalMessage w K width (n+u+d)
  let bu := originalBlockTransfer w K width u (polyMul (terminalMessage w K width n) psi)
  let bt := originalBlockTransfer w K width (u+d) (polyMul (terminalMessage w K width n) psi)
  let Zu := weightedMass w K width (polyMul Au Au)
  let Zt := weightedMass w K width (polyMul At At)
  let Bu := weightedMass w K width (polyMul bu bu)
  let Bt := weightedMass w K width (polyMul bt bt)
  let J := filteredTerminalBracket hw0 hw1 K width hK n u d hdepth
  let l := J.lower
  let U := J.upper
  let eta := comparisonEta hw0 hw1 width (n+u-1)
  let F := 1+eta
  have hl : (0 : Q') ≤ l := Q'.le_of_lt
    (terminalComparison_lower_positive hw0 hw1 K width hK (n+u-1) d 0)
  have hU : (0 : Q') ≤ U := bracket_upper_nonnegative hw0 hw1 K width hK n u d hdepth
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one
    (comparisonEta_nonnegative hw0 hw1 width (n+u-1))
  have hZu : (0 : Q') ≤ Zu := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square Au (terminalMessage_supported w K width (n+u)))
  have hBu : (0 : Q') ≤ Bu := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square bu (iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) u
      (supported_polyMul (terminalMessage_supported w K width n) hp)))
  have PU : Certificate (N width)
      (polyAdd (polySmul U Au) (polyNeg (originalBlockTransfer w K width d Au))) := by
    have P : Certificate (N width) (polyAdd (polySmul U Au) (polyNeg At)) :=
      Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add (neg_smul At)) J.upperCertificate
    simpa only [Au, At, terminal_block] using P
  have hnorm := original_block_terminal_schur_source_le hw0 hw1 K width hK
    n u d hdepth hp U hU PU
  have hBt : Bt ≤ (U*U)*Bu := by
    simpa only [source_block] using hnorm
  have hw := terminalComparison_relative_width hw0 hw1 K width hK (n+u-1) d 0
  have hUle : U ≤ F*l := by
    have h := Q'.add_le_add_right _ _ l hw
    have heL : U + -l + l ≈ U :=
      poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
        (.var 0) (by decide) (fun | 0 => U | _ => l)
    have heR : eta*l+l ≈ F*l :=
      poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 1))
        (.mul (.add (.const 1) (.var 0)) (.var 1))
        (by decide) (fun | 0 => eta | _ => l)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heL)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv heR))
  have hUsq := Q'.mul_le_mul_of_nonneg hUle hUle (Q'.mul_nonneg _ _ hF hl) hU
  have hUsq' : U*U ≤ (F*F)*(l*l) := Q'.le_trans' _ _ _ hUsq
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => F | _ => l)))
  have hlower : (l*l)*Zu ≤ Zt := filtered_terminal_partition_lower hw0 hw1 K width hK n u d hdepth
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ Zu hBt hZu
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _ Bu hUsq' hBu
  have h3 := Q'.mul_le_mul_of_nonneg_left _ _ Zu h2 hZu
  have hreorder : Zu*(((F*F)*(l*l))*Bu) ≈ (F*F)*(((l*l)*Zu)*Bu) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.var 3)))
      (.mul (.mul (.var 1) (.var 1)) (.mul (.mul (.mul (.var 2) (.var 2)) (.var 0)) (.var 3)))
      (by decide) (fun | 0 => Zu | 1 => F | 2 => l | _ => Bu)
  have h4 := Q'.mul_le_mul_of_nonneg_left _ _ (F*F)
    (Q'.mul_le_mul_of_nonneg_right _ _ Bu hlower hBu) (SumOfSquares.q_mul_self_nonneg F)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h3
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) h4))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison.filteredTerminalBracket
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison.filtered_terminal_partition_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison.filtered_variance_cleared_le
