/-
# The original temporal covariance defect as a full-weight conditional pairing

Let m(f)=H[V*f], g=T^n1, p=g*Tg and Z=m(p). The polarized defect is
  C_delta(r,s)=Z*(m(p*r*s)-m((g*r)*T(g*s)))
                -delta*(Z*m(p*r*s)-m(p*r)*m(p*s)).
Its exact test in H[(V*g)*r*F_s] is
  F_s=Z*(1-delta)*(Tg)*s-Z*T(g*s)+delta*m(p*s)*(Tg).
The last term is essential: the conditional residual need not have zero
mean in the original temporal marginal.

For the actual weighted residual, conditional Haar integration gives its
full-weight covariance determinant against F_s. All original spatial and
terminal factors remain, including those using the selected link. This
pins the analytic target to the original temporal form; it neither removes
source-dependent factors nor assumes their response is small.

The diagonal statement is exactly the existing energy/variance inequality.
Its known width-dependent fraction is recovered as a consistency check.
OPEN: improved signed cross control and a weighted stable decomposition,
with the spatial/scaling uniformity required by the continuum route.
No new uniform gap or Clay frontier closure is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixFraction)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity (terminalResidual)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project project_mean)
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] weightedMass spatialWeight baseLinks transferStep

/-- The SAME partition-cleared polarized energy/variance defect, with no
assumed centering, positivity or uniform estimate. -/
def clearedDefect (w delta : Q') (K width : Nat) (g r s : RatPoly) : Q' :=
  let p := polyMul g (transferStep w K width g)
  let Z := weightedMass w K width p
  let A := weightedMass w K width (polyMul p (polyMul r s))
  let J := weightedMass w K width (polyMul (polyMul g r) (transferStep w K width (polyMul g s)))
  Z*(A + -J) + -(delta*(Z*A +
    -(weightedMass w K width (polyMul p r)*weightedMass w K width (polyMul p s))))

/-- A concrete polynomial test; all transfer and marginal-mean terms survive. -/
def combinedTest (w delta : Q') (K width : Nat) (g s : RatPoly) : RatPoly :=
  let p := polyMul g (transferStep w K width g)
  let Z := weightedMass w K width p
  let B := weightedMass w K width (polyMul p s)
  polyAdd
    (polyAdd
      (polySmul (Z*((1 : Q') + -delta)) (polyMul (transferStep w K width g) s))
      (polySmul (-Z) (transferStep w K width (polyMul g s))))
    (polySmul (delta*B) (transferStep w K width g))

private theorem mass_mul_add (w : Q') (K width : Nat) (a b c : RatPoly) :
    weightedMass w K width (polyMul a (polyAdd b c)) ≈
      weightedMass w K width (polyMul a b) + weightedMass w K width (polyMul a c) :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right a b c))
    (weightedMass_add w K width _ _)

private theorem mass_mul_smul (w : Q') (K width : Nat) (a b : RatPoly) (c : Q') :
    weightedMass w K width (polyMul a (polySmul c b)) ≈
      c * weightedMass w K width (polyMul a b) :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right c a b))
    (weightedMass_smul w K width c _)

/-- Exact original-action pairing. This is unconditional signed algebra;
no source-dependent factor is promoted to an independent spectator. -/
theorem clearedDefect_pairing (w delta : Q') (K width : Nat) (g r s : RatPoly) :
    clearedDefect w delta K width g r s ≈
      quaternionHaar (N width)
        (polyMul (polyMul (spatialWeight w K width) g)
          (polyMul r (combinedTest w delta K width g s))) := by
  let t := transferStep w K width g
  let p := polyMul g t
  let Z := weightedMass w K width p
  let B := weightedMass w K width (polyMul p s)
  let A := weightedMass w K width (polyMul p (polyMul r s))
  let J := weightedMass w K width (polyMul (polyMul g r) (transferStep w K width (polyMul g s)))
  let M := weightedMass w K width (polyMul p r)
  have hA : weightedMass w K width (polyMul (polyMul g r) (polyMul t s)) ≈ A :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => g | 1 => r | 2 => t | _ => s))
  have hM : weightedMass w K width (polyMul (polyMul g r) t) ≈ M :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => g | 1 => r | _ => t))
  have hH : quaternionHaar (N width)
      (polyMul (polyMul (spatialWeight w K width) g)
        (polyMul r (combinedTest w delta K width g s))) ≈
      weightedMass w K width (polyMul (polyMul g r) (combinedTest w delta K width g s)) := by
    unfold weightedMass
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (by decide) (fun
        | 0 => spatialWeight w K width
        | 1 => g
        | 2 => r
        | _ => combinedTest w delta K width g s))
  have hlinear : weightedMass w K width
      (polyMul (polyMul g r) (combinedTest w delta K width g s)) ≈
      (Z*((1 : Q') + -delta))*A + (-Z)*J + (delta*B)*M := by
    unfold combinedTest
    exact Q'.eqv_trans _ _ _ (mass_mul_add w K width _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (mass_mul_add w K width _ _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (mass_mul_smul w K width _ _ _)
              (Q'.mul_eqv_congr_left _ _ _ hA))
            (mass_mul_smul w K width _ _ _)))
        (Q'.eqv_trans _ _ _ (mass_mul_smul w K width _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ hM)))
  have hfinish : (Z*((1 : Q') + -delta))*A + (-Z)*J + (delta*B)*M ≈
      clearedDefect w delta K width g r s :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))) (.var 2))
        (.mul (.neg (.var 0)) (.var 3))) (.mul (.mul (.var 1) (.var 4)) (.var 5)))
      (.add (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
        (.neg (.mul (.var 1) (.add (.mul (.var 0) (.var 2))
          (.neg (.mul (.var 5) (.var 4)))))))
      (by decide) (fun | 0 => Z | 1 => delta | 2 => A | 3 => J | 4 => B | _ => M)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hH (Q'.eqv_trans _ _ _ hlinear hfinish))

/-- Conditional covariance for the ACTUAL terminal residual and full endpoint
weight. Only membership of the integrated block is needed; there is no
centering assumption in the temporal marginal. -/
theorem terminalResidual_clearedDefect (w delta : Q') (K width n i : Nat)
    (hi : i < N width) (f s : RatPoly) :
    let g := terminalMessage w K width n
    let a := polyMul (spatialWeight w K width) g
    let F := combinedTest w delta K width g s
    clearedDefect w delta K width g (terminalResidual w K width n i f) s ≈
      quaternionHaar (N width)
        (polyAdd
          (polyMul (project i a) (project i (polyMul a (polyMul f F))))
          (polyNeg (polyMul (project i (polyMul a f)) (project i (polyMul a F))))) := by
  dsimp only
  exact Q'.eqv_trans _ _ _ (clearedDefect_pairing w delta K width _ _ s)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (project_mean (N width) i hi _))
      (haar_of_coeff (weightedResidual_pairing i _ f _)))

/-- The diagonal defect is nonnegative exactly when the original cleared
energy/variance estimate holds. Delta is not assumed to be the supplied rate. -/
theorem clearedDefect_diagonal_nonnegative_iff (w delta : Q') (K width : Nat) (g f : RatPoly) :
    let p := polyMul g (transferStep w K width g)
    (0 : Q') ≤ clearedDefect w delta K width g f f ↔
      delta*(weightedMass w K width p * weightedMass w K width (polyMul p (polyMul f f)) +
        -(weightedMass w K width (polyMul p f)*weightedMass w K width (polyMul p f))) ≤
      weightedMass w K width p * energy w K width g f := by
  constructor
  · exact Q'.le_of_sub_nonneg
  · exact Q'.sub_nonneg_of_le

/-- Consistency with the existing physical consumer, at its existing
WIDTH-DEPENDENT rate. This does not supply an improved fraction. -/
theorem terminal_existing_fraction_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    (0 : Q') ≤ clearedDefect w (mixFraction hw0 hw1 width) K width
      (terminalMessage w K width n) f f :=
  (clearedDefect_diagonal_nonnegative_iff w _ K width _ f).mpr
    (terminal_energy_variance_floor hw0 hw1 K width hK n hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance.clearedDefect
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance.combinedTest
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance.clearedDefect_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance.terminalResidual_clearedDefect
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance.clearedDefect_diagonal_nonnegative_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance.terminal_existing_fraction_nonnegative
