/-
# ORIGINAL shared-output heat interpolation endpoints

At r=1 the finite incoming heat flow reproduces its original source under
every Haar insertion. At r=w the conditional nome-one packet is evaluated
only through its PARTICULAR supported-source reproduction theorem: first
for V(w)^2, then for V(w). Coordinate substitution is used only on the
coefficient identity for a product, never on a generic Haar-carrier equality.
The explicit cutoff belongs to this fixed source and its square-row skeleton.
These are endpoint identities, not positivity at nome one, conditional
variance, changing-family uniformity, or a physical generator claim.
-/

import YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation
import YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport
import YMGap.Continuum.RatPolyNomeRowCutoff
import YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint

namespace YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularDerivative (angularDerivative)
open YMGap.Continuum.QuaternionHaarAngularCarrier (angularDerivative_carrier)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularSquare six)
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionConditionalHeatGenerator
  (finiteConditionalKernel finiteConditionalKernel_original_pin nomeCoefficient)
open YMGap.Continuum.SU2QuaternionHeadHeatFiniteFlow
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator (nomeHeatPolynomial finiteNomeFlow finiteNomeFlow_original_pin)
open YMGap.Continuum.SU2QuaternionHeadHeatCurves (squareNomeRows squareNomeRows_eval)
open YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport (finiteNomeFlow_supported nomeHeatPolynomial_supported)
open YMGap.Continuum.RatPolyNomeRows
open YMGap.Continuum.RatPolyNomeRowCutoff
open YMGap.Continuum.SU2QuaternionConditionalHeatComposition
open YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
  (substituteRetained substituteRetained_mul substituteRetained_congr)
open YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)

local infix:50 " ≈ " => Q'.eqv

private theorem eval_argument {u v : Q'} (h : u ≈ v) :
    ∀ p : Poly, QPoly.eval p u ≈ QPoly.eval p v
  | [] => Q'.eqv_refl _
  | c::p => Q'.add_eqv_congr_left c _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
        (Q'.mul_eqv_congr_left _ _ _ (eval_argument h p)))

private theorem finite_kernel_congr {u v : Q'} (h : u ≈ v) (K : Nat) :
    RatPolyCoeffEqv (finiteConditionalKernel u K) (finiteConditionalKernel v K) := by
  have hs : ∀ ids : List Nat,
      RatPolyCoeffEqv
        (finitePolySum (fun spin => polySmul (QPoly.eval (nomeCoefficient spin) u)
          (SU2QuaternionRelativeCharacterSelection.relativeCharacter spin)) ids)
        (finitePolySum (fun spin => polySmul (QPoly.eval (nomeCoefficient spin) v)
          (SU2QuaternionRelativeCharacterSelection.relativeCharacter spin)) ids) := by
    intro ids
    induction ids with
    | nil => exact .refl _
    | cons spin ids ih =>
        exact (RatPolyCoeffEqv.smul_coefficient (eval_argument h _) _).add ih
  exact hs (List.range (K+1))

private theorem conditional_nome_congr {u v : Q'} (h : u ≈ v) (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat u K p) (conditionalHeat v K p) :=
  partialHaarHead_congr
    (((finiteConditionalKernel_original_pin u K).symm.trans
      ((finite_kernel_congr h K).trans (finiteConditionalKernel_original_pin v K))).mul_right p)

private theorem angular_square_carrier {blocks : Nat} (hb : 0<blocks)
    {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (angularSquare p) (angularSquare q) := by
  have hd (i j : Nat) (hi : i<4) (hj : j<4) := angularDerivative_carrier hb hi hj h
  have hs (i j : Nat) (hi : i<4) (hj : j<4) :=
    HaarCarrierEqv.mul (hd i j hi hj) (hd i j hi hj)
  exact HaarCarrierEqv.add (hs 0 1 (by decide) (by decide))
    (HaarCarrierEqv.add (hs 0 2 (by decide) (by decide))
      (HaarCarrierEqv.add (hs 0 3 (by decide) (by decide))
        (HaarCarrierEqv.add (hs 1 2 (by decide) (by decide))
          (HaarCarrierEqv.add (hs 1 3 (by decide) (by decide)) (hs 2 3 (by decide) (by decide))))))

private theorem square_rows_supported (tail : Nat) (p : RatPoly) :
    ∀ row, row ∈ squareNomeRows tail p → SupportedQuaternionBlocks (tail+1) row.2 := by
  intro row hrow
  obtain ⟨a, ha, hrow⟩ := List.mem_flatMap.mp hrow
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hrow
  exact supported_polyMul (nomeHeatPolynomial_supported tail p a ha)
    (nomeHeatPolynomial_supported tail p b hb)

/-- Actual finite-flow endpoint on the SAME source carrier; its auxiliary
head prefix is computed internally from the source. -/
theorem finiteNomeFlow_one_carrier (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (finiteNomeFlow tail p 1) p :=
  (finiteNomeFlow_original_pin tail 1 (inputCutoff tail p) p hp (Nat.le_refl _)).trans
    (headMap_one_reproduction tail (inputCutoff tail p) p hp (Nat.le_refl _))

/-- The original r=1 square endpoint, including arbitrary dependence on the
already-existing output and all spectators. -/
theorem squareInterpolation_one (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv tail (squareInterpolation tail w K p 1)
      (conditionalHeat w K (polyMul p p)) := by
  have hv := finiteNomeFlow_one_carrier tail p hp
  have hw : w*Q'.recip 1 ≈ w := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _ (by decide : Q'.eqv (Q'.recip 1) 1)) (Q'.mul_one_eqv w)
  exact (RatPolyCoeffEqv.haarCarrier (squareInterpolation_original_pin tail w K p 1 (by decide))).trans
    ((conditionalHeat_carrier tail _ K (HaarCarrierEqv.mul hv hv)).trans
      (RatPolyCoeffEqv.haarCarrier (conditional_nome_congr hw K _)))

/-- Actual original r=1 angular endpoint; angular carrier compatibility is
proved by integration by parts, not a diagonal substitution. -/
theorem angularInterpolation_one (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv tail (angularInterpolation tail w K p 1)
      (conditionalHeat w K (angularSquare p)) := by
  have hv := angular_square_carrier (Nat.zero_lt_succ tail) (finiteNomeFlow_one_carrier tail p hp)
  have hw : w*Q'.recip 1 ≈ w :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _ (by decide : Q'.eqv (Q'.recip 1) 1)) (Q'.mul_one_eqv w)
  exact (RatPolyCoeffEqv.haarCarrier (angularInterpolation_original_pin tail w K p 1 (by decide))).trans
    ((conditionalHeat_carrier tail _ K hv).trans
      (RatPolyCoeffEqv.haarCarrier (conditional_nome_congr hw K _)))

/-- Fixed-source bound retaining its incoming modes, finite flow and square
at every nome. It makes no claim for a changing row skeleton. -/
def interpolationEndpointCutoff (tail : Nat) (p : RatPoly) : Nat :=
  max (inputCutoff tail p)
    (max (rowCutoff (tail+1) (nomeHeatPolynomial tail p))
      (rowCutoff (tail+1) (squareNomeRows tail p)))

/-- The true left square endpoint F(w)=(C_w p)^2 at the ORIGINAL retained
output. Only the particular source endpoint is substituted; no general Haar
equality is pulled through identification of input and output coordinates. -/
theorem squareInterpolation_left_endpoint (tail : Nat) (ht : 0<tail)
    (w : Q') (hw : (0:Q')<w) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : interpolationEndpointCutoff tail p ≤ K) :
    HaarCarrierEqv tail (squareInterpolation tail w K p w)
      (polyMul (conditionalHeat w K p) (conditionalHeat w K p)) := by
  let V := finiteNomeFlow tail p w
  have hinput : inputCutoff tail p ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have hrows : max (rowCutoff (tail+1) (nomeHeatPolynomial tail p))
      (rowCutoff (tail+1) (squareNomeRows tail p)) ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) hK
  have hvcut : SU2QuaternionPolynomialHarmonicExpansion.modeCutoff (tail+1) V ≤ K := by
    change SU2QuaternionPolynomialHarmonicExpansion.modeCutoff (tail+1)
      (evalRows (nomeHeatPolynomial tail p) w) ≤ K
    rw [rowCutoff_spec (tail+1) (Nat.zero_lt_succ tail)]
    exact Nat.le_trans (Nat.le_max_left _ _) hrows
  have hsqcut : SU2QuaternionPolynomialHarmonicExpansion.modeCutoff (tail+1)
      (evalRows (squareNomeRows tail p) w) ≤ K := by
    rw [rowCutoff_spec (tail+1) (Nat.zero_lt_succ tail)]
    exact Nat.le_trans (Nat.le_max_right _ _) hrows
  have hV := finiteNomeFlow_supported tail p w
  have hsq : RatPolyCoeffEqv (evalRows (squareNomeRows tail p) w) (polyMul V V) :=
    squareNomeRows_eval tail p w
  have hsquare : HaarCarrierEqv tail (conditionalHeat 1 K (polyMul V V))
      (substituteRetained (polyMul V V)) :=
    (conditionalHeat_carrier tail 1 K (RatPolyCoeffEqv.haarCarrier hsq.symm)).trans
      ((conditionalHeat_one_endpoint tail ht K (evalRows (squareNomeRows tail p) w)
        (evalRows_supported _ (square_rows_supported tail p) w) hsqcut).trans
          (RatPolyCoeffEqv.haarCarrier (substituteRetained_congr hsq)))
  have hendpoint := conditionalHeat_one_endpoint tail ht K V hV hvcut
  have hmixed : HaarCarrierEqv tail (conditionalHeat 1 K V) (conditionalHeat w K p) :=
    (conditionalHeat_carrier tail 1 K (finiteNomeFlow_original_pin tail w K p hp hinput)).trans
      ((conditionalHeat_headMap_composition tail ht 1 w K p hp).trans
        (RatPolyCoeffEqv.haarCarrier (conditional_nome_congr (Q'.one_mul_eqv w) K p)))
  have hsubst := hendpoint.symm.trans hmixed
  exact (RatPolyCoeffEqv.haarCarrier (squareInterpolation_original_pin tail w K p w hw)).trans
    ((RatPolyCoeffEqv.haarCarrier (conditional_nome_congr (Q'.mul_recip_eqv w hw) K _)).trans
      (hsquare.trans ((RatPolyCoeffEqv.haarCarrier (substituteRetained_mul V V)).trans
        (HaarCarrierEqv.mul hsubst hsubst))))

end YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints

#print axioms YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints.finiteNomeFlow_one_carrier
#print axioms YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints.squareInterpolation_one
#print axioms YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints.angularInterpolation_one
#print axioms YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints.interpolationEndpointCutoff
#print axioms YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints.squareInterpolation_left_endpoint
