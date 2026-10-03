/-
# Uniform Haar shape of the ACTUAL small-nome cube terminal message

The retained representative is already pinned to the original terminal under
every supported Haar insertion. Here its centered Haar square is bounded by
a fixed rational radius times its OWN Haar mass squared, at every depth and
every cutoff satisfying both original guards. The six shared action factors
and every retained kinetic factor stay in the constructed proof.

This square-root-free induction combines the certified heat deviation 1/1000
with action deviation 1/128. It is not an interacting OWN-variance estimate,
a favorable gain theorem, or a changing-family survival assertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor
import YMGap.Continuum.SU2QuaternionProductHeatCertifiedFloorContraction
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment
import YMGap.Continuum.SU2QuaternionProductHeatConstant
import YMGap.Continuum.SU2QuaternionProductHeatLocalBand
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
  (cubeWeight cubeTransfer cubeIndices cubeIndices_nodup cubeIndices_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome smallNome_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval (cubeInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
  (quaternionHaar_partialHaarHeads)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand (erasedCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatCertifiedFloorContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks cubeWeight

def terminalRadius : Q' := Q'.mkPos 1 80000 (by decide)

private def center (p : RatPoly) (a : Q') : RatPoly :=
  polyAdd p (polyNeg (cap a))

private theorem neg_supported {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    SupportedQuaternionBlocks N (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem center_supported {p : RatPoly} (hp : SupportedQuaternionBlocks N p) (a : Q') :
    SupportedQuaternionBlocks N (center p a) :=
  supported_add hp (neg_supported (SquareBound.constant N a).support)

private theorem haar_neg : ∀ p : RatPoly,
    quaternionHaar N (polyNeg p) ≈ -(quaternionHaar N p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono N t.1)) (haar_neg rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_one : quaternionHaar N polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one N)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem haar_cap (a : Q') : quaternionHaar N (cap a) ≈ a :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul N a polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ haar_one) (Q'.mul_one_eqv a))

private theorem center_shifted (p : RatPoly) (a : Q') :
    RatPolyCoeffEqv (center p a) (shifted p a) := by
  unfold center shifted cap
  exact ((RatPolyCoeffEqv.one_smul p).symm.add
    ((neg_smul (polySmul a polyOne)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) a polyOne).trans
        (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv 1 a) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))) polyOne))))

private theorem center_mean (p : RatPoly) (a : Q') :
    quaternionHaar N (center p a) ≈ quaternionHaar N p - a :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (haar_neg _) (Q'.neg_eqv_congr _ _ (haar_cap a))))

private theorem center_square_pin {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    quaternionHaar N (polyMul (center p (quaternionHaar N p))
      (center p (quaternionHaar N p))) ≈
    quaternionHaar N (polyMul p p) - quaternionHaar N p * quaternionHaar N p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N)
    ((center_shifted p _).mul (center_shifted p _))) (bare_mean_pin hp)

private theorem center_square_le {p : RatPoly} (hp : SupportedQuaternionBlocks N p) (a : Q') :
    quaternionHaar N (polyMul (center p (quaternionHaar N p)) (center p (quaternionHaar N p))) ≤
      quaternionHaar N (polyMul (center p a) (center p a)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (center_square_pin hp))
    (Q'.le_trans' _ _ _ (bare_variance_le_shifted hp a)
      (Q'.le_of_eqv (Q'.eqv_symm (haar_of_coeff (blocks := N)
        ((center_shifted p a).mul (center_shifted p a))))))

private theorem ids_lt (i : Nat) (hi : i ∈ cubeIndices) : i < N :=
  activeBlocks_lt 2 i (cubeIndices_active i hi)

private def V (K : Nat) : RatPoly := cubeWeight smallNome K
private def M (K : Nat) (p : RatPoly) : RatPoly := productMap N smallNome K cubeIndices p

private theorem map_supported (K : Nat) {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    SupportedQuaternionBlocks N (M K p) := productMap_supported N smallNome K cubeIndices ids_lt hp

private theorem map_mean (K : Nat) {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    quaternionHaar N (M K p) ≈ quaternionHaar N p :=
  Q'.eqv_trans _ _ _ (quaternionHaar_partialHaarHeads N N _)
    (productHeat_lower_marginal N smallNome K cubeIndices cubeIndices_nodup ids_lt p hp)

/-- Constructive positivity of the actual retained terminal representative,
transported from the full original action, not presumed scalar positivity. -/
def cubeTerminal_certificate (K : Nat) (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    Certificate N (cubeTerminal K n) :=
  .transport (carrier_of_supported (cubeTerminal_supported K n)
    (terminalMessage_supported smallNome K 2 n) (terminalMessage_cubeTerminal K n).symm)
    (terminalMessage_certificate smallNome_pos (by decide) K 2 hhead n)

/-- Exact input-weighted Haar mass of the next literal cube terminal. -/
theorem cubeTerminal_mean_pin (K n : Nat) :
    quaternionHaar N (cubeTerminal K (n+1)) ≈
      quaternionHaar N (polyMul (cubeWeight smallNome K) (cubeTerminal K n)) :=
  map_mean K (supported_polyMul
    (by
      unfold cubeWeight
      exact YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence.heatProduct_supported
        smallNome K 2 YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer.cubeFaces)
    (cubeTerminal_supported K n))

private theorem action_mass_pin (K n : Nat) :
    quaternionHaar N (polyMul (V K) (cubeTerminal K n)) ≈
      quaternionHaar N (cubeTerminal K n) +
        quaternionHaar N (polyMul (cubeTerminal K n)
          (polyAdd (V K) (polyNeg polyOne))) := by
  have hp : RatPolyCoeffEqv (polyMul (V K) (cubeTerminal K n))
      (polyAdd (cubeTerminal K n)
        (polyMul (cubeTerminal K n) (polyAdd (V K) (polyNeg polyOne)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 1))
      (.add (.var 1) (.mul (.var 1) (.add (.var 0) (.neg (.const 1)))))
      (by decide) (fun
        | 0 => V K
        | _ => cubeTerminal K n)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) hp) (quaternionHaar_append N _ _)

/-- Positive action deviation bounds the ACTUAL terminal normalization ratio;
the Haar mass and the original weighted odd mass are not identified. -/
theorem cubeTerminal_mass_lower (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (1-actionDeviation)*quaternionHaar N (cubeTerminal K n) ≤
      quaternionHaar N (cubeTerminal K (n+1)) := by
  let a := quaternionHaar N (cubeTerminal K n)
  let e := quaternionHaar N (polyMul (cubeTerminal K n) (polyAdd (V K) (polyNeg polyOne)))
  have hab : Q'.abs e ≤ actionDeviation*a :=
    (sharpCubeRemainder K hK).weighted_haar_bound (cubeTerminal_certificate K hhead n)
  have hl : -(actionDeviation*a) ≤ e :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hab)
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs e))
        (Q'.le_of_eqv (Q'.neg_neg_eqv e)))
  have he : a + -(actionDeviation*a) ≈ (1-actionDeviation)*a :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
      (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)) (by decide) (fun
        | 0 => a
        | _ => actionDeviation)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left a _ _ hl)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (action_mass_pin K n))
        (Q'.eqv_symm (cubeTerminal_mean_pin K n)))))

theorem cubeTerminal_mass_positive (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (0 : Q') < quaternionHaar N (cubeTerminal K n) := by
  induction n with
  | zero =>
      exact HeatKernelRGStep.lt_of_lt_of_le (by decide : (0 : Q') < 1)
        (Q'.ge_of_eqv haar_one)
  | succ n ih =>
      exact HeatKernelRGStep.lt_of_lt_of_le
        (Q'.mul_pos (by decide : (0 : Q') < 1-actionDeviation) ih)
        (cubeTerminal_mass_lower K hK hhead n)

private theorem square_insertion_le {p : RatPoly} {c : Q'} (P : SquareBound N p c)
    {g : RatPoly} (hg : SupportedQuaternionBlocks N g) :
    quaternionHaar N (polyMul (polyMul p g) (polyMul p g)) ≤
      c * quaternionHaar N (polyMul g g) := by
  let B := polyMul g g
  have hpos := ((Certificate.square g hg).mul P.certificate).haar_nonnegative
  have he : quaternionHaar N (polyMul B (gap c p)) ≈
      c*quaternionHaar N B - quaternionHaar N (polyMul (polyMul p g) (polyMul p g)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N)
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 1) (.var 1)) (.add (.var 2) (.neg (.mul (.var 0) (.var 0)))))
        (.add (.mul (.var 2) (.mul (.var 1) (.var 1)))
          (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))
        (by decide) (fun
          | 0 => p
          | 1 => g
          | _ => cap c)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (cap_mul_left c B))
            (quaternionHaar_polySmul N c B)) (haar_neg _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

private theorem mean_centered_map (K : Nat) {p : RatPoly}
    (_hp : SupportedQuaternionBlocks N p) :
    SupportedHaarEqv N (M K (center p (quaternionHaar N p)))
      (center (M K p) (quaternionHaar N p)) := by
  have hcap := productMap_cap N smallNome K cubeIndices cubeIndices_nodup ids_lt
    (quaternionHaar N p)
  have hneg : SupportedHaarEqv N (polyNeg (M K (cap (quaternionHaar N p))))
      (polyNeg (cap (quaternionHaar N p))) :=
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier (neg_smul _))).trans
      ((hcap.smul (-1)).trans
        (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier (neg_smul _).symm)))
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
    ((productMap_add N smallNome K cubeIndices p (polyNeg (cap (quaternionHaar N p)))).trans
      ((RatPolyCoeffEqv.refl _).add
        (productMap_neg N smallNome K cubeIndices (cap (quaternionHaar N p))))))).trans
    ((SupportedHaarEqv.refl N _).add hneg)

private theorem centered_map_square_bound (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) {p : RatPoly} (hp : SupportedQuaternionBlocks N p) :
    quaternionHaar N (polyMul
      (center (M K p) (quaternionHaar N (M K p)))
      (center (M K p) (quaternionHaar N (M K p)))) ≤
    (heatDeviation*heatDeviation)*quaternionHaar N
      (polyMul (center p (quaternionHaar N p)) (center p (quaternionHaar N p))) := by
  let c := center p (quaternionHaar N p)
  have hc := center_supported hp (quaternionHaar N p)
  have hz : quaternionHaar N c ≈ 0 := Q'.eqv_trans _ _ _ (center_mean p _)
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => quaternionHaar N p))
  have hbound := productMap_centered_square_bound N smallNome_pos (by decide) K hhead
    heatDeviation (by decide) (by decide) cubeIndices cubeIndices_nodup ids_lt
    (fun i hi => heatAtSharpFloor
      (by
        have hin := ids_lt i hi
        omega)
      (by
        have hin := ids_lt i hi
        omega) K hK) hc hz
  have he := carrier_of_supported (map_supported K hc)
    (center_supported (map_supported K hp) (quaternionHaar N p)) (mean_centered_map K hp)
  have hmass := map_mean K hp
  have hconst : RatPolyCoeffEqv (center (M K p) (quaternionHaar N (M K p)))
      (center (M K p) (quaternionHaar N p)) :=
    (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
      (RatPolyCoeffEqv.smul_coefficient hmass polyOne))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (blocks := N) (hconst.mul hconst)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (Q'.eqv_symm (haar_of_carrier (HaarCarrierEqv.mul he he)))) hbound)

/-- Uniform terminal shape at every original guarded cutoff and depth.
The centered polynomial is literally g_n minus its OWN Haar mass constant. -/
theorem cubeTerminal_variance_bound (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    quaternionHaar N (polyMul
      (polyAdd (cubeTerminal K n) (polyNeg (cap (quaternionHaar N (cubeTerminal K n)))))
      (polyAdd (cubeTerminal K n) (polyNeg (cap (quaternionHaar N (cubeTerminal K n)))))) ≤
    (terminalRadius*terminalRadius) *
      (quaternionHaar N (cubeTerminal K n) * quaternionHaar N (cubeTerminal K n)) := by
  induction n with
  | zero =>
      have he := center_square_pin (supported_one N)
      have hz : quaternionHaar N (polyMul (center polyOne (quaternionHaar N polyOne))
          (center polyOne (quaternionHaar N polyOne))) ≈ 0 :=
        Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _
            (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul polyOne)) haar_one)
            (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _ haar_one)
              (Q'.mul_eqv_congr_left _ _ _ haar_one)))) (by decide))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz)
        (Q'.mul_nonneg _ _ (by decide)
          (SumOfSquares.q_mul_self_nonneg (quaternionHaar N polyOne)))
  | succ n ih =>
      let g := cubeTerminal K n
      let a := quaternionHaar N g
      let d := center g a
      let e := polyAdd (V K) (polyNeg polyOne)
      let p := polyMul (V K) g
      let m := quaternionHaar N p
      have hg := cubeTerminal_supported K n
      have hV : SupportedQuaternionBlocks N (V K) := (cubeInterval K hK).support
      have hp := supported_polyMul hV hg
      have hd := center_supported hg a
      have he := (sharpCubeRemainder K hK).support
      have haa : (0 : Q') ≤ a*a := SumOfSquares.q_mul_self_nonneg a
      have hnorm : quaternionHaar N (polyMul g g) ≤ (1+terminalRadius*terminalRadius)*(a*a) := by
        have hh := Q'.add_le_add_right _ _ (a*a) ih
        have hpin : quaternionHaar N (polyMul d d) + a*a ≈ quaternionHaar N (polyMul g g) :=
          Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (center_square_pin hg))
            (poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
              (.var 0) (by decide) (fun
                | 0 => quaternionHaar N (polyMul g g)
                | _ => a*a))
        have hr : (terminalRadius*terminalRadius)*(a*a)+a*a ≈
            (1+terminalRadius*terminalRadius)*(a*a) :=
          poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 1))
            (.mul (.add (.const 1) (.var 0)) (.var 1)) (by decide) (fun
              | 0 => terminalRadius*terminalRadius
              | _ => a*a)
        exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin)
          (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv hr))
      have heg : quaternionHaar N (polyMul (polyMul e g) (polyMul e g)) ≤
          ((actionDeviation*actionDeviation)*(1+terminalRadius*terminalRadius))*(a*a) :=
        Q'.le_trans' _ _ _
          (square_insertion_le
            (QuaternionHaarIntervalSecondMoment.Interval.squareBound
              (sharpCubeRemainder K hK)) hg)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hnorm (by decide))
            (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)))
      have htri := weighted_square_add_bound (Certificate.one N) (supported_polyMul he hg) hd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul _))) heg)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul _))) ih)
      have hdecomp : RatPolyCoeffEqv (center p a) (polyAdd (polyMul e g) d) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
          (.add (.mul (.add (.var 0) (.neg (.const 1))) (.var 1))
            (.add (.var 1) (.neg (.var 2)))) (by decide) (fun
              | 0 => V K
              | 1 => g
              | _ => cap a)
      have hraw : quaternionHaar N (polyMul (center p a) (center p a)) ≤
          2*((actionDeviation*actionDeviation)*(1+terminalRadius*terminalRadius)+
            terminalRadius*terminalRadius)*(a*a) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (blocks := N) (hdecomp.mul hdecomp)))
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.eqv_symm (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul _))))
            (Q'.le_trans' _ _ _ htri (Q'.le_of_eqv
              (poly_identity_of_normal_eq
                (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))
                  (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
                (.mul (.mul (.const 2) (.add (.var 0) (.var 1))) (.var 2))
                (by decide) (fun
                  | 0 => (actionDeviation*actionDeviation)*(1+terminalRadius*terminalRadius)
                  | 1 => terminalRadius*terminalRadius
                  | _ => a*a)))))
      have hinput := Q'.le_trans' _ _ _ (center_square_le hp a) hraw
      have houtput := Q'.le_trans' _ _ _ (centered_map_square_bound K hK hhead hp)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hinput (by decide))
      have hscalar : (heatDeviation*heatDeviation)*
          (2*((actionDeviation*actionDeviation)*(1+terminalRadius*terminalRadius)+
            terminalRadius*terminalRadius)*(a*a)) ≤
          (terminalRadius*terminalRadius)*(((1-actionDeviation)*a)*((1-actionDeviation)*a)) := by
        have hconst : (heatDeviation*heatDeviation)*
            (2*((actionDeviation*actionDeviation)*(1+terminalRadius*terminalRadius)+
              terminalRadius*terminalRadius)) ≤
            (terminalRadius*terminalRadius)*((1-actionDeviation)*(1-actionDeviation)) := by decide
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
          (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hconst haa)
            (Q'.le_of_eqv (poly_identity_of_normal_eq
              (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
              (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
              (by decide) (fun
                | 0 => terminalRadius*terminalRadius
                | 1 => 1-actionDeviation
                | _ => a))))
      have hmass : (1-actionDeviation)*a ≤ quaternionHaar N (cubeTerminal K (n+1)) :=
        cubeTerminal_mass_lower K hK hhead n
      have hlow0 : (0 : Q') ≤ (1-actionDeviation)*a :=
        Q'.mul_nonneg _ _ (by decide)
          (Q'.le_of_lt (cubeTerminal_mass_positive K hK hhead n))
      have hsquare := Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hmass hlow0)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hmass
          (Q'.le_of_lt (cubeTerminal_mass_positive K hK hhead (n+1))))
      exact Q'.le_trans' _ _ _ houtput
        (Q'.le_trans' _ _ _ hscalar
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hsquare (by decide)))

#print axioms terminalRadius
#print axioms cubeTerminal_certificate
#print axioms cubeTerminal_mean_pin
#print axioms cubeTerminal_mass_lower
#print axioms cubeTerminal_mass_positive
#print axioms cubeTerminal_variance_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalVariance
