/-
# Raw moment mismatch controlled by the actual product-heat loss

The positive product heat of total mass one gives a positive loss form I-P.
Its sharp Cauchy--Schwarz estimate controls the difference between a raw
source-square moment and the SAME source moment with its heat factor retained.
No independence, eigenpin, mean substitution or small-loss premise is used.
This is an estimate in an explicit source heat loss, not a useful scaling
estimate for that loss or an identification of raw and interacting variance.
-/

import YMGap.Continuum.SU2QuaternionProductHeatJumpMean
import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy

namespace YMGap.Continuum.SU2QuaternionProductHeatMomentDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatJumpMean
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem qmul {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- The actual symmetric product-heat loss, with the source and test untouched. -/
def heatLossPair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (u v : RatPoly) : Q' :=
  H n (polyMul u v)-kineticPair n w K ids u v

/-- Exact jump realization of twice the SAME heat loss. -/
theorem jump_heatLoss_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (u v : RatPoly) (hu : SupportedQuaternionBlocks n u)
    (hv : SupportedQuaternionBlocks n v) :
    weightedPair (n+n) (productHeat n w K ids) (jump n u) (jump n v) ≈
      2*heatLossPair n w K ids u v :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_one
      (polyMul (jump n u) (jump n v))).mul_right (productHeat n w K ids)).symm)
    (jump_mean n w K ids hnd hids hu hv)

theorem heatLossPair_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (u : RatPoly) (hu : SupportedQuaternionBlocks n u) :
    (0 : Q') ≤ heatLossPair n w K ids u u := by
  have hp := (productHeatCertificate n hw0 hw1 K hK ids hids).square_insertion_nonnegative
    (jump n u) (jump_supported hu)
  have ht := Q'.le_trans' _ _ _ hp
    (Q'.le_of_eqv (jump_heatLoss_pin n w K ids hnd hids u u hu hu))
  apply Q'.le_of_mul_le_mul_left (c := 2) _ (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv 2)) ht

/-- The upper diagonal estimate needs only positivity of the kinetic form. -/
theorem heatLossPair_le_haar (n : Nat) (w : Q') (hw0 : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (u : RatPoly) (hu : SupportedQuaternionBlocks n u) :
    heatLossPair n w K ids u u ≤ H n (polyMul u u) := by
  have hk := kineticPair_nonnegative n w hw0 K ids hids u hu
  have hn : -(kineticPair n w K ids u u) ≤ 0 :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hk) (Q'.le_of_eqv (by decide : -(0 : Q') ≈ 0))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left (H n (polyMul u u)) _ _ hn)
    (Q'.le_of_eqv (QPoly.q_add_zero_eqv _))

/-- Sharp Cauchy--Schwarz for I-P, proved on the original normalized heat. -/
theorem heatLossPair_cauchySchwarz (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (u v : RatPoly) (hu : SupportedQuaternionBlocks n u)
    (hv : SupportedQuaternionBlocks n v) :
    heatLossPair n w K ids u v*heatLossPair n w K ids u v ≤
      heatLossPair n w K ids u u*heatLossPair n w K ids v v := by
  let A := heatLossPair n w K ids u v
  let U := heatLossPair n w K ids u u
  let V := heatLossPair n w K ids v v
  have hc := weighted_cauchySchwarz (n+n) (productHeat n w K ids)
    (jump n u) (jump n v) (productHeatCertificate n hw0 hw1 K hK ids hids)
    (jump_supported hu) (jump_supported hv)
  have hA := jump_heatLoss_pin n w K ids hnd hids u v hu hv
  have hU := jump_heatLoss_pin n w K ids hnd hids u u hu hu
  have hV := jump_heatLoss_pin n w K ids hnd hids v v hv hv
  have hleft := Q'.eqv_trans _ _ _ (qmul hA hA)
    (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.const 4) (.mul (.var 0) (.var 0))) (by decide) (fun _ => A))
  have hright := Q'.eqv_trans _ _ _ (qmul hU hV)
    (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
      (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => U | _ => V))
  apply Q'.le_of_mul_le_mul_left (c := 4) _ (by decide)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv hright))

/-- Raw source-square moment, without its interacting heat factor. -/
def rawSourceMoment (n : Nat) (q p : RatPoly) : Q' :=
  H n (polyMul (polyMul q q) p)

/-- Symmetry supplies the correct sourceMoment orientation. -/
theorem rawMoment_difference_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (q p : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hp : SupportedQuaternionBlocks n p) :
    rawSourceMoment n q p-sourceMoment n w K ids q p ≈
      heatLossPair n w K ids q (polyMul q p) :=
  Q'.add_eqv_congr'
    (haar_of_coeff (RatPolyCoeffEqv.mul_assoc q q p))
    (Q'.neg_eqv_congr _ _ (kineticPair_symm n w K ids hids q (polyMul q p)
      hq (supported_polyMul hq hp)).symm)

/-- The actual moment mismatch is bounded by source heat loss, not by an
assumed replacement density or a coefficient/derivative norm. -/
theorem rawMoment_difference_square_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (q p : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (hp : SupportedQuaternionBlocks n p) :
    (rawSourceMoment n q p-sourceMoment n w K ids q p)*
        (rawSourceMoment n q p-sourceMoment n w K ids q p) ≤
      heatLossPair n w K ids q q*
        H n (polyMul (polyMul q p) (polyMul q p)) := by
  have hpin := rawMoment_difference_pin n w K ids hids q p hq hp
  have hg := supported_polyMul hq hp
  have hc := heatLossPair_cauchySchwarz n hw0 hw1 K hK ids hnd hids q (polyMul q p) hq hg
  have hu := heatLossPair_nonnegative n hw0 hw1 K hK ids hnd hids q hq
  have hv := heatLossPair_le_haar n w (Q'.le_of_lt hw0) K ids hids (polyMul q p) hg
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (qmul hpin hpin))
    (Q'.le_trans' _ _ _ hc (Q'.mul_le_mul_of_nonneg_left _ _ _ hv hu))

#print axioms jump_heatLoss_pin
#print axioms heatLossPair_nonnegative
#print axioms heatLossPair_le_haar
#print axioms heatLossPair_cauchySchwarz
#print axioms rawMoment_difference_pin
#print axioms rawMoment_difference_square_le

end YMGap.Continuum.SU2QuaternionProductHeatMomentDefect
