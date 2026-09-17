/-
# One vertex-odd sector of the ORIGINAL weighted transfer

Use the full spatial vertex star, including fringe links. Erase only its
active kinetic factors. The erased mixed integral vanishes by the actual
lower-end center sign: the full endpoint V*g_n is invariant, whereas the
observable is odd. All other kinetic factors and both original terminal
messages are retained. The selected-factor comparison then rejoins the
ORIGINAL energy and marginal, with no heat-bath operator substitution.

This is a charged-sector estimate. Closed plaquette observables are even;
their spatially uniform coercivity and the physical continuum gap remain
open. No arbitrary weighted-mean-zero observable is asserted to be odd.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer
import YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabStarRateObstruction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar
open YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabStarRateObstruction (prefixCap_ge_one)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionProductHeatCenterSign
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight activeBlocks

/-- All original active kinetic factors NOT incident to the selected vertex. -/
def starRest (width : Nat) (v : Z4Vertex) : List Nat :=
  (activeBlocks width).filter (fun i => !(blockSelector width v i))

theorem star_partition (width : Nat) (v : Z4Vertex) :
    (activeStar width v ++ starRest width v).Perm (activeBlocks width) :=
  List.filter_append_perm (blockSelector width v) (activeBlocks width)

theorem starRest_lt (width : Nat) (v : Z4Vertex) (i : Nat)
    (hi : i ∈ starRest width v) : i < N width :=
  activeBlocks_lt width i (List.mem_filter.mp hi).1

theorem starRest_unselected (width : Nat) (v : Z4Vertex) (i : Nat)
    (hi : i ∈ starRest width v) : blockSelector width v i = false := by
  have h := (List.mem_filter.mp hi).2
  cases he : blockSelector width v i <;> simp_all

private theorem lower_mul (n : Nat) (s : Nat → Bool) (p q : RatPoly) :
    RatPolyCoeffEqv (lowerSign n s (polyMul p q))
      (polyMul (lowerSign n s p) (lowerSign n s q)) :=
  signSelectedPolynomial_mul_coeffEqv _ _ p q

/-- Erasing precisely the active star leaves the full weighted background
invariant under the lower-only star sign. -/
theorem erased_background_invariant (w : Q') (K width : Nat) (v : Z4Vertex)
    {a : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (he : RatPolyCoeffEqv (starSign width v a) a) :
    RatPolyCoeffEqv
      (lowerSign (N width) (blockSelector width v)
        (edgeWeight (N width) w K (starRest width v) a))
      (edgeWeight (N width) w K (starRest width v) a) := by
  have ha' : RatPolyCoeffEqv (lowerSign (N width) (blockSelector width v) a) a := by
    rw [lowerSign_lower _ _ ha]
    exact he
  have hl : RatPolyCoeffEqv
      (lowerSign (N width) (blockSelector width v) (liftBoundary (N width) a))
      (liftBoundary (N width) a) := by
    rw [lowerSign_lift]
    exact .refl _
  exact (lower_mul _ _ _ _).trans
    (((lower_mul _ _ _ _).trans
      ((productHeat_lowerSign (N width) (blockSelector width v) w K (starRest width v)
        (starRest_lt width v) (starRest_unselected width v)).mul ha')).mul hl)

/-- Actual finite erased mixed integral: no conditional-mean hypothesis,
no deleted spatial factor, and no replacement of the terminal message. -/
theorem erased_cross_zero (w : Q') (K width : Nat) (v : Z4Vertex) (depth : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (ho : RatPolyCoeffEqv (starSign width v f) (polyNeg f)) :
    quaternionHaar (N width+N width)
      (polyMul (edgeWeight (N width) w K (starRest width v)
        (polyMul (spatialWeight w K width) (terminalMessage w K width depth)))
        (polyMul f (liftBoundary (N width) f))) ≈ 0 := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width depth)
  let e := edgeWeight (N width) w K (starRest width v) a
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width depth)
  have he : RatPolyCoeffEqv (starSign width v a) a :=
    (starSign_mul width v _ _).trans
      ((spatialWeight_starSign w K width v).mul (terminalMessage_starSign w K width v depth))
  have hf' : RatPolyCoeffEqv (lowerSign (N width) (blockSelector width v) f) (polyNeg f) := by
    rw [lowerSign_lower _ _ hf]
    exact ho
  have hb : RatPolyCoeffEqv
      (lowerSign (N width) (blockSelector width v) (polyMul e (liftBoundary (N width) f)))
      (polyMul e (liftBoundary (N width) f)) := by
    have h := lower_mul (N width) (blockSelector width v) e (liftBoundary (N width) f)
    rw [lowerSign_lift] at h
    exact h.trans ((erased_background_invariant w K width v ha he).mul (.refl _))
  have hz := haar_product_zero_of_sign (N width+N width)
    (fun k => if k/4<N width then blockSelector width v (k/4) else false)
    f (polyMul e (liftBoundary (N width) f)) hf' hb
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => e | 1 => f | _ => liftBoundary (N width) f))) hz

private theorem edge_pin (w : Q') (K width : Nat) (v : Z4Vertex) (g : RatPoly) :
    RatPolyCoeffEqv
      (edgeWeight (N width) w K (activeStar width v ++ starRest width v)
        (polyMul (spatialWeight w K width) g))
      (edgeDensity w K width g) := by
  have hp : RatPolyCoeffEqv
      (productHeat (N width) w K (activeStar width v ++ starRest width v))
      (kineticWeight w K width) := by
    rw [kineticWeight_eq_indexedProduct]
    exact polynomialProduct_perm _ (star_partition width v)
  exact (hp.mul_right _).mul_right _

/-- A vertex-odd observable is centered in the ACTUAL original terminal
marginal; ordinary Haar centering is not substituted for this identity. -/
theorem terminal_starOdd_mean_zero (w : Q') (K width : Nat) (v : Z4Vertex) (depth : Nat)
    {f : RatPoly} (ho : RatPolyCoeffEqv (starSign width v f) (polyNeg f)) :
    weightedMass w K width (polyMul
      (polyMul (terminalMessage w K width depth) (terminalMessage w K width (depth+1))) f) ≈ 0 := by
  let p := polyMul (terminalMessage w K width depth) (terminalMessage w K width (depth+1))
  have hp : RatPolyCoeffEqv (starSign width v p) p :=
    (starSign_mul width v _ _).trans
      ((terminalMessage_starSign w K width v depth).mul
        (terminalMessage_starSign w K width v (depth+1)))
  have hn : RatPolyCoeffEqv (starSign width v (polyMul (spatialWeight w K width) p))
      (polyMul (spatialWeight w K width) p) :=
    (starSign_mul width v _ _).trans ((spatialWeight_starSign w K width v).mul hp)
  have hz := haar_product_zero_of_sign (N width) (coordinateSelector width v)
    f (polyMul (spatialWeight w K width) p) ho hn
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => spatialWeight w K width | 1 => p | _ => f))) hz

/-- The original marginal, without partition division, is controlled by the
original temporal energy for every vertex-odd supported polynomial. There
are at most six selected factors (`activeStar_length_le_six`). -/
theorem terminal_starOdd_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (v : Z4Vertex) (depth : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (ho : RatPolyCoeffEqv (starSign width v f) (polyNeg f)) :
    (headFloor w)^(activeStar width v).length *
        weightedMass w K width (polyMul
          (polyMul (terminalMessage w K width depth) (terminalMessage w K width (depth+1)))
          (polyMul f f)) ≤
      (prefixCap w)^(activeStar width v).length *
        energy w K width (terminalMessage w K width depth) f := by
  let g := terminalMessage w K width depth
  let a := polyMul (spatialWeight w K width) g
  have hg := terminalMessage_supported w K width depth
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width) hg
  let A : Certificate (N width) a :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK depth)
  have h := block_energy_floor (N width) hw0 hw1 K hK
    (activeStar width v) (starRest width v) (activeStar_lt width v) (starRest_lt width v)
    ha hf A (erased_cross_zero w K width v depth hf ho)
  have hd := edge_diagonal_identity w K width hg hf
  rw [terminalMessage_next] at hd
  have he := energy_identity w K width hg hf
  have hp := edge_pin w K width v g
  have hd' := Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_right _)) hd
  have he' := Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_right _)) (Q'.eqv_symm he)
  have hh := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hd')))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he')))
  apply Q'.le_of_mul_le_mul_left (c := (2 : Q')) ?_ (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.mul_assoc_eqv _ _ _))))
    (Q'.le_trans' _ _ _ hh
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
          (Q'.mul_assoc_eqv _ _ _)))))

private theorem pow_exponent_mono {x : Q'} (hx : (1 : Q') ≤ x) {m n : Nat}
    (hmn : m ≤ n) : x^m ≤ x^n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
    exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hx
        (Q'.pow_nonneg x (Q'.le_trans' _ _ _ Q'.zero_le_one hx) (m+d))))

/-- A common six-factor bound: its constants depend on nome w, but NOT on
width, vertex, terminal depth, or any cutoff K beyond headCutoff(w).
This remains restricted to the indicated vertex-odd sector. -/
theorem terminal_starOdd_six_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (v : Z4Vertex) (depth : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (ho : RatPolyCoeffEqv (starSign width v f) (polyNeg f)) :
    (headFloor w)^6 *
        weightedMass w K width (polyMul
          (polyMul (terminalMessage w K width depth) (terminalMessage w K width (depth+1)))
          (polyMul f f)) ≤
      (prefixCap w)^6 * energy w K width (terminalMessage w K width depth) f := by
  have hn := ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (((terminalMessage_certificate hw0 hw1 K width hK depth).mul
      (terminalMessage_certificate hw0 hw1 K width hK (depth+1))).mul
        (Certificate.square f hf))).haar_nonnegative
  have he := energy_nonnegative hw0 hw1 K width hK
    (terminalMessage_supported w K width depth) hf
    (terminalMessage_certificate hw0 hw1 K width hK depth)
  have hlen := activeStar_length_le_six width v
  have hh := HKConvGen.pow_base_antitone (Q'.le_of_lt (headFloor_positive hw0 hw1))
    (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide :
      Q'.mkPos 1 32 (by decide) ≤ (1 : Q'))) hlen
  have hu := pow_exponent_mono (prefixCap_ge_one hw0 hw1) hlen
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hh hn)
    (Q'.le_trans' _ _ _ (terminal_starOdd_energy_floor hw0 hw1 K width hK v depth hf ho)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hu he))

end YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.starRest
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.star_partition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.starRest_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.starRest_unselected
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.erased_background_invariant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.erased_cross_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.terminal_starOdd_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.terminal_starOdd_energy_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy.terminal_starOdd_six_energy_floor
