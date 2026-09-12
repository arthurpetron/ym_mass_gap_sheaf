/-
# Gaussian high-label suppression of the original conditional self-return

At extent one and explicitly 0 < w <= 1/2, the full boundary comparison
and balanced Casimir payment give

  P_K(s,s) <= 4096 * (M+1)^6 * w^(floor(M^2/72)),  M>=1400.

The coefficient and exponent are explicit data. No positive transition
floor, all-vector gap, geometric-time identification or continuum claim.
The degree-12 radial envelope also has a proved finite-tail bound and the
explicit tolerance threshold 1401 + epsilon.den. The actual sector shell-
count/trace comparison is separate and is not asserted here.
Exact untrusted pilot: computations/bf4_cube_gaussian_return.py.
-/

import YMGap.Continuum.BF4PhysicalCubeBoundarySumBound
import YMGap.Continuum.BF4PhysicalCubeBalancedCasimir
import YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.BF4PhysicalCubeGaussianReturn

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBalancedDescent
open YMGap.Continuum.BF4PhysicalCubeBalancedCasimir
open YMGap.Continuum.BF4PhysicalCubeBoundarySumBound
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast];
             try ac_rfl))

def dimensionProduct : List Nat → Nat
  | [] => 1
  | s :: ss => (s + 1) * dimensionProduct ss

theorem dimensionProduct_positive : ∀ ss, 0 < dimensionProduct ss
  | [] => by decide
  | s :: ss => Nat.mul_pos (Nat.zero_lt_succ s) (dimensionProduct_positive ss)

theorem dimensionProduct_le (M : Nat) : ∀ ss : List Nat,
    (∀ s, s ∈ ss → s ≤ M) → dimensionProduct ss ≤ (M + 1) ^ ss.length
  | [], _ => Nat.le_refl 1
  | s :: ss, h => by
      have hs := h s List.mem_cons_self
      have ht := dimensionProduct_le M ss (fun t ht => h t (List.mem_cons_of_mem s ht))
      simpa only [dimensionProduct, List.length_cons, Nat.pow_succ, Nat.mul_comm] using
        Nat.mul_le_mul (Nat.succ_le_succ hs) ht

def cubeDimension (state : EdgeLabelling) : Nat := dimensionProduct (cubeLabels state)

theorem cubeDimension_le (state : EdgeLabelling) : cubeDimension state ≤ (radius state + 1) ^ 6 := by
  have h := dimensionProduct_le (radius state) (cubeLabels state)
    (fun _ hs => member_le_maxLabel _ hs)
  simpa only [cubeLabels, List.length_map, centralLowerCubeFaceIds] using h

private theorem heat_filter (w : Q') (state : EdgeLabelling)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) : ∀ ids,
    eliminateLinks (fun face => coeffW w (state face)) ids ≈
      eliminateLinks (fun face => coeffW w (state face))
        (ids.filter (fun face => decide (face ∈ centralLowerCubeFaceIds)))
  | [] => Q'.eqv_refl 1
  | face :: ids => by
      by_cases hf : face ∈ centralLowerCubeFaceIds
      · simp only [eliminateLinks, List.filter_cons, hf, decide_true, ↓reduceIte]
        exact Q'.mul_eqv_congr_left _ _ _ (heat_filter w state hz ids)
      · simp only [eliminateLinks, List.filter_cons, hf, decide_false, hz face hf, coeffW_zero]
        exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (heat_filter w state hz ids)

private theorem dimension_fold : ∀ ss : List Nat,
    (ss.map (fun s => s + 1)).foldr (· * ·) 1 = dimensionProduct ss
  | [] => rfl
  | s :: ss => by simp only [List.map_cons, List.foldr_cons, dimensionProduct, dimension_fold ss]

private theorem casimir_fold : ∀ ss : List Nat,
    (ss.map c4).foldr (· + ·) 0 = casimirSum ss
  | [] => rfl
  | s :: ss => by simp only [List.map_cons, List.foldr_cons, casimirSum, casimir_fold ss]

/-- Exact six-dimensional factorization of the original 24-face half heat;
the other eighteen coefficients are exactly one by cube support. -/
theorem halfHeat_eq_dimension_casimir (w : Q') (state : EdgeLabelling)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    halfHeat w state ≈ Q'.ofNat (cubeDimension state) * qpow w (cubeCasimir state) := by
  have h := heat_filter w state hz (centralLowerFaceIds 0)
  have hids : (centralLowerFaceIds 0).filter (fun face => decide (face ∈ centralLowerCubeFaceIds)) =
      centralLowerCubeFaceIds := by decide +kernel
  rw [hids] at h
  refine Q'.eqv_trans _ _ _ h ?_
  have he := heat_product w state centralLowerCubeFaceIds
  have hd : (centralLowerCubeFaceIds.map (fun face => state face + 1)).foldr (· * ·) 1 =
      cubeDimension state := by
    simpa only [cubeDimension, cubeLabels, List.map_map, Function.comp_def] using dimension_fold (cubeLabels state)
  have hc : (centralLowerCubeFaceIds.map (fun face => c4 (state face))).foldr (· + ·) 0 =
      cubeCasimir state := by
    simpa only [cubeCasimir, cubeLabels, List.map_map, Function.comp_def] using casimir_fold (cubeLabels state)
  simpa only [hd, hc] using he

/-- Computed number of heat powers paid by the quadratic Casimir reserve. -/
def gaussianExponent (M : Nat) : Nat := M * M / 72

theorem balanced_casimir_exponent (state : EdgeLabelling) (hM : 1400 ≤ radius state) :
    gaussianExponent (radius state) + cubeCasimir (balancedState state) ≤ cubeCasimir state := by
  have h := cube_casimir_quadratic_drop state hM
  unfold gaussianExponent
  omega

/-- Six polynomial dimension factors are paid explicitly; no dimension
ratio is hidden in an opaque constant. -/
theorem balanced_heat_ratio {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (state : EdgeLabelling) (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (hM : 1400 ≤ radius state) :
    halfHeat w state ≤ (Q'.ofNat ((radius state + 1) ^ 6) * qpow w (gaussianExponent (radius state))) *
      halfHeat w (balancedState state) := by
  have hs := halfHeat_eq_dimension_casimir w state hz
  have ht := halfHeat_eq_dimension_casimir w (balancedState state) (balancedState_off state)
  have hp := qpow_antitone hw0 hw1 _ _ (balanced_casimir_exponent state hM)
  have hd := CReal.ofNat_le_ofNat (cubeDimension_le state)
  have hdim : (1 : Q') ≤ Q'.ofNat (cubeDimension (balancedState state)) :=
    CReal.ofNat_le_ofNat (dimensionProduct_positive (cubeLabels (balancedState state)))
  have hd0 : (0 : Q') ≤ Q'.ofNat ((radius state + 1) ^ 6) := zero_le_ofNat _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hs) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hd (qpow_nonneg w hw0 _)) ?_)
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp hd0) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (qpow_add w _ _))) ?_
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hdim (qpow_nonneg w hw0 (cubeCasimir (balancedState state)))
  have hsingle : qpow w (cubeCasimir (balancedState state)) ≤ halfHeat w (balancedState state) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv ht))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hsingle (Q'.mul_nonneg _ _ hd0 (qpow_nonneg w hw0 _))

def returnEnvelope (w : Q') (M : Nat) : Q' :=
  (Q'.ofNat 4096 * Q'.ofNat ((M + 1) ^ 6)) * qpow w (gaussianExponent M)

/-- Quantitative high-label self-return of the ORIGINAL normalized physical
joint kernel divided by its own marginal, at every admitting cutoff. -/
theorem cube_selfReturn_le_gaussian {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) (hM : 1400 ≤ radius state) :
    Q'.divPos (centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw0) K 0 state state)
      (centralPhysicalRowMarginal w (Q'.le_of_lt hw0) K 0 state)
      (mem_centralPositiveHalfStates_iff.mp
        (cubeSupported_mem_positiveHalfStates hw0 K (by omega) state hb hp.1)).2 ≤
      returnEnvelope w (radius state) := by
  have hh := balanced_heat_ratio (Q'.le_of_lt hw0)
    (Q'.le_trans' _ _ (1 : Q') hw (by decide)) state hp.1 hM
  have hs := cube_selfReturn_scaled_le hw0 hw K hK state hb hp
  have ht : (0 : Q') < halfHeat w (balancedState state) := by
    have he := halfHeat_eq_dimension_casimir w (balancedState state) (balancedState_off state)
    have hd : (0 : Q') < Q'.ofNat (cubeDimension (balancedState state)) :=
      Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
        (CReal.ofNat_le_ofNat (dimensionProduct_positive _))
    exact Q'.pos_of_lt_of_le (Q'.mul_pos hd
      (YMGap.Continuum.BondMovingScaledNorm.qpow_pos hw0 _)) (Q'.ge_of_eqv he)
  apply Q'.le_of_mul_le_mul_left (c := halfHeat w (balancedState state)) (hc := ht)
  refine Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hh (zero_le_ofNat 4096)) ?_)
  apply Q'.le_of_eqv
  unfold returnEnvelope
  q_ring

/-- Every high-label member of the actual canonical vacuum sector satisfies
the bound for the existing conditional kernel. Cube support and parity are
derived from sector membership, not supplied as new analytic hypotheses. -/
theorem vacuumSector_selfReturn_le_gaussian {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (K : Nat) {state : EdgeLabelling}
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw0) K 0)
    (hM : 1400 ≤ radius state) :
    centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state ≤ returnEnvelope w (radius state) := by
  have hb := vacuumSector_cubeBounded w (Q'.le_of_lt hw0) K hs
  have hp := vacuumSector_cubeSupportedCommonParity w (Q'.le_of_lt hw0) K hs
  have hK : 2 ≤ K := Nat.le_trans (by omega : 2 ≤ radius state) (radius_le state K hb)
  have hrow := (mem_centralPositiveHalfStates_iff.mp
    (cubeSupported_mem_positiveHalfStates hw0 K (by omega) state hb hp.1)).2
  rw [centralPhysicalConditionalKernel_eq_divPos hrow]
  exact cube_selfReturn_le_gaussian hw0 hw K hK state hb hp hM

/-- Degree twelve allows both six heat dimensions and a six-label counting
factor. The identification with an actual sector trace is a separate step. -/
def radialEnvelope (w : Q') (M : Nat) : Q' :=
  (Q'.ofNat 4096 * Q'.ofNat ((M + 1) ^ 12)) * qpow w (gaussianExponent M)

theorem radialEnvelope_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    (0 : Q') ≤ radialEnvelope w M :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)) (qpow_nonneg w hw _)

theorem gaussianExponent_succ_gain (M : Nat) (hM : 1400 ≤ M) :
    13 + gaussianExponent M ≤ gaussianExponent (M + 1) := by
  simp only [gaussianExponent, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

private theorem natCast_mul (a b : Nat) : Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show Int.ofNat (a * b) * (1 : Int) = (Int.ofNat a * Int.ofNat b) * (1 : Int)
  rfl

theorem radialEnvelope_succ_le_half {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ HalfPow.half) (M : Nat) (hM : 1400 ≤ M) :
    radialEnvelope w (M + 1) ≤ HalfPow.half * radialEnvelope w M := by
  have hdim : (M + 1 + 1) ^ 12 ≤ 4096 * (M + 1) ^ 12 := by
    have h := Nat.pow_le_pow_left (by omega : M + 1 + 1 ≤ 2 * (M + 1)) 12
    simpa only [Nat.mul_pow] using h
  have hd := Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hdim)
    (Q'.le_of_eqv (natCast_mul 4096 ((M + 1) ^ 12)))
  have hp := qpow_antitone hw0 (Q'.le_trans' _ _ (1 : Q') hw (by decide)) _ _ (gaussianExponent_succ_gain M hM)
  have hrate : Q'.ofNat 4096 * qpow w 13 ≤ HalfPow.half :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hw0 hw 13) (zero_le_ofNat 4096)) (by decide)
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hd (zero_le_ofNat 4096))
    (qpow_nonneg w hw0 (gaussianExponent (M + 1)))
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ _ hp
    (Q'.mul_nonneg _ _ (zero_le_ofNat 4096)
      (Q'.mul_nonneg _ _ (zero_le_ofNat 4096) (zero_le_ofNat ((M + 1) ^ 12))))
  refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 ?_)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (qpow_add w 13 _))) ?_
  refine Q'.le_trans' _ ((Q'.ofNat 4096 * qpow w 13) * radialEnvelope w M) _ ?_ ?_
  · apply Q'.le_of_eqv
    unfold radialEnvelope
    q_ring
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _ hrate (radialEnvelope_nonneg hw0 M)

private theorem twice_half (a : Q') : Q'.ofNat 2 * (HalfPow.half * a) ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a (by decide)) (Q'.one_mul_eqv a))

private theorem double_eqv (a : Q') : a + a ≈ Q'.ofNat 2 * a :=
  Q'.eqv_trans _ ((1 : Q') * a + 1 * a) _
    (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.one_mul_eqv a)) (Q'.eqv_symm (Q'.one_mul_eqv a)))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv 1 1 a))
      (Q'.mul_eqv_congr_right _ _ a (by decide)))

/-- Every finite radial tail has an explicit Gaussian bound, independent
of its outer cutoff. This does not yet identify that sum with a trace. -/
theorem radialEnvelope_tail_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ HalfPow.half)
    (N : Nat) (hN : 1400 ≤ N) (n : Nat) :
    RationalTail.finSum (fun k => radialEnvelope w (N + k)) n ≤ Q'.ofNat 2 * radialEnvelope w N := by
  apply CharacterTail.geom_series_le (fun k => radialEnvelope w (N + k))
    (radialEnvelope w N) HalfPow.half (Q'.ofNat 2 * radialEnvelope w N)
    (by decide) (Q'.mul_nonneg _ _ (zero_le_ofNat 2) (radialEnvelope_nonneg hw0 N)) (Q'.le_refl' _) ?_ ?_ n
  · intro k
    simpa only [Nat.add_assoc] using radialEnvelope_succ_le_half hw0 hw (N + k) (by omega)
  · have he : HalfPow.half * (Q'.ofNat 2 * radialEnvelope w N) ≈ radialEnvelope w N :=
      Q'.eqv_trans _ _ _ (by q_ring) (twice_half _)
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) he) (double_eqv _))

theorem radialEnvelope_seed_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ HalfPow.half) :
    radialEnvelope w 1400 ≤ (1 : Q') := by
  have hp := Q'.le_trans' _ _ _ (qpow_mono hw0 hw (gaussianExponent 1400))
    (qpow_antitone (w := HalfPow.half) (by decide) (by decide) 144 (gaussianExponent 1400) (by decide))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp
    (Q'.mul_nonneg _ _ (zero_le_ofNat 4096) (zero_le_ofNat (1401 ^ 12)))) (by decide +kernel)

theorem radialEnvelope_geometric {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ HalfPow.half)
    (k : Nat) : radialEnvelope w (1400 + k) ≤ HalfPow.half ^ k := by
  have h := CharacterTail.geom_dom (fun j => radialEnvelope w (1400 + j)) 1 HalfPow.half
    (by decide) (radialEnvelope_seed_le_one hw0 hw)
    (fun j => by simpa only [Nat.add_assoc] using radialEnvelope_succ_le_half hw0 hw (1400 + j) (by omega)) k
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- A computable tail threshold, uniform for the named coupling interval.
No modulus is hidden in propositional existence. -/
def radialTailCutoff (epsilon : Q') : Nat := 1401 + epsilon.den

theorem radialTailCutoff_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ HalfPow.half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) :
    RationalTail.finSum (fun k => radialEnvelope w (radialTailCutoff epsilon + k)) n ≤ epsilon := by
  refine Q'.le_trans' _ _ _ (radialEnvelope_tail_le hw0 hw (radialTailCutoff epsilon)
    (by unfold radialTailCutoff; omega) n) ?_
  have h := radialEnvelope_geometric hw0 hw (epsilon.den + 1)
  have hi : radialTailCutoff epsilon = 1400 + (epsilon.den + 1) := by unfold radialTailCutoff; omega
  rw [hi]
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h (zero_le_ofNat 2)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (twice_half (HalfPow.half ^ epsilon.den))) ?_
  exact HalfPow.pow_half_le epsilon he

end YMGap.Continuum.BF4PhysicalCubeGaussianReturn

#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.dimensionProduct
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.dimensionProduct_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.dimensionProduct_le
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.cubeDimension
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.cubeDimension_le
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.halfHeat_eq_dimension_casimir
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.gaussianExponent
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.balanced_casimir_exponent
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.balanced_heat_ratio
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.returnEnvelope
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.cube_selfReturn_le_gaussian
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.vacuumSector_selfReturn_le_gaussian
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialEnvelope
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialEnvelope_nonneg
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.gaussianExponent_succ_gain
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialEnvelope_succ_le_half
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialEnvelope_tail_le
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialEnvelope_seed_le_one
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialEnvelope_geometric
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialTailCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeGaussianReturn.radialTailCutoff_bound
