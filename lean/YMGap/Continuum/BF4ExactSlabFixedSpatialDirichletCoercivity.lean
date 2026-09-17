/-
# A constructed variance fraction for the SAME original temporal edge

Center at the explicitly computed V*g mean, retaining all spatial factors.
The kinetic floor bounds energy from below; the transfer cap bounds the
odd marginal's variance from above. Their composition loses ONE floor/cap
fraction, not its square. The proof is division-free until the already
constructed positive kinetic-cap reciprocal in mixFraction.

For g=T^n1 every premise is constructed. The resulting positive fraction
is independent of n and late cutoff, but depends on nome AND width. Its
known width deterioration is NOT repaired; no volume-uniform or physical
mass gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.RationalVarianceCapComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialOddLocalVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOddLocalVariance (odd_variance_floor)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] weightedMass spatialWeight baseLinks

private def centered (f : RatPoly) (M b : Q') : RatPoly :=
  polyAdd (polySmul M f) (polySmul (-b) polyOne)

private theorem support_smul {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hf s hs

private theorem centered_supported {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) (M b : Q') :
    SupportedQuaternionBlocks blocks (centered f M b) :=
  supported_add (support_smul hf M) (support_smul (supported_one blocks) (-b))

private theorem qmul {a b c d : Q'} (h : a≈b) (k : c≈d) : a*c≈b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem pair_reorder (v p f h : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul f h) (polyMul v p))
      (polyMul v (polyMul p (polyMul f h))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 2) (.var 3)) (.mul (.var 0) (.var 1)))
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
    (by decide) (fun | 0 => v | 1 => p | 2 => f | _ => h)

private theorem pair_pin (w : Q') (K width : Nat) (p f h : RatPoly) :
    weightedPair (N width) (polyMul (spatialWeight w K width) p) f h ≈
      weightedMass w K width (polyMul p (polyMul f h)) := by
  unfold weightedMass
  exact haar_of_coeff (pair_reorder (spatialWeight w K width) p f h)

private theorem scalar_expansion (M b C B Z : Q') :
    (M*(M*C) + M*((-b)*B)) + ((-b)*(M*B) + (-b)*((-b)*Z)) ≈
      M*M*C + -(2*M*b*B) + b*b*Z :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.mul (.neg (.var 1)) (.var 3))))
      (.add (.mul (.neg (.var 1)) (.mul (.var 0) (.var 3)))
        (.mul (.neg (.var 1)) (.mul (.neg (.var 1)) (.var 4)))))
    (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
      (.neg (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3))))
      (.mul (.mul (.var 1) (.var 1)) (.var 4)))
    (by decide) (fun | 0 => M | 1 => b | 2 => C | 3 => B | _ => Z)

private theorem centered_square_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p f : RatPoly}
    (P : Certificate (N width) p) (hf : SupportedQuaternionBlocks (N width) f) (M b : Q') :
    weightedMass w K width (polyMul p (polyMul (centered f M b) (centered f M b))) ≈
      M*M*weightedMass w K width (polyMul p (polyMul f f)) +
        -(2*M*b*weightedMass w K width (polyMul p f)) + b*b*weightedMass w K width p := by
  let G := weightedGNSData (N width) (polyMul (spatialWeight w K width) p)
    ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul P)
  have h := G.diag_expand M (-b) ⟨f,hf⟩ ⟨polyOne,supported_one (N width)⟩
  have hc := pair_pin w K width p f f
  have hb := Q'.eqv_trans _ _ _ (pair_pin w K width p f polyOne)
    (weightedMass_congr w K width ((RatPolyCoeffEqv.mul_one f).mul_left p))
  have hz := Q'.eqv_trans _ _ _ (pair_pin w K width p polyOne polyOne)
    (weightedMass_congr w K width
      (((RatPolyCoeffEqv.one_mul polyOne).mul_left p).trans (RatPolyCoeffEqv.mul_one p)))
  have he := Q'.eqv_trans _ _ _ h
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (qmul (Q'.eqv_refl M) (qmul (Q'.eqv_refl M) hc))
        (qmul (Q'.eqv_refl M) (qmul (Q'.eqv_refl (-b)) hb)))
      (Q'.add_eqv_congr' (qmul (Q'.eqv_refl (-b)) (qmul (Q'.eqv_refl M) hb))
        (qmul (Q'.eqv_refl (-b)) (qmul (Q'.eqv_refl (-b)) hz))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (pair_pin w K width p _ _))
    (Q'.eqv_trans _ _ _ he (scalar_expansion M b _ _ _))

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem upper_expansion (p h c : RatPoly) :
    RatPolyCoeffEqv (polyMul p (polyAdd c (polyNeg h)))
      (polyAdd (polyMul p c) (polySmul (-1) (polyMul p h))) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.var 2) (.neg (.var 1))))
    (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 0) (.var 1))))
    (by decide) (fun | 0 => p | 1 => h | _ => c)).trans
    ((RatPolyCoeffEqv.refl _).add (smul_neg _).symm)

private theorem weighted_product_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p h : RatPoly} {c : Q'}
    (P : Certificate (N width) p)
    (H : Certificate (N width) (polyAdd (cap c) (polyNeg h))) :
    weightedMass w K width (polyMul p h) ≤ c*weightedMass w K width p := by
  have hn := weightedMass_nonnegative hw0 hw1 K width hK (P.mul H)
  have hc : weightedMass w K width (polyMul p (cap c)) ≈ c*weightedMass w K width p :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width
      ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left c p)))
      (weightedMass_smul w K width c p)
  have he := Q'.eqv_trans _ _ _ (weightedMass_congr w K width (upper_expansion p h (cap c)))
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' hc
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) _)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

private theorem product_reorder (g t s : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul g t) s) (polyMul (polyMul g s) t) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => g | 1 => t | _ => s)

/-- The original marginal variance is compared at the explicit V*g mean.
No normalized-density comparison or second floor/cap loss is needed. -/
theorem marginal_variance_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g)
    (hM : (0 : Q') < weightedMass w K width g) :
    let p := polyMul g (transferStep w K width g)
    weightedMass w K width p * weightedMass w K width (polyMul p (polyMul f f)) +
        -(weightedMass w K width (polyMul p f)*weightedMass w K width (polyMul p f)) ≤
      kineticCap w width * weightedMass w K width p *
        (weightedMass w K width g * weightedMass w K width (polyMul g (polyMul f f)) +
          -(weightedMass w K width (polyMul g f)*weightedMass w K width (polyMul g f))) := by
  let M := weightedMass w K width g
  let b := weightedMass w K width (polyMul g f)
  let F := centered f M b
  let p := polyMul g (transferStep w K width g)
  let P : Certificate (N width) p := G.mul (transferStep_certificate hw0 hw1 K width hK hg G)
  have hZ := weightedMass_nonnegative hw0 hw1 K width hK P
  have hs := centered_supported hf M b
  have hcap := weighted_product_cap hw0 hw1 K width hK (G.mul (Certificate.square F hs))
    (transferStepUpperCertificate hw0 hw1 K width hK hg G)
  have ht : weightedMass w K width (polyMul p (polyMul F F)) ≤
      kineticCap w width*M*weightedMass w K width (polyMul g (polyMul F F)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (weightedMass_congr w K width
      (product_reorder g (transferStep w K width g) (polyMul F F)))) hcap
  have he := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (centered_square_pin hw0 hw1 K width hK P hf M b))
    (Q'.le_trans' _ _ _ ht
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (centered_square_pin hw0 hw1 K width hK G hf M b))))
  exact RationalVarianceCapComparison.variance_cap_of_centered_test M _ _ _ b _
    (kineticCap w width) hM hZ he

private theorem fraction_compose (r L U Z D E V : Q')
    (hr : (0 : Q') ≤ r) (hZ : (0 : Q') ≤ Z) (hru : r*U≈L)
    (hV : V ≤ U*Z*D) (hE : L*D ≤ E) : r*V ≤ Z*E := by
  have he : r*(U*Z*D) ≈ Z*(L*D) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
      (by decide) (fun | 0 => r | 1 => U | 2 => Z | _ => D))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ hru))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ r hV hr)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_left _ _ Z hE hZ))

/-- A positive fraction of the SAME marginal variance, in cleared form.
The fraction is explicitly width-dependent; all spatial factors survive. -/
theorem energy_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g)
    (hM : (0 : Q') < weightedMass w K width g) :
    let p := polyMul g (transferStep w K width g)
    mixFraction hw0 hw1 width *
        (weightedMass w K width p * weightedMass w K width (polyMul p (polyMul f f)) +
          -(weightedMass w K width (polyMul p f)*weightedMass w K width (polyMul p f))) ≤
      weightedMass w K width p * energy w K width g f :=
  fraction_compose _ _ _ _ _ _ _ (Q'.le_of_lt (mixFraction_positive hw0 hw1 width))
    (weightedMass_nonnegative hw0 hw1 K width hK
      (G.mul (transferStep_certificate hw0 hw1 K width hK hg G)))
    (mixFraction_mul_cap hw0 hw1 width)
    (marginal_variance_cap hw0 hw1 K width hK hg hf G hM)
    (energy_floor hw0 hw1 K width hK hg hf G)

/-- Every positive-mass premise is supplied by the actual finite boundary
message. The same fraction works for every n and every late cutoff. -/
theorem terminal_energy_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let g := terminalMessage w K width n
    let p := polyMul g (transferStep w K width g)
    mixFraction hw0 hw1 width *
        (weightedMass w K width p * weightedMass w K width (polyMul p (polyMul f f)) +
          -(weightedMass w K width (polyMul p f)*weightedMass w K width (polyMul p f))) ≤
      weightedMass w K width p * energy w K width g f :=
  energy_variance_floor hw0 hw1 K width hK
    (terminalMessage_supported w K width n) hf
    (terminalMessage_certificate hw0 hw1 K width hK n)
    (terminalMessage_mass_positive hw0 hw1 K width hK n)

private theorem normalize_floor (q Z A B E r : Q')
    (hr : (0 : Q') ≤ r) (hZr : Z*r≈1)
    (h : q*(Z*A + -(B*B)) ≤ Z*E) :
    q*(A*r + -((B*r)*(B*r))) ≤ E*r := by
  have hl : (q*(Z*A + -(B*B)))*(r*r) ≈ q*(A*r + -((B*r)*(B*r))) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 3)))))
        (.mul (.var 4) (.var 4)))
      (.mul (.var 0) (.add (.mul (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 4)))
        (.neg (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))))
      (by decide) (fun | 0 => q | 1 => Z | 2 => A | 3 => B | _ => r))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hZr) (Q'.one_mul_eqv _))
        (Q'.eqv_refl _)))
  have he : (Z*E)*(r*r) ≈ E*r :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => Z | 1 => E | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hZr) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.mul_nonneg _ _ hr hr))
      (Q'.le_of_eqv he))

/-- The SAME existing normalized odd-chain variance and normalized temporal
energy, with the constructed positive fraction and no extra analytic input. -/
theorem terminal_normalized_energy_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    mixFraction hw0 hw1 width *
        (middleRatio hw0 hw1 K width hK (n+1) n (polyMul f f) +
          -(middleRatio hw0 hw1 K width hK (n+1) n f *
            middleRatio hw0 hw1 K width hK (n+1) n f)) ≤
      normalizedEnergy hw0 hw1 K width hK n f := by
  let g := terminalMessage w K width n
  let p := polyMul g (transferStep w K width g)
  let r := Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)
  have hmass : weightedMass w K width p ≈ oddMass w K width n := by
    dsimp [p, g]
    rw [terminalMessage_next]
    exact weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)
  have hZr : weightedMass w K width p*r≈1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r hmass)
      (Q'.mul_recipPos_eqv _ (oddMass_positive hw0 hw1 K width hK n))
  have h := normalize_floor (mixFraction hw0 hw1 width) _ _ _ _ r
    (Q'.le_of_lt (Q'.recipPos_pos _ (oddMass_positive hw0 hw1 K width hK n))) hZr
    (terminal_energy_variance_floor hw0 hw1 K width hK n hf)
  have hm := marginal_middleRatio hw0 hw1 K width hK n f
  have hs := marginal_middleRatio hw0 hw1 K width hK n (polyMul f f)
  have he := Q'.mul_eqv_congr_left (mixFraction hw0 hw1 width) _ _
    (Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h

/-- An actual plaquette has a quantitative positive original-window energy.
The local variance floor is width-independent; the mixing fraction is NOT. -/
theorem plaquette_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    mixFraction hw0 hw1 width * starRatio w ≤
      normalizedEnergy hw0 hw1 K width hK n
        (characterPolynomial (plaquette width p).scalar 1) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (mixFraction hw0 hw1 width)
      (odd_variance_floor hw0 hw1 K width hK n p hp)
      (Q'.le_of_lt (mixFraction_positive hw0 hw1 width)))
    (terminal_normalized_energy_variance_floor hw0 hw1 K width hK n
      (SU2QuaternionRelativeHeatPairGeometry.character_supported
        (plaquette_supported width (N width) (Nat.le_refl _) p).scalar 1))

theorem plaquette_energy_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    (0 : Q') < normalizedEnergy hw0 hw1 K width hK n
      (characterPolynomial (plaquette width p).scalar 1) :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (mixFraction_positive hw0 hw1 width) (starRatio_positive hw0 hw1))
    (plaquette_energy_floor hw0 hw1 K width hK n p hp)

end YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity.marginal_variance_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity.energy_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity.terminal_energy_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity.terminal_normalized_energy_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity.plaquette_energy_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletCoercivity.plaquette_energy_positive
