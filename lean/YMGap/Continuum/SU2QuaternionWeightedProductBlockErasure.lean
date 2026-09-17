/-
# Local-block comparison retaining the original weighted edge

Erase a specified finite list of kinetic factors, retaining every other
factor and the entire endpoint weight on BOTH slices. Constructed heat
floor/cap certificates compare any certified nonnegative insertion before
and after erasure. Only the number of erased factors enters the constants.

If the erased mixed integral vanishes, these comparisons give a coercive
bound for the original jump square. The vanishing is an explicit finite
identity, not a claimed consequence of global weighted centering. A vertex
center-sign argument can supply that identity for a charged sector; this
module does not assert it for gauge-invariant observables.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local infix:50 " ≈ " => Q'.eqv

private theorem scalar_assoc (a b c : Q') : (a*b)*c ≈ a*(b*c) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => c)

private theorem scalar_commute (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => c)

/-- Positivity retains every selected original kinetic factor and both
endpoint weights; no density comparison is used. -/
def edgeCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {a : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (A : Certificate n a) :
    Certificate (n+n) (edgeWeight n w K ids a) :=
  ((productHeatCertificate n hw0 hw1 K hK ids hids).mul
    (certificate_extend n ha A)).mul (lift_certificate n A)

/-- A product of floors only over the ERASED list. The retained list,
including its length, remains inside the same weighted integral. -/
theorem selected_floor (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (retained : List Nat)
    (hr : ∀ i, i ∈ retained → i < n) {a s : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (A : Certificate n a)
    (S : Certificate (n+n) s) :
    ∀ selected : List Nat, (∀ i, i ∈ selected → i < n) →
    (headFloor w)^selected.length *
        quaternionHaar (n+n) (polyMul (edgeWeight n w K retained a) s) ≤
      quaternionHaar (n+n) (polyMul (edgeWeight n w K (selected++retained) a) s)
  | [], _ => Q'.le_of_eqv (Q'.one_mul_eqv _)
  | i::selected, hs => by
      have hi := hs i List.mem_cons_self
      have ht : ∀ j, j ∈ selected → j < n :=
        fun j hj => hs j (List.mem_cons_of_mem i hj)
      have hall : ∀ j, j ∈ selected++retained → j < n :=
        fun j hj => (List.mem_append.mp hj).elim (ht j) (hr j)
      have hone := certified_floor
        (heatAt_floorCertificate (show i < n+n by omega) (show n+i < n+n by omega)
          hw0 hw1 K hK)
        ((edgeCertificate n hw0 hw1 K hK (selected++retained) hall ha A).mul S)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (scalar_assoc _ _ _))
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ (headFloor w)
            (selected_floor n hw0 hw1 K hK retained hr ha A S selected ht)
            (Q'.le_of_lt (headFloor_positive hw0 hw1)))
          (Q'.le_trans' _ _ _ hone
            (Q'.le_of_eqv (Q'.eqv_symm
              (factor_pairing n w K i (selected++retained) a s)))))

/-- The corresponding upper comparison; again only erased factors pay a cap. -/
theorem selected_cap (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (retained : List Nat)
    (hr : ∀ i, i ∈ retained → i < n) {a s : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (A : Certificate n a)
    (S : Certificate (n+n) s) :
    ∀ selected : List Nat, (∀ i, i ∈ selected → i < n) →
    quaternionHaar (n+n) (polyMul (edgeWeight n w K (selected++retained) a) s) ≤
      (prefixCap w)^selected.length *
        quaternionHaar (n+n) (polyMul (edgeWeight n w K retained a) s)
  | [], _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  | i::selected, hs => by
      have hi := hs i List.mem_cons_self
      have ht : ∀ j, j ∈ selected → j < n :=
        fun j hj => hs j (List.mem_cons_of_mem i hj)
      have hall : ∀ j, j ∈ selected++retained → j < n :=
        fun j hj => (List.mem_append.mp hj).elim (ht j) (hr j)
      let e := edgeWeight n w K (selected++retained) a
      let k := heatAt i (n+i) w K
      have hone := (heatInterval (show i < n+n by omega) (show n+i < n+n by omega)
        hw0 hw1 K).weighted_haar_bound
          ((edgeCertificate n hw0 hw1 K hK (selected++retained) hall ha A).mul S)
      have he : quaternionHaar (n+n)
          (polyMul (edgeWeight n w K ((i::selected)++retained) a) s) ≈
          quaternionHaar (n+n) (polyMul (polyMul e s) k) :=
        Q'.eqv_trans _ _ _ (factor_pairing n w K i (selected++retained) a s)
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm k (polyMul e s)))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
          (Q'.le_trans' _ _ _ hone
            (Q'.le_trans' _ _ _
              (Q'.mul_le_mul_of_nonneg_left _ _ (prefixCap w)
                (selected_cap n hw0 hw1 K hK retained hr ha A S selected ht)
                (prefixCap_nonnegative hw0))
              (Q'.le_of_eqv (Q'.eqv_symm (scalar_assoc _ _ _))))))

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Coefficient-level oddness under an actual Haar-preserving sign change
forces a zero integral. This remains valid for signed or zero coefficients;
no syntactic monomial-charge assertion is required. -/
theorem haar_zero_of_sign_odd (n : Nat) (selected : Nat → Bool) (p : RatPoly)
    (hp : RatPolyCoeffEqv (signSelectedPolynomial (4*n) selected p) (polyNeg p)) :
    quaternionHaar n p ≈ 0 := by
  let x := quaternionHaar n p
  have he : x ≈ -x := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_signSelected n selected p))
    (Q'.eqv_trans _ _ _ (haar_of_coeff hp) (haar_neg n p))
  have hz : x+x ≈ 0 := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl x) he)
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => x))
  have ht : (2 : Q')*x ≈ 0 := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.const 2) (.var 0))
      (.add (.var 0) (.var 0)) (by decide) (fun _ => x)) hz
  have hi : x ≈ HalfPow.half*((2 : Q')*x) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv x))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x (by decide : (1 : Q') ≈ HalfPow.half*2))
        (scalar_assoc _ _ _))
  exact Q'.eqv_trans _ _ _ hi
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ht) (Q'.mul_zero_eqv _))

/-- An odd insertion against an invariant retained background has zero
mixed integral on the same Haar carrier. -/
theorem haar_product_zero_of_sign (n : Nat) (selected : Nat → Bool) (p q : RatPoly)
    (hp : RatPolyCoeffEqv (signSelectedPolynomial (4*n) selected p) (polyNeg p))
    (hq : RatPolyCoeffEqv (signSelectedPolynomial (4*n) selected q) q) :
    quaternionHaar n (polyMul p q) ≈ 0 :=
  haar_zero_of_sign_odd n selected (polyMul p q)
    ((signSelectedPolynomial_mul_coeffEqv (4*n) selected p q).trans
      ((hp.mul hq).trans (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => p | _ => q))))

/-- A finite vanishing mixed integral identifies the erased jump and diagonal
integrals. Neither endpoint symmetry nor normalization is presumed. -/
theorem jump_eq_diagonal {n : Nat} (e f g : RatPoly)
    (hz : quaternionHaar n (polyMul e (polyMul f g)) ≈ 0) :
    quaternionHaar n (polyMul e
      (polyMul (polyAdd f (polyNeg g)) (polyAdd f (polyNeg g)))) ≈
      quaternionHaar n (polyMul e (polyAdd (polyMul f f) (polyMul g g))) := by
  have he : RatPolyCoeffEqv
      (polyMul e (polyMul (polyAdd f (polyNeg g)) (polyAdd f (polyNeg g))))
      (polyAdd (polyMul e (polyAdd (polyMul f f) (polyMul g g)))
        (polyAdd (polyNeg (polyMul e (polyMul f g))) (polyNeg (polyMul e (polyMul f g))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))
      (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))))
        (.add (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
          (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))))
      (by decide) (fun | 0 => e | 1 => f | _ => g)
  have hn := Q'.eqv_trans _ _ _ (haar_neg n _) (Q'.neg_eqv_congr _ _ hz)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr' hn hn)))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.add (.neg (.const 0)) (.neg (.const 0)))) (.var 0)
          (by decide) (fun _ => _))))

private theorem support_pair {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks (n+n) f :=
  fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {n : Nat} {f : RatPoly} (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (polyNeg f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hf s hs

/-- Original full-edge coercivity from finite block erasure. The rate is
explicitly nome-dependent and depends on selected.length, not retained.length.
No vanishing premise is supplied for the physical center-even sector here. -/
theorem block_energy_floor (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (selected retained : List Nat)
    (hs : ∀ i, i ∈ selected → i < n) (hr : ∀ i, i ∈ retained → i < n)
    {a f : RatPoly} (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f) (A : Certificate n a)
    (hz : quaternionHaar (n+n) (polyMul (edgeWeight n w K retained a)
      (polyMul f (liftBoundary n f))) ≈ 0) :
    (headFloor w)^selected.length * quaternionHaar (n+n)
        (polyMul (edgeWeight n w K (selected++retained) a)
          (polyAdd (polyMul f f) (polyMul (liftBoundary n f) (liftBoundary n f)))) ≤
      (prefixCap w)^selected.length * quaternionHaar (n+n)
        (polyMul (edgeWeight n w K (selected++retained) a)
          (polyMul (polyAdd f (polyNeg (liftBoundary n f)))
            (polyAdd f (polyNeg (liftBoundary n f))))) := by
  let d := polyAdd (polyMul f f) (polyMul (liftBoundary n f) (liftBoundary n f))
  let j := polyAdd f (polyNeg (liftBoundary n f))
  let D : Certificate (n+n) d := (Certificate.square f (support_pair hf)).add
    (Certificate.square (liftBoundary n f) (lift_supported hf n))
  let J : Certificate (n+n) (polyMul j j) :=
    Certificate.square j (supported_add (support_pair hf) (support_neg (lift_supported hf n)))
  have hd := selected_cap n hw0 hw1 K hK retained hr ha A D selected hs
  have hj := selected_floor n hw0 hw1 K hK retained hr ha A J selected hs
  have he := jump_eq_diagonal (edgeWeight n w K retained a) f (liftBoundary n f) hz
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ ((headFloor w)^selected.length) hd
      (Q'.pow_nonneg _ (Q'.le_of_lt (headFloor_positive hw0 hw1)) _))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (scalar_commute _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ ((prefixCap w)^selected.length)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm he))) hj)
        (Q'.pow_nonneg _ (prefixCap_nonnegative hw0) _)))

end YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure

#print axioms YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure.edgeCertificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure.selected_floor
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure.selected_cap
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure.haar_zero_of_sign_odd
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure.haar_product_zero_of_sign
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure.jump_eq_diagonal
#print axioms YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure.block_energy_floor
