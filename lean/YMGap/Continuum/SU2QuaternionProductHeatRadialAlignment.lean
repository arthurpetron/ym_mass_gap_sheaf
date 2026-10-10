/-
# Radial alignment under the complete original product heat weight

Signed coordinate sources are inserted into the error-free heat displacement
bound. Slice symmetry and supported squares convert the resulting cross
moments into radial moments. Reweighted quaternion-vector Cauchy supplies
the sharp fourth power of the literal ordered word length, including zero.
This is finite polynomial Haar algebra, not a variance or scaling theorem.
-/

import YMGap.Continuum.SU2QuaternionProductHeatExactAlignment
import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.QuaternionHaarWordQuadratic

namespace YMGap.Continuum.SU2QuaternionProductHeatRadialAlignment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord (reindexPolyQuaternion)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (productHeat_swap)
open YMGap.Continuum.SU2QuaternionProductHeatExactAlignment
open YMGap.Continuum.SU2QuaternionTwoSliceSwap
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (kernel_pairing_swap)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarWordQuadratic
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarWordComponents (component)

local infix:50 " ≈ " => Q'.eqv

def moment (n : Nat) (W p : RatPoly) : Q' := quaternionHaar n (polyMul W p)
def square (p : RatPoly) : RatPoly := polyMul p p

theorem support_lower {n : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

theorem support_neg {n : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem support_norm {n : Nat} {p : PolyQuaternion} (hp : Supported n p) :
    SupportedQuaternionBlocks n (polyQuaternionNorm p) :=
  supported_add (supported_polyMul hp.scalar hp.scalar)
    (supported_add (supported_polyMul hp.iPart hp.iPart)
      (supported_add (supported_polyMul hp.jPart hp.jPart) (supported_polyMul hp.kPart hp.kPart)))

def normCertificate {n : Nat} {p : PolyQuaternion} (hp : Supported n p) :
    Certificate n (polyQuaternionNorm p) :=
  (Certificate.square p.scalar hp.scalar).add
    ((Certificate.square p.iPart hp.iPart).add
      ((Certificate.square p.jPart hp.jPart).add (Certificate.square p.kPart hp.kPart)))

theorem padded_neg {n : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv n p q) :
    PaddedPolynomialCoeffEqv n (polyNeg p) (polyNeg q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

theorem padded_norm {n : Nat} {p q : PolyQuaternion} (h : PaddedQuaternionCoeffEqv n p q) :
    PaddedPolynomialCoeffEqv n (polyQuaternionNorm p) (polyQuaternionNorm q) := by
  unfold PaddedPolynomialCoeffEqv
  simp only [polyQuaternionNorm, reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul]
  exact (h.scalar.mul h.scalar).add ((h.iPart.mul h.iPart).add
    ((h.jPart.mul h.jPart).add (h.kPart.mul h.kPart)))

def chordal (n i : Nat) : RatPoly :=
  polyQuaternionNorm (difference (PolyQuaternion.coordinateVariable i)
    (PolyQuaternion.coordinateVariable (n+i)))

private theorem chordal_swap (n i : Nat) (hi : i < n) :
    PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial (swap n) (chordal n i)) (chordal n i) := by
  let p := PolyQuaternion.coordinateVariable i
  let q := PolyQuaternion.coordinateVariable (n+i)
  have hl := PaddedQuaternionCoeffEqv.of_prefix
    (reindex_coordinateVariable_prefix (swap n) (by omega : n+i < n+n) (swap_upper n i hi))
  have hu := PaddedQuaternionCoeffEqv.of_prefix
    (reindex_coordinateVariable_prefix (swap n) (by omega : i < n+n) (swap_lower n i hi))
  have hd : PaddedQuaternionCoeffEqv (n+n)
      (reindexPolyQuaternion (swap n) (difference p q)) (difference q p) := by
    exact ⟨by simpa only [reindexPolyQuaternion, difference,
        reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg] using hl.scalar.add (padded_neg hu.scalar),
      by simpa only [reindexPolyQuaternion, difference,
        reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg] using hl.iPart.add (padded_neg hu.iPart),
      by simpa only [reindexPolyQuaternion, difference,
        reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg] using hl.jPart.add (padded_neg hu.jPart),
      by simpa only [reindexPolyQuaternion, difference,
        reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg] using hl.kPart.add (padded_neg hu.kPart)⟩
  have hn := padded_norm hd
  have he : RatPolyCoeffEqv (polyQuaternionNorm (difference q p)) (polyQuaternionNorm (difference p q)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 4) (.neg (.var 0))) (.add (.var 4) (.neg (.var 0))))
        (.add (.mul (.add (.var 5) (.neg (.var 1))) (.add (.var 5) (.neg (.var 1))))
          (.add (.mul (.add (.var 6) (.neg (.var 2))) (.add (.var 6) (.neg (.var 2))))
            (.mul (.add (.var 7) (.neg (.var 3))) (.add (.var 7) (.neg (.var 3)))))))
      (.add (.mul (.add (.var 0) (.neg (.var 4))) (.add (.var 0) (.neg (.var 4))))
        (.add (.mul (.add (.var 1) (.neg (.var 5))) (.add (.var 1) (.neg (.var 5))))
          (.add (.mul (.add (.var 2) (.neg (.var 6))) (.add (.var 2) (.neg (.var 6))))
            (.mul (.add (.var 3) (.neg (.var 7))) (.add (.var 3) (.neg (.var 7)))))))
      (by decide) (fun
        | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
        | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart)
  have hn' : PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial (swap n) (chordal n i))
      (polyQuaternionNorm (difference q p)) := by
    simpa only [chordal, p, q, polyQuaternionNorm, reindexPolyQuaternion,
      reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul] using hn
  exact hn'.trans (.of_coeff he)

private theorem endpoint_square_swap (n : Nat) (kernel q u : RatPoly)
    (hk : SupportedQuaternionBlocks (n+n) kernel)
    (hq : SupportedQuaternionBlocks n q) (hu : SupportedQuaternionBlocks n u)
    (hs : PaddedPolynomialCoeffEqv (n+n) (reindexQuaternionPolynomial (swap n) kernel) kernel) :
    moment (n+n) (polyMul (polyMul kernel q) (liftBoundary n q)) (square u) ≈
      moment (n+n) (polyMul (polyMul kernel q) (liftBoundary n q)) (square (liftBoundary n u)) := by
  have h := kernel_pairing_swap hk (supported_polyMul hq (supported_polyMul hu hu)) hq hs
  rw [lift_product, lift_product] at h
  let Q := liftBoundary n q
  let U := liftBoundary n u
  have hl : RatPolyCoeffEqv (polyMul (polyMul kernel (polyMul q (square u))) Q)
      (polyMul (polyMul (polyMul kernel q) Q) (square u)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2)))) (.var 3))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => kernel | 1 => q | 2 => u | _ => Q)
  have hr : RatPolyCoeffEqv (polyMul (polyMul kernel q) (polyMul Q (square U)))
      (polyMul (polyMul (polyMul kernel q) Q) (square U)) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff hl))
    (Q'.eqv_trans _ _ _ h (haar_of_coeff hr))

/-- Supported square positivity pays a mixed product without a sign premise. -/
theorem square_young {n : Nat} {W a b : RatPoly} (R : Certificate n W)
    (ha : SupportedQuaternionBlocks n a) (hb : SupportedQuaternionBlocks n b) :
    2*moment n W (polyMul a b) ≤ moment n W (square a)+moment n W (square b) := by
  let d := polyAdd a (polyNeg b)
  have C : Certificate n
      (polyAdd (polyAdd (square a) (square b)) (polyNeg (polySmul 2 (polyMul a b)))) :=
    Certificate.ofCoeff
      ((((RatPolyCoeffEqv.refl (polyAdd (square a) (square b))).add
        (RatPolyCoeffEqv.neg (cap_mul_left 2 (polyMul a b)).symm)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
          (.neg (.mul (.const 2) (.mul (.var 0) (.var 1)))))
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
        (by decide) (fun | 0 => a | _ => b))).trans
        (RatPolyCoeffEqv.refl (square d)))
      (Certificate.square d (supported_add ha (support_neg hb)))
  have h := weighted_order R C
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (weighted_scale n W (polyMul a b) 2))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_weighted_add n W (square a) (square b))))

/-- Both fourth moments imply the mixed second-chordal product bound under
the same weight. Empty or zero budgets require no inverse. -/
theorem mixed_square_bound {n : Nat} {W a b : RatPoly} (R : Certificate n W)
    (ha : SupportedQuaternionBlocks n a) (hb : SupportedQuaternionBlocks n b)
    (B : Q') (hA : moment n W (square a) ≤ B) (hB : moment n W (square b) ≤ B) :
    moment n W (polyMul a b) ≤ B := by
  have h := Q'.le_trans' _ _ _ (square_young R ha hb) (Q'.add_le_add hA hB)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) (by decide) (fun _ => B))))
    (by decide : (0 : Q') < 2)

/-- The exact signed insertion is q*u on both endpoints, with all heat
factors retained. No positivity premise is imposed on q*u. -/
theorem signed_coordinate_cross_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K+1) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i ∈ ids)
    {q u : RatPoly} (hq : SupportedQuaternionBlocks n q) (hu : SupportedQuaternionBlocks n u) :
    moment (n+n) (edgeWeight n w (K+1) ids q)
      (polyMul (chordal n i) (polyMul u (liftBoundary n u))) ≤
      (6*(1-w))*moment (n+n) (edgeWeight n w (K+1) ids q) (polyMul u (liftBoundary n u)) := by
  have h := product_displacement_nome_bound n hw0 hw1 K hK ids hids i hi (supported_polyMul hq hu)
  have he : RatPolyCoeffEqv (edgeWeight n w (K+1) ids (polyMul q u))
      (polyMul (edgeWeight n w (K+1) ids q) (polyMul u (liftBoundary n u))) := by
    unfold edgeWeight
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 2) (.var 4)))
      (by decide) (fun
        | 0 => productHeat n w (K+1) ids | 1 => q | 2 => u
        | 3 => liftBoundary n q | _ => liftBoundary n u)
  have hl := haar_of_coeff (blocks := n+n) ((he.mul_right (chordal n i)).trans
    ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
      ((RatPolyCoeffEqv.mul_comm (polyMul u (liftBoundary n u)) (chordal n i)).mul_left _)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff he))))

/-- Radial scalar endpoint identity plus exact signed heat alignment. The
factor two keeps this estimate division-free; the source may be signed. -/
theorem product_endpoint_square_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K+1) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i ∈ ids)
    {q u : RatPoly} (hq : SupportedQuaternionBlocks n q) (hu : SupportedQuaternionBlocks n u)
    (R : Certificate (n+n) (edgeWeight n w (K+1) ids q)) :
    2*moment (n+n) (edgeWeight n w (K+1) ids q) (polyMul (chordal n i) (square u)) ≤
      (2*(6*(1-w)))*moment (n+n) (edgeWeight n w (K+1) ids q) (square u) +
        moment (n+n) (edgeWeight n w (K+1) ids q)
          (polyMul (chordal n i) (square (polyAdd u (polyNeg (liftBoundary n u))))) := by
  let W := edgeWeight n w (K+1) ids q
  let U := liftBoundary n u
  let D := chordal n i
  let c := 6*(1-w)
  have hs := endpoint_square_swap n (productHeat n w (K+1) ids) q u
    (productHeat_supported n w (K+1) ids hids) hq hu (productHeat_swap n w (K+1) ids hids)
  have hd : SupportedQuaternionBlocks (n+n) D := support_norm (difference_supported
    (Supported.coordinate (by have := hids i hi; omega))
    (Supported.coordinate (by have := hids i hi; omega)))
  have hds := endpoint_square_swap n (polyMul (productHeat n w (K+1) ids) D) q u
    (supported_polyMul (productHeat_supported n w (K+1) ids hids) hd) hq hu (by
      rw [reindexQuaternionPolynomial_mul]
      exact (productHeat_swap n w (K+1) ids hids).mul (chordal_swap n i (hids i hi)))
  have hmove (v : RatPoly) :
      moment (n+n) (polyMul (polyMul (polyMul (productHeat n w (K+1) ids) D) q)
        (liftBoundary n q)) v ≈ moment (n+n) W (polyMul D v) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
      (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.mul (.var 1) (.var 4)))
      (by decide) (fun
        | 0 => productHeat n w (K+1) ids | 1 => D | 2 => q
        | 3 => liftBoundary n q | _ => v))
  have hsD := Q'.eqv_trans _ _ _ (Q'.eqv_symm (hmove (square u)))
    (Q'.eqv_trans _ _ _ hds (hmove (square U)))
  have hy := Q'.le_trans' _ _ _ (square_young R (support_lower hu) (lift_supported hu n))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hs))
      (poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
        (by decide) (fun _ => moment (n+n) W (square u)))))
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  have htwice (z : Q') : 2*(c*z) ≈ c*(2*z) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.const 2) (.var 1)))
      (by decide) (fun | 0 => c | _ => z)
  have hcxy := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 2
      (signed_coordinate_cross_bound n hw0 hw1 K hK ids hids i hi hq hu) (by decide))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (htwice _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ c hy hc)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.const 2) (.var 1)))
          (.mul (.mul (.const 2) (.var 0)) (.var 1)) (by decide)
          (fun | 0 => c | _ => moment (n+n) W (square u))))))
  have he : moment (n+n) W (polyMul D (square (polyAdd u (polyNeg U)))) ≈
      moment (n+n) W (polyMul D (square u)) +
        moment (n+n) W (polyMul D (square U)) +
          -(2*moment (n+n) W (polyMul D (polyMul u U))) := by
    have hp : RatPolyCoeffEqv (polyMul D (square (polyAdd u (polyNeg U))))
        (polyAdd (polyAdd (polyMul D (square u)) (polyMul D (square U)))
          (polyNeg (polySmul 2 (polyMul D (polyMul u U))))) :=
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))
        (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 2) (.var 2))))
          (.neg (.mul (.const 2) (.mul (.var 0) (.mul (.var 1) (.var 2))))))
        (by decide) (fun | 0 => D | 1 => u | _ => U)).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left 2 _)))
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_left W))
      (Q'.eqv_trans _ _ _ (weighted_difference (n+n) W _ _)
        (Q'.add_eqv_congr' (haar_weighted_add (n+n) W _ _)
          (Q'.neg_eqv_congr _ _ (weighted_scale (n+n) W _ 2))))
  have hid : 2*moment (n+n) W (polyMul D (square u)) ≈
      2*moment (n+n) W (polyMul D (polyMul u U))+
        moment (n+n) W (polyMul D (square (polyAdd u (polyNeg U)))) := by
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.const 2) (.var 0))
        (.add (.mul (.const 2) (.var 1))
          (.add (.add (.var 0) (.var 0)) (.neg (.mul (.const 2) (.var 1)))))
        (by decide) (fun
          | 0 => moment (n+n) W (polyMul D (square u))
          | _ => moment (n+n) W (polyMul D (polyMul u U))))
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _ he
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hsD))))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) (Q'.add_le_add_right _ _ _ hcxy)

#print axioms signed_coordinate_cross_bound
#print axioms product_endpoint_square_bound
#print axioms mixed_square_bound
#print axioms support_lower
#print axioms support_neg
#print axioms support_norm
#print axioms normCertificate
#print axioms padded_neg
#print axioms padded_norm
#print axioms square_young

end YMGap.Continuum.SU2QuaternionProductHeatRadialAlignment
