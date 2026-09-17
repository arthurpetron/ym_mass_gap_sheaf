/-
# Off-diagonal original-action Gram bounds for finite plaquette duals

The support of the finite reciprocal stays in the selected boundary star.
If two face boundaries do not touch and no selected action face touches both,
the second dual misses every boundary link of the first face. This yields an
exact zero under the first erased background, not under the full action.

Restoring the FULL selected action leaves the actual finite reciprocal error.
The existing local error and dual norm bounds imply
  lower(w)^2 * H[A*d_p,k*d_q,l]^2 <= rate(w)^(2*k) * H[R_p]*H[R_q].
Every degree is finite; the selected action and both remaining partitions are
retained. The geometric noninterference predicate is explicit and decidable.
No summed frame estimate, inverse limit, OS quotient or spectral gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryOverlap
import YMGap.Continuum.RationalFiniteSparseGram

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryOverlap
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal remainder scale)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (corrector_local)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

attribute [local irreducible] correctedSlabPlaquettePolynomial

/-- The existing finite algorithm introduces no new block coordinates. -/
theorem reciprocal_local {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    BlockLocal blocks allowed (reciprocal p u hu k) := by
  have hr : BlockLocal blocks allowed (remainder p u hu) :=
    (hp.smul (scale u hu)).add (BlockLocal.one blocks allowed).neg
  exact (corrector_local hr k).smul (scale u hu)

/-- Literal locality includes the face boundary AND its complete selected star. -/
theorem dualTest_local {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) (face : Z4Plaq) (k : Nat) :
    LinkLocal extent (edgesOf face ++ faceLinks extent (boundaryStar extent ids face))
      (dualTest hw0 K extent ids face k) := by
  have hc0 : LinkLocal extent (edgesOf face) (faceCharacter extent face) :=
    (face_scalar_local extent face).character 1
  have hc : LinkLocal extent
      (edgesOf face ++ faceLinks extent (boundaryStar extent ids face))
      (faceCharacter extent face) := hc0.mono
    (fun _ hi => List.mem_append.mpr (Or.inl hi))
  have hs : LinkLocal extent
      (edgesOf face ++ faceLinks extent (boundaryStar extent ids face))
      (starHeat w K extent ids face) :=
    (heatProduct_local w K extent (boundaryStar extent ids face)).mono
    (fun _ hi => List.mem_append.mpr (Or.inr hi))
  exact hc.mul (reciprocal_local hs (upper w) (upper_positive hw0) k)

/-- Geometric noninterference supplies the missing-link premise for the ACTUAL
finite second dual; no statistical independence assumption is supplied. -/
theorem rest_dual_pairing_zero {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent) (q : Z4Plaq) (l : Nat)
    (hsep : ¬ Interferes extent ids p q) :
    quaternionHaar (B extent) (polyMul (restHeat w K extent ids p)
      (polyMul (faceCharacter extent p) (dualTest hw0 K extent ids q l))) ≈ 0 := by
  let link : Z4Link := (p.1, (dirsOf p.2).1)
  have hl : link ∈ edgesOf p := List.mem_cons_self
  exact rest_character_spectator_zero w K extent ids hp link hl 1 (by decide)
    (dualTest hw0 K extent ids q l) (dualTest_supported hw0 K extent ids q l)
    (edgesOf q ++ faceLinks extent (boundaryStar extent ids q))
    (dualTest_local hw0 K extent ids q l)
    (fun hi => (List.mem_append.mp hi).elim
      (noninterference_boundary_misses hsep link hl)
      (noninterference_star_misses hsep link hl))

private theorem cancellation_insert (S R C D E F : RatPoly)
    (h : RatPolyCoeffEqv (polyAdd (polyMul S D) (polyMul C E)) C) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul S R) (polyMul D F))
        (polyMul R (polyMul C (polyMul F E))))
      (polyMul R (polyMul C F)) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 5)))
      (.mul (.var 1) (.mul (.var 2) (.mul (.var 5) (.var 4)))))
    (.mul (.var 1)
      (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 4))) (.var 5)))
    (by decide) (fun | 0 => S | 1 => R | 2 => C | 3 => D | 4 => E | _ => F)).trans
    ((h.mul_right F).mul_left R)

/-- The original-action Gram entry is the NEGATIVE of the displayed residual;
finite-degree Gram orthogonality is not asserted. -/
theorem fullAction_gram_residual_zero {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent) (q : Z4Plaq) (k l : Nat)
    (hsep : ¬ Interferes extent ids p q) :
    quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids p k) (dualTest hw0 K extent ids q l))) +
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids p)
        (polyMul (faceCharacter extent p)
          (polyMul (dualTest hw0 K extent ids q l)
            (residualPolynomial hw0 K extent ids p k)))) ≈ 0 := by
  have he := (((selected_heat_partition w K extent ids p).mul_right
      (polyMul (dualTest hw0 K extent ids p k) (dualTest hw0 K extent ids q l))).add
      (RatPolyCoeffEqv.refl
        (polyMul (restHeat w K extent ids p)
          (polyMul (faceCharacter extent p)
            (polyMul (dualTest hw0 K extent ids q l)
              (residualPolynomial hw0 K extent ids p k)))))).trans
    (cancellation_insert (starHeat w K extent ids p) (restHeat w K extent ids p)
      (faceCharacter extent p) (dualTest hw0 K extent ids p k)
      (residualPolynomial hw0 K extent ids p k) (dualTest hw0 K extent ids q l)
      (cancellation_pin hw0 K extent ids p k))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (rest_dual_pairing_zero hw0 K extent ids hp q l hsep))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (j : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ j)

private theorem weighted_haar_cs {blocks : Nat} {R p q : RatPoly}
    (Rpos : Certificate blocks R) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    quaternionHaar blocks (polyMul R (polyMul p q)) *
      quaternionHaar blocks (polyMul R (polyMul p q)) ≤
      quaternionHaar blocks (polyMul R (polyMul p p)) *
        quaternionHaar blocks (polyMul R (polyMul q q)) := by
  have pin (a b : RatPoly) : weightedPair blocks R a b ≈
      quaternionHaar blocks (polyMul R (polyMul a b)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul (pin p q) (pin p q)))
    (Q'.le_trans' _ _ _ (weighted_cauchySchwarz blocks R p q Rpos hp hq)
      (Q'.le_of_eqv (qmul (pin p p) (pin q q))))

private theorem scaled_cauchy_bound {L D E N M x : Q'}
    (hL : (0 : Q') ≤ L) (hM : (0 : Q') ≤ M) (hD : (0 : Q') ≤ D)
    (hcs : x*x ≤ N*M) (hn : L*N ≤ D) (hm : L*M ≤ E) :
    (L*L)*(x*x) ≤ D*E := by
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (L*L) hcs (Q'.mul_nonneg _ _ hL hL)
  have he : (L*L)*(N*M) ≈ (L*N)*(L*M) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => L | 1 => N | _ => M)
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hn (Q'.mul_nonneg _ _ hL hM))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hm hD)))

private theorem square_of_sum_zero {a b : Q'} (h : a+b ≈ 0) : a*a ≈ b*b := by
  have hz : (a+b)*(a + -b) ≈ 0 :=
    Q'.eqv_trans _ _ _ (qmul h (Q'.eqv_refl _)) (Q'.zero_mul_eqv _)
  have he : a*a ≈ b*b+(a+b)*(a + -b) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.neg (.var 1)))))
      (by decide) (fun | 0 => a | _ => b)
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hz)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem scaled_error_bound {L r D E N a b : Q'}
    (hL : (0 : Q') ≤ L) (hr : (0 : Q') ≤ r) (hD : (0 : Q') ≤ D)
    (hz : a+b ≈ 0) (hb : L*(b*b) ≤ (r*D)*N) (hn : L*N ≤ E) :
    (L*L)*(a*a) ≤ (r*D)*E := by
  have he : (L*L)*(a*a) ≈ L*(L*(b*b)) :=
    Q'.eqv_trans _ _ _ (qmul (Q'.eqv_refl _) (square_of_sum_zero hz))
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 0)) (.var 1))
        (.mul (.var 0) (.mul (.var 0) (.var 1))) (by decide)
        (fun | 0 => L | _ => b*b))
  have hm : L*((r*D)*N) ≈ (r*D)*(L*N) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => L | 1 => r*D | _ => N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ L hb hL)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hm)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hn (Q'.mul_nonneg _ _ hr hD))))

/-- Quantitative off-diagonal Gram control in the FULL original selected
action. Both remaining partitions survive; no sum over faces is bounded here.
Only the first dual's finite degree appears in this one-sided estimate. -/
theorem fullAction_gram_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {p q : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (k l : Nat)
    (hsep : ¬ Interferes extent ids p q) :
    let gram := quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids p k) (dualTest hw0 K extent ids q l)))
    (lower w * lower w) * (gram * gram) ≤
      ((rate hw0)^k * (rate hw0)^k * quaternionHaar (B extent) (restHeat w K extent ids p)) *
        quaternionHaar (B extent) (restHeat w K extent ids q) := by
  let S := starHeat w K extent ids p
  let R := restHeat w K extent ids p
  let F := dualTest hw0 K extent ids q l
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  have Rpos : Certificate (B extent) R :=
    headProduct_certificate hw0 hw1 K extent hK _
      (fun id hi => hids id (boundaryRest_mem hi).1)
  have hb := QuaternionHaarLocalDualNorm.local_dual_pairing_error
    (starHeat_supported w K extent ids p) (lower_positive hw0 hw1)
    (upper_positive hw0) (lower_le_upper hw0 hw1)
    (starLowerCertificate hw0 hw1 K extent hK ids hids hnodup p)
    (starUpperCertificate hw0 hw1 K extent ids hids hnodup p) k Rpos
    (faceCharacter_supported extent p) (dualTest_supported hw0 K extent ids q l)
  have hn : quaternionHaar (B extent) (polyMul (polyMul R S) (polyMul F F)) ≈
      quaternionHaar (B extent) (polyMul A (polyMul F F)) :=
    haar_of_coeff (((RatPolyCoeffEqv.mul_comm R S).trans
      (selected_heat_partition w K extent ids p).symm).mul_right (polyMul F F))
  have herror := Q'.le_trans' _ _ _ hb
    (Q'.le_of_eqv (qmul
      (qmul (Q'.eqv_refl _) (rest_square_moment w K extent ids hp)) hn))
  exact scaled_error_bound (Q'.le_of_lt (lower_positive hw0 hw1))
    (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (rate_nonnegative hw0 hw1) k)
      (Q'.pow_nonneg _ (rate_nonnegative hw0 hw1) k)) Rpos.haar_nonnegative
    (fullAction_gram_residual_zero hw0 K extent ids hp q k l hsep) herror
    (fullAction_norm_bound hw0 hw1 K extent hK ids hids hnodup hq l)

/-- The unconditional Gram cap includes interfering faces, equal labels and
arbitrary finite degrees. It uses the SAME original-action Cauchy--Schwarz. -/
theorem fullAction_gram_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {p q : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (k l : Nat) :
    let gram := quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids p k) (dualTest hw0 K extent ids q l)))
    (lower w * lower w) * (gram * gram) ≤
      quaternionHaar (B extent) (restHeat w K extent ids p) *
        quaternionHaar (B extent) (restHeat w K extent ids q) := by
  have Apos := headProduct_certificate hw0 hw1 K extent hK ids hids
  have Rpos := headProduct_certificate hw0 hw1 K extent hK
    (boundaryRest extent ids p) (fun id hi => hids id (boundaryRest_mem hi).1)
  exact scaled_cauchy_bound (Q'.le_of_lt (lower_positive hw0 hw1))
    (Apos.mul (Certificate.square _ (dualTest_supported hw0 K extent ids q l))).haar_nonnegative
    Rpos.haar_nonnegative
    (weighted_haar_cs Apos (dualTest_supported hw0 K extent ids p k)
      (dualTest_supported hw0 K extent ids q l))
    (fullAction_norm_bound hw0 hw1 K extent hK ids hids hnodup hp k)
    (fullAction_norm_bound hw0 hw1 K extent hK ids hids hnodup hq l)

private theorem coefficient_young {L g r D E : Q'}
    (hr : (0 : Q') ≤ r) (hD : (0 : Q') ≤ D) (hE : (0 : Q') ≤ E)
    (a b : Q') (h : (L*L)*(g*g) ≤ (r*r*D)*E) :
    (2 : Q')*(L*a*b*g) ≤ r*(a*a*D+b*b*E) := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ ((a*a)*(b*b)) h
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg a)
      (SumOfSquares.q_mul_self_nonneg b))
  have hl : (L*a*b*g)*(L*a*b*g) ≈ ((a*a)*(b*b))*((L*L)*(g*g)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)))
      (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))))
      (by decide) (fun | 0 => L | 1 => a | 2 => b | _ => g)
  have ht : ((a*a)*(b*b))*((r*r*D)*E) ≈
      (r*r)*((a*a*D)*(b*b*E)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.mul (.var 2) (.var 2)) (.var 3)) (.var 4)))
      (.mul (.mul (.var 2) (.var 2))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 3))
          (.mul (.mul (.var 1) (.var 1)) (.var 4))))
      (by decide) (fun | 0 => a | 1 => b | 2 => r | 3 => D | _ => E)
  exact RationalFiniteSparseGram.weighted_young hr
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg a) hD)
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg b) hE)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ht)))

/-- Signed coefficients enter through weighted Young, not their absolute sum.
The actual interference test selects the unit cap or the finite-degree rate.
This is the pairwise input to a later bounded-degree finite-family sum. -/
theorem fullAction_gram_young {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {p q : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (k : Nat) (a b : Q') :
    let gram := quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids p k) (dualTest hw0 K extent ids q k)))
    (2 : Q')*(lower w*a*b*gram) ≤
      (if Interferes extent ids p q then 1 else (rate hw0)^k) *
        (a*a*quaternionHaar (B extent) (restHeat w K extent ids p) +
          b*b*quaternionHaar (B extent) (restHeat w K extent ids q)) := by
  have hD := (headProduct_certificate hw0 hw1 K extent hK
    (boundaryRest extent ids p) (fun id hi => hids id (boundaryRest_mem hi).1)).haar_nonnegative
  have hE := (headProduct_certificate hw0 hw1 K extent hK
    (boundaryRest extent ids q) (fun id hi => hids id (boundaryRest_mem hi).1)).haar_nonnegative
  by_cases hi : Interferes extent ids p q
  · simp only [if_pos hi]
    apply coefficient_young Q'.zero_le_one hD hE a b
    exact Q'.le_trans' _ _ _
      (fullAction_gram_square_le hw0 hw1 K extent hK ids hids hnodup hp hq k k)
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.var 0) (.var 1))
        (.mul (.mul (.mul (.const 1) (.const 1)) (.var 0)) (.var 1))
        (by decide) (fun
          | 0 => quaternionHaar (B extent) (restHeat w K extent ids p)
          | _ => quaternionHaar (B extent) (restHeat w K extent ids q))))
  · simp only [if_neg hi]
    exact coefficient_young (Q'.pow_nonneg _ (rate_nonnegative hw0 hw1) k) hD hE a b
      (fullAction_gram_square_bound hw0 hw1 K extent hK ids hids hnodup hp hq k k hi)

#print axioms reciprocal_local
#print axioms dualTest_local
#print axioms rest_dual_pairing_zero
#print axioms fullAction_gram_residual_zero
#print axioms fullAction_gram_square_bound
#print axioms fullAction_gram_square_le
#print axioms fullAction_gram_young

end YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualGram
