/-
# A finite signed plaquette dual family in the full original action

The actual dual sum has the same rational coefficients as the original face
span. A duplicate-free physical label list makes coefficient extraction exact;
no positivity assumption is made on those coefficients. The concrete bounded
interference rows and the finite off-row residual control its full-action norm.

The exact summed pairing retains its residual, whose upper bound is in the
original face-span square norm. Every reciprocal degree is finite. These are
original weighted-Haar estimates, not a limiting OS gap or continuum claim.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualGram
import YMGap.Continuum.RationalFiniteSparseGram
import YMGap.Continuum.GNSFiniteDualCoercivity

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryOverlap
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualGram
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] correctedSlabPlaquettePolynomial

def dualFamily {w : Q'} (hw0 : (0 : Q') < w) (K extent : Nat) (ids : List Nat)
    (k : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : RatPoly :=
  finitePolySum (fun p => polySmul (c p) (dualTest hw0 K extent ids p k)) qs

def sourceSpan (extent : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : RatPoly :=
  faceSpan extent (qs.map (fun p => (c p, p)))

def familyBudget (w : Q') (K extent : Nat) (ids : List Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  listQSum (fun p => c p*c p*quaternionHaar (B extent) (restHeat w K extent ids p)) qs

def sourceEnergy (w : Q') (K extent : Nat) (ids : List Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  quaternionHaar (B extent)
    (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polyMul (sourceSpan extent c qs) (sourceSpan extent c qs)))

def familyError {w : Q'} (hw0 : (0 : Q') < w) (K extent : Nat) (ids : List Nat)
    (k : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  listQSum (fun p => c p * quaternionHaar (B extent)
    (polyMul (restHeat w K extent ids p) (polyMul (faceCharacter extent p)
      (polyMul (residualPolynomial hw0 K extent ids p k) (sourceSpan extent c qs))))) qs

theorem sourceSpan_supported (extent : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    SupportedQuaternionBlocks (B extent) (sourceSpan extent c qs) :=
  faceSpan_supported extent _

private theorem supported_sum {A : Type} {blocks : Nat} (f : A → RatPoly) (c : A → Q')
    (hf : ∀ p, SupportedQuaternionBlocks blocks (f p)) : ∀ qs,
    SupportedQuaternionBlocks blocks (finitePolySum (fun p => polySmul (c p) (f p)) qs)
  | [] => by intro t ht; cases ht
  | p::qs => supported_add (by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact hf p s hs) (supported_sum f c hf qs)

theorem dualFamily_supported {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) (k : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    SupportedQuaternionBlocks (B extent) (dualFamily hw0 K extent ids k c qs) :=
  supported_sum _ c (fun p => dualTest_supported hw0 K extent ids p k) qs

private theorem coefficient_absent (p : Z4Plaq) (c : Z4Plaq → Q') : ∀ qs : List Z4Plaq,
    p ∉ qs → coefficientAt p (qs.map (fun q => (c q,q))) ≈ 0
  | [], _ => Q'.eqv_refl _
  | q::qs, hp => by
      have hq : q ≠ p := fun he => hp (List.mem_cons.mpr (Or.inl he.symm))
      have ht : p ∉ qs := fun he => hp (List.mem_cons_of_mem q he)
      simp only [List.map_cons, coefficientAt, listQSum, if_neg hq]
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (coefficient_absent p c qs ht))
        (Q'.eqv_of_eq (Q'.zero_add' _))

/-- The source map and the dual coefficients agree, with no hidden duplicate deletion. -/
theorem coefficientAt_map (p : Z4Plaq) (c : Z4Plaq → Q') : ∀ qs : List Z4Plaq,
    qs.Nodup → p ∈ qs → coefficientAt p (qs.map (fun q => (c q,q))) ≈ c p
  | [], _, hp => False.elim (List.not_mem_nil hp)
  | q::qs, hn, hp => by
      rcases List.mem_cons.mp hp with he | ht
      · subst p
        simp only [List.map_cons, coefficientAt, listQSum]
        exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (coefficient_absent q c qs (List.nodup_cons.mp hn).1))
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hq : q ≠ p := fun he => (List.nodup_cons.mp hn).1 (he.symm ▸ ht)
        simp only [List.map_cons, coefficientAt, listQSum, if_neg hq]
        exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (coefficientAt_map p c qs (List.nodup_cons.mp hn).2 ht))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (j : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ j)

private def pair (blocks : Nat) (A p q : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul A (polyMul p q))

private theorem pair_symm (blocks : Nat) (A p q : RatPoly) : pair blocks A p q ≈ pair blocks A q p :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_comm p q).mul_left A)

private theorem pair_add (blocks : Nat) (A p q r : RatPoly) :
    pair blocks A (polyAdd p q) r ≈ pair blocks A p r + pair blocks A q r := by
  unfold pair
  rw [polyMul_add_left_exact]
  exact quaternionHaar_polyMul_add_right blocks A _ _

private theorem pair_smul (blocks : Nat) (A : RatPoly) (c : Q') (p q : RatPoly) :
    pair blocks A (polySmul c p) q ≈ c*pair blocks A p q :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_left c p q).mul_left A))
    (quaternionHaar_polyMul_smul_right blocks c A (polyMul p q))

/-- Weighted Haar pairing is linear in the literal finite signed dual sum. -/
theorem pair_sum_left {I : Type} (blocks : Nat) (A : RatPoly)
    (c : I → Q') (f : I → RatPoly) (q : RatPoly) : ∀ xs,
    pair blocks A (finitePolySum (fun p => polySmul (c p) (f p)) xs) q ≈
      listQSum (fun p => c p*pair blocks A (f p) q) xs
  | [] => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right A)
  | p::xs => Q'.eqv_trans _ _ _ (pair_add blocks A _ _ q)
      (Q'.add_eqv_congr' (pair_smul blocks A (c p) (f p) q) (pair_sum_left blocks A c f q xs))

private theorem pair_sum_right {I : Type} (blocks : Nat) (A : RatPoly)
    (c : I → Q') (f : I → RatPoly) (q : RatPoly) (xs : List I) :
    pair blocks A q (finitePolySum (fun p => polySmul (c p) (f p)) xs) ≈
      listQSum (fun p => c p*pair blocks A q (f p)) xs :=
  Q'.eqv_trans _ _ _ (pair_symm blocks A _ _)
    (Q'.eqv_trans _ _ _ (pair_sum_left blocks A c f q xs)
      (listQSum_congr (fun p => qmul (Q'.eqv_refl _) (pair_symm blocks A (f p) q)) xs))

private theorem scaled_double_sum {I : Type} (blocks : Nat) (A : RatPoly) (L : Q')
    (c : I → Q') (f : I → RatPoly) (xs : List I) :
    L*pair blocks A (finitePolySum (fun p => polySmul (c p) (f p)) xs)
      (finitePolySum (fun p => polySmul (c p) (f p)) xs) ≈
    listQSum (fun p => listQSum (fun q => L*c p*c q*pair blocks A (f p) (f q)) xs) xs := by
  have hh := qmul (Q'.eqv_refl L)
    (pair_sum_left blocks A c f (finitePolySum (fun p => polySmul (c p) (f p)) xs) xs)
  refine Q'.eqv_trans _ _ _ hh (Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_left L _ xs)) ?_)
  apply listQSum_congr
  intro p
  have hp := qmul (Q'.eqv_refl L) (qmul (Q'.eqv_refl (c p)) (pair_sum_right blocks A c f (f p) xs))
  refine Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv L (c p) _)) ?_)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_left (L*c p) _ xs)) ?_
  exact listQSum_congr (fun q => Q'.eqv_symm (Q'.mul_assoc_eqv (L*c p) (c q) _)) xs

private theorem budget_term_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (c : Q') (p : Z4Plaq) :
    (0 : Q') ≤ c*c*quaternionHaar (B extent) (restHeat w K extent ids p) :=
  Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg c)
    (headProduct_certificate hw0 hw1 K extent hK (boundaryRest extent ids p)
      (fun id hi => hids id (boundaryRest_mem hi).1)).haar_nonnegative

theorem familyBudget_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    (0 : Q') ≤ familyBudget w K extent ids c qs :=
  listQSum_nonnegative_on _ qs (fun p _ => budget_term_nonnegative hw0 hw1 K extent hK ids hids (c p) p)

theorem sourceEnergy_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    (0 : Q') ≤ sourceEnergy w K extent ids c qs :=
  ((headProduct_certificate hw0 hw1 K extent hK ids hids).mul
    (Certificate.square (sourceSpan extent c qs) (sourceSpan_supported extent c qs))).haar_nonnegative

/-- The concrete 600-neighbor geometry controls the actual finite dual norm;
the remaining finite-degree term names the family cardinality explicitly. -/
theorem family_norm_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') (k : Nat) :
    lower w * quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualFamily hw0 K extent ids k c qs) (dualFamily hw0 K extent ids k c qs))) ≤
      (Q'.ofNat 600 + (rate hw0)^k * Q'.ofNat qs.length) * familyBudget w K extent ids c qs := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let d := fun p => dualTest hw0 K extent ids p k
  have hs := RationalFiniteSparseGram.sparse_gram_bound qs (Interferes extent ids) 600 ((rate hw0)^k)
    (fun p => c p*c p*quaternionHaar (B extent) (restHeat w K extent ids p))
    (fun p q => lower w*c p*c q*pair (B extent) A (d p) (d q))
    (Q'.pow_nonneg _ (rate_nonnegative hw0 hw1) k)
    (fun p _ => budget_term_nonnegative hw0 hw1 K extent hK ids hids (c p) p)
    (fun _ _ _ _ => ⟨Interferes.symm, Interferes.symm⟩)
    (fun p _ => nodup_interfering_length_le extent ids p _ (List.filter_sublist.nodup hn)
      (fun q hq => of_decide_eq_true (List.mem_filter.mp hq).2))
    (fun p hp q hq => fullAction_gram_young hw0 hw1 K extent hK ids hids hnodup
      (hqs p hp) (hqs q hq) k (c p) (c q))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (scaled_double_sum (B extent) A (lower w) c d qs)) hs

/-- Exact original pairing, including all finite inverse errors with their signs. -/
theorem family_pairing {w : Q'} (hw0 : (0 : Q') < w) (K extent : Nat) (ids : List Nat)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') (k : Nat) :
    quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualFamily hw0 K extent ids k c qs) (sourceSpan extent c qs))) +
      familyError hw0 K extent ids k c qs ≈ familyBudget w K extent ids c qs := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let F := sourceSpan extent c qs
  let d := fun p => dualTest hw0 K extent ids p k
  let e := fun p => quaternionHaar (B extent) (polyMul (restHeat w K extent ids p)
    (polyMul (faceCharacter extent p) (polyMul (residualPolynomial hw0 K extent ids p k) F)))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (pair_sum_left (B extent) A c d F qs) (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_add (fun p => c p*pair (B extent) A (d p) F)
    (fun p => c p*e p) qs)) ?_
  apply listQSum_congr_on _ _ qs
  intro p hp
  have hs := fullAction_signed_pairing hw0 K extent ids (hqs p hp) k (qs.map (fun q => (c q,q)))
  have hc := Q'.eqv_trans _ _ _ hs (qmul (coefficientAt_map p c qs hn hp) (Q'.eqv_refl _))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv (c p) _ _))
    (Q'.eqv_trans _ _ _ (qmul (Q'.eqv_refl _) hc)
      (Q'.eqv_symm (Q'.mul_assoc_eqv (c p) (c p) _)))

/-- Signed residual payment from its squared bound, for any nonnegative energy. -/
theorem error_young {L r D E x : Q'} (c : Q')
    (hL : (0 : Q') ≤ L) (hr : (0 : Q') ≤ r) (hD : (0 : Q') ≤ D) (hE : (0 : Q') ≤ E)
    (hx : L*(x*x) ≤ (r*r*D)*E) : 2*L*(c*x) ≤ r*(L*(c*c*D)+E) := by
  have he : (L*c*x)*(L*c*x) ≈ (L*(c*c))*(L*(x*x)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => L | 1 => c | _ => x)
  have hm : (L*(c*c))*((r*r*D)*E) ≈ (r*r)*((L*(c*c*D))*E) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.mul (.var 2) (.var 2)) (.var 3)) (.var 4)))
      (.mul (.mul (.var 2) (.var 2))
        (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 3))) (.var 4)))
      (by decide) (fun | 0 => L | 1 => c | 2 => r | 3 => D | _ => E)
  have hb := Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hx (Q'.mul_nonneg _ _ hL (SumOfSquares.q_mul_self_nonneg c)))
      (Q'.le_of_eqv hm))
  have hy := RationalFiniteSparseGram.weighted_young hr
    (Q'.mul_nonneg _ _ hL (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg c) hD)) hE hb
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
    (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
    (by decide) (fun | 0 => L | 1 => c | _ => x))) hy

/-- The signed residual needs only an upper estimate. Its exact source norm
and finite family size remain visible; coefficients may have either sign. -/
theorem family_error_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (_hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') (k : Nat) :
    2*lower w*familyError hw0 K extent ids k c qs ≤
      (rate hw0)^k * (lower w*familyBudget w K extent ids c qs +
        Q'.ofNat qs.length*sourceEnergy w K extent ids c qs) := by
  let L := lower w
  let r := (rate hw0)^k
  let E := sourceEnergy w K extent ids c qs
  let b := fun p => c p*c p*quaternionHaar (B extent) (restHeat w K extent ids p)
  let e := fun p => quaternionHaar (B extent) (polyMul (restHeat w K extent ids p)
    (polyMul (faceCharacter extent p)
      (polyMul (residualPolynomial hw0 K extent ids p k) (sourceSpan extent c qs))))
  have hpoint : ∀ p, p ∈ qs → 2*L*(c p*e p) ≤ r*(L*b p+E) := by
    intro p hp
    have hD := (headProduct_certificate hw0 hw1 K extent hK (boundaryRest extent ids p)
      (fun id hi => hids id (boundaryRest_mem hi).1)).haar_nonnegative
    exact error_young (c p) (Q'.le_of_lt (lower_positive hw0 hw1))
      (Q'.pow_nonneg _ (rate_nonnegative hw0 hw1) k) hD
      (sourceEnergy_nonnegative hw0 hw1 K extent hK ids hids c qs)
      (fullAction_signed_pairing_error hw0 hw1 K extent hK ids hids hnodup (hqs p hp) k
        (qs.map (fun q => (c q,q))))
  have hs := Z4FiniteCylinderQuadraticStability.listQSum_mono _ _ qs hpoint
  have hrhs : listQSum (fun p => r*(L*b p+E)) qs ≈
      r*(L*familyBudget w K extent ids c qs + Q'.ofNat qs.length*E) :=
    Q'.eqv_trans _ _ _ (listQSum_mul_left r _ qs)
      (qmul (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (listQSum_add _ _ qs)
        (Q'.add_eqv_congr' (listQSum_mul_left L b qs)
          (Q'.eqv_trans _ _ _ (RationalFiniteSparseGram.listQSum_const E qs) (Q'.mul_comm_eqv E _)))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (listQSum_mul_left (2*L) (fun p => c p*e p) qs))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hrhs))

/-- The finite residuals disappear by an explicit geometric modulus. The
original signed span controls the entire retained-mass coefficient budget,
with no final factor depending on family cardinality or selected volume. -/
theorem family_coercivity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') :
    lower w * familyBudget w K extent ids c qs ≤
      600 * sourceEnergy w K extent ids c qs := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let P := headProduct_certificate hw0 hw1 K extent hK ids hids
  let D := QuaternionHaarWeightedCauchySchwarz.weightedGNSData (B extent) A P
  let F : D.V := ⟨sourceSpan extent c qs, sourceSpan_supported extent c qs⟩
  let tests : Nat → D.V := fun k =>
    ⟨dualFamily hw0 K extent ids k c qs, dualFamily_supported hw0 K extent ids k c qs⟩
  have pin (f g : D.V) : D.B f g ≈ pair (B extent) A f.val g.val :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hnorm (k : Nat) : lower w*D.B (tests k) (tests k) ≤
      (600+(rate hw0)^k*Q'.ofNat qs.length)*familyBudget w K extent ids c qs :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (qmul (Q'.eqv_refl _) (pin (tests k) (tests k))))
      (family_norm_bound hw0 hw1 K extent hK ids hids hnodup qs hn hqs c k)
  have hpair (k : Nat) : D.B (tests k) F + familyError hw0 K extent ids k c qs ≈
      familyBudget w K extent ids c qs :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (pin (tests k) F) (Q'.eqv_refl _))
      (family_pairing hw0 K extent ids qs hn hqs c k)
  have herror (k : Nat) : 2*lower w*familyError hw0 K extent ids k c qs ≤
      (rate hw0)^k*(lower w*familyBudget w K extent ids c qs+Q'.ofNat qs.length*D.B F F) :=
    Q'.le_trans' _ _ _ (family_error_bound hw0 hw1 K extent hK ids hids hnodup qs hn hqs c k)
      (Q'.ge_of_eqv (qmul (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (qmul (Q'.eqv_refl _) (pin F F)))))
  have h := GNSFiniteDualCoercivity.coercivity_of_finite_tests D F tests
    (fun k => familyError hw0 K extent ids k c qs) (familyBudget w K extent ids c qs)
    (lower w) 600 (Q'.ofNat qs.length) (rate hw0)
    (familyBudget_nonnegative hw0 hw1 K extent hK ids hids c qs)
    (Q'.le_of_lt (lower_positive hw0 hw1)) (by decide)
    (CReal.ofNat_le_ofNat (Nat.zero_le qs.length))
    (rate_nonnegative hw0 hw1) (rate_lt_one hw0 hw1) hnorm hpair herror
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (qmul (Q'.eqv_refl _) (pin F F)))

/-- Each retained mass is compared with the same original partition before
summing the nonnegative coefficient squares. No volume floor is used. -/
theorem partition_coefficient_budget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (c : Z4Plaq → Q') :
    quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) *
      listQSum (fun p => c p*c p) qs ≤ upper w*familyBudget w K extent ids c qs := by
  let Z := quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids)
  let d := fun p => quaternionHaar (B extent) (restHeat w K extent ids p)
  have h := Z4FiniteCylinderQuadraticStability.listQSum_mono
    (fun p => Z*(c p*c p)) (fun p => upper w*(c p*c p*d p)) qs (by
      intro p _
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ (c p*c p)
        (full_mass_le_upper_rest_mass hw0 hw1 K extent hK ids hids hnodup p)
        (SumOfSquares.q_mul_self_nonneg (c p))
      exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
        (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.var 1)))
        (by decide) (fun | 0 => upper w | 1 => d p | _ => c p))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (listQSum_mul_left Z _ qs))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (listQSum_mul_left (upper w) _ qs)))

/-- A concrete volume- and family-size-independent lower bound for every
finite signed fundamental plaquette span in the FULL original selected action.
The positive constant depends only on nome; cofinal cutoff is a hypothesis.
This bounds a coefficient-square norm, NOT the spatial variance or an OS gap. -/
theorem family_partition_coercivity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (qs : List Z4Plaq) (hn : qs.Nodup)
    (hqs : ∀ p, p ∈ qs → p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q') :
    lower w * quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) *
      listQSum (fun p => c p*c p) qs ≤
      (600*upper w) * sourceEnergy w K extent ids c qs := by
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (lower w)
    (partition_coefficient_budget hw0 hw1 K extent hK ids hids hnodup qs c)
    (Q'.le_of_lt (lower_positive hw0 hw1))
  have he : lower w*(upper w*familyBudget w K extent ids c qs) ≈
      upper w*(lower w*familyBudget w K extent ids c qs) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => lower w | 1 => upper w | _ => familyBudget w K extent ids c qs)
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (upper w)
    (family_coercivity hw0 hw1 K extent hK ids hids hnodup qs hn hqs c)
    (Q'.le_of_lt (upper_positive hw0))
  have hfinish : upper w*(600*sourceEnergy w K extent ids c qs) ≈
      (600*upper w)*sourceEnergy w K extent ids c qs :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 600) (.var 1)))
      (.mul (.mul (.const 600) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => upper w | _ => sourceEnergy w K extent ids c qs)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hfinish))))

#print axioms dualFamily
#print axioms sourceSpan
#print axioms familyBudget
#print axioms sourceEnergy
#print axioms familyError
#print axioms sourceSpan_supported
#print axioms dualFamily_supported
#print axioms coefficientAt_map
#print axioms familyBudget_nonnegative
#print axioms sourceEnergy_nonnegative
#print axioms family_norm_bound
#print axioms family_pairing
#print axioms family_error_bound
#print axioms family_coercivity
#print axioms partition_coefficient_budget
#print axioms family_partition_coercivity
#print axioms pair_sum_left
#print axioms error_young

end YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
