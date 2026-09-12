/-
# The original signed slab quadratic is an explicit reflected-square Haar sum

Syntactic support is proved for the actual representation columns, all
interface factors and every channel in the finite square tree. This
licenses removing common padding under the ORIGINAL 116-link Haar law.

The resulting equality retains the original signed boundary coefficients,
all cutoff spins and all heat coefficients. For nonnegative w the stored
channel weights are nonnegative. Individual reflected-square Haar values
are not declared nonnegative here: half-carrier factorization remains open.
-/

import YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
import YMGap.Continuum.SU2QuaternionPolynomialGramPositivity

namespace YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionPolynomialGramPositivity
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

private theorem support_zero (blocks : Nat) : SupportedQuaternionBlocks blocks polyZero :=
  fun _ h => False.elim (List.not_mem_nil h)

private theorem support_one (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

private theorem support_var {blocks i : Nat} (hi : i < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar i) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem support_add {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_neg {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_smul {blocks : Nat} (a : Q') {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_sum {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => support_zero blocks
  | a :: xs => support_add (h a) (support_sum f h xs)

private theorem support_fold {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (xs.foldr (fun a p => polyMul (f a) p) polyOne)
  | [] => support_one blocks
  | a :: xs => supported_polyMul (h a) (support_fold f h xs)

private abbrev CSupported (blocks : Nat) (p : ComplexRatPoly) := PolyTensorSupported blocks 0 p

private theorem complex_zero_support (blocks : Nat) : CSupported blocks complexRatPolyZero :=
  ⟨support_zero blocks, support_zero blocks⟩
private theorem complex_one_support (blocks : Nat) : CSupported blocks complexRatPolyOne :=
  ⟨support_one blocks, support_zero blocks⟩

private theorem complex_add_support {blocks : Nat} {p q : ComplexRatPoly}
    (hp : CSupported blocks p) (hq : CSupported blocks q) : CSupported blocks (complexRatPolyAdd p q) :=
  ⟨support_add hp.1 hq.1, support_add hp.2 hq.2⟩

private theorem complex_mul_support {blocks : Nat} {p q : ComplexRatPoly}
    (hp : CSupported blocks p) (hq : CSupported blocks q) : CSupported blocks (complexRatPolyMul p q) :=
  ⟨support_add (supported_polyMul hp.1 hq.1) (support_neg (supported_polyMul hp.2 hq.2)),
    support_add (supported_polyMul hp.1 hq.2) (supported_polyMul hp.2 hq.1)⟩

private theorem tensor_add_support {blocks : Nat} : ∀ {n : Nat} {p q : PolyTensor n},
    PolyTensorSupported blocks n p → PolyTensorSupported blocks n q →
      PolyTensorSupported blocks n (polyTensorAdd n p q)
  | 0, _, _, hp, hq => complex_add_support hp hq
  | _ + 1, _, _, hp, hq => fun b => tensor_add_support (hp b) (hq b)

private theorem tensor_scale_support {blocks : Nat} {a : ComplexRatPoly} (ha : CSupported blocks a) :
    ∀ {n : Nat} {p : PolyTensor n}, PolyTensorSupported blocks n p →
      PolyTensorSupported blocks n (polyTensorScale n a p)
  | 0, _, h => complex_mul_support ha h
  | _ + 1, _, h => fun b => tensor_scale_support ha (h b)

private theorem matrix_support {blocks : Nat} {M : Bool → Bool → ComplexRatPoly}
    (hM : ∀ i j, CSupported blocks (M i j)) :
    ∀ {n : Nat} {p : PolyTensor n}, PolyTensorSupported blocks n p →
      PolyTensorSupported blocks n (polyMatrixAction n M p)
  | 0, _, h => h
  | _ + 1, _, h => fun b =>
      tensor_add_support (tensor_scale_support (hM b false) (matrix_support hM (h false)))
        (tensor_scale_support (hM b true) (matrix_support hM (h true)))

private theorem embed_support {blocks : Nat} : ∀ n {f : Nat → ComplexRatPoly},
    (∀ k, CSupported blocks (f k)) → PolyTensorSupported blocks n (polyEmbed n f)
  | 0, _, h => h 0
  | n + 1, _, h => by
      intro b
      cases b
      · exact embed_support n h
      · exact embed_support n (fun k => h (k + 1))

private theorem basis_support (blocks k j : Nat) : CSupported blocks (polynomialBasis k j) := by
  unfold polynomialBasis
  split
  · exact complex_one_support blocks
  · exact complex_zero_support blocks

private theorem fundamental_link_support (extent : Nat) (link : Z4Link) (row column : Bool) :
    CSupported (boundaryCompleteSlabLinks extent).length
      (fundamentalMatrixCoefficient (asRepresentationQuaternion (correctedSlabLinkPolynomial extent link)) row column) := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hl]
    have hi := List.idxOf_lt_length_of_mem hl
    cases row <;> cases column
    · exact ⟨support_var (by omega), support_var (by omega)⟩
    · exact ⟨support_var (by omega), support_var (by omega)⟩
    · exact ⟨support_neg (support_var (by omega)), support_var (by omega)⟩
    · exact ⟨support_var (by omega), support_neg (support_var (by omega))⟩
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    cases row <;> cases column
    · exact complex_one_support _
    · exact complex_zero_support _
    · exact ⟨support_neg (support_zero _), support_zero _⟩
    · exact ⟨support_one _, support_neg (support_zero _)⟩

theorem spatialColumn_support (extent : Nat) (link : Z4Link) (n k : Nat) :
    PolyTensorSupported (boundaryCompleteSlabLinks extent).length n
      (polynomialColumn (asRepresentationQuaternion (correctedSlabLinkPolynomial extent link)) n k) :=
  matrix_support (fundamental_link_support extent link) (embed_support n (basis_support _ k))

private theorem inner_support {blocks : Nat} : ∀ {n : Nat} {p q : PolyTensor n},
    PolyTensorSupported blocks n p → PolyTensorSupported blocks n q →
      CSupported blocks (polyTensorInner n p q)
  | 0, _, _, hp, hq => complex_mul_support ⟨hp.1, support_neg hp.2⟩ hq
  | _ + 1, _, _, hp, hq => complex_add_support (inner_support (hp false) (hq false))
      (inner_support (hp true) (hq true))

private theorem complex_sum_support {blocks : Nat} (f : Nat → ComplexRatPoly)
    (h : ∀ k, CSupported blocks (f k)) : ∀ n, CSupported blocks (polynomialSum n f)
  | 0 => complex_zero_support blocks
  | n + 1 => complex_add_support (complex_sum_support f h n) (h n)

theorem spatialGram_support (extent : Nat) (link : Z4Link) (n : Nat) :
    CSupported (boundaryCompleteSlabLinks extent).length (reflectedSpatialLinkGram extent link n) :=
  complex_sum_support _ (fun k =>
    let h := inner_support (spatialColumn_support extent _ n k) (spatialColumn_support extent _ n k)
    ⟨support_smul _ h.1, support_smul _ h.2⟩) (n + 1)

/-- Every stored channel has syntactic support on the stated carrier. -/
def SquareTreeSupported (blocks : Nat) : SquareTree → Prop
  | .zero => True
  | .term _ p => SupportedQuaternionBlocks blocks p
  | .add p q => SquareTreeSupported blocks p ∧ SquareTreeSupported blocks q

theorem squareTree_eval_support (extent : Nat) : ∀ t : SquareTree,
    SquareTreeSupported (boundaryCompleteSlabLinks extent).length t →
      SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (t.eval extent)
  | .zero, _ => support_zero _
  | .term w p, h => support_smul w (supported_polyMul (reflectCorrectedSlabPolynomial_support extent p) h)
  | .add p q, h => support_add (squareTree_eval_support extent p h.1) (squareTree_eval_support extent q h.2)

private theorem tree_scale_support {blocks : Nat} (s : Q') : ∀ t : SquareTree,
    SquareTreeSupported blocks t → SquareTreeSupported blocks (t.scale s)
  | .zero, _ => True.intro
  | .term _ _, h => h
  | .add p q, h => ⟨tree_scale_support s p h.1, tree_scale_support s q h.2⟩

private theorem tree_multiplyTerm_support {blocks : Nat} (s : Q') (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) : ∀ t : SquareTree,
      SquareTreeSupported blocks t → SquareTreeSupported blocks (t.multiplyTerm s p)
  | .zero, _ => True.intro
  | .term _ _, h => supported_polyMul hp h
  | .add q r, h => ⟨tree_multiplyTerm_support s p hp q h.1, tree_multiplyTerm_support s p hp r h.2⟩

theorem squareTree_product_support {blocks : Nat} : ∀ p q : SquareTree,
    SquareTreeSupported blocks p → SquareTreeSupported blocks q → SquareTreeSupported blocks (p.product q)
  | .zero, _, _, _ => True.intro
  | .term s p, q, hp, hq => tree_multiplyTerm_support s p hp q hq
  | .add p q, r, hp, hr => ⟨squareTree_product_support p r hp.1 hr, squareTree_product_support q r hp.2 hr⟩

private theorem tree_sum_support {A : Type} {blocks : Nat} (f : A → SquareTree)
    (h : ∀ a, SquareTreeSupported blocks (f a)) : ∀ xs : List A, SquareTreeSupported blocks (SquareTree.sum f xs)
  | [] => True.intro
  | a :: xs => ⟨h a, tree_sum_support f h xs⟩

private theorem tree_prefix_support {blocks : Nat} (f : Nat → SquareTree)
    (h : ∀ k, SquareTreeSupported blocks (f k)) : ∀ n, SquareTreeSupported blocks (SquareTree.prefixSum f n)
  | 0 => True.intro
  | n + 1 => ⟨tree_prefix_support f h n, h n⟩

private theorem tensorSquares_support {blocks : Nat} : ∀ {n : Nat} {x : PolyTensor n},
    PolyTensorSupported blocks n x → SquareTreeSupported blocks (tensorSquares n x)
  | 0, _, h => h
  | _ + 1, _, h => ⟨tensorSquares_support (h false), tensorSquares_support (h true)⟩

theorem spatialGramSquares_support (extent : Nat) (link : Z4Link) (n : Nat) :
    SquareTreeSupported (boundaryCompleteSlabLinks extent).length
      (gramSquares (asRepresentationQuaternion (correctedSlabLinkPolynomial extent link)) n) :=
  tree_prefix_support _ (fun _ => tree_scale_support _ _ (tensorSquares_support (spatialColumn_support extent link n _))) (n + 1)

theorem faceHeatSquares_support (w : Q') (K id : Nat) : SquareTreeSupported 116 (faceHeatSquares w K id) := by
  have h := tree_sum_support _ (fun spin => tree_scale_support (coeffAt (heatKernelPacket K w) spin) _ (spatialGramSquares_support 1
    (faceLinkA (slabPlaquetteAt 1 id)) spin)) (List.range (K + 1))
  rw [correctedSlabLinks_extent_one_length] at h
  exact h

private theorem tree_fold_support (w : Q') (K : Nat) : ∀ ids : List Nat,
    SquareTreeSupported 116 (ids.foldr (fun id t => (faceHeatSquares w K id).product t) (.term 1 polyOne))
  | [] => support_one 116
  | id :: ids => squareTree_product_support _ _ (faceHeatSquares_support w K id) (tree_fold_support w K ids)

theorem interfaceSquares_support (w : Q') (K : Nat) : SquareTreeSupported 116 (interfaceSquares w K) :=
  tree_fold_support w K _

theorem observableSquares_support (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    SquareTreeSupported 116 (observableSquares w K c) :=
  squareTree_product_support _ _ (lowerObservable_support w K c) (interfaceSquares_support w K)

theorem spatialGramInterface_support (w : Q') (K : Nat) :
    SupportedQuaternionBlocks 116 (spatialGramInterface w K) := by
  apply support_fold
  intro id
  apply support_sum
  intro spin
  apply support_smul
  have h := (spatialGram_support 1 (faceLinkA (slabPlaquetteAt 1 id)) spin).1
  rw [correctedSlabLinks_extent_one_length] at h
  exact h

/-- The original signed finite-volume quadratic, not a replacement law,
is exactly the Haar value of the explicit global reflected-square tree.
No positivity of those Haar values is assumed or concluded. -/
theorem exact_quadratic_eq_squareTreeHaar (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    (exactSlabAllCutoffQuadratic w K c).eqv
      (quaternionHaar 116 ((observableSquares w K c).eval 1)) := by
  have ht := reflectCorrectedSlabPolynomial_support 1 (lowerObservable w K c)
  have hs := squareTree_eval_support 1 (observableSquares w K c)
  rw [correctedSlabLinks_extent_one_length] at ht hs
  exact Q'.eqv_trans _ _ _ (exact_quadratic_eq_spatialGramHaar w K c)
    ((observableSquares_image w K c).haar
      (supported_polyMul (lowerObservable_support w K c) (supported_polyMul (spatialGramInterface_support w K) ht))
      (hs (observableSquares_support w K c)))

end YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.spatialColumn_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.spatialGram_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.SquareTreeSupported
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.squareTree_eval_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.squareTree_product_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.spatialGramSquares_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.faceHeatSquares_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.interfaceSquares_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.observableSquares_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.spatialGramInterface_support
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm.exact_quadratic_eq_squareTreeHaar
