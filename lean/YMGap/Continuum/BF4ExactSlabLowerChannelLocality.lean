/-
# Literal lower-half locality of the original reflected-square channels

Every lower plaquette uses only lower links. The original signed observable
therefore uses only lower blocks. Actual representation columns of crossing
faces use their literal lower spatial links, and the finite square-tree
operations preserve that dependence, including all shared-link products.

No half-locality certificate is assumed for the final observable tree.
This discharges the geometric premise needed by the reflected Haar square law.
-/

import YMGap.Continuum.BF4ExactSlabLowerHaarFactorization

namespace YMGap.Continuum.BF4ExactSlabLowerChannelLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

private structure LowerQuaternion (half : Nat) (p : PolyQuaternion) : Prop where
  scalar : LowerLocal half p.scalar
  iPart : LowerLocal half p.iPart
  jPart : LowerLocal half p.jPart
  kPart : LowerLocal half p.kPart

private theorem quaternion_one (half : Nat) : LowerQuaternion half PolyQuaternion.one :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _, BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem LowerQuaternion.conj {half : Nat} {p : PolyQuaternion} (h : LowerQuaternion half p) :
    LowerQuaternion half (PolyQuaternion.conj p) := ⟨h.scalar, h.iPart.neg, h.jPart.neg, h.kPart.neg⟩

private theorem LowerQuaternion.mul {half : Nat} {p q : PolyQuaternion}
    (hp : LowerQuaternion half p) (hq : LowerQuaternion half q) : LowerQuaternion half (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply BlockLocal.add | apply BlockLocal.neg | apply BlockLocal.mul

private theorem lower_link {half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks (centralExtent half)) (hs : linkHalfSide half link = .lower) :
    LowerQuaternion half (correctedSlabLinkPolynomial (centralExtent half) link) := by
  have hc (c : Nat) (h : c < 4) : LowerLocal half
      (polyVar (4 * (boundaryCompleteSlabLinks (centralExtent half)).idxOf link + c)) := by
    apply BlockLocal.coordinate
    unfold LowerBlock
    rw [show (4 * (boundaryCompleteSlabLinks (centralExtent half)).idxOf link + c) / 4 =
      (boundaryCompleteSlabLinks (centralExtent half)).idxOf link by omega, correctedSlabLinkAt_idxOf hl]
    exact hs
  rw [correctedSlabLinkPolynomial_of_mem hl]
  exact ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)⟩

theorem lower_face_link {half : Nat} {face : Z4Plaq} {link : Z4Link}
    (hf : plaquetteHalfSide half face = .lower) (hi : link ∈ edgesOf face) :
    linkHalfSide half link = .lower := by
  cases hs : linkHalfSide half link with
  | lower => rfl
  | upper => exact False.elim ((upper_link_incident_face_ne_lower hs hi) hf)
  | fixed => have hh := fixed_link_incident_face_fixed hs hi; rw [hf] at hh; cases hh

private theorem lower_plaquette {half : Nat} {face : Z4Plaq}
    (hp : face ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hf : plaquetteHalfSide half face = .lower) :
    LowerQuaternion half (correctedSlabPlaquettePolynomial (centralExtent half) face) := by
  have hl (link : Z4Link) (hi : link ∈ edgesOf face) :
      LowerQuaternion half (correctedSlabLinkPolynomial (centralExtent half) link) :=
    lower_link ((mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨face, hp, hi⟩) (lower_face_link hf hi)
  exact (((((quaternion_one half).mul (hl (faceLinkA face) (by simp [faceLinkA, edgesOf]))).mul
    (hl (faceLinkB face) (by simp [faceLinkB, edgesOf]))).mul
      (hl (faceLinkC face) (by simp [faceLinkC, edgesOf])).conj).mul
        (hl (faceLinkD face) (by simp [faceLinkD, edgesOf])).conj)

theorem lowerObservable_local (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    LowerLocal 0 (lowerObservable w K c) := by
  apply BlockLocal.finiteSum
  intro state _
  apply BlockLocal.smul
  rw [lowerPolynomial_eq_fold]
  apply BlockLocal.fold
  intro id hi
  apply BlockLocal.smul
  exact (lower_plaquette (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1)
    (mem_centralLowerFaceIds.mp hi).2).scalar.character (state id)

private abbrev LowerComplex (half : Nat) (z : ComplexRatPoly) :=
  LowerLocal half z.1 ∧ LowerLocal half z.2

private theorem complex_zero (half : Nat) : LowerComplex half complexRatPolyZero :=
  ⟨BlockLocal.zero _ _, BlockLocal.zero _ _⟩
private theorem complex_one (half : Nat) : LowerComplex half complexRatPolyOne :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _⟩
private theorem complex_add {half : Nat} {p q : ComplexRatPoly} (hp : LowerComplex half p) (hq : LowerComplex half q) :
    LowerComplex half (complexRatPolyAdd p q) := ⟨hp.1.add hq.1, hp.2.add hq.2⟩
private theorem complex_mul {half : Nat} {p q : ComplexRatPoly} (hp : LowerComplex half p) (hq : LowerComplex half q) :
    LowerComplex half (complexRatPolyMul p q) :=
  ⟨(hp.1.mul hq.1).add (hp.2.mul hq.2).neg, (hp.1.mul hq.2).add (hp.2.mul hq.1)⟩

def LowerTensor (half : Nat) : (n : Nat) → PolyTensor n → Prop
  | 0, p => LowerComplex half p
  | n + 1, p => ∀ b, LowerTensor half n (p b)

private theorem tensor_add {half : Nat} : ∀ {n : Nat} {p q : PolyTensor n},
    LowerTensor half n p → LowerTensor half n q → LowerTensor half n (polyTensorAdd n p q)
  | 0, _, _, hp, hq => complex_add hp hq
  | _ + 1, _, _, hp, hq => fun b => tensor_add (hp b) (hq b)

private theorem tensor_scale {half : Nat} {a : ComplexRatPoly} (ha : LowerComplex half a) :
    ∀ {n : Nat} {p : PolyTensor n}, LowerTensor half n p → LowerTensor half n (polyTensorScale n a p)
  | 0, _, h => complex_mul ha h
  | _ + 1, _, h => fun b => tensor_scale ha (h b)

private theorem matrix_local {half : Nat} {M : Bool → Bool → ComplexRatPoly}
    (hM : ∀ i j, LowerComplex half (M i j)) :
    ∀ {n : Nat} {p : PolyTensor n}, LowerTensor half n p → LowerTensor half n (polyMatrixAction n M p)
  | 0, _, h => h
  | _ + 1, _, h => fun b => tensor_add (tensor_scale (hM b false) (matrix_local hM (h false)))
      (tensor_scale (hM b true) (matrix_local hM (h true)))

private theorem embed_local {half : Nat} : ∀ n {f : Nat → ComplexRatPoly},
    (∀ k, LowerComplex half (f k)) → LowerTensor half n (polyEmbed n f)
  | 0, _, h => h 0
  | n + 1, _, h => by
      intro b
      cases b
      · exact embed_local n h
      · exact embed_local n (fun k => h (k + 1))

private theorem basis_local (half k j : Nat) : LowerComplex half (polynomialBasis k j) := by
  unfold polynomialBasis
  split
  · exact complex_one half
  · exact complex_zero half

theorem lower_column {half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks (centralExtent half)) (hs : linkHalfSide half link = .lower) (n k : Nat) :
    LowerTensor half n (polynomialColumn
      (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half) link)) n k) := by
  apply matrix_local
  · have h := lower_link hl hs
    intro row col
    cases row <;> cases col
    · exact ⟨h.scalar, h.iPart⟩
    · exact ⟨h.jPart, h.kPart⟩
    · exact ⟨h.jPart.neg, h.kPart⟩
    · exact ⟨h.scalar, h.iPart.neg⟩
  · exact embed_local n (basis_local half k)

def LowerSquareTree (half : Nat) : SquareTree → Prop
  | .zero => True
  | .term _ p => LowerLocal half p
  | .add p q => LowerSquareTree half p ∧ LowerSquareTree half q

private theorem tree_scale {half : Nat} (s : Q') : ∀ t : SquareTree,
    LowerSquareTree half t → LowerSquareTree half (t.scale s)
  | .zero, _ => True.intro
  | .term _ _, h => h
  | .add p q, h => ⟨tree_scale s p h.1, tree_scale s q h.2⟩

private theorem tree_term_product {half : Nat} (s : Q') {p : RatPoly} (hp : LowerLocal half p) : ∀ t : SquareTree,
    LowerSquareTree half t → LowerSquareTree half (t.multiplyTerm s p)
  | .zero, _ => True.intro
  | .term _ _, h => hp.mul h
  | .add q r, h => ⟨tree_term_product s hp q h.1, tree_term_product s hp r h.2⟩

theorem lower_tree_product {half : Nat} : ∀ p q : SquareTree,
    LowerSquareTree half p → LowerSquareTree half q → LowerSquareTree half (p.product q)
  | .zero, _, _, _ => True.intro
  | .term s _, q, hp, hq => tree_term_product s hp q hq
  | .add p q, r, hp, hr => ⟨lower_tree_product p r hp.1 hr, lower_tree_product q r hp.2 hr⟩

private theorem tree_sum {A : Type} {half : Nat} (f : A → SquareTree) : ∀ xs : List A,
    (∀ a, a ∈ xs → LowerSquareTree half (f a)) → LowerSquareTree half (SquareTree.sum f xs)
  | [], _ => True.intro
  | a :: xs, h => ⟨h a List.mem_cons_self, tree_sum f xs (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

private theorem tree_prefix {half : Nat} (f : Nat → SquareTree) (h : ∀ k, LowerSquareTree half (f k)) :
    ∀ n, LowerSquareTree half (SquareTree.prefixSum f n)
  | 0 => True.intro
  | n + 1 => ⟨tree_prefix f h n, h n⟩

private theorem tensor_tree {half : Nat} : ∀ {n : Nat} {x : PolyTensor n},
    LowerTensor half n x → LowerSquareTree half (tensorSquares n x)
  | 0, _, h => h
  | _ + 1, _, h => ⟨tensor_tree (h false), tensor_tree (h true)⟩

theorem lower_gram_tree {half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks (centralExtent half)) (hs : linkHalfSide half link = .lower) (n : Nat) :
    LowerSquareTree half (gramSquares
      (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half) link)) n) :=
  tree_prefix _ (fun k => tree_scale _ _ (tensor_tree (lower_column hl hs n k))) (n + 1)

theorem faceHeatSquares_lower (w : Q') (K : Nat) {id : Nat} (hi : id ∈ centralFixedFaceIds 0) :
    LowerSquareTree 0 (faceHeatSquares w K id) := by
  apply tree_sum
  intro spin _
  apply tree_scale
  apply lower_gram_tree
  · exact faceLinkA_physical (slabPlaquetteAt_mem (mem_centralFixedFaceIds.mp hi).1)
  · exact (crossing_face_path_sides (mem_centralFixedFaceIds.mp hi).2).1

private theorem tree_fold (w : Q') (K : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ centralFixedFaceIds 0) →
      LowerSquareTree 0 (ids.foldr (fun id t => (faceHeatSquares w K id).product t) (.term 1 polyOne))
  | [], _ => BlockLocal.one _ _
  | id :: ids, h => lower_tree_product _ _ (faceHeatSquares_lower w K (h id List.mem_cons_self))
      (tree_fold w K ids (fun j hj => h j (List.mem_cons_of_mem id hj)))

theorem interfaceSquares_lower (w : Q') (K : Nat) : LowerSquareTree 0 (interfaceSquares w K) :=
  tree_fold w K _ (fun _ h => h)

/-- Every channel of the ORIGINAL global tree is lower-local, with no
assumed semantic certificate and no restriction on signed coefficients. -/
theorem observableSquares_lower (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    LowerSquareTree 0 (observableSquares w K c) :=
  lower_tree_product _ _ (lowerObservable_local w K c) (interfaceSquares_lower w K)

end YMGap.Continuum.BF4ExactSlabLowerChannelLocality

#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.lower_face_link
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.lowerObservable_local
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.LowerTensor
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.lower_column
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.LowerSquareTree
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.lower_tree_product
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.lower_gram_tree
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.faceHeatSquares_lower
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.interfaceSquares_lower
#print axioms YMGap.Continuum.BF4ExactSlabLowerChannelLocality.observableSquares_lower
