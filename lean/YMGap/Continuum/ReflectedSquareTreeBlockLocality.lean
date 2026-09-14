/-
# Explicit block dependence of actual representation-channel trees

The original complex tensor recursion and Gram columns preserve any named
block-locality predicate. Finite tree scaling, sums and products preserve
the same predicate. These are syntactic statements about each retained
channel, not assumptions of probabilistic independence or positivity.
-/

import YMGap.Continuum.SU2QuaternionBlockLocality

namespace YMGap.Continuum.ReflectedSquareTreeBlockLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram

def ComplexLocal (blocks : Nat) (allowed : Nat → Prop) (p : ComplexRatPoly) : Prop :=
  BlockLocal blocks allowed p.1 ∧ BlockLocal blocks allowed p.2

def TensorLocal (blocks : Nat) (allowed : Nat → Prop) : (n : Nat) → PolyTensor n → Prop
  | 0, p => ComplexLocal blocks allowed p
  | n + 1, p => ∀ b, TensorLocal blocks allowed n (p b)

def TreeLocal (blocks : Nat) (allowed : Nat → Prop) : SquareTree → Prop
  | .zero => True
  | .term _ p => BlockLocal blocks allowed p
  | .add s t => TreeLocal blocks allowed s ∧ TreeLocal blocks allowed t

variable {blocks : Nat} {allowed : Nat → Prop}

private theorem complex_zero : ComplexLocal blocks allowed complexRatPolyZero :=
  ⟨BlockLocal.zero _ _, BlockLocal.zero _ _⟩

private theorem complex_one : ComplexLocal blocks allowed complexRatPolyOne :=
  ⟨BlockLocal.one _ _, BlockLocal.zero _ _⟩

private theorem complex_add {p q : ComplexRatPoly} (hp : ComplexLocal blocks allowed p)
    (hq : ComplexLocal blocks allowed q) : ComplexLocal blocks allowed (complexRatPolyAdd p q) :=
  ⟨hp.1.add hq.1, hp.2.add hq.2⟩

private theorem complex_mul {p q : ComplexRatPoly} (hp : ComplexLocal blocks allowed p)
    (hq : ComplexLocal blocks allowed q) : ComplexLocal blocks allowed (complexRatPolyMul p q) :=
  ⟨(hp.1.mul hq.1).add (hp.2.mul hq.2).neg, (hp.1.mul hq.2).add (hp.2.mul hq.1)⟩

private theorem tensor_add : ∀ {n : Nat} {p q : PolyTensor n},
    TensorLocal blocks allowed n p → TensorLocal blocks allowed n q →
      TensorLocal blocks allowed n (polyTensorAdd n p q)
  | 0, _, _, hp, hq => complex_add hp hq
  | _ + 1, _, _, hp, hq => fun b => tensor_add (hp b) (hq b)

private theorem tensor_scale {a : ComplexRatPoly} (ha : ComplexLocal blocks allowed a) :
    ∀ {n : Nat} {p : PolyTensor n}, TensorLocal blocks allowed n p →
      TensorLocal blocks allowed n (polyTensorScale n a p)
  | 0, _, h => complex_mul ha h
  | _ + 1, _, h => fun b => tensor_scale ha (h b)

theorem matrix_local {M : Bool → Bool → ComplexRatPoly} (hM : ∀ i j, ComplexLocal blocks allowed (M i j)) :
    ∀ {n : Nat} {p : PolyTensor n}, TensorLocal blocks allowed n p →
      TensorLocal blocks allowed n (polyMatrixAction n M p)
  | 0, _, h => h
  | _ + 1, _, h => fun b => tensor_add (tensor_scale (hM b false) (matrix_local hM (h false)))
      (tensor_scale (hM b true) (matrix_local hM (h true)))

private theorem embed_local : ∀ n {f : Nat → ComplexRatPoly},
    (∀ k, ComplexLocal blocks allowed (f k)) → TensorLocal blocks allowed n (polyEmbed n f)
  | 0, _, h => h 0
  | n + 1, _, h => by
      intro b
      cases b
      · exact embed_local n h
      · exact embed_local n (fun k => h (k + 1))

private theorem basis_local (k j : Nat) : ComplexLocal blocks allowed (polynomialBasis k j) := by
  unfold polynomialBasis
  split
  · exact complex_one
  · exact complex_zero

theorem column_local (q : RationalQuaternionRatPoly.RatPolyQuaternion)
    (hr : BlockLocal blocks allowed q.r) (hi : BlockLocal blocks allowed q.i)
    (hj : BlockLocal blocks allowed q.j) (hk : BlockLocal blocks allowed q.k) (n k : Nat) :
    TensorLocal blocks allowed n (polynomialColumn q n k) := by
  apply matrix_local
  · intro row col
    cases row <;> cases col
    · exact ⟨hr, hi⟩
    · exact ⟨hj, hk⟩
    · exact ⟨hj.neg, hk⟩
    · exact ⟨hr, hi.neg⟩
  · exact embed_local n (basis_local k)

theorem TreeLocal.scale (s : Q') : ∀ {t : SquareTree},
    TreeLocal blocks allowed t → TreeLocal blocks allowed (t.scale s)
  | .zero, _ => True.intro
  | .term _ _, h => h
  | .add _ _, h => ⟨h.1.scale s, h.2.scale s⟩

theorem TreeLocal.multiplyTerm (s : Q') {p : RatPoly} (hp : BlockLocal blocks allowed p) : ∀ {t : SquareTree},
    TreeLocal blocks allowed t → TreeLocal blocks allowed (t.multiplyTerm s p)
  | .zero, _ => True.intro
  | .term _ _, h => hp.mul h
  | .add _ _, h => ⟨h.1.multiplyTerm s hp, h.2.multiplyTerm s hp⟩

theorem TreeLocal.product : ∀ {s t : SquareTree}, TreeLocal blocks allowed s → TreeLocal blocks allowed t →
    TreeLocal blocks allowed (s.product t)
  | .zero, _, _, _ => True.intro
  | .term a _, _, hs, ht => ht.multiplyTerm a hs
  | .add _ _, _, hs, ht => ⟨hs.1.product ht, hs.2.product ht⟩

theorem TreeLocal.sum {A : Type} (f : A → SquareTree) : ∀ xs : List A,
    (∀ a, a ∈ xs → TreeLocal blocks allowed (f a)) → TreeLocal blocks allowed (SquareTree.sum f xs)
  | [], _ => True.intro
  | a :: xs, h => ⟨h a List.mem_cons_self, TreeLocal.sum f xs (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

theorem TreeLocal.prefix (f : Nat → SquareTree) (h : ∀ k, TreeLocal blocks allowed (f k)) :
    ∀ n, TreeLocal blocks allowed (SquareTree.prefixSum f n)
  | 0 => True.intro
  | n + 1 => ⟨TreeLocal.prefix f h n, h n⟩

theorem tensor_tree : ∀ {n : Nat} {x : PolyTensor n},
    TensorLocal blocks allowed n x → TreeLocal blocks allowed (tensorSquares n x)
  | 0, _, h => h
  | _ + 1, _, h => ⟨tensor_tree (h false), tensor_tree (h true)⟩

/-- Every original symmetric-power degree, not just the selected degree one. -/
theorem gram_local (q : RationalQuaternionRatPoly.RatPolyQuaternion)
    (hr : BlockLocal blocks allowed q.r) (hi : BlockLocal blocks allowed q.i)
    (hj : BlockLocal blocks allowed q.j) (hk : BlockLocal blocks allowed q.k) (n : Nat) :
    TreeLocal blocks allowed (gramSquares q n) :=
  TreeLocal.prefix _ (fun k => (tensor_tree (column_local q hr hi hj hk n k)).scale _) (n + 1)

end YMGap.Continuum.ReflectedSquareTreeBlockLocality

#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.matrix_local
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.column_local
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.TreeLocal.scale
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.TreeLocal.multiplyTerm
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.TreeLocal.product
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.TreeLocal.sum
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.TreeLocal.prefix
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.tensor_tree
#print axioms YMGap.Continuum.ReflectedSquareTreeBlockLocality.gram_local
