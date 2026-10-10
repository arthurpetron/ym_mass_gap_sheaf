/-
# The actual three-dimensional adjoint matrix of completed quaternions

The nine entries are homogeneous quadratic rational polynomials. Their raw
Hamilton product law is certified before restricting to the unit sphere.
Each completed entry is evaluated on the EXISTING Point coordinates; supplied
Cauchy rows retain an explicit inner regularity witness. The image group below
has literal matrices as values and uses actual matrix multiplication and
transpose. It is not an identification with compact SO(3), a faithful-action
claim, or a claim about the interacting Yang--Mills transfer.
-/

import YMGap.RepTheory.RationalQuaternionCompletedMatrix
import YMGap.RepTheory.RationalQuaternionCompletedSignQuotient
import YMGap.RepTheory.ConstructiveRepresentationDescent
import YMGap.Constructive.CRealInnerMultiplication
import YMGap.Continuum.QuaternionSignQuotientRepresentedHaar

namespace YMGap.RepTheory.RationalQuaternionCompletedAdjointMatrix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternionCoordinateCompletion
open YMGap.RepTheory.RationalQuaternionCompletedSignQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly)
open YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation (quaternionCoordinates)
open YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation
  (pointEval pointEval_rowPolynomialEval rowPolynomialEval_approx)
open YMGap.Continuum.QuaternionRepresentedPolynomialHaar (evaluate_polynomial)
open YMGap.Continuum.QuaternionSignQuotientRepresentedHaar (chiTwoPolynomial)

local infix:50 " ≈ " => Q'.eqv

abbrev Matrix := Fin 3 → Fin 3 → RC
abbrev RawMatrix := Fin 3 → Fin 3 → Q'

/-- One algebraic expression, instantiated in Q', CReal and RC. -/
private def quadraticEntry {α : Type} (add mul : α → α → α) (neg : α → α)
    (two r u v w : α) (row column : Fin 3) : α :=
  let sq (x : α) := mul x x
  match row.val, column.val with
  | 0, 0 => add (add (add (sq r) (sq u)) (neg (sq v))) (neg (sq w))
  | 0, 1 => mul two (add (mul u v) (neg (mul r w)))
  | 0, _ => mul two (add (mul u w) (mul r v))
  | 1, 0 => mul two (add (mul u v) (mul r w))
  | 1, 1 => add (add (add (sq r) (neg (sq u))) (sq v)) (neg (sq w))
  | 1, _ => mul two (add (mul v w) (neg (mul r u)))
  | _, 0 => mul two (add (mul u w) (neg (mul r v)))
  | _, 1 => mul two (add (mul v w) (mul r u))
  | _, _ => add (add (add (sq r) (neg (sq u))) (neg (sq v))) (sq w)

/-- Standard adjoint conjugation on imaginary quaternion basis vectors.
The entries are all homogeneous quadratics, with the Hamilton orientation
`I*J=K`. No normalization is used in this raw definition. -/
def rawEntry (q : RationalQuaternion) (row column : Fin 3) : Q' :=
  quadraticEntry (· + ·) (· * ·) Neg.neg 2 q.r q.i q.j q.k row column

def rawMatrix (q : RationalQuaternion) : RawMatrix := rawEntry q
def rawMatrixMul (A B : RawMatrix) : RawMatrix := fun i j =>
  A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j
def rawMatrixTranspose (A : RawMatrix) : RawMatrix := fun i j => A j i
def rawMatrixOne : RawMatrix := fun i j => if i == j then 1 else 0

private def fin3_all.{u} (P : Fin 3 → Sort u) (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ i, P i := by
  intro ⟨i, hi⟩
  cases i with
  | zero => exact h0
  | succ i =>
      cases i with
      | zero => exact h1
      | succ i =>
          cases i with
          | zero => exact h2
          | succ i => exact False.elim (by omega : False)

private abbrev PE := PolyExpr
private structure QuaternionExpr where
  r : PE
  i : PE
  j : PE
  k : PE

private def quaternionVar (base : Nat) : QuaternionExpr :=
  ⟨.var base,.var (base+1),.var (base+2),.var (base+3)⟩
private def quaternionConj (q : QuaternionExpr) : QuaternionExpr :=
  ⟨q.r,.neg q.i,.neg q.j,.neg q.k⟩
private def quaternionMul (q p : QuaternionExpr) : QuaternionExpr :=
  ⟨.add (.add (.mul q.r p.r) (.neg (.mul q.i p.i)))
      (.add (.neg (.mul q.j p.j)) (.neg (.mul q.k p.k))),
    .add (.add (.mul q.r p.i) (.mul q.i p.r))
      (.add (.mul q.j p.k) (.neg (.mul q.k p.j))),
    .add (.add (.mul q.r p.j) (.neg (.mul q.i p.k)))
      (.add (.mul q.j p.r) (.mul q.k p.i)),
    .add (.add (.mul q.r p.k) (.mul q.i p.j))
      (.add (.neg (.mul q.j p.i)) (.mul q.k p.r))⟩

private def quaternionEval (ρ : Nat → Q') (q : QuaternionExpr) : RationalQuaternion :=
  ⟨eval ρ q.r,eval ρ q.i,eval ρ q.j,eval ρ q.k⟩

private theorem quaternionEval_mul (ρ : Nat → Q') (q p : QuaternionExpr) :
    quaternionEval ρ (quaternionMul q p) =
      RationalQuaternion.mul (quaternionEval ρ q) (quaternionEval ρ p) := rfl

private theorem quaternionEval_conj (ρ : Nat → Q') (q : QuaternionExpr) :
    quaternionEval ρ (quaternionConj q) =
      RationalQuaternion.conj (quaternionEval ρ q) := rfl

private def exprEntry (q : QuaternionExpr) (i j : Fin 3) : PE :=
  quadraticEntry .add .mul .neg (.const 2) q.r q.i q.j q.k i j

private theorem exprEntry_eval (ρ : Nat → Q') (q : QuaternionExpr) (i j : Fin 3) :
    eval ρ (exprEntry q i j) = rawEntry (quaternionEval ρ q) i j := by
  have h : ∀ i j, eval ρ (exprEntry q i j) = rawEntry (quaternionEval ρ q) i j := by
    apply fin3_all
    all_goals apply fin3_all
    all_goals rfl
  exact h i j

private def exprDot (q p : QuaternionExpr) (i j : Fin 3) : PE :=
  .add (.add (.mul (exprEntry q i 0) (exprEntry p 0 j))
    (.mul (exprEntry q i 1) (exprEntry p 1 j)))
    (.mul (exprEntry q i 2) (exprEntry p 2 j))

private theorem exprDot_eval (ρ : Nat → Q') (q p : QuaternionExpr) (i j : Fin 3) :
    eval ρ (exprDot q p i j) =
      rawMatrixMul (rawMatrix (quaternionEval ρ q))
        (rawMatrix (quaternionEval ρ p)) i j := by
  change (eval ρ (exprEntry q i 0) * eval ρ (exprEntry p 0 j) +
    eval ρ (exprEntry q i 1) * eval ρ (exprEntry p 1 j)) +
    eval ρ (exprEntry q i 2) * eval ρ (exprEntry p 2 j) = _
  simp only [exprEntry_eval]
  rfl

private def qx : QuaternionExpr := quaternionVar 0
private def qy : QuaternionExpr := quaternionVar 4

private def exprBasis (j : Fin 3) : QuaternionExpr :=
  if j = 0 then ⟨.const 0,.const 1,.const 0,.const 0⟩
  else if j = 1 then ⟨.const 0,.const 0,.const 1,.const 0⟩
  else ⟨.const 0,.const 0,.const 0,.const 1⟩

private def rawBasis (j : Fin 3) : RationalQuaternion :=
  if j = 0 then RationalQuaternion.basisI
  else if j = 1 then RationalQuaternion.basisJ
  else RationalQuaternion.basisK

private def exprImag (q : QuaternionExpr) (i : Fin 3) : PE :=
  if i = 0 then q.i else if i = 1 then q.j else q.k

private def rawImag (q : RationalQuaternion) (i : Fin 3) : Q' :=
  if i = 0 then q.i else if i = 1 then q.j else q.k

private theorem exprImag_eval (ρ : Nat → Q') (q : QuaternionExpr) (i : Fin 3) :
    eval ρ (exprImag q i) = rawImag (quaternionEval ρ q) i := by
  have h : ∀ i, eval ρ (exprImag q i) = rawImag (quaternionEval ρ q) i := by
    apply fin3_all
    all_goals rfl
  exact h i

private theorem rawBasis_eval (ρ : Nat → Q') (j : Fin 3) :
    quaternionEval ρ (exprBasis j) = rawBasis j := by
  have h : ∀ j, quaternionEval ρ (exprBasis j) = rawBasis j := by
    apply fin3_all
    all_goals rfl
  exact h j
private def environment (q p : RationalQuaternion) : Nat → Q'
  | 0 => q.r | 1 => q.i | 2 => q.j | 3 => q.k
  | 4 => p.r | 5 => p.i | 6 => p.j | _ => p.k

private theorem rawMatrix_mul_normal : ∀ i j,
    normalize (exprEntry (quaternionMul qx qy) i j) =
      normalize (exprDot qx qy i j) := by
  apply fin3_all
  all_goals apply fin3_all
  all_goals decide

/-- Exact arbitrary-raw Hamilton law, not merely a unit-sphere assertion. -/
theorem rawMatrix_mul (q p : RationalQuaternion) :
    ∀ i j, rawMatrix (RationalQuaternion.mul q p) i j ≈
      rawMatrixMul (rawMatrix q) (rawMatrix p) i j := by
  intro i j
  have h := poly_identity_of_normal_eq
    (exprEntry (quaternionMul qx qy) i j) (exprDot qx qy i j)
    (rawMatrix_mul_normal i j) (environment q p)
  simp only [exprEntry_eval,exprDot_eval,quaternionEval_mul] at h
  change rawMatrix (RationalQuaternion.mul q p) i j ≈
    rawMatrixMul (rawMatrix q) (rawMatrix p) i j at h
  exact h

/-- The rational identity matrix is the adjoint of Hamilton one. -/
theorem rawMatrix_one : ∀ i j, rawMatrix RationalQuaternion.one i j ≈ rawMatrixOne i j := by
  apply fin3_all
  all_goals apply fin3_all
  all_goals
    dsimp [rawMatrix, rawEntry, quadraticEntry, rawMatrixOne, RationalQuaternion.one,
      RationalQuaternion.scalar]
    decide

theorem rawMatrix_negativeOne :
    ∀ i j, rawMatrix unitNegativeOne.val i j ≈ rawMatrixOne i j := by
  apply fin3_all
  all_goals apply fin3_all
  all_goals dsimp [rawMatrix, rawEntry, quadraticEntry, rawMatrixOne,
    unitNegativeOne, RationalQuaternion.scalar]
  all_goals decide

/-- The first imaginary basis gives the literal half-turn diagonal. -/
theorem rawMatrix_basisI :
    ∀ i j, rawMatrix RationalQuaternion.basisI i j ≈
      (if i = j then (if i = (0 : Fin 3) then 1 else -1) else 0) := by
  apply fin3_all
  all_goals apply fin3_all
  all_goals dsimp [rawMatrix, rawEntry, quadraticEntry, RationalQuaternion.basisI]
  all_goals decide

theorem rawMatrix_basisJ :
    ∀ i j, rawMatrix RationalQuaternion.basisJ i j ≈
      (if i = j then (if i = (1 : Fin 3) then 1 else -1) else 0) := by
  apply fin3_all
  all_goals apply fin3_all
  all_goals dsimp [rawMatrix, rawEntry, quadraticEntry, RationalQuaternion.basisJ]
  all_goals decide

theorem rawMatrix_basisK :
    ∀ i j, rawMatrix RationalQuaternion.basisK i j ≈
      (if i = j then (if i = (2 : Fin 3) then 1 else -1) else 0) := by
  apply fin3_all
  all_goals apply fin3_all
  all_goals dsimp [rawMatrix, rawEntry, quadraticEntry, RationalQuaternion.basisK]
  all_goals decide

/-- Raw conjugation transposes the adjoint matrix. -/
theorem rawMatrix_conj (q : RationalQuaternion) :
    ∀ i j, rawMatrix (RationalQuaternion.conj q) i j ≈
      rawMatrixTranspose (rawMatrix q) i j := by
  intro i j
  have hn : normalize (exprEntry (quaternionConj qx) i j) =
      normalize (exprEntry qx j i) := by
    have h : ∀ i j, normalize (exprEntry (quaternionConj qx) i j) =
        normalize (exprEntry qx j i) := by
      apply fin3_all
      all_goals apply fin3_all
      all_goals decide
    exact h i j
  have h := poly_identity_of_normal_eq
    (exprEntry (quaternionConj qx) i j) (exprEntry qx j i) hn
    (environment q q)
  simp only [exprEntry_eval,quaternionEval_conj] at h
  change rawMatrix (RationalQuaternion.conj q) i j ≈
    rawMatrixTranspose (rawMatrix q) i j at h
  exact h

/-- The displayed degree-two entries are the IMAGINARY coordinates of the
actual raw Hamilton conjugation `q * basis_j * conj(q)`. -/
theorem raw_conjugation_entry (q : RationalQuaternion) : ∀ i j,
    rawImag (RationalQuaternion.mul
      (RationalQuaternion.mul q (rawBasis j)) (RationalQuaternion.conj q)) i ≈
      rawEntry q i j := by
  intro i j
  let lhs : PE := exprImag
    (quaternionMul (quaternionMul qx (exprBasis j)) (quaternionConj qx)) i
  let rhs : PE := exprEntry qx i j
  have hn : normalize lhs = normalize rhs := by
    have h : ∀ i j,
        normalize (exprImag (quaternionMul
          (quaternionMul qx (exprBasis j)) (quaternionConj qx)) i) =
          normalize (exprEntry qx i j) := by
      apply fin3_all
      all_goals apply fin3_all
      all_goals decide
    exact h i j
  have h := poly_identity_of_normal_eq lhs rhs hn (environment q q)
  change eval (environment q q)
      (exprImag (quaternionMul (quaternionMul qx (exprBasis j))
        (quaternionConj qx)) i) ≈
      eval (environment q q) (exprEntry qx i j) at h
  simp only [exprImag_eval,exprEntry_eval,quaternionEval_mul,
    quaternionEval_conj,rawBasis_eval] at h
  change rawImag (RationalQuaternion.mul
      (RationalQuaternion.mul q (rawBasis j)) (RationalQuaternion.conj q)) i ≈
        rawEntry q i j at h
  exact h

/-! ## Supplied-row and quotient entry values -/

def rowEntry (X : CauchyPoint) (i j : Fin 3) : CReal :=
  quadraticEntry CReal.add CReal.mul CReal.neg (CReal.ofQ' 2)
    (rowCoordinate X 0) (rowCoordinate X 1)
    (rowCoordinate X 2) (rowCoordinate X 3) i j

private def regularSquare {x : CReal} (R : InnerRegularity x) :
    InnerRegularity (CReal.mul x x) := R.mul R

private def regularDouble {x : CReal} (R : InnerRegularity x) :
    InnerRegularity (CReal.mul (CReal.ofQ' 2) x) :=
  (InnerRegularity.ofQ' 2).mul R

/-- Every actual matrix entry on a SUPPLIED row has a computable inner rate. -/
def rowEntryRegularity (X : CauchyPoint) :
    ∀ i j, InnerRegularity (rowEntry X i j) := by
  let r := rowCoordinateRegularity X 0
  let u := rowCoordinateRegularity X 1
  let v := rowCoordinateRegularity X 2
  let w := rowCoordinateRegularity X 3
  apply fin3_all
  all_goals apply fin3_all
  all_goals dsimp [rowEntry, quadraticEntry]
  · exact (((regularSquare r).add (regularSquare u)).add
      (regularSquare v).neg).add (regularSquare w).neg
  · exact regularDouble ((u.mul v).add (r.mul w).neg)
  · exact regularDouble ((u.mul w).add (r.mul v))
  · exact regularDouble ((u.mul v).add (r.mul w))
  · exact (((regularSquare r).add (regularSquare u).neg).add
      (regularSquare v)).add (regularSquare w).neg
  · exact regularDouble ((v.mul w).add (r.mul u).neg)
  · exact regularDouble ((u.mul w).add (r.mul v).neg)
  · exact regularDouble ((v.mul w).add (r.mul u))
  · exact (((regularSquare r).add (regularSquare u).neg).add
      (regularSquare v).neg).add (regularSquare w)

/-- Each supplied row's rational approximation is the ORIGINAL degree-two
Hamilton polynomial at exactly the same row index. -/
theorem rowEntry_approx (X : CauchyPoint) (n : Nat) :
    ∀ i j, (rowEntry X i j).approx n = rawEntry (X.seq n).val i j := by
  apply fin3_all
  all_goals apply fin3_all
  all_goals rfl

/-- The completed adjoint matrix is a function of quotient coordinates,
not of a chosen representative row. -/
def representation (x : Point) : Matrix := fun i j =>
  quadraticEntry RCadd RCmul RCneg
    (Quotient.mk crealSetoid (CReal.ofQ' 2))
    (pointCoordinate 0 x) (pointCoordinate 1 x)
    (pointCoordinate 2 x) (pointCoordinate 3 x) i j

theorem representation_mk (X : CauchyPoint) (i j : Fin 3) :
    representation (Quotient.mk chordSeminorm.completionSetoid X) i j =
      Quotient.mk crealSetoid (rowEntry X i j) := by
  have h : ∀ i j, representation
      (Quotient.mk chordSeminorm.completionSetoid X) i j =
        Quotient.mk crealSetoid (rowEntry X i j) := by
    apply fin3_all
    all_goals apply fin3_all
    all_goals rfl
  exact h i j

theorem representation_embed (q : UnitNorm) (i j : Fin 3) :
    representation (embed q) i j =
      Quotient.mk crealSetoid (CReal.ofQ' (rawEntry q.val i j)) := by
  have h : ∀ i j, representation (embed q) i j =
      Quotient.mk crealSetoid (CReal.ofQ' (rawEntry q.val i j)) := by
    apply fin3_all
    all_goals apply fin3_all
    all_goals apply Quotient.sound
    all_goals exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  exact h i j

def matrixMul (A B : Matrix) : Matrix := fun i j =>
  RCadd (RCadd (RCmul (A i 0) (B 0 j)) (RCmul (A i 1) (B 1 j)))
    (RCmul (A i 2) (B 2 j))
def matrixTranspose (A : Matrix) : Matrix := fun i j => A j i
def matrixOne : Matrix := fun i j =>
  Quotient.mk crealSetoid (CReal.ofQ' (rawMatrixOne i j))

/-- Literal matrix product on EVERY completed quaternion Point. -/
theorem representation_mul (x y : Point) :
    representation (completedMul x y) =
      matrixMul (representation x) (representation y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  funext i j
  change representation
      (Quotient.mk chordSeminorm.completionSetoid (multiplication.mapCauchy X Y)) i j =
        matrixMul
          (representation (Quotient.mk chordSeminorm.completionSetoid X))
          (representation (Quotient.mk chordSeminorm.completionSetoid Y)) i j
  rw [representation_mk]
  have hX : representation (Quotient.mk chordSeminorm.completionSetoid X) =
      fun a b => Quotient.mk crealSetoid (rowEntry X a b) := by
    funext a b
    exact representation_mk X a b
  have hY : representation (Quotient.mk chordSeminorm.completionSetoid Y) =
      fun a b => Quotient.mk crealSetoid (rowEntry Y a b) := by
    funext a b
    exact representation_mk Y a b
  rw [hX,hY]
  change Quotient.mk crealSetoid (rowEntry (multiplication.mapCauchy X Y) i j) =
    Quotient.mk crealSetoid
      (CReal.add (CReal.add (CReal.mul (rowEntry X i 0) (rowEntry Y 0 j))
        (CReal.mul (rowEntry X i 1) (rowEntry Y 1 j)))
        (CReal.mul (rowEntry X i 2) (rowEntry Y 2 j)))
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change (rowEntry (multiplication.mapCauchy X Y) i j).approx n ≈
    ((rowEntry X i 0).approx n * (rowEntry Y 0 j).approx n +
      (rowEntry X i 1).approx n * (rowEntry Y 1 j).approx n) +
      (rowEntry X i 2).approx n * (rowEntry Y 2 j).approx n
  simp only [rowEntry_approx]
  exact rawMatrix_mul (X.seq n).val (Y.seq n).val i j

theorem representation_one : representation completedOne = matrixOne := by
  funext i j
  change representation
      (Quotient.mk chordSeminorm.completionSetoid (chordSeminorm.constant unitOne)) i j =
        matrixOne i j
  rw [representation_mk]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change (rowEntry (chordSeminorm.constant unitOne) i j).approx n ≈
    (CReal.ofQ' (rawMatrixOne i j)).approx n
  rw [rowEntry_approx]
  exact rawMatrix_one i j

/-- Completed inversion is actual transpose, not only an abstract inverse. -/
theorem representation_inv (x : Point) :
    representation (completedInv x) = matrixTranspose (representation x) := by
  refine Quotient.inductionOn x ?_
  intro X
  funext i j
  change representation
      (Quotient.mk chordSeminorm.completionSetoid (inversion.mapCauchy X)) i j =
        matrixTranspose (representation
          (Quotient.mk chordSeminorm.completionSetoid X)) i j
  rw [representation_mk]
  change Quotient.mk crealSetoid (rowEntry (inversion.mapCauchy X) i j) =
    representation (Quotient.mk chordSeminorm.completionSetoid X) j i
  rw [representation_mk]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change (rowEntry (inversion.mapCauchy X) i j).approx n ≈
    (rowEntry X j i).approx n
  simp only [rowEntry_approx]
  exact rawMatrix_conj (X.seq n).val i j

theorem representation_orthogonal_left (x : Point) :
    matrixMul (matrixTranspose (representation x)) (representation x) = matrixOne := by
  rw [← representation_inv, ← representation_mul, completedInv_mul, representation_one]

theorem representation_orthogonal_right (x : Point) :
    matrixMul (representation x) (matrixTranspose (representation x)) = matrixOne := by
  rw [← representation_inv, ← representation_mul, completedMul_inv, representation_one]

/-! ## Trace and the already represented even character -/

def matrixTrace (A : Matrix) : RC :=
  RCadd (RCadd (A 0 0) (A 1 1)) (A 2 2)

private def rawTrace (q : RationalQuaternion) : Q' :=
  rawEntry q 0 0 + rawEntry q 1 1 + rawEntry q 2 2

private def exprTrace (q : QuaternionExpr) : PE :=
  .add (.add (exprEntry q 0 0) (exprEntry q 1 1)) (exprEntry q 2 2)

private def exprNorm (q : QuaternionExpr) : PE :=
  .add (.add (.mul q.r q.r) (.mul q.i q.i))
    (.add (.mul q.j q.j) (.mul q.k q.k))

private theorem rawTrace_formula (q : RationalQuaternion) :
    rawTrace q ≈ 4*(q.r*q.r) + -(normSq q) := by
  have hn : normalize (exprTrace qx) = normalize
      (.add (.mul (.const 4) (.mul (.var 0) (.var 0)))
        (.neg (exprNorm qx))) := by decide
  have h := poly_identity_of_normal_eq _ _ hn (environment q q)
  change rawTrace q ≈ 4*(q.r*q.r) + -(normSq q) at h
  exact h

private theorem rawChiTwo_formula (q : RationalQuaternion) :
    evalRatPoly (quaternionCoordinates q) chiTwoPolynomial ≈
      4*(q.r*q.r)+(-1) := by
  change (4 : Q') * (((1*q.r)*q.r)*1) + ((-1:Q')*1+0) ≈ _
  exact poly_identity_of_normal_eq
    (.add (.mul (.const 4)
      (.mul (.mul (.mul (.const 1) (.var 0)) (.var 0)) (.const 1)))
      (.add (.mul (.const (-1)) (.const 1)) (.const 0)))
    (.add (.mul (.const 4) (.mul (.var 0) (.var 0))) (.const (-1)))
    (by decide) (fun _ => q.r)

private theorem rawTrace_chiTwo (q : UnitNorm) :
    rawTrace q.val ≈ evalRatPoly (quaternionCoordinates q.val) chiTwoPolynomial := by
  have hs : 4*(q.val.r*q.val.r) + -(normSq q.val) ≈
      4*(q.val.r*q.val.r)+(-1) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ q.unitNorm)
  exact Q'.eqv_trans _ _ _ (rawTrace_formula q.val)
    (Q'.eqv_trans _ _ _ hs (Q'.eqv_symm (rawChiTwo_formula q.val)))

/-- The REAL matrix trace is the already represented spin-one even character
on EVERY completed Point, not a new Haar or continuous-function premise. -/
theorem trace_chiTwo (x : Point) :
    matrixTrace (representation x) =
      YMGap.Continuum.QuaternionSignQuotientRepresentedHaar.evaluation
        YMGap.Continuum.QuaternionSignQuotientRepresentedHaar.chiTwo x := by
  rw [show YMGap.Continuum.QuaternionSignQuotientRepresentedHaar.evaluation
      YMGap.Continuum.QuaternionSignQuotientRepresentedHaar.chiTwo x =
      YMGap.Continuum.QuaternionRepresentedHaar.evaluate
        (YMGap.Continuum.QuaternionRepresentedPolynomialHaar.polynomial
          chiTwoPolynomial) x from rfl]
  rw [evaluate_polynomial]
  refine Quotient.inductionOn x ?_
  intro X
  rw [pointEval_rowPolynomialEval]
  change Quotient.mk crealSetoid
      (CReal.add (CReal.add (rowEntry X 0 0) (rowEntry X 1 1))
        (rowEntry X 2 2)) =
      Quotient.mk crealSetoid (YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation.rowPolynomialEval
        X chiTwoPolynomial)
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  rw [rowPolynomialEval_approx]
  exact rawTrace_chiTwo (X.seq n)

/-! ## Actual matrix image and central-sign descent -/

/-- A literal matrix with a supplied realization by an existing Point. The
group setoid below identifies equal MATRICES, not equal Point witnesses. -/
structure RepresentedMatrix where
  matrix : Matrix
  point : Point
  pin : matrix = representation point

def ofPoint (x : Point) : RepresentedMatrix := ⟨representation x,x,rfl⟩

def representedMul (A B : RepresentedMatrix) : RepresentedMatrix where
  matrix := matrixMul A.matrix B.matrix
  point := completedMul A.point B.point
  pin := by rw [A.pin, B.pin, ← representation_mul]

def representedInv (A : RepresentedMatrix) : RepresentedMatrix where
  matrix := matrixTranspose A.matrix
  point := completedInv A.point
  pin := by rw [A.pin, ← representation_inv]

def representedOne : RepresentedMatrix where
  matrix := matrixOne
  point := completedOne
  pin := representation_one.symm

/-- Matrix equality is the represented-image equivalence. Point realizations
remain data, but are not used as the equality relation. -/
def representedGroup : ConstructiveGroup where
  Carrier := RepresentedMatrix
  setoid := {
    r := fun A B => A.matrix = B.matrix
    iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩ }
  one := representedOne
  mul := representedMul
  inv := representedInv
  mul_congr := by
    intro A A' B B' hA hB
    change matrixMul A.matrix B.matrix = matrixMul A'.matrix B'.matrix
    rw [hA,hB]
  inv_congr := by
    intro A B h
    change matrixTranspose A.matrix = matrixTranspose B.matrix
    rw [h]
  mul_assoc := by
    intro A B C
    change (representedMul (representedMul A B) C).matrix =
      (representedMul A (representedMul B C)).matrix
    rw [(representedMul (representedMul A B) C).pin,
      (representedMul A (representedMul B C)).pin]
    exact congrArg representation (completedMul_assoc A.point B.point C.point)
  one_mul := by
    intro A
    change (representedMul representedOne A).matrix = A.matrix
    rw [(representedMul representedOne A).pin, A.pin]
    exact congrArg representation (completedOne_mul A.point)
  mul_one := by
    intro A
    change (representedMul A representedOne).matrix = A.matrix
    rw [(representedMul A representedOne).pin, A.pin]
    exact congrArg representation (completedMul_one A.point)
  inv_mul := by
    intro A
    change (representedMul (representedInv A) A).matrix = representedOne.matrix
    rw [(representedMul (representedInv A) A).pin,representedOne.pin]
    exact congrArg representation (completedInv_mul A.point)
  mul_inv := by
    intro A
    change (representedMul A (representedInv A)).matrix = representedOne.matrix
    rw [(representedMul A (representedInv A)).pin,representedOne.pin]
    exact congrArg representation (completedMul_inv A.point)

/-- Concrete representation of the EXISTING completed quaternion group. -/
def coverRepresentation : ConstructiveGroup.Hom completedGroup representedGroup where
  toFun := ofPoint
  map_equivalent := by
    intro x y h
    exact congrArg representation h
  map_one := representation_one
  map_mul := representation_mul

/-- Both central signs are killed by the literal three-dimensional matrix. -/
theorem representation_sign (z : QuaternionSign) :
    representation (includeSign z) = matrixOne := by
  funext i j
  cases z with
  | positive =>
      change representation (embed unitOne) i j = matrixOne i j
      rw [representation_embed]
      exact Quotient.sound (ofQ'_equiv_of_eqv (rawMatrix_one i j))
  | negative =>
      change representation (embed unitNegativeOne) i j = matrixOne i j
      rw [representation_embed]
      exact Quotient.sound (ofQ'_equiv_of_eqv (rawMatrix_negativeOne i j))

def coverRepresentation_kills_signs :
    signQuotientPresentation.gamma.IsKilledBy coverRepresentation := by
  intro z
  exact representation_sign z

/-- Concrete, constructive descent to ACTUAL completed sign cosets. -/
def quotientRepresentation :
    ConstructiveGroup.Hom signQuotientGroup representedGroup :=
  signQuotientPresentation.descendRepresentation coverRepresentation
    coverRepresentation_kills_signs

theorem quotientRepresentation_matrix (x : Point) :
    (quotientRepresentation.toFun (signQuotientHom.toFun x)).matrix =
      representation x :=
  signQuotientPresentation.descendRepresentation_quotient_hom
    coverRepresentation coverRepresentation_kills_signs x

theorem representation_coset_congr (x y : Point)
    (h : signQuotientGroup.Equivalent x y) : representation x = representation y :=
  signQuotientPresentation.images_equivalent_of_quotient_equivalent
    coverRepresentation coverRepresentation_kills_signs h

#print axioms rawEntry
#print axioms rawMatrix_mul
#print axioms rawMatrix_one
#print axioms rawMatrix_negativeOne
#print axioms rawMatrix_basisI
#print axioms rawMatrix_basisJ
#print axioms rawMatrix_basisK
#print axioms raw_conjugation_entry
#print axioms rawMatrix_conj
#print axioms rowEntry
#print axioms rowEntryRegularity
#print axioms rowEntry_approx
#print axioms representation
#print axioms representation_mk
#print axioms representation_embed
#print axioms representation_mul
#print axioms representation_one
#print axioms representation_inv
#print axioms representation_orthogonal_left
#print axioms representation_orthogonal_right
#print axioms matrixTrace
#print axioms trace_chiTwo
#print axioms representedMul
#print axioms representedInv
#print axioms representedGroup
#print axioms coverRepresentation
#print axioms representation_sign
#print axioms coverRepresentation_kills_signs
#print axioms quotientRepresentation
#print axioms quotientRepresentation_matrix
#print axioms representation_coset_congr

end YMGap.RepTheory.RationalQuaternionCompletedAdjointMatrix
