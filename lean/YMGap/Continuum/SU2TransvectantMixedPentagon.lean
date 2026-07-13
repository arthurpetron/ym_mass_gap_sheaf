/-
# A rational transvectant pentagon with genuinely mixed external labels

The signed orthonormal SU(2) recoupling matrices contain square roots.  In the
unnormalized binary-form basis the Clebsch--Gordan maps are Cayley
transvectants, so every coefficient is instead an exact rational combination
of binomial and factorial ratios.  This file makes that basis computationally
explicit and follows one complete, non-unit pentagon.

The mixed external twice-spin labels are `(2,2,1,1)` (two spin-one and two
spin-half factors), with total label `0`.  Each of the five bracketings has two
admissible fusion paths.  The five transvectant basis changes are

  P0 -> P1 : [ -2/3  1/3 ]      P1 -> P2 : diag(1/2,1)
             [  4/3  1/3 ]

  P2 -> P3 : [ -1  1/2 ]        P0 -> P4 : diag(1,1/2)
             [  2  1/2 ]

  P4 -> P3 : identity.

Consequently the three-edge and two-edge routes are the same full matrix,
`diag(1,1/2)`.  In particular both off-diagonal coefficients vanish by genuine
two-channel cancellation; this is not the label-independent constant-block
construction refuted upstream.

For comparison, the five path bases for four spin-one factors and total zero
are also enumerated.  Each contains exactly the three expected channels
`0,2,4`, with the second internal label fixed by the bracketing.

Constructive contract: `Q'`/`Nat`/`Fin` only, with no classical reasoning,
nonconstructive reals, compiler-trusted decisions, proof holes, or new axioms.
All finite tables are checked by the kernel.  This is one finite physical
pentagon, not the all-label pentagon and not a Clay-frontier discharge.
-/

import YMGap.Continuum.TransvectantCG
import YMGap.Continuum.SU2SpinOneNontrivialPentagon

namespace YMGap.Continuum.SU2TransvectantMixedPentagon

set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2TrivalentThetaRecoupling
open YMGap.Continuum.SU2SpinOneLabelWiredPentagon

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The binomial/factorial coefficient of an unnormalized transvectant -/

/-- Factorial used by the explicit transvectant coefficient. -/
def tvFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * tvFact n

/-- The exact rational falling factorial `n!/(n-r)!`, zero outside `r ≤ n`. -/
def tvFallQ (n r : Nat) : Q' :=
  if r ≤ n then Q'.mkN (tvFact n) (tvFact (n - r) - 1) else 0

/-- The exact rational binomial coefficient `k!/(r!(k-r)!)`. -/
def tvBinomQ (k r : Nat) : Q' :=
  if r ≤ k then
    Q'.mkN (tvFact k) (tvFact r * tvFact (k - r) - 1)
  else 0

def tvPhase (r : Nat) : Q' :=
  if r % 2 = 0 then 1 else Q'.ofInt (-1)

/-- Coefficient of the single output monomial in the order-`k` transvectant of
`x^i y^(m-i)` and `x^j y^(n-j)`.  This is the binomial expansion of
`(∂x₁∂y₂ - ∂y₁∂x₂)^k`, with no normalization or square root. -/
def transvectFactorialCoeff (m n k i j : Nat) : Q' :=
  finSum (fun r =>
    tvPhase r * tvBinomQ k r * tvFallQ i (k - r) * tvFallQ (m - i) r *
      tvFallQ j r * tvFallQ (n - j) (k - r)) (k + 1)

/-- The factorial formula agrees with the actual Cayley `OmegaK` construction
on every spin-one/spin-half monomial and both possible contraction orders. -/
theorem transvectFactorialCoeff_21_exact :
    ∀ k, k < 2 → ∀ i, i < 3 → ∀ j, j < 2 → ∀ s, s < 4 →
      transvect 2 1 k (tprod (mono i) (mono j)) s ≈
        (if s = i + j - k then transvectFactorialCoeff 2 1 k i j else 0) := by
  decide

/-- The same exact formula on the complete spin-one/spin-one window, through
the maximal physical contraction order `2`. -/
theorem transvectFactorialCoeff_22_exact :
    ∀ k, k < 3 → ∀ i, i < 3 → ∀ j, j < 3 → ∀ s, s < 5 →
      transvect 2 2 k (tprod (mono i) (mono j)) s ≈
        (if s = i + j - k then transvectFactorialCoeff 2 2 k i j else 0) := by
  decide

/-! ## 2. Nested trivalent maps and exact mixed associator rows -/

/-- The order selecting output label `c` from input labels `a,b`. -/
def couplingOrder (a b c : Nat) : Nat := (a + b - c) / 2

/-- Left-associated unnormalized trivalent map `((a b)_e c)_d`. -/
def triLeft (a b c d e : Nat) (x y z : BForm) : BForm :=
  transvect e c (couplingOrder e c d)
    (tprod (transvect a b (couplingOrder a b e) (tprod x y)) z)

/-- Right-associated unnormalized trivalent map `(a (b c)_f)_d`. -/
def triRight (a b c d f : Nat) (x y z : BForm) : BForm :=
  transvect a f (couplingOrder a f d)
    (tprod x (transvect b c (couplingOrder b c f) (tprod y z)))

def scaleForm (q : Q') (x : BForm) : BForm := fun s => q * x s
def addForm (x y : BForm) : BForm := fun s => x s + y s

def lin2Form (q r : Q') (x y : BForm) : BForm :=
  addForm (scaleForm q x) (scaleForm r y)

/-- Equality of trilinear maps, checked on the complete monomial basis and the
whole output window.  Trilinearity then makes this the finite matrix identity. -/
def TriMapEqv (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) : Prop :=
  ∀ i, i < a + 1 → ∀ j, j < b + 1 → ∀ k, k < c + 1 →
    FormEqv (d + 1) (L (mono i) (mono j) (mono k))
      (R (mono i) (mono j) (mono k))

instance (a b c d : Nat) (L R : BForm → BForm → BForm → BForm) :
    Decidable (TriMapEqv a b c d L R) := by
  unfold TriMapEqv
  infer_instance

def twoThirds : Q' := Q'.mkPos 2 3 (by decide)
def fourThirds : Q' := Q'.mkPos 4 3 (by decide)

/-- First row of the genuinely mixed local block
`F^(2,2,1)_1`, in the source channels `e=0,2` and target channels `f=1,3`. -/
theorem mixed221_assoc_e0 :
    TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 0)
      (fun x y z => lin2Form (-twoThirds) oneThird
        (triRight 2 2 1 1 1 x y z) (triRight 2 2 1 1 3 x y z)) := by
  decide

/-- Second row of `F^(2,2,1)_1`. -/
theorem mixed221_assoc_e2 :
    TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 2)
      (fun x y z => lin2Form fourThirds oneThird
        (triRight 2 2 1 1 1 x y z) (triRight 2 2 1 1 3 x y z)) := by
  decide

/-- The other two-channel edge used by the mixed pentagon:
`F^(2,1,1)_2 = [[-1,1/2],[2,1/2]]`. -/
theorem mixed211_assoc_rows :
    TriMapEqv 2 1 1 2 (triLeft 2 1 1 2 1)
      (fun x y z => lin2Form (-1) oneHalf
        (triRight 2 1 1 2 0 x y z) (triRight 2 1 1 2 2 x y z)) ∧
    TriMapEqv 2 1 1 2 (triLeft 2 1 1 2 3)
      (fun x y z => lin2Form 2 oneHalf
        (triRight 2 1 1 2 0 x y z) (triRight 2 1 1 2 2 x y z)) := by
  decide

/-- All one-channel transvectant associators on the remaining three pentagon
edges.  These are still derived maps, not inserted unit axioms. -/
theorem mixed_scalar_assoc_edges :
    TriMapEqv 2 1 1 0 (triLeft 2 1 1 0 1)
      (fun x y z => scaleForm oneHalf (triRight 2 1 1 0 2 x y z)) ∧
    TriMapEqv 2 3 1 0 (triLeft 2 3 1 0 1)
      (triRight 2 3 1 0 2) ∧
    TriMapEqv 0 1 1 0 (triLeft 0 1 1 0 1)
      (triRight 0 1 1 0 0) ∧
    TriMapEqv 2 2 0 0 (triLeft 2 2 0 0 0)
      (triRight 2 2 0 0 2) ∧
    TriMapEqv 2 2 2 0 (triLeft 2 2 2 0 2)
      (triRight 2 2 2 0 2) := by
  decide

/-! ## 3. The five finite fusion-path bases -/

inductive PentagonTree where
  | p0 | p1 | p2 | p3 | p4
deriving DecidableEq

abbrev SmallPath := Fin 5 × Fin 5

def pathValidNat (T : PentagonTree) (a b c d total x y : Nat) : Bool :=
  match T with
  | .p0 => fusionOK a b x && fusionOK x c y && fusionOK y d total
  | .p1 => fusionOK b c x && fusionOK a x y && fusionOK y d total
  | .p2 => fusionOK b c x && fusionOK x d y && fusionOK a y total
  | .p3 => fusionOK c d x && fusionOK b x y && fusionOK a y total
  | .p4 => fusionOK a b x && fusionOK c d y && fusionOK x y total

def pathValid (T : PentagonTree) (a b c d total : Nat) (p : SmallPath) : Bool :=
  pathValidNat T a b c d total p.1.val p.2.val

theorem fusionOK_upper_constructive {a b s : Nat} (h : fusionOK a b s = true) :
    s ≤ a + b := by
  unfold fusionOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.2

theorem fusionOK_zero_output_constructive {a b : Nat} (h : fusionOK a b 0 = true) :
    a = b := by
  unfold fusionOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, _⟩, _⟩ := h
  have hzero : Nat.max a b - Nat.min a b = 0 := Nat.le_zero.mp h1
  have hle : Nat.max a b ≤ Nat.min a b := Nat.sub_eq_zero_iff_le.mp hzero
  have hab : a ≤ b := Nat.le_trans (Nat.le_max_left a b)
    (Nat.le_trans hle (Nat.min_le_right a b))
  have hba : b ≤ a := Nat.le_trans (Nat.le_max_right a b)
    (Nat.le_trans hle (Nat.min_le_left a b))
  exact Nat.le_antisymm hab hba

/-- No all-spin-one path can escape the displayed `0..4` window. -/
theorem allSpinOnePaths_bounded (T : PentagonTree) (x y : Nat)
    (h : pathValidNat T 2 2 2 2 0 x y = true) : x < 5 ∧ y < 5 := by
  cases T
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_succ_of_le hx
    · rw [hy]
      decide
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_succ_of_le hx
    · rw [hy]
      decide
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_succ_of_le hx
    · rw [← hy]
      decide
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_succ_of_le hx
    · rw [← hy]
      decide
  · obtain ⟨h12, _⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_upper_constructive h2
    exact ⟨Nat.lt_succ_of_le hx, Nat.lt_succ_of_le hy⟩

/-- The mixed `(2,2,1,1)` paths also lie in the same finite window. -/
theorem mixedPaths_bounded (T : PentagonTree) (x y : Nat)
    (h : pathValidNat T 2 2 1 1 0 x y = true) : x < 5 ∧ y < 5 := by
  cases T
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_succ_of_le hx
    · rw [hy]
      decide
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_of_le_of_lt hx (by decide)
    · rw [hy]
      decide
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_of_le_of_lt hx (by decide)
    · rw [← hy]
      decide
  · obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_zero_output_constructive h3
    constructor
    · exact Nat.lt_of_le_of_lt hx (by decide)
    · rw [← hy]
      decide
  · obtain ⟨h12, _⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
    have hx := fusionOK_upper_constructive h1
    have hy := fusionOK_upper_constructive h2
    constructor
    · exact Nat.lt_succ_of_le hx
    · exact Nat.lt_of_le_of_lt hy (by decide)

private def f0 : Fin 5 := ⟨0, by decide⟩
private def f1 : Fin 5 := ⟨1, by decide⟩
private def f2 : Fin 5 := ⟨2, by decide⟩
private def f3 : Fin 5 := ⟨3, by decide⟩
private def f4 : Fin 5 := ⟨4, by decide⟩

/-- Complete path bases for four spin-one factors `(2,2,2,2)` and total zero. -/
def allSpinOnePaths : PentagonTree → List SmallPath
  | .p0 => [(f0, f2), (f2, f2), (f4, f2)]
  | .p1 => [(f0, f2), (f2, f2), (f4, f2)]
  | .p2 => [(f0, f2), (f2, f2), (f4, f2)]
  | .p3 => [(f0, f2), (f2, f2), (f4, f2)]
  | .p4 => [(f0, f0), (f2, f2), (f4, f4)]

def fin5Window : List (Fin 5) := [f0, f1, f2, f3, f4]

/-- The complete `5×5` candidate window, before applying fusion guards. -/
def pathWindow : List SmallPath :=
  fin5Window.flatMap (fun x => fin5Window.map (fun y => (x, y)))

def spinOneValidPaths (T : PentagonTree) : List SmallPath :=
  pathWindow.filter (fun p => pathValid T 2 2 2 2 0 p)

/-- Filtering the whole finite candidate window gives exactly the five lists
above.  This is completeness, not just validity of the displayed paths. -/
theorem allSpinOnePaths_complete :
    spinOneValidPaths .p0 = allSpinOnePaths .p0 ∧
    spinOneValidPaths .p1 = allSpinOnePaths .p1 ∧
    spinOneValidPaths .p2 = allSpinOnePaths .p2 ∧
    spinOneValidPaths .p3 = allSpinOnePaths .p3 ∧
    spinOneValidPaths .p4 = allSpinOnePaths .p4 := by
  decide

/-- Complete path bases for the mixed external labels `(2,2,1,1)`, total zero. -/
def mixedPaths : PentagonTree → List SmallPath
  | .p0 => [(f0, f1), (f2, f1)]
  | .p1 => [(f1, f1), (f3, f1)]
  | .p2 => [(f1, f2), (f3, f2)]
  | .p3 => [(f0, f2), (f2, f2)]
  | .p4 => [(f0, f0), (f2, f2)]

def mixedValidPaths (T : PentagonTree) : List SmallPath :=
  pathWindow.filter (fun p => pathValid T 2 2 1 1 0 p)

theorem mixedPaths_complete :
    mixedValidPaths .p0 = mixedPaths .p0 ∧
    mixedValidPaths .p1 = mixedPaths .p1 ∧
    mixedValidPaths .p2 = mixedPaths .p2 ∧
    mixedValidPaths .p3 = mixedPaths .p3 ∧
    mixedValidPaths .p4 = mixedPaths .p4 := by
  decide

/-! ## 4. The full mixed five-tree pentagon matrix -/

abbrev Matrix2 := Fin 2 → Fin 2 → Q'

private def i0 : Fin 2 := ⟨0, by decide⟩
private def i1 : Fin 2 := ⟨1, by decide⟩

/-- `P0 -> P1`, certified by `mixed221_assoc_e0/e2`. -/
def edge01 : Matrix2
  | ⟨0, _⟩, ⟨0, _⟩ => -twoThirds
  | ⟨0, _⟩, ⟨1, _⟩ => oneThird
  | ⟨1, _⟩, ⟨0, _⟩ => fourThirds
  | ⟨1, _⟩, ⟨1, _⟩ => oneThird

/-- `P1 -> P2`, the two one-channel blocks at fixed `g=1,3`. -/
def edge12 : Matrix2
  | ⟨0, _⟩, ⟨0, _⟩ => oneHalf
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | _, _ => 0

/-- `P2 -> P3`, certified by `mixed211_assoc_rows`. -/
def edge23 : Matrix2
  | ⟨0, _⟩, ⟨0, _⟩ => -1
  | ⟨0, _⟩, ⟨1, _⟩ => oneHalf
  | ⟨1, _⟩, ⟨0, _⟩ => 2
  | ⟨1, _⟩, ⟨1, _⟩ => oneHalf

/-- `P0 -> P4`, at fixed source `e=0,2`. -/
def edge04 : Matrix2
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => oneHalf
  | _, _ => 0

/-- `P4 -> P3`; the two unnormalized scalar transvectants both equal one. -/
def edge43 : Matrix2
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | _, _ => 0

def mul2 (A B : Matrix2) : Matrix2 := fun i k =>
  A i i0 * B i0 k + A i i1 * B i1 k

def mixedPentagonLong : Matrix2 := mul2 (mul2 edge01 edge12) edge23
def mixedPentagonShort : Matrix2 := mul2 edge04 edge43

/-- The three-edge and two-edge routes agree on all four matrix coefficients.
This is a full finite pentagon matrix, not a single normalization check. -/
theorem mixed_five_tree_pentagon_full_matrix :
    mixedPentagonLong i0 i0 ≈ mixedPentagonShort i0 i0 ∧
    mixedPentagonLong i0 i1 ≈ mixedPentagonShort i0 i1 ∧
    mixedPentagonLong i1 i0 ≈ mixedPentagonShort i1 i0 ∧
    mixedPentagonLong i1 i1 ≈ mixedPentagonShort i1 i1 := by
  decide

/-- Exact common matrix and off-diagonal cancellation ledger. -/
theorem mixed_five_tree_pentagon_values :
    mixedPentagonLong i0 i0 ≈ 1 ∧
    mixedPentagonLong i0 i1 ≈ 0 ∧
    mixedPentagonLong i1 i0 ≈ 0 ∧
    mixedPentagonLong i1 i1 ≈ oneHalf ∧
    mixedPentagonShort i0 i0 ≈ 1 ∧
    mixedPentagonShort i0 i1 ≈ 0 ∧
    mixedPentagonShort i1 i0 ≈ 0 ∧
    mixedPentagonShort i1 i1 ≈ oneHalf := by
  decide

/-! ## 5. A single Type-level certificate tying the maps to the matrix -/

/-- The finite mixed pentagon as one constructive datum: complete path
enumerations, the actual transvectant edge expansions, and the full matrix
coherence all live in the same certificate. -/
structure MixedPentagonCertificate where
  spinOneBounded :
    ∀ T x y, pathValidNat T 2 2 2 2 0 x y = true → x < 5 ∧ y < 5
  mixedBounded :
    ∀ T x y, pathValidNat T 2 2 1 1 0 x y = true → x < 5 ∧ y < 5
  spinOnePathsExact :
    spinOneValidPaths .p0 = allSpinOnePaths .p0 ∧
    spinOneValidPaths .p1 = allSpinOnePaths .p1 ∧
    spinOneValidPaths .p2 = allSpinOnePaths .p2 ∧
    spinOneValidPaths .p3 = allSpinOnePaths .p3 ∧
    spinOneValidPaths .p4 = allSpinOnePaths .p4
  mixedPathsExact :
    mixedValidPaths .p0 = mixedPaths .p0 ∧
    mixedValidPaths .p1 = mixedPaths .p1 ∧
    mixedValidPaths .p2 = mixedPaths .p2 ∧
    mixedValidPaths .p3 = mixedPaths .p3 ∧
    mixedValidPaths .p4 = mixedPaths .p4
  edge01row0 :
    TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 0)
      (fun x y z => lin2Form (-twoThirds) oneThird
        (triRight 2 2 1 1 1 x y z) (triRight 2 2 1 1 3 x y z))
  edge01row1 :
    TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 2)
      (fun x y z => lin2Form fourThirds oneThird
        (triRight 2 2 1 1 1 x y z) (triRight 2 2 1 1 3 x y z))
  edge23rows :
    TriMapEqv 2 1 1 2 (triLeft 2 1 1 2 1)
      (fun x y z => lin2Form (-1) oneHalf
        (triRight 2 1 1 2 0 x y z) (triRight 2 1 1 2 2 x y z)) ∧
    TriMapEqv 2 1 1 2 (triLeft 2 1 1 2 3)
      (fun x y z => lin2Form 2 oneHalf
        (triRight 2 1 1 2 0 x y z) (triRight 2 1 1 2 2 x y z))
  scalarEdges :
    TriMapEqv 2 1 1 0 (triLeft 2 1 1 0 1)
      (fun x y z => scaleForm oneHalf (triRight 2 1 1 0 2 x y z)) ∧
    TriMapEqv 2 3 1 0 (triLeft 2 3 1 0 1) (triRight 2 3 1 0 2) ∧
    TriMapEqv 0 1 1 0 (triLeft 0 1 1 0 1) (triRight 0 1 1 0 0) ∧
    TriMapEqv 2 2 0 0 (triLeft 2 2 0 0 0) (triRight 2 2 0 0 2) ∧
    TriMapEqv 2 2 2 0 (triLeft 2 2 2 0 2) (triRight 2 2 2 0 2)
  pentagon :
    mixedPentagonLong i0 i0 ≈ mixedPentagonShort i0 i0 ∧
    mixedPentagonLong i0 i1 ≈ mixedPentagonShort i0 i1 ∧
    mixedPentagonLong i1 i0 ≈ mixedPentagonShort i1 i0 ∧
    mixedPentagonLong i1 i1 ≈ mixedPentagonShort i1 i1

/-- Import-ready witness for the complete finite construction. -/
def mixedPentagonCertificate : MixedPentagonCertificate where
  spinOneBounded := allSpinOnePaths_bounded
  mixedBounded := mixedPaths_bounded
  spinOnePathsExact := allSpinOnePaths_complete
  mixedPathsExact := mixedPaths_complete
  edge01row0 := mixed221_assoc_e0
  edge01row1 := mixed221_assoc_e2
  edge23rows := mixed211_assoc_rows
  scalarEdges := mixed_scalar_assoc_edges
  pentagon := mixed_five_tree_pentagon_full_matrix

end YMGap.Continuum.SU2TransvectantMixedPentagon

#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.transvectFactorialCoeff_21_exact
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.transvectFactorialCoeff_22_exact
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixed221_assoc_e0
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixed221_assoc_e2
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixed211_assoc_rows
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixed_scalar_assoc_edges
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.fusionOK_upper_constructive
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.fusionOK_zero_output_constructive
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.allSpinOnePaths_bounded
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixedPaths_bounded
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.allSpinOnePaths_complete
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixedPaths_complete
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixed_five_tree_pentagon_full_matrix
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixed_five_tree_pentagon_values
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagon.mixedPentagonCertificate
