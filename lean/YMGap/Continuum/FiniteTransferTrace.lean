/-
# P4: finite transfer matrices: Gram PSD, `Z = Tr T^R`, trace Cauchy–Schwarz and the four-factor trace Hölder

**Label: finite-dimensional linear-algebra scaffolding; also true for U(1); not gap evidence. No chart-closure claim.**
Additive. Constructive: finite rational sums (`RationalTail.finSum`) and rational inequalities only. No `Classical`,
no roots, no spectral theorem.

* `gram_symm`, `gram_psd`: a weighted Gram kernel `T_ij = Σ_g w_g φ_g(i) φ_g(j)` with `w ≥ 0` is symmetric and PSD.
  This is the form of an RP / character-truncated transfer slice.
* `partition_trace`: the periodic configuration sum `Z_{R+1} = Σ_{x_0..x_R} T(x_0,x_1)⋯T(x_R,x_0)` equals
  `Tr T^{R+1}`. Here `Z` is defined independently, as a sum over tuples.
* `trace_cs`: `(Tr AB)² ≤ Tr A² · Tr B²` for symmetric `A, B` (Hilbert–Schmidt Cauchy–Schwarz).
* `trace_holder4`: `(Tr ABCD)⁴ ≤ Tr A⁴ · Tr B⁴ · Tr C⁴ · Tr D⁴` for symmetric `A, B, C, D` (power form,
  two CS levels).

**Not ported (flagged):** trace Hölder for general `m`, `(Tr A₁⋯A_m)^m ≤ ∏ Tr A_i^m`. Beyond `m ∈ {1,2,4}`, the
iterated-CS route does not close: the doubled words stop being products of squares. The standard proofs use the spectral
theorem or Schatten norms (matrix roots), which have no rational constructive route in this repo. The instantiation of
`T` to the character-truncated Wilson slice is also not done here; that is P2′-adjacent.
-/

import YMGap.Constructive.FinSumAlg
import YMGap.Continuum.SU2TorusRPCSRat
import YMGap.Constructive.Sqrt
import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.FiniteTransferTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr finSum_mul_const const_mul_finSum finSum_add finSum_swap)
open YMGap.Continuum.SU2TorusRPCSRat (quad cs_q)

local infix:50 " ≈ " => Q'.eqv

abbrev Mat : Type := Nat → Nat → Q'

/-! ## Finite sums: nonnegativity and the double-sum Cauchy–Schwarz -/

theorem finSum_nonneg (f : Nat → Q') (h : ∀ i, (0 : Q') ≤ f i) : ∀ n, (0 : Q') ≤ finSum f n
  | 0 => Q'.le_refl' _
  | n + 1 => Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q') ≈ 0 + 0))
      (Q'.add_le_add (finSum_nonneg f h n) (h n))

theorem finSum_congr {f g : Nat → Q'} (h : ∀ i, f i ≈ g i) (n : Nat) : finSum f n ≈ finSum g n :=
  finSum_eqv_congr f g h n

/-- Double sum over `[0,n)²`. -/
def dsum (n : Nat) (f : Nat → Nat → Q') : Q' := finSum (fun i => finSum (fun c => f i c) n) n

theorem dsum_congr (n : Nat) {f g : Nat → Nat → Q'} (h : ∀ i c, f i c ≈ g i c) : dsum n f ≈ dsum n g :=
  finSum_congr (fun i => finSum_congr (fun c => h i c) n) n

theorem dsum_add (n : Nat) (f g : Nat → Nat → Q') :
    dsum n (fun i c => f i c + g i c) ≈ dsum n f + dsum n g :=
  Q'.eqv_trans _ _ _ (finSum_congr (fun i => finSum_add (fun c => f i c) (fun c => g i c) n) n)
    (finSum_add _ _ n)

theorem dsum_smul (n : Nat) (a : Q') (f : Nat → Nat → Q') :
    dsum n (fun i c => a * f i c) ≈ a * dsum n f :=
  Q'.eqv_symm (Q'.eqv_trans _ _ _ (const_mul_finSum _ a n)
    (finSum_congr (fun i => const_mul_finSum (fun c => f i c) a n) n))

theorem dsum_nonneg (n : Nat) (f : Nat → Nat → Q') (h : ∀ i c, (0 : Q') ≤ f i c) : (0 : Q') ≤ dsum n f :=
  finSum_nonneg _ (fun i => finSum_nonneg _ (fun c => h i c) n) n

theorem dsum_swap (n : Nat) (f : Nat → Nat → Q') : dsum n f ≈ dsum n (fun i c => f c i) :=
  finSum_swap f n n

/-- **Double-sum Cauchy–Schwarz:** `(Σ f g)² ≤ (Σ f²)(Σ g²)`. -/
theorem dsum_cs (n : Nat) (f g : Nat → Nat → Q') :
    dsum n (fun i c => f i c * g i c) * dsum n (fun i c => f i c * g i c) ≤
      dsum n (fun i c => f i c * f i c) * dsum n (fun i c => g i c * g i c) := by
  refine cs_q _ _ _ fun s t => ?_
  let S := Q'.ofInt s
  let T := Q'.ofInt t
  have hq : (0 : Q') ≤ dsum n (fun i c => (S * f i c + T * g i c) * (S * f i c + T * g i c)) :=
    dsum_nonneg n _ fun i c => YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _
  refine Q'.le_trans' _ _ _ hq (Q'.le_of_eqv ?_)
  have pt : ∀ i c, ((S * f i c + T * g i c) * (S * f i c + T * g i c)) ≈
      ((S * S) * (f i c * f i c) + ((S * T) * (f i c * g i c) + (S * T) * (f i c * g i c))) +
        (T * T) * (g i c * g i c) := fun i c =>
    YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))
          (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))))
        (.mul (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3)))) (by decide)
      (fun k => if k = 0 then S else if k = 1 then T else if k = 2 then f i c else g i c)
  refine Q'.eqv_trans _ _ _ (dsum_congr n pt) ?_
  refine Q'.eqv_trans _ _ _ (dsum_add n _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (dsum_add n _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (dsum_add n _ _))) ?_
  show _ ≈ quad _ _ _ s t
  unfold quad
  exact Q'.add_eqv_congr' (Q'.add_eqv_congr' (dsum_smul n _ _)
    (Q'.add_eqv_congr' (dsum_smul n _ _) (dsum_smul n _ _))) (dsum_smul n _ _)

/-! ## Matrices -/

def mmul (n : Nat) (A B : Mat) : Mat := fun i j => finSum (fun c => A i c * B c j) n

def tr (n : Nat) (A : Mat) : Q' := finSum (fun i => A i i) n

def Symm (A : Mat) : Prop := ∀ i j, A i j ≈ A j i

theorem tr_congr (n : Nat) {A B : Mat} (h : ∀ i j, A i j ≈ B i j) : tr n A ≈ tr n B :=
  finSum_congr (fun i => h i i) n

theorem mmul_congr (n : Nat) {A A' B B' : Mat} (hA : ∀ i j, A i j ≈ A' i j) (hB : ∀ i j, B i j ≈ B' i j) :
    ∀ i j, mmul n A B i j ≈ mmul n A' B' i j := fun i j =>
  finSum_congr (fun c => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (hA i c))
    (Q'.mul_eqv_congr_left _ _ _ (hB c j))) n

theorem mmul_assoc (n : Nat) (A B C : Mat) :
    ∀ i j, mmul n (mmul n A B) C i j ≈ mmul n A (mmul n B C) i j := fun i j => by
  show finSum (fun c => finSum (fun d => A i d * B d c) n * C c j) n ≈
    finSum (fun d => A i d * finSum (fun c => B d c * C c j) n) n
  refine Q'.eqv_trans _ _ _ (finSum_congr (fun c => finSum_mul_const _ (C c j) n) n) ?_
  refine Q'.eqv_trans _ _ _ (finSum_swap (fun c d => A i d * B d c * C c j) n n) ?_
  refine finSum_congr (fun d => Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (const_mul_finSum _ (A i d) n))) n
  exact finSum_congr (fun c => Q'.mul_assoc_eqv _ _ _) n

/-- Trace cyclicity `Tr(AB) = Tr(BA)`. -/
theorem tr_cyc (n : Nat) (A B : Mat) : tr n (mmul n A B) ≈ tr n (mmul n B A) :=
  Q'.eqv_trans _ _ _ (finSum_swap (fun i c => A i c * B c i) n n)
    (finSum_congr (fun _ => finSum_congr (fun _ => Q'.mul_comm_eqv _ _) n) n)

/-- For symmetric `A, B`: `(AB)_{ic} = (BA)_{ci}`. -/
theorem mmul_transpose (n : Nat) {A B : Mat} (hA : Symm A) (hB : Symm B) (i c : Nat) :
    mmul n A B i c ≈ mmul n B A c i :=
  finSum_congr (fun d => Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (hB d c)) (Q'.mul_eqv_congr_left _ _ _ (hA i d)))) n

theorem symm_sq (n : Nat) {A : Mat} (hA : Symm A) : Symm (mmul n A A) := fun i j =>
  mmul_transpose n hA hA i j

/-! ## Gram kernels are symmetric PSD -/

/-- Weighted Gram kernel `T_ij = Σ_{g<m} w_g φ_g(i) φ_g(j)`. -/
def gram (m : Nat) (w : Nat → Q') (φ : Nat → Nat → Q') : Mat :=
  fun i j => finSum (fun g => w g * (φ g i * φ g j)) m

theorem gram_symm (m : Nat) (w : Nat → Q') (φ : Nat → Nat → Q') : Symm (gram m w φ) := fun _ _ =>
  finSum_congr (fun _ => Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) m

/-- Quadratic form `xᵀ A x` on `[0,n)`. -/
def qform (n : Nat) (A : Mat) (x : Nat → Q') : Q' := dsum n (fun i j => x i * (A i j * x j))

theorem finSum_mul_finSum (n : Nat) (a b : Nat → Q') :
    finSum a n * finSum b n ≈ dsum n (fun i j => a i * b j) :=
  Q'.eqv_trans _ _ _ (finSum_mul_const a _ n)
    (finSum_congr (fun i => const_mul_finSum b (a i) n) n)

/-- **Gram PSD:** `xᵀ T x = Σ_g w_g (Σ_i φ_g(i) x_i)² ≥ 0` for `w ≥ 0`. -/
theorem gram_psd (n m : Nat) (w : Nat → Q') (φ : Nat → Nat → Q') (hw : ∀ g, (0 : Q') ≤ w g)
    (x : Nat → Q') : (0 : Q') ≤ qform n (gram m w φ) x := by
  let v : Nat → Q' := fun g => finSum (fun i => φ g i * x i) n
  have hnn : (0 : Q') ≤ finSum (fun g => w g * (v g * v g)) m :=
    finSum_nonneg _ (fun g => Q'.mul_nonneg _ _ (hw g)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _)) m
  refine Q'.le_trans' _ _ _ hnn (Q'.le_of_eqv ?_)
  -- Σ_g w_g v_g v_g = Σ_g Σ_i Σ_j w_g (φ_gi x_i)(φ_gj x_j) = Σ_i Σ_j x_i (Σ_g w_g φ_gi φ_gj) x_j
  have e1 : ∀ g, w g * (v g * v g) ≈
      finSum (fun i => finSum (fun j => x i * (w g * (φ g i * φ g j) * x j)) n) n := fun g => by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (finSum_mul_finSum n _ _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (dsum_smul n (w g) _)) ?_
    exact dsum_congr n fun i j =>
      YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
        (.mul (.var 2) (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.var 4))) (by decide)
        (fun k => if k = 0 then w g else if k = 1 then φ g i else if k = 2 then x i
          else if k = 3 then φ g j else x j)
  refine Q'.eqv_trans _ _ _ (finSum_congr e1 m) ?_
  refine Q'.eqv_trans _ _ _ (finSum_swap (fun g i => finSum (fun j => x i * (w g * (φ g i * φ g j) * x j)) n) m n) ?_
  refine finSum_congr (fun i => ?_) n
  refine Q'.eqv_trans _ _ _ (finSum_swap (fun g j => x i * (w g * (φ g i * φ g j) * x j)) m n) ?_
  refine finSum_congr (fun j => ?_) n
  show finSum (fun g => x i * (w g * (φ g i * φ g j) * x j)) m ≈ x i * (finSum (fun g => w g * (φ g i * φ g j)) m * x j)
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (finSum_mul_const _ (x j) m)) ?_)
  exact const_mul_finSum _ (x i) m

/-! ## The periodic configuration sum is a trace -/

/-- Sum over tuples `(x_1,…,x_m) ∈ [0,n)^m`. -/
def tupSum (n : Nat) : Nat → (List Nat → Q') → Q'
  | 0, f => f []
  | m + 1, f => finSum (fun c => tupSum n m fun xs => f (c :: xs)) n

theorem tupSum_congr (n : Nat) : ∀ (m : Nat) {f g : List Nat → Q'}, (∀ xs, f xs ≈ g xs) →
    tupSum n m f ≈ tupSum n m g
  | 0, _, _, h => h []
  | m + 1, _, _, h => finSum_congr (fun _ => tupSum_congr n m fun _ => h _) n

theorem tupSum_smul (n : Nat) : ∀ (m : Nat) (a : Q') (f : List Nat → Q'),
    tupSum n m (fun xs => a * f xs) ≈ a * tupSum n m f
  | 0, _, _ => Q'.eqv_refl _
  | m + 1, a, _ => Q'.eqv_trans _ _ _ (finSum_congr (fun _ => tupSum_smul n m a _) n)
      (Q'.eqv_symm (const_mul_finSum _ a n))

/-- Chain weight `T(a,x_1)T(x_1,x_2)⋯T(x_m,b)`. -/
def chain (T : Mat) : Nat → List Nat → Nat → Q'
  | a, [], b => T a b
  | a, c :: xs, b => T a c * chain T c xs b

/-- `tpow n T m = T^{m+1}` (first-step recursion). -/
def tpow (n : Nat) (T : Mat) : Nat → Mat
  | 0 => T
  | m + 1 => mmul n T (tpow n T m)

/-- Periodic configuration sum `Z_{m+1} = Σ_{x_0,…,x_m} T(x_0,x_1)⋯T(x_m,x_0)`. -/
def Zper (n : Nat) (T : Mat) (m : Nat) : Q' :=
  tupSum n (m + 1) fun xs => match xs with
    | [] => 0
    | x0 :: rest => chain T x0 rest x0

theorem chain_sum (n : Nat) (T : Mat) : ∀ (m a b : Nat),
    tupSum n m (fun xs => chain T a xs b) ≈ tpow n T m a b
  | 0, _, _ => Q'.eqv_refl _
  | m + 1, a, b =>
      finSum_congr (fun c => Q'.eqv_trans _ _ _ (tupSum_smul n m (T a c) _)
        (Q'.mul_eqv_congr_left _ _ _ (chain_sum n T m c b))) n

/-- **`Z_{m+1} = Tr T^{m+1}`.** -/
theorem partition_trace (n : Nat) (T : Mat) (m : Nat) : Zper n T m ≈ tr n (tpow n T m) :=
  finSum_congr (fun x0 => chain_sum n T m x0 x0) n

/-! ## Trace Cauchy–Schwarz and the four-factor trace Hölder (power form) -/

/-- `Tr(XY) = Σ_{ic} X_ic Y_ci`. -/
theorem tr_mmul (n : Nat) (X Y : Mat) : tr n (mmul n X Y) = dsum n (fun i c => X i c * Y c i) := rfl

/-- **Trace CS:** `(Tr AB)² ≤ Tr A² · Tr B²` for symmetric `A, B`. -/
theorem trace_cs (n : Nat) {A B : Mat} (hA : Symm A) (hB : Symm B) :
    tr n (mmul n A B) * tr n (mmul n A B) ≤ tr n (mmul n A A) * tr n (mmul n B B) := by
  have e1 : tr n (mmul n A B) ≈ dsum n (fun i c => A i c * B i c) :=
    dsum_congr n fun i c => Q'.mul_eqv_congr_left _ _ _ (hB c i)
  have e2 : tr n (mmul n A A) ≈ dsum n (fun i c => A i c * A i c) :=
    dsum_congr n fun i c => Q'.mul_eqv_congr_left _ _ _ (hA c i)
  have e3 : tr n (mmul n B B) ≈ dsum n (fun i c => B i c * B i c) :=
    dsum_congr n fun i c => Q'.mul_eqv_congr_left _ _ _ (hB c i)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e1)
    (Q'.mul_eqv_congr_left _ _ _ e1))) (Q'.le_trans' _ _ _ (dsum_cs n _ _) (Q'.le_of_eqv ?_))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e2) (Q'.mul_eqv_congr_left _ _ _ e3))

/-- `Σ_{ic} (AB)_ic² = Tr(A²B²)` for symmetric `A, B`. -/
theorem sq_sum_ab (n : Nat) {A B : Mat} (hA : Symm A) (hB : Symm B) :
    dsum n (fun i c => mmul n A B i c * mmul n A B i c) ≈ tr n (mmul n (mmul n A A) (mmul n B B)) := by
  -- Σ (AB)_ic (AB)_ic = Σ (AB)_ic (BA)_ci = Tr((AB)(BA))
  have h1 : dsum n (fun i c => mmul n A B i c * mmul n A B i c) ≈ tr n (mmul n (mmul n A B) (mmul n B A)) :=
    dsum_congr n fun i c => Q'.mul_eqv_congr_left _ _ _ (mmul_transpose n hA hB i c)
  refine Q'.eqv_trans _ _ _ h1 ?_
  -- (AB)(BA) = A(B(BA)) ; Tr(A·M) = Tr(M·A) ; M·A = (B(BA))A = ((BB)A)A = (BB)(AA) ; then cyc.
  refine Q'.eqv_trans _ _ _ (tr_congr n (mmul_assoc n A B (mmul n B A))) ?_
  refine Q'.eqv_trans _ _ _ (tr_cyc n A _) ?_
  have h2 : ∀ i j, mmul n (mmul n B (mmul n B A)) A i j ≈ mmul n (mmul n B B) (mmul n A A) i j := by
    intro i j
    refine Q'.eqv_trans _ _ _ (mmul_congr n (fun i j => Q'.eqv_symm (mmul_assoc n B B A i j))
      (fun _ _ => Q'.eqv_refl _) i j) ?_
    exact mmul_assoc n (mmul n B B) A A i j
  refine Q'.eqv_trans _ _ _ (tr_congr n h2) ?_
  exact tr_cyc n _ _

theorem tr_sq_nonneg (n : Nat) {A B : Mat} (hA : Symm A) (hB : Symm B) :
    (0 : Q') ≤ tr n (mmul n (mmul n A A) (mmul n B B)) :=
  Q'.le_trans' _ _ _ (dsum_nonneg n _ fun _ _ => YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _)
    (Q'.le_of_eqv (sq_sum_ab n hA hB))

/-- `X⁴ := (XX)(XX)`. -/
def pow4 (n : Nat) (X : Mat) : Mat := mmul n (mmul n X X) (mmul n X X)

/-- **Four-factor trace Hölder, power form:** for symmetric `A, B, C, D`,
`(Tr ABCD)⁴ ≤ Tr A⁴ · Tr B⁴ · Tr C⁴ · Tr D⁴`, with `ABCD := (AB)(CD)` and `x⁴ := (x·x)·(x·x)`. -/
theorem trace_holder4 (n : Nat) {A B C D : Mat} (hA : Symm A) (hB : Symm B) (hC : Symm C) (hD : Symm D) :
    let t := tr n (mmul n (mmul n A B) (mmul n C D))
    (t * t) * (t * t) ≤
      (tr n (pow4 n A) * tr n (pow4 n B)) * (tr n (pow4 n C) * tr n (pow4 n D)) := by
  intro t
  let p := tr n (mmul n (mmul n A A) (mmul n B B))
  let q := tr n (mmul n (mmul n C C) (mmul n D D))
  have hp : (0 : Q') ≤ p := tr_sq_nonneg n hA hB
  have hq : (0 : Q') ≤ q := tr_sq_nonneg n hC hD
  -- level 1: t² ≤ p q
  have l1 : t * t ≤ p * q := by
    have h := dsum_cs n (fun i c => mmul n A B i c) (fun i c => mmul n C D c i)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_refl _)) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_))
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (sq_sum_ab n hA hB))
      (Q'.mul_eqv_congr_left _ _ _ ?_)
    refine Q'.eqv_trans _ _ _ (dsum_swap n _) ?_
    exact sq_sum_ab n hC hD
  -- level 2: p² ≤ Tr A⁴ Tr B⁴ and q² ≤ Tr C⁴ Tr D⁴
  have l2p : p * p ≤ tr n (pow4 n A) * tr n (pow4 n B) := trace_cs n (symm_sq n hA) (symm_sq n hB)
  have l2q : q * q ≤ tr n (pow4 n C) * tr n (pow4 n D) := trace_cs n (symm_sq n hC) (symm_sq n hD)
  have hpq : (0 : Q') ≤ p * q := Q'.mul_nonneg _ _ hp hq
  have s1 : (t * t) * (t * t) ≤ (p * q) * (p * q) :=
    Q'.mul_le_mul_of_nonneg l1 l1 hpq (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg t)
  have e : ((p * q) * (p * q)) ≈ ((p * p) * (q * q)) :=
    YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun k => if k = 0 then p else q)
  refine Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_)
  exact Q'.mul_le_mul_of_nonneg l2p l2q
    (Q'.le_trans' _ _ _ (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg p) l2p)
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg q)

end YMGap.Continuum.FiniteTransferTrace
#print axioms YMGap.Continuum.FiniteTransferTrace.finSum_nonneg
#print axioms YMGap.Continuum.FiniteTransferTrace.finSum_congr
#print axioms YMGap.Continuum.FiniteTransferTrace.dsum
#print axioms YMGap.Continuum.FiniteTransferTrace.dsum_congr
#print axioms YMGap.Continuum.FiniteTransferTrace.dsum_add
#print axioms YMGap.Continuum.FiniteTransferTrace.dsum_smul
#print axioms YMGap.Continuum.FiniteTransferTrace.dsum_nonneg
#print axioms YMGap.Continuum.FiniteTransferTrace.dsum_swap
#print axioms YMGap.Continuum.FiniteTransferTrace.dsum_cs
#print axioms YMGap.Continuum.FiniteTransferTrace.mmul
#print axioms YMGap.Continuum.FiniteTransferTrace.tr
#print axioms YMGap.Continuum.FiniteTransferTrace.Symm
#print axioms YMGap.Continuum.FiniteTransferTrace.tr_congr
#print axioms YMGap.Continuum.FiniteTransferTrace.mmul_congr
#print axioms YMGap.Continuum.FiniteTransferTrace.mmul_assoc
#print axioms YMGap.Continuum.FiniteTransferTrace.tr_cyc
#print axioms YMGap.Continuum.FiniteTransferTrace.mmul_transpose
#print axioms YMGap.Continuum.FiniteTransferTrace.symm_sq
#print axioms YMGap.Continuum.FiniteTransferTrace.gram
#print axioms YMGap.Continuum.FiniteTransferTrace.gram_symm
#print axioms YMGap.Continuum.FiniteTransferTrace.qform
#print axioms YMGap.Continuum.FiniteTransferTrace.finSum_mul_finSum
#print axioms YMGap.Continuum.FiniteTransferTrace.gram_psd
#print axioms YMGap.Continuum.FiniteTransferTrace.tupSum
#print axioms YMGap.Continuum.FiniteTransferTrace.tupSum_congr
#print axioms YMGap.Continuum.FiniteTransferTrace.tupSum_smul
#print axioms YMGap.Continuum.FiniteTransferTrace.chain
#print axioms YMGap.Continuum.FiniteTransferTrace.tpow
#print axioms YMGap.Continuum.FiniteTransferTrace.Zper
#print axioms YMGap.Continuum.FiniteTransferTrace.chain_sum
#print axioms YMGap.Continuum.FiniteTransferTrace.partition_trace
#print axioms YMGap.Continuum.FiniteTransferTrace.tr_mmul
#print axioms YMGap.Continuum.FiniteTransferTrace.trace_cs
#print axioms YMGap.Continuum.FiniteTransferTrace.sq_sum_ab
#print axioms YMGap.Continuum.FiniteTransferTrace.tr_sq_nonneg
#print axioms YMGap.Continuum.FiniteTransferTrace.pow4
#print axioms YMGap.Continuum.FiniteTransferTrace.trace_holder4
