/-
# Raising covariance for arbitrary-label Cayley transvectants

This module treats the positive-index polynomial identity and all three
zero-index boundary cases separately.  That separation is essential because
`E2` is defined by coefficient-vector pattern matching at zero.  The resulting
one-step identity is then iterated with the physical support control already
proved for lowering.
-/

import YMGap.Continuum.SU2TransvectantBinaryGramInvariant

namespace YMGap.Continuum.SU2TransvectantRaisingCovariance

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem scale_zero (q x : Q') (hx : x ≈ 0) : q * x ≈ 0 :=
  Q'.eqv_trans _ (q * 0) _ (Q'.mul_eqv_congr_left q _ _ hx)
    (Q'.mul_zero_eqv q)

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

private theorem ofNat_signed_cross (A B C D : Nat)
    (h : A + D = C + B) :
    Q'.ofNat A + -(Q'.ofNat B) ≈ Q'.ofNat C + -(Q'.ofNat D) := by
  show (Q'.ofNat A + -(Q'.ofNat B)).num *
      ((Q'.ofNat C + -(Q'.ofNat D)).den : Int) =
    (Q'.ofNat C + -(Q'.ofNat D)).num *
      ((Q'.ofNat A + -(Q'.ofNat B)).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den, neg_num_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  have hi := congrArg Int.ofNat h
  push_cast at hi ⊢
  omega

private theorem signed_product_cross
    (A B C D E F G H : Nat)
    (h : A * B + G * H = E * F + C * D) :
    Q'.ofNat A * Q'.ofNat B + -(Q'.ofNat C * Q'.ofNat D) ≈
      Q'.ofNat E * Q'.ofNat F + -(Q'.ofNat G * Q'.ofNat H) := by
  refine Q'.eqv_trans _
    (Q'.ofNat (A * B) + -(Q'.ofNat (C * D))) _
    (Q'.add_eqv_congr' (ofNat_mul_eqv A B)
      (Q'.neg_eqv_congr _ _ (ofNat_mul_eqv C D))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (E * F) + -(Q'.ofNat (G * H))) _
    (ofNat_signed_cross _ _ _ _ h) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm (ofNat_mul_eqv E F))
    (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (ofNat_mul_eqv G H)))

private theorem product3_ac (A B C D E F : Nat)
    (h : A * B * C = D * E * F) :
    (Q'.ofNat A * Q'.ofNat B) * Q'.ofNat C ≈
      (Q'.ofNat D * Q'.ofNat E) * Q'.ofNat F := by
  refine Q'.eqv_trans _ (Q'.ofNat (A * B * C)) _
    (Q'.eqv_trans _ (Q'.ofNat (A * B) * Q'.ofNat C) _
      (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv A B))
      (ofNat_mul_eqv _ _)) ?_
  rw [h]
  exact Q'.eqv_symm
    (Q'.eqv_trans _ (Q'.ofNat (D * E) * Q'.ofNat F) _
      (ofNat_mul_eqv _ _) (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (ofNat_mul_eqv D E))))

private theorem product2_ac (A B C D : Nat) (h : A * B = C * D) :
    Q'.ofNat A * Q'.ofNat B ≈ Q'.ofNat C * Q'.ofNat D := by
  refine Q'.eqv_trans _ (Q'.ofNat (A * B)) _ (ofNat_mul_eqv A B) ?_
  rw [h]
  exact Q'.eqv_symm (ofNat_mul_eqv C D)

private def sourceExpandLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.mul (.var 1) (.var 6))
      (.mul (.var 2) (.var 7))))
    (.neg (.mul (.var 3) (.add (.mul (.var 4) (.var 8))
      (.mul (.var 5) (.var 6)))))

private def sourceExpandRHS : PolyExpr :=
  .add
    (.add
      (.mul (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 3) (.var 5)))) (.var 6))
      (.mul (.mul (.var 0) (.var 2)) (.var 7)))
    (.mul (.neg (.mul (.var 3) (.var 4))) (.var 8))

private theorem sourceExpand_normal :
    normalize sourceExpandLHS = normalize sourceExpandRHS := by decide

private def expandEnv
    (A M NP B MP N x y z : Q') : Nat → Q'
  | 0 => A | 1 => M | 2 => NP | 3 => B | 4 => MP | 5 => N
  | 6 => x | 7 => y | _ => z

private theorem source_expand
    (A M NP B MP N x y z : Q') :
    A * (M * x + NP * y) + -(B * (MP * z + N * x)) ≈
      (A * M + -(B * N)) * x + (A * NP) * y +
        (-(B * MP)) * z := by
  have h := poly_identity_of_normal_eq sourceExpandLHS sourceExpandRHS
    sourceExpand_normal (expandEnv A M NP B MP N x y z)
  simpa only [sourceExpandLHS, sourceExpandRHS, expandEnv, eval] using h

private def targetExpandLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.mul (.var 1) (.var 6))
      (.neg (.mul (.var 2) (.var 8)))))
    (.mul (.var 3) (.add (.mul (.var 4) (.var 7))
      (.neg (.mul (.var 5) (.var 6)))))

private def targetExpandRHS : PolyExpr :=
  .add
    (.add
      (.mul (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 3) (.var 5)))) (.var 6))
      (.mul (.mul (.var 3) (.var 4)) (.var 7)))
    (.mul (.neg (.mul (.var 0) (.var 2))) (.var 8))

private theorem targetExpand_normal :
    normalize targetExpandLHS = normalize targetExpandRHS := by decide

private theorem target_expand
    (M C D N E F x y z : Q') :
    M * (C * x + -(D * z)) + N * (E * y + -(F * x)) ≈
      (M * C + -(N * F)) * x + (N * E) * y +
        (-(M * D)) * z := by
  have h := poly_identity_of_normal_eq targetExpandLHS targetExpandRHS
    targetExpand_normal (expandEnv M C D N E F x y z)
  simpa only [targetExpandLHS, targetExpandRHS, expandEnv, eval] using h

/-- The positive-positive coefficient identity, written with successor slots
so no pattern-match simplification is hidden. -/
theorem omega_E2_comm_succ_succ (m n i j : Nat) (c : BForm2)
    (hi : i + 1 < m) (hj : j + 1 < n) :
    Omega m n (E2 m n c) (i + 1) (j + 1) ≈
      E2 (m - 1) (n - 1) (Omega m n c) (i + 1) (j + 1) := by
  let x := c (i + 1) (j + 1)
  let y := c (i + 2) j
  let z := c i (j + 2)
  let A := Q'.ofNat ((i + 2) * (n - (j + 1)))
  let B := Q'.ofNat ((m - (i + 1)) * (j + 2))
  let M := Q'.ofNat (m - (i + 1))
  let N := Q'.ofNat (n - (j + 1))
  let NP := Q'.ofNat (n - j)
  let MP := Q'.ofNat (m - i)
  let C := Q'.ofNat ((i + 1) * (n - (j + 1)))
  let D := Q'.ofNat ((m - i) * (j + 2))
  let E := Q'.ofNat ((i + 2) * (n - j))
  let F := Q'.ofNat ((m - (i + 1)) * (j + 1))
  have hL := source_expand A M NP B MP N x y z
  have hR := target_expand M C D N E F x y z
  have hx : A * M + -(B * N) ≈ M * C + -(N * F) := by
    dsimp only [A, B, M, N, C, F]
    apply signed_product_cross
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    ac_rfl
  have hy : A * NP ≈ N * E := by
    dsimp only [A, NP, N, E]
    apply product2_ac
    ac_rfl
  have hz : -(B * MP) ≈ -(M * D) := by
    apply Q'.neg_eqv_congr
    dsimp only [B, MP, M, D]
    apply product2_ac
    ac_rfl
  change
    Q'.ofNat ((i + 2) * (n - (j + 1))) *
        (Q'.ofNat (m - (i + 1)) * c (i + 1) (j + 1) +
          Q'.ofNat (n - j) * c (i + 2) j) +
      -(Q'.ofNat ((m - (i + 1)) * (j + 2)) *
        (Q'.ofNat (m - i) * c i (j + 2) +
          Q'.ofNat (n - (j + 1)) * c (i + 1) (j + 1))) ≈
    Q'.ofNat ((m - 1) - i) *
        (Q'.ofNat ((i + 1) * (n - (j + 1))) * c (i + 1) (j + 1) +
          -(Q'.ofNat ((m - i) * (j + 2)) * c i (j + 2))) +
      Q'.ofNat ((n - 1) - j) *
        (Q'.ofNat ((i + 2) * (n - j)) * c (i + 2) j +
          -(Q'.ofNat ((m - (i + 1)) * (j + 1)) * c (i + 1) (j + 1)))
  rw [show (m - 1) - i = m - (i + 1) by omega,
    show (n - 1) - j = n - (j + 1) by omega]
  refine Q'.eqv_trans _
    ((A * M + -(B * N)) * x + (A * NP) * y + (-(B * MP)) * z) _
    (by simpa only [A, B, M, N, NP, MP, x, y, z] using hL) ?_
  refine Q'.eqv_trans _
    ((M * C + -(N * F)) * x + (N * E) * y + (-(M * D)) * z) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ x hx)
        (Q'.mul_eqv_congr_right _ _ y hy))
      (Q'.mul_eqv_congr_right _ _ z hz)
  · exact Q'.eqv_symm (by
      simpa only [M, C, D, N, E, F, x, y, z] using hR)

private theorem cancel_comm_blocks (A B x : Q') :
    A * (B * x + 0) + -(B * (0 + A * x)) ≈ 0 := by
  have h1 : A * (B * x + 0) ≈ (A * B) * x := by
    refine Q'.eqv_trans _ (A * (B * x)) _
      (Q'.mul_eqv_congr_left A _ _ (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv A B x)
  have h2 : B * (0 + A * x) ≈ (A * B) * x := by
    refine Q'.eqv_trans _ (B * (A * x)) _
      (Q'.mul_eqv_congr_left B _ _ (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
    refine Q'.eqv_trans _ ((B * A) * x) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv B A x)) ?_
    exact Q'.mul_eqv_congr_right _ _ x (Q'.mul_comm_eqv B A)
  refine Q'.eqv_trans _ ((A * B) * x + -((A * B) * x)) _
    (Q'.add_eqv_congr' h1 (Q'.neg_eqv_congr _ _ h2)) ?_
  refine Q'.eqv_trans _ (-((A * B) * x) + (A * B) * x) _
    (Q'.add_comm_eqv _ _) ?_
  exact Q'.neg_add_self_eqv _

/-- The corner boundary is a genuine cancellation, not a vacuous support
case: the two mixed derivatives are `n*m` and `m*n`. -/
theorem omega_E2_comm_zero_zero (m n : Nat) (c : BForm2) :
    Omega m n (E2 m n c) 0 0 ≈
      E2 (m - 1) (n - 1) (Omega m n c) 0 0 := by
  unfold Omega E2
  simp only [Nat.zero_add, Nat.sub_zero, Nat.add_zero, Nat.one_mul, Nat.mul_one]
  change
    Q'.ofNat n * (Q'.ofNat m * c 0 0 + 0) +
        -(Q'.ofNat m * (0 + Q'.ofNat n * c 0 0)) ≈ 0 + 0
  refine Q'.eqv_trans _ 0 _ (cancel_comm_blocks _ _ _) ?_
  exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem mul_zero_eqv (A : Q') : A * 0 ≈ 0 := Q'.mul_zero_eqv A

/-- Boundary covariance on the left edge (`a=0`, `b>0`). -/
theorem omega_E2_comm_zero_succ (m n j : Nat) (c : BForm2)
    (hj : j + 1 < n) :
    Omega m n (E2 m n c) 0 (j + 1) ≈
      E2 (m - 1) (n - 1) (Omega m n c) 0 (j + 1) := by
  let x := c 0 (j + 1)
  let y := c 1 j
  let z : Q' := 0
  let A := Q'.ofNat (n - (j + 1))
  let B := Q'.ofNat (m * (j + 2))
  let M := Q'.ofNat m
  let NP := Q'.ofNat (n - j)
  let F := Q'.ofNat (m * (j + 1))
  have hL := source_expand A M NP B 0 A x y z
  have hR := target_expand 0 0 0 A NP F x y z
  have hx : A * M + -(B * A) ≈ 0 * 0 + -(A * F) := by
    have hcore : A * M + -(B * A) ≈ Q'.ofNat 0 + -(A * F) := by
      dsimp only [A, M, B, F]
      refine Q'.eqv_trans _
        (Q'.ofNat ((n - (j + 1)) * m) +
          -(Q'.ofNat ((m * (j + 2)) * (n - (j + 1))))) _
        (Q'.add_eqv_congr' (ofNat_mul_eqv _ _)
          (Q'.neg_eqv_congr _ _ (ofNat_mul_eqv _ _))) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat 0 +
          -(Q'.ofNat ((n - (j + 1)) * (m * (j + 1))))) _ ?_ ?_
      · apply ofNat_signed_cross
        rw [show j + 2 = (j + 1) + 1 by omega]
        simp only [Nat.zero_add, Nat.add_mul, Nat.mul_add, Nat.one_mul,
          Nat.mul_one]
        ac_rfl
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (ofNat_mul_eqv _ _)))
    refine Q'.eqv_trans _ _ _ hcore ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ ((0 : Q') * 0) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv 0)))
  have hz : -(B * 0) ≈ -(0 * 0) :=
    Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ 0 _ (mul_zero_eqv B)
        (Q'.eqv_symm (Q'.zero_mul_eqv 0)))
  unfold Omega E2
  simp only [Nat.zero_add, Nat.sub_zero, Nat.add_zero, Nat.one_mul, Nat.mul_one]
  change
    Q'.ofNat (n - (j + 1)) *
        (Q'.ofNat m * c 0 (j + 1) + Q'.ofNat (n - j) * c 1 j) +
      -(Q'.ofNat (m * (j + 2)) *
        (0 + Q'.ofNat (n - (j + 1)) * c 0 (j + 1))) ≈
    0 + Q'.ofNat ((n - 1) - j) *
      (Q'.ofNat (n - j) * c 1 j +
        -(Q'.ofNat (m * (j + 1)) * c 0 (j + 1)))
  rw [show (n - 1) - j = n - (j + 1) by omega]
  refine Q'.eqv_trans _
    ((A * M + -(B * A)) * x + (A * NP) * y + (-(B * 0)) * z) _
    (by simpa only [A, B, M, NP, x, y, z] using hL) ?_
  refine Q'.eqv_trans _
    ((0 * 0 + -(A * F)) * x + (A * NP) * y + (-(0 * 0)) * z) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ x hx) (Q'.eqv_refl _))
      (Q'.mul_eqv_congr_right _ _ z hz)
  · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hR) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _)

/-- Boundary covariance on the bottom edge (`a>0`, `b=0`). -/
theorem omega_E2_comm_succ_zero (m n i : Nat) (c : BForm2)
    (hi : i + 1 < m) :
    Omega m n (E2 m n c) (i + 1) 0 ≈
      E2 (m - 1) (n - 1) (Omega m n c) (i + 1) 0 := by
  let x := c (i + 1) 0
  let y : Q' := 0
  let z := c i 1
  let A := Q'.ofNat ((i + 2) * n)
  let B := Q'.ofNat (m - (i + 1))
  let M := Q'.ofNat (m - (i + 1))
  let N := Q'.ofNat n
  let MP := Q'.ofNat (m - i)
  let C := Q'.ofNat ((i + 1) * n)
  let D := Q'.ofNat (m - i)
  have hL := source_expand A M 0 B MP N x y z
  have hR := target_expand M C D 0 0 0 x y z
  have hx : A * M + -(B * N) ≈ M * C + -(0 * 0) := by
    have hcore : A * M + -(B * N) ≈ M * C + -(Q'.ofNat 0) := by
      dsimp only [A, M, B, N, C]
      refine Q'.eqv_trans _
        (Q'.ofNat (((i + 2) * n) * (m - (i + 1))) +
          -(Q'.ofNat ((m - (i + 1)) * n))) _
        (Q'.add_eqv_congr' (ofNat_mul_eqv _ _)
          (Q'.neg_eqv_congr _ _ (ofNat_mul_eqv _ _))) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat ((m - (i + 1)) * ((i + 1) * n)) +
          -(Q'.ofNat 0)) _ ?_ ?_
      · apply ofNat_signed_cross
        rw [show i + 2 = (i + 1) + 1 by omega]
        simp only [Nat.add_zero, Nat.add_mul, Nat.mul_add, Nat.one_mul,
          Nat.mul_one]
        ac_rfl
      · exact Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (ofNat_mul_eqv _ _))
    refine Q'.eqv_trans _ _ _ hcore ?_
    apply Q'.add_eqv_congr_left
    exact Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ 0 _ Q'.ofNat_zero_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv 0)))
  have hz : -(B * MP) ≈ -(M * D) := by
    dsimp only [B, MP, M, D]
    exact Q'.eqv_refl _
  unfold Omega E2
  simp only [Nat.zero_add, Nat.sub_zero, Nat.add_zero, Nat.one_mul, Nat.mul_one,
    Nat.add_assoc]
  change
    Q'.ofNat ((i + 2) * n) *
        (Q'.ofNat (m - (i + 1)) * c (i + 1) 0 + 0) +
      -(Q'.ofNat (m - (i + 1)) *
        (Q'.ofNat (m - i) * c i 1 + Q'.ofNat n * c (i + 1) 0)) ≈
    Q'.ofNat ((m - 1) - i) *
        (Q'.ofNat ((i + 1) * n) * c (i + 1) 0 +
          -(Q'.ofNat (m - i) * c i 1)) + 0
  rw [show (m - 1) - i = m - (i + 1) by omega]
  refine Q'.eqv_trans _
    ((A * M + -(B * N)) * x + (A * 0) * y + (-(B * MP)) * z) _
    (by simpa only [A, B, M, N, MP, x, y, z] using hL) ?_
  refine Q'.eqv_trans _
    ((M * C + -(0 * 0)) * x + (0 * 0) * y + (-(M * D)) * z) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ x hx)
        (Q'.mul_eqv_congr_right _ _ y
          (Q'.eqv_trans _ 0 _ (mul_zero_eqv A)
            (Q'.eqv_symm (Q'.zero_mul_eqv 0)))))
      (Q'.mul_eqv_congr_right _ _ z hz)
  · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hR) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)

/-- Complete one-step raising covariance on the physical residual rectangle,
assembled from the four genuinely different coefficient-vector boundaries. -/
theorem omega_E2_comm (m n a b : Nat) (c : BForm2)
    (ha : a < m) (hb : b < n) :
    Omega m n (E2 m n c) a b ≈
      E2 (m - 1) (n - 1) (Omega m n c) a b := by
  cases a with
  | zero =>
      cases b with
      | zero => exact omega_E2_comm_zero_zero m n c
      | succ j => exact omega_E2_comm_zero_succ m n j c hb
  | succ i =>
      cases b with
      | zero => exact omega_E2_comm_succ_zero m n i c ha
      | succ j => exact omega_E2_comm_succ_succ m n i j c ha hb

/-- Total raising preserves a physical bidegree rectangle. -/
private theorem raise_first_zero (m n i b : Nat) {c : BForm2}
    (hc : BidegreeSupported m n c) (hab : m < i + 1 ∨ n < b) :
    Q'.ofNat (m - i) * c i b ≈ 0 := by
  rcases hab with ha | hb
  · by_cases hmi : i = m
    · subst i
      simp only [Nat.sub_self]
      exact Q'.eqv_trans _ ((0 : Q') * c m b) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    · exact scale_zero _ _ (hc i b (by omega))
  · exact scale_zero _ _ (hc i b (Or.inr hb))

private theorem raise_second_zero (m n a j : Nat) {c : BForm2}
    (hc : BidegreeSupported m n c) (hab : m < a ∨ n < j + 1) :
    Q'.ofNat (n - j) * c a j ≈ 0 := by
  rcases hab with ha | hb
  · exact scale_zero _ _ (hc a j (Or.inl ha))
  · by_cases hjn : j = n
    · subst j
      simp only [Nat.sub_self]
      exact Q'.eqv_trans _ ((0 : Q') * c a n) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    · exact scale_zero _ _ (hc a j (by omega))

theorem E2_supported (m n : Nat) {c : BForm2}
    (hc : BidegreeSupported m n c) :
    BidegreeSupported m n (E2 m n c) := by
  intro a b hab
  cases a with
  | zero =>
      cases b with
      | zero => omega
      | succ j =>
          unfold E2
          refine Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (raise_second_zero m n 0 j hc hab)) ?_
          exact Q'.eqv_of_eq (Q'.zero_add' 0)
  | succ i =>
      cases b with
      | zero =>
          unfold E2
          refine Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr'
              (raise_first_zero m n i 0 hc hab) (Q'.eqv_refl 0)) ?_
          exact Q'.eqv_of_eq (Q'.zero_add' 0)
      | succ j =>
          unfold E2
          refine Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr'
              (raise_first_zero m n i (j + 1) hc hab)
              (raise_second_zero m n (i + 1) j hc hab)) ?_
          exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- Iterated Cayley contraction commutes with raising on the physical forward
box. -/
theorem omegaK_E2_comm : ∀ k m n a b : Nat, ∀ c : BForm2,
    a + k ≤ m → b + k ≤ n →
      OmegaK m n k (E2 m n c) a b ≈
        E2 (m - k) (n - k) (OmegaK m n k c) a b
  | 0, m, n, a, b, c, _, _ => Q'.eqv_refl _
  | k + 1, m, n, a, b, c, hm, hn => by
      have hbox : ∀ i, i ≤ a + k → ∀ j, j ≤ b + k →
          Omega m n (E2 m n c) i j ≈
            E2 (m - 1) (n - 1) (Omega m n c) i j := by
        intro i hi j hj
        exact omega_E2_comm m n i j c (by omega) (by omega)
      have h0 :=
        YMGap.Continuum.SU2TransvectantRowToFullGram.omegaK_congr_forward_box
          k (m - 1) (n - 1) a b
          (Omega m n (E2 m n c))
          (E2 (m - 1) (n - 1) (Omega m n c)) hbox
      have h1 := omegaK_E2_comm k (m - 1) (n - 1) a b (Omega m n c)
        (by omega) (by omega)
      refine Q'.eqv_trans _ _ _ h0 ?_
      simpa only [OmegaK, show m - (k + 1) = (m - 1) - k by omega,
        show n - (k + 1) = (n - 1) - k by omega] using h1

/-- Raising covariance is global on a supported input; outside the residual
rectangle both sides vanish. -/
theorem omegaK_E2_comm_supported (m n k a b : Nat) (c : BForm2)
    (hm : k ≤ m) (hn : k ≤ n) (hc : BidegreeSupported m n c) :
    OmegaK m n k (E2 m n c) a b ≈
      E2 (m - k) (n - k) (OmegaK m n k c) a b := by
  by_cases ha : a + k ≤ m
  · by_cases hb : b + k ≤ n
    · exact omegaK_E2_comm k m n a b c ha hb
    · have hleftSupport := omegaK_supported k m n (E2 m n c) hm hn
        (E2_supported m n hc)
      have hrightSupport := E2_supported (m - k) (n - k)
        (omegaK_supported k m n c hm hn hc)
      have hleft := hleftSupport a b (by omega)
      have hright := hrightSupport a b (by omega)
      exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)
  · have hleftSupport := omegaK_supported k m n (E2 m n c) hm hn
      (E2_supported m n hc)
    have hrightSupport := E2_supported (m - k) (n - k)
      (omegaK_supported k m n c hm hn hc)
    have hleft := hleftSupport a b (by omega)
    have hright := hrightSupport a b (by omega)
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)

end YMGap.Continuum.SU2TransvectantRaisingCovariance

#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.omega_E2_comm_succ_succ
#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.omega_E2_comm_zero_zero
#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.omega_E2_comm_zero_succ
#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.omega_E2_comm_succ_zero
#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.omega_E2_comm
#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.E2_supported
#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.omegaK_E2_comm
#print axioms YMGap.Continuum.SU2TransvectantRaisingCovariance.omegaK_E2_comm_supported
