/-
# Supported lowering covariance toward the binary Cayley Gram

This successor adds physical bidegree support to the exact lowering machinery
in `SU2TransvectantRowToFullGram` and proves the corresponding global
lowering-intertwining statement.  The raising boundary calculation, normalized
row constancy, and final binary Hilbert--Schmidt multiplier are deliberately
left to successor modules.
-/

import YMGap.Continuum.SU2TransvectantRowToFullGram

namespace YMGap.Continuum.SU2TransvectantBinaryGramInvariant

set_option maxHeartbeats 1800000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2TransvectantRowToFullGram
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- A two-factor coefficient array is supported in the physical bidegree
rectangle `[0,m] x [0,n]`. -/
def BidegreeSupported (m n : Nat) (c : BForm2) : Prop :=
  ∀ a b, (m < a ∨ n < b) → c a b ≈ 0

private theorem scale_zero (q x : Q') (hx : x ≈ 0) : q * x ≈ 0 :=
  Q'.eqv_trans _ (q * 0) _ (Q'.mul_eqv_congr_left q _ _ hx)
    (Q'.mul_zero_eqv q)

/-- Total lowering preserves the physical bidegree rectangle. -/
theorem F2_supported (m n : Nat) {c : BForm2}
    (hc : BidegreeSupported m n c) :
    BidegreeSupported m n (F2 m n c) := by
  intro a b hab
  unfold F2
  have h0 : c (a + 1) b ≈ 0 := hc (a + 1) b (by omega)
  have h1 : c a (b + 1) ≈ 0 := hc a (b + 1) (by omega)
  refine Q'.eqv_trans _ (0 + 0) _
    (Q'.add_eqv_congr' (scale_zero _ _ h0) (scale_zero _ _ h1)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- One Cayley contraction lowers each physical bidegree by one. -/
theorem omega_supported (m n : Nat) {c : BForm2}
    (hm : 0 < m) (hn : 0 < n) (hc : BidegreeSupported m n c) :
    BidegreeSupported (m - 1) (n - 1) (Omega m n c) := by
  intro a b hab
  unfold Omega
  have hfirst :
      Q'.ofNat ((a + 1) * (n - b)) * c (a + 1) b ≈ 0 := by
    rcases hab with ha | hb
    · exact scale_zero _ _ (hc (a + 1) b (by omega))
    · have hnb : n - b = 0 := by omega
      rw [hnb, Nat.mul_zero]
      exact Q'.eqv_trans _ ((0 : Q') * c (a + 1) b) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
  have hsecond :
      Q'.ofNat ((m - a) * (b + 1)) * c a (b + 1) ≈ 0 := by
    rcases hab with ha | hb
    · have hma : m - a = 0 := by omega
      rw [hma, Nat.zero_mul]
      exact Q'.eqv_trans _ ((0 : Q') * c a (b + 1)) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    · exact scale_zero _ _ (hc a (b + 1) (by omega))
  exact Q'.eqv_trans _ (0 + (-0)) _
    (Q'.add_eqv_congr' hfirst (Q'.neg_eqv_congr _ _ hsecond)) (by decide)

/-- Every admissible iterate of `Omega` has the expected residual support. -/
theorem omegaK_supported : ∀ k m n : Nat, ∀ c : BForm2,
    k ≤ m → k ≤ n → BidegreeSupported m n c →
      BidegreeSupported (m - k) (n - k) (OmegaK m n k c)
  | 0, m, n, c, _, _, hc => hc
  | k + 1, m, n, c, hm, hn, hc => by
      have hstep := omega_supported m n (by omega) (by omega) hc
      have ih := omegaK_supported k (m - 1) (n - 1) (Omega m n c)
        (by omega) (by omega) hstep
      simpa only [OmegaK, show m - (k + 1) = (m - 1) - k by omega,
        show n - (k + 1) = (n - 1) - k by omega] using ih

/-- Pure tensor monomials in the degree windows have physical support. -/
theorem tprod_mono_supported (m n i j : Nat) (hi : i ≤ m) (hj : j ≤ n) :
    BidegreeSupported m n (tprod (mono i) (mono j)) := by
  intro a b hab
  unfold tprod mono
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      omega
    · rw [if_pos rfl, if_neg hbj]
      exact Q'.mul_zero_eqv 1
  · rw [if_neg hai]
    exact Q'.zero_mul_eqv _

/-- Lowering covariance is global once the input has physical support; outside
the residual rectangle both sides vanish. -/
theorem omegaK_F2_comm_supported (m n k a b : Nat) (c : BForm2)
    (hm : k ≤ m) (hn : k ≤ n) (hc : BidegreeSupported m n c) :
    OmegaK m n k (F2 m n c) a b ≈
      F2 (m - k) (n - k) (OmegaK m n k c) a b := by
  by_cases ha : a + k ≤ m
  · by_cases hb : b + k ≤ n
    · exact omegaK_F2_comm k m n a b c ha hb
    · have hleftSupport := omegaK_supported k m n (F2 m n c) hm hn
        (F2_supported m n hc)
      have hrightSupport := F2_supported (m - k) (n - k)
        (omegaK_supported k m n c hm hn hc)
      have hleft := hleftSupport a b (by omega)
      have hright := hrightSupport a b (by omega)
      exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)
  · have hleftSupport := omegaK_supported k m n (F2 m n c) hm hn
      (F2_supported m n hc)
    have hrightSupport := F2_supported (m - k) (n - k)
      (omegaK_supported k m n c hm hn hc)
    have hleft := hleftSupport a b (by omega)
    have hright := hrightSupport a b (by omega)
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)

/-- The all-order Cayley transvectant commutes with lowering on every
physically supported input. -/
theorem transvect_F2_supported (m n k s : Nat) (c : BForm2)
    (hm : k ≤ m) (hn : k ≤ n) (hc : BidegreeSupported m n c) :
    transvect m n k (F2 m n c) s ≈
      Fop (m + n - 2 * k) (transvect m n k c) s := by
  have hpoint : BForm2Eqv
      (OmegaK m n k (F2 m n c))
      (F2 (m - k) (n - k) (OmegaK m n k c)) :=
    fun a b => omegaK_F2_comm_supported m n k a b c hm hn hc
  have hdiag := diag_congr hpoint s
  have hF := diag_F2 (m - k) (n - k) s (OmegaK m n k c)
  refine Q'.eqv_trans _ _ _ hdiag ?_
  simpa only [transvect,
    show (m - k) + (n - k) = m + n - 2 * k by omega] using hF

/-! ## Algebraic preparation for raising covariance -/

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


private def raiseSourceExpandLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.mul (.var 1) (.var 6))
      (.mul (.var 2) (.var 7))))
    (.neg (.mul (.var 3) (.add (.mul (.var 4) (.var 8))
      (.mul (.var 5) (.var 6)))))

private def raiseSourceExpandRHS : PolyExpr :=
  .add
    (.add
      (.mul (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 3) (.var 5)))) (.var 6))
      (.mul (.mul (.var 0) (.var 2)) (.var 7)))
    (.mul (.neg (.mul (.var 3) (.var 4))) (.var 8))

private theorem raiseSourceExpand_normal :
    normalize raiseSourceExpandLHS = normalize raiseSourceExpandRHS := by decide


private def raiseExpandEnv
    (A M NP B MP N x y z : Q') : Nat → Q'
  | 0 => A | 1 => M | 2 => NP | 3 => B | 4 => MP | 5 => N
  | 6 => x | 7 => y | _ => z

private theorem raise_source_expand
    (A M NP B MP N x y z : Q') :
    A * (M * x + NP * y) + -(B * (MP * z + N * x)) ≈
      (A * M + -(B * N)) * x + (A * NP) * y +
        (-(B * MP)) * z := by
  have h := poly_identity_of_normal_eq raiseSourceExpandLHS raiseSourceExpandRHS
    raiseSourceExpand_normal (raiseExpandEnv A M NP B MP N x y z)
  simpa only [raiseSourceExpandLHS, raiseSourceExpandRHS,
    raiseExpandEnv, eval] using h

private def raiseTargetExpandLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.mul (.var 1) (.var 6))
      (.neg (.mul (.var 2) (.var 8)))))
    (.mul (.var 3) (.add (.mul (.var 4) (.var 7))
      (.neg (.mul (.var 5) (.var 6)))))

private def raiseTargetExpandRHS : PolyExpr :=
  .add
    (.add
      (.mul (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 3) (.var 5)))) (.var 6))
      (.mul (.mul (.var 3) (.var 4)) (.var 7)))
    (.mul (.neg (.mul (.var 0) (.var 2))) (.var 8))

private theorem raiseTargetExpand_normal :
    normalize raiseTargetExpandLHS = normalize raiseTargetExpandRHS := by decide


private theorem raise_target_expand
    (M C D N E F x y z : Q') :
    M * (C * x + -(D * z)) + N * (E * y + -(F * x)) ≈
      (M * C + -(N * F)) * x + (N * E) * y +
        (-(M * D)) * z := by
  have h := poly_identity_of_normal_eq raiseTargetExpandLHS raiseTargetExpandRHS
    raiseTargetExpand_normal (raiseExpandEnv M C D N E F x y z)
  simpa only [raiseTargetExpandLHS, raiseTargetExpandRHS,
    raiseExpandEnv, eval] using h

end YMGap.Continuum.SU2TransvectantBinaryGramInvariant

#print axioms YMGap.Continuum.SU2TransvectantBinaryGramInvariant.F2_supported
#print axioms YMGap.Continuum.SU2TransvectantBinaryGramInvariant.omega_supported
#print axioms YMGap.Continuum.SU2TransvectantBinaryGramInvariant.omegaK_supported
#print axioms YMGap.Continuum.SU2TransvectantBinaryGramInvariant.tprod_mono_supported
#print axioms YMGap.Continuum.SU2TransvectantBinaryGramInvariant.omegaK_F2_comm_supported
#print axioms YMGap.Continuum.SU2TransvectantBinaryGramInvariant.transvect_F2_supported
