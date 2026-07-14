/-
# Uniform input-swap parity of the Cayley transvectant

Transposing the two tensor inputs negates one Cayley `Omega` step.  Iteration
therefore contributes the exact recursive sign `(-1)^k`, while diagonal
restriction is invariant under transposition by finite anti-diagonal
reversal.  The result is the all-degree, all-order raw transvectant swap law
needed to bridge cyclic coordinate charts to fixed ordered normalization.
-/

import YMGap.Continuum.SU2TransvectantLinearity

namespace YMGap.Continuum.SU2TransvectantSwapParity

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity

local infix:50 " ≈ " => Q'.eqv

/-- Transpose the two tensor factors. -/
def transpose2 (x : BForm2) : BForm2 := fun i j => x j i

/-- Exact recursive parity phase: `1,-1,1,-1,...`. -/
def swapPhase : Nat → Q'
  | 0 => 1
  | k + 1 => -(swapPhase k)

private theorem neg_one_mul (x : Q') : (-1 : Q') * x ≈ -x := by
  exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 x)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv x))

private theorem reverse_sub (x y : Q') : y + (-x) ≈ -(x + (-y)) := by
  refine Q'.eqv_trans _ (-x + y) _ (Q'.add_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ (-x + (-(-y))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (-x) _ _
      (Q'.eqv_symm (Q'.neg_neg_eqv y))
  · exact Q'.eqv_symm (Q'.neg_add_eqv x (-y))

/-- One Cayley step is antisymmetric under tensor transposition. -/
theorem omega_transpose (m n : Nat) (x : BForm2) :
    BForm2Eqv (Omega n m (transpose2 x))
      (bscale (-1) (transpose2 (Omega m n x))) := by
  intro i j
  unfold Omega transpose2 bscale
  rw [Nat.mul_comm (i + 1) (m - j), Nat.mul_comm (n - i) (j + 1)]
  let X := Q'.ofNat ((j + 1) * (n - i)) * x (j + 1) i
  let Y := Q'.ofNat ((m - j) * (i + 1)) * x j (i + 1)
  exact Q'.eqv_trans _ (-(X + (-Y))) _
    (by simpa only [X, Y] using reverse_sub X Y)
    (Q'.eqv_symm (neg_one_mul (X + (-Y))))

private theorem phase_step_mul (k : Nat) (x : Q') :
    (-1 : Q') * (swapPhase k * x) ≈ swapPhase (k + 1) * x := by
  refine Q'.eqv_trans _ (((-1 : Q') * swapPhase k) * x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (-1) (swapPhase k) x)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (neg_one_mul (swapPhase k))

/-- Every iterated Cayley process acquires exactly the recursive swap phase. -/
theorem omegaK_transpose (m n k : Nat) (x : BForm2) :
    BForm2Eqv (OmegaK n m k (transpose2 x))
      (bscale (swapPhase k) (transpose2 (OmegaK m n k x))) := by
  induction k generalizing m n x with
  | zero =>
      intro i j
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | succ k ih =>
      have hOmega := omega_transpose m n x
      have hcongr := omegaK_congr (n - 1) (m - 1) k hOmega
      have hscale := omegaK_scale (n - 1) (m - 1) k (-1)
        (transpose2 (Omega m n x))
      have hih := ih (m - 1) (n - 1) (Omega m n x)
      intro i j
      exact Q'.eqv_trans _ _ _ (hcongr i j)
        (Q'.eqv_trans _ _ _ (hscale i j)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (-1) _ _ (hih i j))
            (phase_step_mul k _)))

private theorem finSum_reverse (g : QSeq) : ∀ N,
    finSum g N ≈ finSum (fun i => g (N - 1 - i)) N
  | 0 => Q'.eqv_refl 0
  | N + 1 => by
      have hpeel := finSum_peel_left (fun i => g (N - i)) N
      have hrefl : (fun i => g (N + 1 - 1 - i)) =
          (fun i => g (N - i)) := by
        funext i
        congr 1 <;> omega
      have htail : (fun i => g (N - (i + 1))) =
          (fun i => g (N - 1 - i)) := by
        funext i
        congr 1 <;> omega
      have hih : finSum (fun i => g (N - 1 - i)) N ≈ finSum g N :=
        Q'.eqv_symm (finSum_reverse g N)
      rw [hrefl]
      show finSum g N + g N ≈ finSum (fun i => g (N - i)) (N + 1)
      refine Q'.eqv_trans _ (g N + finSum (fun i => g (N - 1 - i)) N) _ ?_ ?_
      · exact Q'.eqv_trans _ (g N + finSum g N) _
          (Q'.add_comm_eqv _ _)
          (Q'.add_eqv_congr_left (g N) _ _ (Q'.eqv_symm hih))
      · rw [← htail]
        exact Q'.eqv_symm hpeel

/-- Diagonal restriction is invariant under tensor transposition. -/
theorem diag_transpose (x : BForm2) :
    BFormEqv (diag (transpose2 x)) (diag x) := by
  intro s
  unfold diag transpose2
  have hrev := finSum_reverse (fun i => x i (s - i)) (s + 1)
  have htail :
      finSum (fun i => x (s + 1 - 1 - i) (s - (s + 1 - 1 - i))) (s + 1) ≈
        finSum (fun i => x (s - i) i) (s + 1) := by
    apply finSum_eqv_congr_lt
    intro i hi
    have h₁ : s + 1 - 1 - i = s - i := by omega
    rw [h₁]
    have h₂ : s - (s - i) = i := by omega
    rw [h₂]
    exact Q'.eqv_refl _
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hrev htail)

/-- Diagonal restriction commutes with exact rational scaling. -/
theorem diag_scale (q : Q') (x : BForm2) :
    BFormEqv (diag (bscale q x)) (fun s => q * diag x s) := by
  intro s
  unfold diag bscale
  exact Q'.eqv_symm
    (const_mul_finSum (fun i => x i (s - i)) q (s + 1))

/-- **Uniform raw transvectant swap law.**  Swapping the two tensor inputs of
the order-`k` Cayley transvectant multiplies every output coefficient by the
exact phase `swapPhase k`. -/
theorem transvect_transpose (m n k : Nat) (x : BForm2) :
    ∀ s, transvect n m k (transpose2 x) s ≈
      swapPhase k * transvect m n k x s := by
  intro s
  have hiter := diag_congr (omegaK_transpose m n k x) s
  have hscale := diag_scale (swapPhase k)
    (transpose2 (OmegaK m n k x)) s
  have hdiag := diag_transpose (OmegaK m n k x) s
  exact Q'.eqv_trans _ _ _ hiter
    (Q'.eqv_trans _ _ _ hscale
      (Q'.mul_eqv_congr_left (swapPhase k) _ _ hdiag))

end YMGap.Continuum.SU2TransvectantSwapParity

#print axioms YMGap.Continuum.SU2TransvectantSwapParity.omega_transpose
#print axioms YMGap.Continuum.SU2TransvectantSwapParity.omegaK_transpose
#print axioms YMGap.Continuum.SU2TransvectantSwapParity.diag_transpose
#print axioms YMGap.Continuum.SU2TransvectantSwapParity.diag_scale
#print axioms YMGap.Continuum.SU2TransvectantSwapParity.transvect_transpose
