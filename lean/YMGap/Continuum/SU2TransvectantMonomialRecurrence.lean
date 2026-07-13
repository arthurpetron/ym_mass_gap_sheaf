/-
# Monomial recurrence for arbitrary-label Cayley transvectants

One Cayley contraction of a pure tensor has exactly two derivative branches.
This module proves that decomposition pointwise for arbitrary natural labels,
including the zero-index boundary cases, and transports it through the
all-order linearity layer.  The result is the constructive two-branch
recurrence used by the factorial/Pascal induction.
-/

import YMGap.Continuum.SU2TransvectantLinearity

namespace YMGap.Continuum.SU2TransvectantMonomialRecurrence

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity

private theorem scale_zero_of_eqv (A x : Q') (hx : x.eqv 0) :
    (A * x).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A x 0 hx)
    (Q'.mul_zero_eqv A)

/-- The positive derivative branch of Omega sends the first monomial index
`i` to `i-1`, with exact coefficient `i(n-j)`. -/
theorem omega_first_monomial (n i j a b : Nat) :
    (Q'.ofNat ((a + 1) * (n - b)) *
      tprod (mono i) (mono j) (a + 1) b).eqv
    (Q'.ofNat (i * (n - j)) *
      tprod (mono (i - 1)) (mono j) a b) := by
  cases i with
  | zero =>
      have hsucc : ¬ a + 1 = 0 := by omega
      have hleftInner :
          (tprod (mono 0) (mono j) (a + 1) b).eqv 0 := by
        unfold tprod mono
        rw [if_neg hsucc]
        exact Q'.zero_mul_eqv _
      have hleft := scale_zero_of_eqv
        (Q'.ofNat ((a + 1) * (n - b))) _ hleftInner
      have hright :
          (Q'.ofNat (0 * (n - j)) *
            tprod (mono (0 - 1)) (mono j) a b).eqv 0 := by
        simp only [Nat.zero_mul, Nat.zero_sub]
        change ((0 : Q') * tprod (mono 0) (mono j) a b).eqv 0
        exact Q'.zero_mul_eqv _
      exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)
  | succ i =>
      have hipred : i + 1 - 1 = i := by omega
      rw [hipred]
      by_cases ha : a = i
      · subst a
        by_cases hb : b = j
        · subst b
          simp only [tprod, mono, if_pos]
          exact Q'.eqv_refl _
        · have hleftInner :
              (tprod (mono (i + 1)) (mono j) (i + 1) b).eqv 0 := by
            unfold tprod mono
            rw [if_pos rfl, if_neg hb]
            exact Q'.mul_zero_eqv 1
          have hrightInner :
              (tprod (mono i) (mono j) i b).eqv 0 := by
            unfold tprod mono
            rw [if_pos rfl, if_neg hb]
            exact Q'.mul_zero_eqv 1
          exact Q'.eqv_trans _ 0 _
            (scale_zero_of_eqv _ _ hleftInner)
            (Q'.eqv_symm (scale_zero_of_eqv _ _ hrightInner))
      · have hsucc : ¬ a + 1 = i + 1 := by omega
        have hleftInner :
            (tprod (mono (i + 1)) (mono j) (a + 1) b).eqv 0 := by
          unfold tprod mono
          rw [if_neg hsucc]
          exact Q'.zero_mul_eqv _
        have hrightInner :
            (tprod (mono i) (mono j) a b).eqv 0 := by
          unfold tprod mono
          rw [if_neg ha]
          exact Q'.zero_mul_eqv _
        exact Q'.eqv_trans _ 0 _
          (scale_zero_of_eqv _ _ hleftInner)
          (Q'.eqv_symm (scale_zero_of_eqv _ _ hrightInner))

/-- The negative derivative branch of Omega sends the second monomial index
`j` to `j-1`, with exact coefficient `(m-i)j`. -/
theorem omega_second_monomial (m i j a b : Nat) :
    (Q'.ofNat ((m - a) * (b + 1)) *
      tprod (mono i) (mono j) a (b + 1)).eqv
    (Q'.ofNat ((m - i) * j) *
      tprod (mono i) (mono (j - 1)) a b) := by
  cases j with
  | zero =>
      have hsucc : ¬ b + 1 = 0 := by omega
      have hleftInner :
          (tprod (mono i) (mono 0) a (b + 1)).eqv 0 := by
        unfold tprod mono
        rw [if_neg hsucc]
        exact Q'.mul_zero_eqv _
      have hleft := scale_zero_of_eqv
        (Q'.ofNat ((m - a) * (b + 1))) _ hleftInner
      have hright :
          (Q'.ofNat ((m - i) * 0) *
            tprod (mono i) (mono (0 - 1)) a b).eqv 0 := by
        change ((0 : Q') * tprod (mono i) (mono 0) a b).eqv 0
        exact Q'.zero_mul_eqv _
      exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)
  | succ j =>
      have hjpred : j + 1 - 1 = j := by omega
      rw [hjpred]
      by_cases hb : b = j
      · subst b
        by_cases ha : a = i
        · subst a
          simp only [tprod, mono, if_pos]
          exact Q'.eqv_refl _
        · have hleftInner :
              (tprod (mono i) (mono (j + 1)) a (j + 1)).eqv 0 := by
            unfold tprod mono
            rw [if_neg ha]
            exact Q'.zero_mul_eqv _
          have hrightInner :
              (tprod (mono i) (mono j) a j).eqv 0 := by
            unfold tprod mono
            rw [if_neg ha]
            exact Q'.zero_mul_eqv _
          exact Q'.eqv_trans _ 0 _
            (scale_zero_of_eqv _ _ hleftInner)
            (Q'.eqv_symm (scale_zero_of_eqv _ _ hrightInner))
      · have hsucc : ¬ b + 1 = j + 1 := by omega
        have hleftInner :
            (tprod (mono i) (mono (j + 1)) a (b + 1)).eqv 0 := by
          unfold tprod mono
          rw [if_neg hsucc]
          exact Q'.mul_zero_eqv _
        have hrightInner :
            (tprod (mono i) (mono j) a b).eqv 0 := by
          unfold tprod mono
          rw [if_neg hb]
          exact Q'.mul_zero_eqv _
        exact Q'.eqv_trans _ 0 _
          (scale_zero_of_eqv _ _ hleftInner)
          (Q'.eqv_symm (scale_zero_of_eqv _ _ hrightInner))

/-- Exact two-branch monomial decomposition of one Cayley contraction. -/
theorem omega_monomial_decomposition (m n i j : Nat) :
    BForm2Eqv (Omega m n (tprod (mono i) (mono j)))
      (badd
        (bscale (Q'.ofNat (i * (n - j)))
          (tprod (mono (i - 1)) (mono j)))
        (bscale (-(Q'.ofNat ((m - i) * j)))
          (tprod (mono i) (mono (j - 1))))) := by
  intro a b
  unfold Omega badd bscale
  have hfirst := omega_first_monomial n i j a b
  have hsecond0 := omega_second_monomial m i j a b
  have hsecond :
      (-(Q'.ofNat ((m - a) * (b + 1)) *
        tprod (mono i) (mono j) a (b + 1))).eqv
      ((-(Q'.ofNat ((m - i) * j))) *
        tprod (mono i) (mono (j - 1)) a b) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hsecond0) ?_
    exact Q'.eqv_symm
      (Q'.neg_mul_eqv (Q'.ofNat ((m - i) * j))
        (tprod (mono i) (mono (j - 1)) a b))
  exact Q'.add_eqv_congr' hfirst hsecond

/-- **Arbitrary-order monomial recurrence.**  Order `k+1` is the sum of
the two first-derivative branches followed by order `k` at bidegree
`(m-1,n-1)`. -/
theorem transvect_succ_monomial (m n k i j s : Nat) :
    (transvect m n (k + 1) (tprod (mono i) (mono j)) s).eqv
      (Q'.ofNat (i * (n - j)) *
          transvect (m - 1) (n - 1) k
            (tprod (mono (i - 1)) (mono j)) s +
        (-(Q'.ofNat ((m - i) * j))) *
          transvect (m - 1) (n - 1) k
            (tprod (mono i) (mono (j - 1))) s) := by
  let A := Q'.ofNat (i * (n - j))
  let B := -(Q'.ofNat ((m - i) * j))
  let C := tprod (mono (i - 1)) (mono j)
  let D := tprod (mono i) (mono (j - 1))
  have hdecomp :
      BForm2Eqv (Omega m n (tprod (mono i) (mono j)))
        (badd (bscale A C) (bscale B D)) := by
    simpa only [A, B, C, D] using omega_monomial_decomposition m n i j
  have h0 := transvect_congr (m - 1) (n - 1) k hdecomp s
  have hadd := transvect_add (m - 1) (n - 1) k (bscale A C) (bscale B D) s
  have hA := transvect_scale (m - 1) (n - 1) k A C s
  have hB := transvect_scale (m - 1) (n - 1) k B D s
  change (transvect (m - 1) (n - 1) k
      (Omega m n (tprod (mono i) (mono j))) s).eqv _
  refine Q'.eqv_trans _ _ _ h0 ?_
  refine Q'.eqv_trans _ _ _ hadd ?_
  simpa only [A, B, C, D] using Q'.add_eqv_congr' hA hB

end YMGap.Continuum.SU2TransvectantMonomialRecurrence

#print axioms YMGap.Continuum.SU2TransvectantMonomialRecurrence.omega_first_monomial
#print axioms YMGap.Continuum.SU2TransvectantMonomialRecurrence.omega_second_monomial
#print axioms YMGap.Continuum.SU2TransvectantMonomialRecurrence.omega_monomial_decomposition
#print axioms YMGap.Continuum.SU2TransvectantMonomialRecurrence.transvect_succ_monomial
