/-
# General-label seed for the transvectant coordinate-basis route

The mixed-label pentagon was checked on a finite spin window.  The all-label
coordinate-basis route instead needs symbolic facts about the Cayley
transvectants.  This module starts that route with the order-zero theorem for
arbitrary degrees and monomial indices: diagonal restriction of a pure tensor
is exactly the product monomial, supported at coefficient `i+j`.

The proof is a genuine finite-sum argument over arbitrary naturals.  It records
the one-hot and zero-support lemmas needed by the higher-order Omega induction;
no finite cutoff enumeration is used.

Mathlib-free; no classical choice, native decision procedure, proof hole, or
new axiom.
-/

import YMGap.Continuum.TransvectantCG

namespace YMGap.Continuum.SU2TransvectantGeneralCoefficient

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG

/-- A rational finite sum whose every term vanishes is equivalent to zero. -/
theorem finSum_zero_on (f : Nat → Q') : ∀ k,
    (∀ a, a < k → (f a).eqv 0) → (finSum f k).eqv 0
  | 0, _ => Q'.eqv_refl 0
  | k + 1, h => by
      have hpre : (finSum f k).eqv 0 :=
        finSum_zero_on f k (fun a ha => h a (Nat.lt_succ_of_lt ha))
      have hlast : (f k).eqv 0 := h k (Nat.lt_succ_self k)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hpre hlast) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- The finite sum of a one-hot rational sequence is one when its support lies
inside the summation window. -/
theorem finSum_onehot_one : ∀ k i,
    i < k → (finSum (fun a => if a = i then (1 : Q') else 0) k).eqv 1
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, i, hi => by
      by_cases hik : i < k
      · have hki : ¬ k = i := fun h => by subst i; exact Nat.lt_irrefl k hik
        simp only [finSum_succ, if_neg hki]
        refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
        exact finSum_onehot_one k i hik
      · have hieq : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp hik)
        subst i
        simp only [finSum_succ, if_pos]
        have hzero :
            (finSum (fun a => if a = k then (1 : Q') else 0) k).eqv 0 :=
          finSum_zero_on _ k (fun a ha => by
            have hne : ¬ a = k := fun h => by subst a; exact Nat.lt_irrefl k ha
            simp only [if_neg hne]
            exact Q'.eqv_refl 0)
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ 1 hzero) ?_
        exact Q'.eqv_of_eq (Q'.zero_add' 1)

/-- One-hot finite sum with an arbitrary rational payload. -/
theorem finSum_onehot_value (c : Q') : ∀ k i,
    i < k → (finSum (fun a => if a = i then c else 0) k).eqv c
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, i, hi => by
      by_cases hik : i < k
      · have hki : ¬ k = i := fun h => by subst i; exact Nat.lt_irrefl k hik
        simp only [finSum_succ, if_neg hki]
        refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
        exact finSum_onehot_value c k i hik
      · have hieq : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp hik)
        subst i
        simp only [finSum_succ, if_pos]
        have hzero : (finSum (fun a => if a = k then c else 0) k).eqv 0 :=
          finSum_zero_on _ k (fun a ha => by
            have hne : ¬ a = k := fun h => by subst a; exact Nat.lt_irrefl k ha
            simp only [if_neg hne]
            exact Q'.eqv_refl 0)
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ c hzero) ?_
        exact Q'.eqv_of_eq (Q'.zero_add' c)

/-- Negation commutes with rational finite sums. -/
theorem finSum_neg (f : Nat → Q') : ∀ k,
    (finSum (fun a => -(f a)) k).eqv (-(finSum f k))
  | 0 => Q'.eqv_refl 0
  | k + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (finSum_neg f k)) ?_
      show (-(finSum f k) + -(f k)).eqv (-(finSum f k + f k))
      exact Q'.eqv_symm (Q'.neg_add_eqv _ _)

/-- On the diagonal coefficient `s=i+j`, a pure tensor contributes the one-hot
summand supported at diagonal index `i`. -/
theorem tprod_mono_diagonal_onehot (i j a : Nat) :
    (tprod (mono i) (mono j) a (i + j - a)).eqv
      (if a = i then (1 : Q') else 0) := by
  by_cases ha : a = i
  · subst a
    simp only [tprod, mono, if_pos, Nat.add_sub_cancel_left]
    exact Q'.mul_one_eqv 1
  · simp only [tprod, mono, if_neg ha]
    exact Q'.zero_mul_eqv _

/-- Away from `s=i+j`, every diagonal summand of the pure tensor vanishes. -/
theorem tprod_mono_diagonal_zero_of_ne (i j s a : Nat)
    (hs : ¬ s = i + j) (ha : a < s + 1) :
    (tprod (mono i) (mono j) a (s - a)).eqv 0 := by
  unfold tprod mono
  by_cases hai : a = i
  · subst a
    have his : i ≤ s := Nat.lt_succ_iff.mp ha
    have hsub : ¬ s - i = j := by
      intro h
      apply hs
      omega
    simp only [if_pos, if_neg hsub]
    exact Q'.mul_zero_eqv 1
  · simp only [if_neg hai]
    exact Q'.zero_mul_eqv _

/-- **All-label order-zero transvectant coefficient.**  For arbitrary degrees
and monomial indices, the zeroth Cayley transvectant is the ordinary product
monomial: its coefficient is one exactly at `s=i+j` and zero elsewhere. -/
theorem transvect_zero_monomial (m n i j s : Nat) :
    (transvect m n 0 (tprod (mono i) (mono j)) s).eqv
      (if s = i + j then (1 : Q') else 0) := by
  unfold transvect OmegaK diag
  by_cases hs : s = i + j
  · subst s
    simp only [if_pos]
    refine Q'.eqv_trans _
      (finSum (fun a => if a = i then (1 : Q') else 0) (i + j + 1)) _ ?_ ?_
    · exact finSum_eqv_congr _ _
        (fun a => tprod_mono_diagonal_onehot i j a) _
    · exact finSum_onehot_one _ i (by omega)
  · simp only [if_neg hs]
    exact finSum_zero_on _ (s + 1)
      (fun a ha => tprod_mono_diagonal_zero_of_ne i j s a hs ha)

/-! ## The first Cayley contraction, for arbitrary labels -/

/-- Positive half of the first Omega contraction at diagonal summand `a`. -/
def omegaFirstTerm (m n i j s a : Nat) : Q' :=
  Q'.ofNat ((a + 1) * (n - (s - a))) *
    tprod (mono i) (mono j) (a + 1) (s - a)

/-- Negative half of the first Omega contraction at diagonal summand `a`. -/
def omegaSecondTerm (m n i j s a : Nat) : Q' :=
  Q'.ofNat ((m - a) * ((s - a) + 1)) *
    tprod (mono i) (mono j) a ((s - a) + 1)

/-- On the contraction shell `s+1=i+j`, and for `i>0`, the first Omega half is
one-hot at `a=i-1`. -/
theorem omegaFirst_shell_onehot (m n i j s a : Nat)
    (hs : s + 1 = i + j) (hi : 0 < i) :
    (omegaFirstTerm m n i j s a).eqv
      (if a = i - 1 then Q'.ofNat (i * (n - j)) else 0) := by
  by_cases ha : a = i - 1
  · have hai : a + 1 = i := by omega
    have hsaj : s - a = j := by omega
    rw [if_pos ha]
    simp only [omegaFirstTerm, tprod, mono, hai, hsaj, if_pos]
    exact Q'.mul_one_eqv _
  · have hai : ¬ a + 1 = i := by omega
    simp only [omegaFirstTerm, tprod, mono, if_neg ha, if_neg hai]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) ?_
    exact Q'.mul_zero_eqv _

/-- If `i=0`, the first Omega half vanishes identically. -/
theorem omegaFirst_zero_of_i_zero (m n j s a : Nat) :
    (omegaFirstTerm m n 0 j s a).eqv 0 := by
  have hne : ¬ a + 1 = 0 := by omega
  simp only [omegaFirstTerm, tprod, mono, if_neg hne]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) ?_
  exact Q'.mul_zero_eqv _

/-- On the contraction shell, and for `j>0`, the second Omega half is one-hot
at `a=i`. -/
theorem omegaSecond_shell_onehot (m n i j s a : Nat)
    (hs : s + 1 = i + j) (hj : 0 < j) :
    (omegaSecondTerm m n i j s a).eqv
      (if a = i then Q'.ofNat ((m - i) * j) else 0) := by
  by_cases ha : a = i
  · have hsaj : s - a + 1 = j := by omega
    have hsij : s - i + 1 = j := by omega
    rw [if_pos ha]
    unfold omegaSecondTerm tprod mono
    rw [ha, hsij]
    simp only [if_pos]
    exact Q'.mul_one_eqv _
  · simp only [omegaSecondTerm, tprod, mono, if_neg ha]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) ?_
    exact Q'.mul_zero_eqv _

/-- If `j=0`, the second Omega half vanishes identically. -/
theorem omegaSecond_zero_of_j_zero (m n i s a : Nat) :
    (omegaSecondTerm m n i 0 s a).eqv 0 := by
  have hne : ¬ s - a + 1 = 0 := by omega
  unfold omegaSecondTerm tprod mono
  by_cases ha : a = i
  · simp only [if_pos ha, if_neg hne]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.mul_zero_eqv 1)) ?_
    exact Q'.mul_zero_eqv _
  · simp only [if_neg ha]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) ?_
    exact Q'.mul_zero_eqv _

/-- Off the contraction shell, the first Omega half vanishes at every diagonal
summand. -/
theorem omegaFirst_zero_offshell (m n i j s a : Nat)
    (hs : ¬ s + 1 = i + j) (ha : a < s + 1) :
    (omegaFirstTerm m n i j s a).eqv 0 := by
  unfold omegaFirstTerm tprod mono
  by_cases h1 : a + 1 = i
  · by_cases h2 : s - a = j
    · exfalso
      apply hs
      omega
    · simp only [if_pos h1, if_neg h2]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ 0 (Q'.mul_zero_eqv 1)) ?_
      exact Q'.mul_zero_eqv _
  · simp only [if_neg h1]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) ?_
    exact Q'.mul_zero_eqv _

/-- Off the contraction shell, the second Omega half also vanishes. -/
theorem omegaSecond_zero_offshell (m n i j s a : Nat)
    (hs : ¬ s + 1 = i + j) (ha : a < s + 1) :
    (omegaSecondTerm m n i j s a).eqv 0 := by
  unfold omegaSecondTerm tprod mono
  by_cases h1 : a = i
  · by_cases h2 : s - a + 1 = j
    · exfalso
      apply hs
      omega
    · simp only [if_pos h1, if_neg h2]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ 0 (Q'.mul_zero_eqv 1)) ?_
      exact Q'.mul_zero_eqv _
  · simp only [if_neg h1]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv _)) ?_
    exact Q'.mul_zero_eqv _

/-- **All-label first transvectant coefficient.**  The first Cayley contraction
has its expected signed falling-factor coefficient, at exactly the monomial
degree lowered by one. -/
theorem transvect_one_monomial (m n i j s : Nat) :
    (transvect m n 1 (tprod (mono i) (mono j)) s).eqv
      (if s + 1 = i + j then
        Q'.ofNat (i * (n - j)) + -(Q'.ofNat ((m - i) * j))
       else 0) := by
  unfold transvect OmegaK diag
  by_cases hs : s + 1 = i + j
  · simp only [if_pos hs]
    let F := fun a => omegaFirstTerm m n i j s a
    let G := fun a => omegaSecondTerm m n i j s a
    have hterm : ∀ a,
        (Omega m n (tprod (mono i) (mono j)) a (s - a)).eqv
          (F a + -(G a)) := fun a => Q'.eqv_refl _
    refine Q'.eqv_trans _
      (finSum (fun a => F a + -(G a)) (s + 1)) _
      (finSum_eqv_congr _ _ hterm (s + 1)) ?_
    refine Q'.eqv_trans _
      (finSum F (s + 1) + finSum (fun a => -(G a)) (s + 1)) _
      (RationalTail.finSum_add F (fun a => -(G a)) (s + 1)) ?_
    refine Q'.eqv_trans _
      (finSum F (s + 1) + -(finSum G (s + 1))) _
      (Q'.add_eqv_congr_left _ _ _ (finSum_neg G (s + 1))) ?_
    have hF : (finSum F (s + 1)).eqv (Q'.ofNat (i * (n - j))) := by
      by_cases hi : i = 0
      · subst i
        refine Q'.eqv_trans _ 0 _
          (finSum_zero_on F (s + 1) (fun a _ => omegaFirst_zero_of_i_zero m n j s a)) ?_
        simpa only [Nat.zero_mul] using Q'.eqv_symm (Q'.ofNat_zero_eqv)
      · have hip : 0 < i := Nat.pos_of_ne_zero hi
        refine Q'.eqv_trans _
          (finSum (fun a => if a = i - 1 then Q'.ofNat (i * (n - j)) else 0)
            (s + 1)) _ ?_ ?_
        · exact finSum_eqv_congr _ _
            (fun a => omegaFirst_shell_onehot m n i j s a hs hip) _
        · exact finSum_onehot_value _ _ _ (by omega)
    have hG : (finSum G (s + 1)).eqv (Q'.ofNat ((m - i) * j)) := by
      by_cases hj : j = 0
      · subst j
        refine Q'.eqv_trans _ 0 _
          (finSum_zero_on G (s + 1) (fun a _ => omegaSecond_zero_of_j_zero m n i s a)) ?_
        exact Q'.eqv_symm (Q'.ofNat_zero_eqv)
      · have hjp : 0 < j := Nat.pos_of_ne_zero hj
        refine Q'.eqv_trans _
          (finSum (fun a => if a = i then Q'.ofNat ((m - i) * j) else 0)
            (s + 1)) _ ?_ ?_
        · exact finSum_eqv_congr _ _
            (fun a => omegaSecond_shell_onehot m n i j s a hs hjp) _
        · exact finSum_onehot_value _ _ _ (by omega)
    exact Q'.add_eqv_congr' hF (Q'.neg_eqv_congr _ _ hG)
  · simp only [if_neg hs]
    apply finSum_zero_on
    intro a ha
    show (omegaFirstTerm m n i j s a + -(omegaSecondTerm m n i j s a)).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (omegaFirst_zero_offshell m n i j s a hs ha)
        (Q'.neg_eqv_congr _ _ (omegaSecond_zero_offshell m n i j s a hs ha))) ?_
    decide

/-! ## Arbitrary-order support propagation -/

/-- A two-form is supported on the affine degree layer `a+b+r=S`.  The offset
`r` records how many Cayley contractions have already been performed. -/
def LayerSupported (c : BForm2) (r S : Nat) : Prop :=
  ∀ a b, ¬ a + b + r = S → (c a b).eqv 0

/-- One Cayley Omega contraction advances the support-layer offset by one. -/
theorem omega_preserves_layer (m n r S : Nat) (c : BForm2)
    (h : LayerSupported c r S) :
    LayerSupported (Omega m n c) (r + 1) S := by
  intro a b hab
  have h1 : ¬ (a + 1) + b + r = S := by omega
  have h2 : ¬ a + (b + 1) + r = S := by omega
  have hz1 :
      (Q'.ofNat ((a + 1) * (n - b)) * c (a + 1) b).eqv 0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (h (a + 1) b h1)) ?_
    exact Q'.mul_zero_eqv _
  have hz2 :
      (Q'.ofNat ((m - a) * (b + 1)) * c a (b + 1)).eqv 0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (h a (b + 1) h2)) ?_
    exact Q'.mul_zero_eqv _
  unfold Omega
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hz1 (Q'.neg_eqv_congr _ _ hz2)) ?_
  decide

/-- Iterating Omega `k` times advances the layer offset by exactly `k`. -/
theorem omegaK_preserves_layer (m n k r S : Nat) (c : BForm2)
    (h : LayerSupported c r S) :
    LayerSupported (OmegaK m n k c) (r + k) S := by
  induction k generalizing m n r c with
  | zero =>
      exact h
  | succ k ih =>
      have hnext : LayerSupported (Omega m n c) (r + 1) S :=
        omega_preserves_layer m n r S c h
      have hk := ih (m - 1) (n - 1) (r + 1) (Omega m n c) hnext
      intro a b hab
      apply hk a b
      omega

/-- A pure tensor of monomials starts on the exact layer `a+b=i+j`. -/
theorem tprod_mono_layer (i j : Nat) :
    LayerSupported (tprod (mono i) (mono j)) 0 (i + j) := by
  intro a b hab
  unfold tprod mono
  by_cases hai : a = i
  · have hbj : ¬ b = j := by
      intro h
      apply hab
      omega
    simp only [if_pos hai, if_neg hbj]
    exact Q'.mul_zero_eqv 1
  · simp only [if_neg hai]
    exact Q'.zero_mul_eqv _

/-- Every order of the monomial Omega process stays on its exact
degree-lowered layer. -/
theorem omegaK_monomial_layer (m n k i j : Nat) :
    LayerSupported (OmegaK m n k (tprod (mono i) (mono j))) k (i + j) := by
  have h := omegaK_preserves_layer m n k 0 (i + j)
    (tprod (mono i) (mono j)) (tprod_mono_layer i j)
  simpa only [Nat.zero_add] using h

/-- **All-order support theorem.**  An order-`k` transvectant of monomials has
no coefficient away from the unique output degree `s+k=i+j`.  This is symbolic
in all labels and contraction orders, not a finite verification. -/
theorem transvect_monomial_zero_offshell (m n k i j s : Nat)
    (hs : ¬ s + k = i + j) :
    (transvect m n k (tprod (mono i) (mono j)) s).eqv 0 := by
  unfold transvect diag
  apply finSum_zero_on
  intro a ha
  have has : a ≤ s := Nat.lt_succ_iff.mp ha
  apply omegaK_monomial_layer m n k i j a (s - a)
  omega

end YMGap.Continuum.SU2TransvectantGeneralCoefficient

#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_zero_on
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_one
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_neg
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.tprod_mono_diagonal_onehot
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.tprod_mono_diagonal_zero_of_ne
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_zero_monomial
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_one_monomial
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.omega_preserves_layer
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.omegaK_preserves_layer
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.omegaK_monomial_layer
#print axioms YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
