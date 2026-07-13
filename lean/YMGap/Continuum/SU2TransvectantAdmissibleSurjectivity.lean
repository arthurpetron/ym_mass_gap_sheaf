/-
# Coordinate pivots for every admissible transvectant output

The highest-monomial pivot is extended to both triangular halves of an
arbitrary Clebsch--Gordan channel.  A zero second index follows only positive
Cayley branches and covers the lower output slots; a saturated first index
does the same for the upper slots.  Together they give a nonzero pivot for
every coordinate of every admissible output module.
-/

import YMGap.Continuum.SU2TransvectantAdmissibleExtremal

namespace YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantMonomialRecurrence
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantAdmissibleExtremal
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.BondMovingStep

/-- Product of the two simultaneously descending positive-branch labels. -/
def positiveBranchCoeff : Nat → Nat → Nat → Q'
  | _, _, 0 => 1
  | p, q, k + 1 =>
      Q'.ofNat (p * q) * positiveBranchCoeff (p - 1) (q - 1) k

/-- Constructive reciprocal of a rational with strictly positive numerator. -/
def positiveRecip (q : Q') (hq : 0 < q.num) : Q' :=
  Q'.mkPos (Int.ofNat q.den) q.num.toNat (by
    have : 0 < q.num.toNat := by omega
    exact this)

theorem mul_positiveRecip_eqv_one (q : Q') (hq : 0 < q.num) :
    (q * positiveRecip q hq).eqv 1 := by
  unfold Q'.eqv positiveRecip
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.mkPos_num, Q'.mkPos_den,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl]
  have hcast : Int.ofNat q.num.toNat = q.num :=
    Int.toNat_of_nonneg (Int.le_of_lt hq)
  have hcast' : (q.num.toNat : Int) = q.num := hcast
  rw [hcast']
  simp only [Int.mul_one, Int.one_mul]
  exact Int.mul_comm _ _

theorem positiveRecip_scale_eqv (q x : Q') (hq : 0 < q.num) :
    (positiveRecip q hq * (q * x)).eqv x := by
  refine Q'.eqv_trans _ ((positiveRecip q hq * q) * x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  have hcomm := Q'.mul_comm_eqv (positiveRecip q hq) q
  have hone : (positiveRecip q hq * q).eqv 1 :=
    Q'.eqv_trans _ _ _ hcomm (mul_positiveRecip_eqv_one q hq)
  refine Q'.eqv_trans _ (1 * x) _
    (Q'.mul_eqv_congr_right _ _ x hone) ?_
  exact Q'.one_mul_eqv x

theorem positiveBranchCoeff_num_pos : ∀ p q k : Nat,
    k ≤ p → k ≤ q → 0 < (positiveBranchCoeff p q k).num := by
  intro p q k
  induction k generalizing p q with
  | zero =>
      intro _ _
      change 0 < (1 : Q').num
      decide
  | succ k ih =>
      intro hp hq
      have hp0 : 0 < p := by omega
      have hq0 : 0 < q := by omega
      have hih := ih (p - 1) (q - 1) (by omega) (by omega)
      unfold positiveBranchCoeff
      simp only [Q'.mul_num_cast, Q'.ofNat_num_cast]
      exact Int.mul_pos (by exact_mod_cast Nat.mul_pos hp0 hq0) hih

theorem positiveBranchCoeff_not_eqv_zero (p q k : Nat)
    (hp : k ≤ p) (hq : k ≤ q) :
    ¬ (positiveBranchCoeff p q k).eqv 0 := by
  intro h
  unfold Q'.eqv at h
  have hn : (positiveBranchCoeff p q k).num = 0 := by
    have h' : (positiveBranchCoeff p q k).num * (1 : Int) =
        (0 : Int) * ((positiveBranchCoeff p q k).den : Int) := h
    rwa [Int.mul_one, Int.zero_mul] at h'
  have hpnum := positiveBranchCoeff_num_pos p q k hp hq
  omega

/-- Lower triangular pivot: with second monomial index zero, every negative
branch vanishes. -/
theorem transvect_positive_low : ∀ k m n i : Nat,
    k ≤ i → k ≤ n →
    (transvect m n k (tprod (mono i) (mono 0)) (i - k)).eqv
      (positiveBranchCoeff i n k) := by
  intro k
  induction k with
  | zero =>
      intro m n i _ _
      have h := transvect_monomial_matches_factorial_on_shell 0 m n i 0
        (Nat.zero_le (i + 0))
      refine Q'.eqv_trans _ (transvectFactorialCoeff m n 0 i 0) _
        (by simpa using h) ?_
      simpa [positiveBranchCoeff] using transvectFactorialCoeff_zero m n i 0
  | succ k ih =>
      intro m n i hki hkn
      have hi : 0 < i := by omega
      have hn : 0 < n := by omega
      have hbranch0 := ih (m - 1) (n - 1) (i - 1) (by omega) (by omega)
      have hs : i - (k + 1) = (i - 1) - k := by omega
      have hbranch :
          (transvect (m - 1) (n - 1) k
            (tprod (mono (i - 1)) (mono 0)) (i - (k + 1))).eqv
            (positiveBranchCoeff (i - 1) (n - 1) k) := by
        rw [hs]
        exact hbranch0
      have hpositive := Q'.mul_eqv_congr_left (Q'.ofNat (i * n)) _ _ hbranch
      have hnegative :
          ((-(Q'.ofNat ((m - i) * 0))) *
            transvect (m - 1) (n - 1) k
              (tprod (mono i) (mono (0 - 1))) (i - (k + 1))).eqv 0 := by
        simp only [Nat.mul_zero, Nat.zero_sub]
        change ((0 : Q') *
          transvect (m - 1) (n - 1) k
            (tprod (mono i) (mono 0)) (i - (k + 1))).eqv 0
        exact Q'.zero_mul_eqv _
      have hrec := transvect_succ_monomial m n k i 0 (i - (k + 1))
      refine Q'.eqv_trans _ _ _ (by simpa only [Nat.sub_zero] using hrec) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (i * n) * positiveBranchCoeff (i - 1) (n - 1) k + 0) _
        (Q'.add_eqv_congr' hpositive hnegative) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (i * n) * positiveBranchCoeff (i - 1) (n - 1) k) _
        (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
      exact Q'.eqv_refl _

/-- Upper triangular pivot: with saturated first index, every negative branch
again vanishes. -/
theorem transvect_positive_high : ∀ k m n j : Nat,
    j ≤ n → k ≤ m → k ≤ n - j →
    (transvect m n k (tprod (mono m) (mono j)) (m + j - k)).eqv
      (positiveBranchCoeff m (n - j) k) := by
  intro k
  induction k with
  | zero =>
      intro m n j hj _ _
      have h := transvect_monomial_matches_factorial_on_shell 0 m n m j
        (Nat.zero_le (m + j))
      refine Q'.eqv_trans _ (transvectFactorialCoeff m n 0 m j) _
        (by simpa using h) ?_
      simpa [positiveBranchCoeff] using transvectFactorialCoeff_zero m n m j
  | succ k ih =>
      intro m n j hj hkm hkq
      have hm : 0 < m := by omega
      have hn : 0 < n := by omega
      have hj' : j ≤ n - 1 := by omega
      have hq : (n - 1) - j = n - j - 1 := by omega
      have hbranch0 := ih (m - 1) (n - 1) j hj' (by omega) (by omega)
      have hs : m + j - (k + 1) = (m - 1) + j - k := by omega
      have hbranch :
          (transvect (m - 1) (n - 1) k
            (tprod (mono (m - 1)) (mono j)) (m + j - (k + 1))).eqv
            (positiveBranchCoeff (m - 1) (n - j - 1) k) := by
        rw [hs, ← hq]
        exact hbranch0
      have hpositive := Q'.mul_eqv_congr_left (Q'.ofNat (m * (n - j)))
        _ _ hbranch
      have hnegative :
          ((-(Q'.ofNat ((m - m) * j))) *
            transvect (m - 1) (n - 1) k
              (tprod (mono m) (mono (j - 1))) (m + j - (k + 1))).eqv 0 := by
        simp only [Nat.sub_self, Nat.zero_mul]
        change ((0 : Q') *
          transvect (m - 1) (n - 1) k
            (tprod (mono m) (mono (j - 1))) (m + j - (k + 1))).eqv 0
        exact Q'.zero_mul_eqv _
      have hrec := transvect_succ_monomial m n k m j (m + j - (k + 1))
      refine Q'.eqv_trans _ _ _ hrec ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (m * (n - j)) *
            positiveBranchCoeff (m - 1) (n - j - 1) k + 0) _
        (Q'.add_eqv_congr' hpositive hnegative) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (m * (n - j)) *
          positiveBranchCoeff (m - 1) (n - j - 1) k) _
        (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
      exact Q'.eqv_refl _

theorem transvect_positive_low_form (m n i k : Nat)
    (hki : k ≤ i) (hkn : k ≤ n) :
    BFormEqv
      (transvect m n k (tprod (mono i) (mono 0)))
      (fun s => positiveBranchCoeff i n k * mono (i - k) s) := by
  intro s
  by_cases hs : s = i - k
  · subst s
    refine Q'.eqv_trans _ _ _ (transvect_positive_low k m n i hki hkn) ?_
    simp only [mono]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · have hoff :=
      YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
        m n k i 0 s (by omega)
    refine Q'.eqv_trans _ 0 _ hoff ?_
    simp only [mono, if_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

theorem transvect_positive_high_form (m n j k : Nat)
    (hj : j ≤ n) (hkm : k ≤ m) (hkq : k ≤ n - j) :
    BFormEqv
      (transvect m n k (tprod (mono m) (mono j)))
      (fun s => positiveBranchCoeff m (n - j) k * mono (m + j - k) s) := by
  intro s
  by_cases hs : s = m + j - k
  · subst s
    refine Q'.eqv_trans _ _ _ (transvect_positive_high k m n j hj hkm hkq) ?_
    simp only [mono]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · have hoff :=
      YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
        m n k m j s (by omega)
    refine Q'.eqv_trans _ 0 _ hoff ?_
    simp only [mono, if_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-- **Coordinatewise constructive surjectivity up to a nonzero scalar.**
For every admissible channel and every output monomial, explicit input
monomial indices produce precisely a nonzero multiple of that output and zero
in all other coordinates.  This is the triangular basis-existence pivot used
by the all-label recoupling construction. -/
theorem admissible_transvect_coordinate_pivot (a b c s : Nat)
    (h : fusionOK a b c = true) (hs : s ≤ c) :
    ∃ i j q, i ≤ a ∧ j ≤ b ∧ ¬ q.eqv 0 ∧
      BFormEqv
        (transvect a b (couplingOrder a b c) (tprod (mono i) (mono j)))
        (fun t => q * mono s t) := by
  let k := couplingOrder a b c
  have hspec := fusionOK_couplingOrder_spec a b c h
  have hka : k ≤ a := by simpa only [k] using hspec.2.1
  have hkb : k ≤ b := by simpa only [k] using hspec.2.2.1
  have hc : c = a + b - 2 * k := by
    dsimp only [k]
    omega
  by_cases hlo : s ≤ a - k
  · let i := s + k
    let q := positiveBranchCoeff i b k
    have hki : k ≤ i := by dsimp only [i]; omega
    have hia : i ≤ a := by dsimp only [i]; omega
    refine ⟨i, 0, q, hia, Nat.zero_le b, ?_, ?_⟩
    · exact positiveBranchCoeff_not_eqv_zero i b k hki hkb
    · have hf := transvect_positive_low_form a b i k hki hkb
      have his : i - k = s := by dsimp only [i]; omega
      intro t
      simpa only [k, q, his] using hf t
  · let j := s + k - a
    let q := positiveBranchCoeff a (b - j) k
    have haj : a ≤ s + k := by omega
    have hjb : j ≤ b := by
      dsimp only [j]
      rw [hc] at hs
      omega
    have hkq : k ≤ b - j := by
      dsimp only [j]
      rw [hc] at hs
      omega
    have hout : a + j - k = s := by dsimp only [j]; omega
    refine ⟨a, j, q, Nat.le_refl a, hjb, ?_, ?_⟩
    · exact positiveBranchCoeff_not_eqv_zero a (b - j) k hka hkq
    · have hf := transvect_positive_high_form a b j k hjb hka hkq
      intro t
      simpa only [k, q, hout] using hf t

/-- Literal coordinate surjectivity.  Scaling the explicit pivot by its
constructive positive reciprocal produces the selected output monomial itself,
not merely a nonzero multiple. -/
theorem admissible_transvect_coordinate_surjective (a b c s : Nat)
    (h : fusionOK a b c = true) (hs : s ≤ c) :
    ∃ input : BForm2,
      BFormEqv (transvect a b (couplingOrder a b c) input) (mono s) := by
  let k := couplingOrder a b c
  have hspec := fusionOK_couplingOrder_spec a b c h
  have hka : k ≤ a := by simpa only [k] using hspec.2.1
  have hkb : k ≤ b := by simpa only [k] using hspec.2.2.1
  have hc : c = a + b - 2 * k := by
    dsimp only [k]
    omega
  by_cases hlo : s ≤ a - k
  · let i := s + k
    let q := positiveBranchCoeff i b k
    have hki : k ≤ i := by dsimp only [i]; omega
    have hq : 0 < q.num := positiveBranchCoeff_num_pos i b k hki hkb
    let rinv := positiveRecip q hq
    let carrier := tprod (mono i) (mono 0)
    refine ⟨bscale rinv carrier, ?_⟩
    have hpivot := transvect_positive_low_form a b i k hki hkb
    have his : i - k = s := by dsimp only [i]; omega
    intro t
    have hscale := transvect_scale a b k rinv carrier t
    have hp : (transvect a b k carrier t).eqv (q * mono s t) := by
      simpa only [carrier, q, his] using hpivot t
    refine Q'.eqv_trans _ _ _ (by simpa only [k, carrier] using hscale) ?_
    refine Q'.eqv_trans _ (rinv * (q * mono s t)) _
      (Q'.mul_eqv_congr_left rinv _ _ hp) ?_
    exact positiveRecip_scale_eqv q (mono s t) hq
  · let j := s + k - a
    let q := positiveBranchCoeff a (b - j) k
    have hjb : j ≤ b := by
      dsimp only [j]
      rw [hc] at hs
      omega
    have hkq : k ≤ b - j := by
      dsimp only [j]
      rw [hc] at hs
      omega
    have hout : a + j - k = s := by dsimp only [j]; omega
    have hq : 0 < q.num := positiveBranchCoeff_num_pos a (b - j) k hka hkq
    let rinv := positiveRecip q hq
    let carrier := tprod (mono a) (mono j)
    refine ⟨bscale rinv carrier, ?_⟩
    have hpivot := transvect_positive_high_form a b j k hjb hka hkq
    intro t
    have hscale := transvect_scale a b k rinv carrier t
    have hp : (transvect a b k carrier t).eqv (q * mono s t) := by
      simpa only [carrier, q, hout] using hpivot t
    refine Q'.eqv_trans _ _ _ (by simpa only [k, carrier] using hscale) ?_
    refine Q'.eqv_trans _ (rinv * (q * mono s t)) _
      (Q'.mul_eqv_congr_left rinv _ _ hp) ?_
    exact positiveRecip_scale_eqv q (mono s t) hq

/-- A Type-level, choice-free preimage for each bounded output coordinate. -/
def admissibleCoordinateInput (a b c : Nat) (h : fusionOK a b c = true)
    (s : Fin (c + 1)) : BForm2 :=
  let k := couplingOrder a b c
  if hlo : s.val ≤ a - k then
    let i := s.val + k
    let q := positiveBranchCoeff i b k
    let hspec := fusionOK_couplingOrder_spec a b c h
    let hki : k ≤ i := by omega
    let hkb : k ≤ b := hspec.2.2.1
    let hq : 0 < q.num := positiveBranchCoeff_num_pos i b k hki hkb
    bscale (positiveRecip q hq) (tprod (mono i) (mono 0))
  else
    let j := s.val + k - a
    let q := positiveBranchCoeff a (b - j) k
    let hspec := fusionOK_couplingOrder_spec a b c h
    let hka : k ≤ a := hspec.2.1
    let hc : c = a + b - 2 * k := by omega
    let hjb : j ≤ b := by omega
    let hkq : k ≤ b - j := by omega
    let hq : 0 < q.num := positiveBranchCoeff_num_pos a (b - j) k hka hkq
    bscale (positiveRecip q hq) (tprod (mono a) (mono j))

/-- The explicit Type-level input maps to its selected monomial. -/
theorem admissibleCoordinateInput_maps (a b c : Nat)
    (h : fusionOK a b c = true) (s : Fin (c + 1)) :
    BFormEqv
      (transvect a b (couplingOrder a b c)
        (admissibleCoordinateInput a b c h s))
      (mono s.val) := by
  let k := couplingOrder a b c
  have hspec := fusionOK_couplingOrder_spec a b c h
  have hka : k ≤ a := by simpa only [k] using hspec.2.1
  have hkb : k ≤ b := by simpa only [k] using hspec.2.2.1
  have hc : c = a + b - 2 * k := by
    dsimp only [k]
    omega
  unfold admissibleCoordinateInput
  dsimp only
  split
  next hlo =>
    let i := s.val + k
    let q := positiveBranchCoeff i b k
    have hki : k ≤ i := by dsimp only [i]; omega
    have hq : 0 < q.num := positiveBranchCoeff_num_pos i b k hki hkb
    let rinv := positiveRecip q hq
    let carrier := tprod (mono i) (mono 0)
    have hpivot := transvect_positive_low_form a b i k hki hkb
    have his : i - k = s.val := by dsimp only [i]; omega
    intro t
    have hscale := transvect_scale a b k rinv carrier t
    have hp : (transvect a b k carrier t).eqv (q * mono s.val t) := by
      simpa only [carrier, q, his] using hpivot t
    refine Q'.eqv_trans _ _ _
      (by simpa only [k, i, q, rinv, carrier] using hscale) ?_
    refine Q'.eqv_trans _ (rinv * (q * mono s.val t)) _
      (Q'.mul_eqv_congr_left rinv _ _ hp) ?_
    exact positiveRecip_scale_eqv q (mono s.val t) hq
  next hlo =>
    let j := s.val + k - a
    let q := positiveBranchCoeff a (b - j) k
    have hjb : j ≤ b := by
      dsimp only [j]
      have hs := s.isLt
      omega
    have hkq : k ≤ b - j := by
      dsimp only [j]
      have hs := s.isLt
      omega
    have hout : a + j - k = s.val := by dsimp only [j]; omega
    have hq : 0 < q.num := positiveBranchCoeff_num_pos a (b - j) k hka hkq
    let rinv := positiveRecip q hq
    let carrier := tprod (mono a) (mono j)
    have hpivot := transvect_positive_high_form a b j k hjb hka hkq
    intro t
    have hscale := transvect_scale a b k rinv carrier t
    have hp : (transvect a b k carrier t).eqv (q * mono s.val t) := by
      simpa only [carrier, q, hout] using hpivot t
    refine Q'.eqv_trans _ _ _
      (by simpa only [k, j, q, rinv, carrier] using hscale) ?_
    refine Q'.eqv_trans _ (rinv * (q * mono s.val t)) _
      (Q'.mul_eqv_congr_left rinv _ _ hp) ?_
    exact positiveRecip_scale_eqv q (mono s.val t) hq
end YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity

#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.positiveBranchCoeff_num_pos
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.mul_positiveRecip_eqv_one
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.positiveRecip_scale_eqv
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.positiveBranchCoeff_not_eqv_zero
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.transvect_positive_low
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.transvect_positive_high
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.transvect_positive_low_form
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.transvect_positive_high_form
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.admissible_transvect_coordinate_pivot
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.admissible_transvect_coordinate_surjective
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity.admissibleCoordinateInput_maps
