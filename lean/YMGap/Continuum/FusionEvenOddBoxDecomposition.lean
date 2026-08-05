/-
`FusionEvenOddBoxDecomposition` — the exact even/odd decomposition of the
weighted Clebsch box and of its remaining finite interlacing triangle.

# The decomposition

For an even output channel `2*n`, Clebsch parity forces the two input degrees
to have the same parity.  Thus the weighted box is the sum of its even-even
and odd-odd sectors.  For an odd output channel `2*n+1`, the inputs have
opposite parity.  Symmetry under exchange of the two input degrees identifies
the odd-even and even-odd sectors, so the odd channel is twice one oriented
sector.

Writing

    E_n = boxSum w N (2*n),       O_n = boxSum w N (2*n+1),

in these sector coordinates, the finite weighted-interlacing residual splits
exactly into the two alternating heat-exchange margins

    O_n^2       - E_n E_(n+1),
    E_(n+1)^2   - O_n O_(n+1).

The compiler at the end proves that these two half-triangle families are
equivalent to the original finite `quadDiff` triangle.  It does not prove the
margins nonnegative: that is still the heat-kernel-specific weighted exchange
input.  No same-parity row theorem is silently promoted to a mixed-parity
claim.

# Relation to `(r,d)` coordinates

With `i=a+1`, `j=b+1`, `r=i+j`, the same-parity sectors have even `r` and the
opposite-parity sectors have odd `r`.  The elementary parity bridge is recorded
below, tying this split to the exact per-term diagonalization in
`FusionRDFactor` without asserting the known-false naive rectangular reindex.

# Constructive contract

Mathlib-free; pure `Q'`/`Nat`.  No `Classical`, `native_decide`, `sorry`, new
axiom, or noncomputable definition.  Load-bearing declarations are axiom gated
at the end.
-/

import YMGap.Continuum.FusionWeightedBoxInterlacing
import YMGap.Continuum.FusionRDFactor

namespace YMGap.Continuum.FusionEvenOddBoxDecomposition

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionWeightedBoxInterlacing

/-! ## 1. Parity-filtered box sectors -/

/-- A single box-kernel term restricted to prescribed input parities. -/
def paritySectorTerm (w : Q') (s pa pb a b : Nat) : Q' :=
  if a % 2 = pa ∧ b % 2 = pb then boxKer w s a b else 0

/-- The finite weighted box restricted to prescribed input parities. -/
def paritySector (w : Q') (N s pa pb : Nat) : Q' :=
  fsum (fun a => fsum (fun b => paritySectorTerm w s pa pb a b) (N + 1)) (N + 1)

def evenEvenBox (w : Q') (N s : Nat) : Q' := paritySector w N s 0 0
def evenOddBox (w : Q') (N s : Nat) : Q' := paritySector w N s 0 1
def oddEvenBox (w : Q') (N s : Nat) : Q' := paritySector w N s 1 0
def oddOddBox (w : Q') (N s : Nat) : Q' := paritySector w N s 1 1

private theorem mul_eqv_congr {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') : (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem fsum2_add (F G : Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (fun b => F a b + G a b) n) n).eqv
      (fsum (fun a => fsum (F a) n) n + fsum (fun a => fsum (G a) n) n) :=
  Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun a => fsum_add (F a) (G a) n) n)
    (fsum_add (fun a => fsum (F a) n) (fun a => fsum (G a) n) n)

/-- The weighted Clebsch kernel is symmetric in its two input degrees. -/
theorem boxKer_swap (w : Q') (s a b : Nat) :
    (boxKer w s a b).eqv (boxKer w s b a) := by
  unfold boxKer
  have hind : fusionInd a b s = fusionInd b a s := by
    unfold fusionInd
    rw [fusionOK_symm_ab]
  rw [hind]
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (coeffW w a) (coeffW w b))

/-- A kernel term vanishes when its Clebsch parity test fails. -/
private theorem boxKer_eqv_zero_of_parity {w : Q'} {s a b : Nat}
    (hpar : (a + b + s) % 2 ≠ 0) : (boxKer w s a b).eqv 0 := by
  have hok : fusionOK a b s = false := by
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_false_iff]
    rintro ⟨_, _, hp⟩
    exact hpar hp
  unfold boxKer fusionInd
  rw [hok]
  exact q_zero_mul _

private theorem mod_two_eq_one_of_ne_zero (a : Nat) (h : a % 2 ≠ 0) : a % 2 = 1 := by
  have hlt : a % 2 < 2 := Nat.mod_lt a (by decide)
  omega

/-- Pointwise even-channel split: only even-even and odd-odd inputs survive. -/
private theorem boxKer_even_split (w : Q') (n a b : Nat) :
    (boxKer w (2 * n) a b).eqv
      (paritySectorTerm w (2 * n) 0 0 a b +
        paritySectorTerm w (2 * n) 1 1 a b) := by
  by_cases ha0 : a % 2 = 0
  · by_cases hb0 : b % 2 = 0
    · have ha1 : a % 2 ≠ 1 := by omega
      have hb1 : b % 2 ≠ 1 := by omega
      unfold paritySectorTerm
      rw [if_pos ⟨ha0, hb0⟩, if_neg (by rintro ⟨ha, _⟩; exact ha1 ha)]
      exact Q'.eqv_symm (q_add_zero_eqv _)
    · have hb1 : b % 2 = 1 := mod_two_eq_one_of_ne_zero b hb0
      have ha1 : a % 2 ≠ 1 := by omega
      have hzero : (boxKer w (2 * n) a b).eqv 0 :=
        boxKer_eqv_zero_of_parity (by omega)
      unfold paritySectorTerm
      rw [if_neg (by rintro ⟨_, hb⟩; exact hb0 hb),
        if_neg (by rintro ⟨ha, _⟩; exact ha1 ha)]
      exact Q'.eqv_trans _ _ _ hzero (Q'.eqv_symm (q_zero_add_eqv 0))
  · have ha1 : a % 2 = 1 := mod_two_eq_one_of_ne_zero a ha0
    by_cases hb0 : b % 2 = 0
    · have hb1 : b % 2 ≠ 1 := by omega
      have hzero : (boxKer w (2 * n) a b).eqv 0 :=
        boxKer_eqv_zero_of_parity (by omega)
      unfold paritySectorTerm
      rw [if_neg (by rintro ⟨ha, _⟩; exact ha0 ha),
        if_neg (by rintro ⟨_, hb⟩; exact hb1 hb)]
      exact Q'.eqv_trans _ _ _ hzero (Q'.eqv_symm (q_zero_add_eqv 0))
    · have hb1 : b % 2 = 1 := mod_two_eq_one_of_ne_zero b hb0
      unfold paritySectorTerm
      rw [if_neg (by rintro ⟨ha, _⟩; exact ha0 ha), if_pos ⟨ha1, hb1⟩]
      exact Q'.eqv_symm (q_zero_add_eqv _)

/-- Pointwise odd-channel split: only even-odd and odd-even inputs survive. -/
private theorem boxKer_odd_split (w : Q') (n a b : Nat) :
    (boxKer w (2 * n + 1) a b).eqv
      (paritySectorTerm w (2 * n + 1) 0 1 a b +
        paritySectorTerm w (2 * n + 1) 1 0 a b) := by
  by_cases ha0 : a % 2 = 0
  · by_cases hb0 : b % 2 = 0
    · have ha1 : a % 2 ≠ 1 := by omega
      have hb1 : b % 2 ≠ 1 := by omega
      have hzero : (boxKer w (2 * n + 1) a b).eqv 0 :=
        boxKer_eqv_zero_of_parity (by omega)
      unfold paritySectorTerm
      rw [if_neg (by rintro ⟨_, hb⟩; exact hb1 hb),
        if_neg (by rintro ⟨ha, _⟩; exact ha1 ha)]
      exact Q'.eqv_trans _ _ _ hzero (Q'.eqv_symm (q_zero_add_eqv 0))
    · have hb1 : b % 2 = 1 := mod_two_eq_one_of_ne_zero b hb0
      have ha1 : a % 2 ≠ 1 := by omega
      unfold paritySectorTerm
      rw [if_pos ⟨ha0, hb1⟩, if_neg (by rintro ⟨ha, _⟩; exact ha1 ha)]
      exact Q'.eqv_symm (q_add_zero_eqv _)
  · have ha1 : a % 2 = 1 := mod_two_eq_one_of_ne_zero a ha0
    by_cases hb0 : b % 2 = 0
    · have hb1 : b % 2 ≠ 1 := by omega
      unfold paritySectorTerm
      rw [if_neg (by rintro ⟨ha, _⟩; exact ha0 ha), if_pos ⟨ha1, hb0⟩]
      exact Q'.eqv_symm (q_zero_add_eqv _)
    · have hb1 : b % 2 = 1 := mod_two_eq_one_of_ne_zero b hb0
      have hzero : (boxKer w (2 * n + 1) a b).eqv 0 :=
        boxKer_eqv_zero_of_parity (by omega)
      unfold paritySectorTerm
      rw [if_neg (by rintro ⟨ha, _⟩; exact ha0 ha),
        if_neg (by rintro ⟨_, hb⟩; exact hb0 hb)]
      exact Q'.eqv_trans _ _ _ hzero (Q'.eqv_symm (q_zero_add_eqv 0))

/-- Every even channel is exactly its even-even plus odd-odd sector. -/
theorem boxSum_even_eq_sectors (w : Q') (N n : Nat) :
    (boxSum w N (2 * n)).eqv
      (evenEvenBox w N (2 * n) + oddOddBox w N (2 * n)) := by
  rw [boxSum_eq_ker]
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun a =>
      fsum_eqv_congr _ _ (fun b => boxKer_even_split w n a b) (N + 1)) (N + 1)) ?_
  exact fsum2_add
    (fun a b => paritySectorTerm w (2 * n) 0 0 a b)
    (fun a b => paritySectorTerm w (2 * n) 1 1 a b) (N + 1)

/-- Every odd channel is exactly its even-odd plus odd-even sector. -/
theorem boxSum_odd_eq_sectors (w : Q') (N n : Nat) :
    (boxSum w N (2 * n + 1)).eqv
      (evenOddBox w N (2 * n + 1) + oddEvenBox w N (2 * n + 1)) := by
  rw [boxSum_eq_ker]
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _ (fun a =>
      fsum_eqv_congr _ _ (fun b => boxKer_odd_split w n a b) (N + 1)) (N + 1)) ?_
  exact fsum2_add
    (fun a b => paritySectorTerm w (2 * n + 1) 0 1 a b)
    (fun a b => paritySectorTerm w (2 * n + 1) 1 0 a b) (N + 1)

/-! ## 2. One-sided odd sector and `(r,d)` parity -/

/-- Exchanging the two box indices identifies the odd-even and even-odd
sectors.  This is valid for every channel, not only odd channels. -/
theorem oddEvenBox_eq_evenOddBox (w : Q') (N s : Nat) :
    (oddEvenBox w N s).eqv (evenOddBox w N s) := by
  unfold oddEvenBox evenOddBox paritySector
  refine Q'.eqv_trans _ _ _
    (fsum_swap (fun a b => paritySectorTerm w s 1 0 a b) (N + 1) (N + 1)) ?_
  refine fsum_eqv_congr _ _ (fun b => ?_) (N + 1)
  refine fsum_eqv_congr _ _ (fun a => ?_) (N + 1)
  unfold paritySectorTerm
  by_cases h : a % 2 = 1 ∧ b % 2 = 0
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    exact boxKer_swap w s a b
  · rw [if_neg h, if_neg (by rintro ⟨hb, ha⟩; exact h ⟨ha, hb⟩)]
    exact Q'.eqv_refl 0

/-- Even-even input degrees give even `r=(a+1)+(b+1)`. -/
theorem evenEven_r_even {a b : Nat} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    ((a + 1) + (b + 1)) % 2 = 0 := by omega

/-- Odd-odd input degrees also give even `r=(a+1)+(b+1)`. -/
theorem oddOdd_r_even {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    ((a + 1) + (b + 1)) % 2 = 0 := by omega

/-- Even-odd input degrees give odd `r=(a+1)+(b+1)`. -/
theorem evenOdd_r_odd {a b : Nat} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    ((a + 1) + (b + 1)) % 2 = 1 := by omega

/-- Odd-even input degrees also give odd `r=(a+1)+(b+1)`. -/
theorem oddEven_r_odd {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 0) :
    ((a + 1) + (b + 1)) % 2 = 1 := by omega

/-! ## 3. Exact alternating mode masses -/

/-- The same-parity sector mass representing channel `2*n`. -/
def evenModeMass (w : Q') (N n : Nat) : Q' :=
  evenEvenBox w N (2 * n) + oddOddBox w N (2 * n)

/-- One oriented opposite-parity half of channel `2*n+1`. -/
def oddModeHalfMass (w : Q') (N n : Nat) : Q' :=
  evenOddBox w N (2 * n + 1)

/-- The full opposite-parity mass, expressed as twice its oriented half. -/
def oddModeMass (w : Q') (N n : Nat) : Q' :=
  oddModeHalfMass w N n + oddModeHalfMass w N n

/-- The even box channel is exactly `evenModeMass`. -/
theorem boxSum_even_eq_evenModeMass (w : Q') (N n : Nat) :
    (boxSum w N (2 * n)).eqv (evenModeMass w N n) :=
  boxSum_even_eq_sectors w N n

/-- The odd box channel is exactly twice its oriented even-odd sector. -/
theorem boxSum_odd_eq_oddModeMass (w : Q') (N n : Nat) :
    (boxSum w N (2 * n + 1)).eqv (oddModeMass w N n) := by
  refine Q'.eqv_trans _ _ _ (boxSum_odd_eq_sectors w N n) ?_
  exact Q'.add_eqv_congr_left _ _ _ (oddEvenBox_eq_evenOddBox w N (2 * n + 1))

/-! ## 4. The two exact heat-exchange margins -/

/-- The even-channel interlacing margin `O_n^2 - E_n E_(n+1)`. -/
def evenExchangeMargin (w : Q') (N n : Nat) : Q' :=
  oddModeMass w N n * oddModeMass w N n +
    -(evenModeMass w N n * evenModeMass w N (n + 1))

/-- The odd-channel interlacing margin `E_(n+1)^2 - O_n O_(n+1)`. -/
def oddExchangeMargin (w : Q') (N n : Nat) : Q' :=
  evenModeMass w N (n + 1) * evenModeMass w N (n + 1) +
    -(oddModeMass w N n * oddModeMass w N (n + 1))

/-- `quadDiff` at an even channel is exactly the even-to-odd exchange margin. -/
theorem quadDiff_even_eq_exchangeMargin (w : Q') (N n : Nat) :
    (quadDiff w N (2 * n)).eqv (evenExchangeMargin w N n) := by
  have hodd := boxSum_odd_eq_oddModeMass w N n
  have heven := boxSum_even_eq_evenModeMass w N n
  have hevenNext : (boxSum w N (2 * n + 2)).eqv (evenModeMass w N (n + 1)) := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      boxSum_even_eq_evenModeMass w N (n + 1)
  have hbox :
      (boxSum w N (2 * n + 1) * boxSum w N (2 * n + 1) +
        -(boxSum w N (2 * n) * boxSum w N (2 * n + 2))).eqv
        (evenExchangeMargin w N n) := by
    unfold evenExchangeMargin
    exact Q'.add_eqv_congr' (mul_eqv_congr hodd hodd)
      (Q'.neg_eqv_congr _ _ (mul_eqv_congr heven hevenNext))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (boxDiff_eq_quadDiff w N (2 * n))) hbox

/-- `quadDiff` at an odd channel is exactly the odd-to-even exchange margin. -/
theorem quadDiff_odd_eq_exchangeMargin (w : Q') (N n : Nat) :
    (quadDiff w N (2 * n + 1)).eqv (oddExchangeMargin w N n) := by
  have hevenNext : (boxSum w N (2 * n + 2)).eqv (evenModeMass w N (n + 1)) := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      boxSum_even_eq_evenModeMass w N (n + 1)
  have hodd := boxSum_odd_eq_oddModeMass w N n
  have hoddNext : (boxSum w N (2 * n + 3)).eqv (oddModeMass w N (n + 1)) := by
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
      boxSum_odd_eq_oddModeMass w N (n + 1)
  have hbox :
      (boxSum w N (2 * n + 2) * boxSum w N (2 * n + 2) +
        -(boxSum w N (2 * n + 1) * boxSum w N (2 * n + 3))).eqv
        (oddExchangeMargin w N n) := by
    unfold oddExchangeMargin
    exact Q'.add_eqv_congr' (mul_eqv_congr hevenNext hevenNext)
      (Q'.neg_eqv_congr _ _ (mul_eqv_congr hodd hoddNext))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (boxDiff_eq_quadDiff w N (2 * n + 1))) hbox

/-! ## 5. Exact compiler for the remaining finite triangle -/

/-- The two alternating half-triangle margin families imply every inequality
in the original finite weighted-interlacing triangle. -/
theorem quadDiff_nonneg_of_exchangeMargins {w : Q'} (N : Nat)
    (heven : ∀ n, n + 1 ≤ N → (0 : Q') ≤ evenExchangeMargin w N n)
    (hodd : ∀ n, 2 * n + 3 ≤ 2 * N → (0 : Q') ≤ oddExchangeMargin w N n) :
    ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s := by
  intro s hs
  by_cases hs0 : s % 2 = 0
  · let n := s / 2
    have hsn : s = 2 * n := by
      dsimp [n]
      have hlt : s % 2 < 2 := Nat.mod_lt s (by decide)
      omega
    rw [hsn] at hs ⊢
    exact Q'.le_trans' _ _ _ (heven n (by omega))
      (Q'.ge_of_eqv (quadDiff_even_eq_exchangeMargin w N n))
  · let n := s / 2
    have hs1 : s % 2 = 1 := mod_two_eq_one_of_ne_zero s hs0
    have hsn : s = 2 * n + 1 := by
      dsimp [n]
      have hlt : s % 2 < 2 := Nat.mod_lt s (by decide)
      omega
    rw [hsn] at hs ⊢
    exact Q'.le_trans' _ _ _ (hodd n (by omega))
      (Q'.ge_of_eqv (quadDiff_odd_eq_exchangeMargin w N n))

/-- Conversely, the original finite triangle supplies both exchange-margin
families.  Together with `quadDiff_nonneg_of_exchangeMargins`, this shows that
the parity split is an exact reduction rather than a stronger assumption. -/
theorem exchangeMargins_of_quadDiff_nonneg {w : Q'} (N : Nat)
    (hfinite : ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s) :
    (∀ n, n + 1 ≤ N → (0 : Q') ≤ evenExchangeMargin w N n) ∧
      (∀ n, 2 * n + 3 ≤ 2 * N → (0 : Q') ≤ oddExchangeMargin w N n) := by
  constructor
  · intro n hn
    exact Q'.le_trans' _ _ _ (hfinite (2 * n) (by omega))
      (Q'.le_of_eqv (quadDiff_even_eq_exchangeMargin w N n))
  · intro n hn
    exact Q'.le_trans' _ _ _ (hfinite (2 * n + 1) (by omega))
      (Q'.le_of_eqv (quadDiff_odd_eq_exchangeMargin w N n))

/-! ## Axiom gates -/

#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.boxKer_swap
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.boxSum_even_eq_sectors
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.boxSum_odd_eq_sectors
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.oddEvenBox_eq_evenOddBox
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.boxSum_even_eq_evenModeMass
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.boxSum_odd_eq_oddModeMass
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.quadDiff_even_eq_exchangeMargin
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.quadDiff_odd_eq_exchangeMargin
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.quadDiff_nonneg_of_exchangeMargins
#print axioms YMGap.Continuum.FusionEvenOddBoxDecomposition.exchangeMargins_of_quadDiff_nonneg

end YMGap.Continuum.FusionEvenOddBoxDecomposition
