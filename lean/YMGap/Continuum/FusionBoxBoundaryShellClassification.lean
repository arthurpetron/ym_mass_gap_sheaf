/-
`FusionBoxBoundaryShellClassification` -- exact first physical shells of the
all-cutoff fusion-box determinant.

The canonical four-index coefficient compiler is much larger than the piece
of it needed at the post-boundary seam.  Convexity leaves only the balanced
Clebsch--Gordan pairs in the first shells.  This module classifies those pairs
and evaluates the resulting finite integer buckets symbolically for every
cutoff.

For orientation, an independent executable scout used the exact factorization

    raw(N,s) = P(N,s+1)^2 - P(N,s) P(N,s+2)

and checked every physical channel and every four-adic prefix through
`N = 100`.  It found no negative prefix; the smallest post-boundary value was
`12`, at `(s,k)=(0,3)`.  That computation is evidence only.  None of the
theorems below depends on the finite census.
-/

import YMGap.Continuum.FusionBoxFirstShellReserve

namespace YMGap.Continuum.FusionBoxBoundaryShellClassification

open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionBoxBernsteinReconstruction
open YMGap.Continuum.FusionBoxPrefixReserve
open YMGap.Continuum.FusionBoxFirstShellReserve

/-! ## 1. Constructive integer-bucket selectors -/

private theorem intFsum_congr_local (f g : Nat -> Int) : forall n,
    (forall i, i < n -> f i = g i) -> intFsum f n = intFsum g n
  | 0, _ => rfl
  | n + 1, h => by
      rw [intFsum, intFsum, intFsum_congr_local f g n
        (fun i hi => h i (by omega)), h n (by omega)]

private theorem intFsum_add_local (f g : Nat -> Int) : forall n,
    intFsum (fun i => f i + g i) n = intFsum f n + intFsum g n
  | 0 => by simp [intFsum]
  | n + 1 => by
      rw [intFsum, intFsum, intFsum, intFsum_add_local f g n]
      omega

private theorem boxCellIntSum_congr_local
    {N : Nat} {f g : Nat -> Nat -> Nat -> Nat -> Int}
    (h : forall a a' b b', a < N + 1 -> a' < N + 1 ->
      b < N + 1 -> b' < N + 1 -> f a a' b b' = g a a' b b') :
    boxCellIntSum N f = boxCellIntSum N g := by
  unfold boxCellIntSum
  apply intFsum_congr_local
  intro a ha
  apply intFsum_congr_local
  intro a' ha'
  apply intFsum_congr_local
  intro b hb
  apply intFsum_congr_local
  intro b' hb'
  exact h a a' b b' ha ha' hb hb'

private theorem boxCellIntSum_add_local
    (N : Nat) (f g : Nat -> Nat -> Nat -> Nat -> Int) :
    boxCellIntSum N (fun a a' b b' => f a a' b b' + g a a' b b') =
      boxCellIntSum N f + boxCellIntSum N g := by
  unfold boxCellIntSum
  rw [intFsum_congr_local
      (fun a => intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
        f a a' b b' + g a a' b b') (N + 1)) (N + 1)) (N + 1))
      (fun a => intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
        f a a' b b') (N + 1)) (N + 1)) (N + 1) +
        intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
          g a a' b b') (N + 1)) (N + 1)) (N + 1)) (N + 1)]
  · exact intFsum_add_local _ _ (N + 1)
  · intro a _
    rw [intFsum_congr_local
        (fun a' => intFsum (fun b => intFsum (fun b' =>
          f a a' b b' + g a a' b b') (N + 1)) (N + 1))
        (fun a' => intFsum (fun b => intFsum (fun b' =>
          f a a' b b') (N + 1)) (N + 1) +
          intFsum (fun b => intFsum (fun b' =>
            g a a' b b') (N + 1)) (N + 1)) (N + 1)]
    · exact intFsum_add_local _ _ (N + 1)
    · intro a' _
      rw [intFsum_congr_local
          (fun b => intFsum (fun b' => f a a' b b' + g a a' b b') (N + 1))
          (fun b => intFsum (fun b' => f a a' b b') (N + 1) +
            intFsum (fun b' => g a a' b b') (N + 1)) (N + 1)]
      · exact intFsum_add_local _ _ (N + 1)
      · intro b _
        exact intFsum_add_local _ _ (N + 1)

private def intDelta (target value : Nat) : Int :=
  if value = target then 1 else 0

@[simp] private theorem intFsum_zero_local : forall n,
    intFsum (fun _ => (0 : Int)) n = 0
  | 0 => rfl
  | n + 1 => by rw [intFsum, intFsum_zero_local n, Int.add_zero]

private theorem intFsum_delta (target : Nat) : forall n,
    target < n -> intFsum (intDelta target) n = 1
  | 0, h => by omega
  | n + 1, h => by
      rw [intFsum]
      by_cases hn : target = n
      · subst target
        have hzero : intFsum (intDelta n) n = 0 := by
          rw [intFsum_congr_local (intDelta n) (fun _ => 0) n]
          · exact intFsum_zero_local n
          · intro i hi
            unfold intDelta
            simp [Nat.ne_of_lt hi]
        rw [hzero]
        unfold intDelta
        simp
      · have hlt : target < n := by omega
        rw [intFsum_delta target n hlt]
        unfold intDelta
        simp [Ne.symm hn]

private theorem intFsum_delta_mul
    (target n : Nat) (h : target < n) (z : Int) :
    intFsum (fun value => intDelta target value * z) n = z := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [intFsum]
      by_cases hn : target = n
      · subst target
        have hprefix : intFsum (fun value => intDelta n value * z) n = 0 := by
          rw [intFsum_congr_local _ (fun _ => 0) n]
          · exact intFsum_zero_local n
          · intro i hi
            unfold intDelta
            simp [Nat.ne_of_lt hi]
        rw [hprefix]
        unfold intDelta
        simp
      · have hlt : target < n := by omega
        rw [ih hlt]
        unfold intDelta
        simp [Ne.symm hn]

private def cellAt
    (A A' B B' : Nat) (z : Int) (a a' b b' : Nat) : Int :=
  intDelta B' b' *
    (intDelta B b * (intDelta A' a' * (intDelta A a * z)))

private theorem boxCellIntSum_cellAt
    (N A A' B B' : Nat) (z : Int)
    (hA : A <= N) (hA' : A' <= N) (hB : B <= N) (hB' : B' <= N) :
    boxCellIntSum N (cellAt A A' B B' z) = z := by
  unfold boxCellIntSum cellAt
  rw [intFsum_congr_local _
      (fun a => intFsum (fun a' => intFsum (fun b =>
        intDelta B b * (intDelta A' a' * (intDelta A a * z)))
        (N + 1)) (N + 1)) (N + 1)]
  · rw [intFsum_congr_local _
        (fun a => intFsum (fun a' =>
          intDelta A' a' * (intDelta A a * z)) (N + 1)) (N + 1)]
    · rw [intFsum_congr_local _
          (fun a => intDelta A a * z) (N + 1)]
      · exact intFsum_delta_mul A (N + 1) (by omega) z
      · intro a _
        exact intFsum_delta_mul A' (N + 1) (by omega) (intDelta A a * z)
    · intro a _
      apply intFsum_congr_local
      intro a' _
      exact intFsum_delta_mul B (N + 1) (by omega)
        (intDelta A' a' * (intDelta A a * z))
  · intro a _
    apply intFsum_congr_local
    intro a' _
    apply intFsum_congr_local
    intro b _
    exact intFsum_delta_mul B' (N + 1) (by omega)
      (intDelta B b * (intDelta A' a' * (intDelta A a * z)))

private theorem fusionOK_at_exact_sum
    (a b t : Nat) (h : a + b = t) : fusionOK a b t = true := by
  apply (fusionOK_strand a b t).mpr
  exact ⟨b, a, 0, by omega, by omega, by omega⟩

private theorem fusionOK_succ_false_at_exact_sum
    (a b t : Nat) (h : a + b = t) : fusionOK a b (t + 1) = false := by
  cases hok : fusionOK a b (t + 1) with
  | false => rfl
  | true =>
      obtain ⟨p, q, r, ha, hb, ht⟩ := (fusionOK_strand a b (t + 1)).mp hok
      omega

private theorem fusionOK_prev_false_at_exact_succ_sum
    (a b t : Nat) (h : a + b = t + 1) : fusionOK a b t = false := by
  cases hok : fusionOK a b t with
  | false => rfl
  | true =>
      obtain ⟨p, q, r, ha, hb, ht⟩ := (fusionOK_strand a b t).mp hok
      omega

/-! ## 2. Positive prefix reserves -/

private theorem intFsum_le_local {f g : Nat -> Int}
    (h : forall i, f i <= g i) : forall n, intFsum f n <= intFsum g n
  | 0 => Int.le_refl 0
  | n + 1 => by
      rw [intFsum, intFsum]
      exact Int.add_le_add (intFsum_le_local h n) (h n)

private theorem boxCellIntSum_le_local
    {N : Nat} {f g : Nat -> Nat -> Nat -> Nat -> Int}
    (h : forall a a' b b', f a a' b b' <= g a a' b b') :
    boxCellIntSum N f <= boxCellIntSum N g := by
  unfold boxCellIntSum
  apply intFsum_le_local
  intro a
  apply intFsum_le_local
  intro a'
  apply intFsum_le_local
  intro b
  apply intFsum_le_local
  intro b'
  exact h a a' b b'

private theorem boxCellIntSum_zero_local (N : Nat) :
    boxCellIntSum N (fun _ _ _ _ => 0) = 0 := by
  unfold boxCellIntSum
  simp only [intFsum_zero_local]

private theorem cellAt_eq_if
    (A A' B B' : Nat) (z : Int) (a a' b b' : Nat) :
    cellAt A A' B B' z a a' b b' =
      if a = A ∧ a' = A' ∧ b = B ∧ b' = B' then z else 0 := by
  by_cases ha : a = A <;> by_cases ha' : a' = A' <;>
      by_cases hb : b = B <;> by_cases hb' : b' = B' <;>
      simp [cellAt, intDelta, ha, ha', hb, hb']

private theorem boxPositiveClearedCell_nonnegative
    (N s a a' b b' : Nat) :
    0 <= boxPositiveClearedCell N s a a' b b' := by
  unfold boxPositiveClearedCell
  change 0 <= (Int.ofNat _)
  exact Int.natCast_nonneg _

private theorem boxPositiveClearedPrefix_nonnegative
    (N s K : Nat) : 0 <= boxPositiveClearedPrefix N s K := by
  unfold boxPositiveClearedPrefix
  have hsum := boxCellIntSum_le_local
    (N := N) (f := fun _ _ _ _ => 0)
    (g := fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' < K then
        boxPositiveClearedCell N s a a' b b'
      else 0)
    (fun a a' b b' => by
      change (0 : Int) <=
        if boxQuadHalfExponent a a' b b' < K then
          boxPositiveClearedCell N s a a' b b'
        else 0
      by_cases h : boxQuadHalfExponent a a' b b' < K
      · rw [if_pos h]
        exact boxPositiveClearedCell_nonnegative N s a a' b b'
      · rw [if_neg h]
        exact Int.le_refl 0)
  rw [boxCellIntSum_zero_local] at hsum
  exact hsum

private theorem boxPositiveClearedCell_eq_active
    {N s a a' b b' k weight : Nat}
    (hl : fusionOK a b (s + 1) = true)
    (hr : fusionOK a' b' (s + 1) = true)
    (he : boxQuadHalfExponent a a' b b' = k)
    (hdim : boxQuadDimension a a' b b' = weight) :
    boxPositiveClearedCell N s a a' b b' =
      Int.ofNat (weight * 4 ^ (boxBernsteinDegree N - k)) := by
  unfold boxPositiveClearedCell boxCellClearedMultiplicity
    boxPositiveMultiplicity boxProductMultiplicity
  simp [hl, hr, he, hdim]

private theorem boxNegativeClearedCell_eq_active
    {N s a a' b b' k weight : Nat}
    (hl : fusionOK a b s = true)
    (hr : fusionOK a' b' (s + 2) = true)
    (he : boxQuadHalfExponent a a' b b' = k)
    (hdim : boxQuadDimension a a' b b' = weight) :
    boxNegativeClearedCell N s a a' b b' =
      Int.ofNat (weight * 4 ^ (boxBernsteinDegree N - k)) := by
  unfold boxNegativeClearedCell boxCellClearedMultiplicity
    boxNegativeMultiplicity boxProductMultiplicity
  simp [hl, hr, he, hdim]

private theorem half_double_sum (x : Nat) : (x + x) / 2 = x := by
  rw [← Nat.mul_two x, Nat.mul_div_left x (by decide)]

private theorem pow_four_eq_square_square (x : Nat) :
    x ^ 4 = (x * x) * (x * x) := by
  simp [Nat.pow_succ, Nat.mul_assoc]

/-- One of the four balanced positive cells at the first even shell. -/
def evenFirstShellCellWeight (N m : Nat) : Int :=
  Int.ofNat
    ((((m + 1) * (m + 2)) ^ 2) *
      4 ^ (boxBernsteinDegree N - (c4 m + c4 (m + 1))))

/-- The complete four-orientation positive reserve at the first even shell. -/
def evenFirstShellPositiveReserve (N m : Nat) : Int :=
  4 * evenFirstShellCellWeight N m

/-- One central positive cell at the first odd shell. -/
def oddFirstShellCellWeight (N m : Nat) : Int :=
  Int.ofNat
    ((m + 2) ^ 4 *
      4 ^ (boxBernsteinDegree N - 2 * c4 (m + 1)))

/-- One displacement/displacement positive cell two shells above the odd
boundary. -/
def oddSecondShellCellWeight (N m : Nat) : Int :=
  Int.ofNat
    ((((m + 1) * (m + 3)) ^ 2) *
      4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 2)))

/-- The sharp odd reserve used by the scalar payment: the central cell plus
the four displacement/displacement cells.  The four nonnegative mixed cells
in the intervening shell are deliberately not charged. -/
def oddSecondShellPositiveReserve (N m : Nat) : Int :=
  oddFirstShellCellWeight N m + 4 * oddSecondShellCellWeight N m

/-- One of the four first-shell odd outer-product cells. -/
def oddFirstNegativeShellCellWeight (N m : Nat) : Int :=
  Int.ofNat
    ((((m + 1) * (m + 2)) * ((m + 2) * (m + 3))) *
      4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1)))

private def evenFirstShellSparse
    (N m a a' b b' : Nat) : Int :=
  cellAt m m (m + 1) (m + 1) (evenFirstShellCellWeight N m) a a' b b' +
    (cellAt m (m + 1) (m + 1) m (evenFirstShellCellWeight N m) a a' b b' +
      (cellAt (m + 1) m m (m + 1) (evenFirstShellCellWeight N m) a a' b b' +
        cellAt (m + 1) (m + 1) m m
          (evenFirstShellCellWeight N m) a a' b b'))

private def oddSecondShellSparse
    (N m a a' b b' : Nat) : Int :=
  cellAt (m + 1) (m + 1) (m + 1) (m + 1)
      (oddFirstShellCellWeight N m) a a' b b' +
    (cellAt m m (m + 2) (m + 2)
        (oddSecondShellCellWeight N m) a a' b b' +
      (cellAt m (m + 2) (m + 2) m
          (oddSecondShellCellWeight N m) a a' b b' +
        (cellAt (m + 2) m m (m + 2)
            (oddSecondShellCellWeight N m) a a' b b' +
          cellAt (m + 2) (m + 2) m m
            (oddSecondShellCellWeight N m) a a' b b')))

private def oddFirstNegativeShellSparse
    (N m a a' b b' : Nat) : Int :=
  cellAt m (m + 1) (m + 1) (m + 2)
      (oddFirstNegativeShellCellWeight N m) a a' b b' +
    (cellAt m (m + 2) (m + 1) (m + 1)
        (oddFirstNegativeShellCellWeight N m) a a' b b' +
      (cellAt (m + 1) (m + 1) m (m + 2)
          (oddFirstNegativeShellCellWeight N m) a a' b b' +
        cellAt (m + 1) (m + 2) m (m + 1)
          (oddFirstNegativeShellCellWeight N m) a a' b b'))

private theorem oddSecondShellSparse_at_center (N m : Nat) :
    oddSecondShellSparse N m (m + 1) (m + 1) (m + 1) (m + 1) =
      oddFirstShellCellWeight N m := by
  unfold oddSecondShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if,
    cellAt_eq_if]
  rw [if_pos ⟨rfl, rfl, rfl, rfl⟩,
    if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_neg (fun h => by omega), if_neg (fun h => by omega)]
  omega

private theorem oddSecondShellSparse_at_far00 (N m : Nat) :
    oddSecondShellSparse N m m m (m + 2) (m + 2) =
      oddSecondShellCellWeight N m := by
  unfold oddSecondShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if,
    cellAt_eq_if]
  rw [if_neg (fun h => by omega), if_pos ⟨rfl, rfl, rfl, rfl⟩,
    if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_neg (fun h => by omega)]
  omega

private theorem oddSecondShellSparse_at_far01 (N m : Nat) :
    oddSecondShellSparse N m m (m + 2) (m + 2) m =
      oddSecondShellCellWeight N m := by
  unfold oddSecondShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if,
    cellAt_eq_if]
  rw [if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_pos ⟨rfl, rfl, rfl, rfl⟩, if_neg (fun h => by omega),
    if_neg (fun h => by omega)]
  omega

private theorem oddSecondShellSparse_at_far10 (N m : Nat) :
    oddSecondShellSparse N m (m + 2) m m (m + 2) =
      oddSecondShellCellWeight N m := by
  unfold oddSecondShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if,
    cellAt_eq_if]
  rw [if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_neg (fun h => by omega), if_pos ⟨rfl, rfl, rfl, rfl⟩,
    if_neg (fun h => by omega)]
  omega

private theorem oddSecondShellSparse_at_far11 (N m : Nat) :
    oddSecondShellSparse N m (m + 2) (m + 2) m m =
      oddSecondShellCellWeight N m := by
  unfold oddSecondShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if,
    cellAt_eq_if]
  rw [if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_pos ⟨rfl, rfl, rfl, rfl⟩]
  omega

private theorem oddFirstNegativeShellSparse_at_00 (N m : Nat) :
    oddFirstNegativeShellSparse N m m (m + 1) (m + 1) (m + 2) =
      oddFirstNegativeShellCellWeight N m := by
  unfold oddFirstNegativeShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  rw [if_pos ⟨rfl, rfl, rfl, rfl⟩, if_neg (fun h => by omega),
    if_neg (fun h => by omega), if_neg (fun h => by omega)]
  omega

private theorem oddFirstNegativeShellSparse_at_01 (N m : Nat) :
    oddFirstNegativeShellSparse N m m (m + 2) (m + 1) (m + 1) =
      oddFirstNegativeShellCellWeight N m := by
  unfold oddFirstNegativeShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  rw [if_neg (fun h => by omega), if_pos ⟨rfl, rfl, rfl, rfl⟩,
    if_neg (fun h => by omega), if_neg (fun h => by omega)]
  omega

private theorem oddFirstNegativeShellSparse_at_10 (N m : Nat) :
    oddFirstNegativeShellSparse N m (m + 1) (m + 1) m (m + 2) =
      oddFirstNegativeShellCellWeight N m := by
  unfold oddFirstNegativeShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  rw [if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_pos ⟨rfl, rfl, rfl, rfl⟩, if_neg (fun h => by omega)]
  omega

private theorem oddFirstNegativeShellSparse_at_11 (N m : Nat) :
    oddFirstNegativeShellSparse N m (m + 1) (m + 2) m (m + 1) =
      oddFirstNegativeShellCellWeight N m := by
  unfold oddFirstNegativeShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  rw [if_neg (fun h => by omega), if_neg (fun h => by omega),
    if_neg (fun h => by omega), if_pos ⟨rfl, rfl, rfl, rfl⟩]
  omega

private theorem evenFirstShellExponent00 (m : Nat) :
    boxQuadHalfExponent m m (m + 1) (m + 1) =
      c4 m + c4 (m + 1) := by
  unfold boxQuadHalfExponent boxQuadExponent
  exact half_double_sum (c4 m + c4 (m + 1))

private theorem evenFirstShellSparse_at_00
    (N m : Nat) :
    evenFirstShellSparse N m m m (m + 1) (m + 1) =
      evenFirstShellCellWeight N m := by
  unfold evenFirstShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  have hne : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  rw [if_pos ⟨rfl, rfl, rfl, rfl⟩,
    if_neg (fun h => hne h.2.1),
    if_neg (fun h => hne h.1),
    if_neg (fun h => hne h.1)]
  rfl

private theorem evenFirstShellSparse_at_01
    (N m : Nat) :
    evenFirstShellSparse N m m (m + 1) (m + 1) m =
      evenFirstShellCellWeight N m := by
  unfold evenFirstShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  have hne : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  rw [if_neg (fun h => hne (Eq.symm h.2.1)),
    if_pos ⟨rfl, rfl, rfl, rfl⟩,
    if_neg (fun h => hne h.1),
    if_neg (fun h => hne h.1)]
  simp only [Int.zero_add, Int.add_zero]

private theorem evenFirstShellSparse_at_10
    (N m : Nat) :
    evenFirstShellSparse N m (m + 1) m m (m + 1) =
      evenFirstShellCellWeight N m := by
  unfold evenFirstShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  have hne : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  rw [if_neg (fun h => hne (Eq.symm h.1)),
    if_neg (fun h => hne (Eq.symm h.1)),
    if_pos ⟨rfl, rfl, rfl, rfl⟩,
    if_neg (fun h => hne h.2.1)]
  simp only [Int.zero_add, Int.add_zero]

private theorem evenFirstShellSparse_at_11
    (N m : Nat) :
    evenFirstShellSparse N m (m + 1) (m + 1) m m =
      evenFirstShellCellWeight N m := by
  unfold evenFirstShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
  have hne : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  rw [if_neg (fun h => hne (Eq.symm h.1)),
    if_neg (fun h => hne (Eq.symm h.1)),
    if_neg (fun h => hne (Eq.symm h.2.1)),
    if_pos ⟨rfl, rfl, rfl, rfl⟩]
  simp only [Int.zero_add]

private theorem evenPositiveClearedCell_at_00
    (N m : Nat) :
    boxPositiveClearedCell N (2 * m) m m (m + 1) (m + 1) =
      evenFirstShellCellWeight N m := by
  have hl : fusionOK m (m + 1) (2 * m + 1) = true :=
    fusionOK_at_exact_sum m (m + 1) (2 * m + 1) (by omega)
  have hdim : boxQuadDimension m m (m + 1) (m + 1) =
      ((m + 1) * (m + 2)) ^ 2 := by
    unfold boxQuadDimension
    rw [Nat.pow_two]
  have hcell := boxPositiveClearedCell_eq_active
    (N := N) (s := 2 * m) (k := c4 m + c4 (m + 1))
    (weight := ((m + 1) * (m + 2)) ^ 2)
    (by simpa using hl) (by simpa using hl) (evenFirstShellExponent00 m) hdim
  exact hcell

private theorem evenFirstShellFilter_at_00
    (m K : Nat) (hK : c4 m + c4 (m + 1) < K) :
    boxQuadHalfExponent m m (m + 1) (m + 1) < K := by
  rw [evenFirstShellExponent00]
  exact hK

private theorem oddSecondShellSparse_le_at_center
    (N m K : Nat) (hK : 2 * c4 (m + 1) < K) :
    oddSecondShellSparse N m (m + 1) (m + 1) (m + 1) (m + 1) <=
      (if boxQuadHalfExponent (m + 1) (m + 1) (m + 1) (m + 1) < K then
        boxPositiveClearedCell N (2 * m + 1)
          (m + 1) (m + 1) (m + 1) (m + 1)
      else 0) := by
  have hl : fusionOK (m + 1) (m + 1) (2 * (m + 1)) = true :=
    fusionOK_at_exact_sum (m + 1) (m + 1) (2 * (m + 1)) (by omega)
  have he : boxQuadHalfExponent (m + 1) (m + 1) (m + 1) (m + 1) =
      2 * c4 (m + 1) := by
    unfold boxQuadHalfExponent boxQuadExponent
    rw [half_double_sum, Nat.two_mul]
  have hdim : boxQuadDimension (m + 1) (m + 1) (m + 1) (m + 1) =
      (m + 2) ^ 4 := by
    unfold boxQuadDimension
    have hs : m + 1 + 1 = m + 2 := by omega
    rw [hs, pow_four_eq_square_square]
  have hcell := boxPositiveClearedCell_eq_active
    (N := N) (s := 2 * m + 1) (k := 2 * c4 (m + 1))
    (weight := (m + 2) ^ 4)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    he hdim
  have hcell' : boxPositiveClearedCell N (2 * m + 1)
      (m + 1) (m + 1) (m + 1) (m + 1) =
        oddFirstShellCellWeight N m := hcell
  have hfilter :
      boxQuadHalfExponent (m + 1) (m + 1) (m + 1) (m + 1) < K := by
    rw [he]
    omega
  rw [if_pos hfilter, hcell', oddSecondShellSparse_at_center]
  exact Int.le_refl _

private theorem oddSecondShellSparse_le_at_far00
    (N m K : Nat) (hK : 2 * c4 (m + 1) + 2 < K) :
    oddSecondShellSparse N m m m (m + 2) (m + 2) <=
      (if boxQuadHalfExponent m m (m + 2) (m + 2) < K then
        boxPositiveClearedCell N (2 * m + 1) m m (m + 2) (m + 2)
      else 0) := by
  have hl : fusionOK m (m + 2) (2 * (m + 1)) = true :=
    fusionOK_at_exact_sum m (m + 2) (2 * (m + 1)) (by omega)
  have hcurve :=
    YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
  have he : boxQuadHalfExponent m m (m + 2) (m + 2) =
      2 * c4 (m + 1) + 2 := by
    unfold boxQuadHalfExponent boxQuadExponent
    rw [hcurve, half_double_sum]
  have hdim : boxQuadDimension m m (m + 2) (m + 2) =
      ((m + 1) * (m + 3)) ^ 2 := by
    unfold boxQuadDimension
    rw [Nat.pow_two]
  have hcell := boxPositiveClearedCell_eq_active
    (N := N) (s := 2 * m + 1) (k := 2 * c4 (m + 1) + 2)
    (weight := ((m + 1) * (m + 3)) ^ 2)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    he hdim
  have hcell' : boxPositiveClearedCell N (2 * m + 1)
      m m (m + 2) (m + 2) = oddSecondShellCellWeight N m := hcell
  have hfilter : boxQuadHalfExponent m m (m + 2) (m + 2) < K := by
    rw [he]
    exact hK
  rw [if_pos hfilter, hcell', oddSecondShellSparse_at_far00]
  exact Int.le_refl _

private theorem oddSecondShellSparse_le_at_far01
    (N m K : Nat) (hK : 2 * c4 (m + 1) + 2 < K) :
    oddSecondShellSparse N m m (m + 2) (m + 2) m <=
      (if boxQuadHalfExponent m (m + 2) (m + 2) m < K then
        boxPositiveClearedCell N (2 * m + 1) m (m + 2) (m + 2) m
      else 0) := by
  have hl : fusionOK m (m + 2) (2 * (m + 1)) = true :=
    fusionOK_at_exact_sum m (m + 2) (2 * (m + 1)) (by omega)
  have hr : fusionOK (m + 2) m (2 * (m + 1)) = true :=
    fusionOK_at_exact_sum (m + 2) m (2 * (m + 1)) (by omega)
  have hcurve :=
    YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
  have he : boxQuadHalfExponent m (m + 2) (m + 2) m =
      2 * c4 (m + 1) + 2 := by
    unfold boxQuadHalfExponent boxQuadExponent
    rw [Nat.add_comm (c4 (m + 2)) (c4 m), hcurve, half_double_sum]
  have hdim : boxQuadDimension m (m + 2) (m + 2) m =
      ((m + 1) * (m + 3)) ^ 2 := by
    unfold boxQuadDimension
    rw [Nat.pow_two]
    have hs : m + 2 + 1 = m + 3 := by omega
    rw [hs, Nat.mul_comm (m + 3) (m + 1)]
  have hcell := boxPositiveClearedCell_eq_active
    (N := N) (s := 2 * m + 1) (k := 2 * c4 (m + 1) + 2)
    (weight := ((m + 1) * (m + 3)) ^ 2)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hr)
    he hdim
  have hcell' : boxPositiveClearedCell N (2 * m + 1)
      m (m + 2) (m + 2) m = oddSecondShellCellWeight N m := hcell
  have hfilter : boxQuadHalfExponent m (m + 2) (m + 2) m < K := by
    rw [he]
    exact hK
  rw [if_pos hfilter, hcell', oddSecondShellSparse_at_far01]
  exact Int.le_refl _

private theorem oddSecondShellSparse_le_at_far10
    (N m K : Nat) (hK : 2 * c4 (m + 1) + 2 < K) :
    oddSecondShellSparse N m (m + 2) m m (m + 2) <=
      (if boxQuadHalfExponent (m + 2) m m (m + 2) < K then
        boxPositiveClearedCell N (2 * m + 1) (m + 2) m m (m + 2)
      else 0) := by
  have hl : fusionOK (m + 2) m (2 * (m + 1)) = true :=
    fusionOK_at_exact_sum (m + 2) m (2 * (m + 1)) (by omega)
  have hr : fusionOK m (m + 2) (2 * (m + 1)) = true :=
    fusionOK_at_exact_sum m (m + 2) (2 * (m + 1)) (by omega)
  have hcurve :=
    YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
  have he : boxQuadHalfExponent (m + 2) m m (m + 2) =
      2 * c4 (m + 1) + 2 := by
    unfold boxQuadHalfExponent boxQuadExponent
    rw [Nat.add_comm (c4 (m + 2)) (c4 m), hcurve, half_double_sum]
  have hdim : boxQuadDimension (m + 2) m m (m + 2) =
      ((m + 1) * (m + 3)) ^ 2 := by
    unfold boxQuadDimension
    rw [Nat.pow_two]
    have hs : m + 2 + 1 = m + 3 := by omega
    rw [hs, Nat.mul_comm (m + 3) (m + 1)]
  have hcell := boxPositiveClearedCell_eq_active
    (N := N) (s := 2 * m + 1) (k := 2 * c4 (m + 1) + 2)
    (weight := ((m + 1) * (m + 3)) ^ 2)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hr)
    he hdim
  have hcell' : boxPositiveClearedCell N (2 * m + 1)
      (m + 2) m m (m + 2) = oddSecondShellCellWeight N m := hcell
  have hfilter : boxQuadHalfExponent (m + 2) m m (m + 2) < K := by
    rw [he]
    exact hK
  rw [if_pos hfilter, hcell', oddSecondShellSparse_at_far10]
  exact Int.le_refl _

private theorem oddSecondShellSparse_le_at_far11
    (N m K : Nat) (hK : 2 * c4 (m + 1) + 2 < K) :
    oddSecondShellSparse N m (m + 2) (m + 2) m m <=
      (if boxQuadHalfExponent (m + 2) (m + 2) m m < K then
        boxPositiveClearedCell N (2 * m + 1) (m + 2) (m + 2) m m
      else 0) := by
  have hl : fusionOK (m + 2) m (2 * (m + 1)) = true :=
    fusionOK_at_exact_sum (m + 2) m (2 * (m + 1)) (by omega)
  have hcurve :=
    YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
  have he : boxQuadHalfExponent (m + 2) (m + 2) m m =
      2 * c4 (m + 1) + 2 := by
    unfold boxQuadHalfExponent boxQuadExponent
    rw [Nat.add_comm (c4 (m + 2)) (c4 m), hcurve, half_double_sum]
  have hdim : boxQuadDimension (m + 2) (m + 2) m m =
      ((m + 1) * (m + 3)) ^ 2 := by
    unfold boxQuadDimension
    rw [Nat.pow_two]
    have hs : m + 2 + 1 = m + 3 := by omega
    rw [hs, Nat.mul_comm (m + 3) (m + 1)]
  have hcell := boxPositiveClearedCell_eq_active
    (N := N) (s := 2 * m + 1) (k := 2 * c4 (m + 1) + 2)
    (weight := ((m + 1) * (m + 3)) ^ 2)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    (by simpa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hl)
    he hdim
  have hcell' : boxPositiveClearedCell N (2 * m + 1)
      (m + 2) (m + 2) m m = oddSecondShellCellWeight N m := hcell
  have hfilter : boxQuadHalfExponent (m + 2) (m + 2) m m < K := by
    rw [he]
    exact hK
  rw [if_pos hfilter, hcell', oddSecondShellSparse_at_far11]
  exact Int.le_refl _

private theorem oddSecondShellSparse_le
    (N m K a a' b b' : Nat)
    (hK : 2 * c4 (m + 1) + 2 < K) :
    oddSecondShellSparse N m a a' b b' <=
      (if boxQuadHalfExponent a a' b b' < K then
        boxPositiveClearedCell N (2 * m + 1) a a' b b'
      else 0) := by
  by_cases hc : a = m + 1 ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 1
  · rcases hc with ⟨ha, ha', hb, hb'⟩
    subst a
    subst a'
    subst b
    subst b'
    exact oddSecondShellSparse_le_at_center N m K (by omega)
  · by_cases h0 : a = m ∧ a' = m ∧ b = m + 2 ∧ b' = m + 2
    · rcases h0 with ⟨ha, ha', hb, hb'⟩
      subst a
      subst a'
      subst b
      subst b'
      exact oddSecondShellSparse_le_at_far00 N m K hK
    · by_cases h1 : a = m ∧ a' = m + 2 ∧ b = m + 2 ∧ b' = m
      · rcases h1 with ⟨ha, ha', hb, hb'⟩
        subst a
        subst a'
        subst b
        subst b'
        exact oddSecondShellSparse_le_at_far01 N m K hK
      · by_cases h2 : a = m + 2 ∧ a' = m ∧ b = m ∧ b' = m + 2
        · rcases h2 with ⟨ha, ha', hb, hb'⟩
          subst a
          subst a'
          subst b
          subst b'
          exact oddSecondShellSparse_le_at_far10 N m K hK
        · by_cases h3 : a = m + 2 ∧ a' = m + 2 ∧ b = m ∧ b' = m
          · rcases h3 with ⟨ha, ha', hb, hb'⟩
            subst a
            subst a'
            subst b
            subst b'
            exact oddSecondShellSparse_le_at_far11 N m K hK
          · unfold oddSecondShellSparse
            rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if,
              cellAt_eq_if]
            rw [if_neg hc, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
            simp only [Int.zero_add]
            by_cases hfilter : boxQuadHalfExponent a a' b b' < K
            · rw [if_pos hfilter]
              exact boxPositiveClearedCell_nonnegative N (2 * m + 1)
                a a' b b'
            · rw [if_neg hfilter]
              exact Int.le_refl 0

private theorem oddFirstNegativeShell_active_classification
    {m a a' b b' : Nat}
    (hl : fusionOK a b (2 * m + 1) = true)
    (hr : fusionOK a' b' (2 * (m + 1) + 1) = true)
    (hlt : boxQuadHalfExponent a a' b b' < 2 * c4 (m + 1) + 2) :
    (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) ∨
    (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) ∨
    (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) ∨
    (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1) := by
  have hminl := fusionCasimir_odd_min (m := m) hl
  have hminr := fusionCasimir_odd_min (m := m + 1) hr
  have hcidx : m + 1 + 1 = m + 2 := by omega
  rw [hcidx] at hminr
  have hcurve :=
    YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
  have hpar := boxQuadExponent_even_of_active (by omega) hl hr
  have hdecomp := Nat.mod_add_div (boxQuadExponent a a' b b') 2
  have hdouble :
      boxQuadExponent a a' b b' =
        2 * boxQuadHalfExponent a a' b b' := by
    unfold boxQuadHalfExponent
    omega
  have htotal :
      c4 a + c4 b + (c4 a' + c4 b') =
        (c4 m + c4 (m + 1)) +
          (c4 (m + 1) + c4 (m + 2)) := by
    unfold boxQuadExponent at hdouble
    omega
  have hleft : c4 a + c4 b = c4 m + c4 (m + 1) := by omega
  have hright : c4 a' + c4 b' =
      c4 (m + 1) + c4 (m + 2) := by omega
  rcases fusionCasimir_odd_eq_min hl hleft with hl0 | hl1 <;>
    rcases fusionCasimir_odd_eq_min hr hright with hr0 | hr1
  · exact Or.inl ⟨hl0.1, hr0.1, hl0.2, hr0.2⟩
  · exact Or.inr (Or.inl ⟨hl0.1, hr1.1, hl0.2, hr1.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hl1.1, hr0.1, hl1.2, hr0.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hl1.1, hr1.1, hl1.2, hr1.2⟩))

private theorem oddNegativeClearedCell_eq_firstShell_of_classified
    {N m a a' b b' : Nat}
    (hl : fusionOK a b (2 * m + 1) = true)
    (hr : fusionOK a' b' (2 * (m + 1) + 1) = true)
    (hc :
      (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) ∨
      (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) ∨
      (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) ∨
      (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1)) :
    boxNegativeClearedCell N (2 * m + 1) a a' b b' =
      oddFirstNegativeShellCellWeight N m := by
  have hgeneric
      (hleft : c4 a + c4 b = c4 m + c4 (m + 1))
      (hright : c4 a' + c4 b' = c4 (m + 1) + c4 (m + 2))
      (hdim : boxQuadDimension a a' b b' =
        ((m + 1) * (m + 2)) * ((m + 2) * (m + 3))) :
      boxNegativeClearedCell N (2 * m + 1) a a' b b' =
        oddFirstNegativeShellCellWeight N m := by
    have hcurve :=
      YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
    have htotal : boxQuadExponent a a' b b' =
        (2 * c4 (m + 1) + 1) + (2 * c4 (m + 1) + 1) := by
      unfold boxQuadExponent
      omega
    have he : boxQuadHalfExponent a a' b b' =
        2 * c4 (m + 1) + 1 := by
      unfold boxQuadHalfExponent
      rw [htotal, half_double_sum]
    exact boxNegativeClearedCell_eq_active
      (N := N) (s := 2 * m + 1)
      (k := 2 * c4 (m + 1) + 1)
      (weight := ((m + 1) * (m + 2)) * ((m + 2) * (m + 3)))
      hl (by simpa [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega]
        using hr) he hdim
  rcases hc with h00 | h01 | h10 | h11
  · rcases h00 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    apply hgeneric
    · rfl
    · rfl
    · unfold boxQuadDimension
      rw [show m + 1 + 1 = m + 2 by omega,
        show m + 2 + 1 = m + 3 by omega]

  · rcases h01 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    apply hgeneric
    · rfl
    · omega
    · unfold boxQuadDimension
      rw [show m + 1 + 1 = m + 2 by omega,
        show m + 2 + 1 = m + 3 by omega,
        Nat.mul_comm (m + 3) (m + 2)]
  · rcases h10 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    apply hgeneric
    · omega
    · rfl
    · unfold boxQuadDimension
      rw [show m + 1 + 1 = m + 2 by omega,
        show m + 2 + 1 = m + 3 by omega,
        Nat.mul_comm (m + 2) (m + 1)]
  · rcases h11 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    apply hgeneric
    · omega
    · omega
    · unfold boxQuadDimension
      rw [show m + 1 + 1 = m + 2 by omega,
        show m + 2 + 1 = m + 3 by omega,
        Nat.mul_comm (m + 2) (m + 1),
        Nat.mul_comm (m + 3) (m + 2)]

private theorem oddFirstNegativeShellSparse_eq_weight_of_classified
    {N m a a' b b' : Nat}
    (hc :
      (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) ∨
      (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) ∨
      (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) ∨
      (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1)) :
    oddFirstNegativeShellSparse N m a a' b b' =
      oddFirstNegativeShellCellWeight N m := by
  rcases hc with h00 | h01 | h10 | h11
  · rcases h00 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    exact oddFirstNegativeShellSparse_at_00 N m
  · rcases h01 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    exact oddFirstNegativeShellSparse_at_01 N m
  · rcases h10 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    exact oddFirstNegativeShellSparse_at_10 N m
  · rcases h11 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    exact oddFirstNegativeShellSparse_at_11 N m

private theorem oddFirstNegativeShell_active_of_classified
    {m a a' b b' : Nat}
    (hc :
      (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) ∨
      (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) ∨
      (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) ∨
      (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1)) :
    fusionOK a b (2 * m + 1) = true ∧
      fusionOK a' b' (2 * (m + 1) + 1) = true := by
  rcases hc with h00 | h01 | h10 | h11
  · rcases h00 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    constructor <;> apply fusionOK_at_exact_sum <;> omega
  · rcases h01 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    constructor <;> apply fusionOK_at_exact_sum <;> omega
  · rcases h10 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    constructor <;> apply fusionOK_at_exact_sum <;> omega
  · rcases h11 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    constructor <;> apply fusionOK_at_exact_sum <;> omega

private theorem oddFirstNegativeShellHalfExponent_of_classified
    {m a a' b b' : Nat}
    (hc :
      (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) ∨
      (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) ∨
      (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) ∨
      (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1)) :
    boxQuadHalfExponent a a' b b' = 2 * c4 (m + 1) + 1 := by
  rcases hc with h00 | h01 | h10 | h11
  · rcases h00 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    have hcurve :=
      YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
    have htotal : boxQuadExponent m (m + 1) (m + 1) (m + 2) =
        (2 * c4 (m + 1) + 1) + (2 * c4 (m + 1) + 1) := by
      unfold boxQuadExponent
      omega
    unfold boxQuadHalfExponent
    rw [htotal, half_double_sum]
  · rcases h01 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    have hcurve :=
      YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
    have htotal : boxQuadExponent m (m + 2) (m + 1) (m + 1) =
        (2 * c4 (m + 1) + 1) + (2 * c4 (m + 1) + 1) := by
      unfold boxQuadExponent
      omega
    unfold boxQuadHalfExponent
    rw [htotal, half_double_sum]
  · rcases h10 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    have hcurve :=
      YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
    have htotal : boxQuadExponent (m + 1) (m + 1) m (m + 2) =
        (2 * c4 (m + 1) + 1) + (2 * c4 (m + 1) + 1) := by
      unfold boxQuadExponent
      omega
    unfold boxQuadHalfExponent
    rw [htotal, half_double_sum]
  · rcases h11 with ⟨ha, ha', hb, hb'⟩
    subst a; subst a'; subst b; subst b'
    have hcurve :=
      YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
    have htotal : boxQuadExponent (m + 1) (m + 2) m (m + 1) =
        (2 * c4 (m + 1) + 1) + (2 * c4 (m + 1) + 1) := by
      unfold boxQuadExponent
      omega
    unfold boxQuadHalfExponent
    rw [htotal, half_double_sum]

private theorem oddFirstNegativeShellSparse_eq_zero_of_not_classified
    {N m a a' b b' : Nat}
    (hc : ¬ (
      (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) ∨
      (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) ∨
      (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) ∨
      (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1))) :
    oddFirstNegativeShellSparse N m a a' b b' = 0 := by
  have h00 : ¬ (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) :=
    fun h => hc (Or.inl h)
  have h01 : ¬ (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) :=
    fun h => hc (Or.inr (Or.inl h))
  have h10 : ¬ (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) :=
    fun h => hc (Or.inr (Or.inr (Or.inl h)))
  have h11 : ¬ (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1) :=
    fun h => hc (Or.inr (Or.inr (Or.inr h)))
  unfold oddFirstNegativeShellSparse
  rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if,
    if_neg h00, if_neg h01, if_neg h10, if_neg h11]
  simp only [Int.zero_add]

private theorem oddNegativeClearedCell_eq_zero_of_left_inactive
    (N m a a' b b' : Nat)
    (hl : fusionOK a b (2 * m + 1) = false) :
    boxNegativeClearedCell N (2 * m + 1) a a' b b' = 0 := by
  unfold boxNegativeClearedCell boxCellClearedMultiplicity
    boxNegativeMultiplicity boxProductMultiplicity
  simp [hl]

private theorem oddNegativeClearedCell_eq_zero_of_right_inactive
    (N m a a' b b' : Nat)
    (hr : fusionOK a' b' (2 * (m + 1) + 1) = false) :
    boxNegativeClearedCell N (2 * m + 1) a a' b b' = 0 := by
  unfold boxNegativeClearedCell boxCellClearedMultiplicity
    boxNegativeMultiplicity boxProductMultiplicity
  simp [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega, hr]

private theorem oddFirstNegativeShellSparse_eq_filteredCell
    (N m a a' b b' : Nat) :
    oddFirstNegativeShellSparse N m a a' b b' =
      (if boxQuadHalfExponent a a' b b' < 2 * c4 (m + 1) + 2 then
        boxNegativeClearedCell N (2 * m + 1) a a' b b'
      else 0) := by
  by_cases hc :
      (a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 2) ∨
      (a = m ∧ a' = m + 2 ∧ b = m + 1 ∧ b' = m + 1) ∨
      (a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m + 2) ∨
      (a = m + 1 ∧ a' = m + 2 ∧ b = m ∧ b' = m + 1)
  · have hactive := oddFirstNegativeShell_active_of_classified hc
    have he := oddFirstNegativeShellHalfExponent_of_classified hc
    have hsparse :=
      oddFirstNegativeShellSparse_eq_weight_of_classified (N := N) hc
    have hcell := oddNegativeClearedCell_eq_firstShell_of_classified
      (N := N) hactive.1 hactive.2 hc
    have hfilter :
        boxQuadHalfExponent a a' b b' < 2 * c4 (m + 1) + 2 := by
      rw [he]
      omega
    rw [if_pos hfilter, hsparse, hcell]
  · rw [oddFirstNegativeShellSparse_eq_zero_of_not_classified (N := N) hc]
    by_cases hfilter :
        boxQuadHalfExponent a a' b b' < 2 * c4 (m + 1) + 2
    · rw [if_pos hfilter]
      by_cases hl : fusionOK a b (2 * m + 1) = true
      · by_cases hr : fusionOK a' b' (2 * (m + 1) + 1) = true
        · exact False.elim
            (hc (oddFirstNegativeShell_active_classification hl hr hfilter))
        · have hr0 : fusionOK a' b' (2 * (m + 1) + 1) = false :=
            Bool.eq_false_iff.mpr hr
          rw [oddNegativeClearedCell_eq_zero_of_right_inactive
            N m a a' b b' hr0]
      · have hl0 : fusionOK a b (2 * m + 1) = false :=
          Bool.eq_false_iff.mpr hl
        rw [oddNegativeClearedCell_eq_zero_of_left_inactive
          N m a a' b b' hl0]
    · rw [if_neg hfilter]

private theorem oddNegativeClearedCell_zero_below_firstBoundary
    (N m a a' b b' : Nat)
    (hlt : boxQuadHalfExponent a a' b b' < 2 * c4 (m + 1) + 1) :
    boxNegativeClearedCell N (2 * m + 1) a a' b b' = 0 := by
  unfold boxNegativeClearedCell
  unfold boxCellClearedMultiplicity boxNegativeMultiplicity boxProductMultiplicity
  by_cases hl : fusionOK a b (2 * m + 1) = true
  · by_cases hr : fusionOK a' b' (2 * (m + 1) + 1) = true
    · exfalso
      have hminl := fusionCasimir_odd_min (m := m) hl
      have hminr := fusionCasimir_odd_min (m := m + 1) hr
      have hcidx : m + 1 + 1 = m + 2 := by omega
      rw [hcidx] at hminr
      have hcurve :=
        YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
      have hpar := boxQuadExponent_even_of_active (by omega) hl hr
      unfold boxQuadHalfExponent boxQuadExponent at hlt
      omega
    · simp [hl, hr, show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega]
  · simp [hl]

/-- At `K=e+1`, where `e=2*c4(m+1)`, the odd outer-product ledger has not
entered the strict prefix yet. -/
theorem oddNegativeClearedPrefix_firstBoundary_eq_zero
    (N m : Nat) :
    boxNegativeClearedPrefix N (2 * m + 1) (2 * c4 (m + 1) + 1) = 0 := by
  unfold boxNegativeClearedPrefix
  rw [boxCellIntSum_congr_local
    (g := fun _ _ _ _ => 0) (fun a a' b b' _ _ _ _ => by
      by_cases hlt : boxQuadHalfExponent a a' b b' < 2 * c4 (m + 1) + 1
      · rw [if_pos hlt,
          oddNegativeClearedCell_zero_below_firstBoundary N m a a' b b' hlt]
      · rw [if_neg hlt])]
  exact boxCellIntSum_zero_local N

/-- The first strict post-boundary odd prefix is nonnegative for every
cutoff: it contains positive cells, while the negative ledger is still
empty. -/
theorem odd_boxClearedPowerPrefix_nonnegative_firstBoundary
    (N m : Nat) :
    0 <= boxClearedPowerPrefix N (2 * m + 1) (2 * c4 (m + 1) + 1) := by
  rw [boxClearedPowerPrefix_eq_positive_sub_negative,
    oddNegativeClearedPrefix_firstBoundary_eq_zero]
  rw [Int.sub_zero]
  exact boxPositiveClearedPrefix_nonnegative N (2 * m + 1)
    (2 * c4 (m + 1) + 1)

private theorem oddNegativeClearedPrefix_secondBoundary_eq_fourFirstShell
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    boxNegativeClearedPrefix N (2 * m + 1) (2 * c4 (m + 1) + 2) =
      4 * oddFirstNegativeShellCellWeight N m := by
  unfold boxNegativeClearedPrefix
  rw [boxCellIntSum_congr_local
    (g := oddFirstNegativeShellSparse N m)
    (fun a a' b b' _ _ _ _ =>
      Eq.symm (oddFirstNegativeShellSparse_eq_filteredCell
        N m a a' b b'))]
  have hbound : m + 2 <= N := by omega
  unfold oddFirstNegativeShellSparse
  rw [boxCellIntSum_add_local, boxCellIntSum_add_local,
    boxCellIntSum_add_local,
    boxCellIntSum_cellAt N m (m + 1) (m + 1) (m + 2),
    boxCellIntSum_cellAt N m (m + 2) (m + 1) (m + 1),
    boxCellIntSum_cellAt N (m + 1) (m + 1) m (m + 2),
    boxCellIntSum_cellAt N (m + 1) (m + 2) m (m + 1)]
  · omega
  all_goals omega

private theorem oddPositiveClearedPrefix_ge_firstShell
    (N m K : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N)
    (hK : 2 * c4 (m + 1) < K) :
    oddFirstShellCellWeight N m <=
      boxPositiveClearedPrefix N (2 * m + 1) K := by
  have hsum := boxCellIntSum_le_local
    (N := N)
    (f := cellAt (m + 1) (m + 1) (m + 1) (m + 1)
      (oddFirstShellCellWeight N m))
    (g := fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' < K then
        boxPositiveClearedCell N (2 * m + 1) a a' b b'
      else 0)
    (fun a a' b b' => by
      by_cases hc :
          a = m + 1 ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m + 1
      · rcases hc with ⟨rfl, rfl, rfl, rfl⟩
        rw [cellAt_eq_if, if_pos ⟨rfl, rfl, rfl, rfl⟩]
        have hcenter := oddSecondShellSparse_le_at_center N m K hK
        rw [oddSecondShellSparse_at_center] at hcenter
        exact hcenter
      · rw [cellAt_eq_if, if_neg hc]
        change (0 : Int) <=
          if boxQuadHalfExponent a a' b b' < K then
            boxPositiveClearedCell N (2 * m + 1) a a' b b'
          else 0
        by_cases hfilter : boxQuadHalfExponent a a' b b' < K
        · rw [if_pos hfilter]
          exact boxPositiveClearedCell_nonnegative N (2 * m + 1)
            a a' b b'
        · rw [if_neg hfilter]
          exact Int.le_refl 0)
  have hbound : m + 1 <= N := by omega
  have heval := boxCellIntSum_cellAt N
    (m + 1) (m + 1) (m + 1) (m + 1)
    (oddFirstShellCellWeight N m) hbound hbound hbound hbound
  unfold boxPositiveClearedPrefix
  rw [heval] at hsum
  exact hsum

private theorem four_oddFirstNegativeShellCellWeight_le_firstShell
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    4 * oddFirstNegativeShellCellWeight N m <=
      oddFirstShellCellWeight N m := by
  have hbound : m + 2 <= N := by omega
  have hcm : c4 m <= c4 N := by
    unfold c4
    exact Nat.mul_le_mul (by omega) (by omega)
  have hcm2 : c4 (m + 2) <= c4 N := by
    unfold c4
    exact Nat.mul_le_mul hbound (by omega)
  have hcurve :=
    YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
  have hdegree :
      2 * c4 (m + 1) + 2 <= boxBernsteinDegree N := by
    unfold boxBernsteinDegree
    omega
  have hexponent :
      boxBernsteinDegree N - 2 * c4 (m + 1) =
        (boxBernsteinDegree N - (2 * c4 (m + 1) + 1)) + 1 := by
    omega
  have hpow :
      4 ^ (boxBernsteinDegree N - 2 * c4 (m + 1)) =
        4 * 4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1)) := by
    rw [hexponent, Nat.pow_succ, Nat.mul_comm]
  have hdimensionIdentity :
      (m + 1) * (m + 3) + 1 = (m + 2) * (m + 2) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega
  have hdimension :
      ((m + 1) * (m + 2)) * ((m + 2) * (m + 3)) <=
        (m + 2) ^ 4 := by
    have hsmall : (m + 1) * (m + 3) <= (m + 2) * (m + 2) := by
      omega
    have hscaled := Nat.mul_le_mul_left ((m + 2) * (m + 2)) hsmall
    rw [pow_four_eq_square_square]
    calc
      ((m + 1) * (m + 2)) * ((m + 2) * (m + 3)) =
          ((m + 2) * (m + 2)) * ((m + 1) * (m + 3)) := by ac_rfl
      _ <= ((m + 2) * (m + 2)) * ((m + 2) * (m + 2)) := hscaled
  have hnat :
      4 *
          ((((m + 1) * (m + 2)) * ((m + 2) * (m + 3))) *
            4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1))) <=
        (m + 2) ^ 4 *
          4 ^ (boxBernsteinDegree N - 2 * c4 (m + 1)) := by
    rw [hpow]
    have hscaled := Nat.mul_le_mul_right
      (4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1))) hdimension
    calc
      4 *
          ((((m + 1) * (m + 2)) * ((m + 2) * (m + 3))) *
            4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1))) <=
          4 * ((m + 2) ^ 4 *
            4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1))) :=
        Nat.mul_le_mul_left 4 hscaled
      _ = (m + 2) ^ 4 *
          (4 * 4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1))) := by
        ac_rfl
  unfold oddFirstNegativeShellCellWeight oddFirstShellCellWeight
  have hint :
      ((4 *
          ((((m + 1) * (m + 2)) * ((m + 2) * (m + 3))) *
            4 ^ (boxBernsteinDegree N - (2 * c4 (m + 1) + 1))) : Nat) : Int) <=
        (((m + 2) ^ 4 *
          4 ^ (boxBernsteinDegree N - 2 * c4 (m + 1)) : Nat) : Int) := by
    exact_mod_cast hnat
  simpa only [Int.ofNat_eq_natCast, Int.natCast_mul] using hint

/-- At `K=e+2`, the four first odd outer-product cells are paid by the
central positive cell. -/
theorem odd_boxClearedPowerPrefix_nonnegative_secondBoundary
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    0 <= boxClearedPowerPrefix N (2 * m + 1)
      (2 * c4 (m + 1) + 2) := by
  rw [boxClearedPowerPrefix_eq_positive_sub_negative,
    oddNegativeClearedPrefix_secondBoundary_eq_fourFirstShell N m hguard]
  apply Int.sub_nonneg.mpr
  exact Int.le_trans
    (four_oddFirstNegativeShellCellWeight_le_firstShell N m hguard)
    (oddPositiveClearedPrefix_ge_firstShell N m
      (2 * c4 (m + 1) + 2) hguard (by omega))

private theorem evenFirstShellSparse_le_at_00
    (N m K : Nat) (hK : c4 m + c4 (m + 1) < K) :
    evenFirstShellSparse N m m m (m + 1) (m + 1) <=
      (if boxQuadHalfExponent m m (m + 1) (m + 1) < K then
        boxPositiveClearedCell N (2 * m) m m (m + 1) (m + 1)
      else 0) := by
  rw [if_pos (evenFirstShellFilter_at_00 m K hK),
    evenPositiveClearedCell_at_00, evenFirstShellSparse_at_00]
  exact Int.le_refl _

private theorem evenFirstShellSparse_le
    (N m K a a' b b' : Nat)
    (hK : c4 m + c4 (m + 1) < K) :
    evenFirstShellSparse N m a a' b b' <=
      (if boxQuadHalfExponent a a' b b' < K then
        boxPositiveClearedCell N (2 * m) a a' b b'
      else 0) := by
  by_cases h0 : a = m ∧ a' = m ∧ b = m + 1 ∧ b' = m + 1
  · rcases h0 with ⟨ha, ha', hb, hb'⟩
    subst a
    subst a'
    subst b
    subst b'
    exact evenFirstShellSparse_le_at_00 N m K hK
  · by_cases h1 : a = m ∧ a' = m + 1 ∧ b = m + 1 ∧ b' = m
    · rcases h1 with ⟨ha, ha', hb, hb'⟩
      subst a
      subst a'
      subst b
      subst b'
      have hl : fusionOK m (m + 1) (2 * m + 1) = true :=
        fusionOK_at_exact_sum m (m + 1) (2 * m + 1) (by omega)
      have hr : fusionOK (m + 1) m (2 * m + 1) = true :=
        fusionOK_at_exact_sum (m + 1) m (2 * m + 1) (by omega)
      have he : boxQuadHalfExponent m (m + 1) (m + 1) m =
          c4 m + c4 (m + 1) := by
        unfold boxQuadHalfExponent boxQuadExponent
        rw [Nat.add_comm (c4 (m + 1)) (c4 m)]
        exact half_double_sum (c4 m + c4 (m + 1))
      have hdim : boxQuadDimension m (m + 1) (m + 1) m =
          ((m + 1) * (m + 2)) ^ 2 := by
        unfold boxQuadDimension
        rw [Nat.pow_two]
        have hs : m + 1 + 1 = m + 2 := by omega
        rw [hs]
        rw [Nat.mul_comm (m + 2) (m + 1)]
      have hcell := boxPositiveClearedCell_eq_active
        (N := N) (s := 2 * m) (k := c4 m + c4 (m + 1))
        (weight := ((m + 1) * (m + 2)) ^ 2)
        (by simpa using hl) (by simpa using hr) he hdim
      have hcell' :
          boxPositiveClearedCell N (2 * m) m (m + 1) (m + 1) m =
            evenFirstShellCellWeight N m := hcell
      have hfilter : boxQuadHalfExponent m (m + 1) (m + 1) m < K := by
        rw [he]
        exact hK
      rw [if_pos hfilter, hcell', evenFirstShellSparse_at_01]
      exact Int.le_refl _
    · by_cases h2 : a = m + 1 ∧ a' = m ∧ b = m ∧ b' = m + 1
      · rcases h2 with ⟨ha, ha', hb, hb'⟩
        subst a
        subst a'
        subst b
        subst b'
        have hl : fusionOK (m + 1) m (2 * m + 1) = true :=
          fusionOK_at_exact_sum (m + 1) m (2 * m + 1) (by omega)
        have hr : fusionOK m (m + 1) (2 * m + 1) = true :=
          fusionOK_at_exact_sum m (m + 1) (2 * m + 1) (by omega)
        have he : boxQuadHalfExponent (m + 1) m m (m + 1) =
            c4 m + c4 (m + 1) := by
          unfold boxQuadHalfExponent boxQuadExponent
          rw [Nat.add_comm (c4 (m + 1)) (c4 m)]
          exact half_double_sum (c4 m + c4 (m + 1))
        have hdim : boxQuadDimension (m + 1) m m (m + 1) =
            ((m + 1) * (m + 2)) ^ 2 := by
          unfold boxQuadDimension
          rw [Nat.pow_two]
          have hs : m + 1 + 1 = m + 2 := by omega
          rw [hs]
          rw [Nat.mul_comm (m + 2) (m + 1)]
        have hcell := boxPositiveClearedCell_eq_active
          (N := N) (s := 2 * m) (k := c4 m + c4 (m + 1))
          (weight := ((m + 1) * (m + 2)) ^ 2)
          (by simpa using hl) (by simpa using hr) he hdim
        have hcell' :
            boxPositiveClearedCell N (2 * m) (m + 1) m m (m + 1) =
              evenFirstShellCellWeight N m := hcell
        have hfilter : boxQuadHalfExponent (m + 1) m m (m + 1) < K := by
          rw [he]
          exact hK
        rw [if_pos hfilter, hcell', evenFirstShellSparse_at_10]
        exact Int.le_refl _
      · by_cases h3 : a = m + 1 ∧ a' = m + 1 ∧ b = m ∧ b' = m
        · rcases h3 with ⟨ha, ha', hb, hb'⟩
          subst a
          subst a'
          subst b
          subst b'
          have hl : fusionOK (m + 1) m (2 * m + 1) = true :=
            fusionOK_at_exact_sum (m + 1) m (2 * m + 1) (by omega)
          have he : boxQuadHalfExponent (m + 1) (m + 1) m m =
              c4 m + c4 (m + 1) := by
            unfold boxQuadHalfExponent boxQuadExponent
            rw [Nat.add_comm (c4 (m + 1)) (c4 m)]
            exact half_double_sum (c4 m + c4 (m + 1))
          have hdim : boxQuadDimension (m + 1) (m + 1) m m =
              ((m + 1) * (m + 2)) ^ 2 := by
            unfold boxQuadDimension
            rw [Nat.pow_two]
            have hs : m + 1 + 1 = m + 2 := by omega
            rw [hs]
            rw [Nat.mul_comm (m + 2) (m + 1)]
          have hcell := boxPositiveClearedCell_eq_active
            (N := N) (s := 2 * m) (k := c4 m + c4 (m + 1))
            (weight := ((m + 1) * (m + 2)) ^ 2)
            (by simpa using hl) (by simpa using hl) he hdim
          have hcell' :
              boxPositiveClearedCell N (2 * m) (m + 1) (m + 1) m m =
                evenFirstShellCellWeight N m := hcell
          have hfilter : boxQuadHalfExponent (m + 1) (m + 1) m m < K := by
            rw [he]
            exact hK
          rw [if_pos hfilter, hcell', evenFirstShellSparse_at_11]
          exact Int.le_refl _
        · unfold evenFirstShellSparse
          rw [cellAt_eq_if, cellAt_eq_if, cellAt_eq_if, cellAt_eq_if]
          rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]
          simp only [Int.add_zero]
          by_cases hfilter : boxQuadHalfExponent a a' b b' < K
          · rw [if_pos hfilter]
            exact boxPositiveClearedCell_nonnegative N (2 * m) a a' b b'
          · rw [if_neg hfilter]
            exact Int.le_refl 0

/-- For every cutoff, once the prefix passes the first even shell it already
contains all four balanced positive orientations. -/
theorem evenPositiveClearedPrefix_ge_firstShellReserve
    (N m K : Nat) (hguard : 2 * m + 2 <= 2 * N)
    (hK : c4 m + c4 (m + 1) < K) :
    evenFirstShellPositiveReserve N m <=
      boxPositiveClearedPrefix N (2 * m) K := by
  have hsum := boxCellIntSum_le_local
    (N := N) (f := evenFirstShellSparse N m)
    (g := fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' < K then
        boxPositiveClearedCell N (2 * m) a a' b b'
      else 0)
    (fun a a' b b' => evenFirstShellSparse_le N m K a a' b b' hK)
  have hbound : m + 1 <= N := by omega
  have heval : boxCellIntSum N (evenFirstShellSparse N m) =
      evenFirstShellPositiveReserve N m := by
    unfold evenFirstShellSparse
    rw [boxCellIntSum_add_local,
      boxCellIntSum_add_local, boxCellIntSum_add_local,
      boxCellIntSum_cellAt N m m (m + 1) (m + 1),
      boxCellIntSum_cellAt N m (m + 1) (m + 1) m,
      boxCellIntSum_cellAt N (m + 1) m m (m + 1),
      boxCellIntSum_cellAt N (m + 1) (m + 1) m m]
    · unfold evenFirstShellPositiveReserve
      omega
    all_goals omega
  unfold boxPositiveClearedPrefix
  rw [heval] at hsum
  exact hsum

/-- Once the odd prefix passes the second reserve shell, it contains the
central cell and all four displacement/displacement cells.  The statement is
the direct positive input to the generic total-negative domination compiler. -/
theorem oddPositiveClearedPrefix_ge_secondReserve
    (N m K : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N)
    (hK : 2 * c4 (m + 1) + 2 < K) :
    oddSecondShellPositiveReserve N m <=
      boxPositiveClearedPrefix N (2 * m + 1) K := by
  have hsum := boxCellIntSum_le_local
    (N := N) (f := oddSecondShellSparse N m)
    (g := fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' < K then
        boxPositiveClearedCell N (2 * m + 1) a a' b b'
      else 0)
    (fun a a' b b' => oddSecondShellSparse_le N m K a a' b b' hK)
  have hbound : m + 2 <= N := by omega
  have heval : boxCellIntSum N (oddSecondShellSparse N m) =
      oddSecondShellPositiveReserve N m := by
    unfold oddSecondShellSparse
    rw [boxCellIntSum_add_local,
      boxCellIntSum_add_local, boxCellIntSum_add_local,
      boxCellIntSum_add_local,
      boxCellIntSum_cellAt N (m + 1) (m + 1) (m + 1) (m + 1),
      boxCellIntSum_cellAt N m m (m + 2) (m + 2),
      boxCellIntSum_cellAt N m (m + 2) (m + 2) m,
      boxCellIntSum_cellAt N (m + 2) m m (m + 2),
      boxCellIntSum_cellAt N (m + 2) (m + 2) m m]
    · unfold oddSecondShellPositiveReserve
      omega
    all_goals omega
  unfold boxPositiveClearedPrefix
  rw [heval] at hsum
  exact hsum

#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.cellAt_eq_if
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.fusionOK_at_exact_sum
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.boxPositiveClearedCell_nonnegative
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.boxPositiveClearedCell_eq_active
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.half_double_sum
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.evenFirstShellExponent00
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.evenFirstShellSparse_at_00
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.evenPositiveClearedCell_at_00
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.evenFirstShellFilter_at_00
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.evenFirstShellSparse_le_at_00
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.evenFirstShellSparse_le
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.evenPositiveClearedPrefix_ge_firstShellReserve
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddSecondShellSparse_le_at_center
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddSecondShellSparse_le_at_far00
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddSecondShellSparse_le
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddPositiveClearedPrefix_ge_secondReserve
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddFirstNegativeShellSparse_eq_filteredCell
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddNegativeClearedPrefix_firstBoundary_eq_zero
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.odd_boxClearedPowerPrefix_nonnegative_firstBoundary
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddNegativeClearedPrefix_secondBoundary_eq_fourFirstShell
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.oddPositiveClearedPrefix_ge_firstShell
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.four_oddFirstNegativeShellCellWeight_le_firstShell
#print axioms YMGap.Continuum.FusionBoxBoundaryShellClassification.odd_boxClearedPowerPrefix_nonnegative_secondBoundary

end YMGap.Continuum.FusionBoxBoundaryShellClassification
