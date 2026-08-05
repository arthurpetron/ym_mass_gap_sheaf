/-
`FusionBoxPrefixReserve` -- the all-cutoff four-adic prefix producer for the
physical heat-weighted Clebsch box.

# Mathematical invariant

Write the box cross-difference as an even polynomial

    P_{N,s}(w) = sum_k a_{N,s,k} w^(2*k).

The Bernstein consumer does not need the signed monomial coefficients to be
nonnegative.  It needs the weaker first-order invariant

    T_0 = a_0,                 T_(k+1) = 4*T_k + a_(k+1),
    0 <= T_k.

Indeed `T_k = 4^k * sum_{i<=k} a_i / 4^i`; it is the physical power prefix at
`w=1/2` with denominators cleared.  `BernsteinPrefixAbel` proves that these
prefixes imply every full-degree `u=4*w^2` Bernstein coefficient is
nonnegative.

This file fixes the producer's actual finite coefficient functions and records
the two structural estimates used by the all-`N` proof.

* Strand energy separates exactly into a balanced antidiagonal energy, a
  squared displacement, and a nonnegative common-strand energy.
* The first one (even `s`) or two (odd `s`) physical shells leave a reserve
  that dominates the complete negative box product once the corresponding
  uniform theta mass ceilings are supplied.

The final direct box ceilings are deliberately stated as theorems about the
actual `boxSum`, not as a detached certificate interface.  Their finite
strand-reindex proofs are the remaining implementation seam in this file.
No continuum/Clay frontier bundle is inhabited here.

# Constructive contract

Mathlib-free; `Nat`/`Int`/`Q'` only.  No `Classical`, `native_decide`, `sorry`,
new axiom, or noncomputable declaration.  All executable coefficient data are
ordinary definitions, and all load-bearing declarations are axiom-gated.
-/

import YMGap.Continuum.BernsteinPrefixAbel
import YMGap.Continuum.CoreBAtomwiseGapBounds
import YMGap.Continuum.FusionBoxBernsteinReconstruction
import YMGap.Continuum.FusionWeightedInterlacingCertificate
import YMGap.Continuum.WHTailCeilingsClose

namespace YMGap.Continuum.FusionBoxPrefixReserve

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.BernsteinPrefixAbel
open YMGap.Continuum.FusionBoxBernsteinReconstruction

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, Q'.mkPos_num, Q'.mkPos_den, neg_num_cast_local,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. Exact integer coefficient compiler -/

/-- Signed, *uncleared* coefficient carried by one cell of Track A's exact
four-index ledger.  The exponent bucket below is therefore definitionally
pinned to the same positive and negative fusion multiplicities as the
canonical Bernstein reconstruction. -/
def boxCellRawCoefficient (s a a' b b' : Nat) : Int :=
  Int.ofNat (boxPositiveMultiplicity s a a' b b') -
    Int.ofNat (boxNegativeMultiplicity s a a' b b')

/-- Four nested finite integer sums, in exactly the order used by
`boxClearedPowerPrefix` and `boxBernsteinCoefficient`. -/
def boxCellIntSum (N : Nat)
    (f : Nat -> Nat -> Nat -> Nat -> Int) : Int :=
  intFsum (fun a => intFsum (fun a' =>
    intFsum (fun b => intFsum (fun b' => f a a' b b') (N + 1))
      (N + 1)) (N + 1)) (N + 1)

/-- The actual signed numerator in physical half-exponent bucket `k`.  This
is not a second convolution compiler: it is a bucketing of Track A's exact
four-index cell ledger. -/
def rawPowerCoeff (N s k : Nat) : Int :=
  boxCellIntSum N (fun a a' b b' =>
    if boxQuadHalfExponent a a' b b' = k then
      boxCellRawCoefficient s a a' b b'
    else 0)

/-- Track A's cleared coefficient is the raw cell coefficient times the
canonical physical power of four. -/
theorem boxCellClearedCoefficient_eq_raw_mul
    {N s a a' b b' : Nat}
    (he : boxQuadHalfExponent a a' b b' <= boxBernsteinDegree N) :
    boxCellClearedCoefficient N s a a' b b' =
      boxCellRawCoefficient s a a' b b' *
        Int.ofNat
          (4 ^ (boxBernsteinDegree N - boxQuadHalfExponent a a' b b')) := by
  unfold boxCellClearedCoefficient boxCellClearedMultiplicity
    boxCellRawCoefficient
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.sub_mul]

/-! ### 1.1 Finite-sum algebra for the canonical four-index ledger -/

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

private theorem intFsum_mul_right_local (f : Nat -> Int) (z : Int) : forall n,
    intFsum (fun i => f i * z) n = intFsum f n * z
  | 0 => by simp [intFsum]
  | n + 1 => by
      rw [intFsum, intFsum, intFsum_mul_right_local f z n, Int.add_mul]

@[simp] private theorem intFsum_zero_local : forall n,
    intFsum (fun _ => (0 : Int)) n = 0
  | 0 => rfl
  | n + 1 => by rw [intFsum, intFsum_zero_local n, Int.add_zero]

private theorem boxCellIntSum_congr
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

private theorem boxCellIntSum_add
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
          (fun b => intFsum (fun b' =>
            f a a' b b' + g a a' b b') (N + 1))
          (fun b => intFsum (fun b' => f a a' b b') (N + 1) +
            intFsum (fun b' => g a a' b b') (N + 1)) (N + 1)]
      · exact intFsum_add_local _ _ (N + 1)
      · intro b _
        exact intFsum_add_local _ _ (N + 1)

private theorem boxCellIntSum_mul_right
    (N : Nat) (f : Nat -> Nat -> Nat -> Nat -> Int) (z : Int) :
    boxCellIntSum N (fun a a' b b' => f a a' b b' * z) =
      boxCellIntSum N f * z := by
  unfold boxCellIntSum
  rw [intFsum_congr_local
      (fun a => intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
        f a a' b b' * z) (N + 1)) (N + 1)) (N + 1))
      (fun a => intFsum (fun a' => intFsum (fun b => intFsum (fun b' =>
        f a a' b b') (N + 1)) (N + 1)) (N + 1) * z) (N + 1)]
  · exact intFsum_mul_right_local _ z (N + 1)
  · intro a _
    rw [intFsum_congr_local
        (fun a' => intFsum (fun b => intFsum (fun b' =>
          f a a' b b' * z) (N + 1)) (N + 1))
        (fun a' => intFsum (fun b => intFsum (fun b' =>
          f a a' b b') (N + 1)) (N + 1) * z) (N + 1)]
    · exact intFsum_mul_right_local _ z (N + 1)
    · intro a' _
      rw [intFsum_congr_local
          (fun b => intFsum (fun b' => f a a' b b' * z) (N + 1))
          (fun b => intFsum (fun b' => f a a' b b') (N + 1) * z)
          (N + 1)]
      · exact intFsum_mul_right_local _ z (N + 1)
      · intro b _
        exact intFsum_mul_right_local _ z (N + 1)

private theorem boxCellIntSum_zero (N : Nat) :
    boxCellIntSum N (fun _ _ _ _ => 0) = 0 := by
  unfold boxCellIntSum
  simp only [intFsum_zero_local]

/-! ### 1.2 Exact seam to Track A's term-filtered prefix -/

theorem boxClearedPowerPrefix_zero (N s : Nat) :
    boxClearedPowerPrefix N s 0 = 0 := by
  change boxCellIntSum N (fun a a' b b' =>
    if boxQuadHalfExponent a a' b b' < 0 then
      boxCellClearedCoefficient N s a a' b b'
    else 0) = 0
  rw [boxCellIntSum_congr
    (g := fun _ _ _ _ => 0) (fun _ _ _ _ _ _ _ _ => by simp)]
  exact boxCellIntSum_zero N

theorem boxClearedPowerPrefix_succ (N s K : Nat) :
    boxClearedPowerPrefix N s (K + 1) =
      boxClearedPowerPrefix N s K +
        boxCellIntSum N (fun a a' b b' =>
          if boxQuadHalfExponent a a' b b' = K then
            boxCellClearedCoefficient N s a a' b b'
          else 0) := by
  change boxCellIntSum N (fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' < K + 1 then
        boxCellClearedCoefficient N s a a' b b'
      else 0) =
    boxCellIntSum N (fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' < K then
        boxCellClearedCoefficient N s a a' b b'
      else 0) +
    boxCellIntSum N (fun a a' b b' =>
      if boxQuadHalfExponent a a' b b' = K then
        boxCellClearedCoefficient N s a a' b b'
      else 0)
  rw [← boxCellIntSum_add]
  apply boxCellIntSum_congr
  intro a a' b b' _ _ _ _
  by_cases hlt : boxQuadHalfExponent a a' b b' < K
  · have hnext : boxQuadHalfExponent a a' b b' < K + 1 := by omega
    have hne : Not (boxQuadHalfExponent a a' b b' = K) := by omega
    simp [hlt, hnext, hne]
  · by_cases heq : boxQuadHalfExponent a a' b b' = K
    · simp [hlt, heq]
    · have hnext : Not (boxQuadHalfExponent a a' b b' < K + 1) := by omega
      simp [hlt, heq, hnext]

theorem boxClearedPowerShell_eq_raw
    (N s K : Nat) (hK : K <= boxBernsteinDegree N) :
    boxCellIntSum N (fun a a' b b' =>
        if boxQuadHalfExponent a a' b b' = K then
          boxCellClearedCoefficient N s a a' b b'
        else 0) =
      rawPowerCoeff N s K *
        Int.ofNat (4 ^ (boxBernsteinDegree N - K)) := by
  unfold rawPowerCoeff
  rw [← boxCellIntSum_mul_right]
  apply boxCellIntSum_congr
  intro a a' b b' ha ha' hb hb'
  by_cases heq : boxQuadHalfExponent a a' b b' = K
  · simp only [if_pos heq]
    rw [boxCellClearedCoefficient_eq_raw_mul
      (boxQuadHalfExponent_le_degree
        (by omega) (by omega) (by omega) (by omega)), heq]
  · simp [heq]

theorem boxClearedPowerPrefix_step
    (N s K : Nat) (hK : K <= boxBernsteinDegree N) :
    boxClearedPowerPrefix N s (K + 1) =
      boxClearedPowerPrefix N s K +
        rawPowerCoeff N s K *
          Int.ofNat (4 ^ (boxBernsteinDegree N - K)) := by
  rw [boxClearedPowerPrefix_succ, boxClearedPowerShell_eq_raw N s K hK]

/-- The requested exact seam: Track A's first `k+1` cleared physical power
shells are a positive terminal power of four times the four-adic raw prefix. -/
theorem boxClearedPowerPrefix_eq_fourPrefix
    (N s k : Nat) (hk : k <= boxBernsteinDegree N) :
    boxClearedPowerPrefix N s (k + 1) =
      fourPrefix (rawPowerCoeff N s) k *
        Int.ofNat (4 ^ (boxBernsteinDegree N - k)) := by
  induction k with
  | zero =>
      rw [boxClearedPowerPrefix_step N s 0 (by omega),
        boxClearedPowerPrefix_zero, fourPrefix_zero]
      simp
  | succ k ih =>
      have hk' : k <= boxBernsteinDegree N := by omega
      rw [boxClearedPowerPrefix_step N s (k + 1) hk, ih hk',
        fourPrefix_succ]
      have hsub : boxBernsteinDegree N - k =
          (boxBernsteinDegree N - (k + 1)) + 1 := by omega
      rw [hsub, Nat.pow_succ, Int.ofNat_eq_natCast, Int.natCast_mul,
        Int.add_mul]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      have hcast : ((4 : Nat) : Int) = (4 : Int) := rfl
      rw [hcast]
      have hpowcast :
          ((4 ^ (boxBernsteinDegree N - (k + 1)) : Nat) : Int) =
            Int.ofNat (4 ^ (boxBernsteinDegree N - (k + 1))) :=
        (Int.ofNat_eq_natCast _).symm
      rw [hpowcast]

/-! ## 2. Strand energy identities -/

/-- The quadratic Casimir has the same parity as its label. -/
theorem c4_mod_two (n : Nat) : c4 n % 2 = n % 2 := by
  exact YMGap.Continuum.CoreBUniversalSquareGap.c4_mod_two n

/-- Adding a common strand `r` separates its heat cost exactly. -/
theorem c4_common_strand (p q r : Nat) :
    c4 (p + r) + c4 (q + r) =
      c4 p + c4 q + 2 * r * (p + q + r + 2) := by
  unfold c4
  simp only [Nat.add_mul, Nat.mul_add, Nat.two_mul, Nat.mul_two]
  ac_rfl

/-- Even antidiagonal energy: displacement `d` costs exactly `2*d^2`
before the common-strand contribution. -/
theorem c4_even_strand (m d r : Nat) (hd : d <= m) :
    c4 (m - d + r) + c4 (m + d + r) =
      2 * c4 m + 2 * d * d + 2 * r * (2 * m + r + 2) := by
  have hbase :=
    YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent_even_left m d hd
  have hright : 2 * m - (m - d) = m + d := by omega
  unfold YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent at hbase
  rw [hright] at hbase
  have hcommon := c4_common_strand (m - d) (m + d) r
  have hsum : m - d + (m + d) = 2 * m := by omega
  rw [hsum] at hcommon
  omega

/-- Odd antidiagonal energy: the two central positions are `d=0` and their
reflections; the displacement cost is `2*d*(d+1)`. -/
theorem c4_odd_strand (m d r : Nat) (hd : d <= m) :
    c4 (m - d + r) + c4 (m + 1 + d + r) =
      c4 m + c4 (m + 1) + 2 * d * (d + 1) +
        2 * r * (2 * m + r + 3) := by
  have hbase :=
    YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent_odd_left m d hd
  have hright : 2 * m + 1 - (m - d) = m + 1 + d := by omega
  unfold YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent at hbase
  rw [hright] at hbase
  have hcommon := c4_common_strand (m - d) (m + 1 + d) r
  have hsum : m - d + (m + 1 + d) = 2 * m + 1 := by omega
  rw [hsum] at hcommon
  have hnorm : 2 * m + 1 + r + 2 = 2 * m + r + 3 := by omega
  rw [hnorm] at hcommon
  omega

/-- The physical cross-difference exponent is even whenever the two fusion
parities agree with channels `s,s+2` (or twice with `s+1`). -/
theorem four_label_casimir_even_of_parity
    {a b c d s : Nat}
    (hab : (a + b + s) % 2 = 0)
    (hcd : (c + d + (s + 2)) % 2 = 0) :
    (c4 a + c4 b + c4 c + c4 d) % 2 = 0 := by
  have ha := c4_mod_two a
  have hb := c4_mod_two b
  have hc := c4_mod_two c
  have hd := c4_mod_two d
  omega

/-! ## 2.1 Balanced-shell lower support -/

/-- Every active even fusion channel lies above its balanced antidiagonal
Casimir.  The common strand can only increase the heat exponent. -/
theorem fusionCasimir_even_min
    {a b m : Nat} (hactive : fusionOK a b (2 * m) = true) :
    2 * c4 m <= c4 a + c4 b := by
  obtain ⟨p, q, r, ha, hb, ht⟩ :=
    (YMGap.Continuum.FusionCoreStepRoundD.fusionOK_strand
      a b (2 * m)).mp hactive
  have hp : p <= 2 * m := by omega
  have hcenter :=
    YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent_even_center_minimum
      m p hp
  unfold YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent at hcenter
  have hsub : 2 * m - p = q := by omega
  have hmid : 2 * m - m = m := by omega
  rw [hsub, hmid] at hcenter
  have hcommon := c4_common_strand q p r
  rw [ha, hb]
  omega

/-- Every active odd fusion channel lies above one of its two balanced
antidiagonal centres. -/
theorem fusionCasimir_odd_min
    {a b m : Nat} (hactive : fusionOK a b (2 * m + 1) = true) :
    c4 m + c4 (m + 1) <= c4 a + c4 b := by
  obtain ⟨p, q, r, ha, hb, ht⟩ :=
    (YMGap.Continuum.FusionCoreStepRoundD.fusionOK_strand
      a b (2 * m + 1)).mp hactive
  have hp : p <= 2 * m + 1 := by omega
  have hcenter :=
    YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent_odd_center_minimum
      m p hp
  unfold YMGap.Continuum.CoreBAtomwiseGapBounds.antidiagonalExponent at hcenter
  have hsub : 2 * m + 1 - p = q := by omega
  have hmid : 2 * m + 1 - m = m + 1 := by omega
  rw [hsub, hmid] at hcenter
  have hcommon := c4_common_strand q p r
  rw [ha, hb]
  omega

/-- For even difference mode `s=2m`, every active positive or negative
four-cell has half-exponent at least the shared first-shell index. -/
theorem even_boxCellRawCoefficient_zero_below
    (m a a' b b' k : Nat)
    (hk : k < c4 m + c4 (m + 1))
    (he : boxQuadHalfExponent a a' b b' = k) :
    boxCellRawCoefficient (2 * m) a a' b b' = 0 := by
  have hpos : boxPositiveMultiplicity (2 * m) a a' b b' = 0 := by
    unfold boxPositiveMultiplicity boxProductMultiplicity
    by_cases hl : fusionOK a b (2 * m + 1) = true
    · by_cases hr : fusionOK a' b' (2 * m + 1) = true
      · have hminl := fusionCasimir_odd_min (m := m) hl
        have hminr := fusionCasimir_odd_min (m := m) hr
        have hpar := boxQuadExponent_even_of_active (by omega) hl hr
        unfold boxQuadHalfExponent boxQuadExponent at he
        omega
      · simp [hl, hr]
    · simp [hl]
  have hneg : boxNegativeMultiplicity (2 * m) a a' b b' = 0 := by
    unfold boxNegativeMultiplicity boxProductMultiplicity
    by_cases hl : fusionOK a b (2 * m) = true
    · by_cases hr : fusionOK a' b' (2 * m + 2) = true
      · have hminl := fusionCasimir_even_min (m := m) hl
        have hminr := fusionCasimir_even_min (m := m + 1) (by simpa [Nat.mul_add] using hr)
        have hpar := boxQuadExponent_even_of_active (by omega) hl hr
        unfold boxQuadHalfExponent boxQuadExponent at he
        omega
      · simp [hl, hr]
    · simp [hl]
  unfold boxCellRawCoefficient
  rw [hpos, hneg]
  rfl

/-- For odd difference mode `s=2m+1`, every active four-cell has
half-exponent at least `2*c4(m+1)`.  Negative cells in fact start one shell
later; the weaker common bound is exactly what lower-prefix vanishing needs. -/
theorem odd_boxCellRawCoefficient_zero_below
    (m a a' b b' k : Nat)
    (hk : k < 2 * c4 (m + 1))
    (he : boxQuadHalfExponent a a' b b' = k) :
    boxCellRawCoefficient (2 * m + 1) a a' b b' = 0 := by
  have hpos : boxPositiveMultiplicity (2 * m + 1) a a' b b' = 0 := by
    unfold boxPositiveMultiplicity boxProductMultiplicity
    by_cases hl : fusionOK a b (2 * (m + 1)) = true
    · by_cases hr : fusionOK a' b' (2 * (m + 1)) = true
      · have hminl := fusionCasimir_even_min (m := m + 1) hl
        have hminr := fusionCasimir_even_min (m := m + 1) hr
        have hpar := boxQuadExponent_even_of_active (by omega) hl hr
        unfold boxQuadHalfExponent boxQuadExponent at he
        omega
      · simp [hl, hr, show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
    · simp [hl, show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
  have hneg : boxNegativeMultiplicity (2 * m + 1) a a' b b' = 0 := by
    unfold boxNegativeMultiplicity boxProductMultiplicity
    by_cases hl : fusionOK a b (2 * m + 1) = true
    · by_cases hr : fusionOK a' b' (2 * (m + 1) + 1) = true
      · have hminl := fusionCasimir_odd_min (m := m) hl
        have hminr := fusionCasimir_odd_min (m := m + 1) hr
        have hcidx : m + 1 + 1 = m + 2 := by omega
        rw [hcidx] at hminr
        have hcurve :=
          YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two m
        have hpar := boxQuadExponent_even_of_active (by omega) hl hr
        unfold boxQuadHalfExponent boxQuadExponent at he
        omega
      · simp [hl, hr,
          show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega]
    · simp [hl]
  unfold boxCellRawCoefficient
  rw [hpos, hneg]
  rfl

theorem even_rawPowerCoeff_zero_below
    (N m k : Nat) (hk : k < c4 m + c4 (m + 1)) :
    rawPowerCoeff N (2 * m) k = 0 := by
  unfold rawPowerCoeff
  rw [boxCellIntSum_congr (g := fun _ _ _ _ => 0) (fun a a' b b' _ _ _ _ => by
    by_cases he : boxQuadHalfExponent a a' b b' = k
    · simp [he, even_boxCellRawCoefficient_zero_below m a a' b b' k hk he]
    · simp [he])]
  exact boxCellIntSum_zero N

theorem odd_rawPowerCoeff_zero_below
    (N m k : Nat) (hk : k < 2 * c4 (m + 1)) :
    rawPowerCoeff N (2 * m + 1) k = 0 := by
  unfold rawPowerCoeff
  rw [boxCellIntSum_congr (g := fun _ _ _ _ => 0) (fun a a' b b' _ _ _ _ => by
    by_cases he : boxQuadHalfExponent a a' b b' = k
    · simp [he, odd_boxCellRawCoefficient_zero_below m a a' b b' k hk he]
    · simp [he])]
  exact boxCellIntSum_zero N

private theorem fourPrefix_zero_of_below
    (a : Nat -> Int) : forall k,
    (forall i, i <= k -> a i = 0) -> fourPrefix a k = 0
  | 0, h => by rw [fourPrefix_zero, h 0 (by omega)]
  | k + 1, h => by
      rw [fourPrefix_succ,
        fourPrefix_zero_of_below a k (fun i hi => h i (by omega)),
        h (k + 1) (by omega)]
      omega

theorem even_firstShell_le_degree
    (N m : Nat) (hguard : 2 * m + 2 <= 2 * N) :
    c4 m + c4 (m + 1) <= boxBernsteinDegree N := by
  have hbound := boxQuadHalfExponent_le_degree
    (N := N) (a := m) (a' := m) (b := m + 1) (b' := m + 1)
    (by omega) (by omega) (by omega) (by omega)
  unfold boxQuadHalfExponent boxQuadExponent at hbound
  omega

theorem odd_firstShell_le_degree
    (N m : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N) :
    2 * c4 (m + 1) <= boxBernsteinDegree N := by
  have hbound := boxQuadHalfExponent_le_degree
    (N := N) (a := m + 1) (a' := m + 1) (b := m + 1) (b' := m + 1)
    (by omega) (by omega) (by omega) (by omega)
  unfold boxQuadHalfExponent boxQuadExponent at hbound
  omega

/-- Every even-mode physical prefix through the first-shell boundary is
definitionally zero. -/
theorem even_boxClearedPowerPrefix_zero_below
    (N m K : Nat) (hguard : 2 * m + 2 <= 2 * N)
    (hK : K <= c4 m + c4 (m + 1)) :
    boxClearedPowerPrefix N (2 * m) K = 0 := by
  cases K with
  | zero => exact boxClearedPowerPrefix_zero N (2 * m)
  | succ k =>
      have hk0 : k < c4 m + c4 (m + 1) := by omega
      have hkD : k <= boxBernsteinDegree N :=
        Nat.le_trans (by omega) (even_firstShell_le_degree N m hguard)
      rw [boxClearedPowerPrefix_eq_fourPrefix N (2 * m) k hkD,
        fourPrefix_zero_of_below (rawPowerCoeff N (2 * m)) k
          (fun i hi => even_rawPowerCoeff_zero_below N m i (by omega)),
        Int.zero_mul]

/-- Every odd-mode physical prefix through the first-shell boundary is
definitionally zero. -/
theorem odd_boxClearedPowerPrefix_zero_below
    (N m K : Nat) (hguard : 2 * m + 1 + 2 <= 2 * N)
    (hK : K <= 2 * c4 (m + 1)) :
    boxClearedPowerPrefix N (2 * m + 1) K = 0 := by
  cases K with
  | zero => exact boxClearedPowerPrefix_zero N (2 * m + 1)
  | succ k =>
      have hk0 : k < 2 * c4 (m + 1) := by omega
      have hkD : k <= boxBernsteinDegree N :=
        Nat.le_trans (by omega) (odd_firstShell_le_degree N m hguard)
      rw [boxClearedPowerPrefix_eq_fourPrefix N (2 * m + 1) k hkD,
        fourPrefix_zero_of_below (rawPowerCoeff N (2 * m + 1)) k
          (fun i hi => odd_rawPowerCoeff_zero_below N m i (by omega)),
        Int.zero_mul]

/-! ## 3. Pure reserve arithmetic pinned to the actual boxes -/

private theorem mul_le_mul_nonneg {a b c d : Q'}
    (hab : a <= b) (hcd : c <= d)
    (hc : (0 : Q') <= c) (hb : (0 : Q') <= b) :
    a * c <= b * d :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

/-- The two even box-mass ceilings leave a strict `23/64` fraction of the
first-shell reserve.  This is already phrased on the actual `boxSum`; the
only inputs are the two individual mass bounds. -/
theorem even_first_shell_dominates_negative
    (N m : Nat)
    (hleft : boxSum wH N (2 * m) <=
      Q'.mkPos 13 8 (by decide) *
        (coeffW wH m * coeffW wH m))
    (hright : boxSum wH N (2 * m + 2) <=
      Q'.mkPos 13 8 (by decide) *
        (coeffW wH (m + 1) * coeffW wH (m + 1))) :
    boxSum wH N (2 * m) * boxSum wH N (2 * m + 2) <=
      Q'.ofNat 3 *
        ((coeffW wH m * coeffW wH m) *
          (coeffW wH (m + 1) * coeffW wH (m + 1))) := by
  have h0 : (0 : Q') <= boxSum wH N (2 * m) :=
    YMGap.Continuum.FusionCoreInduction.boxSum_nonneg (by decide) _ _
  have h1 : (0 : Q') <= boxSum wH N (2 * m + 2) :=
    YMGap.Continuum.FusionCoreInduction.boxSum_nonneg (by decide) _ _
  have hc0 : (0 : Q') <= coeffW wH m * coeffW wH m :=
    Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) _) (coeffW_nonneg (by decide) _)
  have hc1 : (0 : Q') <= coeffW wH (m + 1) * coeffW wH (m + 1) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) _) (coeffW_nonneg (by decide) _)
  have hb0 : (0 : Q') <= Q'.mkPos 13 8 (by decide) *
      (coeffW wH m * coeffW wH m) := Q'.mul_nonneg _ _ (by decide) hc0
  have hp := mul_le_mul_nonneg hleft hright h1 hb0
  have heq :
      (Q'.mkPos 13 8 (by decide) * (coeffW wH m * coeffW wH m)) *
          (Q'.mkPos 13 8 (by decide) *
            (coeffW wH (m + 1) * coeffW wH (m + 1)))
        <= Q'.ofNat 3 *
          ((coeffW wH m * coeffW wH m) *
            (coeffW wH (m + 1) * coeffW wH (m + 1))) := by
    have hconst : Q'.mkPos 13 8 (by decide) * Q'.mkPos 13 8 (by decide)
        <= Q'.ofNat 3 := by decide
    have hprod : (0 : Q') <=
        (coeffW wH m * coeffW wH m) *
          (coeffW wH (m + 1) * coeffW wH (m + 1)) :=
      Q'.mul_nonneg _ _ hc0 hc1
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hconst hprod
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (YMGap.Continuum.FusionGenFunction.mul_swap4
        (Q'.mkPos 13 8 (by decide)) (coeffW wH m * coeffW wH m)
        (Q'.mkPos 13 8 (by decide))
        (coeffW wH (m + 1) * coeffW wH (m + 1)))) hscaled
  exact Q'.le_trans' _ _ _ hp heq

/-- Dimension ratio appearing in the odd two-shell reserve. -/
def oddPeakRatio (m : Nat) : Q' :=
  Q'.mkPos ((m + 1) * (m + 3)) ((m + 2) * (m + 2))
    (Nat.mul_pos (by omega) (by omega))

theorem oddPeakRatio_nonneg (m : Nat) : (0 : Q') <= oddPeakRatio m := by
  unfold oddPeakRatio
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

theorem oddPeakRatio_le_one (m : Nat) : oddPeakRatio m <= (1 : Q') := by
  unfold oddPeakRatio
  show (Q'.mkPos ((m + 1) * (m + 3)) ((m + 2) * (m + 2))
      (Nat.mul_pos (by omega) (by omega))).num * (((1 : Q').den : Int)) <=
    ((1 : Q').num) *
      ((Q'.mkPos ((m + 1) * (m + 3)) ((m + 2) * (m + 2))
        (Nat.mul_pos (by omega) (by omega))).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  simp only [show (1 : Q').num = 1 from rfl,
    show (((1 : Q').den : Int)) = 1 from rfl,
    Int.ofNat_eq_natCast, Int.natCast_add, Int.mul_one, Int.one_mul]
  change Int.ofNat ((m + 1) * (m + 3)) <=
    Int.ofNat ((m + 2) * (m + 2))
  apply Int.ofNat_le.mpr
  have hleft : (m + 1) * (m + 3) = m * m + 4 * m + 3 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hright : (m + 2) * (m + 2) = m * m + 4 * m + 4 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  rw [hleft, hright]
  omega

/-- Scalar inequality behind the odd two-shell payment:
`(35/32)^2*x <= 1+x^2/4` for `0<=x<=1`. -/
theorem odd_two_shell_scalar {x : Q'}
    (hx0 : (0 : Q') <= x) (hx1 : x <= (1 : Q')) :
    (Q'.mkPos 35 32 (by decide) * Q'.mkPos 35 32 (by decide)) * x <=
      (1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x) := by
  have hconst : Q'.mkPos 35 32 (by decide) * Q'.mkPos 35 32 (by decide)
      <= Q'.mkPos 5 4 (by decide) := by decide
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hconst hx0
  have hfactor0 : (0 : Q') <= (1 : Q') - x := Q'.sub_nonneg_of_le hx1
  have hfactor1 : (0 : Q') <= (1 : Q') - Q'.mkPos 1 4 (by decide) * x := by
    have hxq : Q'.mkPos 1 4 (by decide) * x <= Q'.mkPos 1 4 (by decide) :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hx1 (by decide))
        (Q'.le_of_eqv (Q'.mul_one_eqv _))
    have hxone : Q'.mkPos 1 4 (by decide) * x <= (1 : Q') :=
      Q'.le_trans' _ _ _ hxq (by decide)
    exact Q'.sub_nonneg_of_le hxone
  have hprod := Q'.mul_nonneg _ _ hfactor0 hfactor1
  have hid :
      (((1 : Q') - x) * ((1 : Q') - Q'.mkPos 1 4 (by decide) * x)).eqv
        (((1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x)) +
          -(Q'.mkPos 5 4 (by decide) * x)) := by
    have halg : (((1 : Q') + -x) *
        ((1 : Q') + -(Q'.mkPos 1 4 (by decide) * x))).eqv
        (((1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x)) +
          -(((1 : Q') + Q'.mkPos 1 4 (by decide)) * x)) := by
      ring_qeqv
    have hq : ((1 : Q') + Q'.mkPos 1 4 (by decide)).eqv
        (Q'.mkPos 5 4 (by decide)) := by decide
    have hmul : (((1 : Q') + Q'.mkPos 1 4 (by decide)) * x).eqv
        (Q'.mkPos 5 4 (by decide) * x) :=
      Q'.mul_eqv_congr_right _ _ x hq
    have hneg : (-(((1 : Q') + Q'.mkPos 1 4 (by decide)) * x)).eqv
        (-(Q'.mkPos 5 4 (by decide) * x)) :=
      Q'.neg_eqv_congr _ _ hmul
    exact Q'.eqv_trans _ _ _ halg
      (Q'.add_eqv_congr'
        (Q'.eqv_refl
          ((1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x))) hneg)
  have hgap : Q'.mkPos 5 4 (by decide) * x <=
      (1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x) := by
    have hnonneg : (0 : Q') <=
        ((1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x)) +
          -(Q'.mkPos 5 4 (by decide) * x) :=
      Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv hid)
    exact Q'.le_of_sub_nonneg hnonneg
  exact Q'.le_trans' _ _ _ hfirst hgap

/-! ## 4. Exact all-`N` target -/

/-- The concrete producer is stated directly on Track A's public term-filtered
carrier.  Thus there is no detached polynomial or certificate family between
the analytic reserve and the canonical reconstruction. -/
def AllCutoffPhysicalPrefixReserve : Prop :=
  forall N s K, s + 2 <= 2 * N ->
    0 <= boxClearedPowerPrefix N s K

/-- The genuinely remaining producer after balanced-support elimination.
Only prefixes *strictly beyond* the first physical shell are requested. -/
def PostBoundaryEvenOddPrefixReserve : Prop :=
  (forall N m K, 2 * m + 2 <= 2 * N ->
    c4 m + c4 (m + 1) < K ->
      0 <= boxClearedPowerPrefix N (2 * m) K) ∧
  (forall N m K, 2 * m + 1 + 2 <= 2 * N ->
    2 * c4 (m + 1) < K ->
      0 <= boxClearedPowerPrefix N (2 * m + 1) K)

/-- Exact parity split of the all-cutoff producer.  The lower prefixes are
discharged by the proved support theorems; a downstream shell argument need
only pay the post-boundary obligations above. -/
theorem allCutoffPhysicalPrefixReserve_of_postBoundary
    (hpost : PostBoundaryEvenOddPrefixReserve) :
    AllCutoffPhysicalPrefixReserve := by
  intro N s K hs
  by_cases heven : s % 2 = 0
  · let m := s / 2
    have hsform : s = 2 * m := by unfold m; omega
    rw [hsform] at hs ⊢
    by_cases hK : K <= c4 m + c4 (m + 1)
    · rw [even_boxClearedPowerPrefix_zero_below N m K hs hK]
      omega
    · exact hpost.1 N m K hs (by omega)
  · let m := s / 2
    have hsform : s = 2 * m + 1 := by unfold m; omega
    rw [hsform] at hs ⊢
    by_cases hK : K <= 2 * c4 (m + 1)
    · rw [odd_boxClearedPowerPrefix_zero_below N m K hs hK]
      omega
    · exact hpost.2 N m K hs (by omega)

/-- Positivity of the actual term-filtered carrier cancels its strictly
positive terminal power of four and yields the four-adic raw invariant. -/
theorem raw_fourPrefix_nonnegative_of_physical_reserve
    (reserve : AllCutoffPhysicalPrefixReserve)
    (N s k : Nat) (hs : s + 2 <= 2 * N)
    (hk : k <= boxBernsteinDegree N) :
    0 <= fourPrefix (rawPowerCoeff N s) k := by
  let scale : Int := Int.ofNat (4 ^ (boxBernsteinDegree N - k))
  have hscale : 0 < scale := by
    unfold scale
    exact Int.ofNat_lt.mpr
      (Nat.pow_pos (by decide : 0 < 4) :
        0 < 4 ^ (boxBernsteinDegree N - k))
  have hproduct : 0 <= fourPrefix (rawPowerCoeff N s) k * scale := by
    rw [← boxClearedPowerPrefix_eq_fourPrefix N s k hk]
    exact reserve N s (k + 1) hs
  have hzero : 0 * scale <= fourPrefix (rawPowerCoeff N s) k * scale := by
    simpa using hproduct
  exact Int.le_of_mul_le_mul_right hzero hscale

/-- Once the concrete producer is established, Abel gives coefficientwise
nonnegativity at every cutoff and every full Bernstein degree. -/
theorem all_rows_nonnegative_of_prefix_reserve
    (reserve : AllCutoffPhysicalPrefixReserve) :
    forall N s, s + 2 <= 2 * N ->
      forall j, j <= boxBernsteinDegree N ->
        0 <= clearedBernsteinCoefficient (boxBernsteinDegree N)
          (rawPowerCoeff N s) j := by
  intro N s hs
  exact clearedBernsteinRow_nonnegative_of_prefixes
    (boxBernsteinDegree N) (rawPowerCoeff N s)
    (fun k hk =>
      raw_fourPrefix_nonnegative_of_physical_reserve reserve N s k hs hk)

/-! ## PROVED interface and downstream closure

PROVED here:

* the exact bucketing `rawPowerCoeff` of Track A's four-index cell ledger;
* the exact positive-scale seam `boxClearedPowerPrefix_eq_fourPrefix`;
* exact common/even/odd strand energy identities;
* even first-shell and odd two-shell reserve arithmetic;
* the direct Abel composition from the actual public prefix carrier to every
  coefficient at Track A's canonical degree.

EXPOSED as an input in this module:

* classify the first one/two raw shells and combine those facts with the
  post-boundary prefix comparison to inhabit
  `AllCutoffPhysicalPrefixReserve`.

The bounded strand overcount and the actual `13/8`, `35/32` box-mass
ceilings are now proved in the sibling `FusionBoxStrandCeilings` module.  The
support lemmas here eliminate every prefix through the first-shell boundary.
The post-boundary payment is now proved in
`FusionBoxPostBoundaryClosure`, including the exceptional first two odd
prefixes.

The named target is Track A's actual `boxClearedPowerPrefix` family, and it
is reduced by `allCutoffPhysicalPrefixReserve_of_postBoundary` to the strictly
post-first-shell even/odd obligations, and the downstream definition
`FusionBoxPostBoundaryClosure.allCutoffPhysicalPrefixReserve` supplies the
concrete witness.
-/

end YMGap.Continuum.FusionBoxPrefixReserve

/-! ## Axiom gates -/

#print axioms YMGap.Continuum.FusionBoxPrefixReserve.boxCellClearedCoefficient_eq_raw_mul
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.boxClearedPowerPrefix_step
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.boxClearedPowerPrefix_eq_fourPrefix
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.raw_fourPrefix_nonnegative_of_physical_reserve
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.c4_common_strand
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.c4_even_strand
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.c4_odd_strand
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.four_label_casimir_even_of_parity
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.fusionCasimir_even_min
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.fusionCasimir_odd_min
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.even_boxCellRawCoefficient_zero_below
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.odd_boxCellRawCoefficient_zero_below
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.even_rawPowerCoeff_zero_below
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.odd_rawPowerCoeff_zero_below
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.even_boxClearedPowerPrefix_zero_below
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.odd_boxClearedPowerPrefix_zero_below
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.allCutoffPhysicalPrefixReserve_of_postBoundary
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.even_first_shell_dominates_negative
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.odd_two_shell_scalar
#print axioms YMGap.Continuum.FusionBoxPrefixReserve.all_rows_nonnegative_of_prefix_reserve
