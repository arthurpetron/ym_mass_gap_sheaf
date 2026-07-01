/-
# The Hamiltonian mass gap `Δ = −log sep` UNCONDITIONAL in the separator `sep`.

`GNSHamiltonian.mass_gap_hamiltonian` builds the eigenvalue-level H-gap
`Δ = −log sep > 0` from a located transfer separator, but ONLY on the directly
reducible artanh window `|yOf sep| ≤ 1/3` (equivalently `sep ∈ [1/2, 1)`).  For
`sep < 1/2` the separator is out of window and the gap was merely NAMED by the
residual `HGapBelowWindowResidual` (whose field is a `CRealLogRangeReduction`).

`LocatedSpectralGap.sep` is a RATIONAL, so that range reduction is the DECIDABLE
binary case (pure `num`/`den` arithmetic): write `sep ≃ 2^{−k}·r` with a mantissa
`r = sep·2^k ∈ [1/2, 1)`, whence

    −log sep  =  k·log2  +  (−log r),
       k·log2 ≥ 0   (nonneg),      −log r > 0   (strict, since `r < 1`).

Strictness comes ENTIRELY from the mantissa `−log r`; the `k·log2` summand only
needs to be nonnegative (valid for every `k`, `k = 0` included).  The in-window
`sep ∈ [1/2, 1)` theorem is exactly the `k = 0` restriction of the result here.

# What is delivered (genuine content, `[propext]`/`[propext, Quot.sound]`)

* `binExpOf` — the COMPUTABLE binary exponent `k` with `sep·2^k ∈ [1/2, 1)`,
  built by a genuine well-founded search (`searchBin`), NOT postulated.
* `mant`, its `< 1` / `≥ 1/2` / positivity bounds, and `mant_window` — the
  artanh-window certificate for the mantissa on the NEGATIVE branch (`yOf r < 0`),
  the one genuinely new analytic sub-lemma (a sign-mirror of the existing
  `yOf_sep_neg` + `window_of_eqv_nonneg`).
* `kLog2` (`= k·log2`) and its approximation-nonnegativity.
* `hamiltonianGapRealAll` `= k·log2 + (−log r)` and its strict positivity, reusing
  the in-window transport `isPositive_neg_logRat` VERBATIM with the same witness.
* `mass_gap_hamiltonian_all` — the capstone, `Δ = −log sep > 0` with NO window
  hypothesis, and the honest pin `Δ ≃ −log(ofQ' sep)` through the genuine
  `CRealLogRangeReduction` (discharging what `HGapBelowWindowResidual` named).

The only side hypothesis is `0 < sep.num` (physically the transfer eigenvalue-band
top is positive; e.g. `trivialLocatedGap` has `sep = invSucc _ > 0`), needed for
termination of the search and for `r > 0`.
-/

import YMGap.Continuum.GNSHamiltonian
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.TrigAdd

namespace YMGap.Continuum.HamiltonianAllSep

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap

/-! ## 0. `ofQ'` is multiplicative on constants — reused from `CRealAlg`

`CRealAlg.ofQ'_mul : ofQ'(a·b) ≃ ofQ' a · ofQ' b` is exactly the homomorphism
needed for the scaling relation of the range reduction. -/

/-! ## 1. THE binary-exponent search (genuine well-founded recursion)

For `a ≥ 1`, `d ≥ 1` with `a < d`, find the least `k` with `a·2^k < d ≤ a·2^{k+1}`.
The measure `d − a·2^i` strictly decreases (since `a·2^{i+1} = 2·(a·2^i)` and
`a·2^i ≥ 1`). -/

/-- The upward search returning the exponent together with the two-sided bound. -/
def searchBin (a d : Nat) (ha : 0 < a) (i : Nat) (hinv : a * 2 ^ i < d) :
    { k : Nat // a * 2 ^ k < d ∧ d ≤ a * 2 ^ (k + 1) } :=
  if hP : d ≤ a * 2 ^ (i + 1) then ⟨i, hinv, hP⟩
  else
    have hlt : a * 2 ^ (i + 1) < d := Nat.lt_of_not_le hP
    searchBin a d ha (i + 1) hlt
termination_by d - a * 2 ^ i
decreasing_by
  have hlt : a * 2 ^ (i + 1) < d := Nat.lt_of_not_le hP
  have hassoc : a * 2 ^ (i + 1) = (a * 2 ^ i) * 2 := by rw [Nat.pow_succ, Nat.mul_assoc]
  have hX : 0 < a * 2 ^ i := Nat.mul_pos ha (Nat.two_pow_pos i)
  omega

/-- The binary-exponent datum for a rational `sep` (`Type`-level, Rule 8): an
exponent `k` with `sep.num·2^k < sep.den ≤ sep.num·2^{k+1}`. -/
structure BinExpData (sep : Q') : Type where
  /-- The binary exponent. -/
  k : Nat
  /-- Mantissa below `1`: `sep·2^k < 1`. -/
  hlt : sep.num * ((2 ^ k : Nat) : Int) < (sep.den : Int)
  /-- Mantissa at least `1/2`: `sep·2^{k+1} ≥ 1`. -/
  hge : (sep.den : Int) ≤ sep.num * ((2 ^ (k + 1) : Nat) : Int)

/-- **Constructor**: from `0 < sep.num` and `sep < 1` (`sep.num < sep.den`),
compute the binary exponent by the genuine search. -/
def binExpOf (sep : Q') (hnum : 0 < sep.num) (h1 : sep.num < (sep.den : Int)) :
    BinExpData sep := by
  have hcast : ((sep.num.toNat : Nat) : Int) = sep.num :=
    Int.toNat_of_nonneg (Int.le_of_lt hnum)
  have ha : 0 < sep.num.toNat := by omega
  have hinv0 : sep.num.toNat * 2 ^ 0 < sep.den := by
    rw [Nat.pow_zero, Nat.mul_one]; omega
  let res := searchBin sep.num.toNat sep.den ha 0 hinv0
  refine ⟨res.1, ?_, ?_⟩
  · have hr := res.2.1
    have hcm : ((sep.num.toNat * 2 ^ res.1 : Nat) : Int)
        = sep.num * ((2 ^ res.1 : Nat) : Int) := by rw [Int.natCast_mul, hcast]
    have hcasted : ((sep.num.toNat * 2 ^ res.1 : Nat) : Int) < ((sep.den : Nat) : Int) := by
      exact_mod_cast hr
    rw [hcm] at hcasted; exact hcasted
  · have hr := res.2.2
    have hcm : ((sep.num.toNat * 2 ^ (res.1 + 1) : Nat) : Int)
        = sep.num * ((2 ^ (res.1 + 1) : Nat) : Int) := by rw [Int.natCast_mul, hcast]
    have hcasted : ((sep.den : Nat) : Int) ≤ ((sep.num.toNat * 2 ^ (res.1 + 1) : Nat) : Int) := by
      exact_mod_cast hr
    rw [hcm] at hcasted; exact hcasted

/-! ## 2. The mantissa `r = sep·2^k` and its rational bounds -/

/-- The reduced mantissa `r = sep·2^k`. -/
def mant (sep : Q') (k : Nat) : Q' := sep * Q'.ofNat (2 ^ k)

/-- The scale `2^{−k}` as a positive rational. -/
def scaleQ (k : Nat) : Q' := Q'.mkPos 1 (2 ^ k) (Nat.two_pow_pos k)

/-- `mant sep k < 1`. -/
theorem mant_lt_one (sep : Q') (k : Nat)
    (hlt : sep.num * ((2 ^ k : Nat) : Int) < (sep.den : Int)) : mant sep k < (1 : Q') := by
  show (sep.num * (Q'.ofNat (2 ^ k)).num) * ((1 : Q').den : Int)
     < ((1 : Q').num) * ((sep * Q'.ofNat (2 ^ k)).den : Int)
  rw [Q'.ofNat_num_cast, Q'.mul_den_cast, Q'.ofNat_den_cast]
  have h1 : ((1 : Q').den : Int) = 1 := rfl
  have h2 : ((1 : Q').num) = 1 := rfl
  rw [h1, h2]; simp only [Int.mul_one, Int.one_mul]
  exact hlt

/-- `(mant.den : Int) ≤ mant.num · 2`, i.e. `r ≥ 1/2` in the cross-multiplied form
consumed by the negative-branch window lemma. -/
theorem mant_hhalf (sep : Q') (k : Nat)
    (hge : (sep.den : Int) ≤ sep.num * ((2 ^ (k + 1) : Nat) : Int)) :
    ((mant sep k).den : Int) ≤ (mant sep k).num * 2 := by
  show ((sep * Q'.ofNat (2 ^ k)).den : Int) ≤ (sep.num * (Q'.ofNat (2 ^ k)).num) * 2
  rw [Q'.mul_den_cast, Q'.ofNat_den_cast, Q'.ofNat_num_cast]
  simp only [Int.mul_one]
  have hpow : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) * 2 := by
    have hn : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    rw [hn, Int.natCast_mul]; rfl
  rw [Int.mul_assoc, ← hpow]
  exact hge

/-- `0 < mant sep k + 1` (needed for `yOf (mant sep k)`). -/
theorem mant_pos (sep : Q') (k : Nat) (hnum : 0 < sep.num) : (0 : Q') < mant sep k + 1 := by
  have hmn : 0 < (mant sep k).num := by
    show 0 < sep.num * (Q'.ofNat (2 ^ k)).num
    rw [Q'.ofNat_num_cast]
    exact Int.mul_pos hnum (by exact_mod_cast Nat.two_pow_pos k)
  have hmd : (0 : Int) < ((mant sep k).den : Int) := by exact_mod_cast (mant sep k).den_pos
  show (0 : Int) * ((mant sep k + 1).den : Int)
      < ((mant sep k).num * (1 : Int) + (1 : Int) * ((mant sep k).den : Int)) * (1 : Int)
  omega

/-! ## 3. The negative-branch artanh-window certificate for the mantissa

`yOf r = (r−1)/(r+1)`.  For `1/2 ≤ r < 1` we have `−1/3 ≤ yOf r < 0`, so
`|yOf r| = −yOf r ≤ 1/3`.  The lower bound `−1/3 ≤ yOf r` is the cross-multiplied
`r ≥ 1/2` identity; the upper bound `yOf r ≤ 1/3` is `yOf r < 0 < 1/3`. -/

/-- The closed-form numerator of `yOf r`: `(r.num − r.den)·r.den`. -/
theorem yOf_num_eq (r : Q') (hr1 : (0 : Q') < r + 1) :
    (yOf r hr1).num = (r.num - (r.den : Int)) * (r.den : Int) := by
  show (r + -1).num * (Q'.recipPos (r + 1) hr1).num = (r.num - (r.den : Int)) * (r.den : Int)
  rw [Q'.recipPos_num, Q'.add_num_cast, Q'.add_den_cast]
  have h1 : ((-1 : Q').den : Int) = 1 := rfl
  have h2 : ((-1 : Q').num) = -1 := rfl
  have h3 : ((1 : Q').den : Int) = 1 := rfl
  rw [h1, h2, h3]; simp only [Int.mul_one]
  have hstep : r.num + -1 * (r.den : Int) = r.num - (r.den : Int) := by omega
  rw [hstep]

/-- The closed-form denominator of `yOf r`: `r.den·(r.num + r.den)`. -/
theorem yOf_den_eq (r : Q') (hr1 : (0 : Q') < r + 1) :
    ((yOf r hr1).den : Int) = (r.den : Int) * (r.num + (r.den : Int)) := by
  show (((r + -1) * Q'.recipPos (r + 1) hr1).den : Int)
     = (r.den : Int) * (r.num + (r.den : Int))
  rw [Q'.mul_den_cast, Q'.recipPos_den, Q'.add_den_cast, Q'.add_num_cast]
  have h1 : ((-1 : Q').den : Int) = 1 := rfl
  have h3 : ((1 : Q').den : Int) = 1 := rfl
  have h4 : ((1 : Q').num) = 1 := rfl
  rw [h1, h3, h4]; simp only [Int.mul_one, Int.one_mul]

/-- The pure-`Int` inequality behind `−1/3 ≤ yOf r`: from `0 ≤ D` and `D ≤ N·2`,
`(−1)·(D·(N+D)) ≤ ((N−D)·D)·3`. -/
theorem key_int (N D : Int) (hD : 0 ≤ D) (hh : D ≤ N * 2) :
    (-1) * (D * (N + D)) ≤ ((N - D) * D) * 3 := by
  have hkey : 0 ≤ D * (2 * N - D) := Int.mul_nonneg hD (by omega)
  have e1 : D * (N + D) = D * N + D * D := by rw [Int.mul_add]
  have e2 : (N - D) * D = D * N - D * D := by rw [Int.sub_mul, Int.mul_comm N D]
  have e3 : D * (2 * N - D) = 2 * (D * N) - D * D := by
    rw [Int.mul_sub, Int.mul_comm D (2 * N), Int.mul_assoc, Int.mul_comm N D]
  rw [e1, e2]; rw [e3] at hkey; omega

/-- **The negative-branch window certificate.**  For `1/2 ≤ r < 1` (`0 < r+1`),
`|yOf r| ≤ 1/3`. -/
theorem window_neg (r : Q') (hr1 : (0 : Q') < r + 1) (hrlt : r < 1)
    (hhalf : (r.den : Int) ≤ r.num * 2) : Q'.abs (yOf r hr1) ≤ recipOdd 1 := by
  apply Q'.abs_le
  · show ((-(recipOdd 1)).num) * ((yOf r hr1).den : Int)
       ≤ (yOf r hr1).num * ((-(recipOdd 1)).den : Int)
    have hnum : ((-(recipOdd 1)).num) = -1 := rfl
    have hden : ((-(recipOdd 1)).den : Int) = 3 := rfl
    rw [hnum, hden, yOf_num_eq, yOf_den_eq]
    have hD : (0 : Int) ≤ (r.den : Int) := by exact_mod_cast Nat.zero_le r.den
    exact key_int r.num (r.den : Int) hD hhalf
  · have hneg : yOf r hr1 < 0 := YMGap.Continuum.yOf_sep_neg r hr1 hrlt
    exact Q'.le_trans' _ _ _ (Q'.le_of_lt hneg) (recipOdd_nonneg 1)

/-- The mantissa window certificate, packaged from a `BinExpData`. -/
theorem mant_window (sep : Q') (be : BinExpData sep) (hnum : 0 < sep.num) :
    Q'.abs (yOf (mant sep be.k) (mant_pos sep be.k hnum)) ≤ recipOdd 1 :=
  window_neg (mant sep be.k) (mant_pos sep be.k hnum)
    (mant_lt_one sep be.k be.hlt) (mant_hhalf sep be.k be.hge)

/-! ## 4. `k·log2` as a nonnegative `CReal` -/

/-- Partial sums of the artanh series for a nonnegative argument are nonnegative. -/
theorem partialSum_nonneg_of_nonneg (y : Q') (hy : (0 : Q') ≤ y) (n : Nat) :
    (0 : Q') ≤ partialSum y n := by
  have h := partialSum_mono_of_nonneg y hy 0 n
  rw [partialSum_zero, Nat.zero_add] at h
  exact h

/-- Every approximation of `log2` is nonnegative (`yOf 2 ≥ 0`). -/
theorem log2_approx_nonneg (n : Nat) : (0 : Q') ≤ log2.approx n := by
  show (0 : Q') ≤ partialSum (yOf (2 : Q') (by decide)) n
      + partialSum (yOf (2 : Q') (by decide)) n
  have h1 := partialSum_nonneg_of_nonneg (yOf (2 : Q') (by decide)) yOf_two_nonneg n
  exact Q'.le_trans' _ _ _ h1 (Q'.add_le_self_of_nonneg _ _ h1)

/-- `k·log2` as a `CReal`. -/
def kLog2 : Nat → CReal
  | 0     => CReal.czero
  | k + 1 => CReal.add log2 (kLog2 k)

/-- Every approximation of `kLog2 k` is nonnegative. -/
theorem kLog2_approx_nonneg (k n : Nat) : (0 : Q') ≤ (kLog2 k).approx n := by
  induction k with
  | zero => show (0 : Q') ≤ (CReal.czero).approx n; exact Q'.le_refl' 0
  | succ k ih =>
    show (0 : Q') ≤ (CReal.add log2 (kLog2 k)).approx n
    rw [CReal.add_approx]
    exact Q'.le_trans' _ _ _ (log2_approx_nonneg n)
      (Q'.add_le_self_of_nonneg (log2.approx n) ((kLog2 k).approx n) ih)

/-! ## 5. The unconditional gap object and its positivity -/

/-- The full-range Hamiltonian gap `Δ = k·log2 + (−log r)` as a genuine `CReal`. -/
def hamiltonianGapRealAll (m : Q') (k : Nat) (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) : CReal :=
  CReal.add (kLog2 k) (CReal.neg (logRat m hm1 hyb))

/-- **`Δ = k·log2 + (−log r)` is strictly positive.**  Strictness lives entirely in
`−log r` (via the verbatim in-window transport `isPositive_neg_logRat`); the
`k·log2 ≥ 0` summand cannot destroy it. -/
theorem hamiltonianGapRealAll_pos (m : Q') (k : Nat) (hm1 : (0 : Q') < m + 1)
    (hlt : m < 1) (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) :
    CReal.IsPositive (hamiltonianGapRealAll m k hm1 hyb) := by
  obtain ⟨ε, hε, hle⟩ := YMGap.Continuum.isPositive_neg_logRat m hm1 hlt hyb
  refine ⟨ε, hε, ?_⟩
  intro n
  show ε ≤ ((kLog2 k).approx n + (CReal.neg (logRat m hm1 hyb)).approx n) + Q'.invSucc n
  have h1 : ε ≤ (CReal.neg (logRat m hm1 hyb)).approx n + Q'.invSucc n := hle n
  have ha : (0 : Q') ≤ (kLog2 k).approx n := kLog2_approx_nonneg k n
  have h2 : (CReal.neg (logRat m hm1 hyb)).approx n + Q'.invSucc n
      ≤ ((CReal.neg (logRat m hm1 hyb)).approx n + Q'.invSucc n) + (kLog2 k).approx n :=
    Q'.add_le_self_of_nonneg _ _ ha
  have h3 : (((CReal.neg (logRat m hm1 hyb)).approx n + Q'.invSucc n) + (kLog2 k).approx n).eqv
      (((kLog2 k).approx n + (CReal.neg (logRat m hm1 hyb)).approx n) + Q'.invSucc n) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv ((CReal.neg (logRat m hm1 hyb)).approx n + Q'.invSucc n)
        ((kLog2 k).approx n)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv ((kLog2 k).approx n)
      ((CReal.neg (logRat m hm1 hyb)).approx n) (Q'.invSucc n))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv h3))

/-! ## 6. The scaling relation and the range-reduction datum -/

/-- `scaleQ k · mant sep k ≃ sep` (`2^{−k}·(sep·2^k) = sep`). -/
theorem scaleQ_mul_mant_eqv (sep : Q') (k : Nat) : (scaleQ k * mant sep k).eqv sep := by
  show ((Q'.mkPos 1 (2 ^ k) (Nat.two_pow_pos k)).num * (sep.num * (Q'.ofNat (2 ^ k)).num))
        * (sep.den : Int)
     = sep.num * ((Q'.mkPos 1 (2 ^ k) (Nat.two_pow_pos k) * (sep * Q'.ofNat (2 ^ k))).den : Int)
  rw [Q'.mkPos_num, Q'.ofNat_num_cast, Q'.mul_den_cast, Q'.mul_den_cast, Q'.ofNat_den_cast,
      Q'.mkPos_den]
  simp only [Int.one_mul, Int.mul_one]
  rw [Int.mul_assoc]

/-- **The genuine range-reduction datum** for `ofQ' sep`, discharging what
`HGapBelowWindowResidual` named: scale `2^{−k}`, mantissa `r = sep·2^k` in window,
scaling `sep ≃ 2^{−k}·r`, and `logScale = −k·log2`. -/
def reductionOf (sep : Q') (be : BinExpData sep) (hnum : 0 < sep.num) :
    CRealLogRangeReduction (CReal.ofQ' sep) where
  scale := CReal.ofQ' (scaleQ be.k)
  m := mant sep be.k
  hm1 := mant_pos sep be.k hnum
  hyb := mant_window sep be hnum
  scaling :=
    CReal.Equiv.trans
      (TrigAdd.equiv_ofQ'_of_eqv (Q'.eqv_symm (scaleQ_mul_mant_eqv sep be.k)))
      (CRealAlg.ofQ'_mul (scaleQ be.k) (mant sep be.k))
  logScale := CReal.neg (kLog2 be.k)

/-- `(a + −b) ≃ −(−a + b)` — the pointwise identity pinning `Δ` to `−log sep`. -/
theorem add_neg_eqv_neg_neg_add (a b : Q') : (a + -b).eqv (-(-a + b)) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_eqv_congr_right (-(-a)) a (-b) (Q'.neg_neg_eqv a)))
    (Q'.eqv_symm (Q'.neg_add_eqv (-a) b))

/-! ## 7. Capstone — `Δ = −log sep > 0`, unconditional in `sep` -/

/-- **`mass_gap_hamiltonian_all`.**  For ANY rational separator `sep < 1` with
`0 < sep.num`, the reconstructed Hamiltonian `H = −log T` has a strictly positive
mass gap `Δ`, and `Δ ≃ −log(ofQ' sep)` through the genuine range reduction (no
artanh-window hypothesis).  The in-window `mass_gap_hamiltonian` is the `k = 0`
special case. -/
theorem mass_gap_hamiltonian_all {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) (hnum : 0 < G.gap.sep.num) :
    ∃ Δ : CReal, CReal.IsPositive Δ ∧
      ∃ red : CRealLogRangeReduction (CReal.ofQ' G.gap.sep),
        CReal.Equiv Δ (CReal.neg (CReal.log (CReal.ofQ' G.gap.sep) red)) := by
  -- `sep < 1` in cross-multiplied form
  have h1 : G.gap.sep.num < (G.gap.sep.den : Int) := by
    have h : G.gap.sep.num * (1 : Int) < (1 : Int) * (G.gap.sep.den : Int) := G.gap.sep_lt_one
    omega
  let be := binExpOf G.gap.sep hnum h1
  let hm1 := mant_pos G.gap.sep be.k hnum
  let hyb := mant_window G.gap.sep be hnum
  let red := reductionOf G.gap.sep be hnum
  refine ⟨hamiltonianGapRealAll (mant G.gap.sep be.k) be.k hm1 hyb, ?_, red, ?_⟩
  · exact hamiltonianGapRealAll_pos (mant G.gap.sep be.k) be.k hm1
      (mant_lt_one G.gap.sep be.k be.hlt) hyb
  · -- honest pin: Δ ≃ −(−k·log2 + log r) = k·log2 + (−log r)
    refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
    exact add_neg_eqv_neg_neg_add ((kLog2 be.k).approx n)
      ((logRat (mant G.gap.sep be.k) hm1 hyb).approx n)

end YMGap.Continuum.HamiltonianAllSep

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HamiltonianAllSep.searchBin
#print axioms YMGap.Continuum.HamiltonianAllSep.binExpOf
#print axioms YMGap.Continuum.HamiltonianAllSep.mant_window
#print axioms YMGap.Continuum.HamiltonianAllSep.hamiltonianGapRealAll_pos
#print axioms YMGap.Continuum.HamiltonianAllSep.reductionOf
#print axioms YMGap.Continuum.HamiltonianAllSep.mass_gap_hamiltonian_all
