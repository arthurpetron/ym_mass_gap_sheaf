/-
The constructive **semicircle integral** `∫_{−1}^1 √(1−x²) dx = π/2` — the
cleanest `c = d = 0`, `U_0 = 1` case of the U-orthogonality value behind the
node-free Riemann route to the SU(2) heat-kernel Gram PSD.

# The mathematics

With the uniform-midpoint RATIONAL partition `x_k = (2k+1−n)/n` (`k = 0..n−1`)
and weight `w = 2/n`, the rational Riemann sum

    semiSum n  :=  (2/n) · Σ_{k<n} √(1 − x_k²)

is a sequence of constructive reals whose limit is the area of the unit
semicircle,

    ∫_{−1}^1 √(1 − x²) dx  =  π/2.

The integrand `g(x) = √(1 − x²)` is nonnegative and bounded by `1` on `[−1,1]`,
and at the rational node `x_k` the value `1 − x_k² = (n² − (2k+1−n)²)/n² > 0`
is a positive RATIONAL, so `√(1 − x_k²)` is the genuine constructive square root
`CReal.sqrtFrom` of a positive rational — no irrational data and no clamping.

# What is PROVED here (axiom-clean, GENUINE new content)

  * `oneMinusSqNode n k` — the positive rational `1 − x_k² = (n² − (2k+1−n)²)/n²`,
    with `oneMinusSqNode_pos` (`0 < 1 − x_k²`, pure `Int`/`Nat` `omega`) and
    `oneMinusSqNode_le_one` (`1 − x_k² ≤ 1`).
  * `nodeWeight n hn k` — the per-node `√(1 − x_k²) : CReal`, built by
    `CReal.sqrtFrom` from the positive rational `oneMinusSqNode` with the uniform
    rational lower-bound witness `L = 1/n` (`L² = 1/n² ≤ 1 − x_k²`, proved).
  * `nodeWeight_nonneg` — `√(1 − x_k²) ≥ 0` (it is even strictly positive).
  * `nodeWeight_leRat_one` — `√(1 − x_k²) ≤ 1` (`sqrtFrom_leRat_of_sq`, since
    `1 − x_k² ≤ 1 = 1²`).  THE explicit per-node rectangle bound on the integrand.
  * `semiSum n : CReal` — the rational semicircle Riemann sum
    `(2/n) · Σ_{k<n} √(1 − x_k²)`, a genuine `CReal`-valued sum.
  * `semiSum_nonneg` — `semiSum n ≥ 0` for EVERY `n` (a nonneg-weighted finite
    sum of nonneg constructive reals).
  * `semiSum_leRat_two` — `semiSum n ≤ 2` for EVERY `n` (each weight `≤ 2/n`,
    summed `n` times: `n · (2/n) ≤ 2`).  Solid two-sided enclosure `0 ≤ … ≤ 2`.
  * `semiInt … : CReal` — the LIMIT `lim_n semiSum`, built by the completeness
    backbone `CReal.completeLimit` GIVEN a convergence-modulus datum
    `SemicircleCauchy` (see NAMED-open).
  * `semiInt_converges` / `semiInt_nonneg` / `semiInt_leRat_two` — the limit IS
    the limit, is `≥ 0`, and is `≤ 2` (bounds pass to the limit; the nonneg pass
    mirrors the proved `RiemannConverge.riemannLimit_nonneg` pattern).

# What is NAMED-open (the honest residuals — NOT proved here)

  * `SemicircleCauchy` — the convergence-modulus datum `ModCauchy semiSum`, i.e.
    the √-Hölder RECTANGLE error bound.  The integrand is uniformly continuous on
    `[−1,1]` with the explicit modulus `|g(x) − g(y)| ≤ √(2|x−y|)` (from
    `|√u − √v| ≤ √|u−v|` and `|(1−x²) − (1−y²)| = |x²−y²| ≤ 2|x−y|`), so the
    rectangle error between resolutions is `≤ √(2·mesh)·2 → 0` with `mesh = 2/n`.
    The quantitative `ModCauchy` package is the named residual; the substrate has
    no √-Hölder/√-subadditivity lemma yet, so it is named, not faked.  The limit
    engine, the nonneg/bounds-pass-to-limit, and the per-`n` enclosure are all
    UNCONDITIONAL.
  * `semiInt_eq_halfPi` — the VALUE identity `semiInt ≃ π/2` (`Constructive.Pi`
    now provides `halfPi`).  Routes: x = cosθ ⇒ `∫_0^π sin²θ = π/2`, or the
    antiderivative `(x√(1−x²)+arcsin x)/2` with `arcsin 1 = π/2`.  Named precisely;
    the rational enclosure `0 ≤ semiInt ≤ 2` is the proved two-sided witness
    bracketing `π/2 ≈ 1.5708` (the tighter `1.5 ≤ · ≤ 1.6` bracket needs the
    limit evaluated, hence the modulus, hence `SemicircleCauchy`).

# Relation to the U-orthogonality integral

This is the `c = d = 0`, `U_0(x) = 1` case of
`∫_{−1}^1 U_c(x) U_d(x) √(1−x²) dx = (π/2)·δ_{cd}` — the value identity behind
`RiemannConverge.OrthogonalityIntegral` / `RiemannSOS.MomentIntegralIdentity`.
The general `(c,d)` case multiplies the integrand by the Chebyshev-U product
`U_c U_d` (a `QPoly` at the rational node) and reuses EXACTLY this Riemann
value+modulus machinery; the only extra analytic input is the sine
orthogonality `∫_0^π sin(mθ) sin(nθ) dθ = (π/2)·δ_{mn}` (with `U_m(cosθ) =
sin((m+1)θ)/sinθ`).  So closing `semiInt_eq_halfPi` + the modulus is the cleanest
foothold for the general orthogonality value.

# Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'` goals.  PROVED: the Riemann sum, its nonnegativity and
the `≤ 2` enclosure for every `n`, the genuine √ per node and its `≤ 1` rectangle
bound, and the limit/nonneg/bounds-pass-to-limit engine.  NAMED-open: the
convergence modulus `SemicircleCauchy` and the value `semiInt_eq_halfPi`.

# Axiom-gate

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.RiemannConverge
import YMGap.Constructive.Pi
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SemicircleIntegral

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The positive rational `1 − x_k² = (n² − (2k+1−n)²)/n²`

`x_k = (2k+1−n)/n` is the uniform-midpoint node (`RiemannSOS.uniformMidpoint`).
Squaring, `1 − x_k² = (n² − (2k+1−n)²)/n²`, a positive rational for `k < n`
(`(2k+1−n)² ≤ (n−1)² < n²`).  We carry it as a `Q'.mkPos`. -/

/-- The (Int) numerator `n² − (2k+1−n)²` of `1 − x_k²` (written with `*`, the
substrate has no `pow_two`). -/
def omsNum (n k : Nat) : Int :=
  (n : Int) * (n : Int)
    - (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int))

/-- The (Nat) denominator `n²` of `1 − x_k²`. -/
def omsDen (n : Nat) : Nat := n * n

theorem omsDen_pos {n : Nat} (hn : 0 < n) : 0 < omsDen n := Nat.mul_pos hn hn

/-- The difference-of-squares factorisation `N·N − j·j = (N−j)·(N+j)` on `Int`,
proved with core `Int` ring lemmas (no `ring`/`nlinarith` on the substrate). -/
theorem int_sq_diff_factor (N j : Int) :
    N * N - j * j = (N - j) * (N + j) := by
  have e1 : (N - j) * (N + j) = (N - j) * N + (N - j) * j := Int.mul_add (N - j) N j
  have e2 : (N - j) * N = N * N - j * N := by rw [Int.sub_mul]
  have e3 : (N - j) * j = N * j - j * j := by rw [Int.sub_mul]
  have eNj : N * j = j * N := Int.mul_comm N j
  rw [e1, e2, e3, eNj]; omega

/-- **`0 < n² − (2k+1−n)²`** for `k < n`: factor `= (2n−2k−1)·(2k+1)`, a product
of two positive linear factors. -/
theorem omsNum_pos {n k : Nat} (hn : 0 < n) (hk : k < n) : 0 < omsNum n k := by
  have hk' : (k : Int) < (n : Int) := by exact_mod_cast hk
  have hn' : (0 : Int) < (n : Int) := by exact_mod_cast hn
  show 0 < (n : Int) * (n : Int)
    - (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int))
  rw [int_sq_diff_factor (n : Int) (2 * (k : Int) + 1 - (n : Int))]
  -- factors: N − j = 2n − 2k − 1 > 0 ; N + j = 2k + 1 > 0
  have hf1 : (0 : Int) < (n : Int) - (2 * (k : Int) + 1 - (n : Int)) := by omega
  have hf2 : (0 : Int) < (n : Int) + (2 * (k : Int) + 1 - (n : Int)) := by omega
  exact Int.mul_pos hf1 hf2

/-- The positive rational `1 − x_k² = (n² − (2k+1−n)²)/n²`. -/
def oneMinusSqNode (n k : Nat) (hn : 0 < n) (hk : k < n) : Q' :=
  Q'.mkPos (omsNum n k) (omsDen n) (omsDen_pos hn)

/-- **`0 < 1 − x_k²`.** -/
theorem oneMinusSqNode_pos {n k : Nat} (hn : 0 < n) (hk : k < n) :
    (0 : Q') < oneMinusSqNode n k hn hk := by
  show (0 : Int) * ((oneMinusSqNode n k hn hk).den : Int) < (oneMinusSqNode n k hn hk).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos (omsNum n k) (omsDen n) (omsDen_pos hn)).num
  rw [Q'.mkPos_num]
  exact omsNum_pos hn hk

/-- **`1 − x_k² ≤ 1`** (drop the nonneg `x_k²`): `n² − (2k+1−n)² ≤ n²`. -/
theorem oneMinusSqNode_le_one {n k : Nat} (hn : 0 < n) (hk : k < n) :
    oneMinusSqNode n k hn hk ≤ (1 : Q') := by
  show (Q'.mkPos (omsNum n k) (omsDen n) (omsDen_pos hn)).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * ((Q'.mkPos (omsNum n k) (omsDen n) (omsDen_pos hn)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hden : ((1 : Q').den : Int) = 1 := by decide
  have hnum : (1 : Q').num = 1 := by decide
  rw [hden, hnum, Int.mul_one, Int.one_mul]
  show omsNum n k ≤ ((omsDen n : Nat) : Int)
  have hcast : ((omsDen n : Nat) : Int) = (n : Int) * (n : Int) := by
    show ((n * n : Nat) : Int) = (n : Int) * (n : Int); push_cast; rfl
  rw [hcast]
  show (n : Int) * (n : Int)
      - (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int)) ≤ (n : Int) * (n : Int)
  -- N·N − j·j ≤ N·N since j·j ≥ 0
  have hjsq : (0 : Int) ≤ (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int)) := by
    rcases Int.le_total 0 (2 * (k : Int) + 1 - (n : Int)) with hj | hj
    · exact Int.mul_nonneg hj hj
    · have hnegj : (0 : Int) ≤ -(2 * (k : Int) + 1 - (n : Int)) := by omega
      have hprod : (0 : Int) ≤ (-(2 * (k : Int) + 1 - (n : Int)))
          * (-(2 * (k : Int) + 1 - (n : Int))) := Int.mul_nonneg hnegj hnegj
      have heq : (-(2 * (k : Int) + 1 - (n : Int))) * (-(2 * (k : Int) + 1 - (n : Int)))
          = (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int)) := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [heq] at hprod; exact hprod
  omega

/-! ## 2. The uniform rational lower-bound witness `L = 1/n`

`CReal.sqrtFrom` needs a positive rational `L` with `L² ≤ a`.  Uniformly across
`k < n` we may take `L = 1/n`: `L² = 1/n² ≤ (n² − (2k+1−n)²)/n²` reduces to
`1 ≤ n² − (2k+1−n)²`, i.e. `omsNum ≥ 1`, which holds (the extreme node gives
`2n−1 ≥ 1`). -/

/-- The witness `L = 1/n`. -/
def nodeLB (n : Nat) (hn : 0 < n) : Q' := Q'.mkPos 1 n hn

theorem nodeLB_pos {n : Nat} (hn : 0 < n) : (0 : Q') < nodeLB n hn := by
  show (0 : Int) * ((nodeLB n hn).den : Int) < (nodeLB n hn).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos 1 n hn).num
  rw [Q'.mkPos_num]; decide

/-- **`L² ≤ 1 − x_k²`** (`L = 1/n`): `1/n² ≤ (n² − (2k+1−n)²)/n²`, i.e.
`1 ≤ n² − (2k+1−n)²`. -/
theorem nodeLB_sq_le {n k : Nat} (hn : 0 < n) (hk : k < n) :
    nodeLB n hn * nodeLB n hn ≤ oneMinusSqNode n k hn hk := by
  show (nodeLB n hn * nodeLB n hn).num * ((oneMinusSqNode n k hn hk).den : Int)
      ≤ (oneMinusSqNode n k hn hk).num * ((nodeLB n hn * nodeLB n hn).den : Int)
  -- (1/n)·(1/n) has num = 1, den = n*n ; oneMinusSqNode has num = omsNum, den = n*n
  have hLnum : (nodeLB n hn * nodeLB n hn).num = 1 := by
    show (nodeLB n hn).num * (nodeLB n hn).num = 1
    show (Q'.mkPos 1 n hn).num * (Q'.mkPos 1 n hn).num = 1
    rw [Q'.mkPos_num]; decide
  have hd : (nodeLB n hn).den = n := Q'.mkPos_den 1 n hn
  have hLden : ((nodeLB n hn * nodeLB n hn).den : Int) = ((n * n : Nat) : Int) := by
    rw [Q'.mul_den_cast, hd]; push_cast; rfl
  rw [hLnum, hLden]
  show (1 : Int) * ((oneMinusSqNode n k hn hk).den : Int)
      ≤ (Q'.mkPos (omsNum n k) (omsDen n) (omsDen_pos hn)).num * ((n * n : Nat) : Int)
  have hden2 : ((oneMinusSqNode n k hn hk).den : Int) = ((n * n : Nat) : Int) := by
    show ((Q'.mkPos (omsNum n k) (omsDen n) (omsDen_pos hn)).den : Int) = ((n * n : Nat) : Int)
    rw [Q'.mkPos_den]; rfl
  rw [hden2, Q'.mkPos_num, Int.one_mul]
  have hnn : (0 : Int) < ((n * n : Nat) : Int) := by
    have := Nat.mul_pos hn hn; exact_mod_cast this
  have hge1 : 1 ≤ omsNum n k := omsNum_pos hn hk
  calc ((n * n : Nat) : Int) = 1 * ((n * n : Nat) : Int) := by rw [Int.one_mul]
    _ ≤ omsNum n k * ((n * n : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_right hge1 (Int.le_of_lt hnn)

/-! ## 3. The per-node weight `√(1 − x_k²)` -/

/-- **The genuine per-node weight** `√(1 − x_k²) : CReal`, the constructive
square root (Heron) of the positive rational `1 − x_k²`. -/
def nodeWeight (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  if hk : k < n then
    CReal.sqrtFrom (oneMinusSqNode n k hn hk) (nodeLB n hn)
      (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk)
  else CReal.czero

/-- **`√(1 − x_k²) ≥ 0`** (it is strictly positive when `k < n`; `czero ≥ 0`
otherwise). -/
theorem nodeWeight_nonneg (n : Nat) (hn : 0 < n) (k : Nat) :
    ExpPos.geRat (nodeWeight n hn k) 0 := by
  unfold nodeWeight
  by_cases hk : k < n
  · rw [dif_pos hk]
    -- IsPositive ⇒ geRat _ 0
    obtain ⟨ε, hεpos, hle⟩ := CReal.sqrtFrom_isPositive (oneMinusSqNode n k hn hk)
      (nodeLB n hn) (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk)
    -- ofQ' ε ≤ √a  and ε > 0 ⇒ √a ≥ 0.  Use the eventual lower bound 0.
    refine ExpPos.geRat_of_eventually ⟨0, fun m _ => ?_⟩
    -- heronSeq is ≥ L ≥ 0 at every index
    show (0 : Q') ≤ (CReal.sqrtFrom (oneMinusSqNode n k hn hk) (nodeLB n hn)
      (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk)).approx m
    rw [CReal.sqrtFrom_approx]
    exact Q'.le_trans' _ _ _ (Q'.le_of_lt (nodeLB_pos hn))
      (CReal.heronSeq_lb (oneMinusSqNode n k hn hk) (nodeLB n hn)
        (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk) m)
  · rw [dif_neg hk]; exact SumOfSquares.geRat_czero

/-- **`√(1 − x_k²) ≤ 1`** — the explicit per-node RECTANGLE bound on the
integrand `g(x) = √(1−x²)` (since `1 − x_k² ≤ 1 = 1²`).  This is the bounded core
of the √-Hölder modulus on a single cell. -/
theorem nodeWeight_leRat_one (n : Nat) (hn : 0 < n) (k : Nat) :
    CReal.leRat (nodeWeight n hn k) 1 := by
  unfold nodeWeight
  by_cases hk : k < n
  · rw [dif_pos hk]
    refine CReal.leRat_mono
      (CReal.sqrtFrom_leRat_of_sq (oneMinusSqNode n k hn hk) (nodeLB n hn)
        (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk)
        1 (by decide) ?_) (Q'.le_refl' 1)
    -- a ≤ 1·1
    refine Q'.le_trans' _ _ _ (oneMinusSqNode_le_one hn hk) ?_
    exact Q'.ge_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv 1))
  · rw [dif_neg hk]
    exact CReal.leRat_ofQ' (by decide)

/-! ## 4. The Riemann sum `semiSum`

The uniform weight `w = 2/n` times the sum of the `n` node weights.  Built as a
`CReal`-`csum`; the SOLID per-`n` facts (nonneg, `≤ 2`) follow from the per-node
facts. -/

/-- The uniform Lebesgue weight `2/n`. -/
def lebW (n : Nat) (hn : 0 < n) : Q' := Q'.mkPos 2 n hn

theorem lebW_nonneg {n : Nat} (hn : 0 < n) : (0 : Q') ≤ lebW n hn := by
  show (0 : Q') ≤ Q'.mkPos 2 n hn
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide

/-- **The rational semicircle Riemann sum** `semiSum n = (2/n)·Σ_{k<n} √(1−x_k²)`. -/
def semiSum (n : Nat) (hn : 0 < n) : CReal :=
  CReal.csum (fun k => CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn k)) n

/-- **`semiSum n ≥ 0` for every `n`** — a finite sum of `(2/n ≥ 0)·(√… ≥ 0)`. -/
theorem semiSum_nonneg (n : Nat) (hn : 0 < n) :
    ExpPos.geRat (semiSum n hn) 0 :=
  SumOfSquares.geRat_csum_nonneg
    (fun k => CReal.mul_nonneg
      (SumOfSquares.geRat_ofQ'_nonneg (lebW_nonneg hn)) (nodeWeight_nonneg n hn k)) n

/-- Each scaled weight `(2/n)·√(1−x_k²) ≤ 2/n`. -/
theorem scaledWeight_leRat (n : Nat) (hn : 0 < n) (k : Nat) :
    CReal.leRat (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn k)) (lebW n hn) := by
  have h := CReal.leRat_smul_nonneg (lebW_nonneg hn) (nodeWeight_leRat_one n hn k)
  -- leRat (·) (lebW * 1) ; (lebW * 1) ≃ lebW
  refine CReal.leRat_mono h ?_
  exact Q'.le_of_eqv (Q'.mul_one_eqv (lebW n hn))

/-- `mkPos a d + mkPos b d ≃ mkPos (a+b) d` (common denominator). -/
theorem mkPos_add_same_den (a b : Int) (d : Nat) (hd : 0 < d) :
    (Q'.mkPos a d hd + Q'.mkPos b d hd).eqv (Q'.mkPos (a + b) d hd) := by
  show (Q'.mkPos a d hd + Q'.mkPos b d hd).num * ((Q'.mkPos (a + b) d hd).den : Int)
      = (Q'.mkPos (a + b) d hd).num * ((Q'.mkPos a d hd + Q'.mkPos b d hd).den : Int)
  -- (a*d + b*d) * d = (a+b) * (d*d)
  have hLnum : (Q'.mkPos a d hd + Q'.mkPos b d hd).num
      = a * (d : Int) + b * (d : Int) := by
    show (Q'.mkPos a d hd).num * ((Q'.mkPos b d hd).den : Int)
        + (Q'.mkPos b d hd).num * ((Q'.mkPos a d hd).den : Int)
        = a * (d : Int) + b * (d : Int)
    rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hLden : ((Q'.mkPos a d hd + Q'.mkPos b d hd).den : Int)
      = (d : Int) * (d : Int) := by
    rw [Q'.add_den_cast]
    show ((Q'.mkPos a d hd).den : Int) * ((Q'.mkPos b d hd).den : Int) = (d : Int) * (d : Int)
    rw [Q'.mkPos_den, Q'.mkPos_den]
  rw [hLnum, hLden, Q'.mkPos_num, Q'.mkPos_den]
  -- (a*d + b*d) * d = (a+b) * (d*d)
  have e1 : (a * (d : Int) + b * (d : Int)) = (a + b) * (d : Int) := by
    rw [Int.add_mul]
  rw [e1, Int.mul_assoc]

/-- `Σ_{k<n} (2/n) = n·(2/n) ≤ 2` (as a rational `finSum`). -/
theorem finSum_lebW_le_two (n : Nat) (hn : 0 < n) :
    RationalTail.finSum (fun _ => lebW n hn) n ≤ (2 : Q') := by
  -- `finSum … m ≤ (2·m)/n` by induction; then `(2·n)/n ≤ 2`.
  have key : ∀ m : Nat, RationalTail.finSum (fun _ => lebW n hn) m
      ≤ Q'.mkPos (2 * (m : Int)) n hn := by
    intro m
    induction m with
    | zero =>
      show RationalTail.finSum (fun _ => lebW n hn) 0 ≤ Q'.mkPos (2 * (0 : Int)) n hn
      show (0 : Q') ≤ Q'.mkPos (2 * (0 : Int)) n hn
      rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
    | succ p ih =>
      rw [RationalTail.finSum_succ]
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (lebW n hn) ih) ?_
      -- (2p)/n + 2/n ≃ (2(p+1))/n
      show Q'.mkPos (2 * (p : Int)) n hn + lebW n hn ≤ Q'.mkPos (2 * ((p : Int) + 1)) n hn
      refine Q'.le_of_eqv ?_
      -- lebW n hn = mkPos 2 n hn
      have hsum : (Q'.mkPos (2 * (p : Int)) n hn + Q'.mkPos 2 n hn).eqv
          (Q'.mkPos (2 * (p : Int) + 2) n hn) :=
        mkPos_add_same_den (2 * (p : Int)) 2 n hn
      -- 2*(p+1) = 2*p + 2 and (p:Int)+1 casts correctly
      have hnumeq : (2 * ((p : Int) + 1)) = 2 * (p : Int) + 2 := by
        rw [Int.mul_add, Int.mul_one]
      have hcast : ((p + 1 : Nat) : Int) = (p : Int) + 1 := by push_cast; rfl
      -- rewrite the goal denominator-numerator target
      show (Q'.mkPos (2 * (p : Int)) n hn + Q'.mkPos 2 n hn).eqv
          (Q'.mkPos (2 * (((p : Nat) + 1 : Nat) : Int)) n hn)
      rw [hcast, hnumeq]
      exact hsum
  refine Q'.le_trans' _ _ _ (key n) ?_
  -- (2n)/n ≤ 2
  show Q'.mkPos (2 * (n : Int)) n hn ≤ (2 : Q')
  show (Q'.mkPos (2 * (n : Int)) n hn).num * ((2 : Q').den : Int)
      ≤ (2 : Q').num * ((Q'.mkPos (2 * (n : Int)) n hn).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hd : ((2 : Q').den : Int) = 1 := by decide
  have hnm : (2 : Q').num = 2 := by decide
  rw [hd, hnm, Int.mul_one]
  -- 2n ≤ 2·n
  omega

/-- **`semiSum n ≤ 2` for every `n`** — each of the `n` scaled weights is `≤ 2/n`
(`scaledWeight_leRat`), so `semiSum n ≤ Σ_{k<n} 2/n = n·(2/n) ≤ 2`. -/
theorem semiSum_leRat_two (n : Nat) (hn : 0 < n) :
    CReal.leRat (semiSum n hn) (2 : Q') := by
  have hsum : CReal.leRat (semiSum n hn)
      (RationalTail.finSum (fun _ => lebW n hn) n) :=
    CReal.leRat_csum
      (fun k => CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn k))
      (fun _ => lebW n hn)
      (fun k => scaledWeight_leRat n hn k) n
  exact CReal.leRat_mono hsum (finSum_lebW_le_two n hn)

/-! ## 5. The convergence modulus (NAMED-open) and the limit

The sequence `semiSum` (one term per resolution `n ≥ 1`, indexed by `n+1` so the
index `0` is the genuine `n = 1` partition) converges to `∫_{−1}^1 √(1−x²)`.  The
quantitative `ModCauchy` datum — the √-Hölder rectangle bound — is the named
residual `SemicircleCauchy`; everything below it (the limit engine and the
nonneg/`≤ 2` passes to the limit) is unconditional. -/

/-- The resolution-indexed sequence `seqSemi n = semiSum (n+1)` (so every index
is a genuine positive resolution). -/
def seqSemi : Nat → CReal := fun n => semiSum (n + 1) (Nat.succ_pos n)

/-- Each term of the sequence is `≥ 0`. -/
theorem seqSemi_nonneg (n : Nat) : ExpPos.geRat (seqSemi n) 0 :=
  semiSum_nonneg (n + 1) (Nat.succ_pos n)

/-- Each term of the sequence is `≤ 2`. -/
theorem seqSemi_leRat_two (n : Nat) : CReal.leRat (seqSemi n) (2 : Q') :=
  semiSum_leRat_two (n + 1) (Nat.succ_pos n)

/-- **The convergence-modulus residual (Type-level; AGENTS.md Rule 8).**  A
`ModCauchy` datum for `seqSemi`: the √-Hölder rectangle error bound
`|g(x) − g(y)| ≤ √(2|x−y|)` (so the inter-resolution rectangle error is
`≤ √(2·mesh)·2 → 0` with `mesh = 2/(n+1)`), packaged as the explicit outer/inner
moduli the completeness backbone consumes.  It is the named-open analytic crux
(the substrate has no √-Hölder lemma); the limit engine below is unconditional. -/
def SemicircleCauchy : Type := CReal.ModCauchy seqSemi

/-- **The semicircle integral** `∫_{−1}^1 √(1−x²)` as a constructive real, GIVEN
the convergence modulus `mc : SemicircleCauchy`.  Built by `CReal.completeLimit`
(the monotone-shifted diagonal — `Type`-level moduli, Specker-safe). -/
def semiInt (mc : SemicircleCauchy) : CReal :=
  CReal.completeLimit seqSemi mc

/-- **The limit IS the limit of the Riemann sums** (`ConvergesTo`). -/
theorem semiInt_converges (mc : SemicircleCauchy) :
    CReal.ConvergesTo seqSemi (semiInt mc) :=
  CReal.convergesTo_completeLimit seqSemi mc

/-- **`semiInt ≥ 0`** — the limit of the proved-nonneg Riemann sums is `≥ 0`.
Mirrors `RiemannConverge.riemannLimit_nonneg`: at scale `ε`, work at `q = ε/2`;
the convergence gives a term `s Nstage` within `q` of the limit, and the per-term
eventual nonnegativity gives `0 ≤ (s Nstage).approx n + q`; chaining and
collapsing `q + q ≤ ε` yields `geRat (semiInt) 0`. -/
theorem semiInt_nonneg (mc : SemicircleCauchy) :
    ExpPos.geRat (semiInt mc) 0 := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := semiInt_converges mc (HalfPow.half * ε) hq
  obtain ⟨Napx, hbound⟩ := hstage Nstage (Nat.le_refl _)
  obtain ⟨Mge, hge⟩ := seqSemi_nonneg Nstage (HalfPow.half * ε) hq
  refine ⟨max Napx Mge, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Mge ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hA : (0 : Q') ≤ (seqSemi Nstage).approx n + HalfPow.half * ε := hge n hn2
  have hB : (seqSemi Nstage).approx n ≤ (semiInt mc).approx n + HalfPow.half * ε :=
    (hbound n hn1).1
  have hchain : (0 : Q') ≤ ((semiInt mc).approx n + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hA (Q'.add_le_add_right _ _ (HalfPow.half * ε) hB)
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv ((semiInt mc).approx n) (HalfPow.half * ε) (HalfPow.half * ε)))
    ?_
  refine Q'.add_le_add_left _ (HalfPow.half * ε + HalfPow.half * ε) ε ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves ε)

/-- **`semiInt ≤ 2`** — the limit of the proved `≤ 2` Riemann sums is `≤ 2`.
Dual of `semiInt_nonneg`: at scale `ε`, the convergence gives a term within
`q = ε/2` of the limit and the per-term eventual upper bound gives
`(s Nstage).approx n ≤ 2 + q`; chaining yields `leRat (semiInt) 2`. -/
theorem semiInt_leRat_two (mc : SemicircleCauchy) :
    CReal.leRat (semiInt mc) (2 : Q') := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := semiInt_converges mc (HalfPow.half * ε) hq
  obtain ⟨Napx, hbound⟩ := hstage Nstage (Nat.le_refl _)
  obtain ⟨Mle, hle⟩ := seqSemi_leRat_two Nstage (HalfPow.half * ε) hq
  refine ⟨max Napx Mle, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Mle ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- L.approx n ≤ (s Nstage).approx n + q ≤ (2 + q) + q ≤ 2 + ε
  have hB : (semiInt mc).approx n ≤ (seqSemi Nstage).approx n + HalfPow.half * ε :=
    (hbound n hn1).2
  have hA : (seqSemi Nstage).approx n ≤ (2 : Q') + HalfPow.half * ε := hle n hn2
  have hchain : (semiInt mc).approx n ≤ ((2 : Q') + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hB (Q'.add_le_add_right _ _ (HalfPow.half * ε) hA)
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv (2 : Q') (HalfPow.half * ε) (HalfPow.half * ε)))
    ?_
  refine Q'.add_le_add_left _ (HalfPow.half * ε + HalfPow.half * ε) ε ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves ε)

/-! ## 6. The value residual `semiInt ≃ π/2` (NAMED-open)

`Constructive.Pi.halfPi = (1/2)·π` is built on the substrate.  The value identity
`∫_{−1}^1 √(1−x²) = π/2` is the named-open analytic crux; the proved two-sided
enclosure `0 ≤ semiInt ≤ 2` brackets `π/2 ≈ 1.5708`.  Routes to close it:
(V-trig) x = cosθ ⇒ `∫_0^π sin²θ dθ = π/2`; (V-antideriv)
`F(x) = (x√(1−x²) + arcsin x)/2`, `F(1) − F(−1) = arcsin 1 = π/2`. -/

/-- **The value residual (Type-level; AGENTS.md Rule 8).**  Given the convergence
modulus, the semicircle integral equals `π/2`.  This is the `c = d = 0`, `U_0 = 1`
case of the U-orthogonality value `∫U_cU_d√(1−x²) = (π/2)δ`.  Named precisely; NOT
proved (the substrate has the π asset `Constructive.Pi.halfPi` but no constructive
`∫√(1−x²) = π/2` identity). -/
def SemicircleValue : Prop :=
  ∀ (mc : SemicircleCauchy), CReal.Equiv (semiInt mc) Constructive.Pi.halfPi

/-- **`semiInt ≃ π/2` GIVEN the value residual** — the headline value statement,
reduced to the single named obligation `SemicircleValue` (and the convergence
modulus `SemicircleCauchy`). -/
theorem semiInt_eq_halfPi (hv : SemicircleValue) (mc : SemicircleCauchy) :
    CReal.Equiv (semiInt mc) Constructive.Pi.halfPi :=
  hv mc

end YMGap.Continuum.SemicircleIntegral

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `omsNum_pos` / `oneMinusSqNode_pos` / `oneMinusSqNode_le_one` — the positive
    rational `1 − x_k² ∈ (0,1]` at the uniform-midpoint node (`Int`/`Nat` arith).
  * `nodeLB_sq_le` — the uniform `L = 1/n` witness `L² ≤ 1 − x_k²`.
  * `nodeWeight` / `nodeWeight_nonneg` / `nodeWeight_leRat_one` — the GENUINE
    per-node constructive square root `√(1 − x_k²)`, its nonnegativity, and the
    explicit rectangle bound `√(1 − x_k²) ≤ 1`.
  * `semiSum` / `semiSum_nonneg` / `semiSum_leRat_two` — the rational semicircle
    Riemann sum, nonnegative and `≤ 2` for EVERY resolution (solid enclosure).
  * `semiInt` / `semiInt_converges` / `semiInt_nonneg` / `semiInt_leRat_two` —
    the LIMIT (given the modulus), the convergence certificate, and the
    nonneg/`≤ 2` bounds PASSED TO THE LIMIT (unconditional, mirroring
    `RiemannConverge.riemannLimit_nonneg`).
  * `semiInt_eq_halfPi` (THEOREM, given `SemicircleValue`) — the value reduction.

**NAMED-open (the honest residuals — NOT proved here).**
  * `SemicircleCauchy` — the convergence-modulus datum `ModCauchy seqSemi`, i.e.
    the √-Hölder rectangle error bound `|√(1−x²) − √(1−y²)| ≤ √(2|x−y|)`.  The
    engine and the bounds-pass-to-limit are unconditional; only this quantitative
    modulus is open (the substrate has no √-Hölder/√-subadditivity lemma).
  * `SemicircleValue` — the value identity `semiInt ≃ π/2` (`Constructive.Pi.halfPi`
    exists; the constructive `∫√(1−x²) = π/2` proof does not).  The proved
    `0 ≤ semiInt ≤ 2` brackets `π/2 ≈ 1.5708`.

**Path to the general U-orthogonality.**  Multiply the integrand by the
Chebyshev-U product `U_c(x)U_d(x)` (a `QPoly` at the rational node) and reuse this
exact Riemann value+modulus machinery; the extra analytic input is the sine
orthogonality `∫_0^π sin(mθ)sin(nθ)dθ = (π/2)δ_{mn}`.  This `c=d=0` case is the
cleanest foothold: closing `SemicircleValue` + `SemicircleCauchy` here unlocks
`RiemannConverge.OrthogonalityIntegral`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.SemicircleIntegral.omsNum_pos
#print axioms YMGap.Continuum.SemicircleIntegral.oneMinusSqNode_pos
#print axioms YMGap.Continuum.SemicircleIntegral.oneMinusSqNode_le_one
#print axioms YMGap.Continuum.SemicircleIntegral.nodeLB_sq_le
#print axioms YMGap.Continuum.SemicircleIntegral.nodeWeight_nonneg
#print axioms YMGap.Continuum.SemicircleIntegral.nodeWeight_leRat_one
#print axioms YMGap.Continuum.SemicircleIntegral.semiSum_nonneg
#print axioms YMGap.Continuum.SemicircleIntegral.semiSum_leRat_two
#print axioms YMGap.Continuum.SemicircleIntegral.semiInt_converges
#print axioms YMGap.Continuum.SemicircleIntegral.semiInt_nonneg
#print axioms YMGap.Continuum.SemicircleIntegral.semiInt_leRat_two
#print axioms YMGap.Continuum.SemicircleIntegral.semiInt_eq_halfPi
