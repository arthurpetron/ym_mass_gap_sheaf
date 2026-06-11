/-
The **Lindström–Gessel–Viennot / non-intersecting-path (Hankel-moment)**
reduction of the uniform-in-`N` nonnegativity of `P_N = Δ_N / S_N²` for the
SU(2) heat-kernel q-Hankel determinant.

Setup (same uniform base variable as `MomentPositivity`/`Favard`/`QHankel`):
`a = e^{−t/4} ∈ (0,1]`, character moments `m_s = (s+1)·a^{s(s+2)}`, leading
Gram minors `Δ_N(a) = det G[0..N−1]` factoring as `Δ_N = S_N²·P_N` with the
explicit q-product square factor `S_N = SN N` (`QHankel`) and the all-nonneg,
even-exponent residual `P_N` (`P_N(0)=1`, leading coeff `(2N−1)!!`).

# The structural discovery of this file: a genuine Hankel-of-positive-moments form

The SU(2) fusion-Gram minor is `Δ_N = det(⟨χ_i,χ_j⟩)`, the Gram of the
characters `χ_a(θ) = U_a(cosθ)` (Chebyshev-`U`) against the heat-kernel
measure.  Re-expressing in the *power basis* `x = cosθ` turns the Gram into a
genuine **Hankel** matrix of the `x`-moments `h_k = ⟨(cosθ)^k⟩`, and clearing
the dyadic Chebyshev normalization (`ĥ_k := 2^k h_k`) gives the closed form

    ĥ_k(a) = Σ_{r = k, k−2, …, ≥0}  ballot(k,r) · (r+1) · a^{r(r+2)},
    ballot(k,r) = C(k, (k−r)/2) − C(k, (k−r)/2 − 1)   ≥ 0   (ballot numbers).

Every `ĥ_k` is therefore a **manifestly nonnegative integer combination of
monomials** in `a`: the ballot number `ballot(k,r)` *counts* the lattice
paths of length `k` from `0` to `r` staying `≥ 0` (the non-intersecting /
reflection model), and `(r+1) = dim χ_r` is a character dimension.  This is
the LGV/path-positive structure on the *moments*.

Exact computer algebra (sympy, through `N = 6`) gives the **clean Hankel
factorization**

    ┌──────────────────────────────────────────────────────────────────┐
    │   det( ĥ_{i+j} )_{0 ≤ i,j < N}  =  S_N(a)² · P_N(a)   (= `SN N`²·P_N) │
    └──────────────────────────────────────────────────────────────────┘

i.e. the Hankel determinant of the nonneg-coefficient moments `ĥ_k` is the
*same* square factor `SN N` times the *same* residual `P_N` as the fusion
Gram minor.  This is strictly sharper than the value-positivity `Δ_N ≥ 0`:
it exhibits `S_N²·P_N` as a determinant of a matrix whose **entries each have
nonnegative coefficients** with a path-counting meaning.

# What is proved here (axiom-clean; no `Classical`/`sorry`/`native_decide`).

  * `monoNN`, `hMom` — the cleared cos-moment `ĥ_k` as an explicit `QPoly`
    built only from `padd` of `monoNN` (single nonneg monomials), so its
    coefficients are *structurally* `0`/`ofNat`.
  * `hMom_nonneg` — **uniform-in-`k`**: `nonnegCoeffs (hMom k)` for *every*
    `k`, a genuine `∀ k` theorem (not a per-`k` `decide`), because every
    coefficient of `ĥ_k` is a nonneg `ofNat` ballot-weight by construction.
    This is the LGV/path-positivity of the *moment kernel*, formalized.
  * `hankelDet2`, `hankelDet3` — the order-2,3 `ĥ`-Hankel determinants as
    `QPoly`s (cofactor expansion via `pmul`/`psub`), and the `decide`-certified
    identities `hankel_factor_2`, `hankel_factor_3`:
        `det(ĥ_{i+j})_{<N} = (SN N)²·P_N`,  `N = 2,3`,
    realizing the Hankel factorization on the actual nonneg-moment matrix.
  * `P6_nonneg`, `P7_nonneg` — `nonnegCoeffs P_N` extended by `decide` to
    `N = 6, 7` (the verified base was `N = 5` in `Favard`/`LGVPositivity`).
  * `pn_nonneg_of_hankelPositive` — the **named consumer**: the precise
    residual-positivity hypothesis `HankelResidualNonneg` (a `Prop`) that, if
    supplied for all `N`, yields `nonnegCoeffs P_N` uniformly.

# Honest verdict (the wall)

This reduces `nonnegCoeffs P_N` to the *finer* statement that the Hankel
determinant of the path-positive moments `ĥ_k`, *after dividing out the
explicit perfect square `SN N`²*, retains nonnegative coefficients.  The
naive LGV route (Lindström–Gessel–Viennot on the Karlin–McGregor
non-intersecting Motzkin paths, equivalently the Stieltjes–Rogers
J-fraction `det = ∏ λ_k^{N−k}`) does **not** close it: the J-fraction weights
`λ_k = H_{k+1}H_{k−1}/H_k²` are **rational, not nonneg-coefficient** — the
residual `P_k` reappears in the denominator (verified: `λ_k` is a non-polynomial
rational function for `k ≥ 2`).  So although the *moments* `ĥ_k` are
path-positive, the *determinant minor expansion* into a single
manifestly-nonneg monomial path family is obstructed by the square-content
cancellation, exactly as the Favard/Dodgson recurrences were
(`FavardRec`/`LGVPositivity`).  Uniform `nonnegCoeffs P_N` remains **OPEN**;
the named residual obligation `HankelResidualNonneg` is its sharpest form.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.MomentPositivity
import YMGap.Continuum.Favard
import YMGap.Continuum.QHankel

namespace YMGap.Continuum.PNPaths

open YMGap.Constructive
open YMGap.Continuum

/-! ## The cleared cos-moment `ĥ_k` as a structurally-nonneg `QPoly`

`ĥ_k = Σ_{r} ballot(k,r)·(r+1)·a^{r(r+2)}`.  We realize each monomial
`v·a^e` by `monoNN e v = [0,…,0, ofNat v]` (`e` zeros then the nonneg
coefficient), and sum them with `padd`.  Because `monoNN` places only `0`s
and a single `ofNat`, *every* coefficient of the resulting list is nonneg by
construction — no `decide`, uniform in `k`. -/

/-- `monoNN e v = v·a^e` as a coefficient list: `e` zeros then `Q'.ofNat v`. -/
def monoNN : Nat → Nat → QPoly.Poly
  | 0, v => [Q'.ofNat v]
  | (e + 1), v => (0 : Q') :: monoNN e v

/-- A single nonneg monomial is nonneg-coefficient (uniform in `e, v`). -/
theorem monoNN_nonneg : ∀ (e v : Nat), nonnegCoeffsB (monoNN e v) = true
  | 0, v => by
      show nonnegCoeffsB [Q'.ofNat v] = true
      rw [nonnegCoeffsB, nonnegCoeffsB, Bool.and_eq_true]
      exact ⟨decide_eq_true (by
        rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _), rfl⟩
  | (e + 1), v => by
      show nonnegCoeffsB ((0 : Q') :: monoNN e v) = true
      exact nonnegCoeffsB_cons_zero (monoNN_nonneg e v)

/-- Binomial coefficient `C(n,k)` via Pascal's recurrence (self-contained;
the ambient prelude here does not provide `Nat.choose`). -/
def choose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _+1   => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- The ballot number `C(k, (k−r)/2) − C(k, (k−r)/2 − 1)` as a `Nat`
(truncated subtraction; equals the genuine nonneg ballot count).  At `j = 0`
the second term is `C(k,−1) = 0` (handled explicitly, since `j − 1 = 0` in
`Nat` would wrongly read `C(k,0)`). -/
def ballotNat (k r : Nat) : Nat :=
  let j := (k - r) / 2
  match j with
  | 0 => 1
  | j + 1 => choose k (j + 1) - choose k j

/-- Accumulate `ĥ_k = Σ_{r = k, k−2, …} ballot(k,r)·(r+1)·a^{r(r+2)}` over the
descending-by-2 index `r` (encoded via the loop bound `step`, with
`r = k − 2·step`). -/
def hMomAux (k : Nat) : Nat → QPoly.Poly
  | 0 => monoNN (k * (k + 2)) (ballotNat k k * (k + 1))
  | (step + 1) =>
      let r := k - 2 * (step + 1)
      QPoly.padd (monoNN (r * (r + 2)) (ballotNat k r * (r + 1)))
        (hMomAux k step)

/-- The cleared cos-moment `ĥ_k` (`= 2^k ⟨(cosθ)^k⟩`), as a `QPoly` built from
nonneg ballot-weighted monomials.  `k / 2` steps cover `r = k, k−2, …, ≥ 0`. -/
def hMom (k : Nat) : QPoly.Poly := hMomAux k (k / 2)

/-! ## Uniform-in-`k` nonnegativity of the moment kernel (LGV path-positivity)

Every coefficient of `ĥ_k` is a nonneg `ofNat` ballot-weight by construction,
so `nonnegCoeffs (hMom k)` holds for **all** `k` — a genuine `∀ k` theorem,
the formal content of "the moments are path-positive". -/

/-- `hMomAux k step` is nonneg-coefficient for every `k, step`
(`padd`-closure of `monoNN` atoms). -/
theorem hMomAux_nonneg (k : Nat) : ∀ step, nonnegCoeffsB (hMomAux k step) = true
  | 0 => monoNN_nonneg _ _
  | (step + 1) => by
      show nonnegCoeffsB (QPoly.padd (monoNN _ _) (hMomAux k step)) = true
      exact nonnegCoeffsB_padd _ _ (monoNN_nonneg _ _) (hMomAux_nonneg k step)

/-- **Uniform moment-kernel positivity.**  For *every* `k`, the cleared
cos-moment `ĥ_k = hMom k` has all-nonnegative coefficients.  This is the
LGV/path-positive structure of the heat-kernel moments, as a single `∀ k`
theorem (the ballot weights `ballot(k,r)·(r+1)` are nonneg integer monomial
coefficients by construction). -/
theorem hMom_nonneg (k : Nat) : nonnegCoeffs (hMom k) :=
  hMomAux_nonneg k (k / 2)

/-! ## The `ĥ_k` agree with the hand-tabulated cleared moments

`decide`-checks that the uniform `hMom` builder reproduces the exact cleared
cos-moments `2^k⟨(cosθ)^k⟩` (low→high coefficient lists, computer algebra),
`k = 0,…,4`.  Constant terms `1,_,1,_,2` are the Catalan numbers `C_{k/2}`,
leading coefficients `k+1`. -/

/-- `ĥ_0 = 1`. -/
theorem hMom0_eq : hMom 0 = [Q'.ofNat 1] := by decide
/-- `ĥ_1 = 2a³`. -/
theorem hMom1_eq : hMom 1 = [0, 0, 0, Q'.ofNat 2] := by decide
/-- `ĥ_2 = 1 + 3a⁸`. -/
theorem hMom2_eq : hMom 2 = [Q'.ofNat 1, 0, 0, 0, 0, 0, 0, 0, Q'.ofNat 3] := by decide
/-- `ĥ_3 = 4a³ + 4a¹⁵`. -/
theorem hMom3_eq :
    hMom 3 = [0, 0, 0, Q'.ofNat 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Q'.ofNat 4] := by decide
/-- `ĥ_4 = 2 + 9a⁸ + 5a²⁴`. -/
theorem hMom4_eq :
    hMom 4 = [Q'.ofNat 2, 0, 0, 0, 0, 0, 0, 0, Q'.ofNat 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, Q'.ofNat 5] := by decide

/-! ## The `ĥ`-Hankel determinant factorization `det(ĥ_{i+j}) = SN²·P_N`

The order-`N` Hankel determinant of the nonneg moments `ĥ_k` equals the
*same* square factor `SN N` (`QHankel`) times the *same* residual `P_N`.  We
build the determinant as a `QPoly` by cofactor expansion (`pmul`/`psub`) and
certify the identity by `decide` for `N = 2, 3`. -/

/-- The order-2 `ĥ`-Hankel determinant `ĥ_0·ĥ_2 − ĥ_1²`. -/
def hankelDet2 : QPoly.Poly :=
  QPoly.psub (QPoly.pmul (hMom 0) (hMom 2)) (QPoly.pmul (hMom 1) (hMom 1))

/-- The order-3 `ĥ`-Hankel determinant (Sarrus / cofactor expansion of the
`3×3` matrix `(ĥ_{i+j})`):
`ĥ_0(ĥ_2ĥ_4 − ĥ_3²) − ĥ_1(ĥ_1ĥ_4 − ĥ_3ĥ_2) + ĥ_2(ĥ_1ĥ_3 − ĥ_2²)`. -/
def hankelDet3 : QPoly.Poly :=
  QPoly.psub
    (QPoly.padd
      (QPoly.pmul (hMom 0)
        (QPoly.psub (QPoly.pmul (hMom 2) (hMom 4)) (QPoly.pmul (hMom 3) (hMom 3))))
      (QPoly.pmul (hMom 2)
        (QPoly.psub (QPoly.pmul (hMom 1) (hMom 3)) (QPoly.pmul (hMom 2) (hMom 2)))))
    (QPoly.pmul (hMom 1)
      (QPoly.psub (QPoly.pmul (hMom 1) (hMom 4)) (QPoly.pmul (hMom 3) (hMom 2))))

/-- **Order-2 Hankel factorization** `det(ĥ_{i+j})_{<2} = (SN 2)²·P_2`,
`decide`-certified.  The Hankel determinant of the path-positive moments is the
square factor times the nonneg residual `P_2`. -/
theorem hankel_factor_2 (x : Q') :
    (QPoly.eval hankelDet2 x).eqv
      (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 2) (SN 2)) P2) x) :=
  QPoly.poly_eqv _ _ x (by decide)

set_option maxRecDepth 4000 in
/-- **Order-3 Hankel factorization** `det(ĥ_{i+j})_{<3} = (SN 3)²·P_3`,
`decide`-certified.  `P_3` from `MomentPositivity`. -/
theorem hankel_factor_3 (x : Q') :
    (QPoly.eval hankelDet3 x).eqv
      (QPoly.eval (QPoly.pmul (QPoly.pmul (SN 3) (SN 3)) P3) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-! ## `P_N ≥ 0` via the Hankel factorization (orders 2, 3)

Through the uniform `SN`-engine (`QHankel.geRat_minor_SN_factored`), each
`ĥ`-Hankel determinant is `≥ 0` at `a ≥ 0`, certified as `(SN N)²·P_N` from the
`decide`-identity above.  These are the Hankel-form analogues of
`delta2/3_nonneg_uniform`. -/

/-- **`det(ĥ_{i+j})_{<2} ≥ 0`** at `a ≥ 0`, via square × nonneg `P_2`. -/
theorem hankelDet2_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval hankelDet2 a) 0 :=
  ceval_factor_nonneg hankelDet2 (SN 2) P2 ha P2_nonneg (fun y => hankel_factor_2 y)

set_option maxRecDepth 4000 in
/-- **`det(ĥ_{i+j})_{<3} ≥ 0`** at `a ≥ 0`, via square × nonneg `P_3`. -/
theorem hankelDet3_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval hankelDet3 a) 0 :=
  ceval_factor_nonneg hankelDet3 (SN 3) P3 ha P3_nonneg (fun y => hankel_factor_3 y)

/-! ## Extending the `decide`-verified `nonnegCoeffs P_N` to `N = 6, 7`

`Favard`/`LGVPositivity` carry `P_1,…,P_5`.  We add the order-6, order-7
residuals (exact computer algebra) and certify `nonnegCoeffs` by `decide`,
pushing the verified base from `N = 5` to `N = 7`. -/

/-- `P_6` coefficient list (low→high), all nonnegative, only even exponents,
constant term `1`, leading coefficient `11!! = 10395`, degree `140`. -/
def P6 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 10, 0, Q'.ofNat 63, 0, Q'.ofNat 286, 0, Q'.ofNat 1070,
   0, Q'.ofNat 3432, 0, Q'.ofNat 9839, 0, Q'.ofNat 25636, 0, Q'.ofNat 61828, 0,
   Q'.ofNat 139338, 0, Q'.ofNat 296316, 0, Q'.ofNat 598126, 0, Q'.ofNat 1152898,
   0, Q'.ofNat 2130306, 0, Q'.ofNat 3788480, 0, Q'.ofNat 6502244, 0,
   Q'.ofNat 10800204, 0, Q'.ofNat 17395974, 0, Q'.ofNat 27226191, 0,
   Q'.ofNat 41467116, 0, Q'.ofNat 61553491, 0, Q'.ofNat 89153350, 0,
   Q'.ofNat 126141252, 0, Q'.ofNat 174502112, 0, Q'.ofNat 236240792, 0,
   Q'.ofNat 313199886, 0, Q'.ofNat 406912710, 0, Q'.ofNat 518355458, 0,
   Q'.ofNat 647788712, 0, Q'.ofNat 794503330, 0, Q'.ofNat 956737044, 0,
   Q'.ofNat 1131497920, 0, Q'.ofNat 1314650618, 0, Q'.ofNat 1500897078, 0,
   Q'.ofNat 1684091135, 0, Q'.ofNat 1857398012, 0, Q'.ofNat 2013827901, 0,
   Q'.ofNat 2146506450, 0, Q'.ofNat 2249325726, 0, Q'.ofNat 2317192020, 0,
   Q'.ofNat 2346626412, 0, Q'.ofNat 2335824510, 0, Q'.ofNat 2285060688, 0,
   Q'.ofNat 2196435390, 0, Q'.ofNat 2074005930, 0, Q'.ofNat 1923221742, 0,
   Q'.ofNat 1750814208, 0, Q'.ofNat 1564030392, 0, Q'.ofNat 1370431980, 0,
   Q'.ofNat 1177100382, 0, Q'.ofNat 990519417, 0, Q'.ofNat 815940996, 0,
   Q'.ofNat 657462885, 0, Q'.ofNat 517652442, 0, Q'.ofNat 397859004, 0,
   Q'.ofNat 298071948, 0, Q'.ofNat 217391304, 0, Q'.ofNat 154040934, 0,
   Q'.ofNat 105859974, 0, Q'.ofNat 70354758, 0, Q'.ofNat 45110220, 0,
   Q'.ofNat 27783522, 0, Q'.ofNat 16380132, 0, Q'.ofNat 9179040, 0,
   Q'.ofNat 4863645, 0, Q'.ofNat 2403840, 0, Q'.ofNat 1099650, 0,
   Q'.ofNat 451170, 0, Q'.ofNat 163485, 0, Q'.ofNat 47250, 0, Q'.ofNat 10395]

/-- **`nonnegCoeffs P_6`** (`decide`) — extends the verified base to `N = 6`. -/
theorem P6_nonneg : nonnegCoeffs P6 := by decide

/-- **`P_6(a) ≥ 1`** for `a ≥ 0` — constant-term-`1` floor. -/
theorem P6_ge_one {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval P6 a) 1 :=
  geRat_ceval_ge_one_of_headGeOne (Q'.ofNat 1) _ ha P6_nonneg (by decide)

/-- `P_7` coefficient list (low→high), all nonnegative, only even exponents,
constant term `1`, leading coefficient `13!! = 135135`, degree `224`. -/
def P7 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 12, 0, Q'.ofNat 88, 0, Q'.ofNat 468, 0, Q'.ofNat 2032,
   0, Q'.ofNat 7552, 0, Q'.ofNat 24958, 0, Q'.ofNat 74872, 0, Q'.ofNat 207439, 0,
   Q'.ofNat 536768, 0, Q'.ofNat 1309610, 0, Q'.ofNat 3033392, 0, Q'.ofNat 6709825,
   0, Q'.ofNat 14238272, 0, Q'.ofNat 29099474, 0, Q'.ofNat 57461408, 0,
   Q'.ofNat 109938185, 0, Q'.ofNat 204274420, 0, Q'.ofNat 369379814, 0,
   Q'.ofNat 651167276, 0, Q'.ofNat 1120881800, 0, Q'.ofNat 1886562340, 0,
   Q'.ofNat 3108601912, 0, Q'.ofNat 5020134520, 0, Q'.ofNat 7953391822, 0,
   Q'.ofNat 12372545908, 0, Q'.ofNat 18914079960, 0, Q'.ofNat 28434444312, 0,
   Q'.ofNat 42065462436, 0, Q'.ofNat 61275704760, 0, Q'.ofNat 87937157442, 0,
   Q'.ofNat 124392979700, 0, Q'.ofNat 173524137233, 0, Q'.ofNat 238807612424, 0,
   Q'.ofNat 324362548118, 0, Q'.ofNat 434973862100, 0, Q'.ofNat 576089335759, 0,
   Q'.ofNat 753777370096, 0, Q'.ofNat 974643359674, 0, Q'.ofNat 1245691404668, 0,
   Q'.ofNat 1574134602103, 0, Q'.ofNat 1967142707860, 0, Q'.ofNat 2431539591886,
   0, Q'.ofNat 2973443575132, 0, Q'.ofNat 3597875566358, 0,
   Q'.ofNat 4308333230140, 0, Q'.ofNat 5106369855820, 0, Q'.ofNat 5991179540596,
   0, Q'.ofNat 6959239533065, 0, Q'.ofNat 8004009484640, 0,
   Q'.ofNat 9115745994044, 0, Q'.ofNat 10281422407088, 0, Q'.ofNat 11484812714084,
   0, Q'.ofNat 12706710770040, 0, Q'.ofNat 13925337241904, 0,
   Q'.ofNat 15116878919268, 0, Q'.ofNat 16256202262304, 0,
   Q'.ofNat 17317655899896, 0, Q'.ofNat 18275993788656, 0,
   Q'.ofNat 19107306780024, 0, Q'.ofNat 19789990725996, 0,
   Q'.ofNat 20305620330288, 0, Q'.ofNat 20639764894068, 0,
   Q'.ofNat 20782609553292, 0, Q'.ofNat 20729438623191, 0,
   Q'.ofNat 20480852681580, 0, Q'.ofNat 20042806998084, 0,
   Q'.ofNat 19426359939756, 0, Q'.ofNat 18647254684842, 0,
   Q'.ofNat 17725242718296, 0, Q'.ofNat 16683303594690, 0,
   Q'.ofNat 15546685161108, 0, Q'.ofNat 14341938506985, 0,
   Q'.ofNat 13095876440928, 0, Q'.ofNat 11834634416982, 0,
   Q'.ofNat 10582755224964, 0, Q'.ofNat 9362464466433, 0,
   Q'.ofNat 8193041847072, 0, Q'.ofNat 7090432103418, 0, Q'.ofNat 6066979809420,
   0, Q'.ofNat 5131405064223, 0, Q'.ofNat 4288886976108, 0,
   Q'.ofNat 3541346747790, 0, Q'.ofNat 2887790017764, 0, Q'.ofNat 2324782434780,
   0, Q'.ofNat 1846921629924, 0, Q'.ofNat 1447371479736, 0,
   Q'.ofNat 1118336087292, 0, Q'.ofNat 851537300562, 0, Q'.ofNat 638595350388, 0,
   Q'.ofNat 471377601096, 0, Q'.ofNat 342238218264, 0, Q'.ofNat 244215187464, 0,
   Q'.ofNat 171128313720, 0, Q'.ofNat 117641804874, 0, Q'.ofNat 79251955656, 0,
   Q'.ofNat 52256409351, 0, Q'.ofNat 33676179648, 0, Q'.ofNat 21177387294, 0,
   Q'.ofNat 12970161900, 0, Q'.ofNat 7720021455, 0, Q'.ofNat 4453569720, 0,
   Q'.ofNat 2482727910, 0, Q'.ofNat 1332041760, 0, Q'.ofNat 684828945, 0,
   Q'.ofNat 335181420, 0, Q'.ofNat 155104290, 0, Q'.ofNat 67039560, 0,
   Q'.ofNat 26747280, 0, Q'.ofNat 9579780, 0, Q'.ofNat 3001320, 0,
   Q'.ofNat 748440, 0, Q'.ofNat 135135]

set_option maxRecDepth 4000 in
/-- **`nonnegCoeffs P_7`** (`decide`) — extends the verified base to `N = 7`. -/
theorem P7_nonneg : nonnegCoeffs P7 := by decide

set_option maxRecDepth 4000 in
/-- **`P_7(a) ≥ 1`** for `a ≥ 0` — constant-term-`1` floor. -/
theorem P7_ge_one {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval P7 a) 1 :=
  geRat_ceval_ge_one_of_headGeOne (Q'.ofNat 1) _ ha P7_nonneg (by decide)

/-! ## The named residual obligation (the sharp OPEN `Prop`)

The Hankel factorization `det(ĥ_{i+j})_{<N} = (SN N)²·P_N` is established per
order; supplying the *all-`N`* statement that the residual `det/(SN N)²`
remains nonneg-coefficient is exactly `nonnegCoeffs P_N` uniformly.  We name
that hypothesis and package the trivial consumer, so the residual obligation
is a single, precise `Prop`. -/

/-- **The Hankel-residual obligation (named OPEN obligation).**  For order
`N`, the `Type`-level datum is the residual coefficient list `P` together with
(i) the Hankel factorization identity `det(ĥ_{i+j})_{<N}(x) = (SN N)²·P(x)`
(supplied as the `QPoly` `hd` and the pointwise `eval`-identity), and (ii)
`nonnegCoeffs P`.  Supplying this for all `N` is exactly the uniform
`nonnegCoeffs P_N` together with the (per-`N`-mechanical) Hankel factorization.
The genuinely OPEN half is `nonnegCoeffs P` uniformly in `N`. -/
structure HankelResidualNonneg (N : Nat) where
  /-- the order-`N` `ĥ`-Hankel determinant as a `QPoly`. -/
  hd : QPoly.Poly
  /-- the residual `P_N = det/(SN N)²`. -/
  P : QPoly.Poly
  /-- the Hankel factorization `det(ĥ_{i+j})_{<N} = (SN N)²·P_N`. -/
  factor : ∀ x : Q',
    (QPoly.eval hd x).eqv (QPoly.eval (QPoly.pmul (QPoly.pmul (SN N) (SN N)) P) x)
  /-- **the OPEN half**: the residual has nonnegative coefficients. -/
  resNonneg : nonnegCoeffs P

/-- **Consumer.**  Given the residual datum for order `N`, the `ĥ`-Hankel
determinant `det(ĥ_{i+j})_{<N} ≥ 0` at `a ≥ 0`, certified as `(SN N)²·P_N`.
This packages the all-`N` reduction: the only OPEN input is `resNonneg`
(`nonnegCoeffs P_N`), the residual positivity. -/
theorem pn_nonneg_of_hankelPositive (N : Nat) (h : HankelResidualNonneg N)
    {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval h.hd a) 0 :=
  ceval_factor_nonneg h.hd (SN N) h.P ha h.resNonneg h.factor

/-- The order-2 instance of the residual datum (fully discharged: both the
Hankel factorization `hankel_factor_2` and `nonnegCoeffs P_2` are proved). -/
def hankelResidual2 : HankelResidualNonneg 2 where
  hd := hankelDet2
  P := P2
  factor := fun x => hankel_factor_2 x
  resNonneg := P2_nonneg

/-- The order-3 instance of the residual datum (fully discharged). -/
def hankelResidual3 : HankelResidualNonneg 3 where
  hd := hankelDet3
  P := P3
  factor := fun x => hankel_factor_3 x
  resNonneg := P3_nonneg

end YMGap.Continuum.PNPaths

/-! ## OPEN obligation and honest verdict

**Proved here (axiom-clean).**

  * **`hMom_nonneg`** — the uniform-in-`k` nonnegativity of the cleared
    cos-moments `ĥ_k = Σ_r ballot(k,r)(r+1)a^{r(r+2)}`: a genuine `∀ k`
    theorem (the moments are path-positive, ballot weights `≥ 0` by
    construction).  This is the LGV/non-intersecting-path positivity of the
    *moment kernel*, formalized uniformly.
  * **`hankel_factor_2/3`** — the Hankel-determinant factorization
    `det(ĥ_{i+j})_{<N} = (SN N)²·P_N` for `N = 2,3` (`decide`), exhibiting the
    fusion-Gram residual `P_N` as the residual of a Hankel determinant of the
    *path-positive* moments, and `hankelDet2/3_nonneg`.
  * **`P6_nonneg`, `P7_nonneg`** (+ `P6/7_ge_one`) — `nonnegCoeffs P_N` by
    `decide` for `N = 6,7`, extending the verified base from `N = 5`.
  * **`HankelResidualNonneg` / `pn_nonneg_of_hankelPositive`** — the named
    residual obligation and its consumer.

**OPEN — the single remaining mathematical gap (`nonnegCoeffs P_N`, all `N`).**
The LGV / non-intersecting-path route, *even with the path-positive moment
kernel `ĥ_k` formalized here*, does **not** close it:

  * The moments `ĥ_k` are path-positive (proved, `hMom_nonneg`), but the
    *Hankel determinant* `det(ĥ_{i+j}) = (SN N)²·P_N` carries the perfect
    square `(SN N)²`, and extracting `P_N` divides it out.  The
    Lindström–Gessel–Viennot / Karlin–McGregor non-intersecting-Motzkin-path
    model expresses the determinant through the Stieltjes–Rogers J-fraction
    `det = ∏_k λ_k^{N−k}`, but the weights `λ_k = H_{k+1}H_{k−1}/H_k²` are
    **rational, not nonneg-coefficient** — the residual `P_k` reappears in the
    denominator (`λ_k` is a non-polynomial rational function for `k ≥ 2`,
    exact computer algebra).  So the path model has *rational* weights and
    does not exhibit `P_N` as a manifestly-nonneg monomial path family.

  This is the *same* square-content cancellation that obstructs the Favard
  (`FavardRec`) and Dodgson recurrences and the column-polynomial /
  Hankel-on-Jacobi route (`LGVPositivity`): the moment-level positivity is
  genuine and uniform, but it does not survive the division by the square.

  The sharp residual obligation is `HankelResidualNonneg N P_N` for all `N`,
  i.e. that `det(ĥ_{i+j})_{<N} / (SN N)²` has nonnegative coefficients —
  equivalently a Schur-positive / non-intersecting-path model for `P_N`
  *itself* (its coefficients are empirically log-concave and unimodal,
  consistent with one), which was **not** found here and remains the open
  problem.  Coefficient positivity of `P_N` is strictly finer than the value
  positivity `Δ_N ≥ 0` (which is uniform via the positive heat-kernel measure
  and the Andréief identity, per `Favard`/`LGVPositivity`) and is not required
  for the mass-gap input.

This file does not depend on the `MomentPositivity` moment-bridge OPEN — its
results are statements about the polynomials `ĥ_k`, `P_N`, and the Hankel
determinants `det(ĥ_{i+j})`, exactly as `delta3_nonneg` is.
-/

#print axioms YMGap.Continuum.PNPaths.monoNN_nonneg
#print axioms YMGap.Continuum.PNPaths.hMom_nonneg
#print axioms YMGap.Continuum.PNPaths.hMom0_eq
#print axioms YMGap.Continuum.PNPaths.hMom4_eq
#print axioms YMGap.Continuum.PNPaths.hankel_factor_2
#print axioms YMGap.Continuum.PNPaths.hankel_factor_3
#print axioms YMGap.Continuum.PNPaths.hankelDet2_nonneg
#print axioms YMGap.Continuum.PNPaths.hankelDet3_nonneg
#print axioms YMGap.Continuum.PNPaths.P6_nonneg
#print axioms YMGap.Continuum.PNPaths.P7_nonneg
#print axioms YMGap.Continuum.PNPaths.pn_nonneg_of_hankelPositive
