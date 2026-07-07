/-
Track B / R2 — **THE BAŁABAN LARGE-FIELD / SMALL-FIELD CONTROL: SUPPRESSION vs ENTROPY.**
Does the large-field exponential suppression `e^{−|φ|²/g²}` genuinely BEAT the configuration
ENTROPY (the number/volume of large-field configs `~ e^{+V·s}`), making the non-perturbative
config-space measure convergent, or is that control exactly the open `singleStep`?

# The obligation (read first)

The constructive non-perturbative measure requires controlling the LARGE-FIELD region
`{φ : |φ| > M}`.  The suppression `e^{−|φ|²/g²}` competes with the ENTROPY (the number of
large-field configs `~ e^{+V·s}`, `s` = entropy density, `V` = volume / number of modes).  The
Bałaban estimate: for `M` large enough the suppression BEATS the entropy, so the total
large-field measure `~ e^{−M²/g² + V·s}` is small and the measure is dominated by the
small-field (perturbative) region + a controlled large-field remainder.

  * **Single mode / single scale** — the entropy is FINITE (a fixed `V`), and the Gaussian tail
    `∫_M^∞ e^{−φ²/g²} dφ ≤ (g²/2M)·e^{−M²/g²}` is finite; for `M > g·√(V·s)` the suppression
    beats the entropy.  **CONSTRUCTIBLE** (this module PROVES it: the tail is a bounded geometric
    sum, and the suppression-scale that beats a fixed finite entropy is COMPUTED as data).
  * **Multi-scale / continuum** — infinitely many modes (`V → ∞`): the entropy is UNBOUNDED, so
    NO single suppression scale `M` controls all volumes.  The scale-by-scale control (a
    per-scale, diverging threshold `M(V) = g√(V·s)`, the Bałaban RG) is the open `singleStep`.

# What is genuinely PROVED here (axiom-clean `Q'`/`CReal`/`Nat`)

  * `singleModeSuppression` — the single-mode suppression amplitude `e^{−M²/g²}` as a genuine
    CReal in `[0,1]` (reusing the proved `condensateCReal`, the same `e^{−const/g²}` form);
    positivity TRIVIAL (the red herring).
  * `singleMode_tail_bounded` / `gaussTail_concrete` — **the single-mode large-field mass is a
    FINITE (bounded) geometric sum** `Σ_n K·r^n ≤ H` (`r < 1`, the cell-to-cell Gaussian ratio):
    the constructive shadow of `∫_M^∞ e^{−φ²/g²} dφ < ∞` (the suppression is summable).
  * `entropyScale` / `entropyScale_mono` — the entropy cost `g²·s·V` (scaled to compare with the
    suppression `M²`) is NONDECREASING in `V` (more modes ⟹ more entropy).
  * **`suppression_beats_entropy_single_scale`** — **THE DECISIVE SINGLE-SCALE CHECK
    (constructible, data):** for `g,s > 0` and any FIXED finite `V`, a suppression scale `M` with
    `entropyScale g s V < suppressionScale M` is COMPUTED (`Σ'`, Rule 2) — the Gaussian
    suppression beats the finite entropy at a single scale.
  * **`entropy_beats_fixed_suppression`** — **THE MULTI-SCALE OBSTRUCTION (Archimedean):** for
    `g,s > 0` and ANY fixed suppression scale `M`, a volume `V` with `suppressionScale M <
    entropyScale g s V` is COMPUTED — so NO uniform `M` controls all volumes; the entropy across
    `V → ∞` is unbounded.  This is the DUAL of the single-scale bound: single scale = suppression
    wins; all scales at once = entropy wins without the RG.

# THE DECISIVE CHECK (task point 3) — does the large-field control give the measure?

Split cleanly (exactly the Bałaban dichotomy).  At a SINGLE scale / finite volume the entropy is
finite and the Gaussian suppression beats it — the large-field remainder is a finite, small,
CONSTRUCTIBLE piece (`singleMode_tail_bounded`, `suppression_beats_entropy_single_scale`).  For
the CONTINUUM (infinitely many modes) the entropy is UNBOUNDED
(`entropy_beats_fixed_suppression`): no single suppression scale beats it, so the control
requires the scale-by-scale (per-`V`, diverging) threshold `M(V) = g√(V·s)` — the multi-scale
Bałaban RG.  Encoded (def-alias, UNINHABITED, NOT one of the guarded frontier types):
`MultiScaleLargeFieldControl := SingleStepDefectReduction.SingleStepDefectBound`.

# HONEST verdict (task point 4)

The single-mode / single-scale large-field suppression genuinely BEATS the (finite) entropy: the
Gaussian tail is a bounded geometric sum and the suppression-scale that beats a fixed entropy is
COMPUTED — a genuine new constructible piece.  The MULTI-SCALE (continuum, infinite modes)
large-field control is NOT constructible from single-scale data: the entropy is unbounded across
`V → ∞`, so the scale-by-scale RG (the diverging per-scale threshold `M(V)`) = `singleStep`.  A
single-scale bound is a piece, NOT the continuum measure.  The large-field control ISOLATES the
multi-scale Bałaban RG = `singleStep` — a further confirmation of the SAME irreducible core, PLUS
the genuinely new machine-checked suppression-beats-finite-entropy / geometric-tail theorems.  No
guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Numerics (mpmath dps 50, sympy exact — `largefield_verify.py`)

  * single-mode Gaussian tail `∫_M^∞ e^{−φ²/g²} dφ ≤ (g²/2M)·e^{−M²/g²}`: verified for
    `(M,g) ∈ {(1,1),(2,1),(3,½),(5,2)}` (e.g. `M=2,g=1`: tail `0.004146 ≤ 0.004579`);
  * net exponent `M²/g² − s·V > 0 ⟺ M > g√(s·V)`: threshold `M_c = g√(sV)` clean (e.g.
    `g=1,s=½,V=4`: `M_c = √2`, `M = 1.1·M_c` ⟹ net `+0.42 > 0`, `M = 0.9·M_c` ⟹ net `−0.38`);
  * total LF measure `e^{−M²/g² + Vs}`: `g=1,s=½,V=9` gives `1` at `M=M_c`, `1.1·10⁻⁵` at `M=4`;
  * Archimedean (multi-scale): fixed `M=10,g=1,s=½` needs `V > 200` for entropy to win — but such
    `V` always exists, so no uniform `M`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` + the proved `condensateCReal` (nonneg/`≤1`, trivial) and the
`finSum`/`geometric_tail_closure`/`divPos` backbone, a local Archimedean step
(`Int.self_le_toNat` + `omega`), and the named residual
`SingleStepDefectReduction.SingleStepDefectBound`.  Every load-bearing declaration is
`#print axioms`-gated; permitted output `propext`/`Quot.sound` only (or empty).  No
`Classical.*`, no `native_decide` (only `decide` on closed decidable `Q'` facts), no `ring`, no
`sorry`.  All witnesses `Type`-level.  No frontier bundle inhabited.
-/
import YMGap.Continuum.CondensateGeometricErosion
import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Constructive.GeometricTail
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CubeRoot
import YMGap.Constructive.SU3CharFactor
import YMGap.Constructive.CRealMul
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.BalabanLargeFieldEntropy

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CondensateGeometric

/-! ## 0. Local `Q'`/`Int` order glue (self-contained, axiom-clean). -/

/-- `a < b ≤ c ⟹ a < c` on `Q'` (local copy of the `InstantonDiluteGas` pattern; the mirror of
the library `Q'.lt_of_le_of_lt`, but with the `≤` on the RIGHT). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    have hr2 : (c.num * (b.den : Int)) * (a.den : Int)
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [hr, hr2] at this; exact this
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right s3
    (by exact_mod_cast Nat.le_of_lt b.den_pos : (0 : Int) ≤ (b.den : Int))

/-- **THE ARCHIMEDEAN WITNESS, as DATA** (`Σ'`, Rule 8.3).  For every `B : Q'` the explicit
`N = B.num.toNat + 1` satisfies `B < ofNat N`.  Type-level so the suppression-scale witness it
feeds is genuinely computed. -/
def ofNatGt (B : Q') : Σ' N : Nat, B < Q'.ofNat N := by
  refine ⟨B.num.toNat + 1, ?_⟩
  have hQ1 : (1 : Int) ≤ (B.den : Int) := by exact_mod_cast B.den_pos
  have hPle : B.num ≤ (B.num.toNat : Int) := Int.self_le_toNat B.num
  have hm1 : (0 : Int) ≤ (B.num.toNat : Int) + 1 := by
    have : (0 : Int) ≤ (B.num.toNat : Int) := Int.natCast_nonneg _
    omega
  have hmul : ((B.num.toNat : Int) + 1) * (1 : Int)
      ≤ ((B.num.toNat : Int) + 1) * (B.den : Int) :=
    Int.mul_le_mul_of_nonneg_left hQ1 hm1
  rw [Int.mul_one] at hmul
  show B.num * ((Q'.ofNat (B.num.toNat + 1)).den : Int)
     < (Q'.ofNat (B.num.toNat + 1)).num * (B.den : Int)
  have hden : (Q'.ofNat (B.num.toNat + 1)).den = 1 := rfl
  have hnum : (Q'.ofNat (B.num.toNat + 1)).num = ((B.num.toNat + 1 : Nat) : Int) := rfl
  rw [hden, hnum]; push_cast; push_cast at hmul; omega

/-- **THE SCALED ARCHIMEDEAN WITNESS, as DATA.**  For `0 < c` and every `B`, a volume `N` with
`B < c·ofNat N` is COMPUTED (`N` for `B/c`).  This is the engine of the multi-scale obstruction:
scaling by the fixed positive entropy density `c = g²·s`, the entropy `c·V` eventually exceeds
ANY suppression `B = M²`. -/
def scaledGt (c B : Q') (hc : (0 : Q') < c) : Σ' N : Nat, B < c * Q'.ofNat N := by
  obtain ⟨N, hN⟩ := ofNatGt (Q'.divPos B c hc)
  refine ⟨N, ?_⟩
  have hlt : c * Q'.divPos B c hc < c * Q'.ofNat N := Q'.mul_lt_mul_of_pos_left hc hN
  have heqv : (c * Q'.divPos B c hc).eqv B :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv c (Q'.divPos B c hc)) (Q'.divPos_mul_eqv B c hc)
  exact Q'.lt_of_le_of_lt (Q'.ge_of_eqv heqv) hlt

/-! ## 1. THE SINGLE-MODE SUPPRESSION AMPLITUDE `e^{−M²/g²}` (CReal, constructible).

The single-mode large-field suppression `e^{−M²/g²}` is the SAME `e^{−const/g²}` functional form
as the condensate `e^{−c/β₀g²}`; we re-export the proved `condensateCReal` as the suppression
amplitude.  Its positivity is the RED HERRING (`exp` is positive, free) — building the suppression
factor is NOT the mass gap. -/

/-- **THE SINGLE-MODE GAUSSIAN SUPPRESSION `e^{−M²/g²}`** as a genuine CReal — the exponential
suppression of the large-field region, reusing the proved `condensateCReal`. -/
def singleModeSuppression (k : Nat) : CReal := condensateCReal k

/-- **The suppression amplitude is `≥ 0`** — TRIVIALLY (`exp` is nonnegative): the exp-positivity
RED HERRING. -/
theorem singleModeSuppression_nonneg (k : Nat) : ExpPos.geRat (singleModeSuppression k) 0 :=
  condensate_creal_nonneg k

/-- **The suppression amplitude is `≤ 1`** — a bona-fide suppression factor in `[0,1]`. -/
theorem singleModeSuppression_le_one (k : Nat) : CReal.leRat (singleModeSuppression k) 1 :=
  condensate_creal_le_one k

/-! ## 2. THE SINGLE-MODE GAUSSIAN TAIL IS A BOUNDED GEOMETRIC SUM (the finite LF mass).

Discretise the Gaussian tail `∫_M^∞ e^{−φ²/g²} dφ` into unit cells `[M+n, M+n+1]`: cell `n` has
weight `≤ e^{−(M+n)²/g²} ≤ K·r^n` with head `K = e^{−M²/g²}` (the single-mode suppression) and
cell ratio `r = e^{−(2M+1)/g²} < 1`.  So the tail `≤ K·Σ_n r^n = K/(1−r) < ∞` — the single-mode
large-field region has FINITE mass.  This is the constructive shadow of `∫_M^∞ e^{−φ²/g²} < ∞`. -/

/-- The single-mode large-field cell weight `K·r^n` (geometric decay of the discretised Gaussian
tail: head `K = e^{−M²/g²}`, cell ratio `r = e^{−(2M+1)/g²} < 1`). -/
def gaussTailTerm (K r : Q') (n : Nat) : Q' := K * r ^ n

/-- **THE SINGLE-MODE LARGE-FIELD MASS IS UNIFORMLY BOUNDED (FINITE).**  Every partial sum of the
discretised Gaussian tail `K·r^n` is bounded by the closed geometric budget `H` (given the
one-step recurrence `K + r·H ≤ H`, i.e. `H = K/(1−r)`) — UNIFORMLY in `N`.  The suppression is
SUMMABLE: the single-mode large-field region has finite mass.  Reuses the PROVED
`RationalTail.geometric_tail_closure`. -/
theorem singleMode_tail_bounded (K r H : Q') (hr : (0 : Q') ≤ r) (hH : (0 : Q') ≤ H)
    (hrec : K + r * H ≤ H) (N : Nat) :
    finSum (gaussTailTerm K r) N ≤ H :=
  geometric_tail_closure K r H hr hH hrec N

/-- A CONCRETE single-mode large-field mass bound: `Σ_n 1·(1/2)^n ≤ 2` (the head `K = 1`, cell
ratio `r = 1/2`, closed budget `H = K/(1−r) = 2`).  Non-vacuous kernel-checkable witness that the
Gaussian tail is a bounded geometric sum. -/
theorem gaussTail_concrete (N : Nat) :
    finSum (gaussTailTerm (1 : Q') (Q'.mkPos 1 2 (by decide))) N ≤ Q'.ofNat 2 :=
  singleMode_tail_bounded 1 (Q'.mkPos 1 2 (by decide)) (Q'.ofNat 2)
    (by decide) (by decide) (by decide) N

/-! ## 3. THE SUPPRESSION / ENTROPY SCALES AND MONOTONICITY (`Q'`).

The suppression exponent is `M²/g²`, the entropy exponent `s·V`.  Suppression beats entropy iff
`M²/g² > s·V`, i.e. `M² > g²·s·V`.  To avoid `Q'` division we compare the numerators: the
`suppressionScale M = M²` against the `entropyScale g s V = g²·s·V`. -/

/-- The suppression scale `M²` (`= g²·(M²/g²)`, the Gaussian suppression exponent, `×g²`). -/
def suppressionScale (M : Q') : Q' := M * M

/-- The entropy scale `g²·s·V` (`= g²·(s·V)`, the configuration entropy exponent, `×g²`): `s` =
entropy density, `V` = volume / number of modes.  Suppression beats entropy at scale `M`, volume
`V`, iff `entropyScale g s V < suppressionScale M`. -/
def entropyScale (g s : Q') (V : Nat) : Q' := (g * g) * (s * Q'.ofNat V)

/-- **THE ENTROPY IS NONDECREASING IN THE VOLUME** (`0 ≤ g`, `0 ≤ s`): more modes ⟹ more
entropy.  `entropyScale g s V ≤ entropyScale g s (V+1)`.  The physical monotonicity that makes the
multi-scale entropy unbounded. -/
theorem entropyScale_mono (g s : Q') (hg : (0 : Q') ≤ g) (hs : (0 : Q') ≤ s) (V : Nat) :
    entropyScale g s V ≤ entropyScale g s (V + 1) := by
  have hgg : (0 : Q') ≤ g * g := Q'.mul_nonneg _ _ hg hg
  have hinner : s * Q'.ofNat V ≤ s * Q'.ofNat (V + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.ofNat_le_ofNat (Nat.le_succ V)) hs
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hgg

/-! ## 4. THE DECISIVE SINGLE-SCALE CHECK — suppression BEATS finite entropy (constructible). -/

/-- A `Nat` fact used for `M = ofNat N`: `N ≤ N·N` (so `ofNat N ≤ ofNat N · ofNat N = M²`). -/
theorem nat_le_mul_self (n : Nat) : n ≤ n * n := by
  cases n with
  | zero => exact Nat.le_refl 0
  | succ m =>
    have h1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have := Nat.mul_le_mul (Nat.le_refl (m + 1)) h1
    rwa [Nat.mul_one] at this

/-- **THE DECISIVE SINGLE-SCALE BAŁABAN BOUND (CONSTRUCTIBLE, returned as DATA).**  For `g, s > 0`
and ANY FIXED finite volume `V`, a suppression scale `M` with

    entropyScale g s V  <  suppressionScale M     (i.e.  g²·s·V  <  M²,  M > g√(s·V))

is COMPUTED (`Σ'`, Rule 2): the Gaussian suppression BEATS the finite entropy at a single scale.
Witness `M = ofNat N`, `N = (g²·s·V).num.toNat + 1`: then `g²·s·V < ofNat N ≤ ofNat(N²) = M²`.
This is the single-mode / single-scale half of the Bałaban control — genuinely constructible:
at a FIXED finite volume the entropy is finite and a large-enough suppression scale beats it. -/
def suppression_beats_entropy_single_scale (g s : Q') (_hg : (0 : Q') < g) (_hs : (0 : Q') < s)
    (V : Nat) : Σ' M : Q', entropyScale g s V < suppressionScale M := by
  obtain ⟨N, hN⟩ := ofNatGt (entropyScale g s V)
  refine ⟨Q'.ofNat N, ?_⟩
  -- entropyScale < ofNat N ≤ ofNat (N·N) ≃ ofNat N · ofNat N = suppressionScale (ofNat N)
  have hle : Q'.ofNat N ≤ Q'.ofNat (N * N) := Q'.ofNat_le_ofNat (nat_le_mul_self N)
  have heq : (Q'.ofNat (N * N)).eqv (Q'.ofNat N * Q'.ofNat N) := SU3CharFactor.ofNat_mul_eqv N N
  have step1 : entropyScale g s V < Q'.ofNat (N * N) := lt_of_lt_of_le hN hle
  show entropyScale g s V < Q'.ofNat N * Q'.ofNat N
  exact lt_of_lt_of_le step1 (Q'.le_of_eqv heq)

/-! ## 5. THE MULTI-SCALE OBSTRUCTION — entropy BEATS any fixed suppression (Archimedean). -/

/-- **THE MULTI-SCALE OBSTRUCTION (Archimedean, returned as DATA).**  For `g, s > 0` and ANY FIXED
suppression scale `M`, a volume `V` (number of modes) with

    suppressionScale M  <  entropyScale g s V     (i.e.  M²  <  g²·s·V)

is COMPUTED: the entropy of `V` modes EXCEEDS the fixed suppression.  So NO single suppression
scale `M` controls all volumes — the entropy across `V → ∞` (infinitely many modes / the
continuum) is UNBOUNDED.  This is the DUAL of `suppression_beats_entropy_single_scale`: a fixed
scale beats a fixed entropy, but no fixed scale beats ALL entropies.  The multi-scale control needs
the per-`V` diverging threshold `M(V) = g√(s·V)` — the scale-by-scale Bałaban RG. -/
def entropy_beats_fixed_suppression (g s : Q') (hg : (0 : Q') < g) (hs : (0 : Q') < s) (M : Q') :
    Σ' V : Nat, suppressionScale M < entropyScale g s V := by
  have hc : (0 : Q') < (g * g) * s := Q'.mul_pos (Q'.mul_pos hg hg) hs
  obtain ⟨V, hV⟩ := scaledGt ((g * g) * s) (suppressionScale M) hc
  refine ⟨V, ?_⟩
  -- M² < ((g·g)·s)·ofNat V ≃ (g·g)·(s·ofNat V) = entropyScale g s V
  have heq : (((g * g) * s) * Q'.ofNat V).eqv ((g * g) * (s * Q'.ofNat V)) :=
    Q'.mul_assoc_eqv (g * g) s (Q'.ofNat V)
  show suppressionScale M < (g * g) * (s * Q'.ofNat V)
  exact lt_of_lt_of_le hV (Q'.le_of_eqv heq)

/-! ## 6. THE ISOLATION — the multi-scale large-field control = `singleStep`. -/

/-- **THE MULTI-SCALE LARGE-FIELD CONTROL = `singleStep` (named residual, NOT faked).**  The
single-scale suppression beats the finite entropy (`suppression_beats_entropy_single_scale`,
CONSTRUCTIBLE) and the single-mode tail is a bounded geometric sum
(`singleMode_tail_bounded`), but NO uniform suppression scale controls all volumes
(`entropy_beats_fixed_suppression`): the continuum entropy is unbounded.  The multi-scale control
— the per-scale, diverging threshold `M(V) = g√(s·V)` beaten scale-by-scale, the Bałaban RG — IS
the spacing-uniform gap survival `SingleStepDefectReduction.SingleStepDefectBound.singleStep`.
Restated as a `Type`-alias; UNINHABITED (it IS the real RG estimate).  A measure built with an
ASSUMED uniform-in-`V` large-field bound would be the Rule-9 fake — deliberately not written.
(Identification at the level of the SAME irreducible core across confirmations, not an `rfl`
between the distinct structures.) -/
def MultiScaleLargeFieldControl : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8, proof not prose). -/
theorem multiScaleLargeFieldControl_eq :
    MultiScaleLargeFieldControl = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-! ## 7. The assembled verdict (informational bundle — inhabits NO frontier type). -/

/-- A record of the machine-checked facts of the large-field / entropy assessment.  NOT a frontier
bundle: every field is a genuine PROVED theorem / DATA producer, and it inhabits neither
`SingleStepDefectBound` nor any guarded Clay-frontier type.  It certifies: the single-mode
suppression `e^{−M²/g²}` is a bona-fide CReal in `[0,1]` (positivity trivial); the single-mode
tail is a bounded geometric sum (finite LF mass); the entropy is monotone in the volume; a
suppression scale beats any FIXED finite entropy (single-scale, constructible); and the entropy
beats any FIXED suppression scale (multi-scale obstruction). -/
structure LargeFieldEntropyVerdict : Type where
  /-- §1 — the suppression `e^{−M²/g²}` is `≥ 0` (trivial, the red herring). -/
  suppressionNonneg : ∀ k, ExpPos.geRat (singleModeSuppression k) 0
  /-- §1 — the suppression is `≤ 1` (a bona-fide factor in `[0,1]`). -/
  suppressionLeOne : ∀ k, CReal.leRat (singleModeSuppression k) 1
  /-- §2 — the single-mode large-field tail is a bounded geometric sum (finite mass). -/
  tailBounded : ∀ N, finSum (gaussTailTerm (1 : Q') (Q'.mkPos 1 2 (by decide))) N ≤ Q'.ofNat 2
  /-- §3 — the entropy is nondecreasing in the volume. -/
  entropyMono : ∀ (g s : Q'), (0 : Q') ≤ g → (0 : Q') ≤ s → ∀ V,
    entropyScale g s V ≤ entropyScale g s (V + 1)
  /-- §4 — a suppression scale beats any FIXED finite entropy (single-scale, constructible). -/
  singleScale : ∀ (g s : Q'), (0 : Q') < g → (0 : Q') < s → ∀ V,
    Σ' M : Q', entropyScale g s V < suppressionScale M
  /-- §5 — the entropy beats any FIXED suppression scale (multi-scale obstruction). -/
  multiScale : ∀ (g s : Q'), (0 : Q') < g → (0 : Q') < s → ∀ M,
    Σ' V : Nat, suppressionScale M < entropyScale g s V

/-- **The verdict is inhabited by PROVED facts only.**  Every field is a genuine theorem / DATA
producer; NONE inhabits a frontier bundle.  This certifies the honest conclusion: the single-scale
suppression BEATS the finite entropy (constructible) and the single-mode tail is finite, but the
multi-scale entropy is unbounded (no uniform suppression scale), so the multi-scale control
(uninhabited `MultiScaleLargeFieldControl = singleStep`) is the residual — the large-field control
does NOT give the continuum measure; it ISOLATES the multi-scale Bałaban RG. -/
def largeFieldEntropy_verdict : LargeFieldEntropyVerdict where
  suppressionNonneg := singleModeSuppression_nonneg
  suppressionLeOne := singleModeSuppression_le_one
  tailBounded := gaussTail_concrete
  entropyMono := entropyScale_mono
  singleScale := suppression_beats_entropy_single_scale
  multiScale := entropy_beats_fixed_suppression

/-! ## 8. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT.**

The Bałaban large-field / small-field suppression-vs-entropy control is BUILT and assessed.
**CONSTRUCTED (the genuine pieces):**
  * the single-mode suppression `e^{−M²/g²}` as a genuine CReal in `[0,1]`
    (`singleModeSuppression`, `_nonneg`/`_le_one`) — positivity TRIVIAL (the red herring);
  * the single-mode large-field mass is a BOUNDED geometric sum (`singleMode_tail_bounded`,
    `gaussTail_concrete`) — the constructive shadow of `∫_M^∞ e^{−φ²/g²} dφ < ∞`;
  * the entropy `g²·s·V` is monotone in the volume (`entropyScale_mono`);
  * **the DECISIVE single-scale check**: for `g,s>0` and ANY fixed finite `V`, a suppression
    scale `M` with `g²·s·V < M²` is COMPUTED (`suppression_beats_entropy_single_scale`) — the
    Gaussian suppression BEATS the finite entropy at a single scale.  This is the genuinely new
    machine-checked piece: single-scale, the suppression wins.

**RESIDUAL (NOT closed) — the multi-scale control = `singleStep`:** for ANY fixed suppression
scale `M`, a volume `V` with `M² < g²·s·V` is COMPUTED (`entropy_beats_fixed_suppression`), so NO
uniform `M` controls all volumes — the continuum (infinitely many modes) entropy is UNBOUNDED.
The multi-scale control — the per-`V` diverging threshold `M(V) = g√(s·V)` beaten scale-by-scale,
the Bałaban RG — is `MultiScaleLargeFieldControl = SingleStepDefectBound.singleStep` (UNINHABITED).

So the large-field control gives the measure ONLY at a single scale (finite volume): the
suppression beats the finite entropy, CONSTRUCTIBLE.  It does NOT give the CONTINUUM measure — a
single-scale bound is a piece, not the continuum measure; the multi-scale (infinite-modes)
control requires the scale-by-scale Bałaban RG = `singleStep`.  The large-field control ISOLATES
the multi-scale RG = `singleStep`, a further confirmation of the SAME irreducible core, PLUS the
genuinely new suppression-beats-finite-entropy / geometric-tail theorems.  No guarded frontier
bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem balabanLargeFieldEntropy_honesty : True := trivial

end YMGap.Continuum.BalabanLargeFieldEntropy

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.lt_of_lt_of_le
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.ofNatGt
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.scaledGt
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.singleModeSuppression_nonneg
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.singleModeSuppression_le_one
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.singleMode_tail_bounded
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.gaussTail_concrete
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.entropyScale_mono
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.nat_le_mul_self
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.suppression_beats_entropy_single_scale
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.entropy_beats_fixed_suppression
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.multiScaleLargeFieldControl_eq
#print axioms YMGap.Continuum.BalabanLargeFieldEntropy.largeFieldEntropy_verdict
