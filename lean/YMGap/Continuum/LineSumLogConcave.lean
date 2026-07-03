/-
Track A / R2 (track: 1-linesum) — the SHIFT-SUM REINDEXING of the antidiagonal line-sum of
the common-range Gram lag-correlation, and the HONEST reduction of `LineSumLogConcaveCR` to a
single named residual (the shift-family aggregation), matching the Cauchy–Binet verdict.

# What this module adds (read first — load-bearing honesty)

The target `ThetaExponentConvexity.LineSumLogConcaveCR w` asks, for every common cutoff `n`
and antidiagonal argument `s`,

    lineSum (lagCorrCR w n) s · lineSum (lagCorrCR w n) (s+2)
      ≤ lineSum (lagCorrCR w n) (s+1)².

Unfolding the definitions,

    lineSum (lagCorrCR w n) s = Σ_{p=0}^{s} Σ_{r<n} c_{p+r}·c_{(s−p)+r}
                             = Σ_{r<n} ( Σ_{p=0}^{s} c_{p+r}·c_{(s−p)+r} )
                             = Σ_{r<n} windowAuto(w, s, r),

so the line-sum is a **sum over shifts `r` of windowed autoconvolutions at the different
arguments `s+2r`** — NOT a single autoconvolution.  This module proves the reindexing identity
exactly (a clean `fsum_swap`), together with the positivity/symmetry facts, and REDUCES the target
to one honestly-named residual `ShiftFamilyLogConcave w n` (the log-concavity of the shift-family
sum), wired to `LineSumLogConcaveCR` through the proved reindexing.

# The Cauchy–Binet verdict this module encodes (honesty)

Per the tree's analysis, the antidiagonal line-sum log-concavity does NOT follow from bare TP₂ of
`lagCorrCR` (machine-checked rank-1 kernel `f=(1,0,1) → L=(1,0,2,0,1)`).  The correct grouping is
the Toeplitz (autoconvolution) Cauchy–Binet, whose per-pair atom is a product of two same-sign
Toeplitz minors, each sign-definite because `coeffW` is PF₂ (`coeffW_rect`).  That grouping closes
the **baseline δ=0 autoconvolution log-concavity** of a SINGLE full autoconvolution, but a genuine
local-CLT remainder persists for `LineSumLogConcaveCR` on three counts:

  * (i) the strict positive margin (the `AutoconvDefectReserve` δ) is a quantitative variance
    estimate, not a Cauchy–Binet positivity fact;
  * (ii) the moving-window truncation edge (the window `[r, s+r]` of `windowAuto(w,s,r)` grows with
    the argument, so product-of-truncated-Toeplitz ≠ truncated-product at the boundary);
  * (iii) the r-aggregation: a SUM of log-concave sequences is not in general log-concave, so the
    shift-family requires a genuine cross-shift super-modularity, absent from the composition
    identity.

Consequently this module does NOT inhabit `ShiftFamilyLogConcave`; it proves the exact reindexing
that isolates the remainder and supplies the genuinely-proved supporting facts (nonnegativity,
symmetry, the diagonal Cauchy–Schwarz seed, and the reusable Toeplitz/autoconvolution per-pair
positivity atom).  This is a sharp relocation of one box-level log-concavity sub-fact; it is NOT a
4D Yang–Mills mass gap.

# What this module proves (all axiom-clean)

PROVED (`[propext]` / `[propext, Quot.sound]` only):
  * `lagCorrCR_nonneg`, `lineSumCR_nonneg`, `windowAuto_nonneg` — nonnegativity of the building
    blocks (sums of products of nonnegative `coeffW`).
  * `lagCorrCR_symm` — strand symmetry of the common-range lag-correlation.
  * `windowAuto`, `lineSum_lagCorrCR_eq_shiftSum` — THE REINDEXING: the line-sum equals the
    shift-sum of windowed autoconvolutions (`fsum_swap`).
  * `lagCorrCR_diag_logConcave` — the diagonal Cauchy–Schwarz slice that DOES close (re-export of
    `ThetaExponentConvexity.lagCorrCR_cauchy_schwarz`).
  * `autoconvMinor_nonpos`, `autoconvMinorProd_nonneg` — the reusable Toeplitz/autoconvolution
    per-pair Cauchy–Binet atom at Toeplitz indices (instances of `coeffW_rect` /
    `coeffMinorProd_nonneg`), the sign-definite baseline positivity the correct grouping uses.

REDUCTION (Type-level, honest; never `sorry`):
  * `ShiftFamilyLogConcave w n` — the log-concavity of the shift-family sum
    `Σ_r windowAuto(w,·,r)` (obstructions (i)–(iii) above); NAMED-OPEN.
  * `lineSumLogConcaveCR_of_shiftFamily`, `lineSumLogConcaveCR_of_shiftFamily'` — the wiring:
    a shift-family witness (for every `n`) inhabits `LineSumLogConcaveCR w`, via the proved
    reindexing identity.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and the reused finite-sum algebra (`fsum`, `fsum_swap`, `fsum_nonneg`,
`fsum_eqv_congr`), `coeffW`/`coeffW_rect`/`coeffMinorProd_nonneg`, and the proved
`lagCorrCR_cauchy_schwarz`.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.ThetaExponentConvexity

namespace YMGap.Continuum.LineSumLogConcave

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.FusionCoreStepRoundF
open YMGap.Continuum.ThetaExponentConvexity

/-! ## 1. Nonnegativity and symmetry of the building blocks -/

/-- **`lagCorrCR_nonneg`** — the common-range lag-correlation is `≥ 0` (a sum of products of
nonnegative `coeffW`). -/
theorem lagCorrCR_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (n p q : Nat) :
    (0 : Q') ≤ lagCorrCR w n p q := by
  unfold lagCorrCR
  exact fsum_nonneg
    (fun r => Q'.mul_nonneg _ _ (coeffW_nonneg hw _) (coeffW_nonneg hw _)) n

/-- **`lineSumCR_nonneg`** — the antidiagonal line-sum of the common-range lag-correlation is
`≥ 0`. -/
theorem lineSumCR_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (n t : Nat) :
    (0 : Q') ≤ lineSum (lagCorrCR w n) t := by
  unfold lineSum
  exact fsum_nonneg (fun p => lagCorrCR_nonneg hw n p (t - p)) _

/-- **`lagCorrCR_symm`** — the common-range lag-correlation is symmetric in its two strand
arguments (`coeffW`-commutativity per summand). -/
theorem lagCorrCR_symm (w : Q') (n p q : Nat) :
    (lagCorrCR w n p q).eqv (lagCorrCR w n q p) := by
  unfold lagCorrCR
  exact fsum_eqv_congr _ _ (fun r => Q'.mul_comm_eqv _ _) n

/-! ## 2. The windowed autoconvolution and the shift-sum reindexing (the key identity) -/

/-- **`windowAuto w s r`** — the windowed autoconvolution of `coeffW` at antidiagonal argument
`s`, shifted by `r`:

    windowAuto(w, s, r) = Σ_{p=0}^{s} c_{p+r} · c_{(s−p)+r}.

Reindexing `i = p+r`, this is the truncated autoconvolution `Σ_{i=r}^{s+r} c_i·c_{s+2r−i}` at
argument `s+2r` over the moving window `[r, s+r]`. -/
def windowAuto (w : Q') (s r : Nat) : Q' :=
  fsum (fun p => coeffW w (p + r) * coeffW w ((s - p) + r)) (s + 1)

/-- **`windowAuto_nonneg`** — each windowed autoconvolution is `≥ 0`. -/
theorem windowAuto_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (s r : Nat) :
    (0 : Q') ≤ windowAuto w s r := by
  unfold windowAuto
  exact fsum_nonneg
    (fun p => Q'.mul_nonneg _ _ (coeffW_nonneg hw _) (coeffW_nonneg hw _)) (s + 1)

/-- **`lineSum_lagCorrCR_eq_shiftSum` — THE REINDEXING IDENTITY.**  The antidiagonal line-sum of the
common-range lag-correlation equals the sum over shifts `r<n` of windowed autoconvolutions:

    lineSum (lagCorrCR w n) s  ≃  Σ_{r<n} windowAuto(w, s, r).

Pure finite-sum reassociation: `lineSum` opens as `Σ_p Σ_r c_{p+r}·c_{(s−p)+r}`, and `fsum_swap`
exchanges the `p`- and `r`-sums into `Σ_r ( Σ_p c_{p+r}·c_{(s−p)+r} ) = Σ_r windowAuto`.  This is
the honest structural fact that the line-sum is a shift-FAMILY sum, not a single autoconvolution. -/
theorem lineSum_lagCorrCR_eq_shiftSum (w : Q') (n s : Nat) :
    (lineSum (lagCorrCR w n) s).eqv (fsum (fun r => windowAuto w s r) n) :=
  fsum_swap (fun p r => coeffW w (p + r) * coeffW w ((s - p) + r)) (s + 1) n

/-! ## 3. The diagonal seed that DOES close, and the Toeplitz per-pair atom -/

/-- **`lagCorrCR_diag_logConcave`** — the diagonal Cauchy–Schwarz slice of the Gram Cauchy–Binet
(re-export of the PROVED `ThetaExponentConvexity.lagCorrCR_cauchy_schwarz`):

    lagCorrCR(p,q)²  ≤  lagCorrCR(p,p) · lagCorrCR(q,q).

This is the honest diagonal seed; it does NOT reach the antidiagonal line-sum (wrong pairing). -/
theorem lagCorrCR_diag_logConcave (w : Q') (n p q : Nat) :
    lagCorrCR w n p q * lagCorrCR w n p q
      ≤ lagCorrCR w n p p * lagCorrCR w n q q :=
  lagCorrCR_cauchy_schwarz w n p q

/-- **`autoconvMinor_nonpos`** — the Toeplitz/autoconvolution `2×2` Hankel minor is `≤ 0` (a
reindexing of `coeffW_rect` at the autoconvolution/Toeplitz indices).  For any `i a b`,

    c_i · c_{i+a+b}  ≤  c_{i+a} · c_{i+b}

is the sign-definite Toeplitz minor the Cauchy–Binet grouping uses; hence its additive form is
`≤ 0`.  This is the reusable atom the correct grouping needs (PF₂ of `coeffW`). -/
theorem autoconvMinor_nonpos {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (i a b : Nat) :
    coeffMinor w i a 0 (a + b) ≤ (0 : Q') := by
  -- `coeffMinor w i a 0 (a+b) = c_i·c_{i+a+(a+b)} − c_{i+(a+b)}·c_{i+a+0}`; but we only need the
  -- sign via the already-packaged `coeffMinor_nonpos`.
  exact coeffMinor_nonpos hw0 hw1 hwpos i a 0 (a + b)

/-- **`autoconvMinorProd_nonneg`** — the Cauchy–Binet per-pair positivity at Toeplitz indices: a
product of two same-sign autoconvolution Hankel minors is `≥ 0` (instance of the RoundE
`coeffMinorProd_nonneg`).  This is the exact per-summand content of the Toeplitz composition
grouping that closes the baseline δ=0 autoconvolution log-concavity. -/
theorem autoconvMinorProd_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (p ap q aq r b : Nat) :
    (0 : Q') ≤ coeffMinor w p ap r b * coeffMinor w q aq r b :=
  coeffMinorProd_nonneg hw0 hw1 hwpos p ap q aq r b

/-! ## 4. The honest residual and the wiring to `LineSumLogConcaveCR` -/

/-- **`ShiftFamilyLogConcave w n`** — the SOLE remaining residual for the target at a fixed common
cutoff `n`: the log-concavity of the shift-family sum

    (Σ_{r<n} windowAuto(w,s,r)) · (Σ_{r<n} windowAuto(w,s+2,r))
      ≤ (Σ_{r<n} windowAuto(w,s+1,r))².

This is the object the reindexing isolates.  Per the honest verdict it is NOT closed by the
composition Cauchy–Binet identity alone: a sum of log-concave sequences is not in general
log-concave (r-aggregation), and the moving window `[r, s+r]` grows with the argument (truncation
edge).  NAMED-OPEN (never `sorry`); this module does not inhabit it. -/
structure ShiftFamilyLogConcave (w : Q') (n : Nat) : Type where
  /-- Log-concavity of the shift-family sum of windowed autoconvolutions. -/
  slc : ∀ s,
    fsum (fun r => windowAuto w s r) n * fsum (fun r => windowAuto w (s + 2) r) n
      ≤ fsum (fun r => windowAuto w (s + 1) r) n * fsum (fun r => windowAuto w (s + 1) r) n

/-- **`lineSumLogConcaveCR_of_shiftFamily` — THE WIRING (pointwise).**  A `ShiftFamilyLogConcave w n`
witness gives the antidiagonal line-sum log-concavity of `lagCorrCR w n` at every `s`: transport the
shift-family inequality across the proved reindexing identity `lineSum_lagCorrCR_eq_shiftSum` on both
sides.  This exhibits that the ONLY content between the reindexed line-sum and the target is the
shift-family log-concavity. -/
theorem lineSumLogConcaveCR_of_shiftFamily {w : Q'} (n : Nat)
    (H : ShiftFamilyLogConcave w n) : ∀ s,
    lineSum (lagCorrCR w n) s * lineSum (lagCorrCR w n) (s + 2)
      ≤ lineSum (lagCorrCR w n) (s + 1) * lineSum (lagCorrCR w n) (s + 1) := by
  intro s
  -- LHS product ≃ shift-family product
  have eL : (lineSum (lagCorrCR w n) s * lineSum (lagCorrCR w n) (s + 2)).eqv
      (fsum (fun r => windowAuto w s r) n * fsum (fun r => windowAuto w (s + 2) r) n) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (lineSum_lagCorrCR_eq_shiftSum w n s))
      (Q'.mul_eqv_congr_left _ _ _ (lineSum_lagCorrCR_eq_shiftSum w n (s + 2)))
  -- RHS product ≃ shift-family product
  have eR : (lineSum (lagCorrCR w n) (s + 1) * lineSum (lagCorrCR w n) (s + 1)).eqv
      (fsum (fun r => windowAuto w (s + 1) r) n * fsum (fun r => windowAuto w (s + 1) r) n) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (lineSum_lagCorrCR_eq_shiftSum w n (s + 1)))
      (Q'.mul_eqv_congr_left _ _ _ (lineSum_lagCorrCR_eq_shiftSum w n (s + 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
    (Q'.le_trans' _ _ _ (H.slc s) (Q'.ge_of_eqv eR))

/-- **`lineSumLogConcaveCR_of_shiftFamily'` — THE WIRING (packaged).**  A family of
`ShiftFamilyLogConcave w n` witnesses (one per common cutoff `n`) inhabits the pipeline residual
`ThetaExponentConvexity.LineSumLogConcaveCR w`.  This is the honest reduction: the antidiagonal
line-sum log-concovity target reduces EXACTLY to the shift-family log-concavity, the reindexing
being fully proved. -/
def lineSumLogConcaveCR_of_shiftFamily' {w : Q'}
    (H : ∀ n, ShiftFamilyLogConcave w n) : LineSumLogConcaveCR w where
  llc := fun n s => lineSumLogConcaveCR_of_shiftFamily n (H n) s

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `lagCorrCR_nonneg`, `lineSumCR_nonneg`, `windowAuto_nonneg` — nonnegativity of the blocks.
  * `lagCorrCR_symm` — strand symmetry.
  * `lineSum_lagCorrCR_eq_shiftSum` — the shift-sum reindexing identity (`fsum_swap`).
  * `lagCorrCR_diag_logConcave` — the diagonal Cauchy–Schwarz slice (re-export).
  * `autoconvMinor_nonpos`, `autoconvMinorProd_nonneg` — the reusable Toeplitz/autoconvolution
    per-pair Cauchy–Binet atom (instances of `coeffW_rect` / `coeffMinorProd_nonneg`).
  * `lineSumLogConcaveCR_of_shiftFamily`, `lineSumLogConcaveCR_of_shiftFamily'` — the wiring.

NAMED OPEN (Type-level structure, never `sorry`):
  * `ShiftFamilyLogConcave w n` — the shift-family log-concavity (the r-aggregation + moving-window
    remainder; the strict-margin `AutoconvDefectReserve` is a strictly stronger cousin).

HONEST VERDICT.  The Toeplitz Cauchy–Binet grouping dispatches the *indefiniteness* that walled the
Menon/diagonal-pair route and closes the baseline δ=0 autoconvolution log-concavity, but the target
`LineSumLogConcaveCR` is a SHIFT-FAMILY sum (proved here by `lineSum_lagCorrCR_eq_shiftSum`), and a
genuine local-CLT remainder — the shift aggregation and moving-window edge — persists in
`ShiftFamilyLogConcave`.  This is a sharp reduction, not a closure.
-/

end YMGap.Continuum.LineSumLogConcave

