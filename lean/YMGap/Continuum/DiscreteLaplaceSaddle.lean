/-
Track 11.7-fusion / R2 — DISCRETE-LAPLACE / STEEPEST-DESCENT cumulant form of the
fusion local-CLT residual.

# What this module does (read first)

The δ-loop reduced the 4D Migdal–Kadanoff bond-moving obstruction to ONE named
residual, re-expressed by `FusionKernelStatement.SaddleLogForm` in log / saddle form:

    |log(fusionEig s) + A·C₂(s)|  ≤  eta·C₂(s)²,     C₂(s) = c4 s = s(s+2).

This ROUTE-3 tranche re-views THAT SAME estimate as an explicit two-cumulant
(steepest-descent) decomposition `log K = −A·C₂ + R`, where the leading term `−A·C₂`
is the cumulant-1 saddle exponent (a parabola of curvature `−2A`, PROVED here from
`Δ²C₄ = 2`) and `R` is the cumulant-2 (`C₂²`) remainder.  It then:

  * packages the remainder as `CumulantSaddleForm`, PROVED *bijective* with
    `SaddleLogForm` (`toSaddleLogForm` / `ofSaddleLogForm` — pure `Type`-level
    repackaging, field-for-field);
  * isolates the `C₂²` remainder as a single named residual `EtaRemainderResidual`
    (field-for-field the same `estimate`) and threads it into the saddle form
    (`cumulantSaddle_of_residual`, `saddleLogForm_of_residual`);
  * re-exports the two genuine cumulant identities (`mu_eq`'s cumulant-1 and
    `dsq_moment_eq`'s cumulant-2 variance) and proves the leading-exponent curvature
    fact `Δ²(A·C₂) = 2A` (`leadingExponent_curvature`), the discrete steepest-descent
    content.

# Honest verdict (Rule 5)

This module closes NOTHING new.  Its value-add is a cumulant *factorization* of the
already-named-open `SaddleLogForm`: leading term PROVED, `C₂²` remainder NAMED-OPEN.
`EtaRemainderResidual` for the genuine 4D exponent `p ≥ 2` is NOT inhabited and NOT
faked — it is field-for-field the existing named-open `SaddleLogForm.estimate`, and
its content is exactly the same discrete SU(2) fusion local-CLT curvature wall
(`MeanComplementCovariance.DShiftCovResidual` / `XMeanSecondDiffProgress`).  The log
form is uninhabited even at `p = 1` (the `s > N` tail vanishes and `log 0` is out of
range) — the inhabited `p = 1` object lives at the `Q'`-level wiring carrier
`FusionKernelStatement.SaddleLocalCLT`, not at the log form.  NOT a 4D Yang–Mills
mass gap.
-/
import YMGap.Continuum.FusionKernelStatement
import YMGap.Continuum.FusionMarginMonotone
import YMGap.Continuum.MeanComplementCovariance
import YMGap.Continuum.MeanExpConvexProgress

namespace YMGap.Continuum.DiscreteLaplaceSaddle

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.MeanComplementCovariance

/-! ## 1. The cumulant/saddle residual (STATEMENT layer, `CReal`)

(The cancellation-free `Q'`-ring closer `ring_qeqv` is inherited from the imported
`MeanExpConvexProgress`.) -/

/-- **`logResidual`** — the cumulant remainder `R(s) := log(fusionEig s) + A·C₂(s)`,
so the saddle form reads `log K = −A·C₂ + R`.  Definitionally the inner term of
`SaddleLogForm.estimate`. -/
def logResidual (N : Nat) (w : Q') (p : Nat)
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0)
    (A : Q')
    (red : (s : Nat) → CRealLogRangeReduction (CReal.ofQ' (fusionEig N w p s (h0' s))))
    (s : Nat) : CReal :=
  CReal.add
    (CReal.log (CReal.ofQ' (fusionEig N w p s (h0' s))) (red s))
    (CReal.ofQ' (A * Q'.ofNat (c4 s)))

/-- **`CumulantSaddleForm`** — the steepest-descent view of `SaddleLogForm`: leading
cumulant-1 exponent `A`, cumulant-2 remainder modulus `eta` (DATA), and the `C₂²`
remainder bound `|R(s)| ≤ eta·C₂(s)²`.  Field-for-field the same open surface as
`SaddleLogForm`; NAMED-OPEN for the genuine 4D exponent `p ≥ 2`. -/
structure CumulantSaddleForm (N : Nat) (w : Q') (p : Nat)
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  /-- cumulant-1 leading exponent `A_p` (expected `−log w`). -/
  A : Q'
  /-- cumulant-2 remainder modulus `η_p` (DATA). -/
  eta : Q'
  /-- range-reduction plumbing so `CReal.log` is defined on each eigenvalue. -/
  red : (s : Nat) → CRealLogRangeReduction (CReal.ofQ' (fusionEig N w p s (h0' s)))
  /-- **THE `C₂²` REMAINDER BOUND**: `|log(fusionEig s) + A·C₂(s)| ≤ eta·C₂(s)²`. -/
  remainder : ∀ s,
    CReal.leEv (CReal.abs (logResidual N w p h0' A red s))
      (CReal.ofQ' (eta * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))))

/-! ## 2. EQUIVALENCE with the existing statement layer (PROVED, both directions) -/

/-- **`toSaddleLogForm`** — the cumulant remainder IS the saddle estimate (`logResidual`
unfolds definitionally to the `estimate` inner term). -/
def toSaddleLogForm {N : Nat} {w : Q'} {p : Nat}
    {h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (f : CumulantSaddleForm N w p h0') : SaddleLogForm N w p h0' where
  A := f.A
  eta := f.eta
  red := f.red
  estimate := f.remainder

/-- **`ofSaddleLogForm`** — the reverse repackaging (`SaddleLogForm` ⟶ cumulant form). -/
def ofSaddleLogForm {N : Nat} {w : Q'} {p : Nat}
    {h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (g : SaddleLogForm N w p h0') : CumulantSaddleForm N w p h0' where
  A := g.A
  eta := g.eta
  red := g.red
  remainder := g.estimate

/-! ## 3. The `C₂²` remainder as the single named-open residual -/

/-- **`EtaRemainderResidual`** — THE SINGLE NAMED-OPEN RESIDUAL of ROUTE 3.  The
vacuum-rebased leading exponent `A = A_p = p·⟨single-step⟩` (`w_eff = exp(−A)`) and the
cumulant-2 remainder modulus `eta = η_p` (DATA; pilot worst `η = 0.00246` at `w=1/2,p=2`,
34× under the `1/12` budget) with the open content the `C₂²`-controlled remainder bound
`|log(fusionEig s) + A·C₂(s)| ≤ η_p·C₂(s)²`, uniformly in `s`.  Field-for-field the
existing named-open `SaddleLogForm.estimate`: this module creates NO new open surface,
it re-packages the same wall.  NOT inhabited for `p ≥ 2`; NOT faked. -/
structure EtaRemainderResidual (N : Nat) (w : Q') (p : Nat)
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  /-- `η_p(w)` — the cumulant-2 remainder modulus (DATA). -/
  eta : Q'
  /-- the vacuum-rebased leading exponent `A_p = p·⟨single-step⟩` (`w_eff = exp(−A_p)`). -/
  A : Q'
  /-- range-reduction plumbing so `CReal.log` is defined on each eigenvalue. -/
  red : (s : Nat) → CRealLogRangeReduction (CReal.ofQ' (fusionEig N w p s (h0' s)))
  /-- **THE OPEN CONTENT**: the second-cumulant remainder is `C₂²`-controlled by `η_p`,
  uniformly in `s`. -/
  remainderBound : ∀ s,
    CReal.leEv (CReal.abs (logResidual N w p h0' A red s))
      (CReal.ofQ' (eta * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))))

/-- **`cumulantSaddle_of_residual`** — the residual inhabits the cumulant-saddle form. -/
def cumulantSaddle_of_residual {N : Nat} {w : Q'} {p : Nat}
    {h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (E : EtaRemainderResidual N w p h0') : CumulantSaddleForm N w p h0' where
  A := E.A
  eta := E.eta
  red := E.red
  remainder := E.remainderBound

/-- **`saddleLogForm_of_residual`** — the residual threads all the way to the existing
`SaddleLogForm` statement (composition over the proved repackaging). -/
def saddleLogForm_of_residual {N : Nat} {w : Q'} {p : Nat}
    {h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (E : EtaRemainderResidual N w p h0') : SaddleLogForm N w p h0' :=
  toSaddleLogForm (cumulantSaddle_of_residual E)

/-! ## 4. Cumulant-1 (leading term) — the steepest-descent curvature, PROVED -/

/-- **`leadingExponent_curvature`** — the discrete steepest-descent leading-term fact:
if the exponent statistic has constant second difference `a + b ≃ 2c + 2` (this is
`Δ²C₄ = 2`, `casimir_secondDiff_eq_two`, once bridged to `Q'`), then the saddle
leading exponent `A·C₂` is a parabola of curvature `−2A`:

    A·a + A·b  ≃  2·(A·c) + 2·A.

Cancellation-free (`ring_qeqv` on the two ring identities; `h` rewritten in the middle
slot).  This is the cumulant-1 content: the `−A·C₂` term reproduces the Gaussian
curvature exactly, leaving only the `C₂²` remainder. -/
theorem leadingExponent_curvature (A a b c : Q')
    (h : (a + b).eqv (Q'.ofNat 2 * c + Q'.ofNat 2)) :
    (A * a + A * b).eqv (Q'.ofNat 2 * (A * c) + Q'.ofNat 2 * A) := by
  have h1 : (A * a + A * b).eqv (A * (a + b)) := by ring_qeqv
  have h2 : (A * (a + b)).eqv (A * (Q'.ofNat 2 * c + Q'.ofNat 2)) :=
    Q'.mul_eqv_congr_left A _ _ h
  have h3 : (A * (Q'.ofNat 2 * c + Q'.ofNat 2)).eqv
      (Q'.ofNat 2 * (A * c) + Q'.ofNat 2 * A) := by ring_qeqv
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)

/-- Local `Q'`-cast bridge `ofNat a + ofNat b ≃ ofNat (a + b)`. -/
theorem ofNatAdd (a b : Nat) : (Q'.ofNat a + Q'.ofNat b).eqv (Q'.ofNat (a + b)) := by
  show (Q'.ofNat a + Q'.ofNat b).num * ((Q'.ofNat (a + b)).den : Int)
      = (Q'.ofNat (a + b)).num * ((Q'.ofNat a + Q'.ofNat b).den : Int)
  rw [Q'.add_num_cast, Q'.add_den_cast]
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  omega

/-- **`casimir_C2_secondDiff`** — the `Q'`-level Casimir second-difference bridge:
`C₂(s) + C₂(s+2) ≃ 2·C₂(s+1) + 2` with `C₂(s) = ofNat (c4 s)`.  (`ofNatAdd` +
`casimir_secondDiff_eq_two` + `ofNatMul`; supplies the hypothesis of
`leadingExponent_curvature`.) -/
theorem casimir_C2_secondDiff (s : Nat) :
    (Q'.ofNat (c4 s) + Q'.ofNat (c4 (s + 2))).eqv
      (Q'.ofNat 2 * Q'.ofNat (c4 (s + 1)) + Q'.ofNat 2) := by
  -- ofNat(c4 s) + ofNat(c4(s+2)) ≃ ofNat(c4 s + c4(s+2)) = ofNat(2·c4(s+1) + 2)
  have hnat : c4 s + c4 (s + 2) = 2 * c4 (s + 1) + 2 :=
    casimir_secondDiff_eq_two s
  have e1 : (Q'.ofNat (c4 s) + Q'.ofNat (c4 (s + 2))).eqv
      (Q'.ofNat (2 * c4 (s + 1) + 2)) := by
    refine Q'.eqv_trans _ _ _ (ofNatAdd (c4 s) (c4 (s + 2))) ?_
    rw [hnat]
    exact Q'.eqv_refl _
  -- ofNat(2·c4(s+1) + 2) ≃ ofNat(2·c4(s+1)) + ofNat 2 ≃ (ofNat 2 · ofNat(c4(s+1))) + ofNat 2
  have e2 : (Q'.ofNat (2 * c4 (s + 1) + 2)).eqv
      (Q'.ofNat 2 * Q'.ofNat (c4 (s + 1)) + Q'.ofNat 2) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (ofNatAdd (2 * c4 (s + 1)) 2)) ?_
    exact Q'.add_eqv_congr_right _ _ (Q'.ofNat 2) (ofNat_mul_eqv' 2 (c4 (s + 1)))
  exact Q'.eqv_trans _ _ _ e1 e2

/-- **`leadingExponent_secondDiff`** — the saddle leading exponent `A·C₂` is a parabola
of curvature `−2A` over the fusion tower: `A·C₂(s) + A·C₂(s+2) ≃ 2·(A·C₂(s+1)) + 2·A`.
This is `leadingExponent_curvature` specialized along `casimir_C2_secondDiff`; it pins
the cumulant-1 saddle term and isolates the `C₂²` remainder as the sole residual. -/
theorem leadingExponent_secondDiff (A : Q') (s : Nat) :
    (A * Q'.ofNat (c4 s) + A * Q'.ofNat (c4 (s + 2))).eqv
      (Q'.ofNat 2 * (A * Q'.ofNat (c4 (s + 1))) + Q'.ofNat 2 * A) :=
  leadingExponent_curvature A _ _ _ (casimir_C2_secondDiff s)

/-! ## 5. Cumulant-2 (variance) identity — PROVED re-export

The `C₂²` remainder is not a bare bound: its coefficient is the second cumulant, a
genuine variance identity.  We re-export the proved moment identity — cleared over the
mass `A_t = acN` — as the honest cumulant-2 supply:

    4·⟨x⟩_t + ⟨D²⟩_t  ≃  t²·A_t.

Together with `Δ²C₄ = 2` (`leadingExponent_secondDiff`) this exhibits the two-cumulant
structure `log K = −A·C₂ + R` with `R`'s coefficient `= ½·Δ²C₄·Var`.  -/

/-- **`secondCumulantIdentity`** — the cumulant-2 (variance) identity, cleared over
`acN`, re-exported verbatim from `MeanComplementCovariance.dsq_moment_eq`. -/
theorem secondCumulantIdentity (w : Q') (s t : Nat) (h : s ≤ t) :
    (Q'.ofNat 4 * xmomN w (s + 1) t + dmomN w (s + 1) t).eqv
      (Q'.ofNat (t * t) * acN w (s + 1) t) :=
  dsq_moment_eq w s t h

/-! ## 6. Honest collapse onto the curvature wall (Rule 5 documentation)

`EtaRemainderResidual N w p h0'` for `p ≥ 2` is the SAME single discrete SU(2) fusion
local-CLT curvature wall reached from every side: exponentiating its `C₂²` remainder
bound is exactly the vacuum-normalized eigenvalue-shift control
`SaddleLocalCLT.bulkShiftBound ≤ 1/12`, whose moment-level (variance) content is
`MeanComplementCovariance.DShiftCovResidual` (equiv. `XMeanSecondDiffProgress`'s
`d2x ≤ 1 = ½·Δ²C₄`).  ROUTE 3 re-derives the two-cumulant saddle structure but does
NOT escape that boundary; `p = 2` is the only exact exponent (`FusionAdditiveBridge`),
and for `p ≥ 3` the sum-of-`p` Casimirs has curvature `2p`, mandating the vacuum
rebasing `w_eff = exp(−A_p)`.  No closure is claimed and nothing is inhabited for
`p ≥ 2`. -/

end YMGap.Continuum.DiscreteLaplaceSaddle
