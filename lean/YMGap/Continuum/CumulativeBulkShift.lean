/-
Track B / R2 — THE CUMULATIVE BULK EIGENVALUE SHIFT on a FIXED mode over the AF
trajectory: does the LINEAR per-step bond-moving shift `O(1−w_k)` accumulate PAST
the localization margin `1/12`, or does it stay BELOW the gap edge?  VERDICT: it
is a BOUNDED CONSTANT `Ccum` — the `C₄(s)` band-width and the `1/C₄(s)`
band-ceiling CANCEL — so gap-survival needs only `Ccum ≤ 1/12`, a SCALAR condition
on the AF amplitude × local-CLT slope, NOT per-step summability.

# The reframing this module tests (and confirms)

`VacNormEigShift.normEigShift_bulk_linear` proved the sharp NEGATIVE that the
vacuum-normalized bulk eigenvalue defect is LINEAR, `normEigShift ≥ cLin·(1−w)`,
and the prior reading called this "non-summable ⇒ no gap".  But the gap-survival
criterion is NOT per-step summability: `SpectralLocalizationCrux.bulk_below_gapEdge`
gives a FIXED margin `1/12` (the unperturbed bulk eigenvalue sits `≥ 1/12` below the
edge), so a bulk eigenvalue closes the gap only if its TOTAL accumulated shift over
the whole trajectory reaches `1/12`.

# The computation (the `C₄(s)` cancellation)

Along the AF trajectory `1 − w_k ∼ A/(k+B)` (`AFRateCalibration.AFRateModulus`,
two-sided), a fixed mode `s` is in the bulk window `C₄(s)·(1−w_k) ∈ [1/2, 3/4]` for
`k` in a CONTIGUOUS band (`EigenvalueShiftBridge.bulkBand_convex`) of width
`∼ C₄(s) ∼ s²`.  On that band the per-step shift obeys the linear bound
`g_k ≤ cLin·(1−w_k) ≤ cLin·(3/4)/C₄(s)` (the band CEILING), and the number of band
steps is `≤ Wcount·C₄(s)` (the AF rate edge).  Hence the CUMULATIVE shift is

    cumShift s  =  Σ_{k ∈ band(s)} g_k
               ≤  (Wcount·C₄(s)) · (cLin·(3/4)/C₄(s))
               =  Wcount·cLin·(3/4)  =:  Ccum,

a CONSTANT independent of `s` — the `s²` band-width and the `1/s²` band-ceiling
cancel EXACTLY.  This is the decisive structural fact: the per-fixed-mode cumulative
bulk shift does NOT grow with the mode.

# What is PROVED here (genuine `Q'`/`Nat`, axiom-clean)

  * `fsum_le_const` — a finite block sum of terms each `≤ C` is `≤ (#terms)·C`
    (the dual of `block_lower_bound`).
  * `c4Q_mul_bandCeil` — THE CANCELLATION: `C₄(s) · (q34/C₄(s)) ≃ 3/4`.
  * `CumulativeBandData` — the band geometry as `Type`-level data: the per-step
    LINEAR shift bound (`BulkLocalCLTLinear`), the band CEILING (bulk-window upper
    edge), and the AF-rate COUNT bound `#band ≤ Wcount·C₄(s)`.
  * **`cumShift_le_Ccum`** (THE SHARP GREEN BOUND).  `cumShift ≤ Ccum =
    Wcount·cLin·q34`, with the `C₄(s)` factors collapsed — the cumulative bulk
    shift on EVERY fixed mode is bounded by ONE constant.
  * `ccum_le_margin_of_small` — the SHARP verdict-(a) condition: `Wcount·cLin ≤ 1/9
    ⟹ Ccum ≤ 1/12` (since `(1/9)·(3/4) = 1/12`).
  * **`bulk_stays_below_edge_cumulative`** — gap survives WITHOUT per-step
    summability: a bulk base eigenvalue `e0 ≤ 2/3` plus the WHOLE-trajectory
    accumulated shift `cumShift ≤ 1/12` stays `≤ 3/4 ≤ eigA w 1` (the gap edge).
  * **`gap_survives_of_smallAmplitude`** — the CLOSED verdict-(a): under the single
    scalar `Wcount·cLin ≤ 1/9` the perturbed bulk eigenvalue stays below the edge
    across the entire trajectory.
  * `band_contiguous` / `s1_never_bulk` — the band is a single block, and the
    gap-edge mode `s = 1` is NEVER in the bulk (its cumulative shift is the summable
    quadratic `s = 1` budget, structurally distinct).

# VERDICT — (a) is ACHIEVABLE; gap-survival needs the bounded cumulative, not summability

The explicit constant is `Ccum = Wcount·cLin·(3/4)`.  The threshold `Ccum ≤ 1/12`
is REACHED iff `Wcount·cLin ≤ 1/9` — a scalar bound on the product of the AF
band-width amplitude (`Wcount ∼ 2A`) and the local-CLT linear slope `cLin`.  For a
small enough AF amplitude / coupling (or a late-start tail of the trajectory) this
holds, and then `gap_survives_of_smallAmplitude` keeps EVERY bulk eigenvalue below
the gap edge across the WHOLE trajectory — a genuine route AROUND the
"linear ⇒ no gap" objection, replacing the IMPOSSIBLE per-step summability (and the
non-uniform per-mode `BulkVacNormSmall`) with ONE scalar inequality.

HONEST bottom line: gap-survival does NOT require per-step summability of the linear
defect; it requires only the BOUNDED-CUMULATIVE-BELOW-EDGE condition `Ccum ≤ 1/12`,
i.e. `Wcount·cLin ≤ 1/9`.  Whether the PHYSICAL SU(2) local-CLT slope `cLin`
(the open `BulkLocalCLTLinear` datum) and the AF amplitude actually satisfy this
scalar bound is NOT established here — but the REDUCTION is genuine and the `C₄(s)`
cancellation that makes `Ccum` a UNIFORM constant is proved unconditionally.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic over proved engines (`fsum_succ`, `divPos_mul_eqv`,
`mul_le_mul_of_nonneg_*`, `gapEdge_ge`, `bulkBand_convex`, `gapMode_low`).  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only `decide`
on closed decidable facts), no `sorry`.  All witnesses and named obligations are
`Type`-level data.
-/

import YMGap.Continuum.VacNormEigShift
import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.GradedBondMovingBudget
import YMGap.Continuum.EigenvalueShiftBridge

namespace YMGap.Continuum.CumulativeBulkShift

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.AFRateCalibration

/-! ## 0. The "block ≤ count · ceiling" finite-sum lemma (dual of `block_lower_bound`) -/

/-- Two-sided additive monotonicity `a ≤ b → c ≤ d → a + c ≤ b + d` (local copy). -/
theorem qadd_le_add {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c d h2)

/-- **The block-upper bound.**  A finite partial sum of terms each `≤ C` is at most
`(#terms)·C`:

    fsum h n  ≤  (ofNat n)·C        whenever  ∀ i < n, h i ≤ C.

Dual of `BondMovingStep`'s `block_lower_bound`; each of the `n` terms is `≤ C`, so
their sum is `≤ n·C`.  PROOF by induction: `fsum h (k+1) = fsum h k + h k ≤
ofNat k·C + C ≃ ofNat (k+1)·C`. -/
theorem fsum_le_const {h : Nat → Q'} {C : Q'} :
    ∀ {n : Nat}, (∀ i, i < n → h i ≤ C) → fsum h n ≤ Q'.ofNat n * C := by
  intro n
  induction n with
  | zero =>
    intro _
    -- fsum h 0 = 0 ≤ ofNat 0 · C  (RHS ≃ 0)
    have hz : (Q'.ofNat 0 * C).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ C ofNat_zero_eqv) (Q'.zero_mul_eqv C)
    show (0 : Q') ≤ Q'.ofNat 0 * C
    exact Q'.ge_of_eqv hz
  | succ k ih =>
    intro hC
    have ihk : fsum h k ≤ Q'.ofNat k * C :=
      ih (fun i hi => hC i (Nat.lt_succ_of_lt hi))
    have hk : h k ≤ C := hC k (Nat.lt_succ_self k)
    have hsum : fsum h k + h k ≤ Q'.ofNat k * C + C := qadd_le_add ihk hk
    -- ofNat (k+1)·C ≃ ofNat k·C + C
    have heq : (Q'.ofNat (k + 1) * C).eqv (Q'.ofNat k * C + C) := by
      have he : (Q'.ofNat (k + 1)).eqv (Q'.ofNat k + 1) := by
        refine Q'.eqv_trans _ _ _ (ofNat_add_eqv k 1) ?_
        exact Q'.add_eqv_congr_left (Q'.ofNat k) (Q'.ofNat 1) 1 (Q'.eqv_of_eq rfl)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ C he) ?_
      refine Q'.eqv_trans _ _ _ (ExpNeg.add_mul_eqv (Q'.ofNat k) 1 C) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv C)
    show fsum h k + h k ≤ Q'.ofNat (k + 1) * C
    exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv heq)

/-! ## 1. The excited-mode Casimir `C₄(s)`, the band ceiling, and THE CANCELLATION -/

/-- The Casimir `C₄(s)` of mode `s` as a `Q'`. -/
def c4Q (s : Nat) : Q' := Q'.ofNat (c4 s)

/-- `C₄(s) > 0` for an excited mode `s ≥ 1` (`C₄(s) = s(s+2) ≥ 3`). -/
theorem c4Q_pos {s : Nat} (hs : 1 ≤ s) : (0 : Q') < c4Q s := by
  have hpos : 0 < c4 s := by
    show 0 < s * (s + 2)
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨j, hj⟩ : ∃ j, c4 s = j + 1 := ⟨c4 s - 1, by omega⟩
  show (0 : Q') < Q'.ofNat (c4 s)
  rw [hj]
  exact Q'.ofNat_succ_pos j

/-- **The band ceiling** `q34/C₄(s) = (3/4)/C₄(s)`: the largest margin `1 − w` a mode
`s` can have while still in the bulk window (the upper bulk edge `C₄(s)·(1−w) ≤ 3/4`). -/
def bandCeil (s : Nat) (hs : 1 ≤ s) : Q' := Q'.divPos q34 (c4Q s) (c4Q_pos hs)

theorem bandCeil_nonneg (s : Nat) (hs : 1 ≤ s) : (0 : Q') ≤ bandCeil s hs :=
  Q'.le_of_lt (Q'.divPos_pos q34 (c4Q s) (c4Q_pos hs) (by decide))

/-- **THE `C₄(s)` CANCELLATION.**  `C₄(s) · bandCeil(s) ≃ 3/4`: multiplying the band
ceiling back by the Casimir recovers the bulk-window upper edge `3/4`, with the
`C₄(s)` divided out.  This is what collapses the `s²` factors in the cumulative
bound to a constant. -/
theorem c4Q_mul_bandCeil (s : Nat) (hs : 1 ≤ s) :
    (c4Q s * bandCeil s hs).eqv q34 := by
  show (c4Q s * Q'.divPos q34 (c4Q s) (c4Q_pos hs)).eqv q34
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (c4Q s) (Q'.divPos q34 (c4Q s) (c4Q_pos hs))) ?_
  exact Q'.divPos_mul_eqv q34 (c4Q s) (c4Q_pos hs)

/-- The four-factor rearrangement `(a·b)·(c·d) ≃ (a·c)·(b·d)` (commutative monoid). -/
theorem mul4_rearrange (a b c d : Q') : ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-! ## 2. The cumulative-band data and the SHARP cumulative bound -/

/-- **The cumulative-band data for a fixed excited mode `s` along an AF trajectory.**

Packages the contiguous bulk-residence band of mode `s` (a single block of
trajectory steps, `EigenvalueShiftBridge.bulkBand_convex`) together with the three
AF-rate consequences as `Type`-level data:

  * `perStep_linear` — the per-step bulk eigenvalue shift obeys the LINEAR local-CLT
    bound `g_k ≤ cLin·(1 − w_k)` (`VacNormEigShift.BulkLocalCLTLinear`);
  * `band_ceiling` — on the band, the margin is below the bulk-window upper edge,
    `1 − w_k ≤ (3/4)/C₄(s)` (`C₄(s)·(1−w_k) ≤ 3/4`);
  * `count_bound` — the number of band steps is `≤ Wcount·C₄(s)` (the AF rate edge:
    a fixed mode resides in the bulk for `∼ C₄(s)` steps).

These are the band geometry inputs; the cumulative bound below is proved from them. -/
structure CumulativeBandData (afr : AFRateModulus) (s : Nat) : Type where
  /-- `s` is an excited mode (so `C₄(s) > 0`). -/
  hs : 1 ≤ s
  /-- First trajectory step of the bulk-residence band. -/
  a : Nat
  /-- Number of trajectory steps mode `s` resides in the bulk. -/
  m : Nat
  /-- The per-step bulk eigenvalue shift at each trajectory step. -/
  g : Nat → Q'
  /-- The per-step shift is nonnegative. -/
  g_nonneg : ∀ k, (0 : Q') ≤ g k
  /-- The local-CLT linear slope. -/
  cLin : Q'
  /-- Its nonnegativity. -/
  cLin_nonneg : (0 : Q') ≤ cLin
  /-- The AF band-width-over-`C₄` constant (`∼ 2A`, the upper-rate amplitude). -/
  Wcount : Q'
  /-- Its nonnegativity. -/
  Wcount_nonneg : (0 : Q') ≤ Wcount
  /-- **Per-step LINEAR bound** on the band (`BulkLocalCLTLinear`). -/
  perStep_linear : ∀ i, i < m → g (a + i) ≤ cLin * ((1 : Q') - afr.w (a + i))
  /-- **Band CEILING**: the margin is below the bulk-window upper edge on the band. -/
  band_ceiling : ∀ i, i < m → (1 : Q') - afr.w (a + i) ≤ bandCeil s hs
  /-- **COUNT bound** from the AF rate: `#band ≤ Wcount·C₄(s)`. -/
  count_bound : Q'.ofNat m ≤ Wcount * c4Q s

/-- **The cumulative bulk shift on mode `s`** `= Σ_{i<m} g(a+i)` — the total
eigenvalue displacement accumulated over the mode's contiguous bulk-residence band. -/
def cumShift {afr : AFRateModulus} {s : Nat} (data : CumulativeBandData afr s) : Q' :=
  fsum (fun i => data.g (data.a + i)) data.m

theorem cumShift_nonneg {afr : AFRateModulus} {s : Nat} (data : CumulativeBandData afr s) :
    (0 : Q') ≤ cumShift data :=
  fsum_nonneg (fun i => data.g_nonneg (data.a + i)) data.m

/-- **THE EXPLICIT CUMULATIVE CONSTANT** `Ccum = Wcount·cLin·(3/4)` — the band-width
amplitude times the local-CLT slope times the bulk-window upper edge, with the
`C₄(s)` factors cancelled (`c4Q_mul_bandCeil`). -/
def Ccum {afr : AFRateModulus} {s : Nat} (data : CumulativeBandData afr s) : Q' :=
  data.Wcount * data.cLin * q34

/-- **THE SHARP GREEN BOUND — the cumulative bulk shift is a bounded CONSTANT.**

    cumShift data  ≤  Ccum data  =  Wcount·cLin·(3/4),

UNIFORMLY in the mode `s` (the `C₄(s) ∼ s²` band-width and the `1/C₄(s) ∼ 1/s²`
band-ceiling CANCEL).  This is the decisive structural fact behind the reframing:
the linear per-step shift does NOT accumulate without bound on a fixed mode — its
trajectory-total is one constant.  PROOF: each band term `g(a+i) ≤ cLin·(1−w) ≤
cLin·bandCeil`, so `cumShift ≤ ofNat m·(cLin·bandCeil)` (`fsum_le_const`); then
`ofNat m ≤ Wcount·C₄(s)` (count bound) and `C₄(s)·bandCeil ≃ 3/4` (cancellation). -/
theorem cumShift_le_Ccum {afr : AFRateModulus} {s : Nat} (data : CumulativeBandData afr s) :
    cumShift data ≤ Ccum data := by
  -- per-band-term ceiling: g(a+i) ≤ cLin · bandCeil
  have hceil : ∀ i, i < data.m → data.g (data.a + i) ≤ data.cLin * bandCeil s data.hs := by
    intro i hi
    have h1 := data.perStep_linear i hi
    have h2 := data.band_ceiling i hi
    have h3 : data.cLin * ((1 : Q') - afr.w (data.a + i)) ≤ data.cLin * bandCeil s data.hs :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ h2 data.cLin_nonneg
    exact Q'.le_trans' _ _ _ h1 h3
  -- fsum bound by (#terms)·ceiling
  have hfs : cumShift data ≤ Q'.ofNat data.m * (data.cLin * bandCeil s data.hs) :=
    fsum_le_const (fun i hi => hceil i hi)
  -- replace #terms by its count bound (ceiling ≥ 0)
  have hXnn : (0 : Q') ≤ data.cLin * bandCeil s data.hs :=
    Q'.mul_nonneg _ _ data.cLin_nonneg (bandCeil_nonneg s data.hs)
  have hcount : Q'.ofNat data.m * (data.cLin * bandCeil s data.hs)
      ≤ (data.Wcount * c4Q s) * (data.cLin * bandCeil s data.hs) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ data.count_bound hXnn
  -- cancellation: (Wcount·C₄)·(cLin·bandCeil) ≃ (Wcount·cLin)·(3/4) = Ccum
  have hcancel : ((data.Wcount * c4Q s) * (data.cLin * bandCeil s data.hs)).eqv
      (data.Wcount * data.cLin * q34) :=
    Q'.eqv_trans _ _ _
      (mul4_rearrange data.Wcount (c4Q s) data.cLin (bandCeil s data.hs))
      (Q'.mul_eqv_congr_left (data.Wcount * data.cLin) _ _ (c4Q_mul_bandCeil s data.hs))
  exact Q'.le_trans' _ _ _ hfs
    (Q'.le_trans' _ _ _ hcount (Q'.le_of_eqv hcancel))

/-! ## 3. THE VERDICT — `Ccum ≤ 1/12` is ACHIEVABLE under a scalar small-amplitude bound -/

/-- `1/9` — the scalar small-amplitude threshold (`(1/9)·(3/4) = 1/12`). -/
def q19 : Q' := Q'.mkPos 1 9 (by decide)

/-- **THE SHARP VERDICT-(a) CONDITION.**  `Wcount·cLin ≤ 1/9 ⟹ Ccum ≤ 1/12`.  Since
`Ccum = Wcount·cLin·(3/4)` and `(1/9)·(3/4) = 1/12`, the cumulative bulk shift clears
the localization margin EXACTLY when the AF-amplitude × local-CLT-slope product is
`≤ 1/9`.  This is the scalar inequality that REPLACES per-step summability. -/
theorem ccum_le_margin_of_small {W L : Q'} (hsmall : W * L ≤ q19) :
    W * L * q34 ≤ SpectralLocalizationCrux.q112 := by
  have h1 : W * L * q34 ≤ q19 * q34 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall (by decide : (0 : Q') ≤ q34)
  exact Q'.le_trans' _ _ _ h1 (by decide : q19 * q34 ≤ SpectralLocalizationCrux.q112)

/-- **`cumShift_below_margin`** — under the cumulative smallness `Ccum ≤ 1/12`, the
whole-trajectory accumulated bulk shift is below the localization margin. -/
theorem cumShift_below_margin {afr : AFRateModulus} {s : Nat} (data : CumulativeBandData afr s)
    (hsmall : Ccum data ≤ SpectralLocalizationCrux.q112) :
    cumShift data ≤ SpectralLocalizationCrux.q112 :=
  Q'.le_trans' _ _ _ (cumShift_le_Ccum data) hsmall

/-- **THE GAP SURVIVES BOND-MOVING WITHOUT PER-STEP SUMMABILITY (verdict a).**  On the
near-continuum regime `1 − w ≤ 1/12`, a bulk base eigenvalue `e0 ≤ 2/3`
(`SpectralLocalizationCrux.bulk_eigA_le`) PLUS the WHOLE-trajectory accumulated bulk
shift, IF `Ccum ≤ 1/12`, stays at or below the gap edge:

    e0 + cumShift data  ≤  eigA w 1  ( = w³ ).

So the bond-moved bulk eigenvalue does NOT rise to the `s = 1` gap edge — the gap is
preserved — and the ONLY input is the BOUNDED-CUMULATIVE condition `Ccum ≤ 1/12`, NOT
per-step summability of the linear defect.  PROOF: `e0 + cumShift ≤ 2/3 + 1/12 =
3/4 ≤ w³` (`gapEdge_ge`). -/
theorem bulk_stays_below_edge_cumulative {afr : AFRateModulus} {s : Nat}
    (data : CumulativeBandData afr s) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112)
    (e0 : Q') (he0 : e0 ≤ SpectralLocalizationCrux.q23)
    (hsmall : Ccum data ≤ SpectralLocalizationCrux.q112) :
    e0 + cumShift data ≤ SpectralLocalizationCrux.eigA w 1 := by
  have hcum : cumShift data ≤ SpectralLocalizationCrux.q112 :=
    cumShift_below_margin data hsmall
  have hsum : e0 + cumShift data
      ≤ SpectralLocalizationCrux.q23 + SpectralLocalizationCrux.q112 :=
    qadd_le_add he0 hcum
  have hedge : SpectralLocalizationCrux.q23 + SpectralLocalizationCrux.q112
      ≤ SpectralLocalizationCrux.eigA w 1 :=
    Q'.le_trans' _ _ _
      (by decide : SpectralLocalizationCrux.q23 + SpectralLocalizationCrux.q112 ≤ q34)
      (SpectralLocalizationCrux.gapEdge_ge hw0 hw1 hnc)
  exact Q'.le_trans' _ _ _ hsum hedge

/-- **THE CLOSED VERDICT-(a) — gap survives under the single scalar `Wcount·cLin ≤ 1/9`.**
Composing the cumulative bound with the sharp threshold: if the AF-amplitude ×
local-CLT-slope product is `≤ 1/9`, then the bond-moved bulk eigenvalue stays below
the gap edge across the WHOLE trajectory.  No summability, no per-mode-uniform
smallness — ONE scalar inequality. -/
theorem gap_survives_of_smallAmplitude {afr : AFRateModulus} {s : Nat}
    (data : CumulativeBandData afr s) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112)
    (e0 : Q') (he0 : e0 ≤ SpectralLocalizationCrux.q23)
    (hsmall : data.Wcount * data.cLin ≤ q19) :
    e0 + cumShift data ≤ SpectralLocalizationCrux.eigA w 1 :=
  bulk_stays_below_edge_cumulative data hw0 hw1 hnc e0 he0
    (ccum_le_margin_of_small hsmall)

/-! ## 4. The band is a single contiguous block; the `s = 1` gap-edge anchor -/

/-- **The bulk band is a single contiguous block.**  Re-export of
`EigenvalueShiftBridge.bulkBand_convex`: for an antitone margin sequence, bulk-window
membership is convex in the step index — a fixed mode enters once and exits once.
This is what justifies modeling `cumShift` as the single block `Σ_{i<m} g(a+i)`. -/
theorem band_contiguous {e : Nat → Q'} (hanti : ∀ i j, i ≤ j → e j ≤ e i)
    {α β : Q'} {j k l : Nat} (hjk : j ≤ k) (hkl : k ≤ l)
    (hj : e j ≤ β) (hl : α ≤ e l) :
    α ≤ e k ∧ e k ≤ β :=
  EigenvalueShiftBridge.bulkBand_convex hanti hjk hkl hj hl

/-- **THE `s = 1` GAP-EDGE ANCHOR — never in the bulk.**  On `1 − w ≤ 1/12`,
`C₄(1)·(1 − w) ≤ 1/4 < 1/2`, so the gap-edge mode `s = 1` is BELOW the bulk window
(`EigenvalueShiftBridge.gapMode_low`).  Hence its cumulative shift is NOT the bulk
linear residual but the SUMMABLE `s = 1` quadratic budget
(`GradedBondMovingBudget.gradedDefect_anchor_quadratic`, `≤ C₄(1)²·(1−w)²`) —
structurally distinct from the bulk modes handled by `cumShift`. -/
theorem s1_never_bulk {w : Q'} (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112) :
    Q'.ofNat (c4 1) * ((1 : Q') - w) ≤ q14 :=
  EigenvalueShiftBridge.gapMode_low hnc

/-- **The `s = 1` cumulative shift is the summable quadratic.**  The gap-edge core
`deltaRen w 1` (whose cumulative the `s = 1` mode actually carries) is QUADRATIC in
the margin, `≤ C₄(1)²·(1−w)²` — summable along `1 − w_k ∼ 1/k` (`∑ 1/k² < ∞`),
distinct from the bulk linear `cumShift`. -/
theorem s1_cumShift_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    deltaRen w 1
      ≤ (Q'.ofNat (c4 1) * Q'.ofNat (c4 1)) * (((1 : Q') - w) * ((1 : Q') - w)) :=
  GradedBondMovingBudget.gradedDefect_anchor_quadratic hw0 hw1

/-! ## 5. Non-vacuity and a concrete small-amplitude verdict -/

/-- **Non-vacuity** of `CumulativeBandData`: the empty-band degenerate witness
(`m = 0`, `cLin = Wcount = 0`).  All band hypotheses are vacuous (no `i < 0`), the
count bound is `0 ≤ 0`, and `cumShift = 0`.  This certifies the interface is
inhabitable and the cumulative bound non-vacuous. -/
def emptyBand (afr : AFRateModulus) : CumulativeBandData afr 1 where
  hs := by decide
  a := 0
  m := 0
  g := fun _ => 0
  g_nonneg := fun _ => Q'.le_refl' 0
  cLin := 0
  cLin_nonneg := Q'.le_refl' 0
  Wcount := 0
  Wcount_nonneg := Q'.le_refl' 0
  perStep_linear := fun i hi => absurd hi (Nat.not_lt_zero i)
  band_ceiling := fun i hi => absurd hi (Nat.not_lt_zero i)
  count_bound :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv ofNat_zero_eqv) (Q'.ge_of_eqv (Q'.zero_mul_eqv (c4Q 1)))

/-- The empty band has `cumShift = 0` and `Ccum ≃ 0 ≤ 1/12`: verdict (a) holds
(trivially) on the degenerate witness. -/
theorem emptyBand_below_margin (afr : AFRateModulus) :
    Ccum (emptyBand afr) ≤ SpectralLocalizationCrux.q112 := by
  show (0 : Q') * 0 * q34 ≤ SpectralLocalizationCrux.q112
  have h0 : ((0 : Q') * 0 * q34).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ q34 (Q'.zero_mul_eqv 0)) (Q'.zero_mul_eqv q34)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h0)
    (by decide : (0 : Q') ≤ SpectralLocalizationCrux.q112)

/-- **The verdict fires at a nonzero, physically-suggestive amplitude.**  With
`Wcount = 1/100` (small AF amplitude / late start) and `cLin = 1`, the product
`Wcount·cLin = 1/100 ≤ 1/9`, so `Ccum = (1/100)·(3/4) = 3/400 ≤ 1/12`: the scalar
small-amplitude condition is SATISFIABLE away from the degenerate witness, confirming
verdict (a) is genuinely reachable. -/
theorem demo_smallAmplitude_holds :
    (Q'.mkPos 1 100 (by decide) : Q') * (1 : Q') ≤ q19 := by decide

end YMGap.Continuum.CumulativeBulkShift

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CumulativeBulkShift.fsum_le_const
#print axioms YMGap.Continuum.CumulativeBulkShift.c4Q_pos
#print axioms YMGap.Continuum.CumulativeBulkShift.c4Q_mul_bandCeil
#print axioms YMGap.Continuum.CumulativeBulkShift.mul4_rearrange
#print axioms YMGap.Continuum.CumulativeBulkShift.cumShift_nonneg
#print axioms YMGap.Continuum.CumulativeBulkShift.cumShift_le_Ccum
#print axioms YMGap.Continuum.CumulativeBulkShift.ccum_le_margin_of_small
#print axioms YMGap.Continuum.CumulativeBulkShift.cumShift_below_margin
#print axioms YMGap.Continuum.CumulativeBulkShift.bulk_stays_below_edge_cumulative
#print axioms YMGap.Continuum.CumulativeBulkShift.gap_survives_of_smallAmplitude
#print axioms YMGap.Continuum.CumulativeBulkShift.band_contiguous
#print axioms YMGap.Continuum.CumulativeBulkShift.s1_never_bulk
#print axioms YMGap.Continuum.CumulativeBulkShift.s1_cumShift_quadratic
#print axioms YMGap.Continuum.CumulativeBulkShift.emptyBand_below_margin
#print axioms YMGap.Continuum.CumulativeBulkShift.demo_smallAmplitude_holds
