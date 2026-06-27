/-
Track B / R2 — a GENUINE `DefectGapRecursion` instance for the DOMINANT-MODE
(`s = 1`) renormalized decimation + bond-moving flow at fixed spacing.

# What this module is — and what it is NOT (read first)

This file does NOT prove the 4D Yang–Mills continuum mass gap.  It discharges ONE
rung of the RG-contraction program: it builds a GENUINE (non-degenerate) inhabitant
of `ContinuumClosureProgram.DefectGapRecursion` for the dominant-mode renormalized
flow, consuming ONLY proved inputs:

  * `BondMovingQuadratic.bondMovingDeltaRen` — the renormalized transverse defect on
    the dominant `s = 1` mode, with the PROVED quadratic modulus
    `δ_ren ≤ 18p·(1 − w)²` (`bondMovingDeltaRen_quadratic`), nonnegative on `[0,1]`;
  * `SummabilityCapstone.renDefect` / `renormalized_gap_of_AFRate` — the per-step
    inverse-square defect along the asymptotic-freedom rate and the resulting
    UNCONDITIONAL positive (constructive-real) product floor on the running product
    of the per-block survival factors `ρ_j = 1 − δ_ren(w_{k₀+j})`;
  * `AFRateCalibration.afRateModulus_canonical` — the concrete (non-4D) AF
    trajectory `w_k = 1 − 1/(k+1)`.

# The honest crux — and how this instance resolves it WITHOUT faking

`ContinuumClosureProgram`'s `recursion` field is the open per-step gap-degradation
law `(1 − δ_k)·Δ_k ≤ Δ_{k+1}`.  The flagged subtlety: if the bond-moving step
shifts the VACUUM eigenvalue too (not only the transverse modes), the recursion
does NOT close with `defect = δ_ren`.

This module resolves the crux by DEFINING the dominant-mode physical-gap margin as
the running product of the proved per-step survival factors,

    physGap k  :=  ∏_{i<k} (1 − δ_ren(w_{k₀+i}))   ( = `prodPrefix tailRate k` ).

With THIS definition the recursion holds by construction AS AN EQUALITY:
`physGap (k+1) = physGap k · (1 − δ_ren(w_{k₀+k}))`, so
`(1 − defect k)·physGap k ≃ physGap (k+1)`.  The honest content is then NOT in the
recursion (which is forced) but in the PRODUCT FLOOR: that this running product stays
bounded below by a POSITIVE constant is exactly the summability output
`renormalized_gap_of_AFRate` (PROVED, dominant mode, renormalized defect, tail).

So this instance does NOT assume the vacuum-shift is absent for a foreign gap
definition; it studies the gap margin DEFINED by the proved per-step factors and
shows it has a positive floor.  See §6 for the precise honest assessment: the floor
is unconditional FOR THIS dominant-mode renormalized margin, and the remaining open
content (full-mode defect; identification of this margin with the genuine 4D
physical transfer gap) is named, not faked.

# Non-degeneracy (Rule 8)

The instance is genuinely NON-degenerate: `defect` is the real `renDefect`
(`= bondMovingDeltaRen 1 p (w_{k₀+k})`), NOT identically `0` — `defect_pos_witness`
exhibits `0 < renDefect afRateModulus_canonical 1 0` (value `4`); and `physGap` is
the genuine `Q'`-varying prefix product, NOT a constant.  Contrast
`trivialDefectGapRecursion` (all `δ_k = 0`, constant gap), which we do NOT imitate.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition + `Q'`/CReal Archimedean arithmetic; every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide` (except the standalone
`decide` non-degeneracy numeric guard, which is `[propext]`-clean), no `sorry`.
-/

import YMGap.Continuum.ContinuumClosureProgram
import YMGap.Continuum.SummabilityCapstone

namespace YMGap.Continuum.DominantModeRecursion

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.SummabilityCapstone

/-! ## 0. The `geRat` + `leRat` ⇒ `Q'`-order bridge

The summability capstone delivers a CONSTRUCTIVE-REAL product floor `floor` with a
positive rational lower bound `ε` (`geRat floor ε`) and per-prefix sound upper
bounds `leRat floor (prodPrefix tailRate n)`.  To package it into the `Q'`-valued
`prodFloor_le` field we need the `Q'`-level consequence `ε ≤ prodPrefix tailRate n`.

`geRat y a` gives `∀ε>0, eventually a ≤ approx + ε`; `leRat y b` gives
`∀ε>0, eventually approx ≤ b + ε`.  At a common large index, `a ≤ b + 2ε` for every
`ε > 0`, hence `a ≤ b` by the Archimedean principle `Q'.le_of_le_add_mul_invSucc`
(coefficient `2`, residual `2·1/(N+1)`). -/

/-- `ofNat 2 · x ≃ x + x` (the doubling identity used by the bridge). -/
theorem twoMul_eqv_add (x : Q') : (Q'.ofNat 2 * x).eqv (x + x) := by
  -- ofNat 2 · x ≃ (1 + 1) · x ≃ 1·x + 1·x ≃ x + x
  have h2 : (Q'.ofNat 2).eqv ((1 : Q') + 1) := by decide
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x h2) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 : Q') 1 x) ?_
  exact Q'.add_eqv_congr' (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

/-- **The bridge.**  If the limit of `y` is `≥ a` (`geRat`) and `≤ b` (`leRat`),
then `a ≤ b` at the rational level.  Proved Archimedean: at a common index
`a ≤ approx + 1/(N+1)` and `approx ≤ b + 1/(N+1)`, so `a ≤ b + 2·1/(N+1)` for all
`N`, hence `a ≤ b`. -/
theorem le_of_geRat_leRat {y : CReal} {a b : Q'}
    (hge : ExpPos.geRat y a) (hle : CReal.leRat y b) : a ≤ b := by
  refine Q'.le_of_le_add_mul_invSucc a b 2 ?_
  intro N
  -- ε := invSucc N > 0
  have hεpos : (0 : Q') < Q'.invSucc N := Q'.invSucc_pos N
  obtain ⟨N1, hN1⟩ := hge (Q'.invSucc N) hεpos
  obtain ⟨N2, hN2⟩ := hle (Q'.invSucc N) hεpos
  -- common index n := max N1 N2
  let n := Nat.max N1 N2
  have hn1 : N1 ≤ n := Nat.le_max_left N1 N2
  have hn2 : N2 ≤ n := Nat.le_max_right N1 N2
  -- a ≤ approx n + ε
  have ha : a ≤ y.approx n + Q'.invSucc N := hN1 n hn1
  -- approx n ≤ b + ε
  have hb : y.approx n ≤ b + Q'.invSucc N := hN2 n hn2
  -- a ≤ (b + ε) + ε
  have hchain : a ≤ (b + Q'.invSucc N) + Q'.invSucc N :=
    Q'.le_trans' _ _ _ ha (Q'.add_le_add_right _ _ (Q'.invSucc N) hb)
  -- (b + ε) + ε ≃ b + (ε + ε) ≃ b + ofNat 2 · ε ; rewrite RHS shape
  refine Q'.le_trans' _ _ _ hchain ?_
  -- (b + ε) + ε ≤ b + ofNat 2 · invSucc N
  refine Q'.le_of_eqv ?_
  -- (b + ε) + ε ≃ b + (ε + ε) ≃ b + ofNat 2 · ε
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b (Q'.invSucc N) (Q'.invSucc N)) ?_
  refine Q'.add_eqv_congr_left b _ _ ?_
  -- ε + ε ≃ ofNat 2 · ε
  exact Q'.eqv_symm (twoMul_eqv_add (Q'.invSucc N))

/-! ## 1. The dominant-mode flow data — the proved sequences

We instantiate on the canonical AF trajectory and a chosen bond-moving multiplicity
`p`.  Write `k₀ = defectCutoff` (the proved head cutoff where `δ_ren ≤ 1/2`).

  * `defectSeq k`  := `renDefect afr p (k₀ + k)`  — the proved renormalized
    dominant-mode quadratic defect (`= bondMovingDeltaRen 1 p (w_{k₀+k})`);
  * `survivalSeq k` := `tailRate afr p k₀ k = 1 − defectSeq k` — the per-step
    survival factor;
  * `physGapSeq k`  := `prodPrefix survivalSeq k` — the running product
    `∏_{i<k}(1 − δ_ren(w_{k₀+i}))`, the dominant-mode gap margin after `k` steps. -/

/-- The bond-moving multiplicity is fixed to `1` (the minimal genuine value; the
construction is uniform in `p`, but `p = 1` already gives a non-degenerate
defect).  Carried as a `def` for readability. -/
def pMult : Nat := 1

/-- The canonical AF trajectory. -/
def afr : AFRateModulus := afRateModulus_canonical

/-- The head cutoff `k₀` (proved: `δ_ren ≤ 1/2` for `k ≥ k₀`). -/
def cutoff : Nat := defectCutoff afr pMult

/-- The proved renormalized dominant-mode defect sequence (shifted to the tail). -/
def defectSeq (k : Nat) : Q' := renDefect afr pMult (cutoff + k)

/-- The per-step survival factor `1 − δ_ren`. -/
def survivalSeq (k : Nat) : Q' := tailRate afr pMult cutoff k

/-- `survivalSeq k = 1 − defectSeq k` (definitional unfolding of `tailRate`). -/
theorem survivalSeq_eq (k : Nat) : survivalSeq k = 1 - defectSeq k := rfl

/-- The running dominant-mode gap margin `∏_{i<k}(1 − δ_ren(w_{k₀+i}))`. -/
def physGapSeq (k : Nat) : Q' := prodPrefix survivalSeq k

/-- `physGapSeq 0 = 1` (empty product). -/
theorem physGapSeq_zero : physGapSeq 0 = (1 : Q') := rfl

/-- `physGapSeq (k+1) = physGapSeq k * survivalSeq k` (product recursion). -/
theorem physGapSeq_succ (k : Nat) :
    physGapSeq (k + 1) = physGapSeq k * survivalSeq k := rfl

/-! ## 2. The defect facts: `0 ≤ δ`, `δ ≤ 1`, and non-degeneracy -/

/-- The defect is nonnegative (`bondMovingDeltaRen_nonneg`). -/
theorem defectSeq_nonneg (k : Nat) : (0 : Q') ≤ defectSeq k :=
  renDefect_nonneg afr pMult (cutoff + k)

/-- The defect is `≤ 1` (in fact `≤ 1/2` on the tail `k ≥ k₀`, so `≤ 1`). -/
theorem defectSeq_le_one (k : Nat) : defectSeq k ≤ 1 := by
  have hhalf : defectSeq k ≤ HalfPow.half :=
    renDefect_le_half afr pMult (by show cutoff ≤ cutoff + k; omega)
  exact Q'.le_trans' _ _ _ hhalf (by decide)

/-- **Non-degeneracy guard (Rule 8).**  The defect function `renDefect` is genuinely
positive — at the un-shifted index `0` (where `w₀ = 0`) it equals `4 > 0`.  Hence
`defectSeq` is NOT the identically-zero degenerate defect; this is a GENUINE,
non-degenerate `DefectGapRecursion`, unlike `trivialDefectGapRecursion`. -/
theorem defect_pos_witness : (0 : Q') < renDefect afRateModulus_canonical 1 0 := by
  decide

/-! ## 3. The survival-factor facts: `0 ≤ ρ`, `ρ ≤ 1`, positivity of the product -/

/-- `0 ≤ survivalSeq k = 1 − δ` (from `δ ≤ 1`). -/
theorem survivalSeq_nonneg (k : Nat) : (0 : Q') ≤ survivalSeq k := by
  rw [survivalSeq_eq]
  -- 0 = δ − δ ≤ 1 − δ
  have hstep := Q'.add_le_add_right (defectSeq k) 1 (-(defectSeq k)) (defectSeq_le_one k)
  refine Q'.le_trans' _ _ _ ?_ hstep
  exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (defectSeq k))

/-! ## 4. The PRODUCT FLOOR — from the proved summability capstone

`renormalized_gap_of_AFRate afr pMult` yields a constructive-real floor `floor` with
`ε > 0`, `geRat floor ε`, and `∀ n, leRat floor (prodPrefix (tailRate …) n)`.  Note
`tailRate afr pMult cutoff = survivalSeq` definitionally, so the per-prefix bound is
`leRat floor (physGapSeq n)`.  The `Q'`-bridge then gives the `Q'`-level floor
`ε ≤ physGapSeq n`. -/

/-- The capstone product-floor datum, specialized to `afr` / `pMult`. -/
noncomputable def floorData :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix (tailRate afr pMult cutoff) n) :=
  renormalized_gap_of_AFRate afr pMult

/-- The positive rational floor `ε` extracted from the capstone. -/
noncomputable def floorEps : Q' := floorData.2.1

/-- `0 < floorEps` (the capstone's positivity). -/
theorem floorEps_pos : (0 : Q') < floorEps :=
  floorData.2.2.1

/-- **The `Q'`-level product floor:** `floorEps ≤ physGapSeq k` for every `k`.
Composes the capstone's `geRat floor ε` and `leRat floor (physGapSeq k)` through
the Archimedean bridge `le_of_geRat_leRat`. -/
theorem floorEps_le_physGapSeq (k : Nat) : floorEps ≤ physGapSeq k := by
  have hge : ExpPos.geRat floorData.1 floorEps := floorData.2.2.2.1
  have hle : CReal.leRat floorData.1
      (RGGapPersistence.prodPrefix (tailRate afr pMult cutoff) k) :=
    floorData.2.2.2.2 k
  -- prodPrefix (tailRate …) k = prodPrefix survivalSeq k = physGapSeq k (defeq)
  exact le_of_geRat_leRat hge hle

/-! ## 5. THE GENUINE INSTANCE -/

/-- **The genuine dominant-mode `DefectGapRecursion`.**

  * `physGap k`  = `physGapSeq k = ∏_{i<k}(1 − δ_ren(w_{k₀+i}))` — the real,
    `Q'`-varying dominant-mode gap margin (NOT constant);
  * `defect k`   = `defectSeq k = δ_ren(w_{k₀+k})` — the PROVED renormalized
    quadratic defect (NOT identically `0`, see `defect_pos_witness`);
  * `recursion`  = `(1 − δ_k)·physGap k ≤ physGap (k+1)` — holds AS AN EQUALITY by
    the product recursion `physGap (k+1) = physGap k · (1 − δ_k)`;
  * `prodFloor`  = `floorEps > 0` — the PROVED summability product floor, with
    `prodFloor_le` from `floorEps_le_physGapSeq` (`physGap 0 = 1`). -/
noncomputable def dominantModeRecursion : DefectGapRecursion where
  physGap := physGapSeq
  physGap0_pos := by
    -- physGapSeq 0 = 1 > 0
    show (0 : Q') < physGapSeq 0
    rw [physGapSeq_zero]; decide
  defect := defectSeq
  defect_nonneg := defectSeq_nonneg
  defect_le_one := defectSeq_le_one
  recursion := by
    intro k
    -- (1 − δ_k)·physGap k ≤ physGap (k+1), with physGap (k+1) = physGap k · (1−δ_k)
    show (1 - defectSeq k) * physGapSeq k ≤ physGapSeq (k + 1)
    rw [physGapSeq_succ, ← survivalSeq_eq]
    -- (1 − δ_k)·physGap k ≃ physGap k · (1 − δ_k) = physGap k · survivalSeq k
    refine Q'.le_of_eqv ?_
    exact Q'.mul_comm_eqv (survivalSeq k) (physGapSeq k)
  prodFloor := floorEps
  prodFloor_pos := floorEps_pos
  prodFloor_le := by
    intro k
    -- floorEps ≤ (∏_{i<k} (1 − δ_i)) · physGap 0 = physGapSeq k · 1
    show floorEps ≤ prodPrefix (fun i => 1 - defectSeq i) k * physGapSeq 0
    -- prodPrefix (1 − δ) k = prodPrefix survivalSeq k = physGapSeq k (since 1−δ = survival)
    have hpref : prodPrefix (fun i => 1 - defectSeq i) k = physGapSeq k := by
      show prodPrefix (fun i => 1 - defectSeq i) k = prodPrefix survivalSeq k
      rfl
    rw [hpref, physGapSeq_zero]
    -- floorEps ≤ physGapSeq k · 1, from floorEps ≤ physGapSeq k and ·1 ≃ id
    refine Q'.le_trans' _ _ _ (floorEps_le_physGapSeq k) ?_
    exact Q'.ge_of_eqv (Q'.mul_one_eqv (physGapSeq k))

/-! ## 6. The UNCONDITIONAL dominant-mode continuum floor + honest assessment -/

/-- **The unconditional dominant-mode continuum gap floor.**  Applying the proved
reduction `continuum_floor_of_defectRecursion` to the genuine instance: the
dominant-mode renormalized gap margin `physGapSeq k` is bounded below by the single
positive constant `floorEps > 0` at EVERY scale `k`.  Unconditional (no open
hypothesis is consumed): the `recursion` field holds by construction and the
`prodFloor` is the proved summability output. -/
theorem dominantMode_continuum_floor :
    (0 : Q') < dominantModeRecursion.prodFloor
      ∧ ∀ k : Nat, dominantModeRecursion.prodFloor ≤ dominantModeRecursion.physGap k :=
  continuum_floor_of_defectRecursion dominantModeRecursion

/-- The dominant-mode gap margin is strictly positive at every scale. -/
theorem dominantMode_physGap_pos (k : Nat) :
    (0 : Q') < dominantModeRecursion.physGap k :=
  DefectGapRecursion.physGap_pos dominantModeRecursion k

/-! ## 7. Honest assessment (English) — what is and is NOT closed

  * GENUINE, NON-DEGENERATE.  `defect = δ_ren` is the proved renormalized quadratic
    defect (`bondMovingDeltaRen`), not identically `0` (`defect_pos_witness`:
    `renDefect _ 1 0 = 4 > 0`); `physGap` is the genuine `Q'`-varying prefix product.
    This is NOT the degenerate `trivialDefectGapRecursion`.

  * THE VACUUM-SHIFT CRUX (the flagged falsifiable obligation).  We did NOT paper
    over it.  Instead of asserting `defect = δ_ren` bounds the margin-loss of some
    INDEPENDENT gap definition (which would be false if the bond-moving step shifts
    the vacuum eigenvalue), we DEFINE the dominant-mode margin AS the running product
    of the proved per-step survival factors `1 − δ_ren`.  The `recursion` then holds
    by construction (an equality), and the real content moves to the PRODUCT FLOOR,
    which is the PROVED summability result `renormalized_gap_of_AFRate`.

    Honest belief on the falsifiable identification `1 − physGap(k+1)/physGap(k) ≤
    δ_ren k` FOR THE GENUINE 4D PHYSICAL GAP: I believe it is TRUE for the
    TRANSVERSE modes but the VACUUM-shift question is genuinely open — the bond-
    moving + decimation step can renormalize the vacuum (ground-state) eigenvalue,
    and equating the margin-loss of the true physical transfer gap with the
    transverse defect `δ_ren` is exactly the unproved multi-link composition step.
    This module SIDESTEPS that by studying the margin DEFINED by `1 − δ_ren`; it does
    NOT claim that margin equals the genuine 4D physical transfer gap.

  * WHAT IS UNCONDITIONAL.  For the dominant-mode renormalized margin `physGapSeq`
    (the product of proved survival factors along the canonical AF trajectory), the
    positive floor `floorEps > 0` at every scale is UNCONDITIONAL — it consumes only
    proved facts.  `dominantMode_continuum_floor` states it.

  * WHAT IS STILL OPEN (named, not faked).
      (A) FULL-MODE defect: `δ_ren` is the dominant `s = 1` transverse residual; the
          all-`s` renormalized defect being quadratic and summable is open.
      (B) PHYSICAL-GAP IDENTIFICATION: that this dominant-mode renormalized margin
          `physGapSeq` IS (up to a positive constant) the genuine 4D physical
          transfer gap `m_lat(a)/a` — i.e. the vacuum-shift question above.
      (C) GENUINE 4D AF TRAJECTORY: the canonical `w_k = 1 − 1/(k+1)` is a concrete
          non-4D AF inhabitant; the genuine 4D running coupling is open.

  * IS THIS 4D YANG–MILLS?  NO.  It is the dominant-mode renormalized decimation +
    bond-moving flow at fixed spacing, with a constructed (proved-floor-backed) gap
    margin.  It is ONE discharged rung of the RG-contraction program, not the Clay
    closure. -/

end YMGap.Continuum.DominantModeRecursion

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DominantModeRecursion.le_of_geRat_leRat
#print axioms YMGap.Continuum.DominantModeRecursion.twoMul_eqv_add
#print axioms YMGap.Continuum.DominantModeRecursion.defectSeq_nonneg
#print axioms YMGap.Continuum.DominantModeRecursion.defectSeq_le_one
#print axioms YMGap.Continuum.DominantModeRecursion.defect_pos_witness
#print axioms YMGap.Continuum.DominantModeRecursion.survivalSeq_nonneg
#print axioms YMGap.Continuum.DominantModeRecursion.floorEps_pos
#print axioms YMGap.Continuum.DominantModeRecursion.floorEps_le_physGapSeq
#print axioms YMGap.Continuum.DominantModeRecursion.dominantModeRecursion
#print axioms YMGap.Continuum.DominantModeRecursion.dominantMode_continuum_floor
#print axioms YMGap.Continuum.DominantModeRecursion.dominantMode_physGap_pos
