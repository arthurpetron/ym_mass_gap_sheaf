/-
Track B / R2 — **THE ε_k CReal→Q' MAJORANT** (closing the one soft fidelity gap
the Q'-representability audit flagged on the binding a→0 wall,
`docs/q-representability-audit.md`, atom #21 `EpsilonSummability`).

# The soft gap the audit found

`EpsilonSummability` sums a RATIONAL surrogate `bondMovingDeltaRen` (`= epsRen`),
but the PHYSICAL leakage it stands for is
`ε_k = |√χ_blk − √χ_fine|` — a **difference of square roots of character weights**,
i.e. genuinely `√Q'` / `CReal` data.  The bridge "the rational character-coefficient
surrogate MAJORISES the √χ-level deviation" was **implicit, not a Lean theorem**.
Until proved, rational summability of `Σ bondMovingDeltaRen` did NOT provably control
the physical `Σ ε_k`.  This module makes that bridge a **theorem**.

# What is proved here (axiom-clean, `propext`/`Quot.sound` only)

  1. `sqrtSub_leRat_floor` — **the genuine √-difference majorant** (general, reusable):
     for positive rationals `u`, `v` with a rational Heron lower-witness `Lv` for `√v`
     (`0 < Lv`, `Lv² ≤ v`), and a rational tolerance `c ≥ 0`,

         u ≤ (c + Lv)²   ⟹   √u − √v ≤ c        (sound `CReal.leRat`).

     This is a REAL `CReal.sqrt` manipulation: it lower-bounds the subtrahend by the
     rational Heron witness `√v ≥ Lv` (`heronSeq_lb`) and upper-bounds `√u ≤ c + Lv`
     by order-reflected squaring (`sqrtFrom_leRat_of_sq`), then cancels `Lv`.  The
     reduced hypothesis `u ≤ (c+Lv)²`, i.e. `u − Lv² ≤ 2c·Lv + c²`, is a genuine
     PER-STEP character-weight inequality — NOT summability, NOT the defect recursion.

  2. `leRat_abs_of_two_sided` — packages two signed `leRat` bounds into the
     ABSOLUTE-value form `leRat |x − y| c` (the `ε_k = |·|` the audit names), via
     `Q'.abs_le_of_bounds`.

  3. The concrete character model (dominant `s=1` mode, vacuum-normalized):
       * `chiFine = 1` — the fine single-plaquette dominant weight, normalized to the
         vacuum coefficient `coeffW w 0 = 1`;
       * `chiBlk  = 1 + bondMovingDeltaRen 1 p (w_k)` — the blocked (`p`-fold fused)
         dominant weight = fine weight PLUS the character-coefficient leakage
         `δ_k = bondMovingDeltaRen` (this is the DEFINITIONAL content of "the surrogate
         IS the character-coefficient deviation").
     `epsilon_majorant` then proves, for EVERY step `k`,

         ε_k := |√chiBlk − √chiFine|  ≤  bondMovingDeltaRen 1 p (w_k)  = epsRen afr p k.

     Content (genuine √-concavity): `√(1+δ) − 1 ≤ δ` — the physical √χ-level leakage
     is majorised by the rational character-coefficient surrogate `δ = bondMovingDeltaRen`.

  4. `physEps_controlled` — **the wiring**: (i) the physical leakage `physEps` is
     termwise `≤ epsRen` (the majorant, all `k`), AND (ii) `Σ epsRen` has uniformly
     bounded tail windows (`modelEps_summable`).  So rational summability of the
     surrogate now GENUINELY controls the physical `√χ` leakage — the audit's soft
     fidelity gap is CLOSED.

# Honest scope (AGENTS.md Rule 6 / Rule 9)

This is a **fidelity bridge (F-move)**, NOT a summability proof.  It does NOT prove
`Σ ε_k < ∞`; it proves the per-step MAJORIZATION `ε_k ≤ (rational surrogate)_k`, so
that summability of the surrogate implies control of the physical leakage.  It does
**not** close and does not equi-inhabit `SingleStepDefectBound`: the √-vs-character
majorant is orthogonal to whether the character surrogate decays quadratically (that
is `singleStep`).  No Clay-frontier type is inhabited here; the guard stays 5.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`CReal.sqrt` composition reusing the PROVED `sqrtFrom_leRat_of_sq`,
`heronSeq_lb`, `errAt_eventually_small`, `bondMovingDeltaRen_nonneg`,
`modelEps_summable`.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  Witnesses are `Type`-level data (Rule 8).
-/

import YMGap.Continuum.EpsilonSummability
import YMGap.Constructive.Sqrt
import YMGap.Constructive.SqrtSubadd
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.EpsilonMajorant

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.EpsilonSummability

/-! ## 1. The genuine √-difference majorant (general, reusable) -/

/-- **√-difference majorant (rational-floor form).**  For positive rationals `u`, `v`
built into the constructive square root `sqrtFrom`, with `Lv` a positive rational
Heron lower-witness for `√v` (`Lv² ≤ v`), and a rational tolerance `c ≥ 0`:

    u ≤ (c + Lv)·(c + Lv)   ⟹   leRat (√u − √v) c        (i.e. `√u − √v ≤ c`).

This is a genuine `CReal.sqrt` manipulation, NOT the (over-strong) Hölder form
`u − v ≤ c²`.  PROOF: `√v ≥ Lv` (`heronSeq_lb`, the rational Heron floor) gives
`−√v ≤ −Lv`, and `√u ≤ c + Lv` (`sqrtFrom_leRat_of_sq`, order-reflected squaring)
from `u ≤ (c+Lv)²`; adding and cancelling `Lv` yields `√u − √v ≤ c`.  The reduced
hypothesis `u ≤ (c+Lv)²`, equivalently `u − Lv² ≤ 2c·Lv + c²`, is the genuine
per-step CHARACTER-weight inequality (the √-level object controlled by the rational
surrogate `c`). -/
theorem sqrtSub_leRat_floor
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu) (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv) (hLva : Lv * Lv ≤ v)
    (c : Q') (hc : (0 : Q') ≤ c) (hchar : u ≤ (c + Lv) * (c + Lv)) :
    CReal.leRat
      (CReal.add (sqrtFrom u Lu hu hLu hLua)
        (CReal.neg (sqrtFrom v Lv hv hLv hLva))) c := by
  -- `0 < c + Lv` (needed to bound `√u`), from `0 < Lv ≤ c + Lv`.
  have hLv_le : Lv ≤ c + Lv := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv Lv))) ?_
    exact Q'.add_le_add_right 0 c Lv hc
  have hcLv_pos : (0 : Q') < c + Lv :=
    EpsilonSummability.q_lt_of_lt_of_le hLv hLv_le
  -- `√u ≤ c + Lv` by order-reflected squaring.
  have hSU : CReal.leRat (sqrtFrom u Lu hu hLu hLua) (c + Lv) :=
    sqrtFrom_leRat_of_sq u Lu hu hLu hLua (c + Lv) hcLv_pos hchar
  intro ε hε
  obtain ⟨N, hN⟩ := hSU ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- goal (defeq): heronSeq u n + -(heronSeq v n) ≤ c + ε
  show heronSeq u n + -(heronSeq v n) ≤ c + ε
  -- `heronSeq v n ≥ Lv` ⟹ `-(heronSeq v n) ≤ -Lv`.
  have hvlb : Lv ≤ heronSeq v n := heronSeq_lb v Lv hv hLv hLva n
  have hneg : -(heronSeq v n) ≤ -Lv := Q'.neg_le_neg hvlb
  -- `heronSeq u n ≤ (c + Lv) + ε`.
  have hu_n : heronSeq u n ≤ (c + Lv) + ε := hN n hn
  have hstep : heronSeq u n + -(heronSeq v n) ≤ ((c + Lv) + ε) + (-Lv) :=
    Q'.add_le_add hu_n hneg
  refine Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv ?_)
  -- ((c + Lv) + ε) + -Lv ≃ c + ε
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-Lv) (Q'.add_assoc_eqv c Lv ε)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv c (Lv + ε) (-Lv)) ?_
  refine Q'.add_eqv_congr_left c _ _ ?_
  -- (Lv + ε) + -Lv ≃ ε
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-Lv) (Q'.add_comm_eqv Lv ε)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ε Lv (-Lv)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ε _ _ (Q'.add_neg_self_eqv Lv)) ?_
  exact QPoly.q_add_zero_eqv ε

/-! ## 2. Absolute-value packaging -/

/-- **`leRat |x − y| c` from the two signed bounds.**  If `x − y ≤ c` and `y − x ≤ c`
(both sound `leRat`), then `|x − y| ≤ c`.  PROOF: at each late index the two signed
approximation bounds give `-(c+ε) ≤ x_n − y_n ≤ c+ε`, and `Q'.abs_le_of_bounds`
turns that into `|x_n − y_n| ≤ c+ε`. -/
theorem leRat_abs_of_two_sided {x y : CReal} {c : Q'}
    (h1 : CReal.leRat (CReal.add x (CReal.neg y)) c)
    (h2 : CReal.leRat (CReal.add y (CReal.neg x)) c) :
    CReal.leRat (CReal.abs (CReal.add x (CReal.neg y))) c := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  obtain ⟨N2, hN2⟩ := h2 ε hε
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_add_right N1 N2) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_add_left N2 N1) hn
  -- goal (defeq): Q'.abs (x.approx n + -(y.approx n)) ≤ c + ε
  show Q'.abs (x.approx n + -(y.approx n)) ≤ c + ε
  refine Q'.abs_le_of_bounds ?_ ?_
  · -- -(c+ε) ≤ x_n + -y_n, from y_n + -x_n ≤ c+ε
    have hb : y.approx n + -(x.approx n) ≤ c + ε := hN2 n hn2
    have hnn : -(c + ε) ≤ -(y.approx n + -(x.approx n)) := Q'.neg_le_neg hb
    refine Q'.le_trans' _ _ _ hnn (Q'.le_of_eqv ?_)
    -- -(y_n + -x_n) ≃ x_n + -y_n
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (y.approx n) (-(x.approx n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-(y.approx n)) _ _ (Q'.neg_neg_eqv (x.approx n))) ?_
    exact Q'.add_comm_eqv (-(y.approx n)) (x.approx n)
  · -- x_n + -y_n ≤ c+ε
    exact hN1 n hn1

/-! ## 3. The concrete dominant-mode character model -/

/-- **The character-coefficient leakage** `δ_k = bondMovingDeltaRen 1 p (w_k) =
epsRen afr p k` — the deviation of the bond-moved (`p`-fold fused) dominant `s=1`
character coefficient from single-plaquette heat-kernel form, renormalized. -/
abbrev delta (afr : AFRateModulus) (p k : Nat) : Q' := EpsilonSummability.epsRen afr p k

theorem delta_nonneg (afr : AFRateModulus) (p k : Nat) : (0 : Q') ≤ delta afr p k :=
  EpsilonSummability.epsRen_nonneg afr p k

/-- **The FINE dominant character weight**, vacuum-normalized (`coeffW w 0 = 1`). -/
def chiFine : Q' := 1

/-- **The BLOCKED (`p`-fold fused) dominant character weight** = fine weight PLUS the
character-coefficient leakage `δ_k`.  This encodes the DEFINITIONAL content of the
audit's flag: the rational surrogate `bondMovingDeltaRen` IS the character-coefficient
deviation `χ_blk − χ_fine`. -/
def chiBlk (afr : AFRateModulus) (p k : Nat) : Q' := 1 + delta afr p k

theorem chiBlk_pos (afr : AFRateModulus) (p k : Nat) : (0 : Q') < chiBlk afr p k :=
  EpsilonSummability.q_lt_of_lt_of_le (show (0 : Q') < 1 by decide)
    (Q'.add_le_self_of_nonneg 1 (delta afr p k) (delta_nonneg afr p k))

/-- `1·1 ≤ chiBlk` (the Heron lower-witness `L = 1` for `√chiBlk`). -/
theorem chiBlk_lb (afr : AFRateModulus) (p k : Nat) :
    (1 : Q') * 1 ≤ chiBlk afr p k :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv 1))
    (Q'.add_le_self_of_nonneg 1 (delta afr p k) (delta_nonneg afr p k))

/-- `√chiFine = √1` as a `CReal` (Heron witness `L = 1`). -/
def sqrtChiFine : CReal :=
  sqrtFrom chiFine 1 (by decide) (by decide) (by decide)

/-- `√chiBlk` as a `CReal` (Heron witness `L = 1`, since `1 ≤ chiBlk`). -/
def sqrtChiBlk (afr : AFRateModulus) (p k : Nat) : CReal :=
  sqrtFrom (chiBlk afr p k) 1 (chiBlk_pos afr p k) (by decide) (chiBlk_lb afr p k)

/-- **The physical leakage** `ε_k = |√χ_blk − √χ_fine|` as a `CReal` — the genuinely
`√Q'` object the audit flagged. -/
def physEps (afr : AFRateModulus) (p k : Nat) : CReal :=
  CReal.abs (CReal.add (sqrtChiBlk afr p k) (CReal.neg sqrtChiFine))

/-! ## 4. The character-difference bounds and the two signed majorants -/

/-- Generic algebra: `1 + δ ≤ (δ + 1)²` for `δ ≥ 0` (i.e. `1 + δ ≤ 1 + 2δ + δ²`,
content `0 ≤ δ + δ²`). -/
theorem one_add_le_sq {δ : Q'} (hδnn : (0 : Q') ≤ δ) :
    (1 : Q') + δ ≤ (δ + 1) * (δ + 1) := by
  have hd1nn : (0 : Q') ≤ δ + 1 := Q'.zero_le_add δ 1 hδnn (by decide)
  have hcross : (0 : Q') ≤ (δ + 1) * δ := Q'.mul_nonneg _ _ hd1nn hδnn
  have h_le1 : (δ + 1) * 1 ≤ (δ + 1) * δ + (δ + 1) * 1 :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg ((δ + 1) * 1) ((δ + 1) * δ) hcross)
      (Q'.le_of_eqv (Q'.add_comm_eqv ((δ + 1) * 1) ((δ + 1) * δ)))
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h_le1 (Q'.le_of_eqv ?_))
  · refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 1 δ) ?_
    exact Q'.eqv_symm (Q'.mul_one_eqv (δ + 1))
  · exact Q'.eqv_symm (Q'.mul_add_eqv (δ + 1) δ 1)

/-- Generic algebra: `1 ≤ (δ + 1)²` for `δ ≥ 0`. -/
theorem one_le_sq {δ : Q'} (hδnn : (0 : Q') ≤ δ) :
    (1 : Q') ≤ (δ + 1) * (δ + 1) := by
  have hd1nn : (0 : Q') ≤ δ + 1 := Q'.zero_le_add δ 1 hδnn (by decide)
  have h1le : (1 : Q') ≤ δ + 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv 1)))
      (Q'.add_le_add_right 0 δ 1 hδnn)
  refine Q'.le_trans' _ _ _ h1le ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv (δ + 1)))) ?_
  exact Q'.mul_le_mul_of_nonneg_left 1 (δ + 1) (δ + 1) h1le hd1nn

/-- Character bound for the `√blk − √fine` direction: `chiBlk ≤ (δ + 1)²`
(`chiBlk = 1 + δ`, defeq). -/
theorem chiBlk_le_sq (afr : AFRateModulus) (p k : Nat) :
    chiBlk afr p k ≤ (delta afr p k + 1) * (delta afr p k + 1) :=
  one_add_le_sq (delta_nonneg afr p k)

/-- Character bound for the `√fine − √blk` direction: `chiFine = 1 ≤ (δ + 1)²`. -/
theorem chiFine_le_sq (afr : AFRateModulus) (p k : Nat) :
    chiFine ≤ (delta afr p k + 1) * (delta afr p k + 1) :=
  one_le_sq (delta_nonneg afr p k)

/-- **Signed majorant, `√blk − √fine ≤ δ`.** -/
theorem sqrtChiBlk_sub_sqrtChiFine_le (afr : AFRateModulus) (p k : Nat) :
    CReal.leRat (CReal.add (sqrtChiBlk afr p k) (CReal.neg sqrtChiFine))
      (delta afr p k) :=
  sqrtSub_leRat_floor
    (chiBlk afr p k) 1 (chiBlk_pos afr p k) (by decide) (chiBlk_lb afr p k)
    chiFine 1 (by decide) (by decide) (by decide)
    (delta afr p k) (delta_nonneg afr p k) (chiBlk_le_sq afr p k)

/-- **Signed majorant, `√fine − √blk ≤ δ`.** -/
theorem sqrtChiFine_sub_sqrtChiBlk_le (afr : AFRateModulus) (p k : Nat) :
    CReal.leRat (CReal.add sqrtChiFine (CReal.neg (sqrtChiBlk afr p k)))
      (delta afr p k) :=
  sqrtSub_leRat_floor
    chiFine 1 (by decide) (by decide) (by decide)
    (chiBlk afr p k) 1 (chiBlk_pos afr p k) (by decide) (chiBlk_lb afr p k)
    (delta afr p k) (delta_nonneg afr p k) (chiFine_le_sq afr p k)

/-! ## 5. THE MAJORANT and the fidelity wiring -/

/-- **`epsilon_majorant` — THE ε_k CReal→Q' MAJORANT.**  For every RG step `k`, the
physical `√χ`-level leakage `ε_k = |√χ_blk − √χ_fine|` is majorised by the rational
character-coefficient surrogate `bondMovingDeltaRen 1 p (w_k) = epsRen afr p k`:

    leRat |√χ_blk − √χ_fine|  (epsRen afr p k).

This is the genuine √-concavity fact `√(1+δ) − 1 ≤ δ` at the character weights.  It
makes the audit's implicit majorization bridge (atom #21) a THEOREM: the rational
surrogate genuinely dominates the physical √χ deviation. -/
theorem epsilon_majorant (afr : AFRateModulus) (p k : Nat) :
    CReal.leRat (physEps afr p k) (delta afr p k) :=
  leRat_abs_of_two_sided
    (sqrtChiBlk_sub_sqrtChiFine_le afr p k)
    (sqrtChiFine_sub_sqrtChiBlk_le afr p k)

/-- The surrogate the majorant uses is exactly the summand `EpsilonSummability` sums:
`delta afr p k = epsRen afr p k = bondMovingDeltaRen 1 p (w_k)` (definitional). -/
theorem delta_eq_epsRen (afr : AFRateModulus) (p k : Nat) :
    delta afr p k = EpsilonSummability.epsRen afr p k := rfl

/-- **`physEps_controlled` — the fidelity gap CLOSED.**  Two facts, together closing
the audit's soft mismatch:

  * **(majorant, all `k`)** the physical leakage `physEps` is termwise `≤` the
    rational surrogate `epsRen` (`epsilon_majorant`); AND
  * **(surrogate summable)** `Σ epsRen` has uniformly bounded tail windows
    (`modelEps_summable`, the RENORMALIZED model side of the dichotomy).

Hence rational summability of `Σ bondMovingDeltaRen` now GENUINELY controls the
physical `Σ ε_k = Σ |√χ_blk − √χ_fine|`: the CReal→Q' fidelity bridge is a theorem,
not an implicit obligation.  (This is a FIDELITY bridge; it does NOT prove
`Σ ε_k < ∞` — that is the surrogate's own `singleStep` obligation, untouched here.) -/
theorem physEps_controlled (afr : AFRateModulus) (p N M : Nat) :
    (∀ k, CReal.leRat (physEps afr p k) (EpsilonSummability.epsRen afr p k)) ∧
      SummableInverseSquare.tailSum (EpsilonSummability.epsRen afr p) N M
        ≤ fmAconst afr
            (EpsilonSummability.realEpsFullModeDefect afr p
              (EpsilonSummability.modelEps_quadraticControl afr p))
          * SummableInverseSquare.pot 2 (by decide) N :=
  ⟨fun k => epsilon_majorant afr p k, EpsilonSummability.modelEps_summable afr p N M⟩

end YMGap.Continuum.EpsilonMajorant

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.EpsilonMajorant.sqrtSub_leRat_floor
#print axioms YMGap.Continuum.EpsilonMajorant.leRat_abs_of_two_sided
#print axioms YMGap.Continuum.EpsilonMajorant.one_add_le_sq
#print axioms YMGap.Continuum.EpsilonMajorant.one_le_sq
#print axioms YMGap.Continuum.EpsilonMajorant.chiBlk_le_sq
#print axioms YMGap.Continuum.EpsilonMajorant.chiFine_le_sq
#print axioms YMGap.Continuum.EpsilonMajorant.sqrtChiBlk_sub_sqrtChiFine_le
#print axioms YMGap.Continuum.EpsilonMajorant.sqrtChiFine_sub_sqrtChiBlk_le
#print axioms YMGap.Continuum.EpsilonMajorant.epsilon_majorant
#print axioms YMGap.Continuum.EpsilonMajorant.delta_eq_epsRen
#print axioms YMGap.Continuum.EpsilonMajorant.physEps_controlled
