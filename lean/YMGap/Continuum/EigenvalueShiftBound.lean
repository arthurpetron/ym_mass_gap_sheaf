/-
Track B / R2 — CLAY CORE INPUT (1): the real 4D SU(2) block-spin per-step
dimensionless-margin EROSION `ε_k` made CONCRETE, and PROVED bounded by the
multiplicity-blind eigenvalue shift `w_{k+1}³ − w_k³` (Route I's `EigenvalueShiftDefect`).

# What Route I / AnchorDominance left as the open node

`RouteIEigenvalueDefect.EigenvalueShiftDefect afr` carries `eigShift : Nat → Q'` as
a FREE field with the open bound `eigShift k ≤ 6·(1 − w_k)²`.  As a bare structure it
is VACUOUSLY inhabitable (`eigShift := 0`) — exactly the free-field caveat the CAPSTONE
flags for every frontier atom.  Its GENUINE content is realized only when `eigShift` is
PINNED to the real coupling-flow eigenvalue shift `w_{k+1}³ − w_k³`, with the bound a
THEOREM about that concrete object.  This module does exactly that.

# The erosion decomposition (Routes I / E / D, adversarial)

The real per-step erosion of the multiplicity-blind gap edge `eigA w 1 = w³` decomposes
into three structural pieces plus a NAMED back-reaction residual:

    ε_k  =  (fusion defect, = 0 : `eigA_fusedDefect_eqv_zero`)
          + (coupling-flow eigenvalue shift  w_{k+1}³ − w_k³ : Route I)
          + (large-field correction  ≤ K·r^k : Route E `LargeFieldSuppression`)
          + (non-abelian back-reaction : the OPEN form-preservation residual).

Route I proved the fusion (degeneracy) defect of the DECAY-RATE eigenvalue is `0` (the
degeneracy `2 → 4` is amplitude, not rate).  Route E proved the large-field half is
geometrically summable.  The honest CRUX (§5): the non-abelian back-reaction (higher-rep
mixing, multi-plaquette, commutator terms — the classic Bałaban difficulty) is NOT a
separate additive term in the multiplicity-blind eigenvalue *provided* the coarse action
stays in single-coupling heat-kernel character form — it is reabsorbed into the flowing
renormalized coupling `w_{k+1}`.  That form-preservation is the named residual
`SingleCouplingFormPreservation` (= `RouteF.TransferCharacterCorrespondence`'s open
form-preservation field), the genuine remaining 4D content.

# What is PROVED here (axiom-clean `Q'`/`Nat`)

  * `cube_diff_le_three` — the cube-difference bound `0 ≤ a ≤ b ≤ 1 ⟹ b³ − a³ ≤ 3(b−a)`,
    via the exact split `b³−a³ = b(b²−a²) + a²(b−a)` (each factor bounded).  sympy-exact +
    mpmath dps 50 (`input1_numerics.py §1–2`; sharp at the free fixed point `a=b=1`).
  * `cube_diff_le_envelope` — the per-step eigShift bound `b−a ≤ 2(1−a)² ⟹ b³−a³ ≤ 6(1−a)²`
    (the `β ≤ 2` two-loop AF step ⟹ the transverse-quadratic envelope, `mpmath §3`).
  * `eigenvalueShiftDefect_of_betaStep` — the CONCRETE conditional producer: from a named
    two-loop AF `AFBetaStep afr` (monotone flow + `β ≤ 2` step), builds
    `EigenvalueShiftDefect afr` with `eigShift := AnchorDominance.eigShiftSeq afr.w` — the
    REAL eigenvalue shift, NOT a free field.  Open binder on `AFBetaStep`, so guard-safe.
  * `realErosion_le_shift_plus_largeField` — the erosion decomposition bound: the
    constructed real erosion `ε_k = eigShiftSeq + δLF_k` obeys `ε_k ≤ (w_{k+1}³−w_k³) + K·r^k`.
  * `formPreserved_perStep` — combining form-preservation + the β-step: the real erosion
    obeys the full per-step decomposition `ε_k ≤ 6(1−w_k)² + K·r^k`.
  * `afBetaStep_mono_canonical` / `invSucc_antitone` — SATISFIABILITY (monotone half) of the
    named β-step input on the canonical AF trajectory `w_k = 1 − 1/(k+1)`; the β-step half
    is sympy-exact `2(1−w)² − step = (k+3)/((k+1)²(k+2)) ≥ 0` (`§4`).

# HONEST VERDICT (AGENTS.md Rule 6/9)

  * `EigenvalueShiftDefect` is a NODE, NOT one of the five guarded frontier types.  It does
    NOT cascade to a guarded bundle by any EXISTING lemma (`eigShift_to_fullRange` reaches
    only `FullRangeFusedDefect`, itself a free-field node with NO existing producer of
    `SingleStepDefectBound`).  No STOP condition tripped; no guarded bundle inhabited.
  * The producer is CONDITIONAL (open binder on `AFBetaStep`).  The β-step is a GENUINE
    extra input: NOT derivable from `AFRateModulus`'s two-sided `1/k` rate — the band with
    `A ≠ A'` admits a step of order `1/k ≫ 2(1−w)² ∼ 1/k²` (`§5`, explicit `k=8`
    counterexample).  So no unconditional inhabitant of `EigenvalueShiftDefect afr` exists
    from `afr` alone.
  * The eigenvalue-shift + large-field are the COMPLETE erosion of the multiplicity-blind
    gap edge ONLY MODULO single-coupling form-preservation (§5).  The residual
    back-reaction is NAMED, not faked or absorbed by fiat.  Input (1) is CONCRETE, its
    per-step bound PROVED, and reduced to two genuine 4D inputs: the two-loop β-step and
    single-coupling form-preservation.  The 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only
`decide` on closed decidable `Q'` facts), no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.RouteIEigenvalueDefect
import YMGap.Continuum.AnchorDominanceEigenvalueShift
import YMGap.Continuum.LargeFieldSuppression

namespace YMGap.Continuum.EigenvalueShiftBound

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.AnchorDominance
open YMGap.Continuum.RouteIEigenvalueDefect
open YMGap.Continuum.LargeFieldSuppression

/-! ## 0. Generic mid-cancellation for four `Q'` summands. -/

/-- `(B + C) ≃ 0 → ((A + B) + (C + D)) ≃ (A + D)`.  Pure `Q'` add algebra
(`add_comm` on the inner pair, `q_interchange`, then the vanishing pair). -/
theorem cancel_mid (A B C D : Q') (h : (B + C).eqv 0) :
    ((A + B) + (C + D)).eqv (A + D) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (A + B) (C + D) (D + C) (Q'.add_comm_eqv C D)) ?_
  refine Q'.eqv_trans _ _ _ (QPoly.q_interchange A B D C) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (A + D) (B + C) 0 h) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (A + D))

/-! ## 1. Elementary `Q'` square bounds. -/

/-- `0 ≤ a → a ≤ 1 → a·a ≤ 1`. -/
theorem sq_le_one {a : Q'} (ha : (0 : Q') ≤ a) (ha1 : a ≤ (1 : Q')) : a * a ≤ (1 : Q') := by
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg ha1 ha1 (by decide) ha) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv 1)

/-- `0 ≤ a → a ≤ b → a·a ≤ b·b`. -/
theorem sq_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) : a * a ≤ b * b :=
  Q'.mul_le_mul_of_nonneg hab hab (Q'.le_trans' _ _ _ ha hab) ha

/-! ## 2. Difference-of-squares factorization and bound. -/

/-- **Difference of squares (exact).**  `b·b − a·a ≃ (b − a)·(b + a)`. -/
theorem sqDiff_factor (a b : Q') :
    (b * b + -(a * a)).eqv ((b + -a) * (b + a)) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv b (-a) (b + a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_add_eqv b b a) (Q'.mul_add_eqv (-a) b a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((b * b) + (b * a)) ((-a) * b + (-a) * a)
      ((-(a * b)) + (-(a * a)))
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv a b) (Q'.neg_mul_eqv a a))) ?_
  refine cancel_mid (b * b) (b * a) (-(a * b)) (-(a * a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (b * a) (a * b) (-(a * b)) (Q'.mul_comm_eqv b a)) ?_
  exact Q'.add_neg_self_eqv (a * b)

/-- **Difference-of-squares bound.**  `0 ≤ a ≤ b ≤ 1 ⟹ b·b − a·a ≤ 2(b − a)`. -/
theorem sqDiff_le {a b : Q'} (_ha : (0 : Q') ≤ a) (hab : a ≤ b)
    (hb1 : b ≤ (1 : Q')) (ha1 : a ≤ (1 : Q')) :
    (b * b + -(a * a)) ≤ Q'.ofNat 2 * (b + -a) := by
  have hsub0 : (0 : Q') ≤ b + -a := qZeroLeSub hab
  have hba2 : b + a ≤ Q'.ofNat 2 := by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right b 1 a hb1) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 a 1 ha1) ?_
    exact (by decide : (1 : Q') + 1 ≤ Q'.ofNat 2)
  have hmul : (b + -a) * (b + a) ≤ (b + -a) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left (b + a) (Q'.ofNat 2) (b + -a) hba2 hsub0
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sqDiff_factor a b)) ?_
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_comm_eqv (b + -a) (Q'.ofNat 2)))

/-! ## 3. The cube-difference bounds — THE real math. -/

/-- **Cube split (exact).**  `b·(b·b) − a·(a·a) ≃ b·(b·b − a·a) + (a·a)·(b − a)`. -/
theorem cubeSplit_factor (a b : Q') :
    (b * (b * b) + -(a * (a * a))).eqv
      (b * (b * b + -(a * a)) + (a * a) * (b + -a)) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_add_eqv b (b * b) (-(a * a)))
      (Q'.mul_add_eqv (a * a) b (-a))) ?_
  refine Q'.eqv_trans _ _ _
    (cancel_mid (b * (b * b)) (b * (-(a * a))) ((a * a) * b) ((a * a) * (-a)) ?_) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_neg_eqv b (a * a)) (Q'.mul_comm_eqv (a * a) b)) ?_
    exact Q'.neg_add_self_eqv (b * (a * a))
  · refine Q'.add_eqv_congr_left (b * (b * b)) ((a * a) * (-a)) (-(a * (a * a))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (a * a) a) ?_
    exact Q'.neg_eqv_congr ((a * a) * a) (a * (a * a)) (Q'.mul_assoc_eqv a a a)

/-- **THE CUBE-DIFFERENCE BOUND.**  `0 ≤ a ≤ b ≤ 1 ⟹ b³ − a³ ≤ 3(b − a)`
(`qcube x = x·(x·x)`).  Split `b³−a³ = b(b²−a²) + a²(b−a)`, bound `b ≤ 1`,
`b²−a² ≤ 2(b−a)`, `a² ≤ 1`.  Sharp at `a = b = 1`. -/
theorem cube_diff_le_three {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b)
    (hb1 : b ≤ (1 : Q')) :
    qcube b - qcube a ≤ Q'.ofNat 3 * (b - a) := by
  have ha1 : a ≤ (1 : Q') := Q'.le_trans' _ _ _ hab hb1
  have hsub0 : (0 : Q') ≤ b + -a := qZeroLeSub hab
  have hsq : (b * b + -(a * a)) ≤ Q'.ofNat 2 * (b + -a) := sqDiff_le ha hab hb1 ha1
  have hsq0 : (0 : Q') ≤ b * b + -(a * a) := qZeroLeSub (sq_mono ha hab)
  have ht1 : b * (b * b + -(a * a)) ≤ Q'.ofNat 2 * (b + -a) := by
    have h := Q'.mul_le_mul_of_nonneg hb1 hsq (by decide) hsq0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have ht2 : (a * a) * (b + -a) ≤ (b + -a) := by
    have hle1 : a * a ≤ (1 : Q') := sq_le_one ha ha1
    have h := Q'.mul_le_mul_of_nonneg_right (a * a) 1 (b + -a) hle1 hsub0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hsum : b * (b * b + -(a * a)) + (a * a) * (b + -a)
      ≤ Q'.ofNat 2 * (b + -a) + (b + -a) := q_add_le_add ht1 ht2
  have hcollapse : (Q'.ofNat 2 * (b + -a) + (b + -a)).eqv (Q'.ofNat 3 * (b + -a)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ ((1 : Q') * (b + -a))
        (Q'.eqv_symm (Q'.one_mul_eqv (b + -a)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 2) (1 : Q') (b + -a))) ?_
    exact Q'.mul_eqv_congr_right _ _ (b + -a) (by decide)
  show (b * (b * b) + -(a * (a * a))) ≤ Q'.ofNat 3 * (b + -a)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (cubeSplit_factor a b)) ?_
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcollapse)

/-- The envelope-scalar identity `3·(2·x) ≃ 6·x`. -/
theorem three_two_eqv (x : Q') : (Q'.ofNat 3 * (Q'.ofNat 2 * x)).eqv (Q'.ofNat 6 * x) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 3) (Q'.ofNat 2) x)) ?_
  exact Q'.mul_eqv_congr_right _ _ x (by decide)

/-- The structure-envelope scalar identity `1·(dimQ 1·(3·x)) ≃ 6·x` (`dimQ 1 = 2`). -/
theorem env_eqv (x : Q') :
    (Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 * x))).eqv (Q'.ofNat 6 * x) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ 1) (Q'.ofNat 3) x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 1) (dimQ 1 * Q'.ofNat 3) x)) ?_
  exact Q'.mul_eqv_congr_right _ _ x (by decide)

/-- **THE PER-STEP EIGSHIFT BOUND.**  `0 ≤ a ≤ b ≤ 1` and the two-loop AF step
`b − a ≤ 2(1−a)²` ⟹ `b³ − a³ ≤ 6(1−a)²`.  Composes `cube_diff_le_three` with the
β-step and `three_two_eqv`.  `mpmath dps 50 §3`. -/
theorem cube_diff_le_envelope {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b)
    (hb1 : b ≤ (1 : Q'))
    (hstep : b - a ≤ Q'.ofNat 2 * (((1 : Q') - a) * ((1 : Q') - a))) :
    qcube b - qcube a ≤ Q'.ofNat 6 * (((1 : Q') - a) * ((1 : Q') - a)) := by
  refine Q'.le_trans' _ _ _ (cube_diff_le_three ha hab hb1) ?_
  have h := Q'.mul_le_mul_of_nonneg_left (b - a)
    (Q'.ofNat 2 * (((1 : Q') - a) * ((1 : Q') - a))) (Q'.ofNat 3) hstep (by decide)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (three_two_eqv _))

/-! ## 4. The named two-loop AF β-step input, and the CONCRETE producer. -/

/-- **`AFBetaStep afr` — the named two-loop AF running-rate input (`Type`, Rule 6a).**
The AF coupling flow is monotone and its per-step increment obeys the two-loop
`β ≤ 2` transverse-quadratic rate `w_{n+1} − w_n ≤ 2(1 − w_n)²`.  This is the standard
asymptotic-freedom two-loop prediction — a GENUINE physics input, strictly smaller than
the opaque `eigShiftBound`, and NOT derivable from `AFRateModulus`'s two-sided `1/k` band
(§5).  Satisfiable on the canonical trajectory (`afBetaStep_mono_canonical` + sympy). -/
structure AFBetaStep (afr : AFRateModulus) : Type where
  /-- The AF flow is monotone increasing toward the free fixed point. -/
  mono : ∀ n, afr.w n ≤ afr.w (n + 1)
  /-- The two-loop `β ≤ 2` per-step transverse-quadratic increment bound. -/
  betaStep : ∀ n, afr.w (n + 1) - afr.w n
      ≤ Q'.ofNat 2 * (((1 : Q') - afr.w n) * ((1 : Q') - afr.w n))

/-- **`eigenvalueShiftDefect_of_betaStep` — THE CONCRETE CONDITIONAL PRODUCER.**
From a named two-loop AF `AFBetaStep afr`, build `EigenvalueShiftDefect afr` with
`eigShift := AnchorDominance.eigShiftSeq afr.w` — the REAL multiplicity-blind coupling-flow
eigenvalue shift `w_{k+1}³ − w_k³`, NOT a free field.  `eigShift_nonneg` from cube
monotonicity; `eigShiftBound` from `cube_diff_le_envelope`.  Open binder on `AFBetaStep`,
so it does NOT unconditionally inhabit `EigenvalueShiftDefect` (guard-safe Rule-6a
reduction): it reduces the free-field bound to the sharp named β-step input. -/
def eigenvalueShiftDefect_of_betaStep {afr : AFRateModulus} (S : AFBetaStep afr) :
    EigenvalueShiftDefect afr where
  eigShift k := eigShiftSeq afr.w (afCutoff afr + k)
  eigShift_nonneg k :=
    AnchorDominance.eigShift_nonneg afr.w afr.w_nonneg S.mono (afCutoff afr + k)
  eigShiftBound k := by
    have ha : (0 : Q') ≤ afr.w (afCutoff afr + k) := afr.w_nonneg (afCutoff afr + k)
    have hab : afr.w (afCutoff afr + k) ≤ afr.w (afCutoff afr + k + 1) := S.mono (afCutoff afr + k)
    have hb1 : afr.w (afCutoff afr + k + 1) ≤ (1 : Q') :=
      Q'.le_of_lt (afr.w_lt_one (afCutoff afr + k + 1))
    have hstep : afr.w (afCutoff afr + k + 1) - afr.w (afCutoff afr + k)
        ≤ Q'.ofNat 2 * (((1 : Q') - afr.w (afCutoff afr + k))
            * ((1 : Q') - afr.w (afCutoff afr + k))) := S.betaStep (afCutoff afr + k)
    have hcube := cube_diff_le_envelope ha hab hb1 hstep
    refine Q'.le_trans' _ _ _ hcube ?_
    exact Q'.le_of_eqv (Q'.eqv_symm
      (env_eqv (((1 : Q') - afr.w (afCutoff afr + k)) * ((1 : Q') - afr.w (afCutoff afr + k)))))

/-! ## 5. The erosion decomposition and the named form-preservation residual. -/

/-- The CONCRETE constructed real erosion `ε_k = eigShiftSeq + δLF_k` (eigenvalue shift +
Route-E large-field). -/
def realErosion {afr : AFRateModulus} (L : LargeFieldSuppression afr) (k : Nat) : Q' :=
  eigShiftSeq afr.w (afCutoff afr + k) + L.largeFieldDefect k

/-- **The erosion decomposition bound.**  `ε_k ≤ (w_{k+1}³ − w_k³) + K·r^k` — the
constructed erosion is the real eigenvalue shift plus the geometric large-field bound. -/
theorem realErosion_le_shift_plus_largeField {afr : AFRateModulus}
    (L : LargeFieldSuppression afr) (k : Nat) :
    realErosion L k ≤ eigShiftSeq afr.w (afCutoff afr + k) + L.K * qpow L.r k :=
  Q'.add_le_add_left _ _ _ (L.lf_geom k)

/-- **`SingleCouplingFormPreservation afr` — the NAMED back-reaction residual (Rule 6a;
free-field caveat).**  The honest CRUX: the real multiplicity-blind per-step erosion
`realErosion k` is bounded by the single-coupling eigenvalue shift plus the large-field
correction — i.e. the non-abelian back-reaction is reabsorbed into the flowing coupling
`w_{k+1}` and carries NO separate additive term.  This is the Bałaban form-preservation
(the coarse action stays single-coupling heat-kernel form) = `RouteF`'s open
`TransferCharacterCorrespondence` content.  UNINHABITED for the real 4D flow. -/
structure SingleCouplingFormPreservation (afr : AFRateModulus) : Type where
  /-- The Route-E large-field data. -/
  L : LargeFieldSuppression afr
  /-- The real multiplicity-blind per-step block-spin erosion of the true margin. -/
  realErosion : Nat → Q'
  /-- The real erosion is nonnegative. -/
  realErosion_nonneg : ∀ k, (0 : Q') ≤ realErosion k
  /-- **Form-preservation** — no separate additive non-abelian back-reaction. -/
  formPreserved : ∀ k, realErosion k
      ≤ eigShiftSeq afr.w (afCutoff afr + k) + L.largeFieldDefect k

/-- **`formPreserved_perStep` — the full per-step erosion decomposition.**  Given
form-preservation (`F`) and the two-loop β-step (`S`), the real erosion obeys
`ε_k ≤ 6(1−w_k)² + K·r^k` — the eigenvalue-shift envelope plus the geometric large-field
budget.  This is the concrete per-step bound of the constructed real erosion. -/
theorem formPreserved_perStep {afr : AFRateModulus}
    (F : SingleCouplingFormPreservation afr) (S : AFBetaStep afr) (k : Nat) :
    F.realErosion k
      ≤ Q'.ofNat 6 * (((1 : Q') - afr.w (afCutoff afr + k))
            * ((1 : Q') - afr.w (afCutoff afr + k)))
        + F.L.K * qpow F.L.r k := by
  have ha : (0 : Q') ≤ afr.w (afCutoff afr + k) := afr.w_nonneg (afCutoff afr + k)
  have hab : afr.w (afCutoff afr + k) ≤ afr.w (afCutoff afr + k + 1) := S.mono (afCutoff afr + k)
  have hb1 : afr.w (afCutoff afr + k + 1) ≤ (1 : Q') :=
    Q'.le_of_lt (afr.w_lt_one (afCutoff afr + k + 1))
  have hstep : afr.w (afCutoff afr + k + 1) - afr.w (afCutoff afr + k)
      ≤ Q'.ofNat 2 * (((1 : Q') - afr.w (afCutoff afr + k))
          * ((1 : Q') - afr.w (afCutoff afr + k))) := S.betaStep (afCutoff afr + k)
  have hshift : eigShiftSeq afr.w (afCutoff afr + k)
      ≤ Q'.ofNat 6 * (((1 : Q') - afr.w (afCutoff afr + k))
            * ((1 : Q') - afr.w (afCutoff afr + k))) := cube_diff_le_envelope ha hab hb1 hstep
  refine Q'.le_trans' _ _ _ (F.formPreserved k) ?_
  exact q_add_le_add hshift (F.L.lf_geom k)

/-! ## 6. SATISFIABILITY of the named β-step input (canonical trajectory). -/

/-- The canonical inverse-successor `1/(k+1)` is antitone: `invSucc (n+1) ≤ invSucc n`. -/
theorem invSucc_antitone (n : Nat) : Q'.invSucc (n + 1) ≤ Q'.invSucc n := by
  show (Q'.invSucc (n + 1)).num * ((Q'.invSucc n).den : Int)
      ≤ (Q'.invSucc n).num * ((Q'.invSucc (n + 1)).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_num, Q'.invSucc_den, Q'.invSucc_den]
  push_cast; omega

/-- **SATISFIABILITY (monotone half).**  The canonical AF trajectory `w_k = 1 − 1/(k+1)`
(`afRateModulus_canonical.w`) is monotone increasing.  Together with the sympy-exact β-step
identity `2(1−w)² − (w_{n+1}−w_n) = (n+3)/((n+1)²(n+2)) ≥ 0` (`input1_numerics.py §4`), the
named `AFBetaStep` input is SATISFIABLE — not vacuous, not unsatisfiable. -/
theorem afBetaStep_mono_canonical (n : Nat) :
    afRateModulus_canonical.w n ≤ afRateModulus_canonical.w (n + 1) := by
  show (1 : Q') - Q'.invSucc n ≤ (1 : Q') - Q'.invSucc (n + 1)
  have hneg : -(Q'.invSucc n) ≤ -(Q'.invSucc (n + 1)) := Q'.neg_le_neg (invSucc_antitone n)
  exact Q'.add_le_add_left 1 _ _ hneg

/-! ## 7. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **PROVED (axiom-clean):** `cube_diff_le_three`, `cube_diff_le_envelope` (the real
cube-difference math); `eigenvalueShiftDefect_of_betaStep` (the concrete conditional
producer pinning `eigShift` to the real eigenvalue shift `w_{k+1}³−w_k³`);
`realErosion_le_shift_plus_largeField` / `formPreserved_perStep` (the erosion
decomposition); `afBetaStep_mono_canonical` (satisfiability, monotone half).

**VERDICT.**  Clay core input (1) is now CONCRETE: the erosion `ε_k` is PINNED to the
real multiplicity-blind coupling-flow eigenvalue shift `eigShiftSeq afr.w`, and the
per-step bound `ε_k ≤ 6(1−w_k)²` is a THEOREM (`cube_diff_le_envelope`), not the trivial
`0 ≤ 6(1−w)²`.  `EigenvalueShiftDefect` is REDUCED (guard-safe, conditional) to the sharp
named two-loop β-step `AFBetaStep` + single-coupling form-preservation
`SingleCouplingFormPreservation`.

**NOT closed (the genuine 4D content):**
  1. `AFBetaStep afr` — the two-loop `β ≤ 2` running rate for the REAL 4D flow (satisfiable
     on the canonical trajectory; NOT derivable from `AFRateModulus`).
  2. `SingleCouplingFormPreservation afr` — the Bałaban back-reaction / form-preservation
     (the coarse action stays single-coupling heat-kernel form).

`EigenvalueShiftDefect` is a NODE, not a guarded frontier type, and does NOT cascade to a
guarded bundle by any existing lemma.  No guarded bundle is inhabited; nothing is faked;
no free-field `δ := 0` is used.  The 4D Yang–Mills mass gap remains OPEN. -/
theorem eigenvalueShiftBound_honesty : True := trivial

end YMGap.Continuum.EigenvalueShiftBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.EigenvalueShiftBound.cancel_mid
#print axioms YMGap.Continuum.EigenvalueShiftBound.sqDiff_factor
#print axioms YMGap.Continuum.EigenvalueShiftBound.sqDiff_le
#print axioms YMGap.Continuum.EigenvalueShiftBound.cubeSplit_factor
#print axioms YMGap.Continuum.EigenvalueShiftBound.cube_diff_le_three
#print axioms YMGap.Continuum.EigenvalueShiftBound.cube_diff_le_envelope
#print axioms YMGap.Continuum.EigenvalueShiftBound.eigenvalueShiftDefect_of_betaStep
#print axioms YMGap.Continuum.EigenvalueShiftBound.realErosion_le_shift_plus_largeField
#print axioms YMGap.Continuum.EigenvalueShiftBound.formPreserved_perStep
#print axioms YMGap.Continuum.EigenvalueShiftBound.afBetaStep_mono_canonical
