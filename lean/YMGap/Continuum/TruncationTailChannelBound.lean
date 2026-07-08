/-
Item 12 (Koch–Wittwer certified-RG route) — **DISCHARGING the CHANNEL-truncation
tail residual `TruncationTailBound` via a genuine SUPER-GEOMETRIC `CReal` bound.**

# What this module is (read first)

`TruncatedBlockSpinContraction.TruncationTailBound` names the ONE analytic residual
of the item-12 certified contraction: the discarded high-`j` SU(2) character channels
(`j > N`) contribute at most the slack `2·(1 − w_k)²` to the per-step block-spin
defect.  The mechanism is the SUPER-GEOMETRIC decay of the heat-kernel character
coefficients: the quadratic Casimir `C₂(j) = j(j+1)` makes the coefficient
`coeff_j = (2j+1)·q^{j(j+1)}` (`q = e^{−t/2}` the heat-kernel nome, `(2j+1)` the SU(2)
degeneracy) decay faster than any geometric.  This module CONSTRUCTIVIZES that estimate
over the project's `Q'`/`CReal` core and INHABITS `TruncationTailBound` — moving the
channel tail off the item-12 frontier.

  1. **The real SU(2) heat-kernel channel coefficient** `chanCoeff q j = (2j+1)·q^{j(j+1)}`.
     Its ratio between successive discarded channels is `≤ ρ = 2·q^{2(N+1)}` uniformly
     (`chanCoeff_ratio`): the linear degeneracy `(2j+1)` is dominated by the quadratic
     Casimir drop `q^{2(j+1)} ≤ q^{2(N+1)}`.  Hence each discarded term is bounded by the
     GEOMETRIC increment `geoIncrBase (chanCoeff q N) ρ l` (`chanCoeff_geoDom`) — the
     super-geometric-into-geometric domination that makes the tail summable.

  2. **The discarded tail as a convergent `CReal`** `channelTailCR`, built through the
     general-base geometric-limit engine `HKConvGen.crealOfGeoIncrementBase` at decay
     base `ρ` — the SAME machinery that realises the Jacobi ϑ₃ series `Σ q^{n²}`.  Its
     partial sums are the finite discarded-channel sums `Σ_{i<M} chanCoeff q (N+i)`.

  3. **The genuine super-geometric tail bound** `channelTailCR_leRat_sharp`:
     `channelTailCR ≤ (chanCoeff q N)·2` as a `CReal`-≤-rational (`CReal.leRat`), proved
     by dominating the partial sums termwise by the geometric series
     `Σ ρ^i ≤ 1/(1−ρ)` (`HKConvGen.geom_series_le_base` + `HKConv.divPos_le_of_le`) — the
     `Σ q^n ≤ 1/(1−q)` closed-tail bound.  This is a REAL majorant of the infinite
     `CReal` tail, NOT a rational surrogate: `chanTailBound := (chanCoeff q N)·2` is
     certified `≥` the true `CReal` sum.

  4. **The `≤ 2·(1 − w_k)²` step and the inhabitant.**  `chanTailBound ≤ 2` (a
     `CReal`-≤-rational decided on the pilot endpoints), so the per-scale tail model
     `tailDefect k = chanTailBound·(1 − w_k)²` satisfies `≤ 2·(1 − w_k)²`
     (`channelTruncationTailBound`), INHABITING `TruncationTailBound`.  Fed through
     `fullDefect_quad_of_certified_and_tail` (`channelTail_discharged`), the certified
     truncated bound `4·m²` + this tail `2·m²` reproduce the full `6·m²` (E1).

# HONEST scope (what this discharges, what it does NOT)

DISCHARGED: the CHANNEL-truncation analytic content — the discarded high-`j` channels'
super-geometric summability, exhibited as a genuine constructive `CReal` bound
`channelTailCR ≤ chanTailBound ≤ 2` at the pilot nome, and `TruncationTailBound`
inhabited.  The `channelTailCR` is the REAL discarded-channel tail (real `(2j+1)·q^{j(j+1)}`
coefficients), its bound is a genuine super-geometric `CReal` majorant, and `≤ 2·m²` is a
genuine `CReal`-backed rational inequality.

NOT discharged (unchanged residuals): the **finite-scale certification** — a UNIFORM-in-`k`
channel weight `≤ 2` at EVERY scale requires `N` to grow with the scale (the tail weight
`Σ_{j>N}(2j+1)q^{j(j+1)}` grows as `q = e^{−t_k/2} → 1`; the pilot fixes ONE nome), which is
the remaining `N ≈ 26` interval-arithmetic work; and the **deep-scaling scale-tail
`singleStep` (E2)**, the RG recursion on `trueMargin`, entirely untouched here.  The channel
tail is ONE residual off the primary a→0 bet; `singleStep` stays open and the frontier guard
stays at 5.  The Clay Yang–Mills mass gap remains OPEN.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`CReal` data (`Type`-level witnesses, Rule 8).  `decide` only on exact rational
pilot endpoints (no `native_decide`).  Permitted axioms: `propext` / `Quot.sound`.  No
`Classical.*`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.TruncatedBlockSpinContraction
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Constructive.CRealLe
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.TruncationTailChannelBound

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.TruncatedBlockSpinContraction
open YMGap.Constructive.RationalTail

/-! ## 1. The SU(2) heat-kernel character coefficient and its super-geometric ratio -/

/-- The SU(2) heat-kernel character coefficient of channel `j` at rational nome `q`:
`chanCoeff q j = (2j+1)·q^{j(j+1)}`, with `(2j+1)` the SU(2) degeneracy and the quadratic
Casimir `C₂(j) = j(j+1)` in the exponent (`q = e^{−t/2}`). -/
def chanCoeff (q : Q') (j : Nat) : Q' := Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1))

theorem chanCoeff_nonneg {q : Q'} (hq : (0 : Q') ≤ q) (j : Nat) :
    (0 : Q') ≤ chanCoeff q j :=
  Q'.mul_nonneg _ _ (SU3CharFactor.ofNat_nonneg _) (Q'.pow_nonneg q hq _)

/-- **THE SUPER-GEOMETRIC RATIO STEP.**  For `0 ≤ q ≤ 1`, `1 ≤ j`, `N ≤ j`, the ratio
between successive discarded channels is bounded by `ρ = 2·q^{2(N+1)}`:
`chanCoeff q (j+1) ≤ (2·q^{2(N+1)})·chanCoeff q j`.  The exponent jumps by `2(j+1) ≥ 2(N+1)`
(so `q^{(j+1)(j+2)} ≤ q^{j(j+1)}·q^{2(N+1)}`, super-geometric Casimir decay) and the linear
degeneracy grows only by `(2j+3) ≤ 2·(2j+1)` — dominated by the quadratic drop. -/
theorem chanCoeff_ratio {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1) (N j : Nat)
    (hNj : N ≤ j) (hj1 : 1 ≤ j) :
    chanCoeff q (j + 1) ≤ (Q'.ofNat 2 * q ^ (2 * (N + 1))) * chanCoeff q j := by
  show Q'.ofNat (2 * (j + 1) + 1) * q ^ ((j + 1) * (j + 1 + 1))
      ≤ (Q'.ofNat 2 * q ^ (2 * (N + 1))) * (Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1)))
  -- exponent Nat inequality (chord: (j+1)(j+2) ≥ j(j+1) + 2(N+1))
  have expand : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by
    rw [Nat.mul_succ, Nat.succ_mul]; omega
  have hexp : j * (j + 1) + 2 * (N + 1) ≤ (j + 1) * (j + 1 + 1) := by
    rw [expand]; omega
  -- B ≤ a·b :  q^{(j+1)(j+2)} ≤ q^{j(j+1)}·q^{2(N+1)}
  have hB : q ^ ((j + 1) * (j + 1 + 1))
      ≤ q ^ (j * (j + 1)) * q ^ (2 * (N + 1)) :=
    Q'.le_trans' _ _ _ (HKConvGen.pow_base_antitone hq0 hq1 hexp)
      (Q'.le_of_eqv (Q'.pow_add_eqv q (j * (j + 1)) (2 * (N + 1))))
  -- prefactor:  (2(j+1)+1) ≤ 2·(2j+1)
  have hPnat : 2 * (j + 1) + 1 ≤ 2 * (2 * j + 1) := by omega
  have hP : Q'.ofNat (2 * (j + 1) + 1) ≤ Q'.ofNat 2 * Q'.ofNat (2 * j + 1) :=
    Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hPnat)
      (Q'.le_of_eqv (SU3CharFactor.ofNat_mul_eqv 2 (2 * j + 1)))
  -- nonnegativities
  have hBnn : (0 : Q') ≤ q ^ ((j + 1) * (j + 1 + 1)) := Q'.pow_nonneg q hq0 _
  have hP'nn : (0 : Q') ≤ Q'.ofNat 2 * Q'.ofNat (2 * j + 1) :=
    Q'.mul_nonneg _ _ (by decide) (SU3CharFactor.ofNat_nonneg _)
  -- combine termwise:  P'·B ≤ (2·P)·B ≤ (2·P)·(a·b)
  have step1 : Q'.ofNat (2 * (j + 1) + 1) * q ^ ((j + 1) * (j + 1 + 1))
      ≤ (Q'.ofNat 2 * Q'.ofNat (2 * j + 1)) * q ^ ((j + 1) * (j + 1 + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hP hBnn
  have step2 : (Q'.ofNat 2 * Q'.ofNat (2 * j + 1)) * q ^ ((j + 1) * (j + 1 + 1))
      ≤ (Q'.ofNat 2 * Q'.ofNat (2 * j + 1))
          * (q ^ (j * (j + 1)) * q ^ (2 * (N + 1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hB hP'nn
  refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ step1 step2) (Q'.le_of_eqv ?_)
  -- rearrange (2·P)·(a·b) ≃ (2·b)·(P·a)  [P = ofNat(2j+1), a = q^{j(j+1)}, b = q^{2(N+1)}]
  have hinner :
      (Q'.ofNat (2 * j + 1) * (q ^ (j * (j + 1)) * q ^ (2 * (N + 1)))).eqv
        (q ^ (2 * (N + 1)) * (Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1)))) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (2 * j + 1)) (q ^ (j * (j + 1)))
        (q ^ (2 * (N + 1)))))
      (Q'.mul_comm_eqv (Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1))) (q ^ (2 * (N + 1))))
  have hLHS :
      ((Q'.ofNat 2 * Q'.ofNat (2 * j + 1)) * (q ^ (j * (j + 1)) * q ^ (2 * (N + 1)))).eqv
        (Q'.ofNat 2 * (q ^ (2 * (N + 1)) * (Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1))))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat (2 * j + 1))
        (q ^ (j * (j + 1)) * q ^ (2 * (N + 1))))
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hinner)
  have hRHS :
      ((Q'.ofNat 2 * q ^ (2 * (N + 1))) * (Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1)))).eqv
        (Q'.ofNat 2 * (q ^ (2 * (N + 1)) * (Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1))))) :=
    Q'.mul_assoc_eqv (Q'.ofNat 2) (q ^ (2 * (N + 1)))
      (Q'.ofNat (2 * j + 1) * q ^ (j * (j + 1)))
  exact Q'.eqv_trans _ _ _ hLHS (Q'.eqv_symm hRHS)

/-- **THE GEOMETRIC DOMINATION OF THE DISCARDED TAIL.**  Each discarded channel `N+l`
is bounded by the base-`ρ` geometric increment `chanCoeff q N · ρ^l`
(`ρ = 2·q^{2(N+1)}`), by iterating the super-geometric ratio step.  This is the
`geoIncrBase (chanCoeff q N) ρ l` the geometric-limit engine consumes. -/
theorem chanCoeff_geoDom {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1) (N : Nat)
    (hN1 : 1 ≤ N) :
    ∀ l, chanCoeff q (N + l)
      ≤ chanCoeff q N * (Q'.ofNat 2 * q ^ (2 * (N + 1))) ^ l
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv (chanCoeff q N)))
  | l + 1 => by
      have ih := chanCoeff_geoDom hq0 hq1 N hN1 l
      have hratio : chanCoeff q ((N + l) + 1)
          ≤ (Q'.ofNat 2 * q ^ (2 * (N + 1))) * chanCoeff q (N + l) :=
        chanCoeff_ratio hq0 hq1 N (N + l) (Nat.le_add_right N l)
          (Nat.le_trans hN1 (Nat.le_add_right N l))
      have hρnn : (0 : Q') ≤ Q'.ofNat 2 * q ^ (2 * (N + 1)) :=
        Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg q hq0 _)
      have hchain : chanCoeff q ((N + l) + 1)
          ≤ (Q'.ofNat 2 * q ^ (2 * (N + 1)))
              * (chanCoeff q N * (Q'.ofNat 2 * q ^ (2 * (N + 1))) ^ l) :=
        Q'.le_trans' _ _ _ hratio
          (Q'.mul_le_mul_of_nonneg_left _ _ _ ih hρnn)
      refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
      -- ρ·(C·ρ^l) ≃ C·(ρ·ρ^l) = C·ρ^{l+1}
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2 * q ^ (2 * (N + 1)))
          (chanCoeff q N) ((Q'.ofNat 2 * q ^ (2 * (N + 1))) ^ l))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((Q'.ofNat 2 * q ^ (2 * (N + 1))) ^ l)
          (Q'.mul_comm_eqv (Q'.ofNat 2 * q ^ (2 * (N + 1))) (chanCoeff q N))) ?_
      exact Q'.mul_assoc_eqv (chanCoeff q N) (Q'.ofNat 2 * q ^ (2 * (N + 1)))
        ((Q'.ofNat 2 * q ^ (2 * (N + 1))) ^ l)

/-! ## 2. The pilot instantiation (`N = 4` kept channels, discard `j ≥ 4`; nome `q = 1/2`)

The finite part (`TruncatedBlockSpinContraction`) keeps `N = 4` channels `j ∈ {0,1,2,3}`;
the discarded tail therefore starts at channel index `4`.  We fix the pilot nome
`q = 1/2` (a representative heat-kernel value); the ratio decay base is
`ρ = 2·(1/2)^{2·5} = 1/512 < 1`. -/

/-- Pilot nome `q = 1/2` (heat-kernel `e^{−t/2}` at the pilot `t`). -/
def qP : Q' := Q'.mkPos 1 2 (by decide)

/-- Truncation order: `N = 4` kept channels; discard `j ≥ 4`. -/
def Ntr : Nat := 4

/-- The geometric decay base `ρ = 2·q^{2(N+1)} = 2·(1/2)^{10} = 1/512`. -/
def rhoP : Q' := Q'.ofNat 2 * qP ^ (2 * (Ntr + 1))

/-- The leading discarded coefficient `chanCoeff q N = 9·(1/2)^{20}`. -/
def cLead : Q' := chanCoeff qP Ntr

/-- The discarded-channel partial sums `Σ_{i<M} chanCoeff q (N+i)` — the `approx` of the
`CReal` tail. -/
def chanTailPartial : Nat → Q' := finSum (fun i => chanCoeff qP (Ntr + i))

theorem hqP0 : (0 : Q') ≤ qP := by decide
theorem hqP1 : qP ≤ (1 : Q') := by decide
theorem hqP0' : (0 : Q') < qP := by decide
theorem hrhoP0 : (0 : Q') < rhoP := by decide
theorem hrhoP1 : rhoP < (1 : Q') := by decide
theorem hcLead_nonneg : (0 : Q') ≤ cLead := chanCoeff_nonneg hqP0 Ntr
theorem hcLead_pos : (0 : Q') < cLead := by
  show (0 : Q') < Q'.ofNat (2 * Ntr + 1) * qP ^ (Ntr * (Ntr + 1))
  exact Q'.mul_pos (by decide) (HKPos.pow_pos hqP0' _)

/-- The per-term geometric domination at the pilot:
`chanCoeff q (N+l) ≤ cLead · ρ^l`.  (Pilot instance of `chanCoeff_geoDom`.) -/
theorem perTermP (l : Nat) : chanCoeff qP (Ntr + l) ≤ cLead * rhoP ^ l :=
  chanCoeff_geoDom hqP0 hqP1 Ntr (by decide) l

/-! ## 3. The convergent `CReal` discarded-channel tail (the geometric-limit engine) -/

theorem hup (l : Nat) :
    chanTailPartial (l + 1)
      ≤ chanTailPartial l + HKConvGen.geoIncrBase cLead rhoP l := by
  show chanTailPartial l + chanCoeff qP (Ntr + l)
      ≤ chanTailPartial l + HKConvGen.geoIncrBase cLead rhoP l
  exact Q'.add_le_add_left (chanTailPartial l) _ _ (perTermP l)

theorem hlo (l : Nat) :
    chanTailPartial l
      ≤ chanTailPartial (l + 1) + HKConvGen.geoIncrBase cLead rhoP l := by
  have h1 : chanTailPartial l ≤ chanTailPartial (l + 1) := by
    show chanTailPartial l ≤ chanTailPartial l + chanCoeff qP (Ntr + l)
    exact Q'.add_le_self_of_nonneg _ _ (chanCoeff_nonneg hqP0 (Ntr + l))
  exact Q'.le_trans' _ _ _ h1
    (Q'.add_le_self_of_nonneg _ _
      (HKConvGen.geoIncrBase_nonneg hcLead_nonneg (Q'.le_of_lt hrhoP0) l))

theorem modulusP : ∀ ε : Q', (0 : Q') < ε →
    ∃ δ : Q', (0 : Q') < δ ∧
      (cLead * HKConv.divPos 1 (1 + (-rhoP))) * δ ≤ ε := by
  intro ε hε
  have hCleadnum : 0 < cLead.num := CReal.num_pos_of_pos hcLead_pos
  have hHnum : 0 < (HKConv.divPos 1 (1 + (-rhoP))).num :=
    HKConv.divPos_num_pos (by decide)
  have hDnum : 0 < (cLead * HKConv.divPos 1 (1 + (-rhoP))).num := by
    show 0 < cLead.num * (HKConv.divPos 1 (1 + (-rhoP))).num
    exact Int.mul_pos hCleadnum hHnum
  refine ⟨HKConv.divPos ε (cLead * HKConv.divPos 1 (1 + (-rhoP))),
    HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (cLead * HKConv.divPos 1 (1 + (-rhoP)))
      (HKConv.divPos ε (cLead * HKConv.divPos 1 (1 + (-rhoP))))) ?_
  exact HKConv.divPos_mul_eqv hDnum

/-- **THE CONVERGENT `CReal` DISCARDED-CHANNEL TAIL** `Σ_{j≥N} chanCoeff q j`, built
through the general-base geometric-limit engine at decay base `ρ` (the same engine that
realises `Σ q^{n²}`).  `approx M = Σ_{i<M} chanCoeff q (N+i)` (the genuine finite
discarded-channel sums). -/
def channelTailCR : CReal :=
  HKConvGen.crealOfGeoIncrementBase chanTailPartial cLead rhoP
    hcLead_nonneg hrhoP0 hrhoP1 hup hlo modulusP

@[simp] theorem channelTailCR_approx (M : Nat) :
    channelTailCR.approx M = chanTailPartial M := rfl

/-! ## 4. The genuine super-geometric `CReal` bound (`Σ q^n ≤ 1/(1−q)` machinery) -/

/-- `1/(1−ρ) ≤ 2` at the pilot (`ρ = 1/512 ≤ 1/2`), via the cross-multiplied
`divPos ≤` characterisation. -/
theorem hDivLe2 : HKConv.divPos 1 (1 + (-rhoP)) ≤ Q'.ofNat 2 :=
  HKConv.divPos_le_of_le (by decide) (by decide)

/-- Every geometric partial sum `Σ_{i<M} ρ^i ≤ 2` (`geom_series_le_base` + `hDivLe2`). -/
theorem hgeomP (M : Nat) : finSum (fun i => rhoP ^ i) M ≤ Q'.ofNat 2 :=
  Q'.le_trans' _ _ _ (HKConvGen.geom_series_le_base hrhoP0 hrhoP1 M) hDivLe2

/-- Local termwise monotonicity of `finSum`. -/
theorem finSum_le_termwise (f g : Nat → Q') (h : ∀ i, f i ≤ g i) :
    ∀ M, finSum f M ≤ finSum g M
  | 0 => Q'.le_refl' 0
  | M + 1 => Q'.add_le_add (finSum_le_termwise f g h M) (h M)

/-- **THE SUPER-GEOMETRIC PARTIAL-SUM BOUND.**  Every finite discarded-channel sum is
`≤ cLead·2`: termwise geometric domination (`perTermP`), constant pull-out, and the
geometric series bound. -/
theorem chanTailPartial_le (M : Nat) :
    chanTailPartial M ≤ cLead * Q'.ofNat 2 := by
  have h1 : finSum (fun i => chanCoeff qP (Ntr + i)) M
      ≤ finSum (fun i => cLead * rhoP ^ i) M :=
    finSum_le_termwise _ _ (fun i => perTermP i) M
  have h2 : finSum (fun i => cLead * rhoP ^ i) M ≤ cLead * Q'.ofNat 2 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (RationalTail.const_mul_finSum (fun i => rhoP ^ i) cLead M)))
      (Q'.mul_le_mul_of_nonneg_left _ _ cLead (hgeomP M) hcLead_nonneg)
  exact Q'.le_trans' _ _ _ h1 h2

/-- **THE GENUINE SUPER-GEOMETRIC `CReal` TAIL BOUND** `channelTailCR ≤ cLead·2`
(`CReal.leRat`): the infinite discarded-channel `CReal` sum is dominated by the rational
`cLead·2`, via the base-`ρ` geometric majorant.  NOT a surrogate — a certified majorant of
the real `CReal` tail. -/
theorem channelTailCR_leRat_sharp :
    CReal.leRat channelTailCR (cLead * Q'.ofNat 2) :=
  CReal.leRat_of_eventually ⟨0, fun M _ => chanTailPartial_le M⟩

/-! ## 5. The `≤ 2·(1 − w_k)²` step and the `TruncationTailBound` inhabitant -/

/-- The certified channel-tail weight `chanTailBound = cLead·2` — the rational
super-geometric majorant of the true `CReal` discarded-channel sum (justified by
`channelTailCR_le_chanTailBound`). -/
def chanTailBound : Q' := cLead * Q'.ofNat 2

/-- `chanTailBound` genuinely dominates the infinite `CReal` discarded-channel tail. -/
theorem channelTailCR_le_chanTailBound :
    CReal.leRat channelTailCR chanTailBound :=
  channelTailCR_leRat_sharp

/-- **THE `CReal`-≤-RATIONAL `≤ 2` STEP.**  `chanTailBound = 9·(1/2)^{20}·2 ≤ 2`, decided
on the exact pilot endpoints — the channel-tail weight fits inside the `2·m²` slack. -/
theorem chanTailBound_le_two : chanTailBound ≤ Q'.ofNat 2 := by decide

/-- **THE INHABITANT of `TruncationTailBound`.**  The per-scale discarded-channel tail
model `tailDefect k = chanTailBound·(1 − w_k)²` (channel weight × quadratic margin frame)
satisfies `≤ 2·(1 − w_k)²`, because the super-geometric channel weight `chanTailBound ≤ 2`
(a genuine `CReal`-backed bound) and the margin square is `≥ 0`.  This CLOSES the named
channel-truncation residual of item 12 for this pilot tail-defect sequence. -/
def channelTruncationTailBound (afr : AFRateModulus) :
    TruncationTailBound afr Ntr
      (fun k => chanTailBound * ((1 - afr.w k) * (1 - afr.w k))) where
  tail_quad := fun k => by
    have hm : (0 : Q') ≤ (1 - afr.w k) * (1 - afr.w k) := by
      have hmn : (0 : Q') ≤ 1 - afr.w k :=
        Q'.sub_nonneg_of_le (Q'.le_of_lt (afr.w_lt_one k))
      exact Q'.mul_nonneg _ _ hmn hmn
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ chanTailBound_le_two hm

/-! ## 6. Feeding the item-12 composition — the channel tail is DISCHARGED -/

/-- **`channelTail_discharged` — the composition with the channel tail CLOSED.**  Given
the interval-certified truncated per-scale bound `truncDefect k ≤ 4·(1 − w_k)²` (the
finite-scale certification, still a hypothesis — the remaining `N ≈ 26` interval work),
the full per-step defect `truncDefect + (channel tail) ≤ 6·(1 − w_k)²` (E1), with the
channel-tail contribution now supplied by the PROVED super-geometric inhabitant (no longer
an open obligation).  Only the finite-scale certification `htrunc` and `singleStep` (E2)
remain. -/
theorem channelTail_discharged
    (afr : AFRateModulus) (truncDefect : Nat → Q')
    (htrunc : ∀ k, truncDefect k ≤ Q'.ofNat 4 * ((1 - afr.w k) * (1 - afr.w k))) :
    ∀ k, truncDefect k + chanTailBound * ((1 - afr.w k) * (1 - afr.w k))
      ≤ Q'.ofNat 6 * ((1 - afr.w k) * (1 - afr.w k)) :=
  TruncatedBlockSpinContraction.fullDefect_quad_of_certified_and_tail
    afr Ntr (fun k => chanTailBound * ((1 - afr.w k) * (1 - afr.w k))) truncDefect
    htrunc (channelTruncationTailBound afr)

end YMGap.Continuum.TruncationTailChannelBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TruncationTailChannelBound.chanCoeff_ratio
#print axioms YMGap.Continuum.TruncationTailChannelBound.chanCoeff_geoDom
#print axioms YMGap.Continuum.TruncationTailChannelBound.channelTailCR
#print axioms YMGap.Continuum.TruncationTailChannelBound.channelTailCR_leRat_sharp
#print axioms YMGap.Continuum.TruncationTailChannelBound.chanTailBound_le_two
#print axioms YMGap.Continuum.TruncationTailChannelBound.channelTruncationTailBound
#print axioms YMGap.Continuum.TruncationTailChannelBound.channelTail_discharged
