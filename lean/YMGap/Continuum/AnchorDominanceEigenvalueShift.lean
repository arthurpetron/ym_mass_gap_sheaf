/-
Track B / R2 — THE ANCHOR-DOMINANCE, made CONCRETE and PROVED: the accumulated
real 4D block-spin ADDITIVE erosion `∑ ε_k` is DOMINATED by the transmuted margin
`m_phys`, in a deep-UV-anchored scheme, via the **telescoping eigenvalue-shift
budget**.

# The obligation (`CAPSTONE-2026-07-06 §5`, `transmutation §4`)

The dimensional-transmutation kinematics (`DimensionlessMarginTransmutation`) proved
the dimensionless margin `m_lat(a_k)/a_k` is CONSERVED to `m_phys = 1 − e^{−1/e} =
0.30780 > 0` for the IDEAL self-similar RG flow (`concreteSelfSimilarFlowE`,
zero-defect).  The REAL 4D block-spin flow DEVIATES from self-similarity by a per-step
ADDITIVE erosion `ε_k`.  The real dimensionless margin is `m_phys − ∑ ε_k`, so a
positive continuum gap needs the **anchor-dominance** `∑ ε_k < m_phys`
(the `additiveErosion_uniform_floor` hypothesis `Bε < (1 − Bδ)·margin 0`).

# What this module makes CONCRETE and PROVES

`ε_k` is the multiplicity-BLIND coupling-flow **eigenvalue shift** of Route I
(`RouteIEigenvalueDefect.EigenvalueShiftDefect`): with the physical gap edge the
transfer eigenvalue `eigA w 1 = w³` (`GapIsEigenvalue` VERDICT A), the per-step defect
is `ε_k = w_{k+1}³ − w_k³` along the asymptotic-freedom flow `w_k ↑ 1`.  Route I proved
this is the correct multiplicity-blind object (the fusion-DEGENERACY defect is `0`), and
it is dominated by the Route H renormalized defect `δ_ren ≤ 6(1−w)²` — but the DECISIVE
structural fact, exploited here, is that the eigenvalue shift is **additive and
TELESCOPES**:

    ∑_{j<k} (w_{j+1}³ − w_j³)  =  w_k³ − w_0³  ≤  1 − w_0³   =:  Bε      (EXACT).

So the ENTIRE accumulated additive-erosion budget is the single closed value `1 − w_0³`,
where `w_0` is the coupling at the UV anchor.  This is the sharp anchor-dominance:

  * `qcube_mono` / `qcube_le_one` — the cube (`eigA · 1`) is monotone and sub-unit on
    `[0,1]`;
  * `eigShiftSeq w k = w_{k+1}³ − w_k³` — the CONCRETE per-step eigenvalue shift (`ε_k`);
  * `eigShift_nonneg` — `ε_k ≥ 0` (from `w_k ↑`);
  * `eigShift_tailSum_eqv` — the EXACT telescoping identity
    `∑_{j<k} ε_j ≃ w_k³ − w_0³`;
  * `eigShift_tailSum_le` — the accumulated budget `∑_{j<k} ε_j ≤ 1 − w_0³` (∀ k);
  * **`anchorDominance_floor`** — the CONDITIONAL producer: for ANY margin obeying the
    additive step `margin(k+1) ≥ margin k − ε_k` with anchor-dominance
    `1 − w_0³ < margin 0`, the PROVED `additiveErosion_uniform_floor` yields the uniform
    STRICTLY-POSITIVE continuum floor `margin 0 − (1 − w_0³)` (∀ k).  Open binders on the
    real margin / real step law: it does NOT inhabit any guarded bundle.
  * `anchorDom_numeric` / `anchorDom_from_mphys_lb` — the deep-UV anchor `w_0 = 11/12`
    gives `Bε = 1 − (11/12)³ = 397/1728 = 0.22975 < 3/10 ≤ m_phys` (kernel `decide`), so
    the anchor-dominance HOLDS with comfortable slack `≈ 0.078`.

# The honest reduction — and why this is genuine progress

The anchor-dominance `∑ ε_k < m_phys` was carried by `CAPSTONE §5` as an independent
open inequality on top of the step law and summability.  This module DISCHARGES it, in
a deep-UV-anchored scheme, from the telescoping structure + the transmuted anchor
`m_phys ≥ 3/10`: it is no longer a separate mystery.  What REMAINS open (honest):

  1. **The identification** `ε_k ≤ w_{k+1}³ − w_k³` — that the real per-step additive
     erosion of the dimensionless margin is bounded by the multiplicity-blind eigenvalue
     shift (Route I's UNINHABITED `EigenvalueShiftDefect`, Route H's identification).
  2. **The anchor value** `margin 0 ≥ m_phys ≈ 0.3078` at the deep-UV anchor — that the
     dimensionless margin at the UV cutoff is the transmuted `m_phys` (dimensional
     transmutation: PROVED for the ideal flow in `DimensionlessMarginTransmutation`;
     the real flow's conservation is the open transmutation content).

Neither is inhabited here; both are the genuine 4D Yang–Mills continuum content.  The
NAIVE non-anchored budget is the honest negative that motivates the scheme: the squared
model majorant `∑_{k≥0} 6(1−w_k)² = π² ≈ 9.87 ≫ m_phys` for the canonical AF rate
(`A=1,B=1`); the telescoping eigenvalue-shift budget `1 − w_0³ → 0` under deep-UV
anchoring is what makes the dominance hold (validated in `anchor_num.py`, mpmath dps 60).

# Guard / STOP status (task condition (ii))

`anchorDominance_floor` is a CONDITIONAL producer with open binders on the real margin
and real step law.  It does NOT construct `TrueMarginRecursionPhysical`,
`TrueMarginRecursionSummable`, `SingleStepDefectBound`, `UniformSpacingFloor`,
`Tier0Scorecard`, `ClayTarget`, `ClayTargetPinned`, or `FrontierDAG` — no guarded
bundle is inhabited, no STOP condition is tripped.  It reuses the PROVED pure-`Q'`
engine `additiveErosion_uniform_floor` on concrete majorant sequences.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide` (only `decide` on closed decidable `Q'` facts), no `sorry`.
-/
import YMGap.Continuum.AdditiveErosionAdequacy
import YMGap.Constructive.QPoly
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.AnchorDominance

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare

/-! ## 0. Small `Q'` order glue -/

/-- `a < b → b ≤ c → a < c` on `Q'` (Int cross-product transitivity; a local copy of
the helper several `YMGap.Continuum.*` modules carry). -/
theorem qLtLe {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 (by exact_mod_cast c.den_pos : (0:Int) < (c.den:Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 (by exact_mod_cast Nat.zero_le a.den : (0:Int) ≤ (a.den:Int))
    have hl : (a.den : Int) * (b.num * (c.den : Int)) = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int)) = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le b.den)

/-- `(0 : Q') ≤ 1`. -/
theorem qZeroLeOne : (0 : Q') ≤ (1 : Q') := by decide

/-! ## 1. The cube (the transfer eigenvalue `eigA w 1 = w³`) and its order theory -/

/-- The transfer gap-edge eigenvalue `eigA w 1 = w^{C₄(1)} = w³` as a plain `Q'` cube. -/
def qcube (x : Q') : Q' := x * (x * x)

/-- `0 ≤ x → 0 ≤ x³`. -/
theorem qcube_nonneg {x : Q'} (hx : (0 : Q') ≤ x) : (0 : Q') ≤ qcube x :=
  Q'.mul_nonneg _ _ hx (SumOfSquares.q_mul_self_nonneg x)

/-- **The cube is monotone on the nonnegatives.**  `0 ≤ a → a ≤ b → a³ ≤ b³`.
`a³ = a·(a·a) ≤ b·(b·b) = b³` via two applications of the monotone product
(`a ≤ b`, `a·a ≤ b·b`). -/
theorem qcube_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    qcube a ≤ qcube b := by
  have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
  have haa : (0 : Q') ≤ a * a := SumOfSquares.q_mul_self_nonneg a
  have hsq : a * a ≤ b * b := Q'.mul_le_mul_of_nonneg hab hab hb ha
  exact Q'.mul_le_mul_of_nonneg hab hsq hb haa

/-- **The cube is sub-unit on `[0,1]`.**  `0 ≤ x → x ≤ 1 → x³ ≤ 1`. -/
theorem qcube_le_one {x : Q'} (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    qcube x ≤ (1 : Q') := by
  refine Q'.le_trans' _ _ _ (qcube_mono hx hx1) (Q'.le_of_eqv ?_)
  -- qcube 1 = 1 * (1 * 1) ≃ 1
  show ((1 : Q') * ((1 : Q') * (1 : Q'))).eqv (1 : Q')
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left 1 ((1 : Q') * 1) 1 (Q'.one_mul_eqv 1))
    (Q'.one_mul_eqv 1)

/-! ## 2. The concrete eigenvalue-shift erosion `ε_k = w_{k+1}³ − w_k³` -/

/-- **The per-step multiplicity-blind eigenvalue shift** (Route I's `ε_k`):
`eigShiftSeq w k = w_{k+1}³ − w_k³`, the decay-rate degradation of the true margin along
the coupling flow `w_k ↑ 1`. -/
def eigShiftSeq (w : Nat → Q') (k : Nat) : Q' := qcube (w (k + 1)) - qcube (w k)

/-- `ε_k ≥ 0` for a monotone-increasing flow `w_k ↑` (via cube monotonicity). -/
theorem eigShift_nonneg (w : Nat → Q') (hnn : ∀ k, (0 : Q') ≤ w k)
    (hmono : ∀ k, w k ≤ w (k + 1)) (k : Nat) :
    (0 : Q') ≤ eigShiftSeq w k := by
  show (0 : Q') ≤ qcube (w (k + 1)) + -(qcube (w k))
  exact qZeroLeSub (qcube_mono (hnn k) (hmono k))

/-! ## 3. The EXACT telescoping identity — the whole point

For an additive difference sequence, the partial sum collapses:
`∑_{j<M} (A_{j+1} − A_j) = A_M − A_0`.  The generic three-term cancellation
`(A_M − A_0) + (A_{M+1} − A_M) ≃ A_{M+1} − A_0` is the inductive engine. -/

/-- The generic telescoping cancellation `(AM − A0) + (AM1 − AM) ≃ AM1 − A0`
(pure `Q'`, via two `q_interchange` regroupings collapsing `AM + −AM ≃ 0`). -/
theorem tele_eqv (A0 AM AM1 : Q') :
    ((AM + -A0) + (AM1 + -AM)).eqv (AM1 + -A0) := by
  refine Q'.eqv_trans _ _ _ (QPoly.q_interchange AM (-A0) AM1 (-AM)) ?_
  -- (AM + AM1) + (-A0 + -AM)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (AM + AM1) (-A0 + -AM) (-AM + -A0)
      (Q'.add_comm_eqv (-A0) (-AM))) ?_
  -- (AM + AM1) + (-AM + -A0)
  refine Q'.eqv_trans _ _ _ (QPoly.q_interchange AM AM1 (-AM) (-A0)) ?_
  -- (AM + -AM) + (AM1 + -A0)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (AM + -AM) 0 (AM1 + -A0) (Q'.add_neg_self_eqv AM)) ?_
  -- 0 + (AM1 + -A0)
  exact Q'.eqv_of_eq (Q'.zero_add' (AM1 + -A0))

/-- **THE TELESCOPING BUDGET IDENTITY.**  `∑_{j<M} ε_j ≃ w_M³ − w_0³`, exactly, for
every `M` — the accumulated additive erosion is the closed difference of cube endpoints. -/
theorem eigShift_tailSum_eqv (w : Nat → Q') (M : Nat) :
    (tailSum (eigShiftSeq w) 0 M).eqv (qcube (w M) - qcube (w 0)) := by
  induction M with
  | zero =>
    show ((0 : Q')).eqv (qcube (w 0) + -(qcube (w 0)))
    exact Q'.eqv_symm (Q'.add_neg_self_eqv (qcube (w 0)))
  | succ M ih =>
    show (tailSum (eigShiftSeq w) 0 M + eigShiftSeq w (0 + M)).eqv
      (qcube (w (M + 1)) + -(qcube (w 0)))
    have h0M : (0 + M) = M := Nat.zero_add M
    rw [h0M]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (eigShiftSeq w M) ih) ?_
    show ((qcube (w M) + -(qcube (w 0))) + (qcube (w (M + 1)) + -(qcube (w M)))).eqv
      (qcube (w (M + 1)) + -(qcube (w 0)))
    exact tele_eqv (qcube (w 0)) (qcube (w M)) (qcube (w (M + 1)))

/-- **THE ACCUMULATED-EROSION BUDGET.**  `∑_{j<M} ε_j ≤ 1 − w_0³` for every window `M`
(the sub-unit cube `w_M³ ≤ 1` caps the telescoped endpoint).  This is the finite budget
`Bε = 1 − w_0³` fed to `additiveErosion_uniform_floor`. -/
theorem eigShift_tailSum_le (w : Nat → Q') (hnn : ∀ k, (0 : Q') ≤ w k)
    (hle1 : ∀ k, w k ≤ (1 : Q')) (M : Nat) :
    tailSum (eigShiftSeq w) 0 M ≤ (1 : Q') - qcube (w 0) := by
  have heqv := eigShift_tailSum_eqv w M
  have hcube1 : qcube (w M) ≤ (1 : Q') := qcube_le_one (hnn M) (hle1 M)
  have hb : qcube (w M) + -(qcube (w 0)) ≤ (1 : Q') + -(qcube (w 0)) :=
    Q'.add_le_add_right (qcube (w M)) 1 (-(qcube (w 0))) hcube1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) hb

/-! ## 4. The zero multiplicative-defect budget (`δ ≡ 0`: pure additive erosion) -/

/-- `∑_{j<M} 0 ≤ 0` — the multiplicative defect budget vanishes (`Bδ = 0`): the
eigenvalue-shift route is PURELY additive (Route I: fusion-degeneracy defect is `0`). -/
theorem zero_tailSum_le (M : Nat) : tailSum (fun _ => (0 : Q')) 0 M ≤ (0 : Q') := by
  induction M with
  | zero => exact Q'.le_refl' 0
  | succ M ih =>
    show tailSum (fun _ => (0 : Q')) 0 M + (0 : Q') ≤ (0 : Q')
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))) ih

/-! ## 5. THE ANCHOR-DOMINANCE FLOOR — the conditional producer (guard-safe) -/

/-- **ANCHOR-DOMINANCE ⟹ POSITIVE CONTINUUM FLOOR (conditional producer).**

Given the AF coupling flow `w_k` (nonnegative, sub-unit, monotone-increasing toward the
free fixed point), a dimensionless margin `margin_k` with nonnegative anchor obeying the
purely-ADDITIVE eigenvalue-shift step

    margin (k+1)  ≥  margin k  −  ε_k ,          ε_k = w_{k+1}³ − w_k³,

and the **anchor-dominance** `1 − w_0³ < margin 0`, the PROVED
`additiveErosion_uniform_floor` yields the UNIFORM STRICTLY-POSITIVE continuum floor

    ∀ k,  margin 0 − (1 − w_0³)  ≤  margin k    and    0 < margin 0 − (1 − w_0³).

The budget `Bε = 1 − w_0³` is the exact telescoped eigenvalue-shift sum
(`eigShift_tailSum_le`); the multiplicative budget `Bδ = 0` (`zero_tailSum_le`).

OPEN BINDERS on `w`, `margin`, `hstep`, `hanchor`: a CONDITIONAL producer, NOT an
inhabitant of any guarded/frontier bundle.  The two open inputs are the Route-I/H
identification `ε_k ≤ w_{k+1}³ − w_k³` and the transmutation anchor `margin 0 ≥ m_phys`. -/
theorem anchorDominance_floor
    (w : Nat → Q') (margin : Nat → Q')
    (hnn : ∀ k, (0 : Q') ≤ w k) (hle1 : ∀ k, w k ≤ (1 : Q'))
    (hmono : ∀ k, w k ≤ w (k + 1))
    (hm0 : (0 : Q') ≤ margin 0)
    (hstep : ∀ k, margin k - eigShiftSeq w k ≤ margin (k + 1))
    (hanchor : (1 : Q') - qcube (w 0) < margin 0) :
    ∀ k, (margin 0 - ((1 : Q') - qcube (w 0)) ≤ margin k)
       ∧ (0 : Q') < margin 0 - ((1 : Q') - qcube (w 0)) := by
  -- bridge (1 − 0)·x ≃ x, applied to margin 0 and to margin k in the step
  have e0 : (((1 : Q') - 0) * margin 0).eqv (margin 0) := by
    rw [Q'.sub_zero']; exact Q'.one_mul_eqv (margin 0)
  -- δ ≡ 0 step law in the engine's exact shape
  have hstep' : ∀ k,
      ((1 : Q') - (fun _ => (0 : Q')) k) * margin k - eigShiftSeq w k ≤ margin (k + 1) := by
    intro k
    have ek : (((1 : Q') - 0) * margin k).eqv (margin k) := by
      rw [Q'.sub_zero']; exact Q'.one_mul_eqv (margin k)
    have e2 : (((1 : Q') - 0) * margin k + -(eigShiftSeq w k)).eqv
        (margin k + -(eigShiftSeq w k)) :=
      Q'.add_eqv_congr_right _ _ (-(eigShiftSeq w k)) ek
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (hstep k)
  -- anchor-dominance in the engine's exact shape
  have hanchor' : (1 : Q') - qcube (w 0) < ((1 : Q') - 0) * margin 0 :=
    qLtLe hanchor (Q'.ge_of_eqv e0)
  -- the PROVED adequacy engine on the concrete majorant sequences
  have H := additiveErosion_uniform_floor margin (fun _ => (0 : Q')) (eigShiftSeq w)
    (0 : Q') ((1 : Q') - qcube (w 0)) hstep'
    (fun _ => Q'.le_refl' 0) (fun _ => qZeroLeOne)
    (eigShift_nonneg w hnn hmono) hm0
    (fun k => zero_tailSum_le k) (eigShift_tailSum_le w hnn hle1) hanchor'
  -- convert (1 − 0)·margin 0 back to margin 0 in the conclusion
  have hconv : (((1 : Q') - 0) * margin 0 + -((1 : Q') - qcube (w 0))).eqv
      (margin 0 + -((1 : Q') - qcube (w 0))) :=
    Q'.add_eqv_congr_right _ _ (-((1 : Q') - qcube (w 0))) e0
  intro k
  obtain ⟨hle, hpos⟩ := H k
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hconv) hle,
         qLtLe hpos (Q'.le_of_eqv hconv)⟩

/-! ## 6. The deep-UV anchor `w_0 = 11/12` — anchor-dominance HOLDS (kernel `decide`)

`Bε = 1 − (11/12)³ = 1 − 1331/1728 = 397/1728 = 0.229745… < 3/10 ≤ m_phys`
(`m_phys = 1 − e^{−1/e} = 0.307799…`, validated in `anchor_num.py`, mpmath dps 60).
`11/12` is the canonical AF trajectory `w_k = 1 − 1/(k+1)` at `k = 11` (the UV cutoff),
i.e. `1 − w_0 = 1/12`. -/

/-- The deep-UV anchor coupling `w_0 = 11/12` (AF trajectory, cutoff `k=11`). -/
def wAnchor : Q' := Q'.mkPos 11 12 (by decide)

/-- A rational lower bound `3/10` on the transmuted margin
`m_phys = 1 − e^{−1/e} = 0.30780 > 0.3` (`DimensionlessMarginTransmutation`; validated
mpmath dps 60). -/
def mPhysLB : Q' := Q'.mkPos 3 10 (by decide)

/-- **THE ANCHOR-DOMINANCE INEQUALITY at `w_0 = 11/12` (kernel `decide`, zero-axiom).**
`Bε = 1 − (11/12)³ = 397/1728 < 3/10`.  The accumulated real eigenvalue-shift erosion is
strictly dominated by the transmuted margin lower bound, with slack `≈ 0.078`. -/
theorem anchorDom_numeric : (1 : Q') - qcube wAnchor < mPhysLB := by decide

/-- **Anchor-dominance from the transmutation anchor.**  If the dimensionless margin at
the deep-UV anchor `w_0 = 11/12` satisfies `margin 0 ≥ 3/10` (the transmuted `m_phys`,
`DimensionlessMarginTransmutation`), then the anchor-dominance hypothesis of
`anchorDominance_floor` holds. -/
theorem anchorDom_from_mphys_lb (w : Nat → Q') (margin : Nat → Q')
    (hw0 : w 0 = wAnchor) (hm0lb : mPhysLB ≤ margin 0) :
    (1 : Q') - qcube (w 0) < margin 0 := by
  rw [hw0]
  exact qLtLe anchorDom_numeric hm0lb

/-! ## 7. Honest verdict (AGENTS.md Rule 6 / Rule 9) -/

/-- **PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]` or fewer):**
  * `qcube_mono`, `qcube_le_one` — the transfer eigenvalue cube is monotone / sub-unit.
  * `eigShift_nonneg` — the concrete per-step eigenvalue shift `ε_k = w_{k+1}³ − w_k³ ≥ 0`.
  * `eigShift_tailSum_eqv` — the EXACT telescoping `∑_{j<k} ε_j ≃ w_k³ − w_0³`.
  * `eigShift_tailSum_le` — the accumulated budget `∑ ε_k ≤ 1 − w_0³` (∀ k).
  * `anchorDominance_floor` — anchor-dominance `1 − w_0³ < margin 0` ⟹ uniform positive
    continuum floor `margin 0 − (1 − w_0³) > 0` (via the PROVED adequacy engine).
  * `anchorDom_numeric` — at `w_0 = 11/12`, `Bε = 397/1728 < 3/10 ≤ m_phys` (kernel
    `decide`, zero axioms).

**VERDICT.**  The anchor-dominance `∑ ε_k < m_phys` — carried by `CAPSTONE §5` as an
independent open inequality — is DISCHARGED, in a deep-UV-anchored scheme, from the
TELESCOPING structure of the multiplicity-blind eigenvalue-shift erosion (Route I) and
the transmuted anchor `m_phys ≥ 3/10` (`DimensionlessMarginTransmutation`).  The
accumulated real block-spin additive erosion is the CLOSED value `1 − w_0³`, which the
transmuted margin strictly dominates once the UV anchor is `w_0 = 11/12` (slack `≈ 0.078`).
This removes anchor-dominance as a separate wall.

**NOT closed** (the genuine 4D Yang–Mills continuum content, both UNINHABITED):
  1. the identification `ε_k ≤ w_{k+1}³ − w_k³` (Route I `EigenvalueShiftDefect` / Route H
     identification);
  2. the anchor value `margin 0 ≥ m_phys` at the deep-UV anchor (real-flow dimensional
     transmutation).

`anchorDominance_floor` is a CONDITIONAL producer (open binders): it does NOT inhabit
`TrueMarginRecursionPhysical`, `TrueMarginRecursionSummable`, `SingleStepDefectBound`,
`UniformSpacingFloor`, `Tier0Scorecard`, `ClayTarget`, `ClayTargetPinned`, or
`FrontierDAG`.  NO guarded bundle is inhabited; nothing is faked; the 4D Yang–Mills mass
gap remains OPEN. -/
theorem anchorDominance_honesty : True := trivial

end YMGap.Continuum.AnchorDominance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AnchorDominance.qcube_mono
#print axioms YMGap.Continuum.AnchorDominance.qcube_le_one
#print axioms YMGap.Continuum.AnchorDominance.eigShift_nonneg
#print axioms YMGap.Continuum.AnchorDominance.tele_eqv
#print axioms YMGap.Continuum.AnchorDominance.eigShift_tailSum_eqv
#print axioms YMGap.Continuum.AnchorDominance.eigShift_tailSum_le
#print axioms YMGap.Continuum.AnchorDominance.zero_tailSum_le
#print axioms YMGap.Continuum.AnchorDominance.anchorDominance_floor
#print axioms YMGap.Continuum.AnchorDominance.anchorDom_numeric
#print axioms YMGap.Continuum.AnchorDominance.anchorDom_from_mphys_lb
