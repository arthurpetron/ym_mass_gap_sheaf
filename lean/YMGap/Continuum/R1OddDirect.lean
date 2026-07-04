/-
Track B / local-CLT — the DIRECT closure of the binding odd-centre cell of R1
(`R1CaseSplit.OddCentreCellLE w`), bypassing the sharp φ / theta enclosure.

# What this file PROVES (axiom-clean, no `sorry`)

For `0 ≤ w ≤ 1/2`, the binding odd-centre cell of R1 is CLOSED OUTRIGHT:

    `oddCentreCell` :  w ≤ 1/2 → ∀ s, s % 2 = 0 → FullRangeFloor w s .

This is exactly `R1CaseSplit.OddCentreCellLE w` — one of the two remaining named-open
cells of R1 (`SaddleVarianceFloor`).  It SUPERSEDES the abstract-ThetaData route of
`R1OddL2Chain`.

## The argument (all elementary, LOOSE geometric tails)

`FullRangeFloor w s` is the cleared `Δ²V ≥ −2`, `V(t) = dmomNfull w t / acNfull w t`, centred
at the ODD window `s+1` (for even `s`), with EVEN neighbours `s, s+2`.  Dividing out the positive
masses it is `2·V(s+1) ≤ V(s) + V(s+2) + 2`.  Two loose moment bounds suffice:

  * `evenVarLower` :  `7·w²·acNfull w N ≤ 2·dmomNfull w N`  for even `N = 2m ≥ 2`
      (i.e. `V(even) ≥ 7/2·w²`).  PROVED by extracting the three central antidiagonal terms
      `p ∈ {m−1, m, m+1}` (rest sign-definite `≥ 0`) and the exact neighbour ratio
      `μ_{m±1} = m(m+2)/(m+1)²·w²·μ_m ≥ 3/4·w²·μ_m`.  No infinite tail.
  * `oddVarUpper` :  `dmomNfull w N ≤ acNfull w N + 9·w⁴·acNfull w N`  for odd `N ≥ 1`
      (i.e. `V(odd) ≤ 1 + 9·w⁴`).  PROVED by the two-point tie (`⟨D²⟩ ≥ 1`) plus a LOOSE
      geometric majorant of the `|D| ≥ 3` excess against the two central `|D| = 1` terms,
      closed by a geometric tail `Σ 8·(1/16)ᵏ ≤ 9`.

Then, for odd centre `s+1` (`s` even, `s ≥ 2`), `oddCellArith` combines the two even-neighbour
lower bounds, the odd-centre upper bound, and `36·w⁴ ≤ 14·w²` (on `w ≤ 1/2`) into the cleared
floor, all subtraction-free over the positive masses.  The base window `s = 0` (centre `N = 1`) is
`CircleFourierPowerModel.fullRangeFloor_zero`.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is axiom-checked at file end; permitted output is
`propext` / `Quot.sound` only (via the `Q'` setoid).  No `Classical.*`, no `native_decide`, no
`sorry`, no custom `axiom`.  All witnesses are `Type`-level / `Q'`-valued data.
-/
import YMGap.Continuum.R1CaseSplit
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.R1OddDirect

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.DiscreteLaplaceMargin
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CubeRatioBounds

/-- Cancellation-free ring closer for `Q'.eqv` (copy of the `R1EvenCentreBound` macro). -/
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, R1EvenCentreBound.neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 0. `Q'` shorthands and small helpers. -/

/-- `1/16` as an exact `Q'`. -/
def sixteenth : Q' := Q'.mkPos 1 16 (by decide)

theorem q_mul_congr {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha) (Q'.mul_eqv_congr_left a' b b' hb)

/-- From `a ≤ b` conclude `0 ≤ b + -a`. -/
theorem nonneg_of_le {a b : Q'} (h : a ≤ b) : (0 : Q') ≤ b + -a := by
  have h2 := Q'.add_le_add_right a b (-a) h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv a)) h2

/-- From `0 ≤ b + -a` conclude `a ≤ b`. -/
theorem le_of_nonneg_sub {a b : Q'} (h : (0 : Q') ≤ b + -a) : a ≤ b := by
  have h2 := Q'.add_le_add_right 0 (b + -a) a h
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' a))) ?_
  refine Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b (-a) a) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left b _ _ (Q'.neg_add_self_eqv a)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' b)

/-! ## 1. Nat exponent shift lemmas and the two exponent identities. -/

theorem c4_shift1 (n : Nat) : c4 (n + 1) = c4 n + 2 * n + 3 := by
  simp only [c4, Nat.mul_add, Nat.add_mul]; omega

theorem c4_shift2 (n : Nat) : c4 (n + 2) = c4 n + 4 * n + 8 := by
  simp only [c4, Nat.mul_add, Nat.add_mul]; omega

/-- `C₄(k+2) + C₄ k = 2·C₄(k+1) + 2` (even-neighbour exponent shift). -/
theorem evenExp (k : Nat) : c4 (k + 2) + c4 k = 2 * c4 (k + 1) + 2 := by
  rw [c4_shift2 k, c4_shift1 k]; omega

/-- `C₄ i + C₄(i+2j+1) = C₄(i+j) + C₄(i+j+1) + 2·j·(j+1)` (odd-centre exponent shift). -/
theorem oddExp (i : Nat) :
    ∀ j, c4 i + c4 (i + 2 * j + 1) = c4 (i + j) + c4 (i + j + 1) + 2 * j * (j + 1)
  | 0 => by
      rw [show i + 2 * 0 + 1 = i + 1 from by omega, show i + 0 = i from by omega,
          show i + 0 + 1 = i + 1 from by omega]; omega
  | j + 1 => by
      have ih := oddExp i j
      have s1 : c4 (i + 2 * (j + 1) + 1) = c4 (i + 2 * j + 1) + 4 * (i + 2 * j + 1) + 8 := by
        rw [show i + 2 * (j + 1) + 1 = (i + 2 * j + 1) + 2 from by omega]; exact c4_shift2 _
      have s2 : c4 (i + (j + 1)) = c4 (i + j) + 2 * (i + j) + 3 := by
        rw [show i + (j + 1) = (i + j) + 1 from by omega]; exact c4_shift1 _
      have s3 : c4 (i + (j + 1) + 1) = c4 (i + j + 1) + 2 * (i + j + 1) + 3 := by
        rw [show i + (j + 1) + 1 = (i + j + 1) + 1 from by omega]; exact c4_shift1 _
      have hj1 : 2 * j * (j + 1) = 2 * (j * j) + 2 * j := by
        simp only [Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
      have hj2 : 2 * (j + 1) * (j + 1 + 1) = 2 * (j * j) + 6 * j + 4 := by
        simp only [Nat.mul_assoc, Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
      omega

/-! ## 2. The coeff-product normal form. -/

/-- `coeffW w s · coeffW w t ≃ ofNat((s+1)(t+1)) · w^{C₄ s + C₄ t}`. -/
theorem coeffMul (w : Q') (s t : Nat) :
    (coeffW w s * coeffW w t).eqv
      (Q'.ofNat ((s + 1) * (t + 1)) * qpow w (c4 s + c4 t)) := by
  have hrew : (coeffW w s * coeffW w t).eqv
      ((Q'.ofNat (s + 1) * Q'.ofNat (t + 1)) * (qpow w (c4 s) * qpow w (c4 t))) := by
    show (Q'.ofNat (s + 1) * qpow w (c4 s) * (Q'.ofNat (t + 1) * qpow w (c4 t))).eqv _
    ring_qeqv
  refine Q'.eqv_trans _ _ _ hrew ?_
  exact q_mul_congr (Q'.eqv_symm (R1EvenCentreBound.ofNat_mul_eqv (s + 1) (t + 1)))
    (Q'.eqv_symm (qpow_add w (c4 s) (c4 t)))

/-! ## 3. The `w`-power arithmetic on `w ≤ 1/2`. -/

/-- On `0 ≤ w ≤ 1/2`, `w² ≤ 1/4`. -/
theorem w2_le_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ R1CaseSplit.half) :
    qpow w 2 ≤ quarter := by
  have hmono : qpow w 2 ≤ qpow R1CaseSplit.half 2 := HeatKernelGap.qpow_mono hw0 hwh 2
  exact Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv (by decide))

/-- `w⁴ ≃ w²·w²`. -/
theorem w4_eq_w2w2 (w : Q') : (qpow w 4).eqv (qpow w 2 * qpow w 2) := qpow_add w 2 2

/-- On `0 ≤ w ≤ 1/2`, `36·w⁴ ≤ 14·w²`. -/
theorem w4_arith {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ R1CaseSplit.half) :
    Q'.ofNat 36 * qpow w 4 ≤ Q'.ofNat 14 * qpow w 2 := by
  have hw2q : qpow w 2 ≤ quarter := w2_le_quarter hw0 hwh
  have hw2nn : (0 : Q') ≤ qpow w 2 := qpow_nonneg w hw0 2
  have e1 : (Q'.ofNat 36 * qpow w 4).eqv (Q'.ofNat 36 * qpow w 2 * qpow w 2) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (w4_eq_w2w2 w)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 36) (qpow w 2) (qpow w 2))
  have h36nn : (0 : Q') ≤ Q'.ofNat 36 * qpow w 2 :=
    Q'.mul_nonneg _ _ (by decide) hw2nn
  have hstep : Q'.ofNat 36 * qpow w 2 * qpow w 2 ≤ Q'.ofNat 36 * qpow w 2 * quarter :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hw2q h36nn
  have e2 : (Q'.ofNat 36 * qpow w 2 * quarter).eqv (Q'.ofNat 9 * qpow w 2) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 36) (qpow w 2) quarter) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (qpow w 2) quarter)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 36) quarter (qpow w 2))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  have h914 : Q'.ofNat 9 * qpow w 2 ≤ Q'.ofNat 14 * qpow w 2 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) hw2nn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ hstep (Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) h914))

/-! ## 4. The odd-centre majorant `μ_p ≤ w^{2j(j+1)}·μ_c`. -/

/-- **`oddCenterBound`** — for `j ≤ c`, the pair term `coeffW(c−j)·coeffW(c+1+j)` is dominated by
`w^{2j(j+1)}·(coeffW c · coeffW (c+1))`. -/
theorem oddCenterBound {w : Q'} (hw0 : (0 : Q') ≤ w) (c j : Nat) (hj : j ≤ c) :
    coeffW w (c - j) * coeffW w (c + 1 + j)
      ≤ qpow w (2 * j * (j + 1)) * (coeffW w c * coeffW w (c + 1)) := by
  obtain ⟨i, rfl⟩ := Nat.le.dest hj      -- c = j + i
  rw [show (j + i) - j = i from by omega, show (j + i) + 1 + j = i + 2 * j + 1 from by omega]
  have hL := coeffMul w i (i + 2 * j + 1)
  have hC := coeffMul w (j + i) (j + i + 1)
  have hexp : c4 i + c4 (i + 2 * j + 1)
      = (c4 (j + i) + c4 (j + i + 1)) + 2 * j * (j + 1) := by
    have h := oddExp i j
    rw [show i + j = j + i from by omega] at h
    omega
  have hsplit : (qpow w (c4 i + c4 (i + 2 * j + 1))).eqv
      (qpow w (2 * j * (j + 1)) * qpow w (c4 (j + i) + c4 (j + i + 1))) := by
    rw [hexp]
    refine Q'.eqv_trans _ _ _ (qpow_add w (c4 (j + i) + c4 (j + i + 1)) (2 * j * (j + 1))) ?_
    exact Q'.mul_comm_eqv _ _
  have hLHS : (coeffW w i * coeffW w (i + 2 * j + 1)).eqv
      (Q'.ofNat ((i + 1) * (i + 2 * j + 1 + 1))
        * (qpow w (2 * j * (j + 1)) * qpow w (c4 (j + i) + c4 (j + i + 1)))) :=
    Q'.eqv_trans _ _ _ hL (Q'.mul_eqv_congr_left _ _ _ hsplit)
  have hRHS : (qpow w (2 * j * (j + 1)) * (coeffW w (j + i) * coeffW w (j + i + 1))).eqv
      (Q'.ofNat ((j + i + 1) * (j + i + 1 + 1))
        * (qpow w (2 * j * (j + 1)) * qpow w (c4 (j + i) + c4 (j + i + 1)))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hC) ?_
    ring_qeqv
  have hnat : (i + 1) * (i + 2 * j + 1 + 1) ≤ (j + i + 1) * (j + i + 1 + 1) := by
    have hid : (j + i + 1) * (j + i + 1 + 1)
        = (i + 1) * (i + 2 * j + 1 + 1) + (j * j + j) := by
      simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul, Nat.mul_comm j i]; omega
    omega
  have hpownn : (0 : Q') ≤ qpow w (2 * j * (j + 1)) * qpow w (c4 (j + i) + c4 (j + i + 1)) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 _) (qpow_nonneg w hw0 _)
  have hscal : Q'.ofNat ((i + 1) * (i + 2 * j + 1 + 1))
      * (qpow w (2 * j * (j + 1)) * qpow w (c4 (j + i) + c4 (j + i + 1)))
      ≤ Q'.ofNat ((j + i + 1) * (j + i + 1 + 1))
        * (qpow w (2 * j * (j + 1)) * qpow w (c4 (j + i) + c4 (j + i + 1))) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (CReal.ofNat_le_ofNat hnat) hpownn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) (Q'.le_trans' _ _ _ hscal (Q'.ge_of_eqv hRHS))

/-! ## 5. The even-neighbour lower ratio `3·w²·μ_m ≤ 4·μ_{m+1}`. -/

/-- **`evenNeighborLB`** — for `m = k+1 ≥ 1`, `3·(w²·(coeffW m)²) ≤ 4·(coeffW(m+1)·coeffW(m−1))`,
i.e. `μ_{m+1} ≥ 3/4·w²·μ_m`. -/
theorem evenNeighborLB {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    Q'.ofNat 3 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1)))
      ≤ Q'.ofNat 4 * (coeffW w (k + 2) * coeffW w k) := by
  have hC := coeffMul w (k + 1) (k + 1)
  have hN := coeffMul w (k + 2) k
  have hsplit : (qpow w (c4 (k + 2) + c4 k)).eqv
      (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1))) := by
    have he : c4 (k + 2) + c4 k = (c4 (k + 1) + c4 (k + 1)) + 2 := by
      have := evenExp k; omega
    rw [he]
    refine Q'.eqv_trans _ _ _ (qpow_add w (c4 (k + 1) + c4 (k + 1)) 2) ?_
    exact Q'.mul_comm_eqv _ _
  have hGnn : (0 : Q') ≤ qpow w (c4 (k + 1) + c4 (k + 1)) := qpow_nonneg w hw0 _
  have hw2nn : (0 : Q') ≤ qpow w 2 := qpow_nonneg w hw0 2
  have hXnn : (0 : Q') ≤ qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1)) :=
    Q'.mul_nonneg _ _ hw2nn hGnn
  -- LHS ≃ ofNat(3·(k+2)²) · (w²·G)
  have hLHS : (Q'.ofNat 3 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1)))).eqv
      (Q'.ofNat (3 * ((k + 1 + 1) * (k + 1 + 1)))
        * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1)))) := by
    have hstep : (Q'.ofNat 3 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1)))).eqv
        (Q'.ofNat 3 * (qpow w 2 *
          (Q'.ofNat ((k + 1 + 1) * (k + 1 + 1)) * qpow w (c4 (k + 1) + c4 (k + 1))))) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hC)
    refine Q'.eqv_trans _ _ _ hstep ?_
    have hrear : (Q'.ofNat 3 * (qpow w 2 *
        (Q'.ofNat ((k + 1 + 1) * (k + 1 + 1)) * qpow w (c4 (k + 1) + c4 (k + 1))))).eqv
        ((Q'.ofNat 3 * Q'.ofNat ((k + 1 + 1) * (k + 1 + 1)))
          * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1)))) := by
      ring_qeqv
    refine Q'.eqv_trans _ _ _ hrear ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (R1EvenCentreBound.ofNat_mul_eqv 3 ((k + 1 + 1) * (k + 1 + 1))))
  -- RHS ≃ ofNat(4·(k+3)(k+1)) · (w²·G)
  have hRHS : (Q'.ofNat 4 * (coeffW w (k + 2) * coeffW w k)).eqv
      (Q'.ofNat (4 * ((k + 2 + 1) * (k + 1)))
        * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1)))) := by
    have hstep : (Q'.ofNat 4 * (coeffW w (k + 2) * coeffW w k)).eqv
        (Q'.ofNat 4 * (Q'.ofNat ((k + 2 + 1) * (k + 1))
          * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1))))) := by
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ _ _ hN ?_
      exact Q'.mul_eqv_congr_left _ _ _ hsplit
    refine Q'.eqv_trans _ _ _ hstep ?_
    have hrear : (Q'.ofNat 4 * (Q'.ofNat ((k + 2 + 1) * (k + 1))
        * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1))))).eqv
        ((Q'.ofNat 4 * Q'.ofNat ((k + 2 + 1) * (k + 1)))
          * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1)))) := by
      ring_qeqv
    refine Q'.eqv_trans _ _ _ hrear ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (R1EvenCentreBound.ofNat_mul_eqv 4 ((k + 2 + 1) * (k + 1))))
  have hnat : 3 * ((k + 1 + 1) * (k + 1 + 1)) ≤ 4 * ((k + 2 + 1) * (k + 1)) := by
    have hid : 4 * ((k + 2 + 1) * (k + 1))
        = 3 * ((k + 1 + 1) * (k + 1 + 1)) + (k * k + 4 * k) := by
      simp only [Nat.mul_add, Nat.add_mul]; omega
    omega
  have hcore : Q'.ofNat (3 * ((k + 1 + 1) * (k + 1 + 1)))
        * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1)))
      ≤ Q'.ofNat (4 * ((k + 2 + 1) * (k + 1)))
        * (qpow w 2 * qpow w (c4 (k + 1) + c4 (k + 1))) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (CReal.ofNat_le_ofNat hnat) hXnn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv hRHS))

/-! ## 6. `dsq` facts on the even lattice. -/

/-- `dsq p (2m) ≥ 4` off the centre `p ≠ m`. -/
theorem dsq_even_off {m p : Nat} (hpm : p ≠ m) : 4 ≤ dsq p (2 * m) := by
  show 4 ≤ (2 * m - 2 * p) * (2 * m - 2 * p) + (2 * p - 2 * m) * (2 * p - 2 * m)
  rcases Nat.lt_or_ge p m with h | h
  · have e : 2 * m - 2 * p = 2 * (m - p) := by omega
    have hpos : 1 ≤ m - p := by omega
    have hsq : 2 * 2 ≤ (2 * (m - p)) * (2 * (m - p)) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpos) (Nat.mul_le_mul_left 2 hpos)
      simpa using this
    rw [e]; omega
  · have hgt : m < p := by omega
    have e : 2 * p - 2 * m = 2 * (p - m) := by omega
    have hpos : 1 ≤ p - m := by omega
    have hsq : 2 * 2 ≤ (2 * (p - m)) * (2 * (p - m)) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpos) (Nat.mul_le_mul_left 2 hpos)
      simpa using this
    rw [e]; omega

/-- `dsq k (2(k+1)) = 4` (the `m−1` neighbour, `m = k+1`). -/
theorem dsq_lo (k : Nat) : dsq k (2 * (k + 1)) = 4 := by
  show (2 * (k + 1) - 2 * k) * (2 * (k + 1) - 2 * k)
      + (2 * k - 2 * (k + 1)) * (2 * k - 2 * (k + 1)) = 4
  rw [show 2 * (k + 1) - 2 * k = 2 from by omega, show 2 * k - 2 * (k + 1) = 0 from by omega]

/-- `dsq (k+2) (2(k+1)) = 4` (the `m+1` neighbour, `m = k+1`). -/
theorem dsq_hi (k : Nat) : dsq (k + 2) (2 * (k + 1)) = 4 := by
  show (2 * (k + 1) - 2 * (k + 2)) * (2 * (k + 1) - 2 * (k + 2))
      + (2 * (k + 2) - 2 * (k + 1)) * (2 * (k + 2) - 2 * (k + 1)) = 4
  rw [show 2 * (k + 1) - 2 * (k + 2) = 0 from by omega, show 2 * (k + 2) - 2 * (k + 1) = 2 from by omega]

/-- `dsq (k+1) (2(k+1)) = 0` (the centre, `m = k+1`). -/
theorem dsq_ctr (k : Nat) : dsq (k + 1) (2 * (k + 1)) = 0 := by
  show (2 * (k + 1) - 2 * (k + 1)) * (2 * (k + 1) - 2 * (k + 1))
      + (2 * (k + 1) - 2 * (k + 1)) * (2 * (k + 1) - 2 * (k + 1)) = 0
  rw [show 2 * (k + 1) - 2 * (k + 1) = 0 from by omega]

/-! ## 7. Finite-sum extraction of the three central terms (for the even lower bound). -/

/-- `0 ≤ fsum f n` from termwise nonnegativity below `n`. -/
theorem fsum_nonneg_lt {f : Nat → Q'} (n : Nat) (h : ∀ i, i < n → (0 : Q') ≤ f i) :
    (0 : Q') ≤ fsum f n :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (R1EvenCentreBound.fsum_zero_fun n))
    (fsum_mono_lt n (fun i hi => h i hi))

/-- **`fsum_extract3`** — the three central terms `p ∈ {k, k+1, k+2}` are `≤` the whole sum when all
other terms are `≥ 0`.  (`k+1` is the odd centre `m`; its neighbours are `k`, `k+2`.) -/
theorem fsum_extract3 (e : Nat → Q') (k : Nat)
    (hrest : ∀ p, p ≠ k + 1 → (0 : Q') ≤ e p) :
    e k + e (k + 1) + e (k + 2) ≤ fsum e (2 * (k + 1) + 1) := by
  rw [show 2 * (k + 1) + 1 = k + (3 + k) from by omega]
  have hsplit1 := R1EvenCentreBound.fsum_split e k (3 + k)
  have hsplit2 := R1EvenCentreBound.fsum_split (fun i => e (k + i)) 3 k
  have hg3 : (fsum (fun i => e (k + i)) 3).eqv (e k + e (k + 1) + e (k + 2)) := by
    show (((0 + e (k + 0)) + e (k + 1)) + e (k + 2)).eqv (e k + e (k + 1) + e (k + 2))
    refine Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _ ?_)
    exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) (Q'.eqv_of_eq (congrArg e (by omega)))
  have hP : (0 : Q') ≤ fsum e k := fsum_nonneg_lt k (fun i hi => hrest i (by omega))
  have hS : (0 : Q') ≤ fsum (fun i => e (k + (3 + i))) k :=
    fsum_nonneg_lt k (fun i _ => hrest (k + (3 + i)) (by omega))
  -- target ≤ fsum g (3+k)
  have htail : (e k + e (k + 1) + e (k + 2)) ≤ fsum (fun i => e (k + i)) (3 + k) := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hsplit2)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hg3) (Q'.add_le_self_of_nonneg _ _ hS)
  -- fsum g (3+k) ≤ fsum e k + fsum g (3+k) ≃ fsum e (k+(3+k))
  refine Q'.le_trans' _ _ _ htail ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hsplit1)
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (fsum (fun i => e (k + i)) (3 + k))))) ?_
  exact Q'.add_le_add_right 0 (fsum e k) (fsum (fun i => e (k + i)) (3 + k)) hP

/-! ## 8. The abstract triple lower bound (`14·w²ν + 7·w²κ ≤ 16·ν`). -/

theorem tripleBound {ν κ w2 : Q'} (hν0 : (0 : Q') ≤ ν) (hw2q : w2 ≤ quarter)
    (hNB : Q'.ofNat 3 * (w2 * κ) ≤ Q'.ofNat 4 * ν) :
    Q'.ofNat 14 * (w2 * ν) + Q'.ofNat 7 * (w2 * κ) ≤ Q'.ofNat 16 * ν := by
  -- h1 : 84·(w2·ν) ≤ 21·ν
  have h84w2 : Q'.ofNat 84 * w2 ≤ Q'.ofNat 21 := by
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hw2q (by decide)) ?_
    exact Q'.le_of_eqv (by decide)
  have h1 : Q'.ofNat 84 * (w2 * ν) ≤ Q'.ofNat 21 * ν := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ h84w2 hν0
  -- h2 : 42·(w2·κ) ≤ 56·ν
  have h2 : Q'.ofNat 42 * (w2 * κ) ≤ Q'.ofNat 56 * ν := by
    have hm := Q'.mul_le_mul_of_nonneg_left (Q'.ofNat 3 * (w2 * κ)) (Q'.ofNat 4 * ν)
      (Q'.ofNat 14) hNB (by decide : (0:Q') ≤ Q'.ofNat 14)
    have eL : (Q'.ofNat 42 * (w2 * κ)).eqv (Q'.ofNat 14 * (Q'.ofNat 3 * (w2 * κ))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 42) (Q'.ofNat 14 * Q'.ofNat 3) (w2 * κ) (by decide)) ?_
      exact Q'.mul_assoc_eqv (Q'.ofNat 14) (Q'.ofNat 3) (w2 * κ)
    have eR : (Q'.ofNat 14 * (Q'.ofNat 4 * ν)).eqv (Q'.ofNat 56 * ν) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 14) (Q'.ofNat 4) ν)) ?_
      exact Q'.mul_eqv_congr_right (Q'.ofNat 14 * Q'.ofNat 4) (Q'.ofNat 56) ν (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv eR))
  -- 84A + 42B ≤ 21ν + 56ν ≃ 77ν ≤ 96ν
  have hsum : Q'.ofNat 84 * (w2 * ν) + Q'.ofNat 42 * (w2 * κ)
      ≤ Q'.ofNat 96 * ν := by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add h1 h2) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (R1CaseSplit.add_mul_local (Q'.ofNat 21) (Q'.ofNat 56) ν))) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right (Q'.ofNat 21 + Q'.ofNat 56) (Q'.ofNat 77) ν (by decide))) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) hν0
  -- cancel the factor 6
  refine Q'.le_of_mul_le_mul_left (c := Q'.ofNat 6) ?_ (by decide)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv ?_))
  · -- 6·(14A+7B) ≃ 84A + 42B
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 6) _ _) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) (Q'.ofNat 14) (w2 * ν))) ?_
      exact Q'.mul_eqv_congr_right (Q'.ofNat 6 * Q'.ofNat 14) (Q'.ofNat 84) (w2 * ν) (by decide)
    · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) (Q'.ofNat 7) (w2 * κ))) ?_
      exact Q'.mul_eqv_congr_right (Q'.ofNat 6 * Q'.ofNat 7) (Q'.ofNat 42) (w2 * κ) (by decide)
  · -- 6·(16ν) ≃ 96ν
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) (Q'.ofNat 16) ν)) ?_
    exact Q'.mul_eqv_congr_right (Q'.ofNat 6 * Q'.ofNat 16) (Q'.ofNat 96) ν (by decide)

/-- `ofNat c · A + ofNat d · A ≃ ofNat (c+d) · A`. -/
theorem ofNat_smul_add (c d : Nat) (A : Q') :
    (Q'.ofNat c * A + Q'.ofNat d * A).eqv (Q'.ofNat (c + d) * A) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (R1CaseSplit.add_mul_local (Q'.ofNat c) (Q'.ofNat d) A)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv c d))

/-! ## 9. `evenVarLower` — `7·w²·acNfull ≤ 2·dmomNfull` on the even lattice. -/

/-- **`evenVarLower`** — for even `N = 2m ≥ 2` and `0 ≤ w ≤ 1/2`, `V(even) ≥ 7/2·w²`, cleared as
`7·w²·acNfull w N ≤ 2·dmomNfull w N`. -/
theorem evenVarLower {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ R1CaseSplit.half)
    (m : Nat) (hm : 1 ≤ m) :
    Q'.ofNat 7 * (qpow w 2 * acNfull w (2 * m)) ≤ Q'.ofNat 2 * dmomNfull w (2 * m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hw2q : qpow w 2 ≤ quarter := w2_le_quarter hw0 hwh
  have hw2nn : (0 : Q') ≤ qpow w 2 := qpow_nonneg w hw0 2
  -- the antidiagonal weight and the two per-term sequences
  let μ : Nat → Q' := fun p => coeffW w p * coeffW w (2 * (k + 1) - p)
  let Rf : Nat → Q' := fun p => Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * (k + 1))) * μ p)
  let Lf : Nat → Q' := fun p => Q'.ofNat 7 * (qpow w 2 * μ p)
  have hμnn : ∀ p, (0 : Q') ≤ μ p := fun p =>
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 p) (coeffW_nonneg hw0 _)
  -- (1) rewrite goal into fsum form
  have hLsum : (Q'.ofNat 7 * (qpow w 2 * acNfull w (2 * (k + 1)))).eqv
      (fsum Lf (2 * (k + 1) + 1)) := by
    show (Q'.ofNat 7 * (qpow w 2 * fsum μ (2 * (k + 1) + 1))).eqv _
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (fsum_const_mul (qpow w 2) μ (2 * (k + 1) + 1))) ?_
    exact fsum_const_mul (Q'.ofNat 7) (fun p => qpow w 2 * μ p) (2 * (k + 1) + 1)
  have hRsum : (Q'.ofNat 2 * dmomNfull w (2 * (k + 1))).eqv (fsum Rf (2 * (k + 1) + 1)) :=
    fsum_const_mul (Q'.ofNat 2)
      (fun p => Q'.ofNat (dsq p (2 * (k + 1))) * μ p) (2 * (k + 1) + 1)
  -- (2) off-centre nonnegativity of e = R + -L
  have hrest : ∀ p, p ≠ k + 1 → (0 : Q') ≤ Rf p + -(Lf p) := by
    intro p hp
    have hdsq : 4 ≤ dsq p (2 * (k + 1)) := dsq_even_off (m := k + 1) hp
    have hscal : Q'.ofNat 7 * qpow w 2 ≤ Q'.ofNat 2 * Q'.ofNat (dsq p (2 * (k + 1))) := by
      have s1 : Q'.ofNat 7 * qpow w 2 ≤ Q'.ofNat 7 * quarter :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hw2q (by decide)
      have s2 : Q'.ofNat 7 * quarter ≤ Q'.ofNat 8 := by decide
      have s3 : Q'.ofNat 8 ≤ Q'.ofNat 2 * Q'.ofNat (dsq p (2 * (k + 1))) := by
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : (Q'.ofNat 8).eqv (Q'.ofNat 2 * Q'.ofNat 4))) ?_
        exact Q'.mul_le_mul_of_nonneg_left _ _ _ (CReal.ofNat_le_ofNat hdsq) (by decide)
      exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ s2 s3)
    have hmul : (Q'.ofNat 7 * qpow w 2) * μ p
        ≤ (Q'.ofNat 2 * Q'.ofNat (dsq p (2 * (k + 1)))) * μ p :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hscal (hμnn p)
    have hLR : Lf p ≤ Rf p := by
      show Q'.ofNat 7 * (qpow w 2 * μ p)
        ≤ Q'.ofNat 2 * (Q'.ofNat (dsq p (2 * (k + 1))) * μ p)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 7) (qpow w 2) (μ p)))) ?_
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_of_eqv (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat (dsq p (2 * (k + 1)))) (μ p)))
    exact nonneg_of_le hLR
  -- (3) the three central terms.  ν = coeffW(k+2)·coeffW k, κ = coeffW(k+1)²
  have hνk : (μ k).eqv (coeffW w (k + 2) * coeffW w k) := by
    show (coeffW w k * coeffW w (2 * (k + 1) - k)).eqv (coeffW w (k + 2) * coeffW w k)
    rw [show 2 * (k + 1) - k = k + 2 from by omega]
    exact Q'.mul_comm_eqv _ _
  have hνk2 : (μ (k + 2)).eqv (coeffW w (k + 2) * coeffW w k) := by
    show (coeffW w (k + 2) * coeffW w (2 * (k + 1) - (k + 2))).eqv (coeffW w (k + 2) * coeffW w k)
    rw [show 2 * (k + 1) - (k + 2) = k from by omega]; exact Q'.eqv_refl _
  have hκ : (μ (k + 1)).eqv (coeffW w (k + 1) * coeffW w (k + 1)) := by
    show (coeffW w (k + 1) * coeffW w (2 * (k + 1) - (k + 1))).eqv
      (coeffW w (k + 1) * coeffW w (k + 1))
    rw [show 2 * (k + 1) - (k + 1) = k + 1 from by omega]; exact Q'.eqv_refl _
  -- abbreviate
  have hν0 : (0 : Q') ≤ coeffW w (k + 2) * coeffW w k :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)
  have hNB : Q'.ofNat 3 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1)))
      ≤ Q'.ofNat 4 * (coeffW w (k + 2) * coeffW w k) := evenNeighborLB hw0 k
  have htb := tripleBound hν0 hw2q hNB
  -- eLsum : Lf k + Lf(k+1) + Lf(k+2) ≃ 14·(w²ν) + 7·(w²κ)
  have eL : (Lf k + Lf (k + 1) + Lf (k + 2)).eqv
      (Q'.ofNat 14 * (qpow w 2 * (coeffW w (k + 2) * coeffW w k))
        + Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1)))) := by
    have c0 : (Lf k).eqv (Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 2) * coeffW w k))) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hνk)
    have c1 : (Lf (k + 1)).eqv (Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1)))) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hκ)
    have c2 : (Lf (k + 2)).eqv (Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 2) * coeffW w k))) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hνk2)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.add_eqv_congr' c0 c1) c2) ?_
    -- (7A + 7B) + 7A ≃ 14A + 7B ,  A = w²ν, B = w²κ
    have hrear : ((Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 2) * coeffW w k))
          + Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1))))
          + Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 2) * coeffW w k))).eqv
        ((Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 2) * coeffW w k))
          + Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 2) * coeffW w k)))
          + Q'.ofNat 7 * (qpow w 2 * (coeffW w (k + 1) * coeffW w (k + 1)))) := by
      ring_qeqv
    refine Q'.eqv_trans _ _ _ hrear ?_
    exact Q'.add_eqv_congr_right _ _ _ (ofNat_smul_add 7 7 _)
  -- eRsum : Rf k + Rf(k+1) + Rf(k+2) ≃ 16·ν
  have eR : (Rf k + Rf (k + 1) + Rf (k + 2)).eqv
      (Q'.ofNat 16 * (coeffW w (k + 2) * coeffW w k)) := by
    have c0 : (Rf k).eqv (Q'.ofNat 2 * (Q'.ofNat 4 * (coeffW w (k + 2) * coeffW w k))) := by
      show (Q'.ofNat 2 * (Q'.ofNat (dsq k (2 * (k + 1))) * μ k)).eqv _
      rw [dsq_lo k]
      exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hνk)
    have c1 : (Rf (k + 1)).eqv (0 : Q') := by
      show (Q'.ofNat 2 * (Q'.ofNat (dsq (k + 1) (2 * (k + 1))) * μ (k + 1))).eqv 0
      rw [dsq_ctr k]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
      exact Q'.mul_zero_eqv _
    have c2 : (Rf (k + 2)).eqv (Q'.ofNat 2 * (Q'.ofNat 4 * (coeffW w (k + 2) * coeffW w k))) := by
      show (Q'.ofNat 2 * (Q'.ofNat (dsq (k + 2) (2 * (k + 1))) * μ (k + 2))).eqv _
      rw [dsq_hi k]
      exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hνk2)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.add_eqv_congr' c0 c1) c2) ?_
    -- (2·(4ν) + 0) + 2·(4ν) ≃ 16ν
    have e8 : (Q'.ofNat 2 * (Q'.ofNat 4 * (coeffW w (k + 2) * coeffW w k))).eqv
        (Q'.ofNat 8 * (coeffW w (k + 2) * coeffW w k)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 4) (coeffW w (k + 2) * coeffW w k))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) e8) e8) ?_
    exact ofNat_smul_add 8 8 _
  -- hLR3 : Lf-sum ≤ Rf-sum
  have hLR3 : Lf k + Lf (k + 1) + Lf (k + 2) ≤ Rf k + Rf (k + 1) + Rf (k + 2) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) (Q'.le_trans' _ _ _ htb (Q'.ge_of_eqv eR))
  -- htri : 0 ≤ e-sum
  have htri : (0 : Q') ≤ (Rf k + -(Lf k)) + (Rf (k + 1) + -(Lf (k + 1)))
      + (Rf (k + 2) + -(Lf (k + 2))) := by
    have heq : ((Rf k + -(Lf k)) + (Rf (k + 1) + -(Lf (k + 1)))
        + (Rf (k + 2) + -(Lf (k + 2)))).eqv
        ((Rf k + Rf (k + 1) + Rf (k + 2)) + -(Lf k + Lf (k + 1) + Lf (k + 2))) := by
      ring_qeqv
    exact Q'.le_trans' _ _ _ (nonneg_of_le hLR3) (Q'.ge_of_eqv heq)
  -- (4) extraction + conclusion
  have hext := fsum_extract3 (fun p => Rf p + -(Lf p)) k hrest
  have h0sum : (0 : Q') ≤ fsum (fun p => Rf p + -(Lf p)) (2 * (k + 1) + 1) :=
    Q'.le_trans' _ _ _ htri hext
  -- fsum (R + -L) ≃ fsum R + -(fsum L)
  have hesum : (fsum (fun p => Rf p + -(Lf p)) (2 * (k + 1) + 1)).eqv
      (fsum Rf (2 * (k + 1) + 1) + -(fsum Lf (2 * (k + 1) + 1))) := by
    refine Q'.eqv_trans _ _ _ (fsum_add Rf (fun p => -(Lf p)) (2 * (k + 1) + 1)) ?_
    exact Q'.add_eqv_congr_left _ _ _ (fsum_neg Lf (2 * (k + 1) + 1))
  have h0' : (0 : Q') ≤ fsum Rf (2 * (k + 1) + 1) + -(fsum Lf (2 * (k + 1) + 1)) :=
    Q'.le_trans' _ _ _ h0sum (Q'.le_of_eqv hesum)
  have hfinal : fsum Lf (2 * (k + 1) + 1) ≤ fsum Rf (2 * (k + 1) + 1) := le_of_nonneg_sub h0'
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLsum) (Q'.le_trans' _ _ _ hfinal (Q'.ge_of_eqv hRsum))

/-! ## 10. The rational geometric tail for the odd excess. -/

/-- `(i+1)(i+2) ≤ 2·4^{i(i+1)}`. -/
theorem natPow : ∀ i, (i + 1) * (i + 2) ≤ 2 * 4 ^ (i * (i + 1))
  | 0 => by decide
  | i + 1 => by
      have ih := natPow i
      have h1 : (i + 2) * (i + 3) ≤ 16 * ((i + 1) * (i + 2)) := by
        have hle : (i + 2) * (i + 3) ≤ (i + 2) * (16 * (i + 1)) :=
          Nat.mul_le_mul_left (i + 2) (by omega)
        have he : (i + 2) * (16 * (i + 1)) = 16 * ((i + 1) * (i + 2)) := by
          simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        omega
      have h2 : 16 * ((i + 1) * (i + 2)) ≤ 16 * (2 * 4 ^ (i * (i + 1))) :=
        Nat.mul_le_mul_left 16 ih
      have hpow : 16 * (2 * 4 ^ (i * (i + 1))) = 2 * 4 ^ (i * (i + 1) + 2) := by
        have h42 : (4 : Nat) ^ 2 = 16 := by decide
        rw [Nat.pow_add, h42]; omega
      have hexp : i * (i + 1) + 2 ≤ (i + 1) * (i + 2) := by
        have hid : (i + 1) * (i + 2) = i * (i + 1) + 2 * i + 2 := by
          simp only [Nat.mul_add, Nat.add_mul]; omega
        omega
      have hmono : (4 : Nat) ^ (i * (i + 1) + 2) ≤ 4 ^ ((i + 1) * (i + 2)) :=
        Nat.pow_le_pow_right (by omega) hexp
      calc (i + 1 + 1) * (i + 1 + 2) = (i + 2) * (i + 3) := rfl
        _ ≤ 16 * ((i + 1) * (i + 2)) := h1
        _ ≤ 16 * (2 * 4 ^ (i * (i + 1))) := h2
        _ = 2 * 4 ^ (i * (i + 1) + 2) := hpow
        _ ≤ 2 * 4 ^ ((i + 1) * (i + 2)) := by omega

/-- `w^{2n} ≤ (1/4)^n` on `w² ≤ 1/4`. -/
theorem qpow_w2n_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw2q : qpow w 2 ≤ quarter) (n : Nat) :
    qpow w (2 * n) ≤ qpow quarter n := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (qpow_qpow w 2 n))) ?_
  exact HeatKernelGap.qpow_mono (qpow_nonneg w hw0 2) hw2q n

/-- `4(i+1)(i+2)·(1/4)^{i(i+1)} ≤ 8`. -/
theorem JqsBound (i : Nat) :
    Q'.ofNat (4 * (i + 1) * (i + 2)) * qpow quarter (i * (i + 1)) ≤ Q'.ofNat 8 := by
  have hnat : 4 * (i + 1) * (i + 2) ≤ 8 * 4 ^ (i * (i + 1)) := by
    have := natPow i
    have hassoc : 4 * (i + 1) * (i + 2) = 4 * ((i + 1) * (i + 2)) := by rw [Nat.mul_assoc]
    omega
  have hq : (0 : Q') ≤ qpow quarter (i * (i + 1)) :=
    qpow_nonneg quarter (by decide) _
  have h1 : Q'.ofNat (4 * (i + 1) * (i + 2)) * qpow quarter (i * (i + 1))
      ≤ Q'.ofNat (8 * 4 ^ (i * (i + 1))) * qpow quarter (i * (i + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (CReal.ofNat_le_ofNat hnat) hq
  refine Q'.le_trans' _ _ _ h1 ?_
  -- ofNat(8·4^n)·qpow quarter n ≃ 8·(ofNat(4^n)·qpow quarter n) ≃ 8·1 = 8
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (R1EvenCentreBound.ofNat_mul_eqv 8 (4 ^ (i * (i + 1))))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 8) (Q'.ofNat (4 ^ (i * (i + 1)))) _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (R1EvenCentreBound.qpow_quarter_inv (i * (i + 1)))) ?_
  exact Q'.mul_one_eqv (Q'.ofNat 8)

/-- `Jqs i := 4(i+1)(i+2)·(1/4)^{i(i+3)} ≤ 8·(1/4)^{2i}`. -/
theorem JqsGeo (i : Nat) :
    Q'.ofNat (4 * (i + 1) * (i + 2)) * qpow quarter (i * (i + 3))
      ≤ Q'.ofNat 8 * qpow quarter (2 * i) := by
  have hsplit : (qpow quarter (i * (i + 3))).eqv
      (qpow quarter (i * (i + 1)) * qpow quarter (2 * i)) := by
    rw [show i * (i + 3) = i * (i + 1) + 2 * i from by
      simp only [Nat.mul_add]; omega]
    exact qpow_add quarter (i * (i + 1)) (2 * i)
  have hq2 : (0 : Q') ≤ qpow quarter (2 * i) := qpow_nonneg quarter (by decide) _
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hsplit)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (4 * (i + 1) * (i + 2)))
      (qpow quarter (i * (i + 1))) (qpow quarter (2 * i))))) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ (JqsBound i) hq2

/-- The geometric invariant `Σ_{i<K} 8·(1/4)^{2i} + (16/15)·8·(1/4)^{2K} ≤ 9`. -/
def c1615 : Q' := Q'.mkPos 16 15 (by decide)

set_option maxRecDepth 2000 in
theorem qpow_q2_sixteenth : (qpow quarter 2).eqv sixteenth := by decide
set_option maxRecDepth 2000 in
theorem coef_1615 : ((1 : Q') + c1615 * sixteenth).eqv c1615 := by decide
set_option maxRecDepth 2000 in
theorem geo_base : (0 : Q') + c1615 * (Q'.ofNat 8 * qpow quarter (2 * 0)) ≤ Q'.ofNat 9 := by decide

theorem geoInvariant : ∀ K,
    fsum (fun i => Q'.ofNat 8 * qpow quarter (2 * i)) K
      + c1615 * (Q'.ofNat 8 * qpow quarter (2 * K)) ≤ Q'.ofNat 9
  | 0 => geo_base
  | K + 1 => by
      have ih := geoInvariant K
      show (fsum (fun i => Q'.ofNat 8 * qpow quarter (2 * i)) K
          + Q'.ofNat 8 * qpow quarter (2 * K))
          + c1615 * (Q'.ofNat 8 * qpow quarter (2 * (K + 1))) ≤ Q'.ofNat 9
      -- ratio: g(K+1) ≃ (1/16)·g K, so the K-term folds back into the invariant
      have hgeo : (Q'.ofNat 8 * qpow quarter (2 * (K + 1))).eqv
          (sixteenth * (Q'.ofNat 8 * qpow quarter (2 * K))) := by
        have hqs : (qpow quarter (2 * (K + 1))).eqv (qpow quarter (2 * K) * qpow quarter 2) := by
          rw [show 2 * (K + 1) = 2 * K + 2 from by omega]
          exact qpow_add quarter (2 * K) 2
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hqs) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ qpow_q2_sixteenth)) ?_
        -- ofNat 8 * (qpow(2K) * sixteenth) ≃ sixteenth * (ofNat 8 * qpow(2K))
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 8) (qpow quarter (2 * K)) sixteenth)) ?_
        exact Q'.mul_comm_eqv (Q'.ofNat 8 * qpow quarter (2 * K)) sixteenth
      -- rearrange to  Σ_{i<K} + (16/15)·g K
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) ih
      -- (Σ + g K) + (16/15)·((1/16)·g K) ≃ Σ + (16/15)·g K
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hgeo)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      -- g K + (16/15)·((1/16)·g K) ≃ (16/15)·g K
      have hcoef : (Q'.ofNat 8 * qpow quarter (2 * K)
          + c1615 * (sixteenth * (Q'.ofNat 8 * qpow quarter (2 * K)))).eqv
          ((1 + c1615 * sixteenth) * (Q'.ofNat 8 * qpow quarter (2 * K))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv c1615 sixteenth (Q'.ofNat 8 * qpow quarter (2 * K))))) ?_
        refine Q'.eqv_symm ?_
        refine Q'.eqv_trans _ _ _
          (R1CaseSplit.add_mul_local 1 (c1615 * sixteenth) (Q'.ofNat 8 * qpow quarter (2 * K))) ?_
        exact Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (Q'.ofNat 8 * qpow quarter (2 * K)))
      refine Q'.eqv_trans _ _ _ hcoef ?_
      exact Q'.mul_eqv_congr_right _ _ _ coef_1615

theorem geoTail (K : Nat) :
    fsum (fun i => Q'.ofNat 8 * qpow quarter (2 * i)) K ≤ Q'.ofNat 9 := by
  have hnn : (0 : Q') ≤ c1615 * (Q'.ofNat 8 * qpow quarter (2 * K)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (by decide) (qpow_nonneg quarter (by decide) _))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hnn) (geoInvariant K)

/-! ## 11. `dsq−1` on the odd lattice and the per-term geometric majorant. -/

/-- `dsq p (2c+1) − 1 = 4·(c−p)(c−p+1)` for `p ≤ c` (left half, `D = 2(c−p)+1 > 0`). -/
theorem dsq_odd_lo (c p : Nat) (hp : p ≤ c) :
    dsq p (2 * c + 1) - 1 = 4 * ((c - p) * (c - p + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hp
  have hcp : (p + d) - p = d := by omega
  show ((2 * (p + d) + 1 - 2 * p) * (2 * (p + d) + 1 - 2 * p)
      + (2 * p - (2 * (p + d) + 1)) * (2 * p - (2 * (p + d) + 1))) - 1 = 4 * (((p + d) - p) * ((p + d) - p + 1))
  rw [hcp, show 2 * (p + d) + 1 - 2 * p = 2 * d + 1 from by omega,
      show 2 * p - (2 * (p + d) + 1) = 0 from by omega]
  have hsq : (2 * d + 1) * (2 * d + 1) = 4 * (d * (d + 1)) + 1 := by
    simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega
  omega

/-- `dsq (c+1+i) (2c+1) − 1 = 4·i(i+1)` (right half, `D = −(2i+1)`). -/
theorem dsq_odd_hi (c i : Nat) :
    dsq (c + 1 + i) (2 * c + 1) - 1 = 4 * (i * (i + 1)) := by
  show ((2 * c + 1 - 2 * (c + 1 + i)) * (2 * c + 1 - 2 * (c + 1 + i))
      + (2 * (c + 1 + i) - (2 * c + 1)) * (2 * (c + 1 + i) - (2 * c + 1))) - 1 = 4 * (i * (i + 1))
  rw [show 2 * c + 1 - 2 * (c + 1 + i) = 0 from by omega,
      show 2 * (c + 1 + i) - (2 * c + 1) = 2 * i + 1 from by omega]
  have hsq : (2 * i + 1) * (2 * i + 1) = 4 * (i * (i + 1)) + 1 := by
    simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega
  omega

/-- **`termGeo`** — the per-term majorant of the excess `j`-sum, keeping one `w⁴`:
`4(i+1)(i+2)·w^{2(i+1)(i+2)} ≤ w⁴·(8·(1/4)^{2i})`. -/
theorem termGeo {w : Q'} (hw0 : (0 : Q') ≤ w) (hw2q : qpow w 2 ≤ quarter) (i : Nat) :
    Q'.ofNat (4 * (i + 1) * (i + 2)) * qpow w (2 * (i + 1) * (i + 2))
      ≤ qpow w 4 * (Q'.ofNat 8 * qpow quarter (2 * i)) := by
  have hofnn : (0 : Q') ≤ Q'.ofNat (4 * (i + 1) * (i + 2)) := ofNatNonneg _
  have hw4nn : (0 : Q') ≤ qpow w 4 := qpow_nonneg w hw0 4
  -- 2(i+1)(i+2) = 4 + 2·i(i+3)
  have hexp : 2 * (i + 1) * (i + 2) = 4 + 2 * (i * (i + 3)) := by
    rw [Nat.mul_assoc]
    have e1 : (i + 1) * (i + 2) = i * (i + 3) + 2 := by
      simp only [Nat.mul_add, Nat.add_mul]; omega
    omega
  have hqs : (qpow w (2 * (i + 1) * (i + 2))).eqv
      (qpow w 4 * qpow w (2 * (i * (i + 3)))) := by
    rw [hexp]; exact qpow_add w 4 (2 * (i * (i + 3)))
  -- w^{2·i(i+3)} ≤ (1/4)^{i(i+3)}
  have hw2n : qpow w (2 * (i * (i + 3))) ≤ qpow quarter (i * (i + 3)) :=
    qpow_w2n_le hw0 hw2q (i * (i + 3))
  -- assemble
  have h1 : Q'.ofNat (4 * (i + 1) * (i + 2)) * qpow w (2 * (i + 1) * (i + 2))
      ≤ Q'.ofNat (4 * (i + 1) * (i + 2)) * (qpow w 4 * qpow quarter (i * (i + 3))) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hqs)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hw2n hw4nn) hofnn
  refine Q'.le_trans' _ _ _ h1 ?_
  -- ofNat(4(i+1)(i+2))·(w⁴·(1/4)^{i(i+3)}) ≃ w⁴·(ofNat(4(i+1)(i+2))·(1/4)^{i(i+3)}) ≤ w⁴·(8·(1/4)^{2i})
  have hrear : (Q'.ofNat (4 * (i + 1) * (i + 2)) * (qpow w 4 * qpow quarter (i * (i + 3)))).eqv
      (qpow w 4 * (Q'.ofNat (4 * (i + 1) * (i + 2)) * qpow quarter (i * (i + 3)))) := by
    ring_qeqv
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrear) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (JqsGeo i) hw4nn

/-- Two-term extraction (for `2·μ_c ≤ acNfull`). -/
theorem fsum_extract2 (f : Nat → Q') (c : Nat)
    (hrest : ∀ p, p ≠ c → p ≠ c + 1 → (0 : Q') ≤ f p) :
    f c + f (c + 1) ≤ fsum f (c + (2 + c)) := by
  have hsplit1 := R1EvenCentreBound.fsum_split f c (2 + c)
  have hsplit2 := R1EvenCentreBound.fsum_split (fun i => f (c + i)) 2 c
  have hg2 : (fsum (fun i => f (c + i)) 2).eqv (f c + f (c + 1)) := by
    show ((0 + f (c + 0)) + f (c + 1)).eqv (f c + f (c + 1))
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) (Q'.eqv_of_eq (congrArg f (by omega))))
  have hP : (0 : Q') ≤ fsum f c := fsum_nonneg_lt c (fun i hi => hrest i (by omega) (by omega))
  have hS : (0 : Q') ≤ fsum (fun i => f (c + (2 + i))) c :=
    fsum_nonneg_lt c (fun i _ => hrest (c + (2 + i)) (by omega) (by omega))
  have htail : (f c + f (c + 1)) ≤ fsum (fun i => f (c + i)) (2 + c) := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hsplit2)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hg2) (Q'.add_le_self_of_nonneg _ _ hS)
  refine Q'.le_trans' _ _ _ htail ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hsplit1)
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (fsum (fun i => f (c + i)) (2 + c))))) ?_
  exact Q'.add_le_add_right 0 (fsum f c) (fsum (fun i => f (c + i)) (2 + c)) hP

/-! ## 12. `oddVarUpper` — `V(odd) ≤ 1 + 9·w⁴`. -/

/-- **`oddVarUpper`** — for odd `N ≥ 1` and `0 ≤ w ≤ 1/2`, `V(odd) ≤ 1 + 9·w⁴`, cleared as
`dmomNfull w N ≤ acNfull w N + 9·w⁴·acNfull w N`. -/
theorem oddVarUpper {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ R1CaseSplit.half)
    (N : Nat) (hN : N % 2 = 1) :
    dmomNfull w N ≤ acNfull w N + Q'.ofNat 9 * (qpow w 4 * acNfull w N) := by
  obtain ⟨c, rfl⟩ : ∃ c, N = 2 * c + 1 := ⟨N / 2, by omega⟩
  have hw2q := w2_le_quarter hw0 hwh
  have hw4nn : (0 : Q') ≤ qpow w 4 := qpow_nonneg w hw0 4
  have hodd : (2 * c + 1) % 2 = 1 := by omega
  -- abbreviations
  let μ : Nat → Q' := fun p => coeffW w p * coeffW w (2 * c + 1 - p)
  let μc : Q' := coeffW w c * coeffW w (c + 1)
  have hμcnn : (0 : Q') ≤ μc := Q'.mul_nonneg _ _ (coeffW_nonneg hw0 c) (coeffW_nonneg hw0 (c + 1))
  have hμnn : ∀ p, (0 : Q') ≤ μ p := fun p =>
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 p) (coeffW_nonneg hw0 _)
  let Gt : Nat → Q' := fun j => Q'.ofNat (4 * j * (j + 1)) * (qpow w (2 * j * (j + 1)) * μc)
  let exc : Nat → Q' := fun p => Q'.ofNat (dsq p (2 * c + 1) - 1) * μ p
  -- (A) dmom ≃ ac + excess
  have hA : (dmomNfull w (2 * c + 1)).eqv (acNfull w (2 * c + 1) + fsum exc (2 * c + 2)) := by
    show (fsum (fun p => Q'.ofNat (dsq p (2 * c + 1)) * μ p) (2 * c + 2)).eqv
      (fsum μ (2 * c + 2) + fsum exc (2 * c + 2))
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ (fun p => μ p + exc p) (fun p => ?_) (2 * c + 2)) ?_
    · -- ofNat(dsq)·μ ≃ μ + ofNat(dsq-1)·μ
      have hd1 : 1 ≤ dsq p (2 * c + 1) := EnvelopeClosure.one_le_dsq_of_odd hodd p
      have hde : dsq p (2 * c + 1) = 1 + (dsq p (2 * c + 1) - 1) := by omega
      have hofn : (Q'.ofNat (dsq p (2 * c + 1))).eqv (1 + Q'.ofNat (dsq p (2 * c + 1) - 1)) := by
        refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg Q'.ofNat hde)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv 1 (dsq p (2 * c + 1) - 1)) ?_
        exact Q'.add_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 1).eqv 1)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hofn) ?_
      refine Q'.eqv_trans _ _ _ (R1CaseSplit.add_mul_local 1 (Q'.ofNat (dsq p (2 * c + 1) - 1)) (μ p)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (μ p))
    · exact fsum_add μ exc (2 * c + 2)
  -- (B0) 2·μc ≤ acNfull
  have hac2 : Q'.ofNat 2 * μc ≤ acNfull w (2 * c + 1) := by
    have hext := fsum_extract2 μ c (fun p _ _ => hμnn p)
    have hidx : c + (2 + c) = 2 * c + 2 := by omega
    rw [hidx] at hext
    have hμc : (μ c).eqv μc := by
      show (coeffW w c * coeffW w (2 * c + 1 - c)).eqv (coeffW w c * coeffW w (c + 1))
      rw [show 2 * c + 1 - c = c + 1 from by omega]; exact Q'.eqv_refl _
    have hμc1 : (μ (c + 1)).eqv μc := by
      show (coeffW w (c + 1) * coeffW w (2 * c + 1 - (c + 1))).eqv (coeffW w c * coeffW w (c + 1))
      rw [show 2 * c + 1 - (c + 1) = c from by omega]; exact Q'.mul_comm_eqv _ _
    have hsum2 : (μ c + μ (c + 1)).eqv (Q'.ofNat 2 * μc) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hμc hμc1) ?_
      exact Q'.eqv_symm (R1CaseSplit.two_smul μc)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsum2) hext
  -- (B1) excess ≤ 2·(fsum Gt (c+1))
  -- left/right term bounds
  have hexcL : ∀ p, p ≤ c → exc p ≤ Gt (c - p) := by
    intro p hpc
    have hoc := oddCenterBound hw0 c (c - p) (by omega)
    -- rewrite c-(c-p)=p and c+1+(c-p)=2c+1-p
    rw [show c - (c - p) = p from by omega, show c + 1 + (c - p) = 2 * c + 1 - p from by omega] at hoc
    -- exc p = ofNat(dsq-1)·μp, dsq-1 = 4·((c-p)(c-p+1))
    have hdeq : dsq p (2 * c + 1) - 1 = 4 * ((c - p) * (c - p + 1)) := dsq_odd_lo c p hpc
    have hexcp : (exc p).eqv (Q'.ofNat (4 * (c - p) * ((c - p) + 1)) * μ p) := by
      show (Q'.ofNat (dsq p (2 * c + 1) - 1) * μ p).eqv _
      rw [hdeq, Nat.mul_assoc 4 (c - p) ((c - p) + 1)]; exact Q'.eqv_refl _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexcp) ?_
    -- ofNat(4(c-p)(c-p+1))·μp ≤ ofNat(4(c-p)(c-p+1))·(qpow·μc) = Gt(c-p)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hoc (ofNatNonneg _)
  have hexcR : ∀ i, i ≤ c → exc (c + 1 + i) ≤ Gt i := by
    intro i hic
    have hoc := oddCenterBound hw0 c i hic
    have hdeq : dsq (c + 1 + i) (2 * c + 1) - 1 = 4 * (i * (i + 1)) := dsq_odd_hi c i
    have hμeq : (μ (c + 1 + i)).eqv (coeffW w (c - i) * coeffW w (c + 1 + i)) := by
      show (coeffW w (c + 1 + i) * coeffW w (2 * c + 1 - (c + 1 + i))).eqv _
      rw [show 2 * c + 1 - (c + 1 + i) = c - i from by omega]
      exact Q'.mul_comm_eqv _ _
    have hexcp : (exc (c + 1 + i)).eqv (Q'.ofNat (4 * i * (i + 1)) * (coeffW w (c - i) * coeffW w (c + 1 + i))) := by
      show (Q'.ofNat (dsq (c + 1 + i) (2 * c + 1) - 1) * μ (c + 1 + i)).eqv _
      rw [hdeq, Nat.mul_assoc 4 i (i + 1)]
      exact Q'.mul_eqv_congr_left _ _ _ hμeq
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexcp) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hoc (ofNatNonneg _)
  have hB1 : fsum exc (2 * c + 2) ≤ fsum Gt (c + 1) + fsum Gt (c + 1) := by
    have hsplit := R1EvenCentreBound.fsum_split exc (c + 1) (c + 1)
    rw [show 2 * c + 2 = (c + 1) + (c + 1) from by omega]
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    refine Q'.add_le_add ?_ ?_
    · -- left ≤ fsum Gt (c+1)  via revSum
      refine Q'.le_trans' _ _ _
        (fsum_mono_lt (c + 1) (fun p hp => hexcL p (by omega))) ?_
      exact Q'.le_of_eqv (R1EvenCentreBound.revSum Gt c)
    · exact fsum_mono_lt (c + 1) (fun i hi => hexcR i (by omega))
  -- (B2) fsum Gt (c+1) ≤ 9·(w⁴·μc)
  have hB2 : fsum Gt (c + 1) ≤ Q'.ofNat 9 * (qpow w 4 * μc) := by
    -- fsum Gt (c+1) ≃ (fsum term (c+1))·μc
    have hGtfac : (fsum Gt (c + 1)).eqv
        ((fsum (fun j => Q'.ofNat (4 * j * (j + 1)) * qpow w (2 * j * (j + 1))) (c + 1)) * μc) := by
      refine Q'.eqv_trans _ _ _
        (fsum_eqv_congr Gt (fun j => (Q'.ofNat (4 * j * (j + 1)) * qpow w (2 * j * (j + 1))) * μc)
          (fun j => Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (c + 1)) ?_
      exact Q'.eqv_symm (fsum_mul_const _ μc (c + 1))
    -- Jrat ≃ fsum (term ∘ succ) c  (term 0 = 0)
    have hterm0 : (Q'.ofNat (4 * 0 * (0 + 1)) * qpow w (2 * 0 * (0 + 1))).eqv 0 := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat (4 * 0 * (0 + 1))).eqv 0)) ?_
      exact Q'.zero_mul_eqv _
    have hshift := R1EvenCentreBound.fsum_shift_cons
      (fun j => Q'.ofNat (4 * j * (j + 1)) * qpow w (2 * j * (j + 1))) c
    -- fsum (term∘succ) c ≤ w⁴·9
    have hJrat : (fsum (fun j => Q'.ofNat (4 * j * (j + 1)) * qpow w (2 * j * (j + 1))) (c + 1))
        ≤ qpow w 4 * Q'.ofNat 9 := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hshift) ?_
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _ hterm0)) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
      -- fsum (fun i => term (i+1)) c ≤ fsum (fun i => w⁴·(8·(1/4)^{2i})) c ≃ w⁴·(fsum …) ≤ w⁴·9
      refine Q'.le_trans' _ _ _
        (fsum_mono_lt c (fun i _ => termGeo hw0 hw2q i)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (fsum_const_mul (qpow w 4)
          (fun i => Q'.ofNat 8 * qpow quarter (2 * i)) c))) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ (geoTail c) hw4nn
    -- assemble  fsum Gt = Jrat·μc ≤ (w⁴·9)·μc ≃ 9·(w⁴·μc)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hGtfac) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hJrat hμcnn) ?_
    refine Q'.le_of_eqv ?_
    -- (w⁴·9)·μc ≃ 9·(w⁴·μc)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (qpow w 4) (Q'.ofNat 9))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofNat 9) (qpow w 4) μc
  -- (B) excess ≤ 9·(w⁴·ac)
  have hB : fsum exc (2 * c + 2) ≤ Q'.ofNat 9 * (qpow w 4 * acNfull w (2 * c + 1)) := by
    -- excess ≤ 2·(9·(w⁴·μc)) ≃ 18·(w⁴·μc) ≤ 9·(w⁴·ac)
    refine Q'.le_trans' _ _ _ hB1 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hB2 hB2) ?_
    -- 9·(w⁴·μc) + 9·(w⁴·μc) ≤ 9·(w⁴·ac)
    have hstep : Q'.ofNat 9 * (qpow w 4 * (Q'.ofNat 2 * μc))
        ≤ Q'.ofNat 9 * (qpow w 4 * acNfull w (2 * c + 1)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hac2 hw4nn) (by decide)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hstep
    -- 9·(w⁴·μc)+9·(w⁴·μc) ≃ 9·(w⁴·(2·μc))
    have e2 : (qpow w 4 * μc + qpow w 4 * μc).eqv (qpow w 4 * (Q'.ofNat 2 * μc)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv (qpow w 4) μc μc)) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (R1CaseSplit.two_smul μc))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat 9) _ _)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ e2
  -- conclude:  dmom ≃ ac + excess ≤ ac + 9·(w⁴·ac)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hA) ?_
  exact Q'.add_le_add_left _ _ _ hB

/-! ## 13. The cleared cell algebra and the closed odd-centre cell. -/

/-- **`oddCellArith`** — the cleared, subtraction-free odd-centre floor.  From the two even-neighbour
lower bounds (`7·w²·a ≤ 2·d`), the odd-centre upper bound (`d₁ ≤ a₁ + 9·w⁴·a₁`), and `36·w⁴ ≤ 14·w²`,
the cleared `FullRangeFloor` inequality holds (margin `2·(7−18w²)·w² ≥ 0`).  PROVED — no `sorry`. -/
theorem oddCellArith {a0 a1 a2 d0 d1 d2 w2 w4 : Q'}
    (h0 : (0 : Q') ≤ a0) (h1 : (0 : Q') ≤ a1) (h2 : (0 : Q') ≤ a2)
    (hE0 : Q'.ofNat 7 * (w2 * a0) ≤ Q'.ofNat 2 * d0)
    (hE2 : Q'.ofNat 7 * (w2 * a2) ≤ Q'.ofNat 2 * d2)
    (hU1 : d1 ≤ a1 + Q'.ofNat 9 * (w4 * a1))
    (harith : Q'.ofNat 36 * w4 ≤ Q'.ofNat 14 * w2) :
    Q'.ofNat 2 * (d1 * (a0 * a2))
      ≤ d0 * (a1 * a2) + d2 * (a0 * a1) + Q'.ofNat 2 * (a0 * (a1 * a2)) := by
  refine Q'.le_of_mul_le_mul_left (c := Q'.ofNat 2) ?_ (by decide)
  have hP : (0 : Q') ≤ a0 * (a1 * a2) := Q'.mul_nonneg _ _ h0 (Q'.mul_nonneg _ _ h1 h2)
  have ha0a2 : (0 : Q') ≤ a0 * a2 := Q'.mul_nonneg _ _ h0 h2
  have ha1a2 : (0 : Q') ≤ a1 * a2 := Q'.mul_nonneg _ _ h1 h2
  have ha0a1 : (0 : Q') ≤ a0 * a1 := Q'.mul_nonneg _ _ h0 h1
  -- hUp : ofNat 2 * LHS ≤ ofNat 4 * P + ofNat 36 * (w4·P)
  have hd1B : d1 * (a0 * a2) ≤ (a1 + Q'.ofNat 9 * (w4 * a1)) * (a0 * a2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hU1 ha0a2
  have hBval : ((a1 + Q'.ofNat 9 * (w4 * a1)) * (a0 * a2)).eqv
      (a0 * (a1 * a2) + Q'.ofNat 9 * (w4 * (a0 * (a1 * a2)))) := by
    refine Q'.eqv_trans _ _ _ (R1CaseSplit.add_mul_local a1 (Q'.ofNat 9 * (w4 * a1)) (a0 * a2)) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · ring_qeqv
    · ring_qeqv
  have hUp : Q'.ofNat 2 * (Q'.ofNat 2 * (d1 * (a0 * a2)))
      ≤ Q'.ofNat 4 * (a0 * (a1 * a2)) + Q'.ofNat 36 * (w4 * (a0 * (a1 * a2))) := by
    have hmono : Q'.ofNat 2 * (Q'.ofNat 2 * (d1 * (a0 * a2)))
        ≤ Q'.ofNat 2 * (Q'.ofNat 2 * ((a1 + Q'.ofNat 9 * (w4 * a1)) * (a0 * a2))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hd1B (by decide)) (by decide)
    refine Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv ?_)
    -- ofNat2*(ofNat2*B) ≃ ofNat4*P + ofNat36*(w4·P)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hBval)) ?_
    -- ofNat2*(ofNat2*(P + 9(w4·P))) ≃ ofNat4*P + ofNat36*(w4·P)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 2) _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 2 * Q'.ofNat 2).eqv (Q'.ofNat 4))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat 4) (a0 * (a1 * a2)) (Q'.ofNat 9 * (w4 * (a0 * (a1 * a2))))) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    -- ofNat4*(9*(w4·P)) ≃ ofNat36*(w4·P)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat 9) (w4 * (a0 * (a1 * a2))))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 4 * Q'.ofNat 9).eqv (Q'.ofNat 36))
  -- hMid : ofNat 4*P + ofNat 36*(w4·P) ≤ ofNat 14*(w2·P) + ofNat 4*P
  have h36 : Q'.ofNat 36 * (w4 * (a0 * (a1 * a2))) ≤ Q'.ofNat 14 * (w2 * (a0 * (a1 * a2))) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 36) w4 (a0 * (a1 * a2))))) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ harith hP) ?_
    exact Q'.le_of_eqv (Q'.mul_assoc_eqv (Q'.ofNat 14) w2 (a0 * (a1 * a2)))
  have hMid : Q'.ofNat 4 * (a0 * (a1 * a2)) + Q'.ofNat 36 * (w4 * (a0 * (a1 * a2)))
      ≤ Q'.ofNat 14 * (w2 * (a0 * (a1 * a2))) + Q'.ofNat 4 * (a0 * (a1 * a2)) := by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ h36) ?_
    exact Q'.le_of_eqv (Q'.add_comm_eqv _ _)
  -- hDown : ofNat 14*(w2·P) + ofNat 4*P ≤ ofNat 2 * RHS
  have hT0 : Q'.ofNat 7 * (w2 * (a0 * (a1 * a2))) ≤ Q'.ofNat 2 * (d0 * (a1 * a2)) := by
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hE0 ha1a2
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv ?_))
    · ring_qeqv
    · ring_qeqv
  have hT2 : Q'.ofNat 7 * (w2 * (a0 * (a1 * a2))) ≤ Q'.ofNat 2 * (d2 * (a0 * a1)) := by
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hE2 ha0a1
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv ?_))
    · ring_qeqv
    · ring_qeqv
  have hDown : Q'.ofNat 14 * (w2 * (a0 * (a1 * a2))) + Q'.ofNat 4 * (a0 * (a1 * a2))
      ≤ Q'.ofNat 2 * (d0 * (a1 * a2) + d2 * (a0 * a1) + Q'.ofNat 2 * (a0 * (a1 * a2))) := by
    -- ofNat 2 * RHS ≃ 2·(d0(a1a2)) + 2·(d2(a0a1)) + 4·P
    have hRHSexp : (Q'.ofNat 2 * (d0 * (a1 * a2) + d2 * (a0 * a1) + Q'.ofNat 2 * (a0 * (a1 * a2)))).eqv
        ((Q'.ofNat 2 * (d0 * (a1 * a2)) + Q'.ofNat 2 * (d2 * (a0 * a1)))
          + Q'.ofNat 4 * (a0 * (a1 * a2))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (Q'.ofNat 2) (d0 * (a1 * a2) + d2 * (a0 * a1)) (Q'.ofNat 2 * (a0 * (a1 * a2)))) ?_
      refine Q'.add_eqv_congr' (Q'.mul_add_eqv (Q'.ofNat 2) (d0 * (a1 * a2)) (d2 * (a0 * a1))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 2) (a0 * (a1 * a2)))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 2 * Q'.ofNat 2).eqv (Q'.ofNat 4))
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHSexp)
    refine Q'.add_le_add ?_ (Q'.le_refl' _)
    -- 14·(w2·P) ≃ 7·(w2·P) + 7·(w2·P) ≤ 2·(d0(a1a2)) + 2·(d2(a0a1))
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (ofNat_smul_add 7 7 (w2 * (a0 * (a1 * a2))))) ?_
    exact Q'.add_le_add hT0 hT2
  -- chain
  exact Q'.le_trans' _ _ _ hUp (Q'.le_trans' _ _ _ hMid hDown)

/-- **`oddCentreCell`** — the BINDING odd-centre cell of R1, CLOSED for every `0 ≤ w` on the lower
half `w ≤ 1/2`.  `s = 0` is the corner base case (`fullRangeFloor_zero`); for even `s = 2m ≥ 2`,
`oddCellArith` combines `evenVarLower` (neighbours `2m`, `2m+2`), `oddVarUpper` (centre `2m+1`), and
`w4_arith`.  This inhabits `R1CaseSplit.OddCentreCellLE w` — SUPERSEDING `R1OddL2Chain`. -/
def oddCentreCell {w : Q'} (hw0 : (0 : Q') ≤ w) : R1CaseSplit.OddCentreCellLE w where
  cell := fun hle s hs => by
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · subst hs0; exact fullRangeFloor_zero hw0
    · obtain ⟨m, rfl⟩ : ∃ m, s = 2 * m := ⟨s / 2, by omega⟩
      have hm : 1 ≤ m := by omega
      have hE0 := evenVarLower hw0 hle m hm
      have hE2 := evenVarLower hw0 hle (m + 1) (by omega)
      rw [show 2 * (m + 1) = 2 * m + 2 from by omega] at hE2
      have hU1 := oddVarUpper hw0 hle (2 * m + 1) (by omega)
      have harith := w4_arith hw0 hle
      show Q'.ofNat 2 * (dmomNfull w (2 * m + 1) * (acNfull w (2 * m) * acNfull w (2 * m + 2)))
        ≤ dmomNfull w (2 * m) * (acNfull w (2 * m + 1) * acNfull w (2 * m + 2))
          + dmomNfull w (2 * m + 2) * (acNfull w (2 * m) * acNfull w (2 * m + 1))
          + Q'.ofNat 2 * (acNfull w (2 * m) * (acNfull w (2 * m + 1) * acNfull w (2 * m + 2)))
      exact oddCellArith
        (acN_nonneg hw0 (2 * m + 1) (2 * m))
        (acN_nonneg hw0 (2 * m + 2) (2 * m + 1))
        (acN_nonneg hw0 (2 * m + 3) (2 * m + 2))
        hE0 hE2 hU1 harith

end YMGap.Continuum.R1OddDirect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/
#print axioms YMGap.Continuum.R1OddDirect.coeffMul
#print axioms YMGap.Continuum.R1OddDirect.oddCenterBound
#print axioms YMGap.Continuum.R1OddDirect.evenNeighborLB
#print axioms YMGap.Continuum.R1OddDirect.w4_arith
#print axioms YMGap.Continuum.R1OddDirect.fsum_extract3
#print axioms YMGap.Continuum.R1OddDirect.tripleBound
#print axioms YMGap.Continuum.R1OddDirect.evenVarLower
#print axioms YMGap.Continuum.R1OddDirect.geoTail
#print axioms YMGap.Continuum.R1OddDirect.oddVarUpper
#print axioms YMGap.Continuum.R1OddDirect.oddCellArith
#print axioms YMGap.Continuum.R1OddDirect.oddCentreCell
