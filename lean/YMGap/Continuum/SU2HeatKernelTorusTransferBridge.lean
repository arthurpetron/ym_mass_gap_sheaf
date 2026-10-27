/-
# Two-Cut Torus Reflection, Semigroup Handle Dominance, and Reduction of `HeatKernelTorusSemigroupBridge`

**Labels: U(1)-true, fixed-coupling heat-kernel action (`BondMovingStep.coeffW`). Conditional on the
minimal two-cut torus slice-disintegration identity (`TorusSliceTraceIdentity` /
`TorusSliceExactTwoHandlePin`). NOT evidence for a non-abelian mass gap.**

Reference: `YMGap/Continuum/SU2HeatKernelTorusClusteringBridge.lean`,
`audits/SCOPE-R1-CLUSTER-TO-GAP-2026-10-07.md`,
`audits/AUDIT-TORUS-FINITE-RATIO-AND-OS-PRODUCER-2026-10-07.md`, and `/workspace/papers/2610.29019.txt`
(Appendix F.5, two-cut torus reflection on `ℤ/(2Mℤ)`).

On the periodic time circle `ℤ/(2Mℤ)` of length `2M`, two spatial plaquette insertions separated by
even time lag `2m` with `2m + 1 ≤ M` split the circle across the two reflection cuts into:
1. a **forward handle** of length `2m`, paired on the BF4 completed carrier as
   `B(y, T^{2m} y) = B(T^m y, T^m y)`, and
2. a **backward (wrap-around) handle** of length `backwardLag M m := 2M - 2m ≥ 2m + 2`, paired as
   `B(y, T^{2M - 2m} y) = B(T^{M - m} y, T^{M - m} y) = B(T^{M - 2m}(T^m y), T^{M - 2m}(T^m y))`.

This module factors `HeatKernelTorusSemigroupBridge` (`hcov`) into:
* **(i) Proved algebraic handle dominance on the BF4 completed semigroup:**
  - `backward_handle_le_forward_handle`: for `2m ≤ M` (and hence `2m + 1 ≤ M`), `completedTime`
    contraction (`completedInner_time_contraction`) unconditionally yields
    `B(y, T^{2M - 2m} y) ≤ B(y, T^{2m} y)` for every `y ∈ Completion hw0 hw1 width`.
  - `backward_handle_strict_decay`: on `VacuumComplement`, `WilsonVacuumSqContraction r` strengthens
    this to `B(y, T^{2M - 2m} y) ≤ (r²)^{M - 2m} B(y, T^{2m} y) ≤ (r²)^{M - m} B(y, y)`.
  - `two_handle_pairing_le_forward`: for `0 ≤ cbwd` and `2m ≤ M`, the two-handle torus combination
    `cfwd · B(y, T^{2m} y) + cbwd · B(y, T^{2M - 2m} y)` is bounded by `(cfwd + cbwd) · B(y, T^{2m} y)`.
* **(ii) Minimal explicit slice-disintegration identity (`TorusSliceTraceIdentity`):**
  Bounding (or equating via `TorusSliceExactTwoHandlePin`) the 4D Haar normalized covariance
  `Rq (EhatHK S_trunc b c d plane m)` on `torusLinks (2M)` by the forward + backward handle pairing
  on a vacuum-orthogonal state `y` implies `HeatKernelTorusSemigroupBridge` (`hcov`) with constant
  `C = cfwd + cbwd`, and hence `(1/16)^m` decay at `existingPilotNome = 1/1024`.

-/

import YMGap.Continuum.SU2HeatKernelTorusClusteringBridge

namespace YMGap.Continuum.SU2HeatKernelTorusTransferBridge

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_add VacuumComplement
   completedTime_preserves_vacuumComplement completedInner_time_sum
   completedInner_time_contraction)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.Continuum.BF4WilsonStrongCouplingUniformRate (existingPilotNome)
open YMGap.Continuum.BF4StrongCouplingClusteringBridge (vacuumSq_iterate)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plane dirsOf)
open YMGap.Continuum.PolymerLatticeDecay (lam)
open YMGap.Continuum.SU2TruncDecay (Ctr)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2HeatKernelTorusClusteringBridge
  (ZHK EhatHK HeatKernelTorusSemigroupBridge ehatHK_semigroup_decay_of_bridge
   pilot_ehatHK_semigroup_decay_of_bridge pilot_ehatHK_two_rate_envelope)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-! ## 1. Periodic `2M`-torus handle arithmetic (`2m ≤ M` and `2m + 1 ≤ M`) -/

/-- Backward (wrap-around) handle length `2M - 2m` on the periodic circle `ℤ/(2Mℤ)`. -/
def backwardLag (M m : Nat) : Nat := 2 * M - 2 * m

/-- Half of the backward handle length `M - m`, used for reflection symmetry across the two cuts. -/
def backwardHalfLag (M m : Nat) : Nat := M - m

/-- Half-lag excess `(M - m) - m = M - 2m` by which the backward half-handle exceeds `m`. -/
def halfLagExcess (M m : Nat) : Nat := M - 2 * m

theorem two_mul_le_of_window {m M : Nat} (hm : 2 * m + 1 ≤ M) : 2 * m ≤ M :=
  Nat.le_of_succ_le hm

theorem le_of_two_mul_le {m M : Nat} (hm : 2 * m ≤ M) : m ≤ M := by
  have hm1 : m ≤ 2 * m := by rw [Nat.two_mul]; exact Nat.le_add_left m m
  exact Nat.le_trans hm1 hm

/-- For `2m ≤ M`, the backward half-lag splits as `M - m = (M - 2m) + m`. -/
theorem backwardHalfLag_decomp {m M : Nat} (hm : 2 * m ≤ M) :
    backwardHalfLag M m = halfLagExcess M m + m := by
  show M - m = (M - 2 * m) + m
  have hM : ((M - 2 * m) + m) + m = M := by
    rw [Nat.add_assoc, ← Nat.two_mul, Nat.sub_add_cancel hm]
  exact Eq.trans (congrArg (· - m) hM.symm) (Nat.add_sub_cancel ((M - 2 * m) + m) m)

/-- For `2m ≤ M`, the backward handle length is even: `2M - 2m = 2(M - m)`. -/
theorem backwardLag_eq_two_mul {m M : Nat} (hm : 2 * m ≤ M) :
    backwardLag M m = 2 * backwardHalfLag M m := by
  show 2 * M - 2 * m = 2 * (M - m)
  have hmM : m ≤ M := le_of_two_mul_le hm
  have h2M : 2 * (M - m) + 2 * m = 2 * M := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hmM]
  exact Eq.trans (congrArg (· - 2 * m) h2M.symm) (Nat.add_sub_cancel (2 * (M - m)) (2 * m))

/-- In the torus window `2m + 1 ≤ M`, `1 ≤ M - 2m`. -/
theorem one_le_halfLagExcess {m M : Nat} (hm : 2 * m + 1 ≤ M) :
    1 ≤ halfLagExcess M m := by
  show 1 ≤ M - 2 * m
  have hM : (M - 2 * m) + 2 * m = M := Nat.sub_add_cancel (two_mul_le_of_window hm)
  have h1 : 1 + 2 * m ≤ (M - 2 * m) + 2 * m := by
    rw [hM, Nat.add_comm 1 (2 * m)]; exact hm
  exact Nat.le_of_add_le_add_right h1

/-- In the torus window `2m + 1 ≤ M`, the backward handle length exceeds the forward lag by at
least 2 steps (`2m + 2 ≤ 2M - 2m`). -/
theorem backwardLag_ge_forward_add_two {m M : Nat} (hm : 2 * m + 1 ≤ M) :
    2 * m + 2 ≤ backwardLag M m := by
  have hm0 : 2 * m ≤ M := two_mul_le_of_window hm
  rw [backwardLag_eq_two_mul hm0, backwardHalfLag_decomp hm0, Nat.mul_add,
      Nat.add_comm (2 * halfLagExcess M m) (2 * m)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (one_le_halfLagExcess hm)) (2 * m)

/-! ## 2. `RC` scalar addition helper -/

/-- Additivity of `RCscale` in the rational scalar: `s · a + t · a = (s + t) · a`. -/
theorem rc_add_scale (s t : Q') (a : RC) :
    RCadd (RCscale s a) (RCscale t a) = RCscale (s + t) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (.mul (.add (.var 0) (.var 1)) (.var 2)) (by decide)
        (fun | 0 => s | 1 => t | _ => A.approx n)))

/-! ## 3. Algebraic semigroup handle comparison on the BF4 completed carrier -/

section SemigroupHandles

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Forward handle reflection identity: `B(y, T^{2m} y) = B(T^m y, T^m y)`. -/
theorem forward_handle_eq_half_norm (m : Nat) (y : Completion hw0 hw1 width) :
    B y (T (2 * m) y) = B (T m y) (T m y) := by
  rw [Nat.two_mul, ← completedInner_time_sum (width := width) hw0 hw1 m m y y]

/-- Backward handle reflection identity: for `2m ≤ M`,
`B(y, T^{2M - 2m} y) = B(T^{M - m} y, T^{M - m} y)`. -/
theorem backward_handle_eq_half_norm {m M : Nat} (hm : 2 * m ≤ M)
    (y : Completion hw0 hw1 width) :
    B y (T (backwardLag M m) y) = B (T (backwardHalfLag M m) y) (T (backwardHalfLag M m) y) := by
  rw [backwardLag_eq_two_mul hm, Nat.two_mul,
      ← completedInner_time_sum (width := width) hw0 hw1 (backwardHalfLag M m) (backwardHalfLag M m) y y]

/-- For `2m ≤ M`, the backward handle is the `(M - 2m)`-step semigroup evolution of `T^m y`:
`B(y, T^{2M - 2m} y) = B(T^{M - 2m}(T^m y), T^{M - 2m}(T^m y))`. -/
theorem backward_handle_eq_shifted_forward {m M : Nat} (hm : 2 * m ≤ M)
    (y : Completion hw0 hw1 width) :
    B y (T (backwardLag M m) y) =
      B (T (halfLagExcess M m) (T m y)) (T (halfLagExcess M m) (T m y)) := by
  rw [backward_handle_eq_half_norm hw0 hw1 width hm y, backwardHalfLag_decomp hm,
      completedTime_add hw0 hw1 (halfLagExcess M m) m y]

/-- **Unconditional backward-handle dominance (`B(y, T^{2M - 2m} y) ≤ B(y, T^{2m} y)`):**
For `2m ≤ M`, the backward torus handle is unconditionally dominated by the forward handle on the
entire completed carrier `Completion hw0 hw1 width`, by `completedInner_time_contraction`. -/
theorem backward_handle_le_forward_handle {m M : Nat} (hm : 2 * m ≤ M)
    (y : Completion hw0 hw1 width) :
    RCle (B y (T (backwardLag M m) y)) (B y (T (2 * m) y)) := by
  rw [backward_handle_eq_shifted_forward hw0 hw1 width hm y,
      forward_handle_eq_half_norm hw0 hw1 width m y]
  exact completedInner_time_contraction (width := width) hw0 hw1 (halfLagExcess M m) (T m y)

/-- **Strict vacuum-complement backward-handle decay relative to the forward handle:**
Under `WilsonVacuumSqContraction hw0 hw1 width r` and `2m ≤ M`,
`B(y, T^{2M - 2m} y) ≤ (r²)^{M - 2m} B(y, T^{2m} y)`. -/
theorem backward_handle_strict_decay (r : Q') (hr : (0 : Q') ≤ r * r)
    (h : WilsonVacuumSqContraction hw0 hw1 width r) {m M : Nat} (hm : 2 * m ≤ M)
    (y : VacuumComplement hw0 hw1 (width := width)) :
    RCle (B y.val (T (backwardLag M m) y.val))
      (RCscale ((r * r) ^ halfLagExcess M m) (B y.val (T (2 * m) y.val))) := by
  rw [backward_handle_eq_shifted_forward hw0 hw1 width hm y.val,
      forward_handle_eq_half_norm hw0 hw1 width m y.val]
  let ym : VacuumComplement hw0 hw1 (width := width) :=
    ⟨T m y.val, completedTime_preserves_vacuumComplement hw0 hw1 m y.val y.property⟩
  exact vacuumSq_iterate hw0 hw1 width r hr h (halfLagExcess M m) ym

/-- **Total vacuum-complement backward-handle decay (`B(y, T^{2M - 2m} y) ≤ (r²)^{M - m} B(y, y)`).** -/
theorem backward_handle_total_decay (r : Q') (hr : (0 : Q') ≤ r * r)
    (h : WilsonVacuumSqContraction hw0 hw1 width r) {m M : Nat} (hm : 2 * m ≤ M)
    (y : VacuumComplement hw0 hw1 (width := width)) :
    RCle (B y.val (T (backwardLag M m) y.val))
      (RCscale ((r * r) ^ backwardHalfLag M m) (B y.val y.val)) := by
  rw [backward_handle_eq_half_norm hw0 hw1 width hm y.val]
  exact vacuumSq_iterate hw0 hw1 width r hr h (backwardHalfLag M m) y

/-- Weighted two-handle torus pairing `cfwd · B(y, T^{2m} y) + cbwd · B(y, T^{2M - 2m} y)`. -/
def twoHandlePairing (cfwd cbwd : Q') (M m : Nat) (y : Completion hw0 hw1 width) : RC :=
  RCadd (RCscale cfwd (B y (T (2 * m) y))) (RCscale cbwd (B y (T (backwardLag M m) y)))

/-- **Two-handle torus sandwich bound:** for `2m ≤ M` and `0 ≤ cbwd`,
`cfwd · B(y, T^{2m} y) + cbwd · B(y, T^{2M - 2m} y) ≤ (cfwd + cbwd) · B(y, T^{2m} y)`. -/
theorem two_handle_pairing_le_forward {cfwd cbwd : Q'} (hcbwd : (0 : Q') ≤ cbwd)
    {m M : Nat} (hm : 2 * m ≤ M) (y : Completion hw0 hw1 width) :
    RCle (twoHandlePairing hw0 hw1 width cfwd cbwd M m y)
      (RCscale (cfwd + cbwd) (B y (T (2 * m) y))) := by
  have hbwd : RCle (RCscale cbwd (B y (T (backwardLag M m) y)))
      (RCscale cbwd (B y (T (2 * m) y))) :=
    RCscale_mono hcbwd (backward_handle_le_forward_handle hw0 hw1 width hm y)
  have hsum := RCadd_le_add (RCle_refl (RCscale cfwd (B y (T (2 * m) y)))) hbwd
  rw [rc_add_scale cfwd cbwd (B y (T (2 * m) y))] at hsum
  exact hsum

/-- Equal-weight specialization (`cfwd = cbwd = C0 ≥ 0`): the sum of the forward and backward
handles is bounded by `(C0 + C0) · B(y, T^{2m} y)`. -/
theorem two_handle_sum_le_two_forward {C0 : Q'} (hC0 : (0 : Q') ≤ C0)
    {m M : Nat} (hm : 2 * m ≤ M) (y : Completion hw0 hw1 width) :
    RCle (twoHandlePairing hw0 hw1 width C0 C0 M m y)
      (RCscale (C0 + C0) (B y (T (2 * m) y))) :=
  two_handle_pairing_le_forward hw0 hw1 width hC0 hm y

/-! ## 4. Minimal two-cut torus slice-disintegration identity (`TorusSliceTraceIdentity`) -/

/-- **Minimal two-cut torus slice-disintegration hypothesis (`TorusSliceTraceIdentity`):**
In the torus window `2m + 1 ≤ M`, cutting `torusLinks (2M)` across the two time slices containing
the separated spatial plaquettes `P` (at `t = 0`) and `Q` (at `t = 2m`) bounds the normalized
4D Haar covariance `Rq (EhatHK S_trunc b c d plane m)` by the forward + backward semigroup handle
pairing `twoHandlePairing cfwd cbwd M m y.val` on a vacuum-orthogonal state `y`. -/
def TorusSliceTraceIdentity {M : Nat} (S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q') : Prop :=
  ∀ m : Nat, 2 * m + 1 ≤ M →
    RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
      (twoHandlePairing hw0 hw1 width cfwd cbwd M m y.val)

/-- **Exact two-handle pin (`TorusSliceExactTwoHandlePin`):** exact equality between the normalized
torus covariance `Rq (EhatHK S_trunc b c d plane m)` and the two-handle semigroup pairing. -/
def TorusSliceExactTwoHandlePin {M : Nat} (S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q') : Prop :=
  ∀ m : Nat, 2 * m + 1 ≤ M →
    Rq (EhatHK (M := M) S_trunc b c d plane m) =
      twoHandlePairing hw0 hw1 width cfwd cbwd M m y.val

theorem torusSliceTraceIdentity_of_exactPin {M : Nat} (S_trunc b c d : Nat)
    (plane : Z4Plane) (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q')
    (hpin : TorusSliceExactTwoHandlePin hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd) :
    TorusSliceTraceIdentity hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd := by
  intro m hm; rw [hpin m hm]; exact RCle_refl _

/-- **Main reduction (`TorusSliceTraceIdentity` implies `HeatKernelTorusSemigroupBridge` `hcov`):**
Combining the two-cut slice-disintegration bound with the proved algebraic handle dominance
`two_handle_pairing_le_forward` discharges `HeatKernelTorusSemigroupBridge` (`hcov`) with constant
`C = cfwd + cbwd`. -/
theorem torusSliceTraceIdentity_implies_hcov {M : Nat} (S_trunc b c d : Nat)
    (plane : Z4Plane) (y : VacuumComplement hw0 hw1 (width := width))
    {cfwd cbwd : Q'} (hcbwd : (0 : Q') ≤ cbwd)
    (htrace : TorusSliceTraceIdentity hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd) :
    HeatKernelTorusSemigroupBridge hw0 hw1 width (M := M) S_trunc b c d plane y (cfwd + cbwd) := by
  intro m hm
  exact RCle_trans (htrace m hm)
    (two_handle_pairing_le_forward hw0 hw1 width hcbwd (two_mul_le_of_window hm) y.val)

/-- Exact-pin corollary: `TorusSliceExactTwoHandlePin` implies `HeatKernelTorusSemigroupBridge`. -/
theorem torusSliceExactPin_implies_hcov {M : Nat} (S_trunc b c d : Nat)
    (plane : Z4Plane) (y : VacuumComplement hw0 hw1 (width := width))
    {cfwd cbwd : Q'} (hcbwd : (0 : Q') ≤ cbwd)
    (hpin : TorusSliceExactTwoHandlePin hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd) :
    HeatKernelTorusSemigroupBridge hw0 hw1 width (M := M) S_trunc b c d plane y (cfwd + cbwd) :=
  torusSliceTraceIdentity_implies_hcov hw0 hw1 width S_trunc b c d plane y hcbwd
    (torusSliceTraceIdentity_of_exactPin hw0 hw1 width S_trunc b c d plane y cfwd cbwd hpin)

/-- **Normalized heat-kernel torus decay from `TorusSliceTraceIdentity`:**
For `2m + 1 ≤ M`, `TorusSliceTraceIdentity` + `WilsonVacuumSqContraction r` implies
`Rq (EhatHK m) ≤ ((cfwd + cbwd) · (r²)^m) · B(y, y)`. -/
theorem ehatHK_decay_of_torusSliceTraceIdentity (r : Q') (hr : (0 : Q') ≤ r * r)
    (h : WilsonVacuumSqContraction hw0 hw1 width r)
    {M : Nat} (S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width))
    {cfwd cbwd : Q'} (hcfwd : (0 : Q') ≤ cfwd) (hcbwd : (0 : Q') ≤ cbwd)
    (htrace : TorusSliceTraceIdentity hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd)
    (m : Nat) (hm : 2 * m + 1 ≤ M) :
    RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
      (RCscale ((cfwd + cbwd) * (r * r) ^ m) (B y.val y.val)) :=
  ehatHK_semigroup_decay_of_bridge hw0 hw1 width r hr h S_trunc b c d plane y
    (cfwd + cbwd) (Q'.zero_le_add cfwd cbwd hcfwd hcbwd)
    (torusSliceTraceIdentity_implies_hcov hw0 hw1 width S_trunc b c d plane y hcbwd htrace) m hm

end SemigroupHandles

/-! ## 5. Concrete pilot (`w0 = existingPilotNome = 1/1024`, `timeRate ≈ 1/4`) closure -/

/-- Pilot strong-coupling `(timeRate²)^m` (`timeRate ≈ 1/4`, `(1/16)^m`) torus decay from
`TorusSliceTraceIdentity`. -/
theorem pilot_ehatHK_semigroup_decay_of_torusSliceTraceIdentity :
    let w := existingPilotNome
    ∃ (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')),
      ∀ (width M S_trunc b c d : Nat) (plane : Z4Plane)
        (y : VacuumComplement hw0 hw1 (width := width))
        (cfwd cbwd : Q'),
        (0 : Q') ≤ cfwd →
        (0 : Q') ≤ cbwd →
        TorusSliceTraceIdentity hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd →
        ∀ m : Nat, 2 * m + 1 ≤ M →
          RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
            (RCscale ((cfwd + cbwd) * (timeRate * timeRate) ^ m)
              (completedInner hw0 hw1 y.val y.val)) := by
  intro w
  obtain ⟨hw0, hw1, hdec⟩ := pilot_ehatHK_semigroup_decay_of_bridge
  refine ⟨hw0, hw1, ?_⟩
  intro width M S_trunc b c d plane y cfwd cbwd hcfwd hcbwd htrace m hm
  exact hdec width M S_trunc b c d plane y (cfwd + cbwd)
    (Q'.zero_le_add cfwd cbwd hcfwd hcbwd)
    (torusSliceTraceIdentity_implies_hcov hw0 hw1 width S_trunc b c d plane y hcbwd htrace) m hm

/-- **Combined two-rate envelope from `TorusSliceTraceIdentity` at `existingPilotNome = 1/1024`:**
Discharges `hcov` in `pilot_ehatHK_two_rate_envelope` via `TorusSliceTraceIdentity`, packaging
`0 < ZHK S_trunc`, the unconditional `(Ctr · λ) · (λ²)^m` polymer bound (`λ = 6/7`), and the
`((cfwd + cbwd) · (timeRate²)^m) · B(y, y)` semigroup bound (`timeRate ≈ 1/4`) for `2m + 1 ≤ M`. -/
theorem pilot_ehatHK_two_rate_of_torusSliceTraceIdentity :
    let w := existingPilotNome
    ∃ (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')),
      ∀ {M : Nat} (width S_trunc b c d : Nat) (plane : Z4Plane),
        1 ≤ M →
        isT (dirsOf plane).1 = false →
        ∀ (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q'),
          (0 : Q') ≤ cfwd →
          (0 : Q') ≤ cbwd →
          TorusSliceTraceIdentity hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd →
          (0 : Q') < ZHK (M := M) S_trunc ∧
          ∀ m : Nat, 2 * m + 1 ≤ M →
            RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
              (Rq ((Ctr * lam) * (lam * lam) ^ m)) ∧
            RCle (Rq (EhatHK (M := M) S_trunc b c d plane m))
              (RCscale ((cfwd + cbwd) * (timeRate * timeRate) ^ m)
                (completedInner hw0 hw1 y.val y.val)) := by
  intro w
  obtain ⟨hw0, hw1, htwo⟩ := pilot_ehatHK_two_rate_envelope
  refine ⟨hw0, hw1, ?_⟩
  intro M width S_trunc b c d plane hM hsp y cfwd cbwd hcfwd hcbwd htrace
  exact htwo width S_trunc b c d plane hM hsp y (cfwd + cbwd)
    (Q'.zero_le_add cfwd cbwd hcfwd hcbwd)
    (torusSliceTraceIdentity_implies_hcov hw0 hw1 width S_trunc b c d plane y hcbwd htrace)

end YMGap.Continuum.SU2HeatKernelTorusTransferBridge
