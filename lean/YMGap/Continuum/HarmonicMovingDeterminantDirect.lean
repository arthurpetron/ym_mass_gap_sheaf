/-
The full moving-cutoff determinant formulation of the harmonic shell/spacing
comparison.

The exact `3-4-5` shell is

  shell_k = mass_k - (9/25) (mass_k - mass_{k+1}).

After clearing the two positive Peter--Weyl normalizers, the desired
shell/spacing comparison is therefore equivalent to one inequality for the
*full* moving determinant.  In particular, the favorable diagonal part of
the newly added shell remains coupled to the fixed-cutoff weight drift; it is
not discarded by a separate upper bound.
-/

import YMGap.Continuum.HarmonicSchurRotationK3337

namespace YMGap.Continuum.HarmonicMovingDeterminantDirect

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK89
open YMGap.Continuum.HarmonicSchurRotationK101112
open YMGap.Continuum.HarmonicSchurRotationK1316
open YMGap.Continuum.HarmonicSchurRotationK1719
open YMGap.Continuum.HarmonicSchurRotationK2023
open YMGap.Continuum.HarmonicSchurRotationK2427
open YMGap.Continuum.HarmonicSchurRotationK2832
open YMGap.Continuum.HarmonicSchurRotationK3337
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-- The fraction of the consecutive mass drop subtracted by the rotated
shell entry. -/
def shellDropFraction : Q' := Q'.mkPos 9 25 (by decide)

/-- Exact convex form of the harmonic `3-4-5` shell. -/
theorem harmonicShell_convex_eqv (k : Nat) :
    harmonicShell k ≈
      Q'.mkPos 16 25 (by decide) * harmonicMass k +
        shellDropFraction * harmonicMass (k + 1) := by
  unfold harmonicShell FusedOffDiagonalCompression.rot11 shellDropFraction
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (by decide))
    (Q'.mul_eqv_congr_right _ _ _ (by decide))

/-- The rotated shell plus its exact `9/25` mass-drop payment recovers the
old mass after multiplication by the old spacing. -/
theorem shell_conservation_eqv (k : Nat) :
    (shellDropFraction *
        (harmonicMass k - harmonicMass (k + 1))) * harmonicSpacing k +
      harmonicShell k * harmonicSpacing k ≈
        harmonicMass k * harmonicSpacing k := by
  let r := shellDropFraction
  let c := Q'.mkPos 16 25 (by decide)
  let a := harmonicMass k
  let b := harmonicMass (k + 1)
  let s := harmonicSpacing k
  let X := (r * a) * s
  let Y := (r * b) * s
  let Z := (c * a) * s
  have hp : (r * (a - b)) * s ≈ X + -Y := by
    refine Q'.eqv_trans _ ((r * a + r * (-b)) * s) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ s (Q'.mul_add_eqv r a (-b))
    refine Q'.eqv_trans _ ((r * a + -(r * b)) * s) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ s
        (Q'.add_eqv_congr_left (r * a) _ _ (Q'.mul_neg_eqv r b))
    refine Q'.eqv_trans _ ((r * a) * s + (-(r * b)) * s) _
      (Q'.add_mul_eqv _ _ s) ?_
    exact Q'.add_eqv_congr_left X _ _ (Q'.neg_mul_eqv (r * b) s)
  have hs : harmonicShell k * s ≈ Z + Y := by
    refine Q'.eqv_trans _ ((c * a + r * b) * s) _
      (Q'.mul_eqv_congr_right _ _ s (harmonicShell_convex_eqv k)) ?_
    exact Q'.add_mul_eqv _ _ s
  change (r * (a - b)) * s + harmonicShell k * s ≈ a * s
  refine Q'.eqv_trans _ ((X + -Y) + (Z + Y)) _
    (Q'.add_eqv_congr' hp hs) ?_
  refine Q'.eqv_trans _ ((-Y + Y) + (X + Z)) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _ ((0 : Q') + (X + Z)) _
    (Q'.add_eqv_congr_right _ _ (X + Z) (Q'.neg_add_self_eqv Y)) ?_
  refine Q'.eqv_trans _ (X + Z) _ (QPoly.q_zero_add_eqv _) ?_
  refine Q'.eqv_trans _ ((r * a + c * a) * s) _
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ s)) ?_
  refine Q'.mul_eqv_congr_right _ _ s ?_
  refine Q'.eqv_trans _ ((r + c) * a) _
    (Q'.eqv_symm (Q'.add_mul_eqv r c a)) ?_
  refine Q'.eqv_trans _ ((1 : Q') * a) _
    (Q'.mul_eqv_congr_right _ _ a (by decide)) ?_
  exact Q'.one_mul_eqv a

/-- Clearing the old positive normalizer in the harmonic mass quotient. -/
theorem harmonicMass_mul_D_eqv (k : Nat) :
    harmonicMass k * harmonicD k ≈ harmonicD k - harmonicA k := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (harmonicD k) (harmonicMass_eq_DA k))
    (Q'.divPos_mul_eqv _ _ _)

/-- Clearing both positive normalizers in the exact consecutive mass-drop
identity. -/
theorem harmonicMass_drop_mul_Ds_eqv (k : Nat) :
    (harmonicMass k - harmonicMass (k + 1)) *
        (harmonicD k * harmonicD (k + 1)) ≈ harmonicMassCross k := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (harmonicD k * harmonicD (k + 1))
      (harmonicMass_drop_eq_cross k)) ?_
  exact Q'.divPos_mul_eqv _ _ _

/-- The spacing gain minus the exact rotated-shell mass-drop payment, after
clearing both Peter--Weyl normalizers.  This retains `harmonicMassCross` as a
single coupled determinant. -/
def movingDetSpacingResidual (k : Nat) : Q' :=
  ((harmonicD k - harmonicA k) *
      (harmonicSpacing k - harmonicSpacing (k + 1))) * harmonicD (k + 1) -
    (shellDropFraction * harmonicMassCross k) * harmonicSpacing k

private theorem rotated_shell_gap_algebra
    (r c a b s t shell : Q')
    (hshell : shell ≈ c * a + r * b)
    (hc : c ≈ (1 : Q') + -r) :
    shell * s - a * t ≈
      a * (s - t) - (r * (a - b)) * s := by
  have hscaled : shell * s ≈ (c * a + r * b) * s :=
    Q'.mul_eqv_congr_right _ _ s hshell
  refine Q'.eqv_trans _ (((c * a + r * b) * s) + -(a * t)) _
    (Q'.add_eqv_congr_right _ _ _ hscaled) ?_
  refine Q'.eqv_trans _ ((((1 : Q') + -r) * a + r * b) * s + -(a * t)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ s
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ a hc)))
  change ((((1 : Q') + -r) * a + r * b) * s + -(a * t)) ≈
    a * (s + -t) + -((r * (a + -b)) * s)
  ring_qeqv

/-- Before clearing normalizers, the shell/spacing surplus is the spacing
gain of the old mass minus exactly `9/25` of the mass drop. -/
theorem shell_spacing_gap_eqv (k : Nat) :
    harmonicShell k * harmonicSpacing k -
        harmonicMass k * harmonicSpacing (k + 1) ≈
      harmonicMass k *
          (harmonicSpacing k - harmonicSpacing (k + 1)) -
        (shellDropFraction *
          (harmonicMass k - harmonicMass (k + 1))) * harmonicSpacing k := by
  apply rotated_shell_gap_algebra
    shellDropFraction (Q'.mkPos 16 25 (by decide))
  · exact harmonicShell_convex_eqv k
  · unfold shellDropFraction
    decide

private theorem quotient_spacing_clear_algebra
    (r m drop s t D0 D1 A0 X : Q')
    (hmD : m * D0 ≈ D0 - A0)
    (hdrop : drop * (D0 * D1) ≈ X) :
    (m * (s - t) - (r * drop) * s) * (D0 * D1) ≈
      ((D0 - A0) * (s - t)) * D1 - (r * X) * s := by
  let ds := s - t
  have hfirst : (m * ds) * (D0 * D1) ≈ ((D0 - A0) * ds) * D1 := by
    refine Q'.eqv_trans _ (((m * D0) * ds) * D1) _ (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ D1
      (Q'.mul_eqv_congr_right _ _ ds hmD)
  have hpaid : ((r * drop) * s) * (D0 * D1) ≈ (r * X) * s := by
    refine Q'.eqv_trans _ ((r * s) * (drop * (D0 * D1))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ ((r * s) * X) _
      (Q'.mul_eqv_congr_left (r * s) _ _ hdrop) ?_
    ring_qeqv
  have hsecond : (-((r * drop) * s)) * (D0 * D1) ≈ -((r * X) * s) := by
    refine Q'.eqv_trans _ (-(((r * drop) * s) * (D0 * D1))) _
      (Q'.neg_mul_eqv ((r * drop) * s) (D0 * D1)) ?_
    exact Q'.neg_eqv_congr _ _ hpaid
  change (m * ds + -((r * drop) * s)) * (D0 * D1) ≈
    ((D0 - A0) * ds) * D1 + -((r * X) * s)
  refine Q'.eqv_trans _ ((m * ds) * (D0 * D1) +
      (-((r * drop) * s)) * (D0 * D1)) _
    (Q'.add_mul_eqv _ _ _) ?_
  exact Q'.add_eqv_congr' hfirst hsecond

/-- **Exact moving-determinant identity.**  Multiplying the shell/spacing
surplus by the two positive normalizers gives precisely the coupled
determinant residual.  No weight/cutoff split and no shell term is dropped. -/
theorem shell_spacing_gap_mul_Ds_eqv (k : Nat) :
    (harmonicShell k * harmonicSpacing k -
        harmonicMass k * harmonicSpacing (k + 1)) *
          (harmonicD k * harmonicD (k + 1)) ≈
      movingDetSpacingResidual k := by
  refine Q'.eqv_trans _
    ((harmonicMass k *
          (harmonicSpacing k - harmonicSpacing (k + 1)) -
        (shellDropFraction *
          (harmonicMass k - harmonicMass (k + 1))) * harmonicSpacing k) *
      (harmonicD k * harmonicD (k + 1))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (shell_spacing_gap_eqv k)
  unfold movingDetSpacingResidual
  exact quotient_spacing_clear_algebra
    shellDropFraction
    (harmonicMass k)
    (harmonicMass k - harmonicMass (k + 1))
    (harmonicSpacing k)
    (harmonicSpacing (k + 1))
    (harmonicD k)
    (harmonicD (k + 1))
    (harmonicA k)
    (harmonicMassCross k)
    (harmonicMass_mul_D_eqv k)
    (harmonicMass_drop_mul_Ds_eqv k)

/-- **Full moving-cutoff criterion.**  The desired harmonic shell/spacing
step is equivalent, in both directions, to a single division-free estimate
on the full determinant.  The right side is the exact spacing payment; the
left side contains the coupled shifted shell, including its favorable
diagonal contribution. -/
theorem harmonicMass_shell_spacing_iff_fullDeterminant (k : Nat) :
    (harmonicMass k * harmonicSpacing (k + 1) ≤
        harmonicShell k * harmonicSpacing k) ↔
      ((shellDropFraction * harmonicMassCross k) * harmonicSpacing k ≤
        ((harmonicD k - harmonicA k) *
          (harmonicSpacing k - harmonicSpacing (k + 1))) *
            harmonicD (k + 1)) := by
  let gap := harmonicShell k * harmonicSpacing k -
    harmonicMass k * harmonicSpacing (k + 1)
  let P := harmonicD k * harmonicD (k + 1)
  let R := movingDetSpacingResidual k
  have hP : (0 : Q') < P :=
    Q'.mul_pos (harmonicD_pos k) (harmonicD_pos (k + 1))
  have hid : gap * P ≈ R := by
    dsimp only [gap, P, R]
    exact shell_spacing_gap_mul_Ds_eqv k
  constructor
  · intro hstage
    have hgap0 : (0 : Q') ≤ gap := by
      dsimp only [gap]
      exact Q'.sub_nonneg_of_le hstage
    have hprod0 : (0 : Q') ≤ gap * P :=
      Q'.mul_nonneg _ _ hgap0 (Q'.le_of_lt hP)
    have hR0 : (0 : Q') ≤ R :=
      Q'.le_trans' _ _ _ hprod0 (Q'.le_of_eqv hid)
    dsimp only [R, movingDetSpacingResidual] at hR0
    exact Q'.le_of_sub_nonneg hR0
  · intro hdet
    have hR0 : (0 : Q') ≤ R := by
      dsimp only [R, movingDetSpacingResidual]
      exact Q'.sub_nonneg_of_le hdet
    have hprod0 : (0 : Q') ≤ gap * P :=
      Q'.le_trans' _ _ _ hR0 (Q'.ge_of_eqv hid)
    have hmul : (0 : Q') * P ≤ gap * P :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv P)) hprod0
    have hgap0 : (0 : Q') ≤ gap :=
      BakryEmery.le_of_mul_le_mul_right_pos hP hmul
    dsimp only [gap] at hgap0
    exact Q'.le_of_sub_nonneg hgap0

/-- Forward-use form of the coupled criterion. -/
theorem harmonicMass_shell_spacing_of_fullDeterminant (k : Nat)
    (hdet : (shellDropFraction * harmonicMassCross k) * harmonicSpacing k ≤
      ((harmonicD k - harmonicA k) *
        (harmonicSpacing k - harmonicSpacing (k + 1))) *
          harmonicD (k + 1)) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k :=
  (harmonicMass_shell_spacing_iff_fullDeterminant k).2 hdet

/-! ## Coupled diagonal-shell reserve

The next three quantities expose the cancellation that is lost by the
existing one-sided cutoff estimate.  `movingPositiveDemand` keeps the
fixed-cutoff weight covariance coupled to the positive adjacent shell, while
`movingDiagonalReserve` is the diagonal shell with its original favorable
sign. -/

def movingSpacingPayment (k : Nat) : Q' :=
  ((harmonicD k - harmonicA k) *
    (harmonicSpacing k - harmonicSpacing (k + 1))) * harmonicD (k + 1)

def movingPositiveDemand (k : Nat) : Q' :=
  (shellDropFraction *
    (harmonicWeightCross k +
      (harmonicA (k + 1) - harmonicMidA k) * harmonicD k)) *
        harmonicSpacing k

def movingDiagonalReserve (k : Nat) : Q' :=
  (shellDropFraction *
    (harmonicA k * (harmonicD (k + 1) - harmonicMidD k))) *
      harmonicSpacing k

/-- Exact expansion of the full moving determinant into weight covariance,
positive adjacent shell, and favorable diagonal shell. -/
theorem harmonicMassCross_eq_weight_adj_sub_diag (k : Nat) :
    harmonicMassCross k ≈
      (harmonicWeightCross k +
        (harmonicA (k + 1) - harmonicMidA k) * harmonicD k) -
      harmonicA k * (harmonicD (k + 1) - harmonicMidD k) := by
  refine Q'.eqv_trans _ _ _
    (harmonicMassCross_eq_weight_add_cutoff k) ?_
  unfold harmonicCutoffCross
  exact Q'.eqv_symm (Q'.add_assoc_eqv
    (harmonicWeightCross k)
    ((harmonicA (k + 1) - harmonicMidA k) * harmonicD k)
    (-(harmonicA k * (harmonicD (k + 1) - harmonicMidD k))))

private theorem residual_reserve_algebra
    (payment r x demandCore reserveCore s : Q')
    (hx : x ≈ demandCore - reserveCore) :
    payment - (r * x) * s ≈
      (payment + (r * reserveCore) * s) - (r * demandCore) * s := by
  refine Q'.eqv_trans _
    (payment + -((r * (demandCore - reserveCore)) * s)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left payment _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ s
          (Q'.mul_eqv_congr_left r _ _ hx)))
  change payment + -((r * (demandCore + -reserveCore)) * s) ≈
    (payment + (r * reserveCore) * s) + -((r * demandCore) * s)
  ring_qeqv

/-- The full residual is exactly spacing payment plus the nonnegative
diagonal-shell reserve minus the still-coupled weight/adjacent demand. -/
theorem movingDetSpacingResidual_eq_payment_add_reserve_sub_demand (k : Nat) :
    movingDetSpacingResidual k ≈
      (movingSpacingPayment k + movingDiagonalReserve k) -
        movingPositiveDemand k := by
  unfold movingDetSpacingResidual movingSpacingPayment
    movingDiagonalReserve movingPositiveDemand
  exact residual_reserve_algebra
    (((harmonicD k - harmonicA k) *
      (harmonicSpacing k - harmonicSpacing (k + 1))) * harmonicD (k + 1))
    shellDropFraction
    (harmonicMassCross k)
    (harmonicWeightCross k +
      (harmonicA (k + 1) - harmonicMidA k) * harmonicD k)
    (harmonicA k * (harmonicD (k + 1) - harmonicMidD k))
    (harmonicSpacing k)
    (harmonicMassCross_eq_weight_adj_sub_diag k)

/-- The retained diagonal-shell term really is a nonnegative reserve. -/
theorem movingDiagonalReserve_nonneg (k : Nat) :
    (0 : Q') ≤ movingDiagonalReserve k := by
  unfold movingDiagonalReserve
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (by decide)
      (Q'.mul_nonneg _ _
        (adjCorr_nonneg (harmW_nonneg k) (Ncut k))
        (Q'.sub_nonneg_of_le (harmonicMidD_le_next k))))
    (Q'.le_of_lt (harmonicSpacing_pos k))

/-- A single coupled comparison against spacing plus the diagonal-shell
reserve proves the full determinant inequality.  Unlike a separate bound on
`harmonicWeightCross`, this hypothesis can spend the negative shifted shell
against the hard covariance modes. -/
theorem fullDeterminant_of_positiveDemand_le_payment_add_reserve (k : Nat)
    (h : movingPositiveDemand k ≤
      movingSpacingPayment k + movingDiagonalReserve k) :
    (shellDropFraction * harmonicMassCross k) * harmonicSpacing k ≤
      ((harmonicD k - harmonicA k) *
        (harmonicSpacing k - harmonicSpacing (k + 1))) *
          harmonicD (k + 1) := by
  have hright0 : (0 : Q') ≤
      (movingSpacingPayment k + movingDiagonalReserve k) -
        movingPositiveDemand k := Q'.sub_nonneg_of_le h
  have hres0 : (0 : Q') ≤ movingDetSpacingResidual k :=
    Q'.le_trans' _ _ _ hright0
      (Q'.ge_of_eqv
        (movingDetSpacingResidual_eq_payment_add_reserve_sub_demand k))
  unfold movingDetSpacingResidual at hres0
  exact Q'.le_of_sub_nonneg hres0

/-- The coupled reserve comparison is not a stronger surrogate: it is
exactly equivalent to the full moving-determinant inequality. -/
theorem fullDeterminant_iff_positiveDemand_le_payment_add_reserve (k : Nat) :
    ((shellDropFraction * harmonicMassCross k) * harmonicSpacing k ≤
      ((harmonicD k - harmonicA k) *
        (harmonicSpacing k - harmonicSpacing (k + 1))) *
          harmonicD (k + 1)) ↔
    (movingPositiveDemand k ≤
      movingSpacingPayment k + movingDiagonalReserve k) := by
  constructor
  · intro hdet
    have hres0 : (0 : Q') ≤ movingDetSpacingResidual k := by
      unfold movingDetSpacingResidual
      exact Q'.sub_nonneg_of_le hdet
    have hcoupled0 : (0 : Q') ≤
        (movingSpacingPayment k + movingDiagonalReserve k) -
          movingPositiveDemand k :=
      Q'.le_trans' _ _ _ hres0
        (Q'.le_of_eqv
          (movingDetSpacingResidual_eq_payment_add_reserve_sub_demand k))
    exact Q'.le_of_sub_nonneg hcoupled0
  · exact fullDeterminant_of_positiveDemand_le_payment_add_reserve k

/-- Direct shell/spacing closure from the cancellation-preserving coupled
reserve comparison. -/
theorem harmonicMass_shell_spacing_of_positiveDemand_le_payment_add_reserve
    (k : Nat)
    (h : movingPositiveDemand k ≤
      movingSpacingPayment k + movingDiagonalReserve k) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k :=
  harmonicMass_shell_spacing_of_fullDeterminant k
    (fullDeterminant_of_positiveDemand_le_payment_add_reserve k h)

/-- Final exact interface: the original shell/spacing comparison is
equivalent to paying the coupled weight-plus-adjacent demand with spacing plus
the retained diagonal-shell reserve. -/
theorem harmonicMass_shell_spacing_iff_positiveDemand_le_payment_add_reserve
    (k : Nat) :
    (harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k) ↔
    (movingPositiveDemand k ≤
      movingSpacingPayment k + movingDiagonalReserve k) := by
  exact Iff.trans
    (harmonicMass_shell_spacing_iff_fullDeterminant k)
    (fullDeterminant_iff_positiveDemand_le_payment_add_reserve k)

/-! The exact rational prefix is transported into the new determinant
formulation.  This is not a finite-case substitute for the all-scale target;
it records that the direct criterion has the correct orientation and agrees
with every existing unconditional anchor through `k=37`. -/

theorem fullDeterminant_initial_thirtyEight {k : Nat} (hk : k ≤ 37) :
    (shellDropFraction * harmonicMassCross k) * harmonicSpacing k ≤
      ((harmonicD k - harmonicA k) *
        (harmonicSpacing k - harmonicSpacing (k + 1))) *
          harmonicD (k + 1) := by
  apply (harmonicMass_shell_spacing_iff_fullDeterminant k).1
  have hcases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
      k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
      k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨
      k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨
      k = 36 ∨ k = 37 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact harmonicMass_shell_spacing_stage_k6
  · exact harmonicMass_shell_spacing_stage_k7
  · exact harmonicMass_shell_spacing_stage_k8
  · exact harmonicMass_shell_spacing_stage_k9
  · exact harmonicMass_shell_spacing_stage_k10
  · exact harmonicMass_shell_spacing_stage_k11
  · exact harmonicMass_shell_spacing_stage_k12
  · exact harmonicMass_shell_spacing_stage_k13
  · exact harmonicMass_shell_spacing_stage_k14
  · exact harmonicMass_shell_spacing_stage_k15
  · exact harmonicMass_shell_spacing_stage_k16
  · exact harmonicMass_shell_spacing_stage_k17
  · exact harmonicMass_shell_spacing_stage_k18
  · exact harmonicMass_shell_spacing_stage_k19
  · exact harmonicMass_shell_spacing_stage_k20
  · exact harmonicMass_shell_spacing_stage_k21
  · exact harmonicMass_shell_spacing_stage_k22
  · exact harmonicMass_shell_spacing_stage_k23
  · exact harmonicMass_shell_spacing_stage_k24
  · exact harmonicMass_shell_spacing_stage_k25
  · exact harmonicMass_shell_spacing_stage_k26
  · exact harmonicMass_shell_spacing_stage_k27
  · exact harmonicMass_shell_spacing_stage_k28
  · exact harmonicMass_shell_spacing_stage_k29
  · exact harmonicMass_shell_spacing_stage_k30
  · exact harmonicMass_shell_spacing_stage_k31
  · exact harmonicMass_shell_spacing_stage_k32
  · exact harmonicMass_shell_spacing_stage_k33
  · exact harmonicMass_shell_spacing_stage_k34
  · exact harmonicMass_shell_spacing_stage_k35
  · exact harmonicMass_shell_spacing_stage_k36
  · exact harmonicMass_shell_spacing_stage_k37

#print axioms shellDropFraction
#print axioms harmonicShell_convex_eqv
#print axioms shell_conservation_eqv
#print axioms harmonicMass_mul_D_eqv
#print axioms harmonicMass_drop_mul_Ds_eqv
#print axioms movingDetSpacingResidual
#print axioms shell_spacing_gap_eqv
#print axioms shell_spacing_gap_mul_Ds_eqv
#print axioms harmonicMass_shell_spacing_iff_fullDeterminant
#print axioms harmonicMass_shell_spacing_of_fullDeterminant
#print axioms movingSpacingPayment
#print axioms movingPositiveDemand
#print axioms movingDiagonalReserve
#print axioms harmonicMassCross_eq_weight_adj_sub_diag
#print axioms movingDetSpacingResidual_eq_payment_add_reserve_sub_demand
#print axioms movingDiagonalReserve_nonneg
#print axioms fullDeterminant_of_positiveDemand_le_payment_add_reserve
#print axioms fullDeterminant_iff_positiveDemand_le_payment_add_reserve
#print axioms harmonicMass_shell_spacing_of_positiveDemand_le_payment_add_reserve
#print axioms harmonicMass_shell_spacing_iff_positiveDemand_le_payment_add_reserve
#print axioms fullDeterminant_initial_thirtyEight

end YMGap.Continuum.HarmonicMovingDeterminantDirect
