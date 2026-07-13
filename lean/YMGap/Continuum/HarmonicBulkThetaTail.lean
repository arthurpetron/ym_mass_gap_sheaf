/-
The complete finite coefficient-square tail beyond the harmonic quadratic
cutoff.  At scale `k`, write `u=1/(k+2)`, `w=1-u`, and `S=(k+2)^2`.
Reciprocal Bernoulli at exponent `2*(2*S+3)` makes the degree-two Casimir-tail
ratio at most `1/2`.  Its head is the boundary square already bounded by
`1/(k+2)^2`, so every finite post-cutoff window is at most twice that
inverse-square term.
-/

import YMGap.Continuum.HarmonicCutoffBoundary
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.PlaquetteActivity

namespace YMGap.Continuum.HarmonicBulkThetaTail

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.CharacterTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- The exponent which turns the squared-base ratio back into a power of `w`. -/
def ratioExp (k : Nat) : Nat := 2 * (2 * Ncut k + 3)

/-- The reciprocal-Bernoulli denominator at the squared-tail ratio exponent is
at least eight.  Cleared with `m=k+2`, this is `8m ≤ m+4m²+6`. -/
theorem eight_le_ratioBernDen (k : Nat) :
    Q'.ofNat 8 ≤ bernDen (harmU k) (ratioExp k) := by
  have hcoef : 7 ≤ 4 * (k + 2) := by omega
  have hmul : 7 * (k + 2) ≤ (4 * (k + 2)) * (k + 2) :=
    Nat.mul_le_mul_right (k + 2) hcoef
  have hmul' : 7 * (k + 2) ≤ 4 * ((k + 2) * (k + 2)) := by
    calc
      7 * (k + 2) ≤ (4 * (k + 2)) * (k + 2) := hmul
      _ = 4 * ((k + 2) * (k + 2)) := Nat.mul_assoc 4 (k + 2) (k + 2)
  have hnat : 8 * (k + 2) ≤ (k + 2) + ratioExp k := by
    unfold ratioExp Ncut
    omega
  show (Q'.ofNat 8).num *
      ((bernDen (harmU k) (ratioExp k)).den : Int) ≤
    (bernDen (harmU k) (ratioExp k)).num * (Q'.ofNat 8).den
  unfold bernDen harmU unit ratioExp
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  exact_mod_cast hnat

private theorem four_mul_mul_two_eqv_eight_mul (p : Q') :
    (Q'.ofNat 4 * p) * Q'.ofNat 2 ≈ Q'.ofNat 8 * p := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 4) p (Q'.ofNat 2)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ (Q'.mul_comm_eqv p (Q'.ofNat 2))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat 2) p)) ?_
  exact Q'.mul_eqv_congr_right _ _ p (by decide)

/-- The degree-two tail ratio at the harmonic quadratic cutoff is at most
`1/2`.  This is the key bulk estimate, derived rather than assumed. -/
theorem squaredBase_cutoff_ratio_le_half (k : Nat) :
    Q'.ofNat 4 * qpow (harmW k * harmW k) (2 * Ncut k + 3) ≤
      HalfPow.half := by
  let n := 2 * Ncut k + 3
  let e := n + n
  let p := qpow (harmW k * harmW k) n
  let D := bernDen (harmU k) e
  have hpow : p ≈ qpow (harmW k) e := by
    dsimp only [p, e]
    refine Q'.eqv_trans _ _ _ (qpow_mul_self (harmW k) n) ?_
    exact Q'.eqv_symm (qpow_add (harmW k) n n)
  have hbern0 := oneSub_pow_mul_bernDen_le
    (harmU_nonneg k) (harmU_le_one k) e
  have hbern : qpow (harmW k) e * D ≤ (1 : Q') := by
    dsimp only [D]
    unfold harmW
    exact hbern0
  have hD8 : Q'.ofNat 8 ≤ D := by
    dsimp only [D, e, n]
    rw [show 2 * Ncut k + 3 + (2 * Ncut k + 3) = ratioExp k by
      unfold ratioExp; omega]
    exact eight_le_ratioBernDen k
  have hp0 : (0 : Q') ≤ p :=
    qpow_nonneg _ (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) n
  have hp8D : p * Q'.ofNat 8 ≤ p * D :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hD8 hp0
  have h8p : Q'.ofNat 8 * p ≤ (1 : Q') := by
    have hcomm : Q'.ofNat 8 * p ≈ p * Q'.ofNat 8 := Q'.mul_comm_eqv _ _
    have hpD : p * D ≤ (1 : Q') :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ D
          (Q'.le_of_eqv hpow)
          (Q'.le_of_lt (bernDen_pos (harmU_nonneg k) e)))
        hbern
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm)
      (Q'.le_trans' _ _ _ hp8D hpD)
  have hmul : (Q'.ofNat 4 * p) * Q'.ofNat 2 ≤
      HalfPow.half * Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (four_mul_mul_two_eqv_eight_mul p))
      (Q'.le_trans' _ _ _ h8p
        (Q'.ge_of_eqv (by decide : HalfPow.half * Q'.ofNat 2 ≈ (1 : Q'))))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide) hmul

/-- The actual squared coefficient, as the summand of the omitted theta tail. -/
def coeffSqTerm (k s : Nat) : Q' :=
  coeffW (harmW k) s * coeffW (harmW k) s

/-- The actual finite post-cutoff coefficient-square window. -/
def bulkThetaWindow (k M : Nat) : Q' :=
  finSum (fun j => coeffSqTerm k (Ncut k + j)) M

/-- Squared coefficients are exactly the degree-two Casimir tail at squared
base. -/
theorem coeffSqTerm_eqv_tailTerm (k s : Nat) :
    coeffSqTerm k s ≈ tailTerm (harmW k * harmW k) 2 s := by
  refine Q'.eqv_trans _ _ _ (coeffW_sq_eqv (harmW k) s) ?_
  unfold tailTerm dimQ
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat (s + 1)) (Q'.ofNat (s + 1))
        (qpow (harmW k * harmW k) (c4 s)))) ?_
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  have hmul := HeatKernelRGStep.ofNat_mul_eqv (s + 1) (s + 1)
  rw [Nat.pow_two]
  exact Q'.eqv_symm hmul

private theorem double_recurrence (A : Q') :
    A + HalfPow.half * (A + A) ≤ A + A := by
  refine Q'.le_of_eqv (Q'.add_eqv_congr_left A _ _ ?_)
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half A A) ?_
  exact ExpNeg.two_halves A

/-- **Full harmonic bulk-theta tail.**  Every finite coefficient-square window
starting at `Ncut k` is bounded by twice the inverse-square boundary envelope. -/
theorem bulkThetaWindow_le_double_invSq (k M : Nat) :
    bulkThetaWindow k M ≤
      invSqTerm 2 (by decide) k + invSqTerm 2 (by decide) k := by
  let A := invSqTerm 2 (by decide) k
  let f : Nat → Q' := fun j => coeffSqTerm k (Ncut k + j)
  have hr : (0 : Q') ≤ HalfPow.half := HalfPow.half_nonneg
  have hA : (0 : Q') ≤ A := unit_nonneg _ _
  have hf0 : f 0 ≤ A := by
    dsimp only [f, A]
    simpa only [Nat.add_zero] using coeffW_Ncut_sq_le_invSq k
  have hdom : ∀ j, f (j + 1) ≤ HalfPow.half * f j := by
    intro j
    have hv0 : (0 : Q') ≤ harmW k * harmW k :=
      Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
    have hv1 : harmW k * harmW k ≤ (1 : Q') := by
      have hmul := Q'.mul_le_mul_of_nonneg
        (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
      exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))
    have ht := tailTerm_ratio hv0 hv1 2 (Ncut k) j
    have hratio := squaredBase_cutoff_ratio_le_half k
    have hterm0 : (0 : Q') ≤ tailTerm (harmW k * harmW k) 2 (Ncut k + j) :=
      tailTerm_nonneg hv0 _ _
    have ht' : tailTerm (harmW k * harmW k) 2 (Ncut k + (j + 1)) ≤
        HalfPow.half * tailTerm (harmW k * harmW k) 2 (Ncut k + j) :=
      Q'.le_trans' _ _ _ ht
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hratio hterm0)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (coeffSqTerm_eqv_tailTerm k (Ncut k + (j + 1))))
      (Q'.le_trans' _ _ _ ht'
        (Q'.ge_of_eqv
          (Q'.mul_eqv_congr_left HalfPow.half _ _
            (coeffSqTerm_eqv_tailTerm k (Ncut k + j)))))
  have hclose := CharacterTail.geom_series_le f A HalfPow.half (A + A)
    hr (Q'.zero_le_add _ _ hA hA) hf0 hdom (double_recurrence A) M
  exact hclose

/-- Equivalent coefficient-`2` inverse-square presentation. -/
theorem bulkThetaWindow_le_two_mul_invSq (k M : Nat) :
    bulkThetaWindow k M ≤ Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
  exact Q'.le_trans' _ _ _ (bulkThetaWindow_le_double_invSq k M)
    (Q'.le_of_eqv (Q'.eqv_symm (BakryEmery.two_mul_eqv _)))

/-- Exact cutoff split for the squared-weight theta normalizer.  The increment
from `Ncut k` to `Ncut k + M` is precisely the actual coefficient-square
window controlled above. -/
theorem Zsum_sq_cutoff_split_eqv (k M : Nat) :
    Zsum (harmW k * harmW k) (Ncut k + M) ≈
      Zsum (harmW k * harmW k) (Ncut k) + bulkThetaWindow k M := by
  unfold Zsum bulkThetaWindow
  rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
  refine Q'.eqv_trans _ _ _
    (YMGap.Constructive.finSum_split
      (fun s => dimQ s *
        (dimQ s * qpow (harmW k * harmW k) (c4 s))) (Ncut k) M) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (RationalTail.finSum_eqv_congr
      (fun j => dimQ (Ncut k + j) *
        (dimQ (Ncut k + j) *
          qpow (harmW k * harmW k) (c4 (Ncut k + j))))
      (fun j => coeffSqTerm k (Ncut k + j))
      (fun j => Q'.eqv_symm (coeffW_sq_eqv (harmW k) (Ncut k + j))) M)

/-- Cutoff-stability form used in finite-to-large-cutoff quotient comparisons:
the squared theta normalizer can grow by at most `2/(k+2)^2` beyond the
quadratic cutoff, uniformly over every finite extension. -/
theorem Zsum_sq_cutoff_extension_le (k M : Nat) :
    Zsum (harmW k * harmW k) (Ncut k + M) ≤
      Zsum (harmW k * harmW k) (Ncut k) +
        Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Zsum_sq_cutoff_split_eqv k M))
    (Q'.add_le_add_left _ _ _ (bulkThetaWindow_le_two_mul_invSq k M))

/-- Any choice of finite character-window lengths inherits the explicit
inverse-square scale modulus.  This is the form consumed by cutoff-limit
comparisons, where the omitted character window may vary with the RG scale. -/
theorem bulkTheta_schedule_window_modulus (L : Nat → Nat) (N M : Nat) :
    tailSum (fun k => bulkThetaWindow k (L k)) N M ≤
      Q'.ofNat 2 * pot 2 (by decide) N := by
  exact summableBound_of_invSq 2 (by decide) (Q'.ofNat 2) (by decide)
    (fun k => bulkThetaWindow k (L k))
    (fun k => bulkThetaWindow_le_two_mul_invSq k (L k)) N M

end YMGap.Continuum.HarmonicBulkThetaTail

#print axioms YMGap.Continuum.HarmonicBulkThetaTail.eight_le_ratioBernDen
#print axioms YMGap.Continuum.HarmonicBulkThetaTail.squaredBase_cutoff_ratio_le_half
#print axioms YMGap.Continuum.HarmonicBulkThetaTail.coeffSqTerm_eqv_tailTerm
#print axioms YMGap.Continuum.HarmonicBulkThetaTail.bulkThetaWindow_le_double_invSq
#print axioms YMGap.Continuum.HarmonicBulkThetaTail.bulkThetaWindow_le_two_mul_invSq
#print axioms YMGap.Continuum.HarmonicBulkThetaTail.Zsum_sq_cutoff_split_eqv
#print axioms YMGap.Continuum.HarmonicBulkThetaTail.Zsum_sq_cutoff_extension_le
#print axioms YMGap.Continuum.HarmonicBulkThetaTail.bulkTheta_schedule_window_modulus
