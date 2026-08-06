/-
Track 11.7-fusion / R3k -- common-denominator theta certificates.

# Purpose

Direct evaluation of a finite `Q'` theta sum repeatedly multiplies unrelated
denominators.  At the first physical tail cell this creates an expression much
larger than the mathematical numerator.  This module starts the constructive
replacement: powers of natural numerators and denominators are evaluated by a
logarithmic square-and-multiply kernel, with a kernel-checked proof that it is
the ordinary natural power.

The next layer uses this kernel to clear every monomial of one theta sum to a
single denominator.  An external Rust program may generate or benchmark the
resulting integer certificate, but it is not trusted: Lean checks the common-
denominator arithmetic and the final integer inequality.

# Constructivity

Structural recursion with an explicit fuel, natural division by two, and
decidable arithmetic only.  No `Classical`, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaPathEnergy

namespace YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "cell_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. Logarithmic natural powers -/

/-- Fuelled square-and-multiply.  The public call supplies `exponent + 1`
units of fuel, while every recursive call halves the exponent. -/
def fastNatPowAux (base accumulator : Nat) : Nat -> Nat -> Nat
  | 0, _ => accumulator
  | fuel + 1, exponent =>
      if exponent = 0 then accumulator
      else
        fastNatPowAux (base * base)
          (if exponent % 2 = 1 then accumulator * base else accumulator)
          fuel (exponent / 2)

/-- Logarithmic square-and-multiply evaluator for natural powers. -/
def fastNatPow (base exponent : Nat) : Nat :=
  fastNatPowAux base 1 (exponent + 1) exponent

private theorem nat_pow_split_two (base exponent : Nat) :
    base ^ exponent =
      base ^ (exponent % 2) * (base * base) ^ (exponent / 2) := by
  have hsplit : exponent % 2 + 2 * (exponent / 2) = exponent :=
    Nat.mod_add_div exponent 2
  calc
    base ^ exponent = base ^ (exponent % 2 + 2 * (exponent / 2)) := by
      rw [hsplit]
    _ = base ^ (exponent % 2) * base ^ (2 * (exponent / 2)) :=
      Nat.pow_add _ _ _
    _ = base ^ (exponent % 2) * (base ^ 2) ^ (exponent / 2) := by
      rw [Nat.pow_mul]
    _ = base ^ (exponent % 2) * (base * base) ^ (exponent / 2) := by
      simp only [Nat.pow_two]

private theorem fastNatPowAux_correct (base accumulator fuel exponent : Nat)
    (hexponent : exponent < fuel) :
    fastNatPowAux base accumulator fuel exponent =
      accumulator * base ^ exponent := by
  induction fuel generalizing base accumulator exponent with
  | zero => omega
  | succ fuel ih =>
      rw [fastNatPowAux]
      by_cases hzero : exponent = 0
      · subst exponent
        simp
      · rw [if_neg hzero]
        have hpos : 0 < exponent := Nat.pos_of_ne_zero hzero
        have hdivlt : exponent / 2 < exponent :=
          Nat.div_lt_self hpos (by decide)
        have hdivfuel : exponent / 2 < fuel := by omega
        rw [ih (base * base)
          (if exponent % 2 = 1 then accumulator * base else accumulator)
          (exponent / 2) hdivfuel]
        by_cases hodd : exponent % 2 = 1
        · rw [if_pos hodd]
          have hpow := nat_pow_split_two base exponent
          rw [hodd] at hpow
          simp only [Nat.pow_one] at hpow
          calc
            (accumulator * base) * (base * base) ^ (exponent / 2) =
                accumulator *
                  (base * (base * base) ^ (exponent / 2)) := by
              rw [Nat.mul_assoc]
            _ = accumulator * base ^ exponent := by rw [hpow]
        · rw [if_neg hodd]
          have hmodlt : exponent % 2 < 2 := Nat.mod_lt exponent (by decide)
          have heven : exponent % 2 = 0 := by omega
          have hpow := nat_pow_split_two base exponent
          rw [heven] at hpow
          simp only [Nat.pow_zero, Nat.one_mul] at hpow
          rw [hpow]

/-- Soundness of the computation kernel.  This theorem is the trust boundary
for all later common-denominator certificates. -/
theorem fastNatPow_eq_pow (base exponent : Nat) :
    fastNatPow base exponent = base ^ exponent := by
  unfold fastNatPow
  have h := fastNatPowAux_correct base 1 (exponent + 1) exponent (by omega)
  simpa using h

/-- The fast evaluator preserves positivity of a positive base. -/
theorem fastNatPow_pos {base : Nat} (hbase : 0 < base) (exponent : Nat) :
    0 < fastNatPow base exponent := by
  rw [fastNatPow_eq_pow]
  exact Nat.pow_pos hbase

/-! ## 2. One common-denominator monomial -/

private theorem qpow_mkPos_num_pow (numerator denominator : Nat)
    (hdenominator : 0 < denominator) : forall exponent : Nat,
    (qpow (Q'.mkPos numerator denominator hdenominator) exponent).num =
      (numerator ^ exponent : Nat) := by
  intro exponent
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [qpow]
      rw [Q'.mul_num_cast, ih, Q'.mkPos_num]
      exact_mod_cast (Nat.pow_succ numerator exponent).symm

private theorem qpow_mkPos_den_pow (numerator denominator : Nat)
    (hdenominator : 0 < denominator) : forall exponent : Nat,
    ((qpow (Q'.mkPos numerator denominator hdenominator) exponent).den : Int) =
      (denominator ^ exponent : Nat) := by
  intro exponent
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [qpow]
      rw [Q'.mul_den_cast, ih, Q'.mkPos_den]
      exact_mod_cast (Nat.pow_succ denominator exponent).symm

/-- A rational power of a positive natural fraction is represented by the
fast powers of its numerator and denominator. -/
theorem qpow_mkPos_eqv_fast (numerator denominator exponent : Nat)
    (hdenominator : 0 < denominator) :
    qpow (Q'.mkPos numerator denominator hdenominator) exponent ≈
      Q'.mkPos (fastNatPow numerator exponent)
        (fastNatPow denominator exponent)
        (fastNatPow_pos hdenominator exponent) := by
  show
    (qpow (Q'.mkPos numerator denominator hdenominator) exponent).num *
        ((Q'.mkPos (fastNatPow numerator exponent)
          (fastNatPow denominator exponent) _).den : Int) =
      (Q'.mkPos (fastNatPow numerator exponent)
        (fastNatPow denominator exponent) _).num *
        ((qpow (Q'.mkPos numerator denominator hdenominator) exponent).den : Int)
  simp only [qpow_mkPos_num_pow, qpow_mkPos_den_pow,
    Q'.mkPos_num, Q'.mkPos_den, fastNatPow_eq_pow]

/-- Cleared numerator of `coefficient * (numerator/denominator)^exponent`
at the shared power denominator `denominator^maxExponent`. -/
def clearedMonomialNum (numerator denominator maxExponent coefficient exponent : Nat) : Nat :=
  coefficient * fastNatPow numerator exponent *
    fastNatPow denominator (maxExponent - exponent)

/-- Shared power denominator used by a cleared monomial row. -/
def clearedPowerDen (denominator maxExponent : Nat) : Nat :=
  fastNatPow denominator maxExponent

/-- The rational value represented by one cleared natural monomial. -/
def clearedMonomialQ (numerator denominator maxExponent coefficient exponent : Nat)
    (hdenominator : 0 < denominator) : Q' :=
  Q'.mkPos
    (clearedMonomialNum numerator denominator maxExponent coefficient exponent)
    (clearedPowerDen denominator maxExponent)
    (fastNatPow_pos hdenominator maxExponent)

/-- Common-denominator soundness for one nonnegative monomial.  The proof is
symbolic in all five natural parameters; later certificate checks therefore
never normalize a `Q'` power or a growing rational sum. -/
theorem monomial_eqv_clearedMonomialQ
    (numerator denominator maxExponent coefficient exponent : Nat)
    (hdenominator : 0 < denominator) (hexponent : exponent <= maxExponent) :
    Q'.ofNat coefficient *
        qpow (Q'.mkPos numerator denominator hdenominator) exponent ≈
      clearedMonomialQ numerator denominator maxExponent coefficient exponent
        hdenominator := by
  have hmax : maxExponent - exponent + exponent = maxExponent :=
    Nat.sub_add_cancel hexponent
  unfold clearedMonomialQ clearedMonomialNum clearedPowerDen
  simp only [fastNatPow_eq_pow]
  show
    (Q'.ofNat coefficient *
      qpow (Q'.mkPos numerator denominator hdenominator) exponent).num *
        ((Q'.mkPos
          (coefficient * numerator ^ exponent * denominator ^ (maxExponent - exponent))
          (denominator ^ maxExponent) _).den : Int) =
      (Q'.mkPos
        (coefficient * numerator ^ exponent * denominator ^ (maxExponent - exponent))
        (denominator ^ maxExponent) _).num *
        ((Q'.ofNat coefficient *
          qpow (Q'.mkPos numerator denominator hdenominator) exponent).den : Int)
  rw [Q'.mul_num_cast, Q'.ofNat_num_cast,
    qpow_mkPos_num_pow, Q'.mkPos_den, Q'.mkPos_num,
    Q'.mul_den_cast, Q'.ofNat_den_cast, Int.one_mul,
    qpow_mkPos_den_pow]
  rw [show denominator ^ maxExponent =
      denominator ^ (maxExponent - exponent) * denominator ^ exponent by
    rw [← Nat.pow_add, hmax]]
  push_cast
  ac_rfl

/-! ## 3. A whole row at one denominator -/

/-- Sum of the cleared natural numerators of a sparse monomial row. -/
def clearedMonomialSum (numerator denominator maxExponent : Nat)
    (coefficient exponent : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | count + 1 =>
      clearedMonomialSum numerator denominator maxExponent coefficient exponent count +
        clearedMonomialNum numerator denominator maxExponent
          (coefficient count) (exponent count)

/-- Rational proxy for a whole cleared monomial row. -/
def clearedMonomialSumQ (numerator denominator maxExponent : Nat)
    (coefficient exponent : Nat -> Nat) (count : Nat)
    (hdenominator : 0 < denominator) : Q' :=
  Q'.mkPos
    (clearedMonomialSum numerator denominator maxExponent
      coefficient exponent count)
    (clearedPowerDen denominator maxExponent)
    (fastNatPow_pos hdenominator maxExponent)

private theorem mkPos_nat_add_same_den (left right denominator : Nat)
    (hdenominator : 0 < denominator) :
    Q'.mkPos left denominator hdenominator +
        Q'.mkPos right denominator hdenominator ≈
      Q'.mkPos (left + right) denominator hdenominator := by
  show
    (Q'.mkPos left denominator hdenominator +
      Q'.mkPos right denominator hdenominator).num *
        ((Q'.mkPos (left + right) denominator hdenominator).den : Int) =
      (Q'.mkPos (left + right) denominator hdenominator).num *
        ((Q'.mkPos left denominator hdenominator +
          Q'.mkPos right denominator hdenominator).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast,
    Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  rw [Int.add_mul, Int.add_mul]
  ac_rfl

/-- Generic row soundness.  The only semantic premise is the cheap exponent
ceiling; the large powers are evaluated once by `fastNatPow`. -/
theorem finSum_monomials_eqv_cleared
    (numerator denominator maxExponent : Nat)
    (coefficient exponent : Nat -> Nat) (hdenominator : 0 < denominator) :
    forall count : Nat,
      (forall i, i < count -> exponent i <= maxExponent) ->
      finSum
          (fun i => Q'.ofNat (coefficient i) *
            qpow (Q'.mkPos numerator denominator hdenominator) (exponent i))
          count ≈
        clearedMonomialSumQ numerator denominator maxExponent
          coefficient exponent count hdenominator
  | 0, _ => by
      unfold clearedMonomialSumQ clearedMonomialSum clearedPowerDen
      show (0 : Q') ≈ Q'.mkPos 0 (fastNatPow denominator maxExponent) _
      change (0 : Int) * _ = (0 : Int) * _
      simp
  | count + 1, hceiling => by
      have ih := finSum_monomials_eqv_cleared numerator denominator maxExponent
        coefficient exponent hdenominator count
        (fun i hi => hceiling i (by omega))
      have hterm := monomial_eqv_clearedMonomialQ numerator denominator
        maxExponent (coefficient count) (exponent count) hdenominator
        (hceiling count (by omega))
      rw [finSum_succ]
      refine Q'.eqv_trans _
        (clearedMonomialSumQ numerator denominator maxExponent
            coefficient exponent count hdenominator +
          clearedMonomialQ numerator denominator maxExponent
            (coefficient count) (exponent count) hdenominator) _ ?_ ?_
      · exact Q'.add_eqv_congr' ih hterm
      · unfold clearedMonomialSumQ clearedMonomialQ
        change
          Q'.mkPos
              (clearedMonomialSum numerator denominator maxExponent
                coefficient exponent count)
              (clearedPowerDen denominator maxExponent) _ +
            Q'.mkPos
              (clearedMonomialNum numerator denominator maxExponent
                (coefficient count) (exponent count))
              (clearedPowerDen denominator maxExponent) _ ≈
          Q'.mkPos
            (clearedMonomialSum numerator denominator maxExponent
                coefficient exponent count +
              clearedMonomialNum numerator denominator maxExponent
                (coefficient count) (exponent count))
            (clearedPowerDen denominator maxExponent) _
        exact mkPos_nat_add_same_den _ _ _ _

private theorem ofNat_mul_eqv_local (left right : Nat) :
    Q'.ofNat left * Q'.ofNat right ≈ Q'.ofNat (left * right) := by
  show ((left : Int) * (right : Int)) * 1 = ((left * right : Nat) : Int) * 1
  push_cast
  simp

private theorem coeffW_product_monomial (w : Q') (left right : Nat) :
    coeffW w left * coeffW w right ≈
      Q'.ofNat ((left + 1) * (right + 1)) *
        qpow w (c4 left + c4 right) := by
  unfold coeffW dimQ
  refine Q'.eqv_trans _
    ((Q'.ofNat (left + 1) * Q'.ofNat (right + 1)) *
      (qpow w (c4 left) * qpow w (c4 right))) _ ?_ ?_
  · show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv_local _ _))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (HeatKernelRGStep.qpow_add w (c4 left) (c4 right))))

/-- Cleared squared-norm numerator for modes `0,...,N`. -/
def clearedCoordNum (numerator denominator N : Nat) : Nat :=
  clearedMonomialSum numerator denominator (2 * c4 N)
    (fun s => (s + 1) * (s + 1))
    (fun s => c4 s + c4 s) (N + 1)

/-- Cleared adjacent-correlation numerator for edges `0,...,N-1`. -/
def clearedAdjNum (numerator denominator N : Nat) : Nat :=
  clearedMonomialSum numerator denominator (2 * c4 N)
    (fun s => (s + 1) * (s + 2))
    (fun s => c4 s + c4 (s + 1)) N

/-- Shared denominator for both cleared coefficient sums at cutoff `N`. -/
def clearedThetaDen (denominator N : Nat) : Nat :=
  clearedPowerDen denominator (2 * c4 N)

/-- Cleared rational proxy for the squared coefficient norm. -/
def clearedCoordQ (numerator denominator N : Nat)
    (hdenominator : 0 < denominator) : Q' :=
  Q'.mkPos (clearedCoordNum numerator denominator N)
    (clearedThetaDen denominator N)
    (fastNatPow_pos hdenominator (2 * c4 N))

/-- Cleared rational proxy for the adjacent coefficient correlation. -/
def clearedAdjQ (numerator denominator N : Nat)
    (hdenominator : 0 < denominator) : Q' :=
  Q'.mkPos (clearedAdjNum numerator denominator N)
    (clearedThetaDen denominator N)
    (fastNatPow_pos hdenominator (2 * c4 N))

private theorem doubled_c4_mono {s N : Nat} (hsN : s <= N) :
    c4 s + c4 s <= 2 * c4 N := by
  have h : c4 s <= c4 N := by
    unfold c4
    exact Nat.mul_le_mul hsN (by omega)
  omega

private theorem adjacent_c4_le_double {s N : Nat} (hsN : s < N) :
    c4 s + c4 (s + 1) <= 2 * c4 N := by
  have h0 : c4 s <= c4 N := by
    unfold c4
    exact Nat.mul_le_mul (by omega) (by omega)
  have h1 : c4 (s + 1) <= c4 N := by
    unfold c4
    exact Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Exact semantics of the common-denominator squared-norm numerator. -/
theorem coordNormSq_eqv_clearedCoordQ
    (numerator denominator N : Nat) (hdenominator : 0 < denominator) :
    coordNormSq (Q'.mkPos numerator denominator hdenominator) N ≈
      clearedCoordQ numerator denominator N hdenominator := by
  unfold coordNormSq
  rw [MovingCutoff.fsum_eq_finSum]
  refine Q'.eqv_trans _
    (finSum
      (fun s => Q'.ofNat ((s + 1) * (s + 1)) *
        qpow (Q'.mkPos numerator denominator hdenominator)
          (c4 s + c4 s)) (N + 1)) _ ?_ ?_
  · exact finSum_eqv_congr _ _
      (fun s => coeffW_product_monomial _ s s) (N + 1)
  · simpa only [clearedCoordQ, clearedCoordNum, clearedThetaDen] using
      (finSum_monomials_eqv_cleared numerator denominator (2 * c4 N)
        (fun s => (s + 1) * (s + 1)) (fun s => c4 s + c4 s)
        hdenominator (N + 1)
        (fun s hs => doubled_c4_mono (by omega)))

/-- Exact semantics of the common-denominator adjacent-correlation numerator. -/
theorem adjCorr_eqv_clearedAdjQ
    (numerator denominator N : Nat) (hdenominator : 0 < denominator) :
    adjCorr (Q'.mkPos numerator denominator hdenominator) N ≈
      clearedAdjQ numerator denominator N hdenominator := by
  unfold adjCorr
  rw [MovingCutoff.fsum_eq_finSum]
  refine Q'.eqv_trans _
    (finSum
      (fun s => Q'.ofNat ((s + 1) * (s + 2)) *
        qpow (Q'.mkPos numerator denominator hdenominator)
          (c4 s + c4 (s + 1))) N) _ ?_ ?_
  · exact finSum_eqv_congr _ _
      (fun s => coeffW_product_monomial _ s (s + 1)) N
  · simpa only [clearedAdjQ, clearedAdjNum, clearedThetaDen] using
      (finSum_monomials_eqv_cleared numerator denominator (2 * c4 N)
        (fun s => (s + 1) * (s + 2)) (fun s => c4 s + c4 (s + 1))
        hdenominator N
        (fun s hs => adjacent_c4_le_double hs))

/-! ## 4. Reflection-friendly coefficient-sandwich cells -/

/-- Coefficient-space deficit.  Its theta path-energy image is proved below;
this coordinate avoids every theta normalization factor. -/
def coefficientDeficit (w : Q') (N : Nat) : Q' :=
  coordNormSq w N + (-adjCorr w N)

/-- Cleared proxy for the coefficient-space deficit. -/
def clearedDeficitQ (numerator denominator N : Nat)
    (hdenominator : 0 < denominator) : Q' :=
  clearedCoordQ numerator denominator N hdenominator +
    (-clearedAdjQ numerator denominator N hdenominator)

/-- The two local inequalities after all positive theta normalization factors
have been canceled. -/
structure CoefficientSandwichCell
    (coarseWeight fineWeight fourthWeight debt : Q')
    (coarseCut fineCut fourthCut : Nat) : Type where
  coarse :
    coordNormSq coarseWeight coarseCut *
        coefficientDeficit fourthWeight fourthCut <=
      coefficientDeficit coarseWeight coarseCut *
          coordNormSq fourthWeight fourthCut +
        debt *
          (coordNormSq coarseWeight coarseCut *
            coordNormSq fourthWeight fourthCut)
  fine :
    Q'.ofNat 2 *
        (coordNormSq fourthWeight fourthCut *
          coefficientDeficit fineWeight fineCut) +
      debt *
        (coordNormSq fineWeight fineCut *
          coordNormSq fourthWeight fourthCut) <=
      coordNormSq fineWeight fineCut *
        coefficientDeficit fourthWeight fourthCut

/-- Executable checker on the cleared proxies only. -/
def clearedCoefficientSandwichCheck
    (coarseNumerator coarseDenominator coarseCut : Nat)
    (fineNumerator fineDenominator fineCut : Nat)
    (fourthNumerator fourthDenominator fourthCut : Nat)
    (debt : Q')
    (hcoarseDen : 0 < coarseDenominator)
    (hfineDen : 0 < fineDenominator)
    (hfourthDen : 0 < fourthDenominator) : Bool :=
  decide
    (clearedCoordQ coarseNumerator coarseDenominator coarseCut hcoarseDen *
          clearedDeficitQ fourthNumerator fourthDenominator fourthCut hfourthDen <=
        clearedDeficitQ coarseNumerator coarseDenominator coarseCut hcoarseDen *
            clearedCoordQ fourthNumerator fourthDenominator fourthCut hfourthDen +
          debt *
            (clearedCoordQ coarseNumerator coarseDenominator coarseCut hcoarseDen *
              clearedCoordQ fourthNumerator fourthDenominator fourthCut hfourthDen) /\
      Q'.ofNat 2 *
          (clearedCoordQ fourthNumerator fourthDenominator fourthCut hfourthDen *
            clearedDeficitQ fineNumerator fineDenominator fineCut hfineDen) +
        debt *
          (clearedCoordQ fineNumerator fineDenominator fineCut hfineDen *
            clearedCoordQ fourthNumerator fourthDenominator fourthCut hfourthDen) <=
        clearedCoordQ fineNumerator fineDenominator fineCut hfineDen *
          clearedDeficitQ fourthNumerator fourthDenominator fourthCut hfourthDen)

private theorem mul_eqv_both {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ right hleft)
    (Q'.mul_eqv_congr_left left' _ _ hright)

private theorem qpow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : forall exponent : Nat,
    qpow left exponent ≈ qpow right exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 =>
      mul_eqv_both (qpow_eqv_congr_local h exponent) h

private theorem coeffW_eqv_congr_local {left right : Q'}
    (h : left ≈ right) (s : Nat) :
    coeffW left s ≈ coeffW right s := by
  unfold coeffW
  exact Q'.mul_eqv_congr_left _ _ _
    (qpow_eqv_congr_local h (c4 s))

private theorem coordNormSq_eqv_congr_local {left right : Q'}
    (h : left ≈ right) (N : Nat) :
    coordNormSq left N ≈ coordNormSq right N := by
  unfold coordNormSq
  rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
  exact finSum_eqv_congr _ _
    (fun s => mul_eqv_both
      (coeffW_eqv_congr_local h s) (coeffW_eqv_congr_local h s)) (N + 1)

private theorem adjCorr_eqv_congr_local {left right : Q'}
    (h : left ≈ right) (N : Nat) :
    adjCorr left N ≈ adjCorr right N := by
  unfold adjCorr
  rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
  exact finSum_eqv_congr _ _
    (fun s => mul_eqv_both
      (coeffW_eqv_congr_local h s) (coeffW_eqv_congr_local h (s + 1))) N

private theorem coefficientDeficit_eqv_congr_local {left right : Q'}
    (h : left ≈ right) (N : Nat) :
    coefficientDeficit left N ≈ coefficientDeficit right N := by
  unfold coefficientDeficit
  exact Q'.add_eqv_congr'
    (coordNormSq_eqv_congr_local h N)
    (Q'.neg_eqv_congr _ _ (adjCorr_eqv_congr_local h N))

private theorem coefficientDeficit_eqv_cleared
    (numerator denominator N : Nat) (hdenominator : 0 < denominator) :
    coefficientDeficit (Q'.mkPos numerator denominator hdenominator) N ≈
      clearedDeficitQ numerator denominator N hdenominator := by
  unfold coefficientDeficit clearedDeficitQ
  exact Q'.add_eqv_congr'
    (coordNormSq_eqv_clearedCoordQ numerator denominator N hdenominator)
    (Q'.neg_eqv_congr _ _
      (adjCorr_eqv_clearedAdjQ numerator denominator N hdenominator))

/-- Reflection soundness: a successful cleared integer check reconstructs the
two exact coefficient inequalities at the represented rational weights. -/
def CoefficientSandwichCell.ofClearedCheck
    (coarseNumerator coarseDenominator coarseCut : Nat)
    (fineNumerator fineDenominator fineCut : Nat)
    (fourthNumerator fourthDenominator fourthCut : Nat)
    (debt : Q')
    (hcoarseDen : 0 < coarseDenominator)
    (hfineDen : 0 < fineDenominator)
    (hfourthDen : 0 < fourthDenominator)
    (hcheck : clearedCoefficientSandwichCheck
      coarseNumerator coarseDenominator coarseCut
      fineNumerator fineDenominator fineCut
      fourthNumerator fourthDenominator fourthCut debt
      hcoarseDen hfineDen hfourthDen = true) :
    CoefficientSandwichCell
      (Q'.mkPos coarseNumerator coarseDenominator hcoarseDen)
      (Q'.mkPos fineNumerator fineDenominator hfineDen)
      (Q'.mkPos fourthNumerator fourthDenominator hfourthDen)
      debt coarseCut fineCut fourthCut := by
  have checked := of_decide_eq_true hcheck
  let Dc := coordNormSq
    (Q'.mkPos coarseNumerator coarseDenominator hcoarseDen) coarseCut
  let Tc := coefficientDeficit
    (Q'.mkPos coarseNumerator coarseDenominator hcoarseDen) coarseCut
  let Df := coordNormSq
    (Q'.mkPos fineNumerator fineDenominator hfineDen) fineCut
  let Tf := coefficientDeficit
    (Q'.mkPos fineNumerator fineDenominator hfineDen) fineCut
  let D4 := coordNormSq
    (Q'.mkPos fourthNumerator fourthDenominator hfourthDen) fourthCut
  let T4 := coefficientDeficit
    (Q'.mkPos fourthNumerator fourthDenominator hfourthDen) fourthCut
  let dc := clearedCoordQ coarseNumerator coarseDenominator coarseCut hcoarseDen
  let tc := clearedDeficitQ coarseNumerator coarseDenominator coarseCut hcoarseDen
  let df := clearedCoordQ fineNumerator fineDenominator fineCut hfineDen
  let tf := clearedDeficitQ fineNumerator fineDenominator fineCut hfineDen
  let d4 := clearedCoordQ fourthNumerator fourthDenominator fourthCut hfourthDen
  let t4 := clearedDeficitQ fourthNumerator fourthDenominator fourthCut hfourthDen
  have hDc : Dc ≈ dc := by
    simpa only [Dc, dc] using coordNormSq_eqv_clearedCoordQ
      coarseNumerator coarseDenominator coarseCut hcoarseDen
  have hTc : Tc ≈ tc := by
    simpa only [Tc, tc] using coefficientDeficit_eqv_cleared
      coarseNumerator coarseDenominator coarseCut hcoarseDen
  have hDf : Df ≈ df := by
    simpa only [Df, df] using coordNormSq_eqv_clearedCoordQ
      fineNumerator fineDenominator fineCut hfineDen
  have hTf : Tf ≈ tf := by
    simpa only [Tf, tf] using coefficientDeficit_eqv_cleared
      fineNumerator fineDenominator fineCut hfineDen
  have hD4 : D4 ≈ d4 := by
    simpa only [D4, d4] using coordNormSq_eqv_clearedCoordQ
      fourthNumerator fourthDenominator fourthCut hfourthDen
  have hT4 : T4 ≈ t4 := by
    simpa only [T4, t4] using coefficientDeficit_eqv_cleared
      fourthNumerator fourthDenominator fourthCut hfourthDen
  refine ⟨?_, ?_⟩
  · have hleft : Dc * T4 ≈ dc * t4 := mul_eqv_both hDc hT4
    have hright :
        Tc * D4 + debt * (Dc * D4) ≈
          tc * d4 + debt * (dc * d4) :=
      Q'.add_eqv_congr'
        (mul_eqv_both hTc hD4)
        (Q'.mul_eqv_congr_left debt _ _ (mul_eqv_both hDc hD4))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ checked.1 (Q'.ge_of_eqv hright))
  · have hleft :
        Q'.ofNat 2 * (D4 * Tf) + debt * (Df * D4) ≈
          Q'.ofNat 2 * (d4 * tf) + debt * (df * d4) :=
      Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (mul_eqv_both hD4 hTf))
        (Q'.mul_eqv_congr_left debt _ _ (mul_eqv_both hDf hD4))
    have hright : Df * T4 ≈ df * t4 := mul_eqv_both hDf hT4
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ checked.2 (Q'.ge_of_eqv hright))

/-- Transport a coefficient cell along exact rational equivalences of its
three weights. -/
def CoefficientSandwichCell.transportWeights
    {coarseWeight coarseWeight' fineWeight fineWeight' fourthWeight fourthWeight'
      debt : Q'} {coarseCut fineCut fourthCut : Nat}
    (C : CoefficientSandwichCell coarseWeight' fineWeight' fourthWeight'
      debt coarseCut fineCut fourthCut)
    (hcoarse : coarseWeight ≈ coarseWeight')
    (hfine : fineWeight ≈ fineWeight')
    (hfourth : fourthWeight ≈ fourthWeight') :
    CoefficientSandwichCell coarseWeight fineWeight fourthWeight
      debt coarseCut fineCut fourthCut := by
  let Dc := coordNormSq coarseWeight coarseCut
  let Tc := coefficientDeficit coarseWeight coarseCut
  let Df := coordNormSq fineWeight fineCut
  let Tf := coefficientDeficit fineWeight fineCut
  let D4 := coordNormSq fourthWeight fourthCut
  let T4 := coefficientDeficit fourthWeight fourthCut
  let dc := coordNormSq coarseWeight' coarseCut
  let tc := coefficientDeficit coarseWeight' coarseCut
  let df := coordNormSq fineWeight' fineCut
  let tf := coefficientDeficit fineWeight' fineCut
  let d4 := coordNormSq fourthWeight' fourthCut
  let t4 := coefficientDeficit fourthWeight' fourthCut
  have hDc : Dc ≈ dc := coordNormSq_eqv_congr_local hcoarse coarseCut
  have hTc : Tc ≈ tc := coefficientDeficit_eqv_congr_local hcoarse coarseCut
  have hDf : Df ≈ df := coordNormSq_eqv_congr_local hfine fineCut
  have hTf : Tf ≈ tf := coefficientDeficit_eqv_congr_local hfine fineCut
  have hD4 : D4 ≈ d4 := coordNormSq_eqv_congr_local hfourth fourthCut
  have hT4 : T4 ≈ t4 := coefficientDeficit_eqv_congr_local hfourth fourthCut
  refine ⟨?_, ?_⟩
  · have hleft : Dc * T4 ≈ dc * t4 := mul_eqv_both hDc hT4
    have hright :
        Tc * D4 + debt * (Dc * D4) ≈
          tc * d4 + debt * (dc * d4) :=
      Q'.add_eqv_congr'
        (mul_eqv_both hTc hD4)
        (Q'.mul_eqv_congr_left debt _ _ (mul_eqv_both hDc hD4))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ C.coarse (Q'.ge_of_eqv hright))
  · have hleft :
        Q'.ofNat 2 * (D4 * Tf) + debt * (Df * D4) ≈
          Q'.ofNat 2 * (d4 * tf) + debt * (df * d4) :=
      Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (mul_eqv_both hD4 hTf))
        (Q'.mul_eqv_congr_left debt _ _ (mul_eqv_both hDf hD4))
    have hright : Df * T4 ≈ df * t4 := mul_eqv_both hDf hT4
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ C.fine (Q'.ge_of_eqv hright))

/-! ## 5. First physical tail anchor (`k = 4`) -/

/-- Exact coarse weight `blockWeight 4 = 3071/3072`. -/
def blockK4CoarseWeight : Q' := Q'.mkPos 3071 3072 (by decide)

/-- Exact fine weight `blockWeight 5 = 12287/12288`. -/
def blockK4FineWeight : Q' := Q'.mkPos 12287 12288 (by decide)

/-- Cleared numerator of the fourth power of the fine weight. -/
def blockK4FourthNumerator : Nat := fastNatPow 12287 4

/-- Cleared denominator of the fourth power of the fine weight. -/
def blockK4FourthDenominator : Nat := fastNatPow 12288 4

/-- Exact fourth-power fine weight used at the common coarse cutoff. -/
def blockK4FourthWeight : Q' :=
  Q'.mkPos blockK4FourthNumerator blockK4FourthDenominator
    (fastNatPow_pos (by decide) 4)

/-- The optimized common-denominator checker closes the first open physical
tail cell.  This is the nonvacuous `N=79 -> 159` anchor; it does not expand a
canonical rational theta expression. -/
theorem blockK4ClearedCoefficientCheck :
    clearedCoefficientSandwichCheck
      3071 3072 79
      12287 12288 159
      blockK4FourthNumerator blockK4FourthDenominator 79
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 4)
      (by decide) (by decide) (fastNatPow_pos (by decide) 4) = true := by
  decide

/-- Kernel-checked coefficient-space sandwich at the first physical tail
scale. -/
def blockK4CoefficientSandwichCell :
    CoefficientSandwichCell
      blockK4CoarseWeight blockK4FineWeight blockK4FourthWeight
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 4)
      79 159 79 :=
  CoefficientSandwichCell.ofClearedCheck
    3071 3072 79
    12287 12288 159
    blockK4FourthNumerator blockK4FourthDenominator 79
    (P2BlockCompatibleThetaParityTransport.blockParityDebt 4)
    (by decide) (by decide) (fastNatPow_pos (by decide) 4)
    blockK4ClearedCoefficientCheck

theorem blockWeight_four_eqv_explicit :
    P2BlockCompatibleSchedule.blockWeight 4 ≈ blockK4CoarseWeight := by
  decide

theorem blockWeight_five_eqv_explicit :
    P2BlockCompatibleSchedule.blockWeight 5 ≈ blockK4FineWeight := by
  decide

theorem blockWeight_five_fourth_eqv_explicit :
    qpow (P2BlockCompatibleSchedule.blockWeight 5) 4 ≈
      blockK4FourthWeight := by
  exact Q'.eqv_trans _ _ _
    (qpow_eqv_congr_local blockWeight_five_eqv_explicit 4)
    (qpow_mkPos_eqv_fast 12287 12288 4 (by decide))

/-- The first checked cell at the literal block-compatible schedule weights. -/
def blockK4PhysicalCoefficientSandwichCell :
    CoefficientSandwichCell
      (P2BlockCompatibleSchedule.blockWeight 4)
      (P2BlockCompatibleSchedule.blockWeight 5)
      (qpow (P2BlockCompatibleSchedule.blockWeight 5) 4)
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 4)
      (P2BlockCompatibleSchedule.blockNcut 4)
      (P2BlockCompatibleSchedule.blockNcut 5)
      (P2BlockCompatibleSchedule.blockNcut 4) := by
  have hN4 : P2BlockCompatibleSchedule.blockNcut 4 = 79 := by decide
  have hN5 : P2BlockCompatibleSchedule.blockNcut 5 = 159 := by decide
  rw [hN4, hN5]
  exact blockK4CoefficientSandwichCell.transportWeights
    blockWeight_four_eqv_explicit blockWeight_five_eqv_explicit
    blockWeight_five_fourth_eqv_explicit

/-! ## 6. Second physical tail anchor (`k = 5`) -/

/-- Exact coarse weight `blockWeight 5 = 12287/12288`. -/
def blockK5CoarseWeight : Q' := Q'.mkPos 12287 12288 (by decide)

/-- Exact fine weight `blockWeight 6 = 49151/49152`. -/
def blockK5FineWeight : Q' := Q'.mkPos 49151 49152 (by decide)

/-- Cleared numerator of `(blockWeight 6)^4`. -/
def blockK5FourthNumerator : Nat := fastNatPow 49151 4

/-- Cleared denominator of `(blockWeight 6)^4`. -/
def blockK5FourthDenominator : Nat := fastNatPow 49152 4

/-- Exact fourth-power fine weight used at the common `k=5` cutoff. -/
def blockK5FourthWeight : Q' :=
  Q'.mkPos blockK5FourthNumerator blockK5FourthDenominator
    (fastNatPow_pos (by decide) 4)

/-- The same logarithmic common-denominator checker at the next physical
scale `k=5`, with cutoffs `N=159 -> 319`. -/
theorem blockK5ClearedCoefficientCheck :
    clearedCoefficientSandwichCheck
      12287 12288 159
      49151 49152 319
      blockK5FourthNumerator blockK5FourthDenominator 159
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 5)
      (by decide) (by decide) (fastNatPow_pos (by decide) 4) = true := by
  decide

/-- Kernel-checked coefficient-space sandwich at `k=5`. -/
def blockK5CoefficientSandwichCell :
    CoefficientSandwichCell
      blockK5CoarseWeight blockK5FineWeight blockK5FourthWeight
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 5)
      159 319 159 :=
  CoefficientSandwichCell.ofClearedCheck
    12287 12288 159
    49151 49152 319
    blockK5FourthNumerator blockK5FourthDenominator 159
    (P2BlockCompatibleThetaParityTransport.blockParityDebt 5)
    (by decide) (by decide) (fastNatPow_pos (by decide) 4)
    blockK5ClearedCoefficientCheck

theorem blockWeight_five_eqv_k5_explicit :
    P2BlockCompatibleSchedule.blockWeight 5 ≈ blockK5CoarseWeight := by
  decide

theorem blockWeight_six_eqv_explicit :
    P2BlockCompatibleSchedule.blockWeight 6 ≈ blockK5FineWeight := by
  decide

theorem blockWeight_six_fourth_eqv_explicit :
    qpow (P2BlockCompatibleSchedule.blockWeight 6) 4 ≈
      blockK5FourthWeight := by
  exact Q'.eqv_trans _ _ _
    (qpow_eqv_congr_local blockWeight_six_eqv_explicit 4)
    (qpow_mkPos_eqv_fast 49151 49152 4 (by decide))

/-- The checked `k=5` cell at the literal block-compatible schedule weights. -/
def blockK5PhysicalCoefficientSandwichCell :
    CoefficientSandwichCell
      (P2BlockCompatibleSchedule.blockWeight 5)
      (P2BlockCompatibleSchedule.blockWeight 6)
      (qpow (P2BlockCompatibleSchedule.blockWeight 6) 4)
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 5)
      (P2BlockCompatibleSchedule.blockNcut 5)
      (P2BlockCompatibleSchedule.blockNcut 6)
      (P2BlockCompatibleSchedule.blockNcut 5) := by
  have hN5 : P2BlockCompatibleSchedule.blockNcut 5 = 159 := by decide
  have hN6 : P2BlockCompatibleSchedule.blockNcut 6 = 319 := by decide
  rw [hN5, hN6]
  exact blockK5CoefficientSandwichCell.transportWeights
    blockWeight_five_eqv_k5_explicit blockWeight_six_eqv_explicit
    blockWeight_six_fourth_eqv_explicit

/-! ## 7. Compile coefficient cells back to the physical path energy -/

/-- Generic path-energy cell before specializing to the physical schedule. -/
structure ThetaPathEnergySandwichCell
    (coarseWeight fineWeight fourthWeight debt : Q')
    (coarseCut fineCut fourthCut : Nat) : Type where
  coarse :
    integerThetaSum coarseWeight coarseCut *
        P2BlockCompatibleThetaPathEnergy.thetaPathEnergy fourthWeight fourthCut <=
      P2BlockCompatibleThetaPathEnergy.thetaPathEnergy coarseWeight coarseCut *
          integerThetaSum fourthWeight fourthCut +
        Q'.ofNat 2 *
          (debt *
            (integerThetaSum coarseWeight coarseCut *
              integerThetaSum fourthWeight fourthCut))
  fine :
    Q'.ofNat 2 *
          (integerThetaSum fourthWeight fourthCut *
            P2BlockCompatibleThetaPathEnergy.thetaPathEnergy fineWeight fineCut) +
        Q'.ofNat 2 *
          (debt *
            (integerThetaSum fineWeight fineCut *
              integerThetaSum fourthWeight fourthCut)) <=
      integerThetaSum fineWeight fineCut *
        P2BlockCompatibleThetaPathEnergy.thetaPathEnergy fourthWeight fourthCut

private theorem integerThetaSum_eqv_scaledCoord (w : Q') (N : Nat) :
    integerThetaSum w N ≈ qpow w 2 * coordNormSq w N :=
  Q'.eqv_symm (HarmonicThetaRepresentation.coordNormSq_theta_eqv w N)

/-- The positive path energy is exactly twice the coefficient deficit with
the common `w^2` theta scale restored. -/
theorem thetaPathEnergy_eqv_scaledCoefficientDeficit (w : Q') (N : Nat) :
    P2BlockCompatibleThetaPathEnergy.thetaPathEnergy w N ≈
      qpow w 2 * (Q'.ofNat 2 * coefficientDeficit w N) := by
  have hdir := AllWindowCorrDirichlet.twice_norm_sub_corr_eq_boundary_dirichlet w N
  unfold P2BlockCompatibleThetaPathEnergy.thetaPathEnergy coefficientDeficit
  exact Q'.mul_eqv_congr_left (qpow w 2) _ _ (Q'.eqv_symm hdir)

private theorem qpow_two_nonneg_any (w : Q') :
    (0 : Q') <= qpow w 2 := by
  have heq : qpow w 2 ≈ w * w := by
    show ((1 : Q') * w) * w ≈ w * w
    exact Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)
  exact Q'.le_trans' _ _ _ (SumOfSquares.q_mul_self_nonneg w)
    (Q'.ge_of_eqv heq)

private theorem scaled_coarse_of_coefficient
    (scaleCoarse scaleFourth Dc Tc D4 T4 debt : Q')
    (hscaleCoarse : (0 : Q') <= scaleCoarse)
    (hscaleFourth : (0 : Q') <= scaleFourth)
    (h : Dc * T4 <= Tc * D4 + debt * (Dc * D4)) :
    (scaleCoarse * Dc) * (scaleFourth * (Q'.ofNat 2 * T4)) <=
      (scaleCoarse * (Q'.ofNat 2 * Tc)) * (scaleFourth * D4) +
        Q'.ofNat 2 *
          (debt * ((scaleCoarse * Dc) * (scaleFourth * D4))) := by
  let common := Q'.ofNat 2 * (scaleCoarse * scaleFourth)
  have hcommon : (0 : Q') <= common :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hscaleCoarse hscaleFourth)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ common h hcommon
  have hleft :
      (scaleCoarse * Dc) * (scaleFourth * (Q'.ofNat 2 * T4)) ≈
        common * (Dc * T4) := by
    dsimp only [common]
    cell_ring
  have hright :
      (scaleCoarse * (Q'.ofNat 2 * Tc)) * (scaleFourth * D4) +
          Q'.ofNat 2 *
            (debt * ((scaleCoarse * Dc) * (scaleFourth * D4))) ≈
        common * (Tc * D4 + debt * (Dc * D4)) := by
    dsimp only [common]
    cell_ring
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

private theorem scaled_fine_of_coefficient
    (scaleFine scaleFourth Df Tf D4 T4 debt : Q')
    (hscaleFine : (0 : Q') <= scaleFine)
    (hscaleFourth : (0 : Q') <= scaleFourth)
    (h : Q'.ofNat 2 * (D4 * Tf) + debt * (Df * D4) <= Df * T4) :
    Q'.ofNat 2 *
          ((scaleFourth * D4) * (scaleFine * (Q'.ofNat 2 * Tf))) +
        Q'.ofNat 2 *
          (debt * ((scaleFine * Df) * (scaleFourth * D4))) <=
      (scaleFine * Df) * (scaleFourth * (Q'.ofNat 2 * T4)) := by
  let common := Q'.ofNat 2 * (scaleFine * scaleFourth)
  have hcommon : (0 : Q') <= common :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hscaleFine hscaleFourth)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ common h hcommon
  have hleft :
      Q'.ofNat 2 *
            ((scaleFourth * D4) * (scaleFine * (Q'.ofNat 2 * Tf))) +
          Q'.ofNat 2 *
            (debt * ((scaleFine * Df) * (scaleFourth * D4))) ≈
        common * (Q'.ofNat 2 * (D4 * Tf) + debt * (Df * D4)) := by
    dsimp only [common]
    cell_ring
  have hright :
      (scaleFine * Df) * (scaleFourth * (Q'.ofNat 2 * T4)) ≈
        common * (Df * T4) := by
    dsimp only [common]
    cell_ring
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

/-- Restore the two positive theta scales canceled by the coefficient cell. -/
def CoefficientSandwichCell.toThetaPathEnergyCell
    {coarseWeight fineWeight fourthWeight debt : Q'}
    {coarseCut fineCut fourthCut : Nat}
    (C : CoefficientSandwichCell coarseWeight fineWeight fourthWeight
      debt coarseCut fineCut fourthCut) :
    ThetaPathEnergySandwichCell coarseWeight fineWeight fourthWeight
      debt coarseCut fineCut fourthCut := by
  let sc := qpow coarseWeight 2
  let sf := qpow fineWeight 2
  let s4 := qpow fourthWeight 2
  let Dc := coordNormSq coarseWeight coarseCut
  let Tc := coefficientDeficit coarseWeight coarseCut
  let Df := coordNormSq fineWeight fineCut
  let Tf := coefficientDeficit fineWeight fineCut
  let D4 := coordNormSq fourthWeight fourthCut
  let T4 := coefficientDeficit fourthWeight fourthCut
  have hIc : integerThetaSum coarseWeight coarseCut ≈ sc * Dc :=
    integerThetaSum_eqv_scaledCoord _ _
  have hIf : integerThetaSum fineWeight fineCut ≈ sf * Df :=
    integerThetaSum_eqv_scaledCoord _ _
  have hI4 : integerThetaSum fourthWeight fourthCut ≈ s4 * D4 :=
    integerThetaSum_eqv_scaledCoord _ _
  have hPc : P2BlockCompatibleThetaPathEnergy.thetaPathEnergy
      coarseWeight coarseCut ≈ sc * (Q'.ofNat 2 * Tc) :=
    thetaPathEnergy_eqv_scaledCoefficientDeficit _ _
  have hPf : P2BlockCompatibleThetaPathEnergy.thetaPathEnergy
      fineWeight fineCut ≈ sf * (Q'.ofNat 2 * Tf) :=
    thetaPathEnergy_eqv_scaledCoefficientDeficit _ _
  have hP4 : P2BlockCompatibleThetaPathEnergy.thetaPathEnergy
      fourthWeight fourthCut ≈ s4 * (Q'.ofNat 2 * T4) :=
    thetaPathEnergy_eqv_scaledCoefficientDeficit _ _
  refine ⟨?_, ?_⟩
  · have hscaled := scaled_coarse_of_coefficient sc s4 Dc Tc D4 T4 debt
      (qpow_two_nonneg_any coarseWeight)
      (qpow_two_nonneg_any fourthWeight) C.coarse
    have hleft :
        integerThetaSum coarseWeight coarseCut *
            P2BlockCompatibleThetaPathEnergy.thetaPathEnergy fourthWeight fourthCut ≈
          (sc * Dc) * (s4 * (Q'.ofNat 2 * T4)) :=
      mul_eqv_both hIc hP4
    have hright :
        P2BlockCompatibleThetaPathEnergy.thetaPathEnergy coarseWeight coarseCut *
              integerThetaSum fourthWeight fourthCut +
            Q'.ofNat 2 *
              (debt *
                (integerThetaSum coarseWeight coarseCut *
                  integerThetaSum fourthWeight fourthCut)) ≈
          (sc * (Q'.ofNat 2 * Tc)) * (s4 * D4) +
            Q'.ofNat 2 * (debt * ((sc * Dc) * (s4 * D4))) :=
      Q'.add_eqv_congr'
        (mul_eqv_both hPc hI4)
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (Q'.mul_eqv_congr_left debt _ _ (mul_eqv_both hIc hI4)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))
  · have hscaled := scaled_fine_of_coefficient sf s4 Df Tf D4 T4 debt
      (qpow_two_nonneg_any fineWeight)
      (qpow_two_nonneg_any fourthWeight) C.fine
    have hleft :
        Q'.ofNat 2 *
              (integerThetaSum fourthWeight fourthCut *
                P2BlockCompatibleThetaPathEnergy.thetaPathEnergy fineWeight fineCut) +
            Q'.ofNat 2 *
              (debt *
                (integerThetaSum fineWeight fineCut *
                  integerThetaSum fourthWeight fourthCut)) ≈
          Q'.ofNat 2 * ((s4 * D4) * (sf * (Q'.ofNat 2 * Tf))) +
            Q'.ofNat 2 * (debt * ((sf * Df) * (s4 * D4))) :=
      Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (mul_eqv_both hI4 hPf))
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (Q'.mul_eqv_congr_left debt _ _ (mul_eqv_both hIf hI4)))
    have hright :
        integerThetaSum fineWeight fineCut *
            P2BlockCompatibleThetaPathEnergy.thetaPathEnergy fourthWeight fourthCut ≈
          (sf * Df) * (s4 * (Q'.ofNat 2 * T4)) :=
      mul_eqv_both hIf hP4
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

/-- All-scale coefficient formulation of the remaining physical sandwich. -/
structure BlockCompatibleP2CoefficientSandwich : Type where
  cell : forall k, 4 <= k ->
    CoefficientSandwichCell
      (P2BlockCompatibleSchedule.blockWeight k)
      (P2BlockCompatibleSchedule.blockWeight (k + 1))
      (qpow (P2BlockCompatibleSchedule.blockWeight (k + 1)) 4)
      (P2BlockCompatibleThetaParityTransport.blockParityDebt k)
      (P2BlockCompatibleSchedule.blockNcut k)
      (P2BlockCompatibleSchedule.blockNcut (k + 1))
      (P2BlockCompatibleSchedule.blockNcut k)

/-- With the `k=4` cell now checked, the honest analytic tail begins at `k=5`. -/
structure BlockCompatibleP2CoefficientSandwichFromFive : Type where
  cell : forall k, 5 <= k ->
    CoefficientSandwichCell
      (P2BlockCompatibleSchedule.blockWeight k)
      (P2BlockCompatibleSchedule.blockWeight (k + 1))
      (qpow (P2BlockCompatibleSchedule.blockWeight (k + 1)) 4)
      (P2BlockCompatibleThetaParityTransport.blockParityDebt k)
      (P2BlockCompatibleSchedule.blockNcut k)
      (P2BlockCompatibleSchedule.blockNcut (k + 1))
      (P2BlockCompatibleSchedule.blockNcut k)

/-- With the `k=4` and `k=5` cells checked, the remaining analytic tail starts
at `k=6`. -/
structure BlockCompatibleP2CoefficientSandwichFromSix : Type where
  cell : forall k, 6 <= k ->
    CoefficientSandwichCell
      (P2BlockCompatibleSchedule.blockWeight k)
      (P2BlockCompatibleSchedule.blockWeight (k + 1))
      (qpow (P2BlockCompatibleSchedule.blockWeight (k + 1)) 4)
      (P2BlockCompatibleThetaParityTransport.blockParityDebt k)
      (P2BlockCompatibleSchedule.blockNcut k)
      (P2BlockCompatibleSchedule.blockNcut (k + 1))
      (P2BlockCompatibleSchedule.blockNcut k)

/-- Insert the checked `k=5` cell in front of a `k>=6` tail. -/
def BlockCompatibleP2CoefficientSandwichFromSix.toFromFive
    (T : BlockCompatibleP2CoefficientSandwichFromSix) :
    BlockCompatibleP2CoefficientSandwichFromFive where
  cell := fun k hk => by
    by_cases hk5 : k = 5
    · subst k
      exact blockK5PhysicalCoefficientSandwichCell
    · exact T.cell k (by omega)

/-- Prefix/tail compiler: the checked `k=4` anchor plus a `k>=5` coefficient
tail yields the complete coefficient sandwich. -/
def BlockCompatibleP2CoefficientSandwichFromFive.toAllScale
    (T : BlockCompatibleP2CoefficientSandwichFromFive) :
    BlockCompatibleP2CoefficientSandwich where
  cell := fun k hk => by
    by_cases hk4 : k = 4
    · subst k
      exact blockK4PhysicalCoefficientSandwichCell
    · exact T.cell k (by omega)

/-- The two checked anchors plus a `k>=6` tail yield the all-scale coefficient
sandwich. -/
def BlockCompatibleP2CoefficientSandwichFromSix.toAllScale
    (T : BlockCompatibleP2CoefficientSandwichFromSix) :
    BlockCompatibleP2CoefficientSandwich :=
  T.toFromFive.toAllScale

/-- The all-scale coefficient family compiles to the exact path-energy family
consumed by the genuine physical bridge. -/
def BlockCompatibleP2CoefficientSandwich.toThetaPathEnergySandwich
    (C : BlockCompatibleP2CoefficientSandwich) :
    P2BlockCompatibleThetaPathEnergy.BlockCompatibleP2ThetaPathEnergySandwich where
  coarseEnergyUpper := fun k hk =>
    (C.cell k hk).toThetaPathEnergyCell.coarse
  fineEnergyLower := fun k hk =>
    (C.cell k hk).toThetaPathEnergyCell.fine

/-- The first physical tail cell in the exact positive path-energy coordinate. -/
def blockK4PhysicalThetaPathEnergyCell :
    ThetaPathEnergySandwichCell
      (P2BlockCompatibleSchedule.blockWeight 4)
      (P2BlockCompatibleSchedule.blockWeight 5)
      (qpow (P2BlockCompatibleSchedule.blockWeight 5) 4)
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 4)
      (P2BlockCompatibleSchedule.blockNcut 4)
      (P2BlockCompatibleSchedule.blockNcut 5)
      (P2BlockCompatibleSchedule.blockNcut 4) :=
  blockK4PhysicalCoefficientSandwichCell.toThetaPathEnergyCell

/-- The second checked physical tail cell in the path-energy coordinate. -/
def blockK5PhysicalThetaPathEnergyCell :
    ThetaPathEnergySandwichCell
      (P2BlockCompatibleSchedule.blockWeight 5)
      (P2BlockCompatibleSchedule.blockWeight 6)
      (qpow (P2BlockCompatibleSchedule.blockWeight 6) 4)
      (P2BlockCompatibleThetaParityTransport.blockParityDebt 5)
      (P2BlockCompatibleSchedule.blockNcut 5)
      (P2BlockCompatibleSchedule.blockNcut 6)
      (P2BlockCompatibleSchedule.blockNcut 5) :=
  blockK5PhysicalCoefficientSandwichCell.toThetaPathEnergyCell

#print axioms fastNatPow_eq_pow
#print axioms fastNatPow_pos
#print axioms monomial_eqv_clearedMonomialQ
#print axioms finSum_monomials_eqv_cleared
#print axioms coordNormSq_eqv_clearedCoordQ
#print axioms adjCorr_eqv_clearedAdjQ
#print axioms CoefficientSandwichCell.ofClearedCheck
#print axioms blockK4ClearedCoefficientCheck
#print axioms blockK4CoefficientSandwichCell
#print axioms blockK4PhysicalCoefficientSandwichCell
#print axioms blockK5ClearedCoefficientCheck
#print axioms blockK5CoefficientSandwichCell
#print axioms blockK5PhysicalCoefficientSandwichCell
#print axioms thetaPathEnergy_eqv_scaledCoefficientDeficit
#print axioms CoefficientSandwichCell.toThetaPathEnergyCell
#print axioms BlockCompatibleP2CoefficientSandwichFromFive.toAllScale
#print axioms BlockCompatibleP2CoefficientSandwichFromSix.toAllScale
#print axioms BlockCompatibleP2CoefficientSandwich.toThetaPathEnergySandwich
#print axioms blockK4PhysicalThetaPathEnergyCell
#print axioms blockK5PhysicalThetaPathEnergyCell

end YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
