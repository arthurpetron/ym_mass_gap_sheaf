/-
# The residual of a coercive positive contraction

For the same rational positive form, eta I <= P <= I makes I-P a
positive symmetric contraction of rate 1-eta. Its actual image norms and
natural iterates obey the squared geometric rate. Only the displayed
form bounds and symmetry are used; no spectral theorem, pointwise order,
linearity hypothesis on P, or inverse is assumed or constructed here.
-/

import YMGap.Continuum.PositiveContractionOneStepForm
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.PositiveContractionResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

/-- The actual carrier difference, using the original vector operations. -/
def residual (D : GNSData) (P : D.V → D.V) (a : D.V) : D.V :=
  D.sub a (P a)

/-- The form contraction rate retains the supplied coercivity floor. -/
def rate (eta : Q') : Q' := 1 + -eta

theorem rate_nonnegative {eta : Q'} (heta1 : eta ≤ (1 : Q')) :
    (0 : Q') ≤ rate eta :=
  Q'.sub_nonneg_of_le heta1

theorem rate_lt_one {eta : Q'} (heta0 : (0 : Q') < eta) :
    rate eta < (1 : Q') := by
  have hnum := (zero_lt_iff_num_pos eta).mp heta0
  change ((1 : Q') + -eta).num * (1 : Int) <
    (1 : Int) * (((1 : Q') + -eta).den : Int)
  rw [Q'.add_den_cast]
  change ((1 : Int) * (eta.den : Int) + (-eta.num) * 1) * 1 <
    (1 : Int) * (1 * (eta.den : Int))
  simp only [Int.one_mul, Int.mul_one]
  omega

/-- Exact pairing with the unchanged residual vector. -/
theorem residual_pairing (D : GNSData) (P : D.V → D.V) (a b : D.V) :
    D.B a (residual D P b) ≈ D.B a b + -(D.B a (P b)) :=
  Q'.eqv_trans _ _ _ (D.B_add_right a b (D.neg (P b)))
    (Q'.add_eqv_congr_left _ _ _ (D.B_neg_right a (P b)))

theorem residual_symmetric (D : GNSData) (P : D.V → D.V)
    (hsa : ∀ a b, D.B a (P b) ≈ D.B (P a) b) (a b : D.V) :
    D.B a (residual D P b) ≈ D.B (residual D P a) b := by
  have hleft : D.B (residual D P a) b ≈ D.B a b + -(D.B (P a) b) :=
    Q'.eqv_trans _ _ _ (D.B_add_left a (D.neg (P a)) b)
      (Q'.add_eqv_congr_left _ _ _ (D.B_neg_left (P a) b))
  exact Q'.eqv_trans _ _ _ (residual_pairing D P a b)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (hsa a b)))
      (Q'.eqv_symm hleft))

theorem residual_nonnegative (D : GNSData) (P : D.V → D.V)
    (hupper : ∀ a, D.B a (P a) ≤ D.B a a) (a : D.V) :
    (0 : Q') ≤ D.B a (residual D P a) :=
  Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le (hupper a))
    (Q'.ge_of_eqv (residual_pairing D P a a))

private theorem rate_mul (eta v : Q') : rate eta * v ≈ v + -(eta * v) :=
  Q'.eqv_trans _ _ _ (QPoly.q_add_mul 1 (-eta) v)
    (Q'.add_eqv_congr' (Q'.one_mul_eqv v) (Q'.neg_mul_eqv eta v))

theorem residual_upper (D : GNSData) (P : D.V → D.V) {eta : Q'}
    (hlower : ∀ a, eta * D.B a a ≤ D.B a (P a)) (a : D.V) :
    D.B a (residual D P a) ≤ rate eta * D.B a a :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (residual_pairing D P a a))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg (hlower a)))
      (Q'.ge_of_eqv (rate_mul eta (D.B a a))))

/-- The coercive form interval controls the norm of the actual residual,
not merely its diagonal pairing with the input. -/
theorem residual_norm (D : GNSData) (P : D.V → D.V)
    (hsa : ∀ a b, D.B a (P b) ≈ D.B (P a) b) {eta : Q'}
    (heta1 : eta ≤ (1 : Q'))
    (hupper : ∀ a, D.B a (P a) ≤ D.B a a)
    (hlower : ∀ a, eta * D.B a a ≤ D.B a (P a)) (a : D.V) :
    D.B (residual D P a) (residual D P a) ≤
      (rate eta * rate eta) * D.B a a :=
  PositiveContractionOneStepForm.norm_bound D (residual D P)
    (residual_symmetric D P hsa) (residual_nonnegative D P hupper)
    (rate_nonnegative heta1) (residual_upper D P hlower) a

/-- Explicit natural iterates of the same residual map. -/
def residualIterate (D : GNSData) (P : D.V → D.V) : Nat → D.V → D.V
  | 0, a => a
  | n + 1, a => residual D P (residualIterate D P n a)

theorem residualIterate_norm (D : GNSData) (P : D.V → D.V)
    (hsa : ∀ a b, D.B a (P b) ≈ D.B (P a) b) {eta : Q'}
    (heta1 : eta ≤ (1 : Q'))
    (hupper : ∀ a, D.B a (P a) ≤ D.B a a)
    (hlower : ∀ a, eta * D.B a a ≤ D.B a (P a)) (a : D.V) :
    ∀ n, D.B (residualIterate D P n a) (residualIterate D P n a) ≤
      (rate eta * rate eta)^n * D.B a a
  | 0 => Q'.ge_of_eqv (Q'.one_mul_eqv (D.B a a))
  | n + 1 => Q'.le_trans' _ _ _
      (residual_norm D P hsa heta1 hupper hlower (residualIterate D P n a))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (residualIterate_norm D P hsa heta1 hupper hlower a n)
          (Q'.mul_nonneg _ _ (rate_nonnegative heta1) (rate_nonnegative heta1)))
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv (rate eta * rate eta)
          ((rate eta * rate eta)^n) (D.B a a))))

/-- Explicit tolerance cutoff for a geometric norm bound. The zero-rate
branch starts at one, and the rescaling never divides by the possibly zero
initial norm C. -/
def geometricCutoff (q C epsilon : Q') : Nat :=
  if (0 : Q') < q then
    HKConvGen.powBaseCutoff q (HKConv.divPos epsilon (1 + C))
  else 1

/-- Every later iterate satisfies the requested rational tolerance,
including zero contraction rate and zero initial squared norm. -/
theorem geometric_bound {q C epsilon : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : geometricCutoff q C epsilon ≤ n) :
    q^n * C ≤ epsilon := by
  by_cases hqpos : (0 : Q') < q
  · simp only [geometricCutoff, if_pos hqpos] at hn
    have hden : (0 : Q') < 1 + C :=
      Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
        (Q'.add_le_self_of_nonneg 1 C hC)
    have ht : (0 : Q') < HKConv.divPos epsilon (1 + C) :=
      HKConv.divPos_pos ((zero_lt_iff_num_pos epsilon).mp hepsilon)
    have hp : q^n ≤ HKConv.divPos epsilon (1 + C) :=
      Q'.le_trans' _ _ _
        (HKConvGen.pow_base_antitone hq0 (Q'.le_of_lt hq1) hn)
        (HKConvGen.pow_base_le_cutoff hqpos hq1 ht)
    have hC1 : C ≤ 1 + C :=
      Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg C 1 Q'.zero_le_one)
        (Q'.le_of_eqv (Q'.add_comm_eqv C 1))
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ C hp hC)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hC1 (Q'.le_of_lt ht))
        (Q'.le_of_eqv (HKConv.divPos_mul_eqv ((zero_lt_iff_num_pos (1 + C)).mp hden))))
  · simp only [geometricCutoff, if_neg hqpos] at hn
    have hnum : q.num ≤ (0 : Int) :=
      Int.not_lt.mp (fun h => hqpos ((zero_lt_iff_num_pos q).mpr h))
    have hqle0 : q ≤ (0 : Q') := by
      change q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
      simpa only [Int.mul_one, Int.zero_mul] using hnum
    have hp : q^n ≤ (0 : Q') :=
      Q'.le_trans' _ _ _
        (HKConvGen.pow_base_antitone hq0 (Q'.le_of_lt hq1) hn)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv q)) hqle0)
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ C hp hC)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv C)) (Q'.le_of_lt hepsilon))

end YMGap.Continuum.PositiveContractionResidual

#print axioms YMGap.Continuum.PositiveContractionResidual.residual
#print axioms YMGap.Continuum.PositiveContractionResidual.rate
#print axioms YMGap.Continuum.PositiveContractionResidual.rate_nonnegative
#print axioms YMGap.Continuum.PositiveContractionResidual.rate_lt_one
#print axioms YMGap.Continuum.PositiveContractionResidual.residual_pairing
#print axioms YMGap.Continuum.PositiveContractionResidual.residual_symmetric
#print axioms YMGap.Continuum.PositiveContractionResidual.residual_nonnegative
#print axioms YMGap.Continuum.PositiveContractionResidual.residual_upper
#print axioms YMGap.Continuum.PositiveContractionResidual.residual_norm
#print axioms YMGap.Continuum.PositiveContractionResidual.residualIterate
#print axioms YMGap.Continuum.PositiveContractionResidual.residualIterate_norm
#print axioms YMGap.Continuum.PositiveContractionResidual.geometricCutoff
#print axioms YMGap.Continuum.PositiveContractionResidual.geometric_bound
