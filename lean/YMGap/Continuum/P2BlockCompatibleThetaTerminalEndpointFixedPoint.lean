/-
Track 11.7-fusion / R3r -- fixed-point compiler for the 640-entry endpoint table.

# Result

The literal table contains 640 powers with exponents as large as 3,276,800.
Evaluating those powers as unnormalised `Q'` expressions is the wrong
algorithm.  This module instead proves a generic soundness theorem for
downward-rounded, fixed-point square-and-multiply.

The scale

    S = 786432 * 10^12

represents `blockWeight 8 = 786431/786432` exactly.  Every fixed-point
multiplication rounds down, so the logarithmic evaluator is a certified lower
bound for the corresponding rational power.  All 640 lower bounds share the
same denominator `S`; the table is therefore accumulated as one natural
integer rather than as 640 mutually multiplied rational denominators.

The final exact integer comparison inhabits `TerminalEndpointFixedCertificate`
with the uniform power ceiling from the preceding module.

# Constructivity

Structural recursion with explicit fuel, natural floor division, exact
cross-multiplication, and kernel-checked closed arithmetic only.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointStep
open YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-! ## Fixed-point arithmetic and logarithmic exponentiation -/

def endpointFloorScale : Nat := 786432000000000000

def endpointFloorBase : Nat := 786431000000000000

theorem endpointFloorScale_pos : 0 < endpointFloorScale := by decide

def endpointFloorVal (n : Nat) : Q' :=
  Q'.mkPos n endpointFloorScale endpointFloorScale_pos

@[simp] theorem endpointFloorVal_num (n : Nat) :
    (endpointFloorVal n).num = (n : Int) := by
  unfold endpointFloorVal
  exact Q'.mkPos_num n endpointFloorScale endpointFloorScale_pos

@[simp] theorem endpointFloorVal_den (n : Nat) :
    (endpointFloorVal n).den = endpointFloorScale := by
  unfold endpointFloorVal
  exact Q'.mkPos_den n endpointFloorScale endpointFloorScale_pos

def endpointFloorMul (a b : Nat) : Nat :=
  (a * b) / endpointFloorScale

/-- Fuelled downward-rounded square-and-multiply. -/
def endpointFloorPowAux (base accumulator : Nat) : Nat -> Nat -> Nat
  | 0, _ => accumulator
  | fuel + 1, exponent =>
      if exponent = 0 then accumulator
      else
        endpointFloorPowAux (endpointFloorMul base base)
          (if exponent % 2 = 1 then endpointFloorMul accumulator base
            else accumulator)
          fuel (exponent / 2)

def endpointFloorPow (exponent : Nat) : Nat :=
  endpointFloorPowAux endpointFloorBase endpointFloorScale
    (exponent + 1) exponent

private theorem endpointFloorVal_nonneg (n : Nat) :
    (0 : Q') <= endpointFloorVal n := by
  show (0 : Q').num * ((endpointFloorVal n).den : Int) <=
    (endpointFloorVal n).num * ((0 : Q').den : Int)
  rw [endpointFloorVal_num, endpointFloorVal_den]
  simp only [show (0 : Q').num = 0 from rfl,
    show ((0 : Q').den : Int) = 1 from rfl,
    Int.zero_mul, Int.mul_one]
  exact Int.natCast_nonneg n

private theorem endpointFloorVal_scale_eqv_one :
    endpointFloorVal endpointFloorScale ≈ (1 : Q') := by
  show (endpointFloorVal endpointFloorScale).num * ((1 : Q').den : Int) =
    (1 : Q').num * ((endpointFloorVal endpointFloorScale).den : Int)
  rw [endpointFloorVal_num, endpointFloorVal_den]
  unfold endpointFloorScale
  decide

private theorem endpointFloorVal_base_eqv_weight :
    endpointFloorVal endpointFloorBase ≈ blockWeight 8 := by
  have hscaled : endpointFloorVal endpointFloorBase ≈
      Q'.mkPos 786431 786432 (by decide) := by
    show (endpointFloorVal endpointFloorBase).num *
        ((Q'.mkPos 786431 786432 (by decide)).den : Int) =
      (Q'.mkPos 786431 786432 (by decide)).num *
        ((endpointFloorVal endpointFloorBase).den : Int)
    rw [endpointFloorVal_num, endpointFloorVal_den,
      Q'.mkPos_num, Q'.mkPos_den]
    unfold endpointFloorBase endpointFloorScale
    decide
  have hweight : blockWeight 8 ≈
      Q'.mkPos 786431 786432 (by decide) := by
    unfold blockWeight blockMargin SpectralLocalizationCrux.q112 blockQuarter
    decide
  exact Q'.eqv_trans _ _ _ hscaled (Q'.eqv_symm hweight)

/-- One downward-rounded multiplication is below exact multiplication of the
two fixed-point values. -/
private theorem endpointFloorMul_sound (a b : Nat) :
    endpointFloorVal (endpointFloorMul a b) <=
      endpointFloorVal a * endpointFloorVal b := by
  have hdiv := Nat.div_mul_le_self (a * b) endpointFloorScale
  have hnat := Nat.mul_le_mul_right endpointFloorScale hdiv
  show (endpointFloorVal (endpointFloorMul a b)).num *
      ((endpointFloorVal a * endpointFloorVal b).den : Int) <=
    (endpointFloorVal a * endpointFloorVal b).num *
      ((endpointFloorVal (endpointFloorMul a b)).den : Int)
  simp only [endpointFloorVal_num, endpointFloorVal_den,
    Q'.mul_num_cast, Q'.mul_den_cast]
  unfold endpointFloorMul
  have hnat' : ((a * b) / endpointFloorScale) *
        (endpointFloorScale * endpointFloorScale) <=
      (a * b) * endpointFloorScale := by
    calc
      ((a * b) / endpointFloorScale) *
          (endpointFloorScale * endpointFloorScale) =
        (((a * b) / endpointFloorScale) * endpointFloorScale) *
          endpointFloorScale := by ac_rfl
      _ <= (a * b) * endpointFloorScale := hnat
  have hInt := Int.ofNat_le.mpr hnat'
  rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul] at hInt
  exact hInt

private theorem endpointFloorVal_add_eqv (a b : Nat) :
    endpointFloorVal (a + b) ≈
      endpointFloorVal a + endpointFloorVal b := by
  show (endpointFloorVal (a + b)).num *
      ((endpointFloorVal a + endpointFloorVal b).den : Int) =
    (endpointFloorVal a + endpointFloorVal b).num *
      ((endpointFloorVal (a + b)).den : Int)
  simp only [endpointFloorVal_num, endpointFloorVal_den,
    Q'.add_num_cast, Q'.add_den_cast,
    Int.natCast_add]
  rw [Int.add_mul, Int.add_mul]
  ac_rfl

private theorem endpointFloorVal_natMul_eqv (a b : Nat) :
    endpointFloorVal (a * b) ≈
      Q'.ofNat a * endpointFloorVal b := by
  show (endpointFloorVal (a * b)).num *
      ((Q'.ofNat a * endpointFloorVal b).den : Int) =
    (Q'.ofNat a * endpointFloorVal b).num *
      ((endpointFloorVal (a * b)).den : Int)
  simp only [endpointFloorVal_num, endpointFloorVal_den,
    Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.natCast_mul, Int.one_mul]

private theorem qpow_one_eqv (x : Q') : qpow x 1 ≈ x := by
  change (1 : Q') * x ≈ x
  exact Q'.one_mul_eqv x

private theorem qpow_binary_split (x : Q') (exponent : Nat) :
    qpow x exponent ≈
      qpow x (exponent % 2) *
        qpow (x * x) (exponent / 2) := by
  have hsplit : exponent % 2 + 2 * (exponent / 2) = exponent :=
    Nat.mod_add_div exponent 2
  have hdouble :
      qpow x (2 * (exponent / 2)) ≈
        qpow (x * x) (exponent / 2) := by
    have hadd := HeatKernelRGStep.qpow_add x
      (exponent / 2) (exponent / 2)
    have hsquare := FusionQuotientCollapse.qpow_mul_self x (exponent / 2)
    have htwo : 2 * (exponent / 2) =
        exponent / 2 + exponent / 2 := by omega
    rw [htwo]
    exact Q'.eqv_trans _ _ _ hadd (Q'.eqv_symm hsquare)
  have hfirst : qpow x exponent ≈
      qpow x (exponent % 2 + 2 * (exponent / 2)) := by
    rw [hsplit]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hfirst
    (Q'.eqv_trans _ _ _
      (HeatKernelRGStep.qpow_add x (exponent % 2)
        (2 * (exponent / 2)))
      (Q'.mul_eqv_congr_left _ _ _ hdouble))

private theorem endpointFloorPowAux_sound
    (base accumulator fuel exponent : Nat)
    (x y : Q')
    (hx0 : (0 : Q') <= x) (hy0 : (0 : Q') <= y)
    (hbase : endpointFloorVal base <= x)
    (hacc : endpointFloorVal accumulator <= y)
    (hexponent : exponent < fuel) :
    endpointFloorVal
        (endpointFloorPowAux base accumulator fuel exponent) <=
      y * qpow x exponent := by
  induction fuel generalizing base accumulator exponent x y with
  | zero => omega
  | succ fuel ih =>
      rw [endpointFloorPowAux]
      by_cases hzero : exponent = 0
      · subst exponent
        rw [if_pos rfl]
        have hright : y ≈ y * qpow x 0 := by
          change y ≈ y * (1 : Q')
          exact Q'.eqv_symm (Q'.mul_one_eqv y)
        exact Q'.le_trans' _ _ _ hacc (Q'.le_of_eqv hright)
      · rw [if_neg hzero]
        have hpos : 0 < exponent := Nat.pos_of_ne_zero hzero
        have hdivfuel : exponent / 2 < fuel := by
          have hdivlt := Nat.div_lt_self hpos (by decide : 1 < 2)
          omega
        let base' := endpointFloorMul base base
        have hbaseFloor := endpointFloorMul_sound base base
        have hbaseMul := Q'.mul_le_mul_of_nonneg hbase hbase hx0
          (endpointFloorVal_nonneg base)
        have hbase' : endpointFloorVal base' <= x * x :=
          Q'.le_trans' _ _ _ hbaseFloor hbaseMul
        have hxx0 : (0 : Q') <= x * x := Q'.mul_nonneg _ _ hx0 hx0
        by_cases hodd : exponent % 2 = 1
        · rw [if_pos hodd]
          let accumulator' := endpointFloorMul accumulator base
          have haccFloor := endpointFloorMul_sound accumulator base
          have haccMul := Q'.mul_le_mul_of_nonneg hacc hbase hy0
            (endpointFloorVal_nonneg base)
          have hacc' : endpointFloorVal accumulator' <= y * x :=
            Q'.le_trans' _ _ _ haccFloor haccMul
          have hyx0 : (0 : Q') <= y * x := Q'.mul_nonneg _ _ hy0 hx0
          have hrec := ih base' accumulator' (exponent / 2)
            (x * x) (y * x) hxx0 hyx0 hbase' hacc' hdivfuel
          have hsplit := qpow_binary_split x exponent
          rw [hodd] at hsplit
          have hone := qpow_one_eqv x
          have hpow : qpow x exponent ≈
              x * qpow (x * x) (exponent / 2) :=
            Q'.eqv_trans _ _ _ hsplit
              (Q'.mul_eqv_congr_right _ _ _ hone)
          have hright :
              (y * x) * qpow (x * x) (exponent / 2) ≈
                y * qpow x exponent := by
            refine Q'.eqv_trans _
              (y * (x * qpow (x * x) (exponent / 2))) _
              (Q'.mul_assoc_eqv y x _) ?_
            exact Q'.mul_eqv_congr_left y _ _ (Q'.eqv_symm hpow)
          exact Q'.le_trans' _ _ _ hrec (Q'.le_of_eqv hright)
        · rw [if_neg hodd]
          have heven : exponent % 2 = 0 := by
            have hmod := Nat.mod_lt exponent (by decide : 0 < 2)
            omega
          have hrec := ih base' accumulator (exponent / 2)
            (x * x) y hxx0 hy0 hbase' hacc hdivfuel
          have hsplit := qpow_binary_split x exponent
          rw [heven] at hsplit
          have hpow : qpow x exponent ≈
              qpow (x * x) (exponent / 2) :=
            Q'.eqv_trans _ _ _ hsplit
              (Q'.one_mul_eqv _)
          exact Q'.le_trans' _ _ _ hrec
            (Q'.le_of_eqv
              (Q'.mul_eqv_congr_left y _ _ (Q'.eqv_symm hpow)))

/-- Public soundness theorem: the fixed-point evaluator is a lower bound for
the literal physical base power, for every exponent. -/
theorem endpointFloorPow_le_physical (exponent : Nat) :
    endpointFloorVal (endpointFloorPow exponent) <=
      qpow (blockWeight 8) exponent := by
  have h := endpointFloorPowAux_sound
    endpointFloorBase endpointFloorScale (exponent + 1) exponent
    (blockWeight 8) (1 : Q')
    (blockWeight_nonneg 8) (by decide)
    (Q'.le_of_eqv endpointFloorVal_base_eqv_weight)
    (Q'.le_of_eqv endpointFloorVal_scale_eqv_one)
    (by omega)
  have hcollapse : (1 : Q') * qpow (blockWeight 8) exponent ≈
      qpow (blockWeight 8) exponent := Q'.one_mul_eqv _
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hcollapse)

/-! ## One common-denominator lower table -/

def endpointFloorTableNum : Nat -> Nat
  | 0 => 0
  | b + 1 => endpointFloorTableNum b +
      endpointShellCubic b * endpointFloorPow (8 * ((b + 1) * (b + 1)))

def endpointFloorTableWitnessNum : Nat :=
  30839543747440921431163816

def endpointFloorWeightWitnessNum : Nat :=
  786428000007629386

/-- The generated 640-entry recurrence certificate.  Keeping this equality
separate ensures that later rational comparisons consume the compact witness
rather than replaying all 640 fixed-point powers. -/
theorem endpointFloorTableNum_640_eq :
    endpointFloorTableNum 640 = endpointFloorTableWitnessNum := by
  decide

/-- The fixed-point fourth power used by the endpoint weight. -/
theorem endpointFloorPow_four_eq :
    endpointFloorPow 4 = endpointFloorWeightWitnessNum := by
  decide

def endpointFloorTable : Q' := endpointFloorVal endpointFloorTableWitnessNum

def endpointFloorWeight : Q' := endpointFloorVal endpointFloorWeightWitnessNum

private theorem endpointFloorTerm_le (b : Nat) :
    endpointFloorVal
        (endpointShellCubic b *
          endpointFloorPow (8 * ((b + 1) * (b + 1)))) <=
      Q'.ofNat (endpointShellCubic b) * physicalEndpointPower 7 b := by
  have hp := endpointFloorPow_le_physical
    (8 * ((b + 1) * (b + 1)))
  have hc0 : (0 : Q') <= Q'.ofNat (endpointShellCubic b) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (endpointShellCubic b)) hp hc0
  have hleft := endpointFloorVal_natMul_eqv
    (endpointShellCubic b)
    (endpointFloorPow (8 * ((b + 1) * (b + 1))))
  have hright :
      qpow (blockWeight 8) (8 * ((b + 1) * (b + 1))) ≈
        physicalEndpointPower 7 b := by
    unfold physicalEndpointPower
    change qpow (blockWeight 8) (8 * ((b + 1) * (b + 1))) ≈
      qpow (blockWeight 8)
        (8 * (((b + 1) * 1) * ((b + 1) * 1)))
    rw [Nat.mul_one]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hright)))

theorem endpointFloorTable_le_fixed : endpointFloorTable <= fixedEndpointTable := by
  unfold endpointFloorTable fixedEndpointTable
  rw [← endpointFloorTableNum_640_eq]
  have h : forall n : Nat,
      endpointFloorVal (endpointFloorTableNum n) <=
        fsum (fun b => Q'.ofNat (endpointShellCubic b) *
          physicalEndpointPower 7 b) n := by
    intro n
    induction n with
    | zero =>
        change endpointFloorVal 0 <= 0
        exact Q'.le_of_eqv (by
          unfold endpointFloorVal endpointFloorScale
          decide)
    | succ n ih =>
        rw [endpointFloorTableNum, fsum_succ]
        have hsum := Q'.add_le_add ih (endpointFloorTerm_le n)
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (endpointFloorVal_add_eqv _ _)) hsum
  exact h 640

theorem endpointFloorWeight_le_fixed :
    endpointFloorWeight <= fixedEndpointWeight := by
  unfold endpointFloorWeight fixedEndpointWeight
  rw [← endpointFloorPow_four_eq]
  exact endpointFloorPow_le_physical 4

theorem endpointFloorTable_nonneg : (0 : Q') <= endpointFloorTable :=
  endpointFloorVal_nonneg _

theorem endpointFloorWeight_nonneg : (0 : Q') <= endpointFloorWeight :=
  endpointFloorVal_nonneg _

/-! ## Closed integer check and terminal certificate -/

/-- The complete finite check.  Its evaluator performs about twenty rounded
multiplications per endpoint and then one small cross multiplication. -/
theorem terminalEndpointFloorCheck :
    Q'.ofNat (640 * 640 * 640) * terminalEndpointPowerRationalCeil <=
      terminalEndpointTableCoeff *
        (endpointFloorWeight * endpointFloorTable) := by
  decide

theorem terminalEndpointFixedTable :
    Q'.ofNat (640 * 640 * 640) * terminalEndpointPowerCeil <=
      terminalEndpointTableCoeff *
        (fixedEndpointWeight * fixedEndpointTable) := by
  have hK0 : (0 : Q') <= Q'.ofNat (640 * 640 * 640) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hceil := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (640 * 640 * 640))
    terminalEndpointPowerCeil_le_rational hK0
  have hfixedWeight0 : (0 : Q') <= fixedEndpointWeight := by
    unfold fixedEndpointWeight
    exact qpow_nonneg _ (blockWeight_nonneg 8) _
  have hweightTable := Q'.mul_le_mul_of_nonneg
    endpointFloorWeight_le_fixed endpointFloorTable_le_fixed
    hfixedWeight0 endpointFloorTable_nonneg
  have hc0 : (0 : Q') <= terminalEndpointTableCoeff := by
    unfold terminalEndpointTableCoeff
    decide
  have hright := Q'.mul_le_mul_of_nonneg_left _ _
    terminalEndpointTableCoeff hweightTable hc0
  exact Q'.le_trans' _ _ _ hceil
    (Q'.le_trans' _ _ _ terminalEndpointFloorCheck hright)

/-- The previously open terminal endpoint certificate, now fully inhabited. -/
opaque terminalEndpointFixedCertificate : TerminalEndpointFixedCertificate :=
  { powerCeil := terminalEndpointPowerCeil
    powerCeil_nonneg := terminalEndpointPowerCeil_nonneg
    endpointPower_le := physicalTerminalEndpointPower_le
    fixedTable := terminalEndpointFixedTable }

def terminalTheta_fromSeven :=
  terminalEndpointFixedCertificate.terminalTheta

end YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint

#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint.endpointFloorPow_le_physical
#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint.endpointFloorTable_le_fixed
#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint.terminalEndpointFloorCheck
#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint.terminalEndpointFixedTable
#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointFixedPoint.terminalTheta_fromSeven
