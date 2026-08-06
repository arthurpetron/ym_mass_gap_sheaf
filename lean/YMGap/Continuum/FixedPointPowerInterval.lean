/-
Track 11.7-fusion / R3t -- generic binary fixed-point power intervals.

# Result

Large theta certificates need both lower and upper rational power tables.
Literal evaluation of `q^e` has linear proof cost in `e` and creates enormous
unnormalised numerators and denominators.  This module proves, once and for
all, that binary square-and-multiply with floor multiplication lies below the
exact power and the same algorithm with ceiling multiplication lies above it.

Both evaluators take `O(log e)` recursive steps.  The scale and represented
base are parameters, so the same proof serves the `k=7` radial base, the
`k=8` dyadic lower table, and the uniform reciprocal-Bernoulli upper base.

# Constructivity

Structural recursion with explicit fuel, Euclidean division with remainder,
exact cross multiplication, and the already-proved binary power split.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialMoment

namespace YMGap.Continuum.FixedPointPowerInterval

set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- A common-denominator fixed-point value `numerator / scale`. -/
def fixedPointVal (scale : Nat) (hScale : 0 < scale) (numerator : Nat) : Q' :=
  Q'.mkPos numerator scale hScale

@[simp] theorem fixedPointVal_num
    (scale : Nat) (hScale : 0 < scale) (numerator : Nat) :
    (fixedPointVal scale hScale numerator).num = (numerator : Int) := by
  unfold fixedPointVal
  exact Q'.mkPos_num numerator scale hScale

@[simp] theorem fixedPointVal_den
    (scale : Nat) (hScale : 0 < scale) (numerator : Nat) :
    (fixedPointVal scale hScale numerator).den = scale := by
  unfold fixedPointVal
  exact Q'.mkPos_den numerator scale hScale

theorem fixedPointVal_nonneg
    (scale : Nat) (hScale : 0 < scale) (numerator : Nat) :
    (0 : Q') <= fixedPointVal scale hScale numerator := by
  show (0 : Q').num *
      ((fixedPointVal scale hScale numerator).den : Int) <=
    (fixedPointVal scale hScale numerator).num * ((0 : Q').den : Int)
  rw [fixedPointVal_num, fixedPointVal_den]
  simp only [show (0 : Q').num = 0 from rfl,
    show ((0 : Q').den : Int) = 1 from rfl,
    Int.zero_mul, Int.mul_one]
  exact Int.natCast_nonneg numerator

theorem fixedPointVal_scale_eqv_one
    (scale : Nat) (hScale : 0 < scale) :
    fixedPointVal scale hScale scale ≈ (1 : Q') := by
  show (fixedPointVal scale hScale scale).num * ((1 : Q').den : Int) =
    (1 : Q').num * ((fixedPointVal scale hScale scale).den : Int)
  rw [fixedPointVal_num, fixedPointVal_den]
  simp only [show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.mul_one, Int.one_mul]

/-- Fixed-point addition is exact when the denominator is shared. -/
theorem fixedPointVal_add_eqv
    (scale : Nat) (hScale : 0 < scale) (a b : Nat) :
    fixedPointVal scale hScale (a + b) ≈
      fixedPointVal scale hScale a + fixedPointVal scale hScale b := by
  show (fixedPointVal scale hScale (a + b)).num *
      ((fixedPointVal scale hScale a +
        fixedPointVal scale hScale b).den : Int) =
    (fixedPointVal scale hScale a +
      fixedPointVal scale hScale b).num *
        ((fixedPointVal scale hScale (a + b)).den : Int)
  simp only [fixedPointVal_num, fixedPointVal_den,
    Q'.add_num_cast, Q'.add_den_cast, Int.natCast_add]
  rw [Int.add_mul, Int.add_mul]
  ac_rfl

/-- Multiplication of a fixed-point numerator by a natural is exact. -/
theorem fixedPointVal_natMul_eqv
    (scale : Nat) (hScale : 0 < scale) (a b : Nat) :
    fixedPointVal scale hScale (a * b) ≈
      Q'.ofNat a * fixedPointVal scale hScale b := by
  show (fixedPointVal scale hScale (a * b)).num *
      ((Q'.ofNat a * fixedPointVal scale hScale b).den : Int) =
    (Q'.ofNat a * fixedPointVal scale hScale b).num *
      ((fixedPointVal scale hScale (a * b)).den : Int)
  simp only [fixedPointVal_num, fixedPointVal_den,
    Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.natCast_mul, Int.one_mul]

/-- Downward-rounded fixed-point multiplication. -/
def floorMul (scale a b : Nat) : Nat := (a * b) / scale

/-- Natural ceiling division, expressed through quotient and remainder. -/
def ceilDiv (value scale : Nat) : Nat :=
  value / scale + if value % scale = 0 then 0 else 1

/-- Upward-rounded fixed-point multiplication. -/
def ceilMul (scale a b : Nat) : Nat := ceilDiv (a * b) scale

private theorem value_le_ceilDiv_mul
    (value scale : Nat) (hScale : 0 < scale) :
    value <= ceilDiv value scale * scale := by
  have hsplit := Nat.mod_add_div value scale
  by_cases hrem : value % scale = 0
  · have hv : value = (value / scale) * scale := by
      rw [hrem, Nat.zero_add] at hsplit
      rw [Nat.mul_comm]
      exact hsplit.symm
    unfold ceilDiv
    rw [if_pos hrem, Nat.add_zero]
    exact Nat.le_of_eq hv
  · have hlt := Nat.mod_lt value hScale
    have hv : value = value % scale + scale * (value / scale) :=
      hsplit.symm
    unfold ceilDiv
    rw [if_neg hrem]
    calc
      value = value % scale + scale * (value / scale) := hv
      _ <=
          scale + scale * (value / scale) :=
        Nat.add_le_add_right (Nat.le_of_lt hlt) _
      _ = (value / scale + 1) * scale := by
        rw [Nat.add_mul, Nat.one_mul]
        ac_rfl

/-- One floor multiplication is below the exact product. -/
theorem floorMul_sound
    (scale : Nat) (hScale : 0 < scale) (a b : Nat) :
    fixedPointVal scale hScale (floorMul scale a b) <=
      fixedPointVal scale hScale a * fixedPointVal scale hScale b := by
  have hdiv := Nat.div_mul_le_self (a * b) scale
  have hnat := Nat.mul_le_mul_right scale hdiv
  show (fixedPointVal scale hScale (floorMul scale a b)).num *
      ((fixedPointVal scale hScale a * fixedPointVal scale hScale b).den : Int) <=
    (fixedPointVal scale hScale a * fixedPointVal scale hScale b).num *
      ((fixedPointVal scale hScale (floorMul scale a b)).den : Int)
  simp only [fixedPointVal_num, fixedPointVal_den,
    Q'.mul_num_cast, Q'.mul_den_cast]
  unfold floorMul
  have hnat' : ((a * b) / scale) * (scale * scale) <=
      (a * b) * scale := by
    calc
      ((a * b) / scale) * (scale * scale) =
          (((a * b) / scale) * scale) * scale := by ac_rfl
      _ <= (a * b) * scale := hnat
  have hInt := Int.ofNat_le.mpr hnat'
  simpa only [Int.natCast_mul] using hInt

/-- The exact product is below one ceiling multiplication. -/
theorem ceilMul_sound
    (scale : Nat) (hScale : 0 < scale) (a b : Nat) :
    fixedPointVal scale hScale a * fixedPointVal scale hScale b <=
      fixedPointVal scale hScale (ceilMul scale a b) := by
  have hceil := value_le_ceilDiv_mul (a * b) scale hScale
  have hnat := Nat.mul_le_mul_right scale hceil
  show (fixedPointVal scale hScale a * fixedPointVal scale hScale b).num *
      ((fixedPointVal scale hScale (ceilMul scale a b)).den : Int) <=
    (fixedPointVal scale hScale (ceilMul scale a b)).num *
      ((fixedPointVal scale hScale a * fixedPointVal scale hScale b).den : Int)
  simp only [fixedPointVal_num, fixedPointVal_den,
    Q'.mul_num_cast, Q'.mul_den_cast]
  unfold ceilMul
  have hnat' : (a * b) * scale <=
      ceilDiv (a * b) scale * (scale * scale) := by
    calc
      (a * b) * scale <= (ceilDiv (a * b) scale * scale) * scale := hnat
      _ = ceilDiv (a * b) scale * (scale * scale) := by ac_rfl
  have hInt := Int.ofNat_le.mpr hnat'
  simpa only [Int.natCast_mul] using hInt

/-- Fuelled binary exponentiation using a supplied rounded multiplication. -/
def roundedPowAux (mul : Nat -> Nat -> Nat)
    (base accumulator : Nat) : Nat -> Nat -> Nat
  | 0, _ => accumulator
  | fuel + 1, exponent =>
      if exponent = 0 then accumulator
      else
        roundedPowAux mul (mul base base)
          (if exponent % 2 = 1 then mul accumulator base else accumulator)
          fuel (exponent / 2)

def floorPow (scale base exponent : Nat) : Nat :=
  roundedPowAux (floorMul scale) base scale (exponent + 1) exponent

def ceilPow (scale base exponent : Nat) : Nat :=
  roundedPowAux (ceilMul scale) base scale (exponent + 1) exponent

private theorem qpow_one_eqv (x : Q') : qpow x 1 ≈ x := by
  change (1 : Q') * x ≈ x
  exact Q'.one_mul_eqv x

/-- Binary split used by both interval directions. -/
theorem qpow_binary_split (x : Q') (exponent : Nat) :
    qpow x exponent ≈
      qpow x (exponent % 2) * qpow (x * x) (exponent / 2) := by
  have hsplit : exponent % 2 + 2 * (exponent / 2) = exponent :=
    Nat.mod_add_div exponent 2
  have hdouble : qpow x (2 * (exponent / 2)) ≈
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

private theorem floorPowAux_sound
    (scale : Nat) (hScale : 0 < scale)
    (base accumulator fuel exponent : Nat)
    (x y : Q')
    (hx0 : (0 : Q') <= x) (hy0 : (0 : Q') <= y)
    (hbase : fixedPointVal scale hScale base <= x)
    (hacc : fixedPointVal scale hScale accumulator <= y)
    (hexponent : exponent < fuel) :
    fixedPointVal scale hScale
        (roundedPowAux (floorMul scale) base accumulator fuel exponent) <=
      y * qpow x exponent := by
  induction fuel generalizing base accumulator exponent x y with
  | zero => omega
  | succ fuel ih =>
      rw [roundedPowAux]
      by_cases hzero : exponent = 0
      · subst exponent
        rw [if_pos rfl]
        exact Q'.le_trans' _ _ _ hacc
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv y)))
      · rw [if_neg hzero]
        have hpos : 0 < exponent := Nat.pos_of_ne_zero hzero
        have hdivfuel : exponent / 2 < fuel := by
          have hdivlt := Nat.div_lt_self hpos (by decide : 1 < 2)
          omega
        let base' := floorMul scale base base
        have hbaseFloor := floorMul_sound scale hScale base base
        have hbaseMul := Q'.mul_le_mul_of_nonneg hbase hbase hx0
          (fixedPointVal_nonneg scale hScale base)
        have hbase' : fixedPointVal scale hScale base' <= x * x :=
          Q'.le_trans' _ _ _ hbaseFloor hbaseMul
        have hxx0 : (0 : Q') <= x * x := Q'.mul_nonneg _ _ hx0 hx0
        by_cases hodd : exponent % 2 = 1
        · rw [if_pos hodd]
          let accumulator' := floorMul scale accumulator base
          have haccFloor := floorMul_sound scale hScale accumulator base
          have haccMul := Q'.mul_le_mul_of_nonneg hacc hbase hy0
            (fixedPointVal_nonneg scale hScale base)
          have hacc' : fixedPointVal scale hScale accumulator' <= y * x :=
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
            Q'.eqv_trans _ _ _ hsplit (Q'.one_mul_eqv _)
          exact Q'.le_trans' _ _ _ hrec
            (Q'.le_of_eqv
              (Q'.mul_eqv_congr_left y _ _ (Q'.eqv_symm hpow)))

private theorem ceilPowAux_sound
    (scale : Nat) (hScale : 0 < scale)
    (base accumulator fuel exponent : Nat)
    (x y : Q')
    (hx0 : (0 : Q') <= x) (hy0 : (0 : Q') <= y)
    (hbase : x <= fixedPointVal scale hScale base)
    (hacc : y <= fixedPointVal scale hScale accumulator)
    (hexponent : exponent < fuel) :
    y * qpow x exponent <=
      fixedPointVal scale hScale
        (roundedPowAux (ceilMul scale) base accumulator fuel exponent) := by
  induction fuel generalizing base accumulator exponent x y with
  | zero => omega
  | succ fuel ih =>
      rw [roundedPowAux]
      by_cases hzero : exponent = 0
      · subst exponent
        rw [if_pos rfl]
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_one_eqv y)) hacc
      · rw [if_neg hzero]
        have hpos : 0 < exponent := Nat.pos_of_ne_zero hzero
        have hdivfuel : exponent / 2 < fuel := by
          have hdivlt := Nat.div_lt_self hpos (by decide : 1 < 2)
          omega
        let base' := ceilMul scale base base
        have hbaseMul := Q'.mul_le_mul_of_nonneg hbase hbase
          (fixedPointVal_nonneg scale hScale base) hx0
        have hbaseCeil := ceilMul_sound scale hScale base base
        have hbase' : x * x <= fixedPointVal scale hScale base' :=
          Q'.le_trans' _ _ _ hbaseMul hbaseCeil
        have hxx0 : (0 : Q') <= x * x := Q'.mul_nonneg _ _ hx0 hx0
        by_cases hodd : exponent % 2 = 1
        · rw [if_pos hodd]
          let accumulator' := ceilMul scale accumulator base
          have haccMul := Q'.mul_le_mul_of_nonneg hacc hbase
            (fixedPointVal_nonneg scale hScale accumulator) hx0
          have haccCeil := ceilMul_sound scale hScale accumulator base
          have hacc' : y * x <= fixedPointVal scale hScale accumulator' :=
            Q'.le_trans' _ _ _ haccMul haccCeil
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
          have hleft : y * qpow x exponent ≈
              (y * x) * qpow (x * x) (exponent / 2) := by
            refine Q'.eqv_trans _
              (y * (x * qpow (x * x) (exponent / 2))) _
              (Q'.mul_eqv_congr_left y _ _ hpow) ?_
            exact Q'.eqv_symm (Q'.mul_assoc_eqv y x _)
          exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hrec
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
            Q'.eqv_trans _ _ _ hsplit (Q'.one_mul_eqv _)
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.mul_eqv_congr_left y _ _ hpow)) hrec

/-- Public logarithmic lower power bound. -/
theorem floorPow_le_qpow
    (scale : Nat) (hScale : 0 < scale) (base : Nat)
    (x : Q') (hx0 : (0 : Q') <= x)
    (hbase : fixedPointVal scale hScale base <= x)
    (exponent : Nat) :
    fixedPointVal scale hScale (floorPow scale base exponent) <=
      qpow x exponent := by
  have h := floorPowAux_sound scale hScale base scale
    (exponent + 1) exponent x (1 : Q') hx0 (by decide) hbase
    (Q'.le_of_eqv (fixedPointVal_scale_eqv_one scale hScale)) (by omega)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- Public logarithmic upper power bound. -/
theorem qpow_le_ceilPow
    (scale : Nat) (hScale : 0 < scale) (base : Nat)
    (x : Q') (hx0 : (0 : Q') <= x)
    (hbase : x <= fixedPointVal scale hScale base)
    (exponent : Nat) :
    qpow x exponent <=
      fixedPointVal scale hScale (ceilPow scale base exponent) := by
  have h := ceilPowAux_sound scale hScale base scale
    (exponent + 1) exponent x (1 : Q') hx0 (by decide) hbase
    (Q'.ge_of_eqv (fixedPointVal_scale_eqv_one scale hScale)) (by omega)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) h

#print axioms floorMul_sound
#print axioms ceilMul_sound
#print axioms fixedPointVal_add_eqv
#print axioms fixedPointVal_natMul_eqv
#print axioms qpow_binary_split
#print axioms floorPow_le_qpow
#print axioms qpow_le_ceilPow

end YMGap.Continuum.FixedPointPowerInterval
