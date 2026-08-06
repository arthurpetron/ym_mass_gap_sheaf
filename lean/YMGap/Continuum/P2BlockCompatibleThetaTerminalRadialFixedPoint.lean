/-
Track 11.7-fusion / R3u -- fixed-point tables for the radial fourth moment.

# Result

The fourth-moment compiler leaves one quantitative inequality.  A 640-cell
right-endpoint estimate is slightly too weak uniformly, so the physical tail
is split into the exact first scale `k=7` and a scale-independent 1280-cell
estimate for `k>=8`.

This module contains the two finite arithmetic certificates.  The companion
transport module relates their common-denominator powers to the physical
theta sums.  All powers are evaluated by the logarithmic floor/ceiling
compiler; no literal million-factor rational power is normalized.

# Constructivity

Structural recursion on finite tables, binary fixed-point exponentiation,
and closed natural-number cross multiplication only.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.FixedPointPowerInterval

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedPoint

set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FixedPointPowerInterval
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialMoment
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## Uniform `k>=8` table -/

def radialTailBlocks : Nat := 1280

def radialTailLowerScale : Nat := 786432000000000000
def radialTailLowerBase : Nat := 786431000000000000
def radialTailUpperScale : Nat := 786433000000000000
def radialTailUpperBase : Nat := 786432000000000000

theorem radialTailLowerScale_pos : 0 < radialTailLowerScale := by decide
theorem radialTailUpperScale_pos : 0 < radialTailUpperScale := by decide

/-- The Bernoulli lower base `1-1/786432`. -/
def radialTailLowerQ : Q' := Q'.mkPos 786431 786432 (by decide)

/-- The reciprocal-Bernoulli upper base `1/(1+1/786432)`. -/
def radialTailUpperQ : Q' := Q'.mkPos 786432 786433 (by decide)

theorem radialTailLowerVal_base_eqv :
    fixedPointVal radialTailLowerScale radialTailLowerScale_pos
        radialTailLowerBase ≈ radialTailLowerQ := by
  show (fixedPointVal radialTailLowerScale radialTailLowerScale_pos
      radialTailLowerBase).num * (radialTailLowerQ.den : Int) =
    radialTailLowerQ.num *
      ((fixedPointVal radialTailLowerScale radialTailLowerScale_pos
        radialTailLowerBase).den : Int)
  rw [fixedPointVal_num, fixedPointVal_den]
  unfold radialTailLowerScale radialTailLowerBase radialTailLowerQ
  rw [Q'.mkPos_num, Q'.mkPos_den]
  decide

theorem radialTailUpperVal_base_eqv :
    fixedPointVal radialTailUpperScale radialTailUpperScale_pos
        radialTailUpperBase ≈ radialTailUpperQ := by
  show (fixedPointVal radialTailUpperScale radialTailUpperScale_pos
      radialTailUpperBase).num * (radialTailUpperQ.den : Int) =
    radialTailUpperQ.num *
      ((fixedPointVal radialTailUpperScale radialTailUpperScale_pos
        radialTailUpperBase).den : Int)
  rw [fixedPointVal_num, fixedPointVal_den]
  unfold radialTailUpperScale radialTailUpperBase radialTailUpperQ
  rw [Q'.mkPos_num, Q'.mkPos_den]
  decide

theorem radialTailFloorPow_le (exponent : Nat) :
    fixedPointVal radialTailLowerScale radialTailLowerScale_pos
        (floorPow radialTailLowerScale radialTailLowerBase exponent) <=
      qpow radialTailLowerQ exponent := by
  exact floorPow_le_qpow radialTailLowerScale radialTailLowerScale_pos
    radialTailLowerBase radialTailLowerQ (by decide)
    (Q'.le_of_eqv radialTailLowerVal_base_eqv) exponent

theorem radialTailPow_le_ceil (exponent : Nat) :
    qpow radialTailUpperQ exponent <=
      fixedPointVal radialTailUpperScale radialTailUpperScale_pos
        (ceilPow radialTailUpperScale radialTailUpperBase exponent) := by
  exact qpow_le_ceilPow radialTailUpperScale radialTailUpperScale_pos
    radialTailUpperBase radialTailUpperQ (by decide)
    (Q'.ge_of_eqv radialTailUpperVal_base_eqv) exponent

/-- Lower table `4 sum b^4 q_-^(2(b+1)^2)`. -/
def radialTailLowerTableNum : Nat -> Nat
  | 0 => 0
  | b + 1 => radialTailLowerTableNum b +
      4 * (b * b * b * b) *
        floorPow radialTailLowerScale radialTailLowerBase
          (2 * ((b + 1) * (b + 1)))

/-- Upper table `sum (b+1)^2 q_+^(2b^2)`. -/
def radialTailUpperTableNum : Nat -> Nat
  | 0 => 0
  | b + 1 => radialTailUpperTableNum b +
      ((b + 1) * (b + 1)) *
        ceilPow radialTailUpperScale radialTailUpperBase (2 * (b * b))

def radialTailLowerWitnessNum : Nat :=
  173758773772799834822565664945344

def radialTailUpperWitnessNum : Nat :=
  82817847393363167394233139

def radialTailTerminalWitnessNum : Nat :=
  12192774397219978

theorem radialTailLowerTableNum_eq :
    radialTailLowerTableNum radialTailBlocks =
      radialTailLowerWitnessNum := by decide

theorem radialTailUpperTableNum_eq :
    radialTailUpperTableNum radialTailBlocks =
      radialTailUpperWitnessNum := by decide

theorem radialTailTerminalPow_eq :
    ceilPow radialTailUpperScale radialTailUpperBase
        (2 * (radialTailBlocks * radialTailBlocks)) =
      radialTailTerminalWitnessNum := by decide

theorem radialTailLowerGenerated_eqv : forall B : Nat,
    fixedPointVal radialTailLowerScale radialTailLowerScale_pos
        (radialTailLowerTableNum B) ≈
      fsum (fun b =>
        Q'.ofNat (4 * (b * b * b * b)) *
          fixedPointVal radialTailLowerScale radialTailLowerScale_pos
            (floorPow radialTailLowerScale radialTailLowerBase
              (2 * ((b + 1) * (b + 1))))) B
  | 0 => by
      change fixedPointVal radialTailLowerScale radialTailLowerScale_pos 0 ≈ 0
      show (0 : Int) * (0 : Int) = (0 : Int) * radialTailLowerScale
      rfl
  | B + 1 => by
      change fixedPointVal radialTailLowerScale radialTailLowerScale_pos
          (radialTailLowerTableNum B +
            4 * (B * B * B * B) *
              floorPow radialTailLowerScale radialTailLowerBase
                (2 * ((B + 1) * (B + 1)))) ≈ _
      refine Q'.eqv_trans _ _ _
        (fixedPointVal_add_eqv _ _ _ _) ?_
      exact Q'.add_eqv_congr'
        (radialTailLowerGenerated_eqv B)
        (fixedPointVal_natMul_eqv _ _ _ _)

theorem radialTailUpperGenerated_eqv : forall B : Nat,
    fixedPointVal radialTailUpperScale radialTailUpperScale_pos
        (radialTailUpperTableNum B) ≈
      fsum (fun b =>
        Q'.ofNat ((b + 1) * (b + 1)) *
          fixedPointVal radialTailUpperScale radialTailUpperScale_pos
            (ceilPow radialTailUpperScale radialTailUpperBase
              (2 * (b * b)))) B
  | 0 => by
      change fixedPointVal radialTailUpperScale radialTailUpperScale_pos 0 ≈ 0
      show (0 : Int) * (0 : Int) = (0 : Int) * radialTailUpperScale
      rfl
  | B + 1 => by
      change fixedPointVal radialTailUpperScale radialTailUpperScale_pos
          (radialTailUpperTableNum B +
            (B + 1) * (B + 1) *
              ceilPow radialTailUpperScale radialTailUpperBase
                (2 * (B * B))) ≈ _
      refine Q'.eqv_trans _ _ _
        (fixedPointVal_add_eqv _ _ _ _) ?_
      exact Q'.add_eqv_congr'
        (radialTailUpperGenerated_eqv B)
        (fixedPointVal_natMul_eqv _ _ _ _)

def radialTailLowerTable : Q' :=
  fixedPointVal radialTailLowerScale radialTailLowerScale_pos
    radialTailLowerWitnessNum

def radialTailUpperTable : Q' :=
  fixedPointVal radialTailUpperScale radialTailUpperScale_pos
    radialTailUpperWitnessNum

def radialTailTerminalUpper : Q' :=
  fixedPointVal radialTailUpperScale radialTailUpperScale_pos
    radialTailTerminalWitnessNum

/-- Exact finite balance behind the uniform tail estimate.  The terminal
coefficient `2B^3+B^2` also absorbs all dyadic factors because `H>=1`. -/
theorem radialTailFixedBalance :
    terminalRadialMomentCoeff *
          (Q'.ofNat (radialTailBlocks * radialTailBlocks) *
            radialTailUpperTable) +
        Q'.ofNat
            (2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) +
              radialTailBlocks * radialTailBlocks) *
          radialTailTerminalUpper <=
      radialTailLowerTable := by
  unfold terminalRadialMomentCoeff radialTailBlocks
    radialTailUpperTable radialTailLowerTable radialTailTerminalUpper
    radialTailUpperWitnessNum radialTailLowerWitnessNum
    radialTailTerminalWitnessNum radialTailUpperScale radialTailLowerScale
  decide

/-! ## Exact first scale `k=7` -/

def radialSevenBlocks : Nat := 640
def radialSevenScale : Nat := 196608000000000000
def radialSevenBase : Nat := 196607000000000000

theorem radialSevenScale_pos : 0 < radialSevenScale := by decide

def radialSevenQ : Q' := Q'.mkPos 196607 196608 (by decide)

theorem radialSevenVal_base_eqv :
    fixedPointVal radialSevenScale radialSevenScale_pos radialSevenBase ≈
      radialSevenQ := by
  show (fixedPointVal radialSevenScale radialSevenScale_pos
      radialSevenBase).num * (radialSevenQ.den : Int) =
    radialSevenQ.num *
      ((fixedPointVal radialSevenScale radialSevenScale_pos
        radialSevenBase).den : Int)
  rw [fixedPointVal_num, fixedPointVal_den]
  unfold radialSevenScale radialSevenBase radialSevenQ
  rw [Q'.mkPos_num, Q'.mkPos_den]
  decide

theorem radialSevenFloorPow_le (exponent : Nat) :
    fixedPointVal radialSevenScale radialSevenScale_pos
        (floorPow radialSevenScale radialSevenBase exponent) <=
      qpow radialSevenQ exponent := by
  exact floorPow_le_qpow radialSevenScale radialSevenScale_pos
    radialSevenBase radialSevenQ (by decide)
    (Q'.le_of_eqv radialSevenVal_base_eqv) exponent

theorem radialSevenPow_le_ceil (exponent : Nat) :
    qpow radialSevenQ exponent <=
      fixedPointVal radialSevenScale radialSevenScale_pos
        (ceilPow radialSevenScale radialSevenBase exponent) := by
  exact qpow_le_ceilPow radialSevenScale radialSevenScale_pos
    radialSevenBase radialSevenQ (by decide)
    (Q'.ge_of_eqv radialSevenVal_base_eqv) exponent

def radialSevenLowerTableNum : Nat -> Nat
  | 0 => 0
  | b + 1 => radialSevenLowerTableNum b +
      4 * ((b + 1) * (b + 1) * (b + 1) * (b + 1)) *
        floorPow radialSevenScale radialSevenBase
          (2 * ((b + 1) * (b + 1)))

def radialSevenUpperTableNum : Nat -> Nat
  | 0 => 0
  | b + 1 => radialSevenUpperTableNum b +
      ((b + 1) * (b + 1)) *
        ceilPow radialSevenScale radialSevenBase
          (2 * ((b + 1) * (b + 1)))

def radialSevenLowerWitnessNum : Nat :=
  1364972877006787839384657499112

def radialSevenUpperWitnessNum : Nat :=
  2579452054761718741144210

def radialSevenTerminalWitnessNum : Nat :=
  3048149348769269

theorem radialSevenLowerTableNum_eq :
    radialSevenLowerTableNum radialSevenBlocks =
      radialSevenLowerWitnessNum := by decide

theorem radialSevenUpperTableNum_eq :
    radialSevenUpperTableNum radialSevenBlocks =
      radialSevenUpperWitnessNum := by decide

theorem radialSevenTerminalPow_eq :
    ceilPow radialSevenScale radialSevenBase
        (2 * (radialSevenBlocks * radialSevenBlocks)) =
      radialSevenTerminalWitnessNum := by decide

theorem radialSevenLowerGenerated_eqv : forall B : Nat,
    fixedPointVal radialSevenScale radialSevenScale_pos
        (radialSevenLowerTableNum B) ≈
      fsum (fun b =>
        Q'.ofNat
            (4 * ((b + 1) * (b + 1) * (b + 1) * (b + 1))) *
          fixedPointVal radialSevenScale radialSevenScale_pos
            (floorPow radialSevenScale radialSevenBase
              (2 * ((b + 1) * (b + 1))))) B
  | 0 => by
      change fixedPointVal radialSevenScale radialSevenScale_pos 0 ≈ 0
      show (0 : Int) * (0 : Int) = (0 : Int) * radialSevenScale
      rfl
  | B + 1 => by
      change fixedPointVal radialSevenScale radialSevenScale_pos
          (radialSevenLowerTableNum B +
            4 * ((B + 1) * (B + 1) * (B + 1) * (B + 1)) *
              floorPow radialSevenScale radialSevenBase
                (2 * ((B + 1) * (B + 1)))) ≈ _
      refine Q'.eqv_trans _ _ _
        (fixedPointVal_add_eqv _ _ _ _) ?_
      exact Q'.add_eqv_congr'
        (radialSevenLowerGenerated_eqv B)
        (fixedPointVal_natMul_eqv _ _ _ _)

theorem radialSevenUpperGenerated_eqv : forall B : Nat,
    fixedPointVal radialSevenScale radialSevenScale_pos
        (radialSevenUpperTableNum B) ≈
      fsum (fun b =>
        Q'.ofNat ((b + 1) * (b + 1)) *
          fixedPointVal radialSevenScale radialSevenScale_pos
            (ceilPow radialSevenScale radialSevenBase
              (2 * ((b + 1) * (b + 1))))) B
  | 0 => by
      change fixedPointVal radialSevenScale radialSevenScale_pos 0 ≈ 0
      show (0 : Int) * (0 : Int) = (0 : Int) * radialSevenScale
      rfl
  | B + 1 => by
      change fixedPointVal radialSevenScale radialSevenScale_pos
          (radialSevenUpperTableNum B +
            (B + 1) * (B + 1) *
              ceilPow radialSevenScale radialSevenBase
                (2 * ((B + 1) * (B + 1)))) ≈ _
      refine Q'.eqv_trans _ _ _
        (fixedPointVal_add_eqv _ _ _ _) ?_
      exact Q'.add_eqv_congr'
        (radialSevenUpperGenerated_eqv B)
        (fixedPointVal_natMul_eqv _ _ _ _)

def radialSevenLowerTable : Q' :=
  fixedPointVal radialSevenScale radialSevenScale_pos
    radialSevenLowerWitnessNum

def radialSevenUpperTable : Q' :=
  fixedPointVal radialSevenScale radialSevenScale_pos
    radialSevenUpperWitnessNum

def radialSevenTerminalUpper : Q' :=
  fixedPointVal radialSevenScale radialSevenScale_pos
    radialSevenTerminalWitnessNum

theorem radialSevenFixedBalance :
    terminalRadialMomentCoeff *
          (Q'.ofNat (radialSevenBlocks * radialSevenBlocks) *
            radialSevenUpperTable) +
        Q'.ofNat
            ((2 * radialSevenBlocks + 1) *
              (radialSevenBlocks * radialSevenBlocks)) *
          radialSevenTerminalUpper <=
      radialSevenLowerTable := by
  unfold terminalRadialMomentCoeff radialSevenBlocks
    radialSevenUpperTable radialSevenLowerTable radialSevenTerminalUpper
    radialSevenUpperWitnessNum radialSevenLowerWitnessNum
    radialSevenTerminalWitnessNum radialSevenScale
  decide

#print axioms radialTailFloorPow_le
#print axioms radialTailPow_le_ceil
#print axioms radialTailLowerTableNum_eq
#print axioms radialTailUpperTableNum_eq
#print axioms radialTailLowerGenerated_eqv
#print axioms radialTailUpperGenerated_eqv
#print axioms radialTailFixedBalance
#print axioms radialSevenLowerTableNum_eq
#print axioms radialSevenUpperTableNum_eq
#print axioms radialSevenLowerGenerated_eqv
#print axioms radialSevenUpperGenerated_eqv
#print axioms radialSevenFixedBalance

end YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedPoint
