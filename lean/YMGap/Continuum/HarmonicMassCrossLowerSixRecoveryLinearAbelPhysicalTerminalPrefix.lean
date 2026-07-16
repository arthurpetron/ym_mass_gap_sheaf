/-
# Terminal Taylor prefix for the physical linear Abel crossing

The constructive crossing search is driven by the sign of the full carrier
prefix at `N = c+1`.  This module begins the terminal estimate with the exact
polynomial block left after clearing the fourth-order Taylor floor.  Its
positivity is proved uniformly from only `36 <= c` and `0 <= X <= 2c`, where
`X = 2D-c^2` is the within-cell slack.  The certificate is subtraction-free
after introducing the two genuine slacks `c-36` and `2c-X`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalPrefixCrossing
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalTerminalPrefix

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalPrefixCrossing
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPostBootstrap
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def pv (n : Nat) : PE := .var n
private def pa (x y : PE) : PE := .add x y
private def pm (x y : PE) : PE := .mul x y
private def pn (x : PE) : PE := .neg x
private def pp (x : PE) (n : Nat) : PE := .pow x n

private theorem eval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const z => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb => exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ iha)
        (Q'.mul_eqv_congr_left _ _ _ ihb)
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

/-! ## The exact cell-slack polynomial certificate -/

private def pTerminalQ0At (c : PE) : PE :=
  pm c
    (pa (pa (pa (pa (pa (pa (pa
      (pm (pc 1260) (pp c 7))
      (pn (pm (pc 44562) (pp c 6))))
      (pm (pc 62251) (pp c 5)))
      (pm (pc 138486) (pp c 4)))
      (pn (pm (pc 3422560) (pp c 3))))
      (pn (pm (pc 5749632) (pp c 2))))
      (pn (pm (pc 1592064) c)))
      (pc 167616))

private def pTerminalRAt (c : PE) : PE :=
  pm (pc 7)
    (pa (pa (pa (pa (pa (pa
      (pm (pc 360) (pp c 6))
      (pn (pm (pc 9882) (pp c 5))))
      (pn (pm (pc 24371) (pp c 4))))
      (pm (pc 76842) (pp c 3)))
      (pm (pc 143156) (pp c 2)))
      (pm (pc 39360) c))
      (pc 2880))

private def pTerminalA2At (c : PE) : PE :=
  pa (pa (pa
    (pm (pc 4662) (pp c 3))
    (pm (pc 202419) (pp c 2)))
    (pm (pc 168714) c))
    (pc 30240)

private def pTerminalBlock : PE :=
  let c := pv 0
  let X := pv 1
  let q0 := pTerminalQ0At c
  let q1 := pa (pa (pa (pa (pa (pa
    (pm (pc 2520) (pp c 6))
    (pn (pm (pc 69174) (pp c 5))))
    (pn (pm (pc 151193) (pp c 4))))
    (pm (pc 952812) (pp c 3)))
    (pm (pc 1339520) (pp c 2)))
    (pm (pc 336000) c))
    (pc 20160)
  let q3 := pa (pa
    (pn (pm (pc 2520) (pp c 2)))
    (pm (pc 19950) c))
    (pc 11025)
  pa (pa (pa (pa q0
    (pm q1 X))
    (pn (pm (pTerminalA2At c) (pp X 2))))
    (pm q3 (pp X 3)))
    (pn (pm (pc 1260) (pp X 4)))

private def pTerminalBlockDecomposition : PE :=
  let c := pv 0
  let X := pv 1
  let T := pa (pm (pc 2) c) (pn X)
  let c2 := pp c 2
  let X2 := pp X 2
  pa (pa (pa (pa (pa
    (pTerminalQ0At c)
    (pm X (pTerminalRAt c)))
    (pm (pm (pm (pTerminalA2At c) X) T) (pc 1)))
    (pm (pm (pm (pm (pm (pc 2520) c2) X) T)
      (pa (pm (pc 2) c) X)) (pc 1)))
    (pm (pm (pm (pc 1260) X) T)
      (pa (pa (pm (pc 4) c2) (pm (pm (pc 2) c) X)) X2)))
    (pm (pa (pm (pc 19950) c) (pc 11025)) (pp X 3))

private theorem pTerminalBlock_decomposition_normal :
    RingNormaliser.normalize pTerminalBlock =
      RingNormaliser.normalize pTerminalBlockDecomposition := by
  decide

private def pTerminalQ0Shift : PE :=
  pTerminalQ0At (pa (pc 36) (pv 0))

private def pTerminalQ0Positive : PE :=
  let z := pv 0
  pa (pa (pa (pa (pa (pa (pa (pa
    (pm (pc 1260) (pp z 8))
    (pm (pc 318318) (pp z 7)))
    (pm (pc 34555507) (pp z 6)))
    (pm (pc 2092832670) (pp z 5)))
    (pm (pc 76605832040) (pp z 4)))
    (pm (pc 1706230525248) (pp z 3)))
    (pm (pc 21818254664448) (pp z 2)))
    (pm (pc 133984648062144) z))
    (pc 200396300348160)

private theorem pTerminalQ0_shift_normal :
    RingNormaliser.normalize pTerminalQ0Shift =
      RingNormaliser.normalize pTerminalQ0Positive := by
  decide

private def pTerminalRShift : PE :=
  pTerminalRAt (pa (pc 36) (pv 0))

private def pTerminalRPositive : PE :=
  let z := pv 0
  pa (pa (pa (pa (pa (pa
    (pm (pc 2520) (pp z 6))
    (pm (pc 475146) (pp z 5)))
    (pm (pc 36366883) (pp z 4)))
    (pm (pc 1430939286) (pp z 3)))
    (pm (pc 29948195732) (pp z 2)))
    (pm (pc 303646058688) z))
    (pc 1042671409920)

private theorem pTerminalR_shift_normal :
    RingNormaliser.normalize pTerminalRShift =
      RingNormaliser.normalize pTerminalRPositive := by
  decide

/-- The exact fourth-order terminal block after the substitution
`2D = c^2+X`.  The surrounding positive factor `16(c+1)(c+2)` is deliberately
kept outside this definition. -/
def lowerSixRecoveryTerminalPrefixBlock (c X : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => c | _ => X) pTerminalBlock

private theorem terminalQ0_nonnegative {c : Nat} (hc : 36 ≤ c) :
    (0 : Q') ≤
      RingNormaliser.eval (fun _ => Q'.ofNat c)
        (pTerminalQ0At (pv 0)) := by
  let z := Q'.ofNat (c - 36)
  have hcz : Q'.ofNat c ≈ Q'.ofNat 36 + z := by
    have hnat : 36 + (c - 36) = c := Nat.add_sub_of_le hc
    rw [← hnat]
    exact Q'.ofNat_add_eqv 36 (c - 36)
  have hshift :
      RingNormaliser.eval (fun _ => Q'.ofNat c)
          (pTerminalQ0At (pv 0)) ≈
        RingNormaliser.eval (fun _ => z) pTerminalQ0Shift := by
    refine Q'.eqv_trans _
      (RingNormaliser.eval (fun _ => Q'.ofNat 36 + z)
        (pTerminalQ0At (pv 0))) _ ?_ ?_
    · exact eval_eqv_congr _ (fun _ => hcz)
    · exact Q'.eqv_refl _
  have hposEq : RingNormaliser.eval (fun _ => z) pTerminalQ0Shift ≈
      RingNormaliser.eval (fun _ => z) pTerminalQ0Positive :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalQ0_shift_normal (fun _ => z)
  have hz0 : (0 : Q') ≤ z := by
    dsimp only [z]
    exact ExpNeg.ofNat_nonneg' _
  have hp0 : (0 : Q') ≤
      RingNormaliser.eval (fun _ => z) pTerminalQ0Positive := by
    simp only [pTerminalQ0Positive, pc, pv, pa, pm, pp,
      RingNormaliser.eval]
    repeat' apply Q'.zero_le_add
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 8)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 7)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 6)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 5)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 4)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 3)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 2)
    · exact Q'.mul_nonneg _ _ (by decide) hz0
    · decide
  exact Q'.le_trans' _ _ _ hp0
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ hshift hposEq))

private theorem terminalR_nonnegative {c : Nat} (hc : 36 ≤ c) :
    (0 : Q') ≤
      RingNormaliser.eval (fun _ => Q'.ofNat c)
        (pTerminalRAt (pv 0)) := by
  let z := Q'.ofNat (c - 36)
  have hcz : Q'.ofNat c ≈ Q'.ofNat 36 + z := by
    have hnat : 36 + (c - 36) = c := Nat.add_sub_of_le hc
    rw [← hnat]
    exact Q'.ofNat_add_eqv 36 (c - 36)
  have hshift :
      RingNormaliser.eval (fun _ => Q'.ofNat c)
          (pTerminalRAt (pv 0)) ≈
        RingNormaliser.eval (fun _ => z) pTerminalRShift := by
    refine Q'.eqv_trans _
      (RingNormaliser.eval (fun _ => Q'.ofNat 36 + z)
        (pTerminalRAt (pv 0))) _ ?_ ?_
    · exact eval_eqv_congr _ (fun _ => hcz)
    · exact Q'.eqv_refl _
  have hposEq : RingNormaliser.eval (fun _ => z) pTerminalRShift ≈
      RingNormaliser.eval (fun _ => z) pTerminalRPositive :=
    RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalR_shift_normal (fun _ => z)
  have hz0 : (0 : Q') ≤ z := by
    dsimp only [z]
    exact ExpNeg.ofNat_nonneg' _
  have hp0 : (0 : Q') ≤
      RingNormaliser.eval (fun _ => z) pTerminalRPositive := by
    simp only [pTerminalRPositive, pc, pv, pa, pm, pp,
      RingNormaliser.eval]
    repeat' apply Q'.zero_le_add
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 6)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 5)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 4)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 3)
    · exact Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hz0 2)
    · exact Q'.mul_nonneg _ _ (by decide) hz0
    · decide
  exact Q'.le_trans' _ _ _ hp0
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ hshift hposEq))

/-- The cleared terminal block is nonnegative throughout every
post-bootstrap within-center cell.  This is an exact algebraic certificate,
not a finite table: the proof uses the slacks `c-36` and `2c-X` and hence
covers all later cells uniformly. -/
theorem lowerSixRecoveryTerminalPrefixBlock_nonnegative
    {c : Nat} {X : Q'} (hc : 36 ≤ c)
    (hX0 : (0 : Q') ≤ X)
    (hX2c : X ≤ Q'.ofNat 2 * Q'.ofNat c) :
    (0 : Q') ≤
      lowerSixRecoveryTerminalPrefixBlock (Q'.ofNat c) X := by
  let C := Q'.ofNat c
  let T := Q'.ofNat 2 * C + -X
  let A2 := RingNormaliser.eval (fun _ => C) (pTerminalA2At (pv 0))
  let Q0 := RingNormaliser.eval (fun _ => C) (pTerminalQ0At (pv 0))
  let R := RingNormaliser.eval (fun _ => C) (pTerminalRAt (pv 0))
  have hC0 : (0 : Q') ≤ C := by
    dsimp only [C]
    exact ExpNeg.ofNat_nonneg' _
  have hT0 : (0 : Q') ≤ T := by
    dsimp only [T, C]
    exact Q'.sub_nonneg_of_le hX2c
  have hA20 : (0 : Q') ≤ A2 := by
    dsimp only [A2]
    simp only [pTerminalA2At, pc, pv, pa, pm, pp,
      RingNormaliser.eval]
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ (by decide)
            (ringQpow_nonnegative hC0 3))
          (Q'.mul_nonneg _ _ (by decide)
            (ringQpow_nonnegative hC0 2)))
        (Q'.mul_nonneg _ _ (by decide) hC0))
      (by decide)
  have hQ00 : (0 : Q') ≤ Q0 := by
    dsimp only [Q0, C]
    exact terminalQ0_nonnegative hc
  have hR0 : (0 : Q') ≤ R := by
    dsimp only [R, C]
    exact terminalR_nonnegative hc
  have htwoCplusX0 : (0 : Q') ≤ Q'.ofNat 2 * C + X :=
    Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide) hC0) hX0
  have hquarticFactor0 : (0 : Q') ≤
      Q'.ofNat 4 * RingNormaliser.qpow C 2 +
          (Q'.ofNat 2 * C) * X + RingNormaliser.qpow X 2 := by
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide)
          (ringQpow_nonnegative hC0 2))
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (by decide) hC0) hX0))
      (ringQpow_nonnegative hX0 2)
  have hdecomp :
      lowerSixRecoveryTerminalPrefixBlock C X ≈
        RingNormaliser.eval (fun | 0 => C | _ => X)
          pTerminalBlockDecomposition := by
    exact RingNormaliser.poly_identity_of_normal_eq _ _
      pTerminalBlock_decomposition_normal (fun | 0 => C | _ => X)
  have hrhs0 : (0 : Q') ≤
      RingNormaliser.eval (fun | 0 => C | _ => X)
        pTerminalBlockDecomposition := by
    simp only [pTerminalBlockDecomposition, pTerminalQ0At,
      pTerminalRAt, pTerminalA2At, pc, pv, pa, pm, pn, pp,
      RingNormaliser.eval]
    change (0 : Q') ≤
      Q0 + X * R + A2 * X * T * Q'.ofNat 1 +
        Q'.ofNat 2520 * RingNormaliser.qpow C 2 * X * T *
          (Q'.ofNat 2 * C + X) * Q'.ofNat 1 +
        Q'.ofNat 1260 * X * T *
          (Q'.ofNat 4 * RingNormaliser.qpow C 2 +
            Q'.ofNat 2 * C * X + RingNormaliser.qpow X 2) +
        (Q'.ofNat 19950 * C + Q'.ofNat 11025) *
          RingNormaliser.qpow X 3
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.zero_le_add _ _ hQ00
              (Q'.mul_nonneg _ _ hX0 hR0))
            (Q'.mul_nonneg _ _
              (Q'.mul_nonneg _ _
                (Q'.mul_nonneg _ _ hA20 hX0) hT0)
              (by decide)))
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _
              (Q'.mul_nonneg _ _
                (Q'.mul_nonneg _ _
                  (Q'.mul_nonneg _ _ (by decide)
                    (ringQpow_nonnegative hC0 2)) hX0) hT0)
                htwoCplusX0)
              (by decide)))
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (by decide) hX0) hT0)
          hquarticFactor0))
      (Q'.mul_nonneg _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ (by decide) hC0) (by decide))
        (ringQpow_nonnegative hX0 3))
  exact Q'.le_trans' _ _ _ hrhs0 (Q'.ge_of_eqv hdecomp)

#print axioms lowerSixRecoveryTerminalPrefixBlock_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalTerminalPrefix
