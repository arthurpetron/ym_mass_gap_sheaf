/-
# Spin-only interval certificates and a small-nome heat envelope

The constructed square cap obeys b(n) <= 16^n. This deliberately coarse
algebraic envelope is independent of the polynomial's coordinate layout.
The actual SU(2) Casimir weights make the positive-label sum geometric
under the explicit guard (2*w^3)*16 <= 1/2. Neither the cap nor this guard
contains a volume or cutoff; the heat remainder bound still depends on w.
-/

import YMGap.Continuum.QuaternionHaarPolynomialInterval
import YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder

namespace YMGap.Continuum.QuaternionHaarCharacterInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

private theorem character_step (n : Nat) :
    Q'.eqv (characterBound (n+2)) (8*characterBound (n+1)+2*characterBound n) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.mul (.mul (.const 2) (.const 2)) (.const 1)) (.var 0))
      (.mul (.mul (.mul (.const 2) (.const 2)) (.const 1)) (.var 0)))
      (.add (.mul (.mul (.neg (.const 1)) (.neg (.const 1))) (.var 1))
        (.mul (.mul (.neg (.const 1)) (.neg (.const 1))) (.var 1))))
    (.add (.mul (.const 8) (.var 0)) (.mul (.const 2) (.var 1))) (by decide)
    (fun i => if i = 0 then characterBound (n+1) else characterBound n)

private theorem envelope_step (n : Nat) :
    8*(16 : Q')^(n+1)+2*(16 : Q')^n ≤ (16 : Q')^(n+2) := by
  have h := Q'.mul_le_mul_of_nonneg_right (130 : Q') 256 ((16 : Q')^n)
    (by decide) (Q'.pow_nonneg _ (by decide) n)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.const 8) (.mul (.const 16) (.var 0))) (.mul (.const 2) (.var 0)))
      (.mul (.const 130) (.var 0)) (by decide) (fun _ => (16 : Q')^n)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.const 256) (.var 0)) (.mul (.const 16) (.mul (.const 16) (.var 0)))
      (by decide) (fun _ => (16 : Q')^n))))

theorem characterBound_le : ∀ n, characterBound n ≤ (16 : Q')^n
  | 0 => by decide
  | 1 => by decide
  | n+2 => Q'.le_trans' _ _ _ (Q'.le_of_eqv (character_step n))
      (Q'.le_trans' _ _ _ (ExpNeg.add_le_add2
        (Q'.mul_le_mul_of_nonneg_left _ _ (8 : Q') (characterBound_le (n+1)) (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') (characterBound_le n) (by decide)))
        (envelope_step n))

private theorem one_le_envelope : ∀ n : Nat, (1 : Q') ≤ (16 : Q')^n
  | 0 => Q'.le_refl' _
  | n+1 => Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 16)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 16))
        (Q'.mul_le_mul_of_nonneg_left _ _ (16 : Q') (one_le_envelope n) (by decide)))

theorem characterCap_le (n : Nat) : characterBound n+1 ≤ 2*(16 : Q')^n :=
  Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 (characterBound_le n) (one_le_envelope n))
    (Q'.le_of_eqv (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
      (.mul (.const 2) (.var 0)) (by decide) (fun _ => (16 : Q')^n)))

/-- Both signs of the actual character, valid under arbitrary Haar insertions. -/
def characterInterval {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) (n : Nat) :
    Interval blocks (characterPolynomial p n) (2*(16 : Q')^n) :=
  (Interval.ofSquare (character_squareBound P n)).weaken (characterCap_le n)

def heatTermBound (w : Q') (n : Nat) : Q' := coeffW w n * (2*(16 : Q')^n)

def heatRatio (w : Q') : Q' := (2*qpow w 3)*16

def heatRemainderBound (w : Q') : Q' := heatTermBound w 1 * 2

/-- The complete coupling dependence of the returned remainder cap. -/
theorem heatRemainderBound_eq (w : Q') : Q'.eqv (heatRemainderBound w) (128*qpow w 3) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.mul (.const 16) (.const 1)))) (.const 2))
    (.mul (.const 128) (.var 0)) (by decide) (fun _ => qpow w 3)

theorem heatTermBound_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (n : Nat) :
    (0 : Q') ≤ heatTermBound w n := Q'.mul_nonneg _ _ (coeffW_nonneg hw n)
  (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) n))

theorem heatRemainderBound_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') ≤ heatRemainderBound w := Q'.mul_nonneg _ _ (heatTermBound_nonnegative hw 1) (by decide)

theorem heatTermBound_step {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat) :
    heatTermBound w (n+1) ≤ heatRatio w * heatTermBound w n := by
  have hc : coeffW w (n+1) ≤ (2*qpow w 3)*coeffW w n := by
    simpa only [tailTerm, Nat.pow_one, coeffW, dimQ] using
      (tailTerm_ratio_gen hw0 hw1 1 0 n (Nat.zero_le n))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hc
    (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) (n+1))))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.mul (.const 16) (.var 2))))
      (.mul (.mul (.var 0) (.const 16)) (.mul (.var 1) (.mul (.const 2) (.var 2))))
      (by decide) (fun i => if i = 0 then 2*qpow w 3 else if i = 1 then coeffW w n else (16 : Q')^n)))

theorem heatTermBound_geometric {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (k : Nat) :
    heatTermBound w (1+k) ≤ heatTermBound w 1 * HalfPow.half^k := by
  apply CharacterTail.geom_dom (fun i => heatTermBound w (1+i)) _ _ HalfPow.half_nonneg (Q'.le_refl' _)
  intro i
  rw [← Nat.add_assoc]
  exact Q'.le_trans' _ _ _ (heatTermBound_step hw0 hw1 _)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall (heatTermBound_nonnegative hw0 _))

theorem heatPositiveLabels_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (count : Nat) :
    finSum (fun i => heatTermBound w (1+i)) count ≤ heatRemainderBound w := by
  have hterm := ExpNeg.finSum_le_finSum_of_termwise _ _ (heatTermBound_geometric hw0 hw1 hsmall) count
  have hgeo : finSum (fun i => heatTermBound w 1 * HalfPow.half^i) count ≤
      geoTailBase (heatTermBound w 1) HalfPow.half 0 := by
    simpa only [geoIncrBase, Nat.zero_add] using
      (geoTailBase_series_le (heatTermBound_nonnegative hw0 1)
        (by decide : (0 : Q') < HalfPow.half) (by decide : HalfPow.half < (1 : Q')) 0 count)
  exact Q'.le_trans' _ _ _ hterm (Q'.le_trans' _ _ _ hgeo (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _))
      (Q'.mul_eqv_congr_left _ _ _ (by decide)))))

end YMGap.Continuum.QuaternionHaarCharacterInterval

#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.characterBound_le
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.characterCap_le
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.characterInterval
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatTermBound
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatRatio
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatRemainderBound
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatRemainderBound_eq
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatTermBound_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatRemainderBound_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatTermBound_step
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatTermBound_geometric
#print axioms YMGap.Continuum.QuaternionHaarCharacterInterval.heatPositiveLabels_bound
