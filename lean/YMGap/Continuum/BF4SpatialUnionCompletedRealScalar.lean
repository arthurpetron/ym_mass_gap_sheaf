/-
# Modulus-bearing real scaling on the SAME completed spatial union

The supplied scalar stream and its explicit Cauchy modulus scale the actual
union Cauchy stream term by term. Original pairing homogeneity identifies the
resulting mixed limit. Pairing separation proves independence of both vector
representatives and equivalent scalar streams, including their moduli.

No representative or modulus is selected for a bare quotient real. The
carrier, spatial-limit law and original physical time are unchanged. This
does not assert unrestricted RC-module or continuum Hilbert/QFT structure.
-/

import YMGap.Continuum.BF4SpatialUnionRealScalarCauchy
import YMGap.Continuum.BF4SpatialUnionLinearLaws

namespace YMGap.Continuum.BF4SpatialUnionCompletedRealScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry (completedZero)
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionLinearLaws
open YMGap.Continuum.BF4SpatialUnionRealScalarCauchy
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner pairSequence_converges)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs

theorem representativeInner_realScalar_left (s : CReal) (cs : QCauchy s.approx)
    (X Y : (D).Cauchy) :
    Equiv (representativeInner PD (realScalarCauchy hw0 hw1 hsmall hd hs s cs X) Y)
      (mul s (representativeInner PD X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_smul_left hw0 hw1 hsmall hd hs (s.approx n) (X.seq n) (Y.seq n))
    (pairSequence_converges PD (realScalarCauchy hw0 hw1 hsmall hd hs s cs X) Y)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self s) (pairSequence_converges PD X Y))

theorem realScalarCauchy_pairing (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (y : V) :
    B (Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 hsmall hd hs s cs X)) y =
      RCmul (Quotient.mk crealSetoid s) (B (Quotient.mk (D).completionSetoid X) y) := by
  refine Quotient.inductionOn y ?_
  exact fun Y => Quotient.sound
    (representativeInner_realScalar_left hw0 hw1 hsmall hd hs s cs X Y)

/-- Independence of the two original vector streams and the supplied scalar moduli. -/
theorem realScalarCauchy_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hst : Equiv s t) (X Y : (D).Cauchy)
    (hX : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 hsmall hd hs s cs X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 hsmall hd hs t ct Y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [realScalarCauchy_pairing, realScalarCauchy_pairing, hX,
    show Quotient.mk crealSetoid s = Quotient.mk crealSetoid t from Quotient.sound hst]

def completedRealSmul (s : CReal) (cs : QCauchy s.approx) : V → V :=
  Quotient.lift
    (fun X => Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 hsmall hd hs s cs X))
    (fun X Y h => realScalarCauchy_congr hw0 hw1 hsmall hd hs
      s s cs cs (Equiv.refl s) X Y (Quotient.sound h))

theorem completedRealSmul_mk (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    completedRealSmul hw0 hw1 hsmall hd hs s cs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (realScalarCauchy hw0 hw1 hsmall hd hs s cs X) := rfl

theorem completedInner_realSmul_left (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B (completedRealSmul hw0 hw1 hsmall hd hs s cs x) y =
      RCmul (Quotient.mk crealSetoid s) (B x y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_pairing hw0 hw1 hsmall hd hs s cs X y

theorem completedInner_realSmul_right (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    B x (completedRealSmul hw0 hw1 hsmall hd hs s cs y) =
      RCmul (Quotient.mk crealSetoid s) (B x y) := by
  rw [completedInner_symm hw0 hw1 hsmall hd hs x, completedInner_realSmul_left,
    completedInner_symm hw0 hw1 hsmall hd hs y x]

theorem completedRealSmul_congr (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (hst : Equiv s t) (x : V) :
    completedRealSmul hw0 hw1 hsmall hd hs s cs x =
      completedRealSmul hw0 hw1 hsmall hd hs t ct x := by
  refine Quotient.inductionOn x ?_
  exact fun X => realScalarCauchy_congr hw0 hw1 hsmall hd hs s t cs ct hst X X rfl

theorem completedRealSmul_ofQ' (q : Q') (cq : QCauchy (ofQ' q).approx) (x : V) :
    completedRealSmul hw0 hw1 hsmall hd hs (ofQ' q) cq x =
      completedSmul hw0 hw1 hsmall hd hs q x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [completedInner_realSmul_left, completedInner_smul_left]

theorem completedRealSmul_one (c : QCauchy cone.approx) (x : V) :
    completedRealSmul hw0 hw1 hsmall hd hs cone c x = x :=
  (completedRealSmul_ofQ' hw0 hw1 hsmall hd hs 1 c x).trans
    (completedSmul_one hw0 hw1 hsmall hd hs x)

theorem completedRealSmul_zero (c : QCauchy czero.approx) (x : V) :
    completedRealSmul hw0 hw1 hsmall hd hs czero c x = completedZero hw0 hw1 hsmall hd hs :=
  (completedRealSmul_ofQ' hw0 hw1 hsmall hd hs 0 c x).trans
    (completedSmul_zero hw0 hw1 hsmall hd hs x)

theorem completedRealSmul_add (s : CReal) (cs : QCauchy s.approx) (x y : V) :
    completedRealSmul hw0 hw1 hsmall hd hs s cs (completedAdd hw0 hw1 hsmall hd hs x y) =
      completedAdd hw0 hw1 hsmall hd hs (completedRealSmul hw0 hw1 hsmall hd hs s cs x)
        (completedRealSmul hw0 hw1 hsmall hd hs s cs y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_add_left, completedInner_realSmul_left]
  refine Quotient.inductionOn₂ (B x test) (B y test) ?_
  exact fun X Y => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_add_eqv (s.approx n) (X.approx n) (Y.approx n)))

#print axioms representativeInner_realScalar_left
#print axioms realScalarCauchy_pairing
#print axioms realScalarCauchy_congr
#print axioms completedRealSmul
#print axioms completedRealSmul_mk
#print axioms completedInner_realSmul_left
#print axioms completedInner_realSmul_right
#print axioms completedRealSmul_congr
#print axioms completedRealSmul_ofQ'
#print axioms completedRealSmul_one
#print axioms completedRealSmul_zero
#print axioms completedRealSmul_add

end YMGap.Continuum.BF4SpatialUnionCompletedRealScalar
