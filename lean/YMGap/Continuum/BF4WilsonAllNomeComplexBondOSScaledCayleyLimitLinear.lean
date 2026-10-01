/-
# Complex linearity of the actual physical Cayley-product limit

Full Hermitian preservation has already been proved for the represented
product limit on the ORIGINAL Wilson-bond carrier.  Physical polarization
and definiteness turn that law into addition and complex-scalar compatibility,
with both supplied constructive scalar Cauchy witnesses retained.  Neither
surjectivity nor a physical-time group law is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGraphNorm
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion inner inner_posdef inner_conj_symm distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
  (inner_add_left inner_add_right inner_smul_left inner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
  (limitMap_pairing_preserved)
open YMGap.Continuum.BF4WilsonAllNomeComplexification
  (valueAdd valueMul valueConj scalarValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "I" => inner hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "D" => distance hw0 hw1
local notation "Z" => BF4WilsonAllNomeComplexBondOSCompletion.zero hw0 hw1 (width := width)

private theorem rc_cancel (a : RC) :
    RCsub (RCsub (RCadd a a) a) a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 0)) (.neg (.var 0)))
        (.neg (.var 0)))
      (.const 0) (by decide) (fun _ => X.approx n)))

/-- A physical zero-distance criterion specialized to the two pairings
actually supplied by Hermitian preservation. -/
private theorem eq_of_norm_cross (a b : H)
    (hnorm : I a a = I b b) (hcross : I a a = I a b) : a = b := by
  have hreverse : (I b a).1 = (I a b).1 := by
    rw [inner_conj_symm hw0 hw1 b a]
    rfl
  have hzero : D a b = RCzero := by
    calc
      D a b = RCsub (RCsub (RCadd (I a a).1 (I b b).1)
          (I a b).1) (I b a).1 :=
        BF4WilsonAllNomeComplexBondOSGraphNorm.distance_pairing hw0 hw1 a b
      _ = RCsub (RCsub (RCadd (I a a).1 (I a a).1)
          (I a a).1) (I a a).1 := by
            rw [← hnorm,hreverse,← hcross]
      _ = RCzero := rc_cancel _
  have hdiff : diff hw0 hw1 a b = Z := by
    apply (inner_posdef hw0 hw1 (diff hw0 hw1 a b)).mp
    change BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound.normSq hw0 hw1
      (diff hw0 hw1 a b) = RCzero
    exact (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit.distance_eq_norm_difference
      hw0 hw1 a b).symm.trans hzero
  calc
    a = A a Z :=
      (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_zero hw0 hw1 a).symm
    _ = A a (A (cneg hw0 hw1 b) b) :=
      congrArg (A a)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.neg_add hw0 hw1 b).symm
    _ = A (A a (cneg hw0 hw1 b)) b :=
      (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc hw0 hw1 _ _ _).symm
    _ = A Z b := congrArg (fun x => A x b) hdiff
    _ = b := BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.zero_add hw0 hw1 b

/-- A full-pairing-preserving endomap is additive on this SAME original
physical carrier, without requiring its range to be surjective. -/
private theorem add_of_pairing (G : H → H)
    (hG : ∀ x y : H, I (G x) (G y) = I x y) (x y : H) :
    G (A x y) = A (G x) (G y) := by
  let u := A x y
  let a := G u
  let b := A (G x) (G y)
  have hpair (z : H) : I b (G z) = I u z := by
    calc
      I b (G z) = valueAdd (I (G x) (G z)) (I (G y) (G z)) :=
        inner_add_left hw0 hw1 (G x) (G y) (G z)
      _ = valueAdd (I x z) (I y z) := by rw [hG x z,hG y z]
      _ = I u z := (inner_add_left hw0 hw1 x y z).symm
  have hnorm : I a a = I b b := by
    calc
      I a a = I u u := hG u u
      _ = valueAdd (I u x) (I u y) := inner_add_right hw0 hw1 u x y
      _ = valueAdd (I b (G x)) (I b (G y)) := by
        rw [hpair x,hpair y]
      _ = I b b := (inner_add_right hw0 hw1 b (G x) (G y)).symm
  have hcross : I a a = I a b := by
    calc
      I a a = I u u := hG u u
      _ = valueAdd (I u x) (I u y) := inner_add_right hw0 hw1 u x y
      _ = valueAdd (I a (G x)) (I a (G y)) := by
        rw [hG u x,hG u y]
      _ = I a b := (inner_add_right hw0 hw1 a (G x) (G y)).symm
  exact eq_of_norm_cross hw0 hw1 a b hnorm hcross

/-- A full-pairing-preserving endomap commutes with the actual complex
scalar action, preserving BOTH supplied QCauchy modulus witnesses. -/
private theorem smul_of_pairing (G : H → H)
    (hG : ∀ x y : H, I (G x) (G y) = I x y)
    (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : H) : G (S s t cs ct x) = S s t cs ct (G x) := by
  let u := S s t cs ct x
  let a := G u
  let b := S s t cs ct (G x)
  have hnorm : I a a = I b b := by
    calc
      I a a = I u u := hG u u
      _ = valueMul (scalarValue s t) (I u x) :=
        inner_smul_right hw0 hw1 s t cs ct u x
      _ = valueMul (scalarValue s t)
          (valueMul (valueConj (scalarValue s t)) (I x x)) := by
            rw [inner_smul_left hw0 hw1 s t cs ct x x]
      _ = valueMul (scalarValue s t)
          (valueMul (valueConj (scalarValue s t)) (I (G x) (G x))) := by
            rw [hG x x]
      _ = valueMul (scalarValue s t) (I b (G x)) := by
        rw [inner_smul_left hw0 hw1 s t cs ct (G x) (G x)]
      _ = I b b := (inner_smul_right hw0 hw1 s t cs ct b (G x)).symm
  have hcross : I a a = I a b := by
    calc
      I a a = I u u := hG u u
      _ = valueMul (scalarValue s t) (I u x) :=
        inner_smul_right hw0 hw1 s t cs ct u x
      _ = valueMul (scalarValue s t) (I a (G x)) := by rw [hG u x]
      _ = I a b := (inner_smul_right hw0 hw1 s t cs ct a (G x)).symm
  exact eq_of_norm_cross hw0 hw1 a b hnorm hcross

/-- The ACTUAL all-Rows dyadic Cayley-product limit preserves physical
addition on every completed complex Wilson-bond class. -/
theorem limitMap_add (t : Q') (ht : (0 : Q') < t) (x y : H) :
    F t ht (A x y) = A (F t ht x) (F t ht y) :=
  add_of_pairing hw0 hw1 (F t ht)
    (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing.limitMap_pairing_preserved
      hw0 hw1 t ht) x y

/-- Complex linearity of the ACTUAL physical limit, with both original
constructive real-scalar moduli retained as arguments. -/
theorem limitMap_smul (t : Q') (ht : (0 : Q') < t)
    (s u : CReal) (cs : QCauchy s.approx) (cu : QCauchy u.approx) (x : H) :
    F t ht (S s u cs cu x) = S s u cs cu (F t ht x) :=
  smul_of_pairing hw0 hw1 (F t ht)
    (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing.limitMap_pairing_preserved
      hw0 hw1 t ht) s u cs cu x

#print axioms limitMap_add
#print axioms limitMap_smul

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitLinear
