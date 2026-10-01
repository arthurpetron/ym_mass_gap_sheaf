/-
# Full Hermitian pairing of the original all-Rows Cayley-product limit

The finite products are the already constructed complex Wilson-bond Cayley
iterates.  Their original represented Rows have a computed all-tail limit.
The original row-pairing modulus passes the real sum and imaginary difference
through that limit, retaining all four mixed terms.  This is at fixed nome
and width, with no physical-time or continuum identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
import YMGap.Continuum.BF4WilsonAllNomeLogOperator
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGraphNorm

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
  (RepresentedCauchy rowPoint limit)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
  (pairingModulus row_pairing_bound constantRows constantRows_point limit_constantRows)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
  (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows CauchySequence ofRows rowState value
    value_ofRows value_ofState inner inner_value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productRows productRows_pin productSequence productLimitRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (quarter quarter_positive four_quarters)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "I" => inner hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Four pairing errors at one quarter each consume exactly one tolerance. -/
private theorem rc_pair_errors (a b : RC) (q : Q') :
    RCadd (RCadd a (rat q)) (RCadd b (rat q)) =
      RCadd (RCadd a b) (RCadd (rat q) (rat q)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2)))
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 2)))
      (by decide) (fun | 0 => A.approx n | 1 => C.approx n | _ => q)))

private theorem rc_four_errors (a : RC) (e : Q') :
    RCadd (RCadd a (RCadd (rat (quarter e)) (rat (quarter e))))
      (RCadd (rat (quarter e)) (rat (quarter e))) = RCadd a (rat e) := by
  have h (u v : RC) : RCadd (RCadd u v) v = RCadd u (RCadd v v) := by
    refine Quotient.inductionOn₂ u v ?_
    intro U W
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.var 1))
        (.add (.var 0) (.add (.var 1) (.var 1)))
        (by decide) (fun | 0 => U.approx n | _ => W.approx n)))
  rw [h a (RCadd (rat (quarter e)) (rat (quarter e))), four_quarters]

/-- Original represented pairings have a computed two-term modulus through
their limits.  This is the combination needed by the real Hermitian part. -/
theorem sum_pairing_limits_eq
    (R S U W A C E F : RepresentedCauchy hw0 hw1 (width := width))
    (hstage : ∀ n,
      RCadd (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n))
        (B (rowPoint hw0 hw1 U n) (rowPoint hw0 hw1 W n)) =
      RCadd (B (rowPoint hw0 hw1 A n) (rowPoint hw0 hw1 C n))
        (B (rowPoint hw0 hw1 E n) (rowPoint hw0 hw1 F n))) :
    RCadd (B (limit hw0 hw1 R) (limit hw0 hw1 S))
      (B (limit hw0 hw1 U) (limit hw0 hw1 W)) =
    RCadd (B (limit hw0 hw1 A) (limit hw0 hw1 C))
      (B (limit hw0 hw1 E) (limit hw0 hw1 F)) := by
  have direction
      (P Q T Z P₂ Q₂ T₂ Z₂ : RepresentedCauchy hw0 hw1 (width := width))
      (hs : ∀ n,
        RCadd (B (rowPoint hw0 hw1 P n) (rowPoint hw0 hw1 Q n))
          (B (rowPoint hw0 hw1 T n) (rowPoint hw0 hw1 Z n)) =
        RCadd (B (rowPoint hw0 hw1 P₂ n) (rowPoint hw0 hw1 Q₂ n))
          (B (rowPoint hw0 hw1 T₂ n) (rowPoint hw0 hw1 Z₂ n))) :
      RCle
        (RCadd (B (limit hw0 hw1 P) (limit hw0 hw1 Q))
          (B (limit hw0 hw1 T) (limit hw0 hw1 Z)))
        (RCadd (B (limit hw0 hw1 P₂) (limit hw0 hw1 Q₂))
          (B (limit hw0 hw1 T₂) (limit hw0 hw1 Z₂))) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro epsilon hepsilon
    let q := quarter epsilon
    have hq : (0 : Q') < q := quarter_positive hepsilon
    let n := max
      (max (pairingModulus hw0 hw1 P Q q) (pairingModulus hw0 hw1 T Z q))
      (max (pairingModulus hw0 hw1 P₂ Q₂ q) (pairingModulus hw0 hw1 T₂ Z₂ q))
    have hPQ := (row_pairing_bound hw0 hw1 P Q q hq n (by dsimp [n]; omega)).2
    have hTZ := (row_pairing_bound hw0 hw1 T Z q hq n (by dsimp [n]; omega)).2
    have hP'Q' := (row_pairing_bound hw0 hw1 P₂ Q₂ q hq n (by dsimp [n]; omega)).1
    have hT'Z' := (row_pairing_bound hw0 hw1 T₂ Z₂ q hq n (by dsimp [n]; omega)).1
    have hleft := RCadd_le_add hPQ hTZ
    have hright := RCadd_le_add hP'Q' hT'Z'
    rw [rc_pair_errors] at hleft hright
    rw [hs n] at hleft
    have htotal := RCle_trans hleft
      (RCadd_le_add hright
        (RCle_refl (RCadd (rat q) (rat q))))
    change RCle _
      (RCadd (RCadd
        (RCadd (B (limit hw0 hw1 P₂) (limit hw0 hw1 Q₂))
          (B (limit hw0 hw1 T₂) (limit hw0 hw1 Z₂)))
        (RCadd (rat (quarter epsilon)) (rat (quarter epsilon))))
        (RCadd (rat (quarter epsilon)) (rat (quarter epsilon)))) at htotal
    rwa [rc_four_errors] at htotal
  apply RCle_antisymm
  · exact direction R S U W A C E F hstage
  · exact direction A C E F R S U W (fun n => (hstage n).symm)

private theorem cross_add_of_sub_eq (a b c d : RC)
    (h : RCsub a b = RCsub c d) : RCadd a d = RCadd c b := by
  have left : RCadd (RCsub a b) (RCadd b d) = RCadd a d := by
    refine Quotient.inductionOn₃ a b d ?_
    intro A C D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.var 2)))
        (.add (.var 0) (.var 2))
        (by decide) (fun | 0 => A.approx n | 1 => C.approx n | _ => D.approx n)))
  have right : RCadd (RCsub c d) (RCadd b d) = RCadd c b := by
    refine Quotient.inductionOn₃ c d b ?_
    intro C D A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.var 1)))
        (.add (.var 0) (.var 2))
        (by decide) (fun | 0 => C.approx n | 1 => D.approx n | _ => A.approx n)))
  calc
    RCadd a d = RCadd (RCsub a b) (RCadd b d) := left.symm
    _ = RCadd (RCsub c d) (RCadd b d) := congrArg (fun z => RCadd z (RCadd b d)) h
    _ = RCadd c b := right

private theorem sub_eq_of_cross_add (a b c d : RC)
    (h : RCadd a d = RCadd c b) : RCsub a b = RCsub c d := by
  have left : RCsub (RCadd a d) (RCadd b d) = RCsub a b := by
    refine Quotient.inductionOn₃ a b d ?_
    intro A C D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 2))
          (.neg (.add (.var 1) (.var 2))))
        (.add (.var 0) (.neg (.var 1)))
        (by decide) (fun | 0 => A.approx n | 1 => C.approx n | _ => D.approx n)))
  have right : RCsub (RCadd c b) (RCadd b d) = RCsub c d := by
    refine Quotient.inductionOn₃ c b d ?_
    intro C A D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1))
          (.neg (.add (.var 1) (.var 2))))
        (.add (.var 0) (.neg (.var 2)))
        (by decide) (fun | 0 => C.approx n | 1 => A.approx n | _ => D.approx n)))
  calc
    RCsub a b = RCsub (RCadd a d) (RCadd b d) := left.symm
    _ = RCsub (RCadd c b) (RCadd b d) := congrArg (fun z => RCsub z (RCadd b d)) h
    _ = RCsub c d := right

private def realRows (C : CauchySequence hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.representedRows hw0 hw1
    (BF4WilsonAllNomeComplexTimeSector.realSequence hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.sectorSequence hw0 hw1 C))

private def imagRows (C : CauchySequence hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.representedRows hw0 hw1
    (BF4WilsonAllNomeComplexTimeSector.imagSequence hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.sectorSequence hw0 hw1 C))

private theorem realRows_point (C : CauchySequence hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (realRows hw0 hw1 C) n =
      (value hw0 hw1 (ofRows hw0 hw1 (C.seq n))).1 := by
  rw [realRows,BF4WilsonAllNomeTimeSector.representedRows_point,value_ofRows]
  rfl

private theorem imagRows_point (C : CauchySequence hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (imagRows hw0 hw1 C) n =
      (value hw0 hw1 (ofRows hw0 hw1 (C.seq n))).2 := by
  rw [imagRows,BF4WilsonAllNomeTimeSector.representedRows_point,value_ofRows]
  rfl

private theorem realRows_limit (C : CauchySequence hw0 hw1 (width := width)) :
    limit hw0 hw1 (realRows hw0 hw1 C) =
      (value hw0 hw1 (ofRows hw0 hw1
        (BF4WilsonAllNomeComplexBondOSCompletion.limitRows hw0 hw1 C))).1 := by
  rw [realRows,BF4WilsonAllNomeComplexBondOSCompletion.limitRows,
    BF4WilsonAllNomeComplexBondOSCompletion.ofRows_rowsOfState,value_ofState]
  rfl

private theorem imagRows_limit (C : CauchySequence hw0 hw1 (width := width)) :
    limit hw0 hw1 (imagRows hw0 hw1 C) =
      (value hw0 hw1 (ofRows hw0 hw1
        (BF4WilsonAllNomeComplexBondOSCompletion.limitRows hw0 hw1 C))).2 := by
  rw [imagRows,BF4WilsonAllNomeComplexBondOSCompletion.limitRows,
    BF4WilsonAllNomeComplexBondOSCompletion.ofRows_rowsOfState,value_ofState]
  rfl

private def constantReal (X : Rows hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  constantRows hw0 hw1
    (representative hw0 hw1 (rowState hw0 hw1 X).1.range)

private def constantImag (X : Rows hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  constantRows hw0 hw1
    (representative hw0 hw1 (rowState hw0 hw1 X).2.range)

private theorem constantReal_point (X : Rows hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (constantReal hw0 hw1 X) n =
      (value hw0 hw1 (ofRows hw0 hw1 X)).1 := by
  rw [constantReal,constantRows_point,representative_pin,value_ofRows]
  rfl

private theorem constantImag_point (X : Rows hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (constantImag hw0 hw1 X) n =
      (value hw0 hw1 (ofRows hw0 hw1 X)).2 := by
  rw [constantImag,constantRows_point,representative_pin,value_ofRows]
  rfl

private theorem constantReal_limit (X : Rows hw0 hw1 (width := width)) :
    limit hw0 hw1 (constantReal hw0 hw1 X) =
      (value hw0 hw1 (ofRows hw0 hw1 X)).1 := by
  rw [constantReal,limit_constantRows,representative_pin,value_ofRows]
  rfl

private theorem constantImag_limit (X : Rows hw0 hw1 (width := width)) :
    limit hw0 hw1 (constantImag hw0 hw1 X) =
      (value hw0 hw1 (ofRows hw0 hw1 X)).2 := by
  rw [constantImag,limit_constantRows,representative_pin,value_ofRows]
  rfl

/-- Full Hermitian pairing is preserved by each finite actual dyadic Cayley
product.  The two inputs use the same dyadic step and power. -/
theorem finite_product_pairing (X Y : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    I (productValue hw0 hw1 X t ht n) (productValue hw0 hw1 Y t ht n) =
      I (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y) := by
  have iterate_pairing (s : Q') (hs : (0 : Q') < s) (x y : H) :
      ∀ k : Nat,
      I (iterate hw0 hw1 s hs x k) (iterate hw0 hw1 s hs y k) = I x y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        change I
          (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1 s hs
            (iterate hw0 hw1 s hs x k))
          (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1 s hs
            (iterate hw0 hw1 s hs y k)) = I x y
        rw [BF4WilsonAllNomeComplexBondOSScaledCayley.pairing_preserved,ih]
  exact iterate_pairing (step t n) (step_pos t ht n)
    (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y) (2^n)

/-- The full original Hermitian form survives the computed all-Rows limit.
The real sum and imaginary cross difference are transported together; no
individual real component of a finite Cayley iterate is claimed invariant. -/
theorem productLimit_pairing (X Y : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) :
    I (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht))
      (ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht)) =
    I (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y) := by
  let CX := productSequence hw0 hw1 X t ht
  let CY := productSequence hw0 hw1 Y t ht
  have hfinite (n : Nat) := finite_product_pairing hw0 hw1 X Y t ht n
  have hstage (n : Nat) :
      I (ofRows hw0 hw1 (CX.seq n)) (ofRows hw0 hw1 (CY.seq n)) =
        I (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y) := by
    change I (ofRows hw0 hw1 (productRows hw0 hw1 X t ht n))
      (ofRows hw0 hw1 (productRows hw0 hw1 Y t ht n)) = _
    rw [productRows_pin,productRows_pin]
    exact hfinite n
  apply Prod.ext
  · rw [inner_value,inner_value]
    change RCadd
      (B (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht))).1
        (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht))).1)
      (B (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht))).2
        (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht))).2) = _
    have h := sum_pairing_limits_eq hw0 hw1
        (realRows hw0 hw1 CX) (realRows hw0 hw1 CY)
        (imagRows hw0 hw1 CX) (imagRows hw0 hw1 CY)
        (constantReal hw0 hw1 X) (constantReal hw0 hw1 Y)
        (constantImag hw0 hw1 X) (constantImag hw0 hw1 Y) (fun n => by
          rw [realRows_point,realRows_point,imagRows_point,imagRows_point,
            constantReal_point,constantReal_point,
            constantImag_point,constantImag_point]
          have hf := congrArg Prod.fst (hstage n)
          simpa only [inner_value,BF4WilsonAllNomeComplexification.inner] using hf)
    rw [realRows_limit,realRows_limit,imagRows_limit,imagRows_limit,
      constantReal_limit,constantReal_limit,constantImag_limit,constantImag_limit] at h
    exact h
  · rw [inner_value,inner_value]
    change RCsub
      (B (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht))).1
        (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht))).2)
      (B (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht))).2
        (value hw0 hw1 (ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht))).1) = _
    have h := sum_pairing_limits_eq hw0 hw1
        (realRows hw0 hw1 CX) (imagRows hw0 hw1 CY)
        (constantImag hw0 hw1 X) (constantReal hw0 hw1 Y)
        (constantReal hw0 hw1 X) (constantImag hw0 hw1 Y)
        (imagRows hw0 hw1 CX) (realRows hw0 hw1 CY) (fun n => by
          rw [realRows_point,imagRows_point,constantImag_point,constantReal_point,
            constantReal_point,constantImag_point,imagRows_point,realRows_point]
          apply cross_add_of_sub_eq
          have hf := congrArg Prod.snd (hstage n)
          simpa only [inner_value,BF4WilsonAllNomeComplexification.inner] using hf)
    rw [realRows_limit,imagRows_limit,constantImag_limit,constantReal_limit,
      constantReal_limit,constantImag_limit,imagRows_limit,realRows_limit] at h
    exact sub_eq_of_cross_add _ _ _ _ h

/-- The choice-free quotient limit map preserves the ORIGINAL full Hermitian
pairing for all physical complex bond classes. -/
theorem limitMap_pairing_preserved (t : Q') (ht : (0 : Q') < t) (x y : H) :
    I (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht x)
      (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht y) =
      I x y := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  refine Quotient.inductionOn₂ x₁ x₂ ?_
  intro X₁ X₂
  refine Quotient.inductionOn₂ y₁ y₂ ?_
  intro Y₁ Y₂
  change I
    (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht
      (ofRows hw0 hw1 (X₁,X₂)))
    (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht
      (ofRows hw0 hw1 (Y₁,Y₂))) =
    I (ofRows hw0 hw1 (X₁,X₂)) (ofRows hw0 hw1 (Y₁,Y₂))
  rw [BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap_ofRows,
    BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap_ofRows]
  exact productLimit_pairing hw0 hw1 (X₁,X₂) (Y₁,Y₂) t ht

/-- Pairing preservation gives an exact isometry of the SAME original
completed squared distance; no inverse or time-composition law is used. -/
theorem limitMap_distance (t : Q') (ht : (0 : Q') < t) (x y : H) :
    BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
      (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht x)
      (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht y) =
    BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1 x y := by
  rw [BF4WilsonAllNomeComplexBondOSGraphNorm.distance_pairing,
    BF4WilsonAllNomeComplexBondOSGraphNorm.distance_pairing,
    limitMap_pairing_preserved,limitMap_pairing_preserved,
    limitMap_pairing_preserved,limitMap_pairing_preserved]

/-- The actual limit map is faithful on the physical quotient.  This does
not assert that its range is all of the carrier. -/
theorem limitMap_injective (t : Q') (ht : (0 : Q') < t) {x y : H}
    (h : BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht x =
      BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht y) :
    x = y := by
  apply BF4WilsonAllNomeComplexBondOSCayley.eq_of_pairings hw0 hw1
  intro z
  calc
    I x z = I
        (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht x)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht z) :=
      (limitMap_pairing_preserved hw0 hw1 t ht x z).symm
    _ = I
        (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht y)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht z) :=
      congrArg (fun u => I u
        (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht z)) h
    _ = I y z := limitMap_pairing_preserved hw0 hw1 t ht y z

#print axioms sum_pairing_limits_eq
#print axioms finite_product_pairing
#print axioms productLimit_pairing
#print axioms limitMap_pairing_preserved
#print axioms limitMap_distance
#print axioms limitMap_injective

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
