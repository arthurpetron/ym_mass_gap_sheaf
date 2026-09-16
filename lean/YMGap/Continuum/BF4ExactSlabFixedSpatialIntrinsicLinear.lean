/-
# Rational linear operations on the original physical reflected carrier

Addition and scalar multiplication retain the original finite signed spatial
probe presentations and their physical-face guards. Their algebraic laws are
proved through the SAME intrinsic reflected pairing, not by identifying lists
with different coefficient presentations. Pairing equality implies zero actual
reflected distance. The two quantitative distance estimates below supply
explicit-modulus completion consumers without assuming a new norm or form.

This is fixed-nome, fixed-width, fixed-cutoff dense algebra. No completed
vector-space structure, spectral gap, or continuum assertion is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm

/-- Literal concatenation of the actual signed physical presentations. -/
def addSpan {width : Nat} (x y : PhysicalSpan width) : PhysicalSpan width :=
  ⟨x.val ++ y.val, physical_append x.property y.property⟩

/-- Literal rational rescaling of the original coefficients. -/
def smulSpan {width : Nat} (c : Q') (x : PhysicalSpan width) : PhysicalSpan width :=
  ⟨scaleSpan c x.val, physical_scale c x.property⟩

/-- Equality tested against every actual physical presentation. -/
def PairingEq {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x y : PhysicalSpan width) : Prop :=
  ∀ z : PhysicalSpan width,
    Equiv (pairing hw0 hw1 width x.val z.val stage)
      (pairing hw0 hw1 width y.val z.val stage)

private def deltaSpan {width : Nat} (x y : PhysicalSpan width) : PhysicalSpan width :=
  ⟨difference x.val y.val, physical_difference x.property y.property⟩

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) :=
  Equiv_add ha (CReal.neg_congr hc)

private theorem sub_self (a : CReal) : Equiv (sub a a) czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (a.approx n))

private theorem zero_pairing {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (z : PhysicalSpan width) :
    Equiv (pairing hw0 hw1 width
      (BF4ExactSlabFixedSpatialCompletedPhysicalTime.zero width).val z.val stage) czero :=
  pairing_difference_self_left hw0 hw1 width [] z.val stage

section ActualForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width stage : Nat)

theorem pairingEq_refl (x : PhysicalSpan width) : PairingEq hw0 hw1 width stage x x :=
  fun _ => Equiv.refl _

theorem pairingEq_symm {x y : PhysicalSpan width}
    (h : PairingEq hw0 hw1 width stage x y) : PairingEq hw0 hw1 width stage y x :=
  fun z => Equiv.symm (h z)

theorem pairingEq_trans {x y z : PhysicalSpan width}
    (hxy : PairingEq hw0 hw1 width stage x y)
    (hyz : PairingEq hw0 hw1 width stage y z) : PairingEq hw0 hw1 width stage x z :=
  fun t => Equiv.trans (hxy t) (hyz t)

theorem pairingEq_add {x x' y y' : PhysicalSpan width}
    (hx : PairingEq hw0 hw1 width stage x x')
    (hy : PairingEq hw0 hw1 width stage y y') :
    PairingEq hw0 hw1 width stage (addSpan x y) (addSpan x' y') := by
  intro z
  exact Equiv.trans (pairing_add_left hw0 hw1 width x.val y.val z.val stage)
    (Equiv.trans (Equiv_add (hx z) (hy z))
      (Equiv.symm (pairing_add_left hw0 hw1 width x'.val y'.val z.val stage)))

theorem pairingEq_smul (c : Q') {x y : PhysicalSpan width}
    (h : PairingEq hw0 hw1 width stage x y) :
    PairingEq hw0 hw1 width stage (smulSpan c x) (smulSpan c y) := by
  intro z
  exact Equiv.trans (pairing_smul_left hw0 hw1 width c x.val z.val stage)
    (Equiv.trans (TrigSignedAdd.mul_congr_right (h z))
      (Equiv.symm (pairing_smul_left hw0 hw1 width c y.val z.val stage)))

/-- Tests against the physical difference give zero SAME-form distance. -/
theorem null_of_pairingEq {x y : PhysicalSpan width}
    (h : PairingEq hw0 hw1 width stage x y) :
    Equiv (distSq hw0 hw1 width stage x y) czero :=
  Equiv.trans (pairing_difference_left hw0 hw1 width x.val y.val
    (difference x.val y.val) stage)
    (Equiv.trans (sub_congr (h (deltaSpan x y)) (Equiv.refl _)) (sub_self _))

theorem pairingEq_of_null {x y : PhysicalSpan width}
    (h : Equiv (distSq hw0 hw1 width stage x y) czero) :
    PairingEq hw0 hw1 width stage x y :=
  pairing_null_left hw0 hw1 width stage h

/-- Diagonal replacement uses the already-proved symmetry of the physical form. -/
theorem diagonal_congr {x y : PhysicalSpan width}
    (h : PairingEq hw0 hw1 width stage x y) :
    Equiv (pairing hw0 hw1 width x.val x.val stage)
      (pairing hw0 hw1 width y.val y.val stage) :=
  Equiv.trans (h x)
    (Equiv.trans (pairing_symm hw0 hw1 width y.val x.val y.property x.property stage)
      (h y))

theorem addSpan_assoc (x y z : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (addSpan (addSpan x y) z) (addSpan x (addSpan y z)) := by
  intro t
  have hscalar : Equiv
      (add (add (pairing hw0 hw1 width x.val t.val stage)
        (pairing hw0 hw1 width y.val t.val stage)) (pairing hw0 hw1 width z.val t.val stage))
      (add (pairing hw0 hw1 width x.val t.val stage)
        (add (pairing hw0 hw1 width y.val t.val stage) (pairing hw0 hw1 width z.val t.val stage))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_assoc_eqv _ _ _)
  exact Equiv.trans (pairing_add_left hw0 hw1 width (x.val++y.val) z.val t.val stage)
    (Equiv.trans (Equiv_add (pairing_add_left hw0 hw1 width x.val y.val t.val stage) (Equiv.refl _))
      (Equiv.trans hscalar
        (Equiv.trans (Equiv_add (Equiv.refl _)
          (Equiv.symm (pairing_add_left hw0 hw1 width y.val z.val t.val stage)))
          (Equiv.symm (pairing_add_left hw0 hw1 width x.val (y.val++z.val) t.val stage)))))

theorem addSpan_comm (x y : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (addSpan x y) (addSpan y x) := by
  intro z
  have hscalar : Equiv
      (add (pairing hw0 hw1 width x.val z.val stage)
        (pairing hw0 hw1 width y.val z.val stage))
      (add (pairing hw0 hw1 width y.val z.val stage)
        (pairing hw0 hw1 width x.val z.val stage)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_comm_eqv
      ((pairing hw0 hw1 width x.val z.val stage).approx n)
      ((pairing hw0 hw1 width y.val z.val stage).approx n))
  exact Equiv.trans (pairing_add_left hw0 hw1 width x.val y.val z.val stage)
    (Equiv.trans hscalar
      (Equiv.symm (pairing_add_left hw0 hw1 width y.val x.val z.val stage)))

theorem zero_addSpan (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage
      (addSpan (BF4ExactSlabFixedSpatialCompletedPhysicalTime.zero width) x) x := by
  intro z
  exact Equiv.trans (pairing_add_left hw0 hw1 width [] x.val z.val stage)
    (Equiv.trans (Equiv_add (zero_pairing hw0 hw1 width stage z) (Equiv.refl _))
      (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' _))))

theorem neg_addSpan (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (addSpan (smulSpan (-1) x) x)
      (BF4ExactSlabFixedSpatialCompletedPhysicalTime.zero width) := by
  intro z
  have hscalar : Equiv
      (add (mul (ofQ' (-1)) (pairing hw0 hw1 width x.val z.val stage))
        (pairing hw0 hw1 width x.val z.val stage)) czero := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.const (-1)) (.var 0)) (.var 0)) (.const 0) (by decide)
      (fun _ => (pairing hw0 hw1 width x.val z.val stage).approx n)
  exact Equiv.trans (pairing_add_left hw0 hw1 width (scaleSpan (-1) x.val) x.val z.val stage)
    (Equiv.trans (Equiv_add (pairing_smul_left hw0 hw1 width (-1) x.val z.val stage) (Equiv.refl _))
      (Equiv.trans hscalar (Equiv.symm (zero_pairing hw0 hw1 width stage z))))

theorem smulSpan_one (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (smulSpan 1 x) x := by
  intro z
  exact Equiv.trans (pairing_smul_left hw0 hw1 width 1 x.val z.val stage)
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.one_mul_eqv _))

theorem smulSpan_zero (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (smulSpan 0 x)
      (BF4ExactSlabFixedSpatialCompletedPhysicalTime.zero width) := by
  intro z
  exact Equiv.trans (pairing_smul_left hw0 hw1 width 0 x.val z.val stage)
    (Equiv.trans (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv _))
      (Equiv.symm (zero_pairing hw0 hw1 width stage z)))

theorem smulSpan_mul (a b : Q') (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (smulSpan (a*b) x) (smulSpan a (smulSpan b x)) := by
  intro z
  exact Equiv.trans (pairing_smul_left hw0 hw1 width (a*b) x.val z.val stage)
    (Equiv.trans (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_assoc_eqv _ _ _))
      (Equiv.trans (TrigSignedAdd.mul_congr_right
        (Equiv.symm (pairing_smul_left hw0 hw1 width b x.val z.val stage)))
        (Equiv.symm (pairing_smul_left hw0 hw1 width a (scaleSpan b x.val) z.val stage))))

theorem smulSpan_add (c : Q') (x y : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (smulSpan c (addSpan x y))
      (addSpan (smulSpan c x) (smulSpan c y)) := by
  intro z
  exact Equiv.trans (pairing_smul_left hw0 hw1 width c (x.val++y.val) z.val stage)
    (Equiv.trans (TrigSignedAdd.mul_congr_right (pairing_add_left hw0 hw1 width x.val y.val z.val stage))
      (Equiv.trans (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_add_eqv _ _ _))
        (Equiv.trans (Equiv_add
          (Equiv.symm (pairing_smul_left hw0 hw1 width c x.val z.val stage))
          (Equiv.symm (pairing_smul_left hw0 hw1 width c y.val z.val stage)))
          (Equiv.symm (pairing_add_left hw0 hw1 width (scaleSpan c x.val) (scaleSpan c y.val) z.val stage)))))

theorem add_smulSpan (a b : Q') (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (smulSpan (a+b) x)
      (addSpan (smulSpan a x) (smulSpan b x)) := by
  intro z
  exact Equiv.trans (pairing_smul_left hw0 hw1 width (a+b) x.val z.val stage)
    (Equiv.trans (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_mul_eqv _ _ _))
      (Equiv.trans (Equiv_add
        (Equiv.symm (pairing_smul_left hw0 hw1 width a x.val z.val stage))
        (Equiv.symm (pairing_smul_left hw0 hw1 width b x.val z.val stage)))
        (Equiv.symm (pairing_add_left hw0 hw1 width (scaleSpan a x.val) (scaleSpan b x.val) z.val stage))))

theorem smulSpan_congr {a b : Q'} (h : Q'.eqv a b) (x : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (smulSpan a x) (smulSpan b x) := by
  intro z
  exact Equiv.trans (pairing_smul_left hw0 hw1 width a x.val z.val stage)
    (Equiv.trans (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_eqv_congr_right _ _ _ h))
      (Equiv.symm (pairing_smul_left hw0 hw1 width b x.val z.val stage)))

private theorem delta_add_pairingEq (x x' y y' : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (deltaSpan (addSpan x y) (addSpan x' y'))
      (addSpan (deltaSpan x x') (deltaSpan y y')) := by
  intro z
  have hscalar : Equiv
      (sub (add (pairing hw0 hw1 width x.val z.val stage) (pairing hw0 hw1 width y.val z.val stage))
        (add (pairing hw0 hw1 width x'.val z.val stage) (pairing hw0 hw1 width y'.val z.val stage)))
      (add (sub (pairing hw0 hw1 width x.val z.val stage) (pairing hw0 hw1 width x'.val z.val stage))
        (sub (pairing hw0 hw1 width y.val z.val stage) (pairing hw0 hw1 width y'.val z.val stage))) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))) (by decide)
      (fun
        | 0 => (pairing hw0 hw1 width x.val z.val stage).approx n
        | 1 => (pairing hw0 hw1 width x'.val z.val stage).approx n
        | 2 => (pairing hw0 hw1 width y.val z.val stage).approx n
        | _ => (pairing hw0 hw1 width y'.val z.val stage).approx n)
  exact Equiv.trans (pairing_difference_left hw0 hw1 width (x.val++y.val) (x'.val++y'.val) z.val stage)
    (Equiv.trans (sub_congr (pairing_add_left hw0 hw1 width x.val y.val z.val stage)
      (pairing_add_left hw0 hw1 width x'.val y'.val z.val stage))
      (Equiv.trans hscalar
        (Equiv.trans (Equiv_add
          (Equiv.symm (pairing_difference_left hw0 hw1 width x.val x'.val z.val stage))
          (Equiv.symm (pairing_difference_left hw0 hw1 width y.val y'.val z.val stage)))
          (Equiv.symm (pairing_add_left hw0 hw1 width
            (difference x.val x'.val) (difference y.val y'.val) z.val stage)))))

/-- The actual original reflected squared distance of sums is bounded by
twice each original squared distance. -/
theorem distSq_add (x x' y y' : PhysicalSpan width) :
    leEv (distSq hw0 hw1 width stage (addSpan x y) (addSpan x' y'))
      (add (add (distSq hw0 hw1 width stage x x') (distSq hw0 hw1 width stage x x'))
        (add (distSq hw0 hw1 width stage y y') (distSq hw0 hw1 width stage y y'))) := by
  let a : PhysicalSpan width := deltaSpan x x'
  let b : PhysicalSpan width := deltaSpan y y'
  let d : PhysicalSpan width := deltaSpan (addSpan x y) (addSpan x' y')
  let s : PhysicalSpan width := addSpan a b
  have hEq : PairingEq hw0 hw1 width stage d s :=
    delta_add_pairingEq hw0 hw1 width stage x x' y y'
  have hdiag : Equiv (pairing hw0 hw1 width d.val d.val stage)
      (pairing hw0 hw1 width s.val s.val stage) :=
    diagonal_congr hw0 hw1 width stage (x := d) (y := s) hEq
  have hbound : leEv (pairing hw0 hw1 width s.val s.val stage)
      (add (add (pairing hw0 hw1 width a.val a.val stage)
        (pairing hw0 hw1 width a.val a.val stage))
        (add (pairing hw0 hw1 width b.val b.val stage)
          (pairing hw0 hw1 width b.val b.val stage))) :=
    pairing_add_bound hw0 hw1 width a.val b.val a.property b.property stage
  change leEv (pairing hw0 hw1 width d.val d.val stage)
    (add (add (pairing hw0 hw1 width a.val a.val stage)
      (pairing hw0 hw1 width a.val a.val stage))
      (add (pairing hw0 hw1 width b.val b.val stage)
        (pairing hw0 hw1 width b.val b.val stage)))
  exact leEv_trans (leEv_of_equiv hdiag) hbound

private theorem delta_smul_pairingEq (c : Q') (x y : PhysicalSpan width) :
    PairingEq hw0 hw1 width stage (deltaSpan (smulSpan c x) (smulSpan c y))
      (smulSpan c (deltaSpan x y)) := by
  intro z
  have hscalar : Equiv
      (sub (mul (ofQ' c) (pairing hw0 hw1 width x.val z.val stage))
        (mul (ofQ' c) (pairing hw0 hw1 width y.val z.val stage)))
      (mul (ofQ' c) (sub (pairing hw0 hw1 width x.val z.val stage)
        (pairing hw0 hw1 width y.val z.val stage))) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
      (fun
        | 0 => c
        | 1 => (pairing hw0 hw1 width x.val z.val stage).approx n
        | _ => (pairing hw0 hw1 width y.val z.val stage).approx n)
  exact Equiv.trans (pairing_difference_left hw0 hw1 width (scaleSpan c x.val) (scaleSpan c y.val) z.val stage)
    (Equiv.trans (sub_congr (pairing_smul_left hw0 hw1 width c x.val z.val stage)
      (pairing_smul_left hw0 hw1 width c y.val z.val stage))
      (Equiv.trans hscalar
        (Equiv.trans (TrigSignedAdd.mul_congr_right
          (Equiv.symm (pairing_difference_left hw0 hw1 width x.val y.val z.val stage)))
          (Equiv.symm (pairing_smul_left hw0 hw1 width c (difference x.val y.val) z.val stage)))))

/-- Signed rational rescaling squares in the actual original diagonal. -/
theorem diagonal_smul (c : Q') (x : PhysicalSpan width) :
    Equiv (pairing hw0 hw1 width (smulSpan c x).val (smulSpan c x).val stage)
      (mul (ofQ' (c*c)) (pairing hw0 hw1 width x.val x.val stage)) :=
  Equiv.trans (pairing_smul_left hw0 hw1 width c x.val (scaleSpan c x.val) stage)
    (Equiv.trans (TrigSignedAdd.mul_congr_right (pairing_smul_right hw0 hw1 width c x.val x.val stage))
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

/-- No sign condition on the scalar is needed for exact squared-distance scaling. -/
theorem distSq_smul (c : Q') (x y : PhysicalSpan width) :
    Equiv (distSq hw0 hw1 width stage (smulSpan c x) (smulSpan c y))
      (mul (ofQ' (c*c)) (distSq hw0 hw1 width stage x y)) := by
  let a : PhysicalSpan width := deltaSpan x y
  let d : PhysicalSpan width := deltaSpan (smulSpan c x) (smulSpan c y)
  let s : PhysicalSpan width := smulSpan c a
  have hEq : PairingEq hw0 hw1 width stage d s :=
    delta_smul_pairingEq hw0 hw1 width stage c x y
  have hdiag : Equiv (pairing hw0 hw1 width d.val d.val stage)
      (pairing hw0 hw1 width s.val s.val stage) :=
    diagonal_congr hw0 hw1 width stage (x := d) (y := s) hEq
  have hscale : Equiv (pairing hw0 hw1 width s.val s.val stage)
      (mul (ofQ' (c*c)) (pairing hw0 hw1 width a.val a.val stage)) :=
    diagonal_smul hw0 hw1 width stage c a
  change Equiv (pairing hw0 hw1 width d.val d.val stage)
    (mul (ofQ' (c*c)) (pairing hw0 hw1 width a.val a.val stage))
  exact Equiv.trans hdiag hscale

end ActualForm

end YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.addSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.pairingEq_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.pairingEq_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.pairingEq_trans
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.pairingEq_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.pairingEq_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.null_of_pairingEq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.pairingEq_of_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.diagonal_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.addSpan_assoc
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.addSpan_comm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.zero_addSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.neg_addSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan_mul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.add_smulSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.distSq_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.diagonal_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear.distSq_smul
