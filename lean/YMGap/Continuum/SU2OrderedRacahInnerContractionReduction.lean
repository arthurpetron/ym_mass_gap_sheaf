/-
# Peeling one common inner contraction from a right channel

An ordered right channel of positive inner order is obtained by one Cayley
`Omega` contraction followed by the right channel on the reduced labels
`(b-1,c-1)`.  The universal monomial transvectant recurrence gives an exact
two-branch formula.  This is the structural induction step that propagates
the already-proved endpoint action into the interior.
-/

import YMGap.Continuum.SU2OrderedRacahInteriorReducedEndpointCoefficient
import YMGap.Continuum.SU2TransvectantMonomialRecurrence

namespace YMGap.Continuum.SU2OrderedRacahInnerContractionReduction

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMonomialRecurrence
open YMGap.Continuum.SU2DirectRightFixedOutputSections

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

/-- Remove one common inner contraction from a positive-order physical right
channel.  The intermediate and final labels, and the outer contraction order,
are unchanged. -/
def reducePositiveInnerRightChannel {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p) :
    FixedRightCGChannel a (b - 1) (c - 1) d where
  p := q.p - 1
  p_le := by
    have h := Nat.le_min.mp q.p_le
    apply Nat.le_min.mpr
    constructor <;> omega
  r := q.r
  r_le := by
    have h := Nat.le_min.mp q.r_le
    have hk := Nat.le_min.mp q.p_le
    apply Nat.le_min.mpr
    constructor
    · exact h.1
    · omega
  degree_eq := by
    have h := q.degree_eq
    have hk := Nat.le_min.mp q.p_le
    omega

theorem reduced_intermediate_eq {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p) :
    (reducePositiveInnerRightChannel q hp).intermediate = q.intermediate := by
  unfold reducePositiveInnerRightChannel FixedRightCGChannel.intermediate
  change (b - 1) + (c - 1) - 2 * (q.p - 1) =
    b + c - 2 * q.p
  have h := Nat.le_min.mp q.p_le
  omega

theorem reduced_inner_order_eq {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p) :
    (reducePositiveInnerRightChannel q hp).p = q.p - 1 := rfl

private theorem tprod_inner_recurrence {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) :
    BForm2Eqv
      (tprod (mono i)
        (transvect b c q.p (tprod (mono j) (mono l))))
      (badd
        (bscale (Q'.ofNat (j * (c - l)))
          (tprod (mono i)
            (transvect (b - 1) (c - 1) (q.p - 1)
              (tprod (mono (j - 1)) (mono l)))))
        (bscale (-(Q'.ofNat ((b - j) * l)))
          (tprod (mono i)
            (transvect (b - 1) (c - 1) (q.p - 1)
              (tprod (mono j) (mono (l - 1))))))) := by
  intro x y
  let U := transvect (b - 1) (c - 1) (q.p - 1)
    (tprod (mono (j - 1)) (mono l)) y
  let V := transvect (b - 1) (c - 1) (q.p - 1)
    (tprod (mono j) (mono (l - 1))) y
  have hinner := transvect_succ_monomial b c (q.p - 1) j l y
  rw [show q.p - 1 + 1 = q.p by omega] at hinner
  have hinner' : transvect b c q.p (tprod (mono j) (mono l)) y ≈
      Q'.ofNat (j * (c - l)) * U +
        (-(Q'.ofNat ((b - j) * l))) * V := by
    simpa only [U, V] using hinner
  unfold badd bscale
  change mono i x * transvect b c q.p (tprod (mono j) (mono l)) y ≈
    Q'.ofNat (j * (c - l)) * (mono i x * U) +
      (-(Q'.ofNat ((b - j) * l))) * (mono i x * V)
  refine Q'.eqv_trans _
    (mono i x *
      (Q'.ofNat (j * (c - l)) * U +
        (-(Q'.ofNat ((b - j) * l))) * V)) _
    (Q'.mul_eqv_congr_left _ _ _ hinner') ?_
  ring_qeqv

/-- **One-contraction induction formula.**  On every monomial coordinate, a
positive-order right channel is the exact two-branch linear combination of
the reduced-label right channel at order `p-1`. -/
theorem triRight_positive_inner_reduction {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l s : Nat) :
    triRight a b c d q.intermediate
        (mono i) (mono j) (mono l) s ≈
      Q'.ofNat (j * (c - l)) *
          triRight a (b - 1) (c - 1) d q.intermediate
            (mono i) (mono (j - 1)) (mono l) s +
        (-(Q'.ofNat ((b - j) * l))) *
          triRight a (b - 1) (c - 1) d q.intermediate
            (mono i) (mono j) (mono (l - 1)) s := by
  let u := reducePositiveInnerRightChannel q hp
  have hintermediate : u.intermediate = q.intermediate :=
    reduced_intermediate_eq q hp
  have hinnerOrder : couplingOrder (b - 1) (c - 1) q.intermediate = q.p - 1 := by
    rw [← hintermediate]
    exact fixedRight_inner_couplingOrder u
  have houterOrder : couplingOrder a q.intermediate d = q.r :=
    fixedRight_outer_couplingOrder q
  have htensor := tprod_inner_recurrence q hp i j l
  have hcongr := transvect_congr a q.intermediate q.r htensor s
  have hadd := transvect_add a q.intermediate q.r
    (bscale (Q'.ofNat (j * (c - l)))
      (tprod (mono i)
        (transvect (b - 1) (c - 1) (q.p - 1)
          (tprod (mono (j - 1)) (mono l)))))
    (bscale (-(Q'.ofNat ((b - j) * l)))
      (tprod (mono i)
        (transvect (b - 1) (c - 1) (q.p - 1)
          (tprod (mono j) (mono (l - 1)))))) s
  have hscale0 := transvect_scale a q.intermediate q.r
    (Q'.ofNat (j * (c - l)))
    (tprod (mono i)
      (transvect (b - 1) (c - 1) (q.p - 1)
        (tprod (mono (j - 1)) (mono l)))) s
  have hscale1 := transvect_scale a q.intermediate q.r
    (-(Q'.ofNat ((b - j) * l)))
    (tprod (mono i)
      (transvect (b - 1) (c - 1) (q.p - 1)
        (tprod (mono j) (mono (l - 1))))) s
  unfold triRight
  rw [fixedRight_inner_couplingOrder q, houterOrder,
    hinnerOrder]
  refine Q'.eqv_trans _ _ _ hcongr ?_
  refine Q'.eqv_trans _ _ _ hadd ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hscale0 hscale1) (Q'.eqv_refl _)

end YMGap.Continuum.SU2OrderedRacahInnerContractionReduction

#print axioms YMGap.Continuum.SU2OrderedRacahInnerContractionReduction.reduced_intermediate_eq
#print axioms YMGap.Continuum.SU2OrderedRacahInnerContractionReduction.triRight_positive_inner_reduction
