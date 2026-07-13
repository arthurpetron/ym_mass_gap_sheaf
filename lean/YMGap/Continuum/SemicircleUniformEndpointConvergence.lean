/-
# Convergence of the uniform semicircle endpoint sums

The exact finite endpoint gap is imported from the frozen predecessor.  This
module proves that the gap vanishes and squeezes both independently refined
uniform endpoint sequences to `halfPi`.
-/

import YMGap.Continuum.SemicircleUniformEndpointGap

namespace YMGap.Continuum.SemicircleUniformEndpointConvergence

open YMGap.Constructive
open YMGap.Continuum.SemicircleRationalPolygon
open YMGap.Continuum.SemicirclePolygonMidpointBridge
open YMGap.Continuum.SemicirclePolygonMidpointValue
open YMGap.Continuum.SemicircleUniformEndpointGap

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm];
             omega))

def unitGapSeq (M : Nat) : CReal := CReal.ofQ' (unitGapQ M)

theorem unitGapSeq_converges_zero :
    CReal.ConvergesTo unitGapSeq CReal.czero := by
  intro epsilon hepsilon
  refine ⟨2 * epsilon.den, fun M hM => ?_⟩
  have hcut : unitGapQ M ≤ epsilon := by
    apply two_over_succ_le hepsilon
    omega
  refine ⟨0, fun _k _ => ?_⟩
  change unitGapQ M ≤ (0 : Q') + epsilon ∧
    (0 : Q') ≤ unitGapQ M + epsilon
  constructor
  · exact Q'.le_trans' _ _ _ hcut
      (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  · have hgap0 : (0 : Q') ≤ unitGapQ M := by
      rw [Q'.zero_le_iff_num_nonneg]
      unfold unitGapQ
      rw [Q'.mkPos_num]
      decide
    exact Q'.zero_le_add (unitGapQ M) epsilon hgap0 (Q'.le_of_lt hepsilon)

private theorem limitLe_refl (A : CReal) : LimitLe A A := by
  apply CReal.leRat_of_eventually
  refine ⟨0, fun k _ => ?_⟩
  exact Q'.le_of_eqv (Q'.add_neg_self_eqv (A.approx k))

private theorem limitLe_add {A B C D : CReal}
    (hAB : LimitLe A B) (hCD : LimitLe C D) :
    LimitLe (CReal.add A C) (CReal.add B D) := by
  have hsum := CReal.leRat_add hAB hCD
  have hzero : (0 + 0 : Q') ≤ 0 := Q'.le_of_eqv (by decide)
  have hsum0 := CReal.leRat_mono hsum hzero
  apply CReal.leRat_congr (b := CReal.add
    (CReal.add A (CReal.neg B)) (CReal.add C (CReal.neg D)))
  · intro k
    change ((A.approx k + C.approx k) + -(B.approx k + D.approx k)).eqv
      ((A.approx k + -(B.approx k)) + (C.approx k + -(D.approx k)))
    ring_qeqv
  · exact hsum0

private theorem equiv_limitLe_left {A A' B : CReal}
    (hAA' : CReal.Equiv A A') (h : LimitLe A' B) : LimitLe A B := by
  apply CReal.leRat_of_equiv (CReal.add_congr_left hAA')
  exact h

private theorem convergesTo_retarget {s : Nat → CReal} {L L' : CReal}
    (h : CReal.ConvergesTo s L) (hL : CReal.Equiv L L') :
    CReal.ConvergesTo s L' := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨Nstage, hstage⟩ := h q hq
  obtain ⟨Nequiv, hequiv⟩ := hL q hq
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napprox, hclose⟩ := hstage N hN
  refine ⟨max Napprox Nequiv, fun k hk => ?_⟩
  have hkA : Napprox ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hkE : Nequiv ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  obtain ⟨hsL, hLs⟩ := hclose k hkA
  obtain ⟨hLL', hL'L⟩ := hequiv k hkE
  have hqq : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  constructor
  · refine Q'.le_trans' _ _ _ hsL ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hLL') ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (L'.approx k) q q)
        (Q'.add_eqv_congr_left (L'.approx k) _ _ hqq))
  · refine Q'.le_trans' _ _ _ hL'L ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hLs) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((s N).approx k) q q)
        (Q'.add_eqv_congr_left ((s N).approx k) _ _ hqq))

def unitUpperSeq (M : Nat) : CReal :=
  CReal.add (polygonUpperSeq M) (unitGapSeq M)

theorem unitUpperSeq_converges_halfPi :
    CReal.ConvergesTo unitUpperSeq Pi.halfPi := by
  have h := TrigAddCReal.convergesTo_add
    polygonUpperSeq_converges_halfPi unitGapSeq_converges_zero
  have hzero : CReal.Equiv (CReal.add Pi.halfPi CReal.czero) Pi.halfPi :=
    TrigAdd.equiv_of_approx_eqv (fun k =>
      Q'.eqv_of_eq (Q'.add_zero' (Pi.halfPi.approx k)))
  exact convergesTo_retarget h hzero

private theorem unitLeft_le_unitUpper (M : Nat) :
    LimitLe (unitLeftSeq M) (unitUpperSeq M) := by
  have hright := unitRight_le_polygonUpper M M
  have hadd := limitLe_add hright (limitLe_refl (unitGapSeq M))
  exact equiv_limitLe_left (unit_endpoint_gap_equiv M) hadd

/-- The independently refined uniform left endpoint sums converge to the
Machin-identified value `halfPi`. -/
theorem unitLeftSeq_converges_halfPi :
    CReal.ConvergesTo unitLeftSeq Pi.halfPi := by
  apply convergesTo_of_limitBracket
    polygonLowerSeq_converges_halfPi unitUpperSeq_converges_halfPi
  intro M
  exact ⟨polygonLower_le_unitLeft M M, unitLeft_le_unitUpper M⟩

private theorem right_equiv_left_add_neg_gap (M : Nat) :
    CReal.Equiv (unitRightSeq M)
      (CReal.add (unitLeftSeq M) (CReal.neg (unitGapSeq M))) := by
  have hsubst : CReal.Equiv
      (CReal.add (unitLeftSeq M) (CReal.neg (unitGapSeq M)))
      (CReal.add
        (CReal.add (unitRightSeq M) (unitGapSeq M))
        (CReal.neg (unitGapSeq M))) :=
    CReal.add_congr_left (unit_endpoint_gap_equiv M)
  have hcancel : CReal.Equiv
      (CReal.add
        (CReal.add (unitRightSeq M) (unitGapSeq M))
        (CReal.neg (unitGapSeq M)))
      (unitRightSeq M) :=
    TrigAdd.equiv_of_approx_eqv (fun k => by
      change (((unitRightSeq M).approx k + (unitGapSeq M).approx k) +
        -(unitGapSeq M).approx k).eqv ((unitRightSeq M).approx k)
      ring_qeqv)
  exact CReal.Equiv.symm (hsubst.trans hcancel)

/-- The independently refined uniform right endpoint sums converge to the
same value `halfPi`. -/
theorem unitRightSeq_converges_halfPi :
    CReal.ConvergesTo unitRightSeq Pi.halfPi := by
  have hneg := TrigAddCReal.convergesTo_neg unitGapSeq_converges_zero
  have hadd := TrigAddCReal.convergesTo_add unitLeftSeq_converges_halfPi hneg
  have hzero : CReal.Equiv
      (CReal.add Pi.halfPi (CReal.neg CReal.czero)) Pi.halfPi :=
    TrigAdd.equiv_of_approx_eqv (fun k => by
      change (Pi.halfPi.approx k + -(0 : Q')).eqv (Pi.halfPi.approx k)
      ring_qeqv)
  have haux : CReal.ConvergesTo
      (fun M => CReal.add (unitLeftSeq M) (CReal.neg (unitGapSeq M)))
      Pi.halfPi := convergesTo_retarget hadd hzero
  exact TrigAddCReal.convergesTo_congr_seq
    (fun M => CReal.Equiv.symm (right_equiv_left_add_neg_gap M)) haux

end YMGap.Continuum.SemicircleUniformEndpointConvergence

#print axioms YMGap.Continuum.SemicircleUniformEndpointConvergence.unitGapSeq_converges_zero
#print axioms YMGap.Continuum.SemicircleUniformEndpointConvergence.unitUpperSeq_converges_halfPi
#print axioms YMGap.Continuum.SemicircleUniformEndpointConvergence.unitLeftSeq_converges_halfPi
#print axioms YMGap.Continuum.SemicircleUniformEndpointConvergence.unitRightSeq_converges_halfPi
