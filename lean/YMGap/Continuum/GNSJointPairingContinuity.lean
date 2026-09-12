/-
# Joint continuity of pairings along constructive completion limits

Write each vector as its limit plus an error. The two fixed-vector cross
terms converge by the existing one-slot theorem; Cauchy--Schwarz makes the
error--error term null because both squared errors are null. No global
bound on an arbitrary family, square root, or representative choice is used.

The original Type-level outer moduli compute the error-pair rate. The
four-pairing identity then gives continuity of squared differences, ready
for the actual dense operator's nonexpansive bound to pass to completion.
-/

import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.RCBilinearDifference

namespace YMGap.Continuum.GNSJointPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

variable {D : GNSData}

/-- The explicit outer rate used by the existing completion convergence proof. -/
def limitRate (X : GeneralCompletionCauchy D) (epsilon : Q') : Nat :=
  X.mod (HalfPow.half * (HalfPow.half * epsilon))

theorem limit_close_at (X : GeneralCompletionCauchy D) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (p : Nat) (hp : limitRate X epsilon ≤ p) :
    ∃ N, ∀ n, N ≤ n → D.distSqQ ((X.pt p).seq n) (X.lim.seq n) ≤ epsilon := by
  let tiny := HalfPow.half * (HalfPow.half * epsilon)
  have htiny : (0 : Q') < tiny := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
  obtain ⟨P, hP⟩ := X.reindex.diag_converges tiny htiny
  let k := max P (X.mod tiny)
  obtain ⟨NK, hNK⟩ := hP k (Nat.le_max_left _ _)
  obtain ⟨NP, hNP⟩ := X.cauchy tiny htiny p (X.phi k) hp
    (Nat.le_trans (Nat.le_max_right _ _) (X.self_le_phi k))
  refine ⟨max NK NP, fun n hn => ?_⟩
  have ha := hNP n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hb := hNK n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have htri := D.distSqQ_triangle ((X.pt p).seq n) ((X.pt (X.phi k)).seq n) (X.lim.seq n)
  have hsum := Q'.add_le_add (Q'.add_le_add ha ha) (Q'.add_le_add hb hb)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ htri hsum) (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (ExpNeg.two_halves (HalfPow.half * epsilon))
      (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon)))

def pairedErrorRate (X Y : GeneralCompletionCauchy D) (epsilon : Q') : Nat :=
  max (limitRate X epsilon) (limitRate Y epsilon)

/-- Both error norms are small at the SAME rational representative index;
Cauchy--Schwarz then bounds their cross pairing without any square root. -/
theorem pairedError_converges (X Y : GeneralCompletionCauchy D) :
    CReal.ConvergesTo (fun p => D.cinnerRep (D.subCauchy (X.pt p) X.lim)
      (D.subCauchy (Y.pt p) Y.lim)) CReal.czero := by
  intro epsilon hepsilon
  refine ⟨pairedErrorRate X Y epsilon, fun p hp => ?_⟩
  obtain ⟨NX, hNX⟩ := limit_close_at X epsilon hepsilon p (Nat.le_trans (Nat.le_max_left _ _) hp)
  obtain ⟨NY, hNY⟩ := limit_close_at Y epsilon hepsilon p (Nat.le_trans (Nat.le_max_right _ _) hp)
  let u := D.subCauchy (X.pt p) X.lim
  let v := D.subCauchy (Y.pt p) Y.lim
  refine ⟨max NX NY, fun n hn => ?_⟩
  let index := CReal.QMhat (D.cInnerSeq u v) (D.cInnerQCauchy u v) n
  have hindex : n ≤ index := CReal.self_le_QMhat _ _ n
  have hx := hNX index (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hn) hindex)
  have hy := hNY index (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hn) hindex)
  have habs := D.cs_term_bound (u.seq index) (v.seq index) epsilon epsilon epsilon
    hepsilon (Q'.le_of_lt hepsilon) hx hy (Q'.le_refl' _)
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs)
      (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  · apply Q'.le_add_of_sub_le
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
      (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) habs)

theorem difference_pairing (u u' v v' : CauchyGNS D) :
    CReal.Equiv (D.cinnerRep (D.subCauchy u u') (D.subCauchy v v'))
      (CReal.sub (CReal.sub (D.cinnerRep u v) (D.cinnerRep u' v))
        (CReal.sub (D.cinnerRep u v') (D.cinnerRep u' v'))) := by
  apply Quotient.exact (s := CReal.crealSetoid)
  let U := Quotient.mk (cauchySetoid D) u
  let U' := Quotient.mk (cauchySetoid D) u'
  let V := Quotient.mk (cauchySetoid D) v
  let V' := Quotient.mk (cauchySetoid D) v'
  change D.cinnerCompl (D.cSub U U') (D.cSub V V') =
    CReal.RCsub (CReal.RCsub (D.cinnerCompl U V) (D.cinnerCompl U' V))
      (CReal.RCsub (D.cinnerCompl U V') (D.cinnerCompl U' V'))
  rw [D.cinnerCompl_comm (D.cSub U U') (D.cSub V V'), D.cinnerCompl_cSub_left,
    D.cinnerCompl_comm V (D.cSub U U'), D.cinnerCompl_comm V' (D.cSub U U'),
    D.cinnerCompl_cSub_left, D.cinnerCompl_cSub_left]

private theorem q_sub_add (a b : Q') : (a + -b) + b ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv b)) (Q'.eqv_of_eq (Q'.add_zero' a)))

private theorem restore (a b c d : CReal) :
    CReal.Equiv (CReal.add (CReal.add (CReal.sub (CReal.sub a b) (CReal.sub c d)) b)
      (CReal.sub c d)) a := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) (Q'.eqv_trans _ _ _
    (Q'.add_swap_inner _ _ _ _) (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (q_sub_add _ _) (Q'.neg_add_self_eqv _))
      (Q'.eqv_of_eq (Q'.add_zero' _))))

private theorem joint_split (u u' v v' : CauchyGNS D) :
    CReal.Equiv (CReal.add
      (CReal.add (D.cinnerRep (D.subCauchy u u') (D.subCauchy v v')) (D.cinnerRep u' v))
      (CReal.sub (D.cinnerRep u v') (D.cinnerRep u' v'))) (D.cinnerRep u v) := by
  refine CReal.Equiv.trans ?_ (restore (D.cinnerRep u v) (D.cinnerRep u' v)
    (D.cinnerRep u v') (D.cinnerRep u' v'))
  exact Quotient.exact (congrArg (fun z : CReal.RC =>
    CReal.RCadd (CReal.RCadd z (Quotient.mk CReal.crealSetoid (D.cinnerRep u' v)))
      (CReal.RCsub (Quotient.mk CReal.crealSetoid (D.cinnerRep u v'))
        (Quotient.mk CReal.crealSetoid (D.cinnerRep u' v'))))
    (Quotient.sound (difference_pairing u u' v v')))

private theorem converges_sub {a b : Nat → CReal} {A B : CReal}
    (ha : CReal.ConvergesTo a A) (hb : CReal.ConvergesTo b B) :
    CReal.ConvergesTo (fun n => CReal.sub (a n) (b n)) (CReal.sub A B) :=
  CReal.convergesTo_add ha (CReal.convergesTo_neg hb)

/-- Joint pairing continuity for the actual representative-family limits. -/
theorem pairing_converges (X Y : GeneralCompletionCauchy D) :
    CReal.ConvergesTo (fun n => D.cinnerRep (X.pt n) (Y.pt n))
      (D.cinnerRep X.lim Y.lim) := by
  have h := CReal.convergesTo_add
    (CReal.convergesTo_add (pairedError_converges X Y) (D.cinnerRep_continuous_right Y X.lim))
    (converges_sub (D.cinnerRep_continuous_left X Y.lim)
      (CReal.convergesTo_const (D.cinnerRep X.lim Y.lim)))
  have hlimit : CReal.Equiv
      (CReal.add (CReal.add CReal.czero (D.cinnerRep X.lim Y.lim))
        (CReal.sub (D.cinnerRep X.lim Y.lim) (D.cinnerRep X.lim Y.lim)))
      (D.cinnerRep X.lim Y.lim) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.eqv_of_eq (Q'.zero_add' _)) (Q'.add_neg_self_eqv _)) (Q'.eqv_of_eq (Q'.add_zero' _))
  exact TrigAddCReal.convergesTo_congr_seq (fun n => joint_split (X.pt n) X.lim (Y.pt n) Y.lim)
    (CReal.convergesTo_limit_congr h hlimit)

/-- Squared differences converge without losing their contraction constant. -/
theorem difference_converges (X Y : GeneralCompletionCauchy D) :
    CReal.ConvergesTo (fun n => D.cinnerRep (D.subCauchy (X.pt n) (Y.pt n))
      (D.subCauchy (X.pt n) (Y.pt n)))
      (D.cinnerRep (D.subCauchy X.lim Y.lim) (D.subCauchy X.lim Y.lim)) := by
  have h := converges_sub
    (converges_sub (pairing_converges X X) (pairing_converges Y X))
    (converges_sub (pairing_converges X Y) (pairing_converges Y Y))
  exact TrigAddCReal.convergesTo_congr_seq
    (fun n => (difference_pairing (X.pt n) (Y.pt n) (X.pt n) (Y.pt n)).symm)
    (CReal.convergesTo_limit_congr h (difference_pairing X.lim Y.lim X.lim Y.lim).symm)

end YMGap.Continuum.GNSJointPairingContinuity

#print axioms YMGap.Continuum.GNSJointPairingContinuity.limitRate
#print axioms YMGap.Continuum.GNSJointPairingContinuity.limit_close_at
#print axioms YMGap.Continuum.GNSJointPairingContinuity.pairedErrorRate
#print axioms YMGap.Continuum.GNSJointPairingContinuity.pairedError_converges
#print axioms YMGap.Continuum.GNSJointPairingContinuity.difference_pairing
#print axioms YMGap.Continuum.GNSJointPairingContinuity.pairing_converges
#print axioms YMGap.Continuum.GNSJointPairingContinuity.difference_converges
