/-
# Exact four-valent SU(2) intertwiner multiplicity space

Four fundamental doublets have a two-dimensional invariant tensor space.
This file constructs it from the signed `epsilon` tensor on two indices,
derives the Gram matrix of two pairings by an exact sixteen-term sum, and
completes the four-link heat-kernel transfer on that multiplicity space.

The two pairing tensors have Gram matrix `[[4,2],[2,4]]`.  In the rational
coordinates `sum=A+B`, `difference=A-B` this becomes the orthogonal weighted
form `diag(3,1)` (the unscaled coordinate change avoids square roots).  Both
intertwiner channels acquire the derived eigenvalue `(1/8)^4 = 1/4096` and
remain distinct in the constructive GNS completion.

Honest scope: this closes the first nontrivial vertex multiplicity space.  A
general finite lattice still needs compatible contractions of such spaces at
all vertices and across arbitrary incident irreducible labels.
-/

import YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted

namespace YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Finite epsilon-tensor calculation -/

def epsilon : Bool → Bool → Q'
  | false, true => 1
  | true, false => -1
  | _, _ => 0

def pairingA (i j k l : Bool) : Q' := epsilon i j * epsilon k l
def pairingB (i j k l : Bool) : Q' := epsilon i k * epsilon j l
def pairingC (i j k l : Bool) : Q' := epsilon i l * epsilon j k

def sumBool (f : Bool → Q') : Q' := f false + f true

def tensorInner
    (f g : Bool → Bool → Bool → Bool → Q') : Q' :=
  sumBool (fun i => sumBool (fun j => sumBool (fun k => sumBool (fun l =>
    f i j k l * g i j k l))))

/-- The third pairing is linearly dependent: `C + A = B`. -/
theorem epsilon_pairing_relation (i j k l : Bool) :
    pairingC i j k l + pairingA i j k l ≈ pairingB i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;> decide

/-- Exact finite contraction of the two independent invariant tensors. -/
theorem epsilon_pairing_gram_exact :
    tensorInner pairingA pairingA ≈ 4 ∧
    tensorInner pairingA pairingB ≈ 2 ∧
    tensorInner pairingB pairingA ≈ 2 ∧
    tensorInner pairingB pairingB ≈ 4 := by
  unfold tensorInner sumBool pairingA pairingB epsilon
  decide

/-! ## Orthogonal rational multiplicity coordinates -/

abbrev PairingCoeff := Q' × Q'

def pairingToOrth (a : PairingCoeff) : Q' × Q' :=
  (a.1 + a.2, a.1 + (-a.2))

def pairingACoord : Q' × Q' := (1, 1)
def pairingBCoord : Q' × Q' := (1, -1)

private def weightThreeLine : GNSData := qWeightGNS 3 (by decide)
private def weightOneLine : GNSData := qWeightGNS 1 (by decide)

/-- Orthogonal coordinates for the two-dimensional invariant space. -/
abbrev intertwinerGNS : GNSData :=
  gnsProduct weightThreeLine weightOneLine

theorem pairing_basis_gram_in_gns :
    intertwinerGNS.B pairingACoord pairingACoord ≈ 4 ∧
    intertwinerGNS.B pairingACoord pairingBCoord ≈ 2 ∧
    intertwinerGNS.B pairingBCoord pairingACoord ≈ 2 ∧
    intertwinerGNS.B pairingBCoord pairingBCoord ≈ 4 := by
  unfold intertwinerGNS gnsProduct weightThreeLine weightOneLine qWeightGNS
    pairingACoord pairingBCoord
  decide

/-- The exact tensor contraction and the constructive GNS form give the same
Gram matrix on the invariant pairing basis. -/
theorem tensor_and_gns_gram_agree :
    tensorInner pairingA pairingA ≈
        intertwinerGNS.B pairingACoord pairingACoord ∧
    tensorInner pairingA pairingB ≈
        intertwinerGNS.B pairingACoord pairingBCoord ∧
    tensorInner pairingB pairingA ≈
        intertwinerGNS.B pairingBCoord pairingACoord ∧
    tensorInner pairingB pairingB ≈
        intertwinerGNS.B pairingBCoord pairingBCoord := by
  exact ⟨Q'.eqv_trans _ _ _ epsilon_pairing_gram_exact.1
      (Q'.eqv_symm pairing_basis_gram_in_gns.1),
    Q'.eqv_trans _ _ _ epsilon_pairing_gram_exact.2.1
      (Q'.eqv_symm pairing_basis_gram_in_gns.2.1),
    Q'.eqv_trans _ _ _ epsilon_pairing_gram_exact.2.2.1
      (Q'.eqv_symm pairing_basis_gram_in_gns.2.2.1),
    Q'.eqv_trans _ _ _ epsilon_pairing_gram_exact.2.2.2
      (Q'.eqv_symm pairing_basis_gram_in_gns.2.2.2)⟩

/-! ## Four-link transfer on the multiplicity space -/

def fourLegEigen : Q' :=
  (eighth * eighth) * (eighth * eighth)

theorem fourLegEigen_exact :
    fourLegEigen ≈ Q'.mkPos 1 4096 (by decide) := by decide

def intertwinerTransfer (a : Q' × Q') : Q' × Q' :=
  (fourLegEigen * a.1, fourLegEigen * a.2)

theorem intertwinerTransfer_map_veq {a b : Q' × Q'}
    (h : intertwinerGNS.veq a b) :
    intertwinerGNS.veq (intertwinerTransfer a) (intertwinerTransfer b) :=
  ⟨Q'.mul_eqv_congr_left fourLegEigen _ _ h.1,
    Q'.mul_eqv_congr_left fourLegEigen _ _ h.2⟩

theorem intertwinerTransfer_map_sub (a b : Q' × Q') :
    intertwinerGNS.veq
      (intertwinerTransfer (intertwinerGNS.sub a b))
      (intertwinerGNS.sub (intertwinerTransfer a) (intertwinerTransfer b)) := by
  unfold GNSData.sub intertwinerTransfer intertwinerGNS gnsProduct
    weightThreeLine weightOneLine qWeightGNS
  exact ⟨by ring_qeqv, by ring_qeqv⟩

theorem intertwinerTransfer_selfAdjoint (a b : Q' × Q') :
    intertwinerGNS.B (intertwinerTransfer a) b ≈
      intertwinerGNS.B a (intertwinerTransfer b) := by
  unfold intertwinerGNS gnsProduct weightThreeLine weightOneLine qWeightGNS
    intertwinerTransfer
  ring_qeqv

private theorem scaled_diag_nonneg (s x : Q') (hs : (0 : Q') ≤ s) :
    (0 : Q') ≤ (s * x) * x := by
  have hbase : (0 : Q') ≤ s * (x * x) :=
    Q'.mul_nonneg _ _ hs (q_mul_self_nonneg x)
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv s x x)))

theorem intertwinerTransfer_positive (a : Q' × Q') :
    (0 : Q') ≤ intertwinerGNS.B (intertwinerTransfer a) a := by
  unfold intertwinerGNS gnsProduct weightThreeLine weightOneLine qWeightGNS
    intertwinerTransfer
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (scaled_diag_nonneg fourLegEigen a.1 (by decide)))
    (Q'.mul_nonneg _ _ (by decide)
      (scaled_diag_nonneg fourLegEigen a.2 (by decide)))

private theorem scaled_square_le (s x : Q')
    (hs0 : (0 : Q') ≤ s) (hs1 : s ≤ (1 : Q')) :
    (s * x) * (s * x) ≤ x * x := by
  have hsq := Q'.mul_le_mul_of_nonneg_right s 1 s hs1 hs0
  have hsq' := Q'.mul_le_mul_of_nonneg_left s 1 1 hs1 (by decide)
  have hss : s * s ≤ (1 : Q') := Q'.le_trans' _ _ _ hsq hsq'
  have hm := Q'.mul_le_mul_of_nonneg_right
    (s * s) 1 (x * x) hss (q_mul_self_nonneg x)
  exact Q'.le_trans' _ ((s * s) * (x * x)) _
    (Q'.le_of_eqv (by ring_qeqv))
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv _)))

theorem intertwinerTransfer_contraction (a : Q' × Q') :
    intertwinerGNS.B (intertwinerTransfer a) (intertwinerTransfer a) ≤
      intertwinerGNS.B a a := by
  unfold intertwinerGNS gnsProduct weightThreeLine weightOneLine qWeightGNS
    intertwinerTransfer
  exact Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ 3
      (scaled_square_le fourLegEigen a.1 (by decide) (by decide)) (by decide))
    (Q'.mul_le_mul_of_nonneg_left _ _ 1
      (scaled_square_le fourLegEigen a.2 (by decide) (by decide)) (by decide))

theorem intertwinerTransfer_distSq_contraction (a b : Q' × Q') :
    intertwinerGNS.distSqQ (intertwinerTransfer a) (intertwinerTransfer b) ≤
      intertwinerGNS.distSqQ a b := by
  have hsub := intertwinerTransfer_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (intertwinerGNS.B_diag_congr hsub))
    (intertwinerTransfer_contraction (intertwinerGNS.sub a b))

/-! ## Constructive completion -/

def applyIntertwinerCauchy
    (x : CauchyGNS intertwinerGNS) : CauchyGNS intertwinerGNS where
  seq := fun n => intertwinerTransfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (intertwinerTransfer_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyIntertwinerCauchy_null {x y : CauchyGNS intertwinerGNS}
    (h : CauchyNull intertwinerGNS x y) :
    CauchyNull intertwinerGNS
      (applyIntertwinerCauchy x) (applyIntertwinerCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (intertwinerTransfer_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

def completedIntertwinerTransfer :
    GNSCompletionSpace intertwinerGNS → GNSCompletionSpace intertwinerGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid intertwinerGNS)
      (applyIntertwinerCauchy x))
    (fun _ _ h => Quotient.sound (applyIntertwinerCauchy_null h))

theorem completedIntertwinerTransfer_embed (a : Q' × Q') :
    completedIntertwinerTransfer (embedV intertwinerGNS a) =
      embedV intertwinerGNS (intertwinerTransfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem completedIntertwinerTransfer_selfAdjoint
    (x y : GNSCompletionSpace intertwinerGNS) :
    intertwinerGNS.cinnerCompl (completedIntertwinerTransfer x) y =
      intertwinerGNS.cinnerCompl x (completedIntertwinerTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (intertwinerGNS.cInnerSeq (applyIntertwinerCauchy u) v n))
    (bSeq := fun n => CReal.ofQ'
      (intertwinerGNS.cInnerSeq u (applyIntertwinerCauchy v) n))
    (fun n => PositiveTimeCompression.lifted_eqv
      (intertwinerTransfer_selfAdjoint (u.seq n) (v.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedIntertwinerTransfer_positive
    (x : GNSCompletionSpace intertwinerGNS) :
    CReal.RCnonneg
      (intertwinerGNS.cinnerCompl (completedIntertwinerTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (intertwinerGNS.cinnerRep (applyIntertwinerCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => intertwinerTransfer_positive (u.seq _))

theorem completedIntertwinerTransfer_contraction
    (x : GNSCompletionSpace intertwinerGNS) :
    CReal.RCle
      (intertwinerGNS.cinnerCompl (completedIntertwinerTransfer x)
        (completedIntertwinerTransfer x))
      (intertwinerGNS.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (fun epsilon hepsilon => ⟨0, fun n _ => Q'.le_trans' _ _ _
      (intertwinerTransfer_contraction (u.seq n))
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩)

/-! ## The two completed multiplicity channels -/

theorem completed_pairingA_transfer :
    completedIntertwinerTransfer (embedV intertwinerGNS pairingACoord) =
      embedV intertwinerGNS
        (fourLegEigen, fourLegEigen) := by
  refine Eq.trans (completedIntertwinerTransfer_embed pairingACoord) ?_
  apply Quotient.sound
  exact embed_null_of_rad intertwinerGNS
    (rad_of_veq intertwinerGNS ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩)

theorem completed_pairingB_transfer :
    completedIntertwinerTransfer (embedV intertwinerGNS pairingBCoord) =
      embedV intertwinerGNS
        (fourLegEigen, -fourLegEigen) := by
  refine Eq.trans (completedIntertwinerTransfer_embed pairingBCoord) ?_
  apply Quotient.sound
  exact embed_null_of_rad intertwinerGNS
    (rad_of_veq intertwinerGNS ⟨Q'.eqv_refl _, by
      unfold pairingBCoord intertwinerTransfer
      exact Q'.mul_neg_eqv fourLegEigen 1⟩)

theorem completed_pairings_distinct :
    embedV intertwinerGNS pairingACoord ≠
      embedV intertwinerGNS pairingBCoord := by
  intro h
  have hr : intertwinerGNS.rad pairingACoord pairingBCoord :=
    constCauchy_null_imp_rad intertwinerGNS (Quotient.exact h)
  have hfour :
      intertwinerGNS.B
          (intertwinerGNS.sub pairingACoord pairingBCoord)
          (intertwinerGNS.sub pairingACoord pairingBCoord) ≈ 4 := by
    unfold intertwinerGNS gnsProduct weightThreeLine weightOneLine qWeightGNS
      GNSData.sub pairingACoord pairingBCoord
    decide
  exact (by decide : ¬ ((4 : Q') ≈ 0))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hfour) hr)

end YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted

#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.epsilon_pairing_relation
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.epsilon_pairing_gram_exact
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.tensor_and_gns_gram_agree
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.fourLegEigen_exact
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.intertwinerTransfer_distSq_contraction
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.completedIntertwinerTransfer
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.completedIntertwinerTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.completedIntertwinerTransfer_positive
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.completedIntertwinerTransfer_contraction
#print axioms YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.completed_pairings_distinct
