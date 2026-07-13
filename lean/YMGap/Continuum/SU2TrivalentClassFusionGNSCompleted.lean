/-
# Completed SU(2) trivalent class-fusion block

Three overlapping fundamental class modes fuse associatively into the four
character coordinates `(chi_0,chi_1,chi_2,chi_3)`.  This file equips those
coordinates with the exact orthonormal Haar form and completes the diagonal
heat-kernel transfer with spectrum `1,1/8,1/256,1/32768`.

The all-fundamental packet is `2 chi_1 + chi_3`.  Its fused Haar norm is five,
not the unit norm of the disjoint eight-coordinate tensor basis.  That failed
normalization is recorded as a checked fence.  A corrected section of the
four-coordinate quotient is constructed explicitly, and the two fusion
associations agree after GNS completion.

Honest scope: these are central class-function coefficients.  The coefficient
two records fusion multiplicity but does not separate the two copies into a
higher-valence vertex intertwiner space.  That multiplicity-space contraction
is the next nonabelian lattice layer.
-/

import YMGap.Continuum.SU2BigonGlobalVacuumGNSCompleted

namespace YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted

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
open YMGap.Continuum.SU2SharedLinkFusionBlock
open YMGap.Continuum.SU2SharedLinkFusionGNSCompleted
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum

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

private theorem q_sub_add_cancel (a b : Q') :
    (a + (-b)) + b ≈ a := by
  refine Q'.eqv_trans _ (a + ((-b) + b)) _
    (Q'.add_assoc_eqv a (-b) b) ?_
  exact Q'.eqv_trans _ (a + 0) _
    (Q'.add_eqv_congr_left a _ _ (Q'.neg_add_self_eqv b))
    (QPoly.q_add_zero_eqv a)

/-! ## Four exact character coordinates -/

def tripleIrrepGram (a b : TripleIrrep) : Q' :=
  a.1 * b.1 +
    (a.2.1 * b.2.1 + (a.2.2.1 * b.2.2.1 + a.2.2.2 * b.2.2.2))

def tripleIrrepTransfer (a : TripleIrrep) : TripleIrrep :=
  (a.1, (eighth * a.2.1,
    (quadraticEigen * a.2.2.1, cubicEigen * a.2.2.2)))

private def tripleUnitLine : GNSData := qWeightGNS 1 (by decide)

abbrev tripleIrrepGNS : GNSData :=
  gnsProduct tripleUnitLine
    (gnsProduct tripleUnitLine (gnsProduct tripleUnitLine tripleUnitLine))

theorem tripleIrrepGNS_B_eq_gram (a b : TripleIrrep) :
    tripleIrrepGNS.B a b ≈ tripleIrrepGram a b := by
  unfold tripleIrrepGNS gnsProduct tripleUnitLine qWeightGNS tripleIrrepGram
  exact QPoly.q_add_congr (Q'.one_mul_eqv _)
    (QPoly.q_add_congr (Q'.one_mul_eqv _)
      (QPoly.q_add_congr (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)))

/-! ## Normalization fence and corrected quotient section -/

def tripleDisjointGram (a b : TripleVec) : Q' :=
  tensorGram a.1 b.1 + tensorGram a.2 b.2

theorem triple_fusion_not_disjoint_isometry :
    ¬ (tripleIrrepGram
          (fuseFirstPairThenThird tripleFundamentalMode)
          (fuseFirstPairThenThird tripleFundamentalMode) ≈
        tripleDisjointGram tripleFundamentalMode tripleFundamentalMode) := by
  unfold tripleIrrepGram tripleDisjointGram fuseFirstPairThenThird
    tripleFundamentalMode fusionCollapse vacuumCoord fundamentalCoord
    quadraticCoord tensorGram
  decide

/-- A literal representative of all four class-character coordinates. -/
def tripleFusionSection (a : TripleIrrep) : TripleVec :=
  (fusionSection (a.1, (a.2.1 + (-a.2.2.2), a.2.2.1)),
    fusionSection (0, (0, a.2.2.2)))

theorem tripleFusion_section (a : TripleIrrep) :
    TripleIrrepEq (fuseFirstPairThenThird (tripleFusionSection a)) a := by
  let r : IrrepVec := (a.1, (a.2.1 + (-a.2.2.2), a.2.2.1))
  let d : IrrepVec := (0, (0, a.2.2.2))
  have hr : IrrepEq (fusionCollapse (fusionSection r)) r :=
    fusionCollapse_section r
  have hd : IrrepEq (fusionCollapse (fusionSection d)) d :=
    fusionCollapse_section d
  change TripleIrrepEq
    ((fusionCollapse (fusionSection r)).1 +
        (fusionCollapse (fusionSection d)).2.1,
      ((fusionCollapse (fusionSection r)).2.1 +
          ((fusionCollapse (fusionSection d)).1 +
            (fusionCollapse (fusionSection d)).2.2),
        ((fusionCollapse (fusionSection r)).2.2 +
          (fusionCollapse (fusionSection d)).2.1,
          (fusionCollapse (fusionSection d)).2.2))) a
  unfold TripleIrrepEq
  refine ⟨?_, ?_, ?_, hd.2.2⟩
  · refine Q'.eqv_trans _ (r.1 + d.2.1) _
      (QPoly.q_add_congr hr.1 hd.2.1) ?_
    dsimp [r, d]
    exact QPoly.q_add_zero_eqv _
  · refine Q'.eqv_trans _ (r.2.1 + (d.1 + d.2.2)) _
      (QPoly.q_add_congr hr.2.1 (QPoly.q_add_congr hd.1 hd.2.2)) ?_
    dsimp [r, d]
    refine Q'.eqv_trans _ ((a.2.1 + (-a.2.2.2)) + a.2.2.2) _
      (Q'.add_eqv_congr_left _ _ _ (QPoly.q_zero_add_eqv _)) ?_
    exact q_sub_add_cancel _ _
  · refine Q'.eqv_trans _ (r.2.2 + d.2.1) _
      (QPoly.q_add_congr hr.2.2 hd.2.1) ?_
    dsimp [r, d]
    exact QPoly.q_add_zero_eqv _

def correctedTripleTransfer (a : TripleVec) : TripleVec :=
  tripleFusionSection (tripleIrrepTransfer (fuseFirstPairThenThird a))

theorem correctedTripleTransfer_intertwines (a : TripleVec) :
    TripleIrrepEq (fuseFirstPairThenThird (correctedTripleTransfer a))
      (tripleIrrepTransfer (fuseFirstPairThenThird a)) :=
  tripleFusion_section _

/-! ## Dense transfer laws -/

theorem tripleIrrepTransfer_map_veq {a b : TripleIrrep}
    (h : tripleIrrepGNS.veq a b) :
    tripleIrrepGNS.veq (tripleIrrepTransfer a) (tripleIrrepTransfer b) :=
  ⟨h.1, Q'.mul_eqv_congr_left eighth _ _ h.2.1,
    Q'.mul_eqv_congr_left quadraticEigen _ _ h.2.2.1,
    Q'.mul_eqv_congr_left cubicEigen _ _ h.2.2.2⟩

theorem tripleIrrepTransfer_map_sub (a b : TripleIrrep) :
    tripleIrrepGNS.veq
      (tripleIrrepTransfer (tripleIrrepGNS.sub a b))
      (tripleIrrepGNS.sub (tripleIrrepTransfer a) (tripleIrrepTransfer b)) := by
  unfold GNSData.sub tripleIrrepTransfer tripleIrrepGNS gnsProduct
    tripleUnitLine qWeightGNS
  exact ⟨Q'.eqv_refl _, by ring_qeqv, by ring_qeqv, by ring_qeqv⟩

theorem tripleIrrepTransfer_selfAdjoint (a b : TripleIrrep) :
    tripleIrrepGNS.B (tripleIrrepTransfer a) b ≈
      tripleIrrepGNS.B a (tripleIrrepTransfer b) := by
  refine Q'.eqv_trans _ _ _ (tripleIrrepGNS_B_eq_gram _ b) ?_
  refine Q'.eqv_trans _ (tripleIrrepGram a (tripleIrrepTransfer b)) _ (by
    unfold tripleIrrepGram tripleIrrepTransfer
    ring_qeqv) ?_
  exact Q'.eqv_symm (tripleIrrepGNS_B_eq_gram a _)

private theorem scaled_diag_nonneg (s x : Q') (hs : (0 : Q') ≤ s) :
    (0 : Q') ≤ (s * x) * x := by
  have hbase : (0 : Q') ≤ s * (x * x) :=
    Q'.mul_nonneg _ _ hs (q_mul_self_nonneg x)
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv s x x)))

theorem tripleIrrepTransfer_positive (a : TripleIrrep) :
    (0 : Q') ≤ tripleIrrepGNS.B (tripleIrrepTransfer a) a := by
  have hraw : (0 : Q') ≤ tripleIrrepGram (tripleIrrepTransfer a) a := by
    unfold tripleIrrepGram tripleIrrepTransfer
    exact Q'.zero_le_add _ _ (q_mul_self_nonneg a.1)
      (Q'.zero_le_add _ _
        (scaled_diag_nonneg eighth a.2.1 (by decide))
        (Q'.zero_le_add _ _
          (scaled_diag_nonneg quadraticEigen a.2.2.1 (by decide))
          (scaled_diag_nonneg cubicEigen a.2.2.2 (by decide))))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv (Q'.eqv_symm (tripleIrrepGNS_B_eq_gram _ a)))

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

theorem tripleIrrepTransfer_contraction (a : TripleIrrep) :
    tripleIrrepGNS.B (tripleIrrepTransfer a) (tripleIrrepTransfer a) ≤
      tripleIrrepGNS.B a a := by
  have hraw : tripleIrrepGram (tripleIrrepTransfer a) (tripleIrrepTransfer a) ≤
      tripleIrrepGram a a := by
    unfold tripleIrrepGram tripleIrrepTransfer
    exact Q'.add_le_add (Q'.le_refl' _)
      (Q'.add_le_add
        (scaled_square_le eighth a.2.1 (by decide) (by decide))
        (Q'.add_le_add
          (scaled_square_le quadraticEigen a.2.2.1 (by decide) (by decide))
          (scaled_square_le cubicEigen a.2.2.2 (by decide) (by decide))))
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (tripleIrrepGNS_B_eq_gram _ _)) hraw)
    (Q'.le_of_eqv (Q'.eqv_symm (tripleIrrepGNS_B_eq_gram a a)))

theorem tripleIrrepTransfer_distSq_contraction (a b : TripleIrrep) :
    tripleIrrepGNS.distSqQ (tripleIrrepTransfer a) (tripleIrrepTransfer b) ≤
      tripleIrrepGNS.distSqQ a b := by
  have hsub := tripleIrrepTransfer_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (tripleIrrepGNS.B_diag_congr hsub))
    (tripleIrrepTransfer_contraction (tripleIrrepGNS.sub a b))

/-! ## Constructive completion -/

def applyTripleCauchy
    (x : CauchyGNS tripleIrrepGNS) : CauchyGNS tripleIrrepGNS where
  seq := fun n => tripleIrrepTransfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (tripleIrrepTransfer_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyTripleCauchy_null {x y : CauchyGNS tripleIrrepGNS}
    (h : CauchyNull tripleIrrepGNS x y) :
    CauchyNull tripleIrrepGNS (applyTripleCauchy x) (applyTripleCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (tripleIrrepTransfer_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

def completedTripleTransfer :
    GNSCompletionSpace tripleIrrepGNS → GNSCompletionSpace tripleIrrepGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid tripleIrrepGNS) (applyTripleCauchy x))
    (fun _ _ h => Quotient.sound (applyTripleCauchy_null h))

theorem completedTripleTransfer_embed (a : TripleIrrep) :
    completedTripleTransfer (embedV tripleIrrepGNS a) =
      embedV tripleIrrepGNS (tripleIrrepTransfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem completedTripleTransfer_selfAdjoint
    (x y : GNSCompletionSpace tripleIrrepGNS) :
    tripleIrrepGNS.cinnerCompl (completedTripleTransfer x) y =
      tripleIrrepGNS.cinnerCompl x (completedTripleTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (tripleIrrepGNS.cInnerSeq (applyTripleCauchy u) v n))
    (bSeq := fun n => CReal.ofQ'
      (tripleIrrepGNS.cInnerSeq u (applyTripleCauchy v) n))
    (fun n => PositiveTimeCompression.lifted_eqv
      (tripleIrrepTransfer_selfAdjoint (u.seq n) (v.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedTripleTransfer_positive
    (x : GNSCompletionSpace tripleIrrepGNS) :
    CReal.RCnonneg
      (tripleIrrepGNS.cinnerCompl (completedTripleTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (tripleIrrepGNS.cinnerRep (applyTripleCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => tripleIrrepTransfer_positive (u.seq _))

theorem completedTripleTransfer_contraction
    (x : GNSCompletionSpace tripleIrrepGNS) :
    CReal.RCle
      (tripleIrrepGNS.cinnerCompl (completedTripleTransfer x)
        (completedTripleTransfer x))
      (tripleIrrepGNS.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (fun epsilon hepsilon => ⟨0, fun n _ => Q'.le_trans' _ _ _
      (tripleIrrepTransfer_contraction (u.seq n))
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩)

def tripleVacuum : TripleIrrep := (1, (0, (0, 0)))

def completedTripleTransferOperator :
    TransferOperator tripleIrrepGNS.gnsComplete where
  T := completedTripleTransfer
  vacuum := embedV tripleIrrepGNS tripleVacuum
  selfAdjoint := completedTripleTransfer_selfAdjoint
  positive := completedTripleTransfer_positive
  contraction := completedTripleTransfer_contraction

/-! ## Completed associative gluing and exact packet -/

theorem completed_triple_fusion_associative (a : TripleVec) :
    embedV tripleIrrepGNS (fuseFirstPairThenThird a) =
      embedV tripleIrrepGNS (fuseLastPairThenFirst a) := by
  apply Quotient.sound
  exact embed_null_of_rad tripleIrrepGNS
    (rad_of_veq tripleIrrepGNS (third_gluing_associative a))

theorem completed_triple_section_retract (a : TripleIrrep) :
    embedV tripleIrrepGNS (fuseFirstPairThenThird (tripleFusionSection a)) =
      embedV tripleIrrepGNS a := by
  apply Quotient.sound
  exact embed_null_of_rad tripleIrrepGNS
    (rad_of_veq tripleIrrepGNS (tripleFusion_section a))

def tripleFundamentalPacket : TripleIrrep := (0, (2, (0, 1)))

theorem completed_tripleFundamental_fuses :
    embedV tripleIrrepGNS
        (fuseFirstPairThenThird tripleFundamentalMode) =
      embedV tripleIrrepGNS tripleFundamentalPacket := by
  apply Quotient.sound
  exact embed_null_of_rad tripleIrrepGNS
    (rad_of_veq tripleIrrepGNS tripleFundamental_fusion_multiplicity)

theorem tripleFundamentalPacket_transfer_exact :
    TripleIrrepEq (tripleIrrepTransfer tripleFundamentalPacket)
      (0, (eighth * 2, (0, cubicEigen))) := by
  unfold TripleIrrepEq tripleIrrepTransfer tripleFundamentalPacket
  decide

theorem completed_tripleFundamental_transfer :
    completedTripleTransferOperator.T
        (embedV tripleIrrepGNS tripleFundamentalPacket) =
      embedV tripleIrrepGNS
        ((0, (eighth * 2, (0, cubicEigen))) : TripleIrrep) := by
  refine Eq.trans (completedTripleTransfer_embed tripleFundamentalPacket) ?_
  apply Quotient.sound
  exact embed_null_of_rad tripleIrrepGNS
    (rad_of_veq tripleIrrepGNS tripleFundamentalPacket_transfer_exact)

theorem completed_tripleVacuum_ne_zero :
    embedV tripleIrrepGNS tripleVacuum ≠
      embedV tripleIrrepGNS tripleIrrepGNS.zero := by
  intro h
  have hr : tripleIrrepGNS.rad tripleVacuum tripleIrrepGNS.zero :=
    constCauchy_null_imp_rad tripleIrrepGNS (Quotient.exact h)
  have hz : tripleIrrepGNS.B tripleVacuum tripleVacuum ≈ 0 :=
    (tripleIrrepGNS.rad_zero_iff tripleVacuum).mp hr
  have hn : tripleIrrepGNS.B tripleVacuum tripleVacuum ≈ 1 :=
    Q'.eqv_trans _ _ _
      (tripleIrrepGNS_B_eq_gram tripleVacuum tripleVacuum) (by decide)
  exact (by decide : ¬ ((1 : Q') ≈ 0))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hn) hz)

end YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted

#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.triple_fusion_not_disjoint_isometry
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.tripleFusion_section
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.correctedTripleTransfer_intertwines
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.tripleIrrepTransfer_distSq_contraction
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.completedTripleTransfer
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.completedTripleTransferOperator
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.completed_triple_fusion_associative
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.completed_triple_section_retract
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.completed_tripleFundamental_transfer
#print axioms YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted.completed_tripleVacuum_ne_zero
