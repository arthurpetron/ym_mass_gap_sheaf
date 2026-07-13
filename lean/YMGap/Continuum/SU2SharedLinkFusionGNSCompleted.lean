/-
# Completed GNS block for the first shared-link SU(2) fusion quotient

The literal disjoint two-plaquette carrier cannot be glued across a common
link: its Gram is not the shared Haar Gram, and its product transfer fails on
the double excitation even modulo the shared radical.  Those frozen no-go
theorems are re-exported here as the entrance fence.

The corrected gluing is the Clebsch--Gordan quotient

    (00,10,01,11) |-> (chi_0,chi_1,chi_2)
      = (00+11, 10+01, 11).

This file equips the three irreducible coordinates with their exact Haar GNS
form, constructs a literal section of the quotient, and proves that both the
collapse and the section preserve the Gram and intertwine the non-unit
heat-kernel transfer.  The transfer is then descended to the constructive GNS
completion, with a nonzero physical vacuum and exact fundamental/quadratic
eigenmodes.

Honest scope: this is the first genuinely shared-link local block.  It does
not assert that independent local sections glue consistently around every
cycle of an arbitrary four-dimensional lattice; the global gauge quotient is
the next compatibility layer.
-/

import YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding
import YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum

namespace YMGap.Continuum.SU2SharedLinkFusionGNSCompleted

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFusionBlock
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

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## The entrance fence -/

theorem literal_disjoint_gluing_not_isometric :
    ¬ (∀ a : SharedVec, sharedGram a a ≈ tensorGram a a) :=
  shared_multiplication_not_isometric

theorem literal_disjoint_time_not_intertwined :
    ¬ SharedRadEq (sharedTransfer doubleMode) (tensorTransfer doubleMode) :=
  double_mode_not_intertwined_mod_radical

/-! ## Exact GNS form on the fusion quotient -/

private def unitLine : GNSData := qWeightGNS 1 (by decide)

/-- The orthonormal irreducible coordinates `(chi_0,chi_1,chi_2)`. -/
abbrev sharedIrrepGNS : GNSData :=
  gnsProduct unitLine (gnsProduct unitLine unitLine)

theorem sharedIrrepGNS_B_eq_irrepGram (a b : IrrepVec) :
    sharedIrrepGNS.B a b ≈ irrepGram a b := by
  unfold sharedIrrepGNS gnsProduct unitLine qWeightGNS irrepGram
  exact QPoly.q_add_congr (Q'.one_mul_eqv _)
    (QPoly.q_add_congr (Q'.one_mul_eqv _) (Q'.one_mul_eqv _))

theorem irrepGram_congr {a a' b b' : IrrepVec}
    (ha : IrrepEq a a') (hb : IrrepEq b b') :
    irrepGram a b ≈ irrepGram a' b' :=
  QPoly.q_add_congr (q_mul_congr ha.1 hb.1)
    (QPoly.q_add_congr (q_mul_congr ha.2.1 hb.2.1)
      (q_mul_congr ha.2.2 hb.2.2))

/-- The frozen shared Gram is literally the pullback of the quotient GNS
form. -/
theorem fusionCollapse_gns_gram (a b : SharedVec) :
    sharedIrrepGNS.B (fusionCollapse a) (fusionCollapse b) ≈
      sharedGram a b := by
  refine Q'.eqv_trans _ _ _ (sharedIrrepGNS_B_eq_irrepGram _ _) ?_
  exact Q'.eqv_refl _

/-- A literal representative of each irreducible quotient vector.  The
`chi_0` coefficient is corrected by subtracting the `chi_0` summand carried
by the double excitation. -/
def fusionSection (a : IrrepVec) : SharedVec :=
  (a.1 + (-a.2.2), (a.2.1, (0, a.2.2)))

theorem fusionCollapse_section (a : IrrepVec) :
    IrrepEq (fusionCollapse (fusionSection a)) a := by
  unfold IrrepEq fusionCollapse fusionSection vacuumCoord fundamentalCoord
    quadraticCoord
  exact ⟨Q'.eqv_trans _ (a.1 + ((-a.2.2) + a.2.2)) _
      (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left a.1 _ _ (Q'.neg_add_self_eqv a.2.2))
        (QPoly.q_add_zero_eqv a.1)),
    Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) (Q'.eqv_refl _),
    Q'.eqv_refl _⟩

/-- The corrected section is an exact isometric gluing into the redundant
shared-link carrier. -/
theorem fusionSection_gram (a b : IrrepVec) :
    sharedGram (fusionSection a) (fusionSection b) ≈
      sharedIrrepGNS.B a b := by
  refine Q'.eqv_trans _
    (irrepGram (fusionCollapse (fusionSection a))
      (fusionCollapse (fusionSection b))) _ (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _ (irrepGram a b) _
    (irrepGram_congr (fusionCollapse_section a) (fusionCollapse_section b)) ?_
  exact Q'.eqv_symm (sharedIrrepGNS_B_eq_irrepGram a b)

def SharedEq (a b : SharedVec) : Prop :=
  a.1 ≈ b.1 ∧ a.2.1 ≈ b.2.1 ∧
    a.2.2.1 ≈ b.2.2.1 ∧ a.2.2.2 ≈ b.2.2.2

/-- Unlike the naive product representative, the corrected section also
intertwines time before taking any radical quotient. -/
theorem fusionSection_transfer_intertwines (a : IrrepVec) :
    SharedEq (sharedTransfer (fusionSection a))
      (fusionSection (irrepTransfer a)) := by
  unfold SharedEq sharedTransfer fusionSection irrepTransfer
  refine ⟨?_, Q'.eqv_refl _, Q'.mul_zero_eqv eighth, Q'.eqv_refl _⟩
  have hsum : (vacuumMix + quadraticEigen) * a.2.2 ≈ a.2.2 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ vacuumMix_add_quadraticEigen)
      (Q'.one_mul_eqv _)
  have hneg : (-a.2.2) ≈ (-((vacuumMix + quadraticEigen) * a.2.2)) :=
    Q'.neg_eqv_congr _ _ (Q'.eqv_symm hsum)
  refine Q'.eqv_trans _
    (a.1 + ((-a.2.2) + vacuumMix * a.2.2)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine QPoly.q_add_congr (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _
    (-((vacuumMix + quadraticEigen) * a.2.2) + vacuumMix * a.2.2) _
    (QPoly.q_add_congr hneg (Q'.eqv_refl _)) ?_
  have hprod : (vacuumMix + quadraticEigen) * a.2.2 ≈
      vacuumMix * a.2.2 + quadraticEigen * a.2.2 :=
    Q'.add_mul_eqv _ _ _
  have hnegprod : (-((vacuumMix + quadraticEigen) * a.2.2)) ≈
      (-(vacuumMix * a.2.2 + quadraticEigen * a.2.2)) :=
    Q'.neg_eqv_congr _ _ hprod
  refine Q'.eqv_trans _
    (-(vacuumMix * a.2.2 + quadraticEigen * a.2.2) +
      vacuumMix * a.2.2) _
    (QPoly.q_add_congr hnegprod (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (((-(vacuumMix * a.2.2)) + (-(quadraticEigen * a.2.2))) +
      vacuumMix * a.2.2) _
    (QPoly.q_add_congr
      (Q'.neg_add_eqv (vacuumMix * a.2.2) (quadraticEigen * a.2.2))
      (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (((-(quadraticEigen * a.2.2)) + (-(vacuumMix * a.2.2))) +
      vacuumMix * a.2.2) _
    (QPoly.q_add_congr
      (Q'.add_comm_eqv (-(vacuumMix * a.2.2)) (-(quadraticEigen * a.2.2)))
      (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    ((-(quadraticEigen * a.2.2)) +
      ((-(vacuumMix * a.2.2)) + vacuumMix * a.2.2)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    ((-(quadraticEigen * a.2.2)) + 0) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_self_eqv (vacuumMix * a.2.2))) ?_
  exact QPoly.q_add_zero_eqv _

/-! ## Dense transfer laws on the quotient -/

theorem irrepTransfer_map_veq {a b : IrrepVec} (h : sharedIrrepGNS.veq a b) :
    sharedIrrepGNS.veq (irrepTransfer a) (irrepTransfer b) :=
  ⟨h.1, Q'.mul_eqv_congr_left eighth _ _ h.2.1,
    Q'.mul_eqv_congr_left quadraticEigen _ _ h.2.2⟩

theorem irrepTransfer_map_sub (a b : IrrepVec) :
    sharedIrrepGNS.veq
      (irrepTransfer (sharedIrrepGNS.sub a b))
      (sharedIrrepGNS.sub (irrepTransfer a) (irrepTransfer b)) := by
  unfold GNSData.sub irrepTransfer sharedIrrepGNS gnsProduct unitLine qWeightGNS
  exact ⟨Q'.eqv_refl _, by ring_qeqv, by ring_qeqv⟩

theorem irrepTransfer_selfAdjoint (a b : IrrepVec) :
    sharedIrrepGNS.B (irrepTransfer a) b ≈
      sharedIrrepGNS.B a (irrepTransfer b) := by
  refine Q'.eqv_trans _ _ _ (sharedIrrepGNS_B_eq_irrepGram _ b) ?_
  refine Q'.eqv_trans _ (irrepGram a (irrepTransfer b)) _ (by
    unfold irrepGram irrepTransfer
    ring_qeqv) ?_
  exact Q'.eqv_symm (sharedIrrepGNS_B_eq_irrepGram a _)

theorem irrepTransfer_positive (a : IrrepVec) :
    (0 : Q') ≤ sharedIrrepGNS.B (irrepTransfer a) a := by
  have h0 : (0 : Q') ≤ a.1 * a.1 := q_mul_self_nonneg a.1
  have h1base : (0 : Q') ≤ eighth * (a.2.1 * a.2.1) :=
    Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg a.2.1)
  have h1 : (0 : Q') ≤ (eighth * a.2.1) * a.2.1 :=
    Q'.le_trans' _ _ _ h1base
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_assoc_eqv eighth a.2.1 a.2.1)))
  have h2base : (0 : Q') ≤ quadraticEigen * (a.2.2 * a.2.2) :=
    Q'.mul_nonneg _ _ quadraticEigen_nonneg (q_mul_self_nonneg a.2.2)
  have h2 : (0 : Q') ≤ (quadraticEigen * a.2.2) * a.2.2 :=
    Q'.le_trans' _ _ _ h2base
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_assoc_eqv quadraticEigen a.2.2 a.2.2)))
  have hraw : (0 : Q') ≤ irrepGram (irrepTransfer a) a := by
    unfold irrepGram irrepTransfer
    exact Q'.zero_le_add _ _ h0 (Q'.zero_le_add _ _ h1 h2)
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv (Q'.eqv_symm (sharedIrrepGNS_B_eq_irrepGram _ a)))

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

theorem irrepTransfer_contraction (a : IrrepVec) :
    sharedIrrepGNS.B (irrepTransfer a) (irrepTransfer a) ≤
      sharedIrrepGNS.B a a := by
  have h1 := scaled_square_le eighth a.2.1 (by decide) (by decide)
  have h2 := scaled_square_le quadraticEigen a.2.2
    quadraticEigen_nonneg (by decide)
  have hraw : irrepGram (irrepTransfer a) (irrepTransfer a) ≤
      irrepGram a a := by
    unfold irrepGram irrepTransfer
    exact Q'.add_le_add (Q'.le_refl' _)
      (Q'.add_le_add h1 h2)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (sharedIrrepGNS_B_eq_irrepGram _ _)) hraw)
    (Q'.le_of_eqv (Q'.eqv_symm (sharedIrrepGNS_B_eq_irrepGram a a)))

theorem irrepTransfer_distSq_contraction (a b : IrrepVec) :
    sharedIrrepGNS.distSqQ (irrepTransfer a) (irrepTransfer b) ≤
      sharedIrrepGNS.distSqQ a b := by
  have hsub := irrepTransfer_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (sharedIrrepGNS.B_diag_congr hsub))
    (irrepTransfer_contraction (sharedIrrepGNS.sub a b))

/-! ## Constructive completion -/

def applyCauchy (x : CauchyGNS sharedIrrepGNS) : CauchyGNS sharedIrrepGNS where
  seq := fun n => irrepTransfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (irrepTransfer_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyCauchy_null {x y : CauchyGNS sharedIrrepGNS}
    (h : CauchyNull sharedIrrepGNS x y) :
    CauchyNull sharedIrrepGNS (applyCauchy x) (applyCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (irrepTransfer_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

def completedIrrepTransfer :
    GNSCompletionSpace sharedIrrepGNS → GNSCompletionSpace sharedIrrepGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid sharedIrrepGNS) (applyCauchy x))
    (fun _ _ h => Quotient.sound (applyCauchy_null h))

theorem completedIrrepTransfer_embed (a : IrrepVec) :
    completedIrrepTransfer (embedV sharedIrrepGNS a) =
      embedV sharedIrrepGNS (irrepTransfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem completedIrrepTransfer_selfAdjoint
    (x y : GNSCompletionSpace sharedIrrepGNS) :
    sharedIrrepGNS.cinnerCompl (completedIrrepTransfer x) y =
      sharedIrrepGNS.cinnerCompl x (completedIrrepTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (sharedIrrepGNS.cInnerSeq (applyCauchy u) v n))
    (bSeq := fun n => CReal.ofQ'
      (sharedIrrepGNS.cInnerSeq u (applyCauchy v) n))
    (fun n => PositiveTimeCompression.lifted_eqv
      (irrepTransfer_selfAdjoint (u.seq n) (v.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedIrrepTransfer_positive
    (x : GNSCompletionSpace sharedIrrepGNS) :
    CReal.RCnonneg
      (sharedIrrepGNS.cinnerCompl (completedIrrepTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (sharedIrrepGNS.cinnerRep (applyCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => irrepTransfer_positive (u.seq _))

theorem completedIrrepTransfer_contraction
    (x : GNSCompletionSpace sharedIrrepGNS) :
    CReal.RCle
      (sharedIrrepGNS.cinnerCompl (completedIrrepTransfer x)
        (completedIrrepTransfer x))
      (sharedIrrepGNS.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (fun epsilon hepsilon => ⟨0, fun n _ => Q'.le_trans' _ _ _
      (irrepTransfer_contraction (u.seq n))
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩)

def completedSharedLinkTransferOperator :
    TransferOperator sharedIrrepGNS.gnsComplete where
  T := completedIrrepTransfer
  vacuum := embedV sharedIrrepGNS quotientVacuum
  selfAdjoint := completedIrrepTransfer_selfAdjoint
  positive := completedIrrepTransfer_positive
  contraction := completedIrrepTransfer_contraction

/-! ## Completed gluing and physical channels -/

/-- Collapse followed by completed time equals completed time after collapse
for every raw shared-link representative. -/
theorem fusionCollapse_completed_intertwines (a : SharedVec) :
    completedIrrepTransfer (embedV sharedIrrepGNS (fusionCollapse a)) =
      embedV sharedIrrepGNS (fusionCollapse (sharedTransfer a)) := by
  refine Eq.trans (completedIrrepTransfer_embed (fusionCollapse a)) ?_
  apply Quotient.sound
  exact embed_null_of_rad sharedIrrepGNS
    (rad_of_veq sharedIrrepGNS
      (sharedIrrepGNS.veq_symm (fusionCollapse_transfer_intertwiner a)))

theorem completed_vacuum_eigen :
    completedSharedLinkTransferOperator.T
        (embedV sharedIrrepGNS quotientVacuum) =
      embedV sharedIrrepGNS quotientVacuum := by
  refine Eq.trans (completedIrrepTransfer_embed quotientVacuum) ?_
  apply Quotient.sound
  exact embed_null_of_rad sharedIrrepGNS
    (rad_of_veq sharedIrrepGNS quotientTransfer_exact_spectrum.1)

theorem completed_fundamental_eigen :
    completedSharedLinkTransferOperator.T
        (embedV sharedIrrepGNS quotientFundamental) =
      embedV sharedIrrepGNS ((0, (eighth, 0)) : IrrepVec) := by
  refine Eq.trans (completedIrrepTransfer_embed quotientFundamental) ?_
  apply Quotient.sound
  exact embed_null_of_rad sharedIrrepGNS
    (rad_of_veq sharedIrrepGNS quotientTransfer_exact_spectrum.2.1)

theorem completed_quadratic_eigen :
    completedSharedLinkTransferOperator.T
        (embedV sharedIrrepGNS quotientQuadratic) =
      embedV sharedIrrepGNS ((0, (0, quadraticEigen)) : IrrepVec) := by
  refine Eq.trans (completedIrrepTransfer_embed quotientQuadratic) ?_
  apply Quotient.sound
  exact embed_null_of_rad sharedIrrepGNS
    (rad_of_veq sharedIrrepGNS quotientTransfer_exact_spectrum.2.2)

theorem completed_vacuum_ne_zero :
    embedV sharedIrrepGNS quotientVacuum ≠
      embedV sharedIrrepGNS sharedIrrepGNS.zero := by
  intro h
  have hr : sharedIrrepGNS.rad quotientVacuum sharedIrrepGNS.zero :=
    constCauchy_null_imp_rad sharedIrrepGNS (Quotient.exact h)
  have hz : sharedIrrepGNS.B quotientVacuum quotientVacuum ≈ 0 :=
    (sharedIrrepGNS.rad_zero_iff quotientVacuum).mp hr
  have hn : sharedIrrepGNS.B quotientVacuum quotientVacuum ≈ 1 :=
    Q'.eqv_trans _ _ _
      (sharedIrrepGNS_B_eq_irrepGram quotientVacuum quotientVacuum) (by decide)
  exact (by decide : ¬ ((1 : Q') ≈ 0))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hn) hz)

theorem completed_fundamental_ne_zero :
    embedV sharedIrrepGNS quotientFundamental ≠
      embedV sharedIrrepGNS sharedIrrepGNS.zero := by
  intro h
  have hr : sharedIrrepGNS.rad quotientFundamental sharedIrrepGNS.zero :=
    constCauchy_null_imp_rad sharedIrrepGNS (Quotient.exact h)
  have hz : sharedIrrepGNS.B quotientFundamental quotientFundamental ≈ 0 :=
    (sharedIrrepGNS.rad_zero_iff quotientFundamental).mp hr
  have hn : sharedIrrepGNS.B quotientFundamental quotientFundamental ≈ 1 :=
    Q'.eqv_trans _ _ _
      (sharedIrrepGNS_B_eq_irrepGram quotientFundamental quotientFundamental)
      (by decide)
  exact (by decide : ¬ ((1 : Q') ≈ 0))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hn) hz)

end YMGap.Continuum.SU2SharedLinkFusionGNSCompleted

#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.literal_disjoint_gluing_not_isometric
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.literal_disjoint_time_not_intertwined
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.fusionCollapse_gns_gram
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.fusionSection_gram
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.fusionSection_transfer_intertwines
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.irrepTransfer_distSq_contraction
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.completedIrrepTransfer
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.completedSharedLinkTransferOperator
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.fusionCollapse_completed_intertwines
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.completed_vacuum_eigen
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.completed_fundamental_eigen
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.completed_quadratic_eigen
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.completed_vacuum_ne_zero
#print axioms YMGap.Continuum.SU2SharedLinkFusionGNSCompleted.completed_fundamental_ne_zero
