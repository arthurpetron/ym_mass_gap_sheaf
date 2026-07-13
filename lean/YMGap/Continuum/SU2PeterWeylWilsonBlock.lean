/-
# A genuine two-channel SU(2) Peter--Weyl Wilson block

This file replaces the finite-group mechanism test by the first two actual
SU(2) character channels.  At the exact rational coupling `w = 1/2`, retain
the heat-kernel link weight

    K_1 = coeffW(w,0) chi_0 + coeffW(w,1) chi_1
        = 1 + (1/4) chi_1.

The coefficient `coeffW(w,s) = dim_s w^{s(s+2)}` is the genuine SU(2)
Peter--Weyl coefficient.  Contracting one matrix-coefficient line contributes
the exact Schur factor `1/dim_s`; hence the reflected one-link channel weight
is `w^{s(s+2)}`.  On `chi_0,chi_1` the Gram matrix is therefore

    diag(1, 1/8).

The same link kernel used twice gives `diag(1,(1/8)^2)`.  Compression relative
to the one-link Gram is consequently the non-isometric Markov transfer
`diag(1,1/8)`.  This is a same-state construction: both the Hilbert form and
the translated moment are derived from the same non-unit Wilson coefficient
table.  No ambient isometry or pure-product state is used.

Honest scope: this is the smallest exact finite Peter--Weyl positive-time
block.  It is not a uniform-volume construction and does not by itself supply
the four-dimensional interacting continuum measure.
-/

import YMGap.Continuum.SU2ClassPolynomialHaarDescent
import YMGap.Continuum.PeterWeylRealWeight
import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2PeterWeylWilsonBlock

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast,
               one_den_cast, two_num_cast, two_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## The non-unit SU(2) heat-kernel link weight -/

def coupling : Q' := Q'.mkPos 1 2 (by decide)
def quarter : Q' := Q'.mkPos 1 4 (by decide)
def eighth : Q' := Q'.mkPos 1 8 (by decide)

theorem coupling_window :
    (0 : Q') < coupling ∧ coupling < (1 : Q') := by decide

/-- The first two terms of the actual SU(2) heat-kernel character expansion. -/
def interactionKernel : Poly := padd chi0 (pscale quarter chi1)

theorem interaction_coeff_vacuum : coeffW coupling 0 = (1 : Q') := by decide

theorem interaction_coeff_fundamental : coeffW coupling 1 ≈ quarter := by decide

/-- Pointwise, `K_1(x) = 1 + x/2` for the SU(2) class coordinate
`x = cos(theta)`. -/
theorem eval_interactionKernel (x : Q') :
    eval interactionKernel x ≈ 1 + coupling * x := by
  refine Q'.eqv_trans _
    (eval chi0 x + eval (pscale quarter chi1) x) _
    (eval_padd chi0 (pscale quarter chi1) x) ?_
  refine Q'.eqv_trans _
    (eval chi0 x + quarter * eval chi1 x) _
    (QPoly.q_add_congr (Q'.eqv_refl _)
      (eval_pscale quarter chi1 x)) ?_
  refine Q'.eqv_trans _
    (1 + quarter * ((2 : Q') * x)) _
    (QPoly.q_add_congr
      (Q'.eqv_trans _ _ _ (eval_chi0 x) (by
        unfold Cheb.U
        exact Q'.eqv_refl _))
      (Q'.mul_eqv_congr_left quarter _ _
        (Q'.eqv_trans _ _ _ (eval_chi1 x) (by
          unfold Cheb.U
          exact Q'.eqv_refl _)))) ?_
  unfold quarter coupling
  ring_qeqv

/-- The retained Wilson weight is not the unit class polynomial. -/
theorem interactionKernel_nonunit : ¬ PolyEqv interactionKernel chi0 := by
  intro h
  have h1 := h (1 : Q')
  have hnot : ¬ (eval interactionKernel (1 : Q')).eqv (eval chi0 (1 : Q')) := by
    unfold interactionKernel quarter chi0 chi1
    decide
  exact hnot h1

/-- On the physical SU(2) class interval `-1 <= x`, the retained heat-kernel
weight is bounded below by `1/2`, hence is a genuine nonnegative Boltzmann
weight rather than merely a signed character kernel. -/
theorem interactionKernel_lower_bound {x : Q'} (hx : (-1 : Q') ≤ x) :
    coupling ≤ eval interactionKernel x := by
  have hm := Q'.mul_le_mul_of_nonneg_left (-1 : Q') x coupling hx (by decide)
  have ha := Q'.add_le_add_left 1
    (coupling * (-1 : Q')) (coupling * x) hm
  refine Q'.le_trans' coupling (1 + coupling * x) _ ?_ ?_
  · exact Q'.le_trans' coupling (1 + coupling * (-1 : Q')) _
      (Q'.le_of_eqv (by decide)) ha
  · exact Q'.le_of_eqv (Q'.eqv_symm (eval_interactionKernel x))

/-! ## Exact Schur contraction and the reflected Gram -/

/-- The full two-body matrix-coefficient Haar kernel `delta_ab/dim_a`.
Unlike `haarSubKernel`, the vacuum channel is retained here. -/
def haarMatrixKernel (a b : Nat) : Q' :=
  if a = b then Q'.invSucc a else 0

/-- One Wilson link followed by one exact Peter--Weyl/Schur contraction. -/
def contractedLinkEntry (w : Q') (a b : Nat) : Q' :=
  coeffW w a * haarMatrixKernel a b

theorem contractedLinkEntry_off {w : Q'} {a b : Nat} (h : a ≠ b) :
    contractedLinkEntry w a b ≈ 0 := by
  unfold contractedLinkEntry haarMatrixKernel
  rw [if_neg h]
  exact Q'.mul_zero_eqv _

/-- The dimension in the heat-kernel coefficient is cancelled by the genuine
Peter--Weyl `1/dim` normalization, leaving the physical channel eigenvalue. -/
theorem contractedLinkEntry_diag (w : Q') (s : Nat) :
    contractedLinkEntry w s s ≈ physLinkWeight w s := by
  unfold contractedLinkEntry haarMatrixKernel coeffW physLinkWeight
  rw [if_pos rfl]
  refine Q'.eqv_trans _
    (qpow w (c4 s) * (dimQ s * Q'.invSucc s)) _ ?_ ?_
  · ring_qeqv
  · refine Q'.eqv_trans _ (qpow w (c4 s) * 1) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.ofNat_succ_mul_invSucc s))
      (Q'.mul_one_eqv _)

theorem vacuum_channel_exact :
    contractedLinkEntry coupling 0 0 ≈ 1 := by decide

theorem fundamental_channel_exact :
    contractedLinkEntry coupling 1 1 ≈ eighth := by decide

/-! The Kronecker factor above is now tied to the completed bare Haar state,
not left as a free diagonal table. -/

theorem bareHaar_vacuum_pairing :
    bareVacuumHaar (pmul (chebPoly 0) (chebPoly 0)) ≈ 1 := by decide

theorem bareHaar_vacuum_fundamental_pairing :
    bareVacuumHaar (pmul (chebPoly 0) (chebPoly 1)) ≈ 0 := by decide

theorem bareHaar_fundamental_vacuum_pairing :
    bareVacuumHaar (pmul (chebPoly 1) (chebPoly 0)) ≈ 0 := by decide

theorem bareHaar_fundamental_pairing :
    bareVacuumHaar (pmul (chebPoly 1) (chebPoly 1)) ≈ 1 := by decide

/-- A retained link entry written literally as
`heat-kernel coefficient * (1/dim) * bare-Haar character pairing`. -/
def bareHaarLinkEntry (w : Q') (a b : Nat) : Q' :=
  (coeffW w a * Q'.invSucc a) *
    bareVacuumHaar (pmul (chebPoly a) (chebPoly b))

theorem bareHaarLinkEntry_vacuum :
    bareHaarLinkEntry coupling 0 0 ≈ 1 := by decide

theorem bareHaarLinkEntry_vacuum_fundamental :
    bareHaarLinkEntry coupling 0 1 ≈ 0 := by decide

theorem bareHaarLinkEntry_fundamental_vacuum :
    bareHaarLinkEntry coupling 1 0 ≈ 0 := by decide

theorem bareHaarLinkEntry_fundamental :
    bareHaarLinkEntry coupling 1 1 ≈ eighth := by decide

/-- On the retained block, the abstract Schur-table spelling and the literal
bare-Haar spelling agree entry by entry. -/
theorem bareHaarLinkEntry_eq_contracted_retained (a b : Fin 2) :
    bareHaarLinkEntry coupling a.val b.val ≈
      contractedLinkEntry coupling a.val b.val := by
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]
    exact Q'.eqv_trans _ _ _ bareHaarLinkEntry_vacuum
      (Q'.eqv_symm vacuum_channel_exact)
  · rw [ha, hb]
    exact Q'.eqv_trans _ _ _ bareHaarLinkEntry_vacuum_fundamental
      (Q'.eqv_symm
        (contractedLinkEntry_off (w := coupling) (a := 0) (b := 1) (by decide)))
  · rw [ha, hb]
    exact Q'.eqv_trans _ _ _ bareHaarLinkEntry_fundamental_vacuum
      (Q'.eqv_symm
        (contractedLinkEntry_off (w := coupling) (a := 1) (b := 0) (by decide)))
  · rw [ha, hb]
    exact Q'.eqv_trans _ _ _ bareHaarLinkEntry_fundamental
      (Q'.eqv_symm fundamental_channel_exact)

abbrev ModeVec := Q' × Q'

/-- The complete four-entry Peter--Weyl expression on the retained block. -/
def reflectedWilsonGram (a b : ModeVec) : Q' :=
  bareHaarLinkEntry coupling 0 0 * (a.1 * b.1) +
    (bareHaarLinkEntry coupling 0 1 * (a.1 * b.2) +
      (bareHaarLinkEntry coupling 1 0 * (a.2 * b.1) +
        bareHaarLinkEntry coupling 1 1 * (a.2 * b.2)))

/-- Exact reflection Gram form: the vacuum and fundamental character channels
are orthogonal and have weights `1` and `1/8`. -/
theorem reflectedWilsonGram_diagonal (a b : ModeVec) :
    reflectedWilsonGram a b ≈ a.1 * b.1 + eighth * (a.2 * b.2) := by
  unfold reflectedWilsonGram
  refine Q'.eqv_trans _
    (1 * (a.1 * b.1) +
      (0 * (a.1 * b.2) + (0 * (a.2 * b.1) + eighth * (a.2 * b.2)))) _ ?_ ?_
  · exact QPoly.q_add_congr
      (Q'.mul_eqv_congr_right _ _ _ bareHaarLinkEntry_vacuum)
      (QPoly.q_add_congr
        (Q'.mul_eqv_congr_right _ _ _
          bareHaarLinkEntry_vacuum_fundamental)
        (QPoly.q_add_congr
          (Q'.mul_eqv_congr_right _ _ _
            bareHaarLinkEntry_fundamental_vacuum)
          (Q'.mul_eqv_congr_right _ _ _ bareHaarLinkEntry_fundamental)))
  · ring_qeqv

theorem reflectedWilsonGram_nonneg (a : ModeVec) :
    (0 : Q') ≤ reflectedWilsonGram a a := by
  have h0 : (0 : Q') ≤ a.1 * a.1 := SumOfSquares.q_mul_self_nonneg a.1
  have h1 : (0 : Q') ≤ eighth * (a.2 * a.2) :=
    Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg a.2)
  exact Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ h0 h1)
    (Q'.le_of_eqv (Q'.eqv_symm (reflectedWilsonGram_diagonal a a)))

/-! ## The actual same-state rational GNS block -/

def modeZero : ModeVec := (0, 0)
def modeAdd (a b : ModeVec) : ModeVec := (a.1 + b.1, a.2 + b.2)
def modeNeg (a : ModeVec) : ModeVec := (-a.1, -a.2)
def modeSmul (s : Q') (a : ModeVec) : ModeVec := (s * a.1, s * a.2)
def modeEqv (a b : ModeVec) : Prop := a.1 ≈ b.1 ∧ a.2 ≈ b.2

/-- Nondegenerate GNS datum whose form is definitionally the one-link Wilson
reflection state just derived. -/
def wilsonModeGNS : GNSData where
  V := ModeVec
  veq := modeEqv
  veq_refl := fun a => ⟨Q'.eqv_refl a.1, Q'.eqv_refl a.2⟩
  veq_symm := fun h => ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2⟩
  veq_trans := fun h k =>
    ⟨Q'.eqv_trans _ _ _ h.1 k.1, Q'.eqv_trans _ _ _ h.2 k.2⟩
  zero := modeZero
  add := modeAdd
  neg := modeNeg
  smul := modeSmul
  add_congr := by
    intro a a' b b' ha hb
    exact ⟨QPoly.q_add_congr ha.1 hb.1, QPoly.q_add_congr ha.2 hb.2⟩
  neg_congr := by
    intro a a' h
    exact ⟨Q'.neg_eqv_congr _ _ h.1, Q'.neg_eqv_congr _ _ h.2⟩
  smul_congr := by
    intro s a a' h
    exact ⟨Q'.mul_eqv_congr_left s _ _ h.1,
      Q'.mul_eqv_congr_left s _ _ h.2⟩
  add_assoc := fun a b c =>
    ⟨Q'.add_assoc_eqv _ _ _, Q'.add_assoc_eqv _ _ _⟩
  add_comm := fun a b => ⟨Q'.add_comm_eqv _ _, Q'.add_comm_eqv _ _⟩
  zero_add := fun a => ⟨QPoly.q_zero_add_eqv _, QPoly.q_zero_add_eqv _⟩
  neg_add := fun a => ⟨Q'.neg_add_self_eqv _, Q'.neg_add_self_eqv _⟩
  B := reflectedWilsonGram
  B_congr_left := by
    intro a a' b h
    refine Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal a b) ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr
        (Q'.mul_eqv_congr_right _ _ b.1 h.1)
        (Q'.mul_eqv_congr_left eighth _ _
          (Q'.mul_eqv_congr_right _ _ b.2 h.2))) ?_
    exact Q'.eqv_symm (reflectedWilsonGram_diagonal a' b)
  B_add_left := by
    intro a b c
    refine Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal _ c) ?_
    unfold modeAdd
    refine Q'.eqv_trans _
      ((a.1 * c.1 + eighth * (a.2 * c.2)) +
        (b.1 * c.1 + eighth * (b.2 * c.2))) _ (by ring_qeqv) ?_
    exact QPoly.q_add_congr
      (Q'.eqv_symm (reflectedWilsonGram_diagonal a c))
      (Q'.eqv_symm (reflectedWilsonGram_diagonal b c))
  B_smul_left := by
    intro s a b
    refine Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal _ b) ?_
    unfold modeSmul
    refine Q'.eqv_trans _
      (s * (a.1 * b.1 + eighth * (a.2 * b.2))) _ (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left s _ _
      (Q'.eqv_symm (reflectedWilsonGram_diagonal a b))
  B_symm := by
    intro a b
    refine Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal a b) ?_
    refine Q'.eqv_trans _
      (b.1 * a.1 + eighth * (b.2 * a.2)) _ (by ring_qeqv) ?_
    exact Q'.eqv_symm (reflectedWilsonGram_diagonal b a)
  self_nonneg := reflectedWilsonGram_nonneg

/-! ## Two uses of the same link kernel and the compressed transfer -/

/-- The same Wilson link contracted twice, i.e. the translated two-link
moment before dividing by the one-link Gram. -/
def twoLinkWilsonMoment (a b : ModeVec) : Q' :=
  (bareHaarLinkEntry coupling 0 0 * bareHaarLinkEntry coupling 0 0) *
      (a.1 * b.1) +
    (bareHaarLinkEntry coupling 1 1 * bareHaarLinkEntry coupling 1 1) *
      (a.2 * b.2)

theorem twoLinkWilsonMoment_diagonal (a b : ModeVec) :
    twoLinkWilsonMoment a b ≈
      a.1 * b.1 + (eighth * eighth) * (a.2 * b.2) := by
  unfold twoLinkWilsonMoment
  have h0 :
      bareHaarLinkEntry coupling 0 0 * bareHaarLinkEntry coupling 0 0 ≈
        (1 : Q') * 1 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ bareHaarLinkEntry_vacuum)
      (Q'.mul_eqv_congr_left 1 _ _ bareHaarLinkEntry_vacuum)
  have h1 :
      bareHaarLinkEntry coupling 1 1 * bareHaarLinkEntry coupling 1 1 ≈
        eighth * eighth :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ bareHaarLinkEntry_fundamental)
      (Q'.mul_eqv_congr_left eighth _ _ bareHaarLinkEntry_fundamental)
  refine Q'.eqv_trans _
    ((1 * 1) * (a.1 * b.1) + (eighth * eighth) * (a.2 * b.2)) _
    (QPoly.q_add_congr
      (Q'.mul_eqv_congr_right _ _ _ h0)
      (Q'.mul_eqv_congr_right _ _ _ h1))
    (QPoly.q_add_congr
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 : Q')))
        (Q'.one_mul_eqv (a.1 * b.1)))
      (Q'.eqv_refl _))

/-- The positive-time compression of one further use of the SAME Wilson link
kernel.  It is a Markov contraction, not an ambient isometry. -/
def sameStateTransfer (a : ModeVec) : ModeVec := (a.1, eighth * a.2)

theorem sameStateTransfer_map_veq {a b : ModeVec} (h : modeEqv a b) :
    modeEqv (sameStateTransfer a) (sameStateTransfer b) :=
  ⟨h.1, Q'.mul_eqv_congr_left eighth _ _ h.2⟩

theorem sameStateTransfer_map_add (a b : ModeVec) :
    modeEqv (sameStateTransfer (modeAdd a b))
      (modeAdd (sameStateTransfer a) (sameStateTransfer b)) := by
  unfold sameStateTransfer modeAdd modeEqv
  exact ⟨Q'.eqv_refl _, by ring_qeqv⟩

theorem sameStateTransfer_map_smul (s : Q') (a : ModeVec) :
    modeEqv (sameStateTransfer (modeSmul s a))
      (modeSmul s (sameStateTransfer a)) := by
  unfold sameStateTransfer modeSmul modeEqv
  exact ⟨Q'.eqv_refl _, by ring_qeqv⟩

/-- Defining same-state identity: pairing the compressed translate against a
one-link state is exactly the two-link moment built from two copies of that
same interaction kernel. -/
theorem same_state_compression (a b : ModeVec) :
    wilsonModeGNS.B (sameStateTransfer a) b ≈
      twoLinkWilsonMoment a b := by
  refine Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal _ b) ?_
  unfold sameStateTransfer
  refine Q'.eqv_trans _
    (a.1 * b.1 + (eighth * eighth) * (a.2 * b.2)) _ (by ring_qeqv) ?_
  exact Q'.eqv_symm (twoLinkWilsonMoment_diagonal a b)

theorem sameStateTransfer_selfAdjoint (a b : ModeVec) :
    wilsonModeGNS.B (sameStateTransfer a) b ≈
      wilsonModeGNS.B a (sameStateTransfer b) := by
  refine Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal _ b) ?_
  unfold sameStateTransfer
  refine Q'.eqv_trans _
    (a.1 * b.1 + eighth * (a.2 * (eighth * b.2))) _ (by ring_qeqv) ?_
  exact Q'.eqv_symm (reflectedWilsonGram_diagonal a _)

theorem sameStateTransfer_positive (a : ModeVec) :
    (0 : Q') ≤ wilsonModeGNS.B (sameStateTransfer a) a := by
  have h0 : (0 : Q') ≤ a.1 * a.1 := SumOfSquares.q_mul_self_nonneg a.1
  have h1 : (0 : Q') ≤ (eighth * eighth) * (a.2 * a.2) :=
    Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg a.2)
  refine Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ h0 h1) ?_
  unfold sameStateTransfer
  exact Q'.le_of_eqv (Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal _ a) (by ring_qeqv)))

theorem sameStateTransfer_contraction (a : ModeVec) :
    wilsonModeGNS.B (sameStateTransfer a) (sameStateTransfer a) ≤
      wilsonModeGNS.B a a := by
  have hsq : (0 : Q') ≤ a.2 * a.2 := SumOfSquares.q_mul_self_nonneg a.2
  have hc : eighth * (eighth * eighth) ≤ eighth := by decide
  have hterm := Q'.mul_le_mul_of_nonneg_right
    (eighth * (eighth * eighth)) eighth (a.2 * a.2) hc hsq
  refine Q'.le_trans' _
    (a.1 * a.1 + (eighth * (eighth * eighth)) * (a.2 * a.2)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (reflectedWilsonGram_diagonal _ _) (by
        unfold sameStateTransfer
        ring_qeqv))
  · refine Q'.le_trans' _
      (a.1 * a.1 + eighth * (a.2 * a.2)) _
      (Q'.add_le_add_left _ _ _ hterm) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (reflectedWilsonGram_diagonal a a))

def vacuumMode : ModeVec := (1, 0)
def fundamentalMode : ModeVec := (0, 1)

theorem vacuum_eigen : modeEqv (sameStateTransfer vacuumMode) vacuumMode := by
  exact ⟨by decide, by decide⟩

theorem fundamental_eighth_eigen :
    modeEqv (sameStateTransfer fundamentalMode)
      (modeSmul eighth fundamentalMode) := by
  exact ⟨by decide, by decide⟩

theorem eighth_strict_window :
    (0 : Q') < eighth ∧ eighth < (1 : Q') := by decide

theorem fundamental_norm :
    wilsonModeGNS.B fundamentalMode fundamentalMode ≈ eighth := by decide

theorem fundamental_qmk_ne_zero :
    wilsonModeGNS.qmk fundamentalMode ≠ wilsonModeGNS.qmk wilsonModeGNS.zero := by
  intro h
  have hr : wilsonModeGNS.rad fundamentalMode wilsonModeGNS.zero :=
    Quotient.exact h
  have hsub : wilsonModeGNS.veq
      (wilsonModeGNS.sub fundamentalMode wilsonModeGNS.zero)
      fundamentalMode := by
    unfold GNSData.sub wilsonModeGNS modeAdd modeNeg modeZero fundamentalMode
      modeEqv
    exact ⟨by decide, by decide⟩
  have hdiag := wilsonModeGNS.B_diag_congr hsub
  have he : eighth ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm fundamental_norm)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiag) hr)
  exact (by decide : ¬ ((eighth : Q').eqv 0)) he

/-- The retained Gram determinant is `1/8 > 0`, so the excited channel is not
a radical artefact or rank-one product collapse. -/
theorem retained_gram_determinant :
    wilsonModeGNS.B vacuumMode vacuumMode *
        wilsonModeGNS.B fundamentalMode fundamentalMode +
      -(wilsonModeGNS.B vacuumMode fundamentalMode *
        wilsonModeGNS.B fundamentalMode vacuumMode) ≈ eighth := by decide

theorem retained_gram_determinant_pos :
    (0 : Q') <
      wilsonModeGNS.B vacuumMode vacuumMode *
          wilsonModeGNS.B fundamentalMode fundamentalMode +
        -(wilsonModeGNS.B vacuumMode fundamentalMode *
          wilsonModeGNS.B fundamentalMode vacuumMode) := by decide

theorem sameStateTransfer_nonidentity : sameStateTransfer ≠ id := by
  intro h
  have hv := congrFun h fundamentalMode
  have h2 := congrArg Prod.snd hv
  exact (by decide : ¬ (eighth = (1 : Q'))) h2

end YMGap.Continuum.SU2PeterWeylWilsonBlock

#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.interactionKernel_nonunit
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.interactionKernel_lower_bound
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.contractedLinkEntry_diag
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.bareHaar_fundamental_pairing
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.bareHaarLinkEntry_eq_contracted_retained
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.reflectedWilsonGram_nonneg
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.wilsonModeGNS
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.same_state_compression
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.sameStateTransfer_map_add
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.sameStateTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.sameStateTransfer_positive
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.sameStateTransfer_contraction
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.fundamental_qmk_ne_zero
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.retained_gram_determinant_pos
#print axioms YMGap.Continuum.SU2PeterWeylWilsonBlock.sameStateTransfer_nonidentity
