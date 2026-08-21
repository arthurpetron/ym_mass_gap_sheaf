/-
# Constructive GNS completion of the physical BF4 macro transfer

This module equips the literal finite BF4 physical observable carrier with its
stationary marginal-weighted form, proves that the conditional Markov action is
a contractive rational-linear symbol, and descends it to the repository's
explicit constructive GNS completion.

The carrier consists of functions on all edge labellings.  Its form only sees
the positive-marginal carrier, so values outside that carrier are correctly
removed by the GNS radical.  In particular, vacuum fixation is asserted only
after quotienting; the zero rows do not fix the constant function pointwise.

The resulting operator is the already-composed physical *macro* transfer.  It
is not iterated again by the Faraut local-density depth.  This construction is
finite-cutoff and does not provide the still-open strict comparison/gap or a
continuum limit.
-/

import YMGap.Continuum.BF4PhysicalMarkovL2Contraction
import YMGap.Continuum.LinearTransferOperator

namespace YMGap.Continuum.BF4PhysicalMarkovGNSCompletion

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalMarkovL2Contraction
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. The exact physical rational GNS module -/

/-- The physical finite BF4 observable module with its literal stationary
marginal-weighted form. -/
def centralPhysicalSmulGNS
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : SmulGNSData where
  V := EdgeLabelling → Q'
  veq := fun a b => ∀ state, a state ≈ b state
  veq_refl := fun _ _ => Q'.eqv_refl _
  veq_symm := fun h state => Q'.eqv_symm (h state)
  veq_trans := fun h₁ h₂ state => Q'.eqv_trans _ _ _ (h₁ state) (h₂ state)
  zero := fun _ => 0
  add := fun a b state => a state + b state
  neg := fun a state => -(a state)
  smul := fun scalar a state => scalar * a state
  add_congr := fun ha hb state => Q'.add_eqv_congr' (ha state) (hb state)
  neg_congr := fun {a a'} h state => Q'.neg_eqv_congr _ _ (h state)
  smul_congr := fun scalar {a a'} h state =>
    Q'.mul_eqv_congr_left scalar _ _ (h state)
  add_assoc := fun a b c state => Q'.add_assoc_eqv _ _ _
  add_comm := fun a b state => Q'.add_comm_eqv _ _
  zero_add := fun a state => Q'.eqv_of_eq (Q'.zero_add' (a state))
  neg_add := fun a state => Q'.neg_add_self_eqv (a state)
  B := centralPhysicalWeightedInner w hw K half
  B_congr_left := by
    intro a a' b h
    unfold centralPhysicalWeightedInner
    apply listQSum_congr
    intro state
    exact Q'.mul_eqv_congr_left
      (centralPhysicalRowMarginal w hw K half state) _ _
      (Q'.mul_eqv_congr_right _ _ (b state) (h state))
  B_add_left := by
    intro a b c
    unfold centralPhysicalWeightedInner
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          centralPhysicalRowMarginal w hw K half state *
              (a state * c state) +
            centralPhysicalRowMarginal w hw K half state *
              (b state * c state))
        (centralPositiveHalfStates w hw K half)) _ ?_ ?_
    · apply listQSum_congr
      intro state
      q_ring
    · exact listQSum_add _ _ _
  B_smul_left := by
    intro scalar a b
    unfold centralPhysicalWeightedInner
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          scalar *
            (centralPhysicalRowMarginal w hw K half state *
              (a state * b state)))
        (centralPositiveHalfStates w hw K half)) _ ?_ ?_
    · apply listQSum_congr
      intro state
      q_ring
    · exact listQSum_mul_left scalar _ _
  B_symm := by
    intro a b
    unfold centralPhysicalWeightedInner
    apply listQSum_congr
    intro state
    exact Q'.mul_eqv_congr_left
      (centralPhysicalRowMarginal w hw K half state) _ _
      (Q'.mul_comm_eqv (a state) (b state))
  self_nonneg := centralPhysicalWeightedSquare_nonnegative w hw K half
  smul_sub := by
    intro scalar a b state
    refine Q'.eqv_trans _
      (scalar * a state + scalar * (-(b state))) _
      (Q'.mul_add_eqv scalar (a state) (-(b state))) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_neg_eqv scalar (b state))

/-- Opaque projection rule for the physical GNS form.  Downstream completion
proofs use this rule instead of unfolding the proof-heavy structure record. -/
theorem centralPhysicalSmulGNS_B_eq
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : EdgeLabelling → Q') :
    (centralPhysicalSmulGNS w hw K half).toGNSData.B left right =
      centralPhysicalWeightedInner w hw K half left right :=
  rfl

/-! ## 2. Exact rational linearity of the physical Markov action -/

theorem centralPhysicalMarkovApply_congr
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {a b : EdgeLabelling → Q'}
    (h : ∀ state, a state ≈ b state) :
    ∀ source,
      centralPhysicalMarkovApply w hw K half a source ≈
        centralPhysicalMarkovApply w hw K half b source := by
  intro source
  unfold centralPhysicalMarkovApply
  apply listQSum_congr
  intro target
  exact Q'.mul_eqv_congr_left
    (centralPhysicalConditionalKernel w hw K half source target)
    _ _ (h target)

theorem centralPhysicalMarkovApply_add
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (a b : EdgeLabelling → Q') :
    ∀ source,
      centralPhysicalMarkovApply w hw K half
          (fun state => a state + b state) source ≈
        centralPhysicalMarkovApply w hw K half a source +
          centralPhysicalMarkovApply w hw K half b source := by
  intro source
  unfold centralPhysicalMarkovApply
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        centralPhysicalConditionalKernel w hw K half source target * a target +
          centralPhysicalConditionalKernel w hw K half source target * b target)
      (centralPositiveHalfStates w hw K half)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_add_eqv _ _ _
  · exact listQSum_add _ _ _

theorem centralPhysicalMarkovApply_smul
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (scalar : Q') (a : EdgeLabelling → Q') :
    ∀ source,
      centralPhysicalMarkovApply w hw K half
          (fun state => scalar * a state) source ≈
        scalar * centralPhysicalMarkovApply w hw K half a source := by
  intro source
  unfold centralPhysicalMarkovApply
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        scalar *
          (centralPhysicalConditionalKernel w hw K half source target *
            a target))
      (centralPositiveHalfStates w hw K half)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    q_ring
  · exact listQSum_mul_left scalar _ _

private theorem listQSum_neg_local {State : Type} (value : State → Q') :
    ∀ states : List State,
      listQSum (fun state => -(value state)) states ≈
        -(listQSum value states)
  | [] => Q'.eqv_symm (by decide : (-(0 : Q')) ≈ 0)
  | head :: tail => by
      change
        -value head + listQSum (fun state => -value state) tail ≈
          -(value head + listQSum value tail)
      refine Q'.eqv_trans _
        (-value head + -(listQSum value tail)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm (Q'.neg_add_eqv _ _)

theorem centralPhysicalMarkovApply_sub
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (a b : EdgeLabelling → Q') :
    ∀ source,
      centralPhysicalMarkovApply w hw K half
          (fun state => a state + -(b state)) source ≈
        centralPhysicalMarkovApply w hw K half a source +
          -centralPhysicalMarkovApply w hw K half b source := by
  intro source
  unfold centralPhysicalMarkovApply
  let kernelValue : EdgeLabelling → Q' := fun target =>
    centralPhysicalConditionalKernel w hw K half source target
  let leftValue : EdgeLabelling → Q' := fun target =>
    kernelValue target * a target
  let rightValue : EdgeLabelling → Q' := fun target =>
    kernelValue target * b target
  refine Q'.eqv_trans _
    (listQSum
      (fun target => leftValue target + -(rightValue target))
      (centralPositiveHalfStates w hw K half)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    dsimp [leftValue, rightValue, kernelValue]
    refine Q'.eqv_trans _
      (_ * a target + _ * (-(b target))) _
      (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_neg_eqv _ _)
  refine Q'.eqv_trans _
    (listQSum leftValue (centralPositiveHalfStates w hw K half) +
      listQSum (fun target => -(rightValue target))
        (centralPositiveHalfStates w hw K half)) _
    (listQSum_add leftValue (fun target => -(rightValue target)) _) ?_
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (listQSum_neg_local rightValue _)

/-! ## 3. Contractive carrier symbol and constructive completion -/

theorem centralPhysicalMarkovApply_distSq_contraction
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (a b : (centralPhysicalSmulGNS w hw K half).toGNSData.V) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.distSqQ
        (centralPhysicalMarkovApply w hw K half a)
        (centralPhysicalMarkovApply w hw K half b) ≤
      (centralPhysicalSmulGNS w hw K half).toGNSData.distSqQ a b := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  have hsub : D.veq
      (D.sub
        (centralPhysicalMarkovApply w hw K half a)
        (centralPhysicalMarkovApply w hw K half b))
      (centralPhysicalMarkovApply w hw K half (D.sub a b)) := by
    intro source
    exact Q'.eqv_symm
      (centralPhysicalMarkovApply_sub w hw K half a b source)
  have hrecode :
      D.distSqQ
          (centralPhysicalMarkovApply w hw K half a)
          (centralPhysicalMarkovApply w hw K half b) ≈
        D.B
          (centralPhysicalMarkovApply w hw K half (D.sub a b))
          (centralPhysicalMarkovApply w hw K half (D.sub a b)) :=
    D.B_diag_congr hsub
  exact le_of_eqv_le hrecode
    (centralPhysicalMarkovApply_l2_contraction
      w hw K half (D.sub a b))

/-- The literal finite physical BF4 macro action as a contractive rational
symbol on its exact stationary GNS carrier. -/
def centralPhysicalMarkovSymbol
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    DiagonalTransferSymbol (centralPhysicalSmulGNS w hw K half) where
  Dv := centralPhysicalMarkovApply w hw K half
  Dv_congr := centralPhysicalMarkovApply_congr w hw K half
  distSqQ_Dv := centralPhysicalMarkovApply_distSq_contraction w hw K half
  Dv_add := centralPhysicalMarkovApply_add w hw K half
  Dv_smul := centralPhysicalMarkovApply_smul w hw K half

/-- Opaque projection rule for the physical macro symbol. -/
theorem centralPhysicalMarkovSymbol_Dv_eq
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    (centralPhysicalMarkovSymbol w hw K half).Dv observable =
      centralPhysicalMarkovApply w hw K half observable :=
  rfl

/-! ## 4. The completed physical macro transfer -/

abbrev CentralPhysicalGNSCompletion
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Type :=
  GNSCompletionSpace
    (centralPhysicalSmulGNS w hw K half).toGNSData

/-- The exact physical BF4 macro transfer descended to the explicit Cauchy
completion. -/
def centralPhysicalCompletedMarkovTransfer
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    CentralPhysicalGNSCompletion w hw K half →
      CentralPhysicalGNSCompletion w hw K half :=
  (centralPhysicalMarkovSymbol w hw K half).TqSymb

theorem centralPhysicalCompletedMarkovTransfer_embed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    centralPhysicalCompletedMarkovTransfer w hw K half
        (embedV
          (centralPhysicalSmulGNS w hw K half).toGNSData observable) =
      embedV
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalMarkovApply w hw K half observable) :=
  (centralPhysicalMarkovSymbol w hw K half).TqSymb_embed observable

theorem centralPhysical_cinnerRep_selfAdjoint
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (x y : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData) :
    CReal.Equiv
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy x) y)
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep x
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy y)) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (D.cInnerSeq
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy x) y n))
    (bSeq := fun n => CReal.ofQ'
      (D.cInnerSeq x
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy y) n))
    (fun n =>
      PositiveTimeCompressedTransfer.PositiveTimeCompression.lifted_eqv
        (Q'.eqv_symm
          (centralPhysicalMarkovApply_self_adjoint
            w hw K half (x.seq n) (y.seq n)))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem centralPhysicalCompletedMarkovTransfer_selfAdjoint
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (x y : CentralPhysicalGNSCompletion w hw K half) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half x) y =
      (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl x
        (centralPhysicalCompletedMarkovTransfer w hw K half y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact centralPhysical_cinnerRep_selfAdjoint w hw K half u v

theorem centralPhysicalMarkovApply_positive_left
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤
      centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply w hw K half observable) observable := by
  have hsymm :
      centralPhysicalWeightedInner w hw K half observable
          (centralPhysicalMarkovApply w hw K half observable) ≈
        centralPhysicalWeightedInner w hw K half
          (centralPhysicalMarkovApply w hw K half observable) observable := by
    unfold centralPhysicalWeightedInner
    apply listQSum_congr
    intro state
    exact Q'.mul_eqv_congr_left
      (centralPhysicalRowMarginal w hw K half state) _ _
      (Q'.mul_comm_eqv _ _)
  exact Q'.le_trans' _ _ _
    (centralPhysicalMarkovApply_positive w hw K half observable)
    (Q'.le_of_eqv hsymm)

theorem centralPhysicalCompletedMarkovTransfer_positive
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (x : CentralPhysicalGNSCompletion w hw K half) :
    CReal.RCnonneg
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
      ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy u) u)
  apply CReal.leEv_ofQ'_of_approx_ge
  intro n
  simp only [GNSData.cinnerRep, CReal.ofQ'CauchySeq_approx,
    GNSData.cInnerSeq, DiagonalTransferSymbol.cDiagCauchy]
  rw [centralPhysicalSmulGNS_B_eq,
    centralPhysicalMarkovSymbol_Dv_eq]
  exact centralPhysicalMarkovApply_positive_left
    w hw K half (u.seq _)

theorem centralPhysical_cinnerRep_contraction
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (x : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData) :
    CReal.leEv
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy x)
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy x))
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep x x) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro epsilon hepsilon
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (centralPhysicalMarkovApply_l2_contraction
      w hw K half (x.seq n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

theorem centralPhysicalCompletedMarkovTransfer_contraction
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (x : CentralPhysicalGNSCompletion w hw K half) :
    CReal.RCle
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half x)
        (centralPhysicalCompletedMarkovTransfer w hw K half x))
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact centralPhysical_cinnerRep_contraction w hw K half u

/-! ## 5. The normalized fixed vacuum and its completed complement -/

def centralPhysicalVacuumCarrier : EdgeLabelling → Q' := fun _ => 1

def centralPhysicalCompletedVacuum
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    CentralPhysicalGNSCompletion w hw K half :=
  embedV (centralPhysicalSmulGNS w hw K half).toGNSData
    centralPhysicalVacuumCarrier

theorem centralPhysicalWeightedInner_vacuum_one
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    centralPhysicalWeightedInner w hw K half
        centralPhysicalVacuumCarrier centralPhysicalVacuumCarrier ≈ 1 := by
  refine Q'.eqv_trans _
    (centralPhysicalStationaryMean w hw K half
      centralPhysicalVacuumCarrier) _ ?_ ?_
  · unfold centralPhysicalWeightedInner centralPhysicalStationaryMean
      centralPhysicalVacuumCarrier
    apply listQSum_congr
    intro state
    refine Q'.eqv_trans _
      (centralPhysicalRowMarginal w hw K half state * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1)
    · exact Q'.eqv_refl _
  · exact centralPhysicalStationaryMean_one w hw K half

theorem centralPhysicalCompletedVacuum_inner_self_eq_one
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedVacuum w hw K half)
        (centralPhysicalCompletedVacuum w hw K half) =
      Quotient.mk CReal.crealSetoid CReal.cone := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  change D.cinnerCompl
      (embedQuot D (D.qmk centralPhysicalVacuumCarrier))
      (embedQuot D (D.qmk centralPhysicalVacuumCarrier)) =
    Quotient.mk CReal.crealSetoid CReal.cone
  rw [(centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl_embed]
  apply Quotient.sound
  exact CReal.ofQ'_equiv_of_eqv
    (centralPhysicalWeightedInner_vacuum_one w hw K half)

theorem centralPhysicalVacuumCarrier_rad_fixed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.rad
      (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
      centralPhysicalVacuumCarrier := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  change
    centralPhysicalWeightedInner w hw K half
      (D.sub
        (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
        centralPhysicalVacuumCarrier)
      (D.sub
        (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
        centralPhysicalVacuumCarrier) ≈ 0
  unfold centralPhysicalWeightedInner
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q'))
      (centralPositiveHalfStates w hw K half)) _ ?_ ?_
  · apply listQSum_congr_on
    intro state hstate
    have hone := centralPhysicalMarkovApply_one
      (w := w) (hw := hw) (K := K) (half := half) hstate
    have hdiff :
        D.sub
            (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
            centralPhysicalVacuumCarrier state ≈ 0 := by
      change
        centralPhysicalMarkovApply w hw K half
            centralPhysicalVacuumCarrier state + -1 ≈ 0
      exact Q'.eqv_trans _ (1 + -1) _
        (Q'.add_eqv_congr' hone (Q'.eqv_refl _))
        (Q'.add_neg_self_eqv 1)
    refine Q'.eqv_trans _
      (centralPhysicalRowMarginal w hw K half state * (0 * 0)) _ ?_ ?_
    · apply Q'.mul_eqv_congr_left
      refine Q'.eqv_trans _ (0 *
        D.sub
          (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
          centralPhysicalVacuumCarrier state) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ hdiff
      · exact Q'.eqv_trans _ 0 _
          (Q'.zero_mul_eqv _)
          (Q'.eqv_symm (Q'.zero_mul_eqv 0))
    · exact Q'.eqv_trans _
        (centralPhysicalRowMarginal w hw K half state * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 0))
        (Q'.mul_zero_eqv _)
  · exact listQSum_zero _

/-- The completed physical macro transfer fixes the stationary vacuum in the
GNS quotient, even though zero-marginal rows do not fix it pointwise. -/
theorem centralPhysicalCompletedMarkovTransfer_vacuum_fixed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    centralPhysicalCompletedMarkovTransfer w hw K half
        (centralPhysicalCompletedVacuum w hw K half) =
      centralPhysicalCompletedVacuum w hw K half := by
  refine Eq.trans
    (centralPhysicalCompletedMarkovTransfer_embed
      w hw K half centralPhysicalVacuumCarrier) ?_
  apply Quotient.sound
  exact embed_null_of_rad
    (centralPhysicalSmulGNS w hw K half).toGNSData
    (centralPhysicalVacuumCarrier_rad_fixed w hw K half)

/-- The completed physical macro transfer with its actual normalized stationary
vacuum. -/
def centralPhysicalCompletedLinearTransfer
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    LinearTransferOperator (centralPhysicalSmulGNS w hw K half) :=
  (centralPhysicalMarkovSymbol w hw K half).toLinearTransfer
    (centralPhysicalCompletedVacuum w hw K half)
    (centralPhysicalCompletedMarkovTransfer_selfAdjoint w hw K half)
    (centralPhysicalCompletedMarkovTransfer_positive w hw K half)
    (centralPhysicalCompletedMarkovTransfer_contraction w hw K half)

def CentralPhysicalCompletedVacuumOrthogonal
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : CentralPhysicalGNSCompletion w hw K half) : Prop :=
  (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
      vector (centralPhysicalCompletedVacuum w hw K half) = CReal.RCzero

theorem centralPhysicalCompletedVacuumOrthogonal_preserved
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {vector : CentralPhysicalGNSCompletion w hw K half}
    (hvector :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (centralPhysicalCompletedMarkovTransfer w hw K half vector) := by
  unfold CentralPhysicalCompletedVacuumOrthogonal at hvector ⊢
  rw [centralPhysicalCompletedMarkovTransfer_selfAdjoint]
  rw [centralPhysicalCompletedMarkovTransfer_vacuum_fixed]
  exact hvector

end YMGap.Continuum.BF4PhysicalMarkovGNSCompletion

#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalSmulGNS
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalMarkovApply_congr
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalMarkovApply_add
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalMarkovApply_smul
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalMarkovApply_sub
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalMarkovApply_distSq_contraction
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalMarkovSymbol
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedMarkovTransfer
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedMarkovTransfer_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedMarkovTransfer_positive
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedMarkovTransfer_contraction
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedVacuum_inner_self_eq_one
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedMarkovTransfer_vacuum_fixed
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedLinearTransfer
#print axioms YMGap.Continuum.BF4PhysicalMarkovGNSCompletion.centralPhysicalCompletedVacuumOrthogonal_preserved
