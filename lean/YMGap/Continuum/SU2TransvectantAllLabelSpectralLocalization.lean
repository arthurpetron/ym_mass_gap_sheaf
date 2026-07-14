/-
# Arbitrary-label local transvectant spectral localization

For external SU(2) twice-spin labels `(a,b,c,d)`, a four-valent channel has
the exact heat-kernel transfer eigenvalue equal to the product of the four
edge eigenvalues.  Its invariant GNS weight is already derived by the
all-label transvectant Gram formula.

This file combines those two independently checked ingredients.  Every
channel and dense coordinate carries a one-mode squared-transfer spectral
model whose `corr 0` and `corr 1` are the actual channel GNS pairings.  If at
least one external edge is nonvacuum, its squared eigenvalue is bounded by
`(1/8)^2 = 1/64`, giving a constructive located gap.  Any exact all-label
recoupling certificate preserves the complete correlator at every integer
time because the Gram equality is derived from the coefficient identity.

Honest scope: a caller must still construct the exact all-label recoupling
certificate, and global coherence of overlapping local moves remains open.
-/

import YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted
import YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope

namespace YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

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

/-! ## The four external edge factors -/

def fourExternalOrder : List Nat := [0, 1, 2, 3]

def fourExternalLabels (a b c d : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

/-- Exact four-edge transfer eigenvalue of an arbitrary-label local channel. -/
def allLabelChannelEigen (a b c d : Nat) : Q' :=
  networkEigen fourExternalOrder (fourExternalLabels a b c d)

theorem allLabelChannelEigen_nonneg (a b c d : Nat) :
    (0 : Q') ≤ allLabelChannelEigen a b c d :=
  networkEigen_nonneg (fourExternalLabels a b c d) fourExternalOrder

/-- The propositional side condition that the local channel is outside the
global vacuum.  It carries no numerical witness consumed downstream. -/
def SomeExternalExcited (a b c d : Nat) : Prop :=
  1 ≤ a ∨ 1 ≤ b ∨ 1 ≤ c ∨ 1 ≤ d

theorem fourExternal_excitedSupport {a b c d : Nat}
    (h : SomeExternalExcited a b c d) :
    ∃ edge, edge ∈ fourExternalOrder ∧
      1 ≤ fourExternalLabels a b c d edge := by
  rcases h with ha | hb | hc | hd
  · exact ⟨0, by decide, ha⟩
  · exact ⟨1, by decide, hb⟩
  · exact ⟨2, by decide, hc⟩
  · exact ⟨3, by decide, hd⟩

theorem allLabelChannelEigen_le_eighth {a b c d : Nat}
    (h : SomeExternalExcited a b c d) :
    allLabelChannelEigen a b c d ≤
      YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth :=
  networkEigen_excited_le_eighth (fourExternalLabels a b c d)
    fourExternalOrder (fourExternal_excitedSupport h)

/-- Normalization cross-check: four fundamental external legs give exactly
the independently derived four-valent intertwiner eigenvalue `(1/8)^4`. -/
theorem fundamental_external_eigen_eq_fourLeg :
    allLabelChannelEigen 1 1 1 1 ≈
      YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.fourLegEigen := by
  decide

/-! ## Actual channel GNS as a one-mode squared spectrum -/

def allLabelSquaredEigen (a b c d : Nat) (_i : Nat) : Q' :=
  allLabelChannelEigen a b c d * allLabelChannelEigen a b c d

/-- The squared arbitrary-label channel eigenvalue agrees with the exact edge
of the dedicated two-channel four-fundamental construction. -/
theorem fundamental_squared_eigen_eq_fourValent_edge :
    allLabelSquaredEigen 1 1 1 1 0 ≈
      YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.fourLegEigen *
        YMGap.Continuum.SU2FourValentIntertwinerGNSCompleted.fourLegEigen := by
  decide

theorem allLabelSquaredEigen_nonneg (a b c d i : Nat) :
    (0 : Q') ≤ allLabelSquaredEigen a b c d i :=
  q_mul_self_nonneg (allLabelChannelEigen a b c d)

/-- The spectral weight is exactly the invariant GNS contribution to
`B(Tq,q)` for the selected transvectant channel. -/
def allLabelChannelSpectralWeight (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) (q : Q') (_i : Nat) : Q' :=
  allLabelChannelEigen a b c d *
    (triMapInner a b c d L L * (q * q))

theorem allLabelChannelSpectralWeight_nonneg (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) (q : Q') (i : Nat) :
    (0 : Q') ≤ allLabelChannelSpectralWeight a b c d L q i :=
  Q'.mul_nonneg _ _ (allLabelChannelEigen_nonneg a b c d)
    (Q'.mul_nonneg _ _ (triMapInner_diagonal_nonneg_all a b c d L)
      (q_mul_self_nonneg q))

/-- Concrete squared-transfer spectral model for one arbitrary-label channel. -/
def allLabelChannelSpectralModel (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) (q : Q') : SpectralModel :=
  diagOp.toSpectralModel (allLabelSquaredEigen a b c d)
    (allLabelChannelSpectralWeight a b c d L q) 1
    (allLabelChannelSpectralWeight_nonneg a b c d L q)
    (allLabelSquaredEigen_nonneg a b c d)

def allLabelChannelSquaredOp (a b c d : Nat) : FiniteOp :=
  diagOp (allLabelSquaredEigen a b c d) 1

theorem allLabelChannel_lam_is_operator_eigen (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) (q : Q') :
    (allLabelChannelSpectralModel a b c d L q).lam 0 ≈
      (allLabelChannelSquaredOp a b c d).apply (basis 0) 0 :=
  toSpectralModel_lam_is_eigen (allLabelSquaredEigen a b c d)
    (allLabelChannelSpectralWeight a b c d L q) 1
    (allLabelChannelSpectralWeight_nonneg a b c d L q)
    (allLabelSquaredEigen_nonneg a b c d) 0 (by decide)

theorem allLabelChannelGNS_eq_corr_zero (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) (q : Q') :
    (triMapChannelGNS a b c d L).B
        (allLabelChannelEigen a b c d * q) q ≈
      corr (allLabelChannelSpectralModel a b c d L q) 0 := by
  change
    triMapInner a b c d L L *
        ((allLabelChannelEigen a b c d * q) * q) ≈
      0 + (allLabelChannelEigen a b c d *
        (triMapInner a b c d L L * (q * q))) * 1
  ring_qeqv

theorem allLabelChannelTransferredGNS_eq_corr_one (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) (q : Q') :
    (triMapChannelGNS a b c d L).B
        (allLabelChannelEigen a b c d *
          (allLabelChannelEigen a b c d * q))
        (allLabelChannelEigen a b c d * q) ≈
      corr (allLabelChannelSpectralModel a b c d L q) 1 := by
  change
    triMapInner a b c d L L *
        ((allLabelChannelEigen a b c d *
          (allLabelChannelEigen a b c d * q)) *
            (allLabelChannelEigen a b c d * q)) ≈
      0 + (allLabelChannelEigen a b c d *
        (triMapInner a b c d L L * (q * q))) *
          ((allLabelChannelEigen a b c d *
            allLabelChannelEigen a b c d) * 1)
  ring_qeqv

/-! ## Uniform local gap whenever an external edge is excited -/

theorem allLabelSquaredEigen_le_sep {a b c d : Nat}
    (h : SomeExternalExcited a b c d) (i : Nat) :
    allLabelSquaredEigen a b c d i ≤ finiteNetworkSquaredSep := by
  let e := allLabelChannelEigen a b c d
  have he0 : (0 : Q') ≤ e := allLabelChannelEigen_nonneg a b c d
  have he : e ≤ YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth :=
    allLabelChannelEigen_le_eighth h
  have h1 : e * e ≤
      YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth * e :=
    Q'.mul_le_mul_of_nonneg_right e _ e he he0
  have h2 : YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth * e ≤
      YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth *
        YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth :=
    Q'.mul_le_mul_of_nonneg_left e _ _ he (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

def allLabelChannelLocatedGap {a b c d : Nat}
    (h : SomeExternalExcited a b c d)
    (L : BForm → BForm → BForm → BForm) (q : Q') :
    LocatedSpectralGap (allLabelChannelSpectralModel a b c d L q) :=
  diagLocatedGap (allLabelSquaredEigen a b c d)
    (allLabelChannelSpectralWeight a b c d L q) 1
    (allLabelChannelSpectralWeight_nonneg a b c d L q)
    (allLabelSquaredEigen_nonneg a b c d)
    finiteNetworkSquaredSep finiteNetworkSquaredSep_lt_one
    (allLabelSquaredEigen_le_sep h)

theorem allLabelChannel_gapMargin_exact {a b c d : Nat}
    (h : SomeExternalExcited a b c d)
    (L : BForm → BForm → BForm → BForm) (q : Q') :
    (allLabelChannelLocatedGap h L q).gapMargin ≈
      Q'.mkPos 63 64 (by decide) := by
  change (1 - finiteNetworkSquaredSep) ≈ Q'.mkPos 63 64 (by decide)
  decide

/-! ## Arbitrary-label recoupling covariance -/

/-- An exact all-label map identity preserves the full local spectral
correlator at every time, not just the completed norm. -/
theorem equivalentTriMap_corr_invariant (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d L R) (q : Q') (n : Nat) :
    corr (allLabelChannelSpectralModel a b c d R q) n ≈
      corr (allLabelChannelSpectralModel a b c d L q) n := by
  have hw := triMapInner_diagonal_congr_all_labels a b c d L R h
  change
    0 + (allLabelChannelEigen a b c d *
      (triMapInner a b c d R R * (q * q))) *
        ((allLabelChannelEigen a b c d *
          allLabelChannelEigen a b c d) ^ n) ≈
    0 + (allLabelChannelEigen a b c d *
      (triMapInner a b c d L L * (q * q))) *
        ((allLabelChannelEigen a b c d *
          allLabelChannelEigen a b c d) ^ n)
  refine Q'.eqv_trans _
    (allLabelChannelEigen a b c d *
      ((triMapInner a b c d R R * (q * q)) *
        ((allLabelChannelEigen a b c d *
          allLabelChannelEigen a b c d) ^ n))) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (allLabelChannelEigen a b c d *
      ((triMapInner a b c d L L * (q * q)) *
        ((allLabelChannelEigen a b c d *
          allLabelChannelEigen a b c d) ^ n))) _ ?_ (by ring_qeqv)
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hw)))

/-- The arbitrary-label dense GNS isometry commutes definitionally with the
physical scalar transfer on its one-dimensional channel coordinate. -/
theorem equivalentTriMap_transfer_commutes (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d L R) (q : Q') :
    (equivalentTriMapDenseIsometry a b c d L R h).map
        (allLabelChannelEigen a b c d * q : Q') =
      (allLabelChannelEigen a b c d * q : Q') := rfl

end YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization

#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.allLabelChannelEigen_le_eighth
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.fundamental_external_eigen_eq_fourLeg
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.fundamental_squared_eigen_eq_fourValent_edge
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.allLabelChannel_lam_is_operator_eigen
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.allLabelChannelGNS_eq_corr_zero
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.allLabelChannelTransferredGNS_eq_corr_one
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.allLabelChannelLocatedGap
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.allLabelChannel_gapMargin_exact
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.equivalentTriMap_corr_invariant
#print axioms YMGap.Continuum.SU2TransvectantAllLabelSpectralLocalization.equivalentTriMap_transfer_commutes
