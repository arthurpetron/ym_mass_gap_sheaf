/-
# A finite spectral envelope for globally projected SU(2) spin networks

After the Haar quotient and all vertex projectors have been imposed, a finite
spin-network state is a finite family of edge-label assignments with
nonnegative exact weights.  The transfer eigenvalue of one assignment is the
product of the exact heat-kernel eigenvalues on its edges.  This file proves
that any retained assignment containing at least one nonvacuum edge has
squared eigenvalue at most `(1/8)^2 = 1/64`.

The result is packaged as a concrete finite diagonal operator, with exact
time-zero and time-one correlators and elimination-order independence.  It is
deliberately independent of a particular graph presentation: theta graphs,
bivalent cycles, and future higher-valence quotients can all supply their
globally projected label families and weights to the same envelope.

Honest scope: the theorem does not construct the projected amplitudes of an
arbitrary four-dimensional lattice.  Its remaining graph-specific hypothesis
is precisely that every retained global mode contains an excited edge.
-/

import YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
import YMGap.Continuum.CompactTransferGNS

namespace YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope

set_option maxHeartbeats 1000000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, zero_num_cast, zero_den_cast, one_num_cast,
               one_den_cast, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Products of exact edge eigenvalues -/

/-- Exact transfer eigenvalue of a spin-network labeling in a specified
finite edge-elimination order. -/
def networkEigen (order : List Nat) (label : Nat → Nat) : Q' :=
  eliminateLinks (fun edge => eigA coupling (label edge)) order

theorem networkEigen_nonneg (label : Nat → Nat) : ∀ order,
    (0 : Q') ≤ networkEigen order label
  | [] => by change (0 : Q') ≤ 1; decide
  | edge :: rest =>
      Q'.mul_nonneg _ _ (eigA_nonneg (by decide) (label edge))
        (networkEigen_nonneg label rest)

theorem networkEigen_le_one (label : Nat → Nat) : ∀ order,
    networkEigen order label ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | edge :: rest => by
      change eigA coupling (label edge) * networkEigen rest label ≤ (1 : Q')
      have hm := Q'.mul_le_mul_of_nonneg
        (eigA_le_one (w := coupling) (by decide) (by decide) (label edge))
        (networkEigen_le_one label rest)
        (by decide : (0 : Q') ≤ 1)
        (networkEigen_nonneg label rest)
      exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-- A single excited edge is enough to locate the entire nonempty network
mode below the fundamental edge eigenvalue `1/8`; all other edge factors are
nonnegative and at most one. -/
theorem networkEigen_excited_le_eighth (label : Nat → Nat) : ∀ order,
    (∃ edge, edge ∈ order ∧ 1 ≤ label edge) →
      networkEigen order label ≤ eighth
  | [], h => by
      rcases h with ⟨edge, hmem, _⟩
      cases hmem
  | head :: rest, h => by
      rcases h with ⟨edge, hmem, hexc⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · subst edge
        change eigA coupling (label head) * networkEigen rest label ≤ eighth
        have hedge : eigA coupling (label head) ≤ eighth :=
          Q'.le_trans' _ _ _
            (gapEdge_dominates (by decide) (by decide) hexc)
            (Q'.le_of_eqv (by decide : eigA coupling 1 ≈ eighth))
        have hm := Q'.mul_le_mul_of_nonneg hedge
          (networkEigen_le_one label rest)
          (by decide : (0 : Q') ≤ eighth)
          (networkEigen_nonneg label rest)
        exact Q'.le_trans' _ _ _ hm
          (Q'.le_of_eqv (Q'.mul_one_eqv eighth))
      · change eigA coupling (label head) * networkEigen rest label ≤ eighth
        have htail : networkEigen rest label ≤ eighth :=
          networkEigen_excited_le_eighth label rest ⟨edge, hrest, hexc⟩
        have hm := Q'.mul_le_mul_of_nonneg
          (eigA_le_one (w := coupling) (by decide) (by decide) (label head))
          htail (by decide : (0 : Q') ≤ 1)
          (networkEigen_nonneg label rest)
        exact Q'.le_trans' _ _ _ hm
          (Q'.le_of_eqv (Q'.one_mul_eqv eighth))

theorem networkEigen_order_independent (label : Nat → Nat)
    {order order' : List Nat} (h : order.Perm order') :
    networkEigen order label ≈ networkEigen order' label :=
  eliminateLinks_perm (fun edge => eigA coupling (label edge)) h

/-! ## A finite family of globally projected modes -/

/-- `labels i edge` is the irrep label on `edge` in global mode `i`.
Only the first `N` modes are physical; setting later eigenvalues to zero lets
the concrete located-gap interface state a total pointwise bound. -/
def familySquaredEigen (order : List Nat) (labels : Nat → Nat → Nat)
    (N : Nat) (i : Nat) : Q' :=
  if i < N then
    networkEigen order (labels i) * networkEigen order (labels i)
  else 0

theorem familySquaredEigen_nonneg (order : List Nat)
    (labels : Nat → Nat → Nat) (N i : Nat) :
    (0 : Q') ≤ familySquaredEigen order labels N i := by
  by_cases hi : i < N
  · rw [familySquaredEigen, if_pos hi]
    exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (networkEigen order (labels i))
  · rw [familySquaredEigen, if_neg hi]
    exact Q'.le_refl' 0

/-- Every retained mode is globally nonvacuum exactly when it has an excited
edge somewhere in the actual finite edge list. -/
def ExcitedSupport (order : List Nat) (labels : Nat → Nat → Nat)
    (N : Nat) : Prop :=
  ∀ i, i < N → ∃ edge, edge ∈ order ∧ 1 ≤ labels i edge

theorem familySquaredEigen_le_sep (order : List Nat)
    (labels : Nat → Nat → Nat) (N : Nat)
    (hsupport : ExcitedSupport order labels N) (i : Nat) :
    familySquaredEigen order labels N i ≤ eighth * eighth := by
  by_cases hi : i < N
  · rw [familySquaredEigen, if_pos hi]
    let a := networkEigen order (labels i)
    have ha : (0 : Q') ≤ a := networkEigen_nonneg (labels i) order
    have hae : a ≤ eighth :=
      networkEigen_excited_le_eighth (labels i) order (hsupport i hi)
    have h1 : a * a ≤ eighth * a :=
      Q'.mul_le_mul_of_nonneg_right a eighth a hae ha
    have h2 : eighth * a ≤ eighth * eighth :=
      Q'.mul_le_mul_of_nonneg_left a eighth eighth hae (by decide)
    exact Q'.le_trans' _ _ _ h1 h2
  · rw [familySquaredEigen, if_neg hi]
    exact Q'.mul_nonneg eighth eighth (by decide) (by decide)

/-- Exact nonnegative weights already include all Haar and vertex-projector
factors of the globally projected state. -/
def finiteNetworkFamilyModel (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) : SpectralModel :=
  diagOp.toSpectralModel (familySquaredEigen order labels N) weight N
    hweight (familySquaredEigen_nonneg order labels N)

def finiteNetworkFamilyOp (order : List Nat)
    (labels : Nat → Nat → Nat) (N : Nat) : FiniteOp :=
  diagOp (familySquaredEigen order labels N) N

theorem finiteNetworkFamily_lam_is_operator_eigen (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) (i : Nat) (hi : i < N) :
    (finiteNetworkFamilyModel order labels weight N hweight).lam i ≈
      (finiteNetworkFamilyOp order labels N).apply (basis i) i :=
  toSpectralModel_lam_is_eigen (familySquaredEigen order labels N) weight N
    hweight (familySquaredEigen_nonneg order labels N) i hi

def finiteNetworkSquaredSep : Q' := eighth * eighth

theorem finiteNetworkSquaredSep_exact :
    finiteNetworkSquaredSep ≈ Q'.mkPos 1 64 (by decide) := by decide

theorem finiteNetworkSquaredSep_lt_one :
    finiteNetworkSquaredSep < (1 : Q') := by decide

def finiteNetworkFamilyLocatedGap (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i)
    (hsupport : ExcitedSupport order labels N) :
    LocatedSpectralGap
      (finiteNetworkFamilyModel order labels weight N hweight) :=
  diagLocatedGap (familySquaredEigen order labels N) weight N hweight
    (familySquaredEigen_nonneg order labels N)
    finiteNetworkSquaredSep finiteNetworkSquaredSep_lt_one
    (familySquaredEigen_le_sep order labels N hsupport)

theorem finiteNetworkFamily_gapMargin_exact (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i)
    (hsupport : ExcitedSupport order labels N) :
    (finiteNetworkFamilyLocatedGap order labels weight N hweight hsupport).gapMargin
      ≈ Q'.mkPos 63 64 (by decide) := by
  change (1 - finiteNetworkSquaredSep) ≈ Q'.mkPos 63 64 (by decide)
  decide

/-! ## Exact correlators and elimination-order independence -/

def finiteNetworkFamilyNorm (weight : Nat → Q') (N : Nat) : Q' :=
  fsum weight N

def finiteNetworkFamilyTransferredNorm (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat) : Q' :=
  fsum (fun i => weight i *
    (networkEigen order (labels i) * networkEigen order (labels i))) N

theorem finiteNetworkFamily_corr_zero_eq_norm (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    corr (finiteNetworkFamilyModel order labels weight N hweight) 0 ≈
      finiteNetworkFamilyNorm weight N := by
  refine Q'.eqv_trans _ _ _
    (corr_zero (finiteNetworkFamilyModel order labels weight N hweight)) ?_
  unfold finiteNetworkFamilyNorm finiteNetworkFamilyModel
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact Q'.eqv_refl _

theorem finiteNetworkFamily_corr_one_eq_transferred_norm (order : List Nat)
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    corr (finiteNetworkFamilyModel order labels weight N hweight) 1 ≈
      finiteNetworkFamilyTransferredNorm order labels weight N := by
  unfold corr finiteNetworkFamilyModel finiteNetworkFamilyTransferredNorm
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact finSum_eqv_congr_lt _ _ N (fun i hi => by
    change weight i * (familySquaredEigen order labels N i) ^ 1 ≈
      weight i *
        (networkEigen order (labels i) * networkEigen order (labels i))
    unfold familySquaredEigen
    rw [if_pos hi, Q'.pow_succ, Q'.pow_zero]
    exact Q'.mul_eqv_congr_left (weight i) _ _
      (Q'.mul_one_eqv
        (networkEigen order (labels i) * networkEigen order (labels i))))

theorem familySquaredEigen_order_independent
    {order order' : List Nat} (h : order.Perm order')
    (labels : Nat → Nat → Nat) (N i : Nat) :
    familySquaredEigen order labels N i ≈
      familySquaredEigen order' labels N i := by
  by_cases hi : i < N
  · rw [familySquaredEigen, if_pos hi, familySquaredEigen, if_pos hi]
    exact q_mul_congr
      (networkEigen_order_independent (labels i) h)
      (networkEigen_order_independent (labels i) h)
  · rw [familySquaredEigen, if_neg hi, familySquaredEigen, if_neg hi]
    exact Q'.eqv_refl 0

private theorem q_pow_eqv_congr {a b : Q'} (h : a ≈ b) :
    ∀ n : Nat, a ^ n ≈ b ^ n
  | 0 => by
      rw [Q'.pow_zero, Q'.pow_zero]
      exact Q'.eqv_refl 1
  | n + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      exact q_mul_congr h (q_pow_eqv_congr h n)

theorem finiteNetworkFamily_corr_order_independent
    {order order' : List Nat} (h : order.Perm order')
    (labels : Nat → Nat → Nat) (weight : Nat → Q') (N n : Nat)
    (hweight : ∀ i, (0 : Q') ≤ weight i) :
    corr (finiteNetworkFamilyModel order labels weight N hweight) n ≈
      corr (finiteNetworkFamilyModel order' labels weight N hweight) n := by
  unfold corr finiteNetworkFamilyModel
  exact finSum_eqv_of_termwise _ _ (fun i =>
    Q'.mul_eqv_congr_left (weight i) _ _
      (q_pow_eqv_congr
        (familySquaredEigen_order_independent h labels N i) n)) N

end YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope

#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.networkEigen_excited_le_eighth
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.networkEigen_order_independent
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.familySquaredEigen_le_sep
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.finiteNetworkFamily_lam_is_operator_eigen
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.finiteNetworkFamilyLocatedGap
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.finiteNetworkFamily_gapMargin_exact
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.finiteNetworkFamily_corr_zero_eq_norm
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.finiteNetworkFamily_corr_one_eq_transferred_norm
#print axioms YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope.finiteNetworkFamily_corr_order_independent
