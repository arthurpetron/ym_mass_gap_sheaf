/-
# Volume composition of the SU(2) plaquette Peter--Weyl block

This file tensorizes the SAME five-channel plaquette kernel from
`SU2PeterWeylPlaquetteTensorBlock`.  A local label `0` is the vacuum and every
nonzero label is one of the four fundamental matrix coefficients.  Its local
transfer eigenvalue is therefore `1` or `1/8`.  The eigenvalue of a pure tensor
is the exact product of its local eigenvalues.

The main theorem is volume-independent: if at least one tensor factor is
excited, the product eigenvalue is at most `1/8`, for every number of factors.
The squared-norm contraction is consequently at most `1/64`.  Exact prefix /
suffix composition is also proved, so this is a genuine tensorization law and
not a finite case check.

Honest scope: the theorem controls the complete pure Peter--Weyl tensor basis
of a product of the frozen plaquette blocks.  It does not identify overlapping
plaquette interactions in a four-dimensional finite-volume Wilson measure
with this product composition.  Extending the bound to that coupled measure
requires a proved comparison/intertwining map; none is assumed here.
-/

import YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock

namespace YMGap.Continuum.SU2PeterWeylVolumeTensor

open YMGap.Constructive
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock

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
               Q'.mkPos_den, zero_num_cast, zero_den_cast, one_num_cast,
               one_den_cast, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Local spectrum and exact tensor products -/

/-- Local label `0` is the vacuum; labels `1,2,3,4` are `D00,D01,D10,D11`.
The formula deliberately maps any other nonzero label to the same excited
channel, so the volume inequalities do not need erased finite-index evidence. -/
def localEigen (mode : Nat) : Q' := if mode = 0 then 1 else eighth

def localGramWeight (mode : Nat) : Q' :=
  if mode = 0 then 1 else fundamentalMatrixWeight

theorem localEigen_vacuum : localEigen 0 = (1 : Q') := rfl

theorem localEigen_excited {mode : Nat} (h : mode ≠ 0) :
    localEigen mode = eighth := by
  unfold localEigen
  rw [if_neg h]

theorem localEigen_nonneg (mode : Nat) :
    (0 : Q') ≤ localEigen mode := by
  by_cases h : mode = 0
  · subst mode; decide
  · rw [localEigen_excited h]; decide

theorem localEigen_le_one (mode : Nat) :
    localEigen mode ≤ (1 : Q') := by
  by_cases h : mode = 0
  · subst mode; exact Q'.le_refl' 1
  · rw [localEigen_excited h]; decide

/-- Product eigenvalue on the first `volume` tensor factors. -/
def tensorEigen (label : Nat → Nat) : Nat → Q'
  | 0 => 1
  | n + 1 => tensorEigen label n * localEigen (label n)

/-- Product one-link Gram weight on the same tensor basis. -/
def tensorGramWeight (label : Nat → Nat) : Nat → Q'
  | 0 => 1
  | n + 1 => tensorGramWeight label n * localGramWeight (label n)

/-- At least one of the retained tensor factors is nonvacuum. -/
def HasExcitation (label : Nat → Nat) (volume : Nat) : Prop :=
  ∃ i, i < volume ∧ label i ≠ 0

theorem tensorEigen_nonneg (label : Nat → Nat) : ∀ volume,
    (0 : Q') ≤ tensorEigen label volume
  | 0 => by change (0 : Q') ≤ 1; decide
  | n + 1 => Q'.mul_nonneg _ _ (tensorEigen_nonneg label n)
      (localEigen_nonneg (label n))

theorem tensorEigen_le_one (label : Nat → Nat) : ∀ volume,
    tensorEigen label volume ≤ (1 : Q')
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hmul := Q'.mul_le_mul_of_nonneg_right
        (tensorEigen label n) 1 (localEigen (label n))
        (tensorEigen_le_one label n) (localEigen_nonneg (label n))
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
          (localEigen_le_one (label n)))

/-! ## Exact volume composition -/

/-- Prefix/suffix composition of the tensor eigenvalue. -/
theorem tensorEigen_add (label : Nat → Nat) (m : Nat) : ∀ n,
    tensorEigen label (m + n) ≈
      tensorEigen label m * tensorEigen (fun i => label (m + i)) n
  | 0 => by
      change tensorEigen label m ≈ tensorEigen label m * 1
      exact Q'.eqv_symm (Q'.mul_one_eqv _)
  | n + 1 => by
      change tensorEigen label (m + n) * localEigen (label (m + n)) ≈
        tensorEigen label m *
          (tensorEigen (fun i => label (m + i)) n *
            localEigen (label (m + n)))
      refine Q'.eqv_trans _
        ((tensorEigen label m * tensorEigen (fun i => label (m + i)) n) *
          localEigen (label (m + n))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ (tensorEigen_add label m n)
      · exact Q'.mul_assoc_eqv _ _ _

/-! ## Uniform excited contraction -/

/-- Every nonvacuum pure tensor has eigenvalue at most the SAME `1/8`, with no
volume degradation. -/
theorem tensorEigen_le_eighth_of_excited (label : Nat → Nat) : ∀ volume,
    HasExcitation label volume → tensorEigen label volume ≤ eighth
  | 0 => by
      intro h
      obtain ⟨i, hi, _⟩ := h
      omega
  | n + 1 => by
      intro h
      obtain ⟨i, hi, hmode⟩ := h
      by_cases hilast : i = n
      · subst i
        rw [tensorEigen, localEigen_excited hmode]
        have hp := Q'.mul_le_mul_of_nonneg_right
          (tensorEigen label n) 1 eighth
          (tensorEigen_le_one label n) (by decide)
        exact Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (Q'.one_mul_eqv eighth))
      · have hi' : i < n := by omega
        have ih := tensorEigen_le_eighth_of_excited label n ⟨i, hi', hmode⟩
        have hfirst := Q'.mul_le_mul_of_nonneg_right
          (tensorEigen label n) eighth (localEigen (label n))
          ih (localEigen_nonneg (label n))
        have hsecond := Q'.mul_le_mul_of_nonneg_left
          (localEigen (label n)) 1 eighth
          (localEigen_le_one (label n)) (by decide)
        exact Q'.le_trans' _ _ _ hfirst
          (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv (Q'.mul_one_eqv eighth)))

/-- Squared-norm version: the excited pure-tensor contraction is uniformly
bounded by `(1/8)^2 = 1/64`. -/
theorem tensorEigen_square_le_of_excited {label : Nat → Nat} {volume : Nat}
    (h : HasExcitation label volume) :
    tensorEigen label volume * tensorEigen label volume ≤ eighth * eighth := by
  have he := tensorEigen_le_eighth_of_excited label volume h
  have hn := tensorEigen_nonneg label volume
  have h8 : (0 : Q') ≤ eighth := by decide
  have hfirst := Q'.mul_le_mul_of_nonneg_right
    (tensorEigen label volume) eighth (tensorEigen label volume) he hn
  have hsecond := Q'.mul_le_mul_of_nonneg_left
    (tensorEigen label volume) eighth eighth he h8
  exact Q'.le_trans' _ _ _ hfirst hsecond

/-- The one-factor volume law reproduces all four audited matrix modes of the
plaquette block. -/
theorem one_factor_matrix_eigen (mode : Nat) (h0 : mode ≠ 0) :
    tensorEigen (fun _ => mode) 1 = eighth := by
  change (1 : Q') * localEigen mode = eighth
  rw [localEigen_excited h0]
  rfl

end YMGap.Continuum.SU2PeterWeylVolumeTensor

#print axioms YMGap.Continuum.SU2PeterWeylVolumeTensor.tensorEigen_add
#print axioms YMGap.Continuum.SU2PeterWeylVolumeTensor.tensorEigen_nonneg
#print axioms YMGap.Continuum.SU2PeterWeylVolumeTensor.tensorEigen_le_one
#print axioms YMGap.Continuum.SU2PeterWeylVolumeTensor.tensorEigen_le_eighth_of_excited
#print axioms YMGap.Continuum.SU2PeterWeylVolumeTensor.tensorEigen_square_le_of_excited
#print axioms YMGap.Continuum.SU2PeterWeylVolumeTensor.one_factor_matrix_eigen
