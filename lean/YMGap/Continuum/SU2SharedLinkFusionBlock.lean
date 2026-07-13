/-
# The smallest exact two-plaquette shared-link SU(2) fusion block

Two plaquettes meeting at one link do not carry independent fundamental
characters on that link.  Their four tensor labels map to

    00 |-> chi_0,   10 |-> chi_1,   01 |-> chi_1,
    11 |-> chi_1^2 = chi_0 + chi_2.

This file computes the resulting four-by-four Gram block from the completed
bare SU(2) Haar functional.  In irreducible coordinates it is simply

    (a00+a11)(b00+b11) + (a10+a01)(b10+b01) + a11 b11.

The non-unit heat-kernel convolution at `w=1/2` has exact eigenvalues
`1, 1/8, 1/256` on `chi_0,chi_1,chi_2`.  This gives an exact shared-link
transfer matrix.  It is positive, self-adjoint and contractive in the Haar
Gram.

The comparison with the disjoint tensor block fails in two checked ways.
First, `10-01` has positive disjoint norm `1/4` but zero shared-link norm.
Second, the double excitation does not intertwine even modulo the shared
radical: product evolution scales `chi_1^2` by `1/64`, whereas fusion
evolution fixes its vacuum summand and scales only `chi_2` by `1/256`.

Honest scope: this is the smallest one-shared-link fusion block.  It does not
yet assemble all links of two full plaquettes or prove a favorable comparison
bound for an arbitrary lattice volume.  It does permanently exclude the
naive isometric/product intertwiner.
-/

import YMGap.Continuum.SU2SharedLinkFactorizationObstruction

namespace YMGap.Continuum.SU2SharedLinkFusionBlock

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
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

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## Shared-link coordinates and the Haar Gram -/

/-- Coordinates `(00,10,01,11)` before shared-link fusion. -/
abbrev SharedVec := Q' × (Q' × (Q' × Q'))

def vacuumCoord (a : SharedVec) : Q' := a.1 + a.2.2.2
def fundamentalCoord (a : SharedVec) : Q' := a.2.1 + a.2.2.1
def quadraticCoord (a : SharedVec) : Q' := a.2.2.2

/-- Haar Gram after the fusion identities
`chi_1 chi_1 = chi_0 + chi_2`. -/
def sharedGram (a b : SharedVec) : Q' :=
  vacuumCoord a * vacuumCoord b +
    (fundamentalCoord a * fundamentalCoord b +
      quadraticCoord a * quadraticCoord b)

def vacuumMode : SharedVec := (1, (0, (0, 0)))
def leftMode : SharedVec := (0, (1, (0, 0)))
def rightMode : SharedVec := (0, (0, (1, 0)))
def doubleMode : SharedVec := (0, (0, (0, 1)))
def antisymmetricMode : SharedVec := (0, (1, (-1, 0)))

/-- The seven independent Gram entries are literal completed-Haar character
sums.  Symmetry supplies the other nine entries. -/
theorem sharedGram_entries_from_Haar :
    bareVacuumHaar (pmul chi0 chi0) ≈ sharedGram vacuumMode vacuumMode ∧
    bareVacuumHaar (pmul chi0 chi1) ≈ sharedGram vacuumMode leftMode ∧
    bareVacuumHaar (pmul chi0 (pmul chi1 chi1)) ≈
      sharedGram vacuumMode doubleMode ∧
    bareVacuumHaar (pmul chi1 chi1) ≈ sharedGram leftMode leftMode ∧
    bareVacuumHaar (pmul chi1 chi1) ≈ sharedGram leftMode rightMode ∧
    bareVacuumHaar (pmul chi1 (pmul chi1 chi1)) ≈
      sharedGram leftMode doubleMode ∧
    bareVacuumHaar (pmul (pmul chi1 chi1) (pmul chi1 chi1)) ≈
      sharedGram doubleMode doubleMode := by decide

/-- Explicit four-by-four matrix audit:
`[[1,0,0,1],[0,1,1,0],[0,1,1,0],[1,0,0,2]]`. -/
theorem sharedGram_matrix_audit :
    sharedGram vacuumMode vacuumMode ≈ 1 ∧
    sharedGram vacuumMode leftMode ≈ 0 ∧
    sharedGram vacuumMode rightMode ≈ 0 ∧
    sharedGram vacuumMode doubleMode ≈ 1 ∧
    sharedGram leftMode leftMode ≈ 1 ∧
    sharedGram leftMode rightMode ≈ 1 ∧
    sharedGram leftMode doubleMode ≈ 0 ∧
    sharedGram rightMode rightMode ≈ 1 ∧
    sharedGram rightMode doubleMode ≈ 0 ∧
    sharedGram doubleMode doubleMode ≈ 2 := by decide

theorem sharedGram_symm (a b : SharedVec) :
    sharedGram a b ≈ sharedGram b a := by
  unfold sharedGram
  ring_qeqv

/-- Reflection positivity is an exact three-square identity. -/
theorem sharedGram_nonneg (a : SharedVec) :
    (0 : Q') ≤ sharedGram a a :=
  Q'.zero_le_add _ _ (q_mul_self_nonneg (vacuumCoord a))
    (Q'.zero_le_add _ _ (q_mul_self_nonneg (fundamentalCoord a))
      (q_mul_self_nonneg (quadraticCoord a)))

/-! ## Exact heat-kernel transfer on the fused channels -/

def quadraticEigen : Q' := physLinkWeight coupling 2

theorem quadraticEigen_exact :
    quadraticEigen ≈ Q'.mkPos 1 256 (by decide) := by decide

theorem quadraticEigen_nonneg : (0 : Q') ≤ quadraticEigen := by decide
theorem quadraticEigen_le_fundamental : quadraticEigen ≤ eighth := by decide

def vacuumMix : Q' := Q'.mkPos 255 256 (by decide)

theorem vacuumMix_add_quadraticEigen :
    vacuumMix + quadraticEigen ≈ 1 := by decide

/-- In the redundant tensor coordinates this is the matrix
`[[1,0,0,255/256],[0,1/8,0,0],[0,0,1/8,0],[0,0,0,1/256]]`.
The off-diagonal vacuum term is forced by `chi_1^2=chi_0+chi_2`. -/
def sharedTransfer (a : SharedVec) : SharedVec :=
  (a.1 + vacuumMix * a.2.2.2,
    (eighth * a.2.1,
      (eighth * a.2.2.1, quadraticEigen * a.2.2.2)))

theorem sharedTransfer_vacuum_coord (a : SharedVec) :
    vacuumCoord (sharedTransfer a) ≈ vacuumCoord a := by
  unfold vacuumCoord sharedTransfer
  refine Q'.eqv_trans _
    (a.1 + (vacuumMix * a.2.2.2 + quadraticEigen * a.2.2.2)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (a.1 + (vacuumMix + quadraticEigen) * a.2.2.2) _ ?_ ?_
  · exact Q'.add_eqv_congr_left a.1 _ _ (by ring_qeqv)
  · exact Q'.add_eqv_congr_left a.1 _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ vacuumMix_add_quadraticEigen)
        (Q'.one_mul_eqv _))

theorem sharedTransfer_fundamental_coord (a : SharedVec) :
    fundamentalCoord (sharedTransfer a) ≈
      eighth * fundamentalCoord a := by
  unfold fundamentalCoord sharedTransfer
  ring_qeqv

theorem sharedTransfer_quadratic_coord (a : SharedVec) :
    quadraticCoord (sharedTransfer a) ≈
      quadraticEigen * quadraticCoord a := Q'.eqv_refl _

/-- Haar moment after one exact heat-kernel convolution. -/
def translatedSharedGram (a b : SharedVec) : Q' :=
  vacuumCoord a * vacuumCoord b +
    (eighth * (fundamentalCoord a * fundamentalCoord b) +
      quadraticEigen * (quadraticCoord a * quadraticCoord b))

/-- Character representatives after one heat-kernel convolution. -/
def translatedVacuumPoly : Poly := chi0
def translatedFundamentalPoly : Poly := pscale eighth chi1
def translatedDoublePoly : Poly := padd chi0 (pscale quadraticEigen chi2)

/-- Every independent entry of the translated matrix is again a literal Haar
character sum.  This audits the off-diagonal `255/256` reconstruction rather
than assuming it from a matrix ansatz. -/
theorem translatedSharedGram_entries_from_Haar :
    bareVacuumHaar (pmul translatedVacuumPoly chi0) ≈
      translatedSharedGram vacuumMode vacuumMode ∧
    bareVacuumHaar (pmul translatedVacuumPoly chi1) ≈
      translatedSharedGram vacuumMode leftMode ∧
    bareVacuumHaar (pmul translatedVacuumPoly (pmul chi1 chi1)) ≈
      translatedSharedGram vacuumMode doubleMode ∧
    bareVacuumHaar (pmul translatedFundamentalPoly chi1) ≈
      translatedSharedGram leftMode leftMode ∧
    bareVacuumHaar (pmul translatedFundamentalPoly chi1) ≈
      translatedSharedGram leftMode rightMode ∧
    bareVacuumHaar (pmul translatedFundamentalPoly (pmul chi1 chi1)) ≈
      translatedSharedGram leftMode doubleMode ∧
    bareVacuumHaar (pmul translatedDoublePoly (pmul chi1 chi1)) ≈
      translatedSharedGram doubleMode doubleMode := by decide

/-- Exact compression identity derived channel-by-channel from the same Haar
fusion table and the non-unit heat-kernel eigenvalues. -/
theorem shared_same_state_compression (a b : SharedVec) :
    sharedGram (sharedTransfer a) b ≈ translatedSharedGram a b := by
  unfold sharedGram translatedSharedGram
  refine QPoly.q_add_congr
    (Q'.mul_eqv_congr_right _ _ _ (sharedTransfer_vacuum_coord a)) ?_
  exact QPoly.q_add_congr
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (sharedTransfer_fundamental_coord a))
      (Q'.mul_assoc_eqv eighth _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (sharedTransfer_quadratic_coord a))
      (Q'.mul_assoc_eqv quadraticEigen _ _))

theorem sharedTransfer_selfAdjoint (a b : SharedVec) :
    sharedGram (sharedTransfer a) b ≈
      sharedGram a (sharedTransfer b) := by
  refine Q'.eqv_trans _ _ _ (shared_same_state_compression a b) ?_
  refine Q'.eqv_trans _ _ _ (show
      translatedSharedGram a b ≈ translatedSharedGram b a by
        unfold translatedSharedGram
        ring_qeqv) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (shared_same_state_compression b a))
    (sharedGram_symm (sharedTransfer b) a)

theorem sharedTransfer_positive (a : SharedVec) :
    (0 : Q') ≤ sharedGram (sharedTransfer a) a := by
  have hraw : (0 : Q') ≤ translatedSharedGram a a :=
    Q'.zero_le_add _ _ (q_mul_self_nonneg (vacuumCoord a))
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) (q_mul_self_nonneg (fundamentalCoord a)))
        (Q'.mul_nonneg _ _ quadraticEigen_nonneg
          (q_mul_self_nonneg (quadraticCoord a))))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv (Q'.eqv_symm (shared_same_state_compression a a)))

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

theorem sharedTransfer_contraction (a : SharedVec) :
    sharedGram (sharedTransfer a) (sharedTransfer a) ≤ sharedGram a a := by
  have h0 : vacuumCoord (sharedTransfer a) * vacuumCoord (sharedTransfer a) ≤
      vacuumCoord a * vacuumCoord a :=
    Q'.le_of_eqv (q_mul_congr
      (sharedTransfer_vacuum_coord a) (sharedTransfer_vacuum_coord a))
  have h1 : fundamentalCoord (sharedTransfer a) *
      fundamentalCoord (sharedTransfer a) ≤
      fundamentalCoord a * fundamentalCoord a :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (q_mul_congr
        (sharedTransfer_fundamental_coord a)
        (sharedTransfer_fundamental_coord a)))
      (scaled_square_le eighth _ (by decide) (by decide))
  have h2 : quadraticCoord (sharedTransfer a) * quadraticCoord (sharedTransfer a) ≤
      quadraticCoord a * quadraticCoord a :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (q_mul_congr
        (sharedTransfer_quadratic_coord a)
        (sharedTransfer_quadratic_coord a)))
      (scaled_square_le quadraticEigen _ quadraticEigen_nonneg (by decide))
  exact Q'.add_le_add h0 (Q'.add_le_add h1 h2)

/-! ## The correct fusion-quotient intertwiner -/

abbrev IrrepVec := Q' × (Q' × Q')

/-- Quotient-coordinate map `00,10,01,11 -> chi_0,chi_1,chi_2`. -/
def fusionCollapse (a : SharedVec) : IrrepVec :=
  (vacuumCoord a, (fundamentalCoord a, quadraticCoord a))

def irrepGram (a b : IrrepVec) : Q' :=
  a.1 * b.1 + (a.2.1 * b.2.1 + a.2.2 * b.2.2)

def irrepTransfer (a : IrrepVec) : IrrepVec :=
  (a.1, (eighth * a.2.1, quadraticEigen * a.2.2))

def IrrepEq (a b : IrrepVec) : Prop :=
  a.1 ≈ b.1 ∧ a.2.1 ≈ b.2.1 ∧ a.2.2 ≈ b.2.2

/-- The shared Gram is exactly the pullback of the diagonal irreducible Gram. -/
theorem sharedGram_fusionCollapse (a b : SharedVec) :
    sharedGram a b = irrepGram (fusionCollapse a) (fusionCollapse b) := rfl

/-- The non-unit heat-kernel transfer genuinely intertwines with the correct
three-channel fusion quotient. -/
theorem fusionCollapse_transfer_intertwiner (a : SharedVec) :
    IrrepEq (fusionCollapse (sharedTransfer a))
      (irrepTransfer (fusionCollapse a)) :=
  ⟨sharedTransfer_vacuum_coord a,
    sharedTransfer_fundamental_coord a,
    sharedTransfer_quadratic_coord a⟩

/-- The previously located antisymmetric direction is exactly in the fusion
kernel, not an accidental zero of a numerical matrix. -/
theorem antisymmetric_fusionCollapse_zero :
    IrrepEq (fusionCollapse antisymmetricMode) (0, (0, 0)) := by
  unfold IrrepEq fusionCollapse antisymmetricMode vacuumCoord fundamentalCoord
    quadraticCoord
  exact ⟨by decide, by decide, by decide⟩

/-! ## Comparison with the disjoint tensor block -/

/-- Gram of two disjoint retained character channels in tensor order
`00,10,01,11`. -/
def tensorGram (a b : SharedVec) : Q' :=
  a.1 * b.1 +
    (eighth * (a.2.1 * b.2.1) +
      (eighth * (a.2.2.1 * b.2.2.1) +
        (eighth * eighth) * (a.2.2.2 * b.2.2.2)))

def tensorTransfer (a : SharedVec) : SharedVec :=
  (a.1, (eighth * a.2.1,
    (eighth * a.2.2.1, (eighth * eighth) * a.2.2.2)))

theorem antisymmetric_shared_null :
    sharedGram antisymmetricMode antisymmetricMode ≈ 0 := by decide

theorem antisymmetric_tensor_norm :
    tensorGram antisymmetricMode antisymmetricMode ≈ quarter := by decide

/-- Multiplication along the shared link cannot be an isometry from the
disjoint tensor Gram: it kills a vector of exact positive norm `1/4`. -/
theorem shared_multiplication_not_isometric :
    ¬ (∀ a : SharedVec, sharedGram a a ≈ tensorGram a a) := by
  intro h
  have ha := h antisymmetricMode
  have he : (0 : Q') ≈ quarter :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm antisymmetric_shared_null)
      (Q'.eqv_trans _ _ _ ha antisymmetric_tensor_norm)
  exact (by decide : ¬ ((0 : Q') ≈ quarter)) he

def subVec (a b : SharedVec) : SharedVec :=
  (a.1 + (-b.1),
    (a.2.1 + (-b.2.1),
      (a.2.2.1 + (-b.2.2.1), a.2.2.2 + (-b.2.2.2))))

def SharedRadEq (a b : SharedVec) : Prop :=
  sharedGram (subVec a b) (subVec a b) ≈ 0

/-- The double excitation also refutes a spectral intertwiner, even after
passing to the shared-link radical quotient. -/
theorem double_mode_not_intertwined_mod_radical :
    ¬ SharedRadEq (sharedTransfer doubleMode) (tensorTransfer doubleMode) := by
  unfold SharedRadEq subVec sharedTransfer tensorTransfer doubleMode sharedGram
    vacuumCoord fundamentalCoord quadraticCoord quadraticEigen physLinkWeight
    coupling eighth vacuumMix
  decide

end YMGap.Continuum.SU2SharedLinkFusionBlock

#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.sharedGram_entries_from_Haar
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.sharedGram_matrix_audit
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.sharedGram_nonneg
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.quadraticEigen_exact
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.translatedSharedGram_entries_from_Haar
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.shared_same_state_compression
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.sharedTransfer_selfAdjoint
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.sharedTransfer_positive
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.sharedTransfer_contraction
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.sharedGram_fusionCollapse
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.fusionCollapse_transfer_intertwiner
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.shared_multiplication_not_isometric
#print axioms YMGap.Continuum.SU2SharedLinkFusionBlock.double_mode_not_intertwined_mod_radical
