/-
# Arbitrary-superposition tensorization of the SU(2) plaquette block

`SU2PeterWeylVolumeTensor` proves the uniform `1/8` bound on every pure
Peter--Weyl tensor.  Here the same statement is upgraded to the entire finite
linear coefficient space.  The volume carrier is built recursively as five
orthogonal copies of the previous carrier: the vacuum channel has weight `1`
and the four fundamental matrix channels have the derived plaquette weight
`1/16`.  The transfer fixes the vacuum branch and multiplies each fundamental
branch by `1/8`.

The main result is the volume-independent squared-norm estimate

    B(T x,T x) <= (1/8)^2 B(x,x)

for every vector whose vacuum coordinate vanishes.  It is an estimate for
arbitrary superpositions, not merely for basis labels.

Honest scope: this is the exact linear tensor coefficient space of disjoint
copies of the frozen one-plaquette kernel.  It does not identify the coupled,
overlapping plaquette Wilson measure on a four-dimensional lattice with this
orthogonal composition.  A comparison or intertwining theorem for those
shared-link interactions remains necessary; none is assumed here.
-/

import YMGap.Continuum.SU2PeterWeylVolumeTensor

namespace YMGap.Continuum.SU2PeterWeylVolumeGNS

set_option maxHeartbeats 100000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveTimeCompressedTransfer
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

private theorem weighted_one_mul (w p : Q') :
    (w * (1 * p)).eqv (w * p) :=
  Q'.mul_eqv_congr_left w _ _ (Q'.one_mul_eqv p)

/-! ## Scaling and five-channel extension of a GNS datum -/

/-- Multiply a GNS form by a nonnegative exact rational, leaving its linear
carrier and equivalence unchanged. -/
def scaleGNS (w : Q') (hw : (0 : Q') ≤ w) (D : GNSData) : GNSData where
  V := D.V
  veq := D.veq
  veq_refl := D.veq_refl
  veq_symm := D.veq_symm
  veq_trans := D.veq_trans
  zero := D.zero
  add := D.add
  neg := D.neg
  smul := D.smul
  add_congr := D.add_congr
  neg_congr := D.neg_congr
  smul_congr := D.smul_congr
  add_assoc := D.add_assoc
  add_comm := D.add_comm
  zero_add := D.zero_add
  neg_add := D.neg_add
  B := fun a b => w * D.B a b
  B_congr_left := fun b h => Q'.mul_eqv_congr_left w _ _ (D.B_congr_left b h)
  B_add_left := fun a b c =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ (D.B_add_left a b c))
      (Q'.mul_add_eqv w (D.B a c) (D.B b c))
  B_smul_left := fun s a b => by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _ (D.B_smul_left s a b)) ?_
    ring_qeqv
  B_symm := fun a b => Q'.mul_eqv_congr_left w _ _ (D.B_symm a b)
  self_nonneg := fun a => Q'.mul_nonneg _ _ hw (D.self_nonneg a)

theorem scaleGNS_B (w : Q') (hw : (0 : Q') ≤ w) (D : GNSData)
    (a b : D.V) :
    (scaleGNS w hw D).B a b = w * D.B a b := rfl

private def matrixScaled (D : GNSData) : GNSData :=
  scaleGNS fundamentalMatrixWeight
    (Q'.le_of_lt fundamentalMatrixWeight_pos) D

/-- Add the five local plaquette channels to an existing coefficient space.
This is an orthogonal linear direct sum, not the nonlinear pointwise product
quotient that collapses under a pure-product relation. -/
def extendFive (D : GNSData) : GNSData :=
  gnsProduct D
    (gnsProduct (matrixScaled D)
      (gnsProduct (matrixScaled D) (gnsProduct (matrixScaled D) (matrixScaled D))))

/-! ## Recursive volume carrier and transfer -/

/-- Exact finite-volume coefficient GNS datum: dimension `5^volume`. -/
def volumeGNS : Nat → GNSData
  | 0 => qWeightGNS 1 (by decide)
  | n + 1 => extendFive (volumeGNS n)

/-- Recursive tensor transfer.  Every nonvacuum local branch receives the
same audited `1/8` eigenvalue. -/
def volumeTransfer : ∀ n, (volumeGNS n).V → (volumeGNS n).V
  | 0 => fun x => x
  | n + 1 => fun x =>
      (volumeTransfer n x.1,
        ((volumeGNS n).smul eighth (volumeTransfer n x.2.1),
            ((volumeGNS n).smul eighth (volumeTransfer n x.2.2.1),
              ((volumeGNS n).smul eighth (volumeTransfer n x.2.2.2.1),
              (volumeGNS n).smul eighth (volumeTransfer n x.2.2.2.2)))))

/-- The coefficient of the all-vacuum tensor. -/
def vacuumCoordinate : ∀ n, (volumeGNS n).V → Q'
  | 0 => fun x => x
  | n + 1 => fun x => vacuumCoordinate n x.1

/-- The exact vacuum-orthogonal hyperplane in the coefficient carrier. -/
def VacuumPerp {n : Nat} (x : (volumeGNS n).V) : Prop :=
  vacuumCoordinate n x ≈ 0

/-! ## One-volume audit against the plaquette checkpoint -/

/-- At one factor, the recursive Gram is exactly the audited five-dimensional
plaquette Gram.  In particular there is one (not four) vacuum/free branch and
four fundamental matrix branches. -/
theorem oneVolume_B_matches_plaquette (a b : PlaquetteVec) :
    (volumeGNS 1).B a b ≈ plaquetteGNS.B a b := by
  simp only [volumeGNS, extendFive, matrixScaled, scaleGNS, gnsProduct,
    vacuumLine, matrixLine, qWeightGNS]
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (Q'.add_eqv_congr'
      (weighted_one_mul _ _)
      (Q'.add_eqv_congr'
        (weighted_one_mul _ _)
        (Q'.add_eqv_congr' (weighted_one_mul _ _) (weighted_one_mul _ _))))

/-- The recursive transfer at one factor is literally the plaquette transfer;
this excludes a hidden trace multiplicity or a character/eigenvalue swap. -/
theorem oneVolume_transfer_matches (a : PlaquetteVec) :
    volumeTransfer 1 a = plaquetteTransfer a := rfl

/-! ## Scalar and direct-sum norm lemmas -/

theorem B_smul_diag (D : GNSData) (s : Q') (x : D.V) :
    D.B (D.smul s x) (D.smul s x) ≈ s * s * D.B x x := by
  refine Q'.eqv_trans _ _ _ (D.B_smul_left s x (D.smul s x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _ (D.B_smul_right s x x)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv s s (D.B x x))

private theorem eighth_square_le_one : eighth * eighth ≤ (1 : Q') := by decide

private theorem eighth_square_nonneg : (0 : Q') ≤ eighth * eighth := by decide

private theorem five_factor (c w a0 a1 a2 a3 a4 : Q') :
    (c * a0 +
      (w * (c * a1) + (w * (c * a2) + (w * (c * a3) + w * (c * a4))))) ≈
      c * (a0 + (w * a1 + (w * a2 + (w * a3 + w * a4)))) := by
  ring_qeqv

/-- Scaling a vector by `1/8` contracts its squared GNS norm. -/
theorem B_eighth_smul_le (D : GNSData) (x : D.V) :
    D.B (D.smul eighth x) (D.smul eighth x) ≤ D.B x x := by
  have hx := D.self_nonneg x
  have hm := Q'.mul_le_mul_of_nonneg_right
    (eighth * eighth) 1 (D.B x x) eighth_square_le_one hx
  refine Q'.le_trans' _ ((eighth * eighth) * D.B x x) _
    (Q'.le_of_eqv (B_smul_diag D eighth x)) ?_
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- If `y` is no larger than `x`, then `1/8 y` is no larger than
`1/8 x`. -/
theorem B_eighth_mono (D : GNSData) {x y : D.V}
    (h : D.B y y ≤ D.B x x) :
    D.B (D.smul eighth y) (D.smul eighth y) ≤
      D.B (D.smul eighth x) (D.smul eighth x) := by
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (eighth * eighth) h
    eighth_square_nonneg
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (B_smul_diag D eighth y))
    (Q'.le_trans' _ _ _ hm
      (Q'.le_of_eqv (Q'.eqv_symm (B_smul_diag D eighth x))))

theorem B_eighth_of_le (D : GNSData) {x y : D.V}
    (h : D.B y y ≤ D.B x x) :
    D.B (D.smul eighth y) (D.smul eighth y) ≤ D.B x x :=
  Q'.le_trans' _ _ _ (B_eighth_mono D h) (B_eighth_smul_le D x)

/-- Exact `1/64` version used in the excited-sector induction. -/
theorem B_eighth_square_of_le (D : GNSData) {x y : D.V}
    (h : D.B y y ≤ D.B x x) :
    D.B (D.smul eighth y) (D.smul eighth y) ≤
      (eighth * eighth) * D.B x x := by
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (eighth * eighth) h
    eighth_square_nonneg
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (B_smul_diag D eighth y)) hm

/-! ## Arbitrary-superposition contraction -/

/-- The recursive transfer is contractive on every finite-volume
superposition. -/
theorem volumeTransfer_contraction : ∀ n (x : (volumeGNS n).V),
    (volumeGNS n).B (volumeTransfer n x) (volumeTransfer n x) ≤
      (volumeGNS n).B x x
  | 0, x => Q'.le_refl' _
  | n + 1, x => by
      simp only [volumeGNS, volumeTransfer, extendFive, gnsProduct, matrixScaled,
        scaleGNS]
      exact Q'.add_le_add (volumeTransfer_contraction n x.1)
        (Q'.add_le_add
          (Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
            (B_eighth_of_le (volumeGNS n) (volumeTransfer_contraction n x.2.1))
            (Q'.le_of_lt fundamentalMatrixWeight_pos))
          (Q'.add_le_add
            (Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
              (B_eighth_of_le (volumeGNS n) (volumeTransfer_contraction n x.2.2.1))
              (Q'.le_of_lt fundamentalMatrixWeight_pos))
            (Q'.add_le_add
              (Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
                (B_eighth_of_le (volumeGNS n) (volumeTransfer_contraction n x.2.2.2.1))
                (Q'.le_of_lt fundamentalMatrixWeight_pos))
              (Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
                (B_eighth_of_le (volumeGNS n) (volumeTransfer_contraction n x.2.2.2.2))
                (Q'.le_of_lt fundamentalMatrixWeight_pos)))))

/-- **Uniform arbitrary-superposition tensor gap.**  On the exact
vacuum-orthogonal hyperplane, every finite volume contracts in squared norm
by the same factor `(1/8)^2`. -/
theorem volumeTransfer_uniform_vacuumPerp : ∀ n (x : (volumeGNS n).V),
    VacuumPerp x →
    (volumeGNS n).B (volumeTransfer n x) (volumeTransfer n x) ≤
      (eighth * eighth) * (volumeGNS n).B x x
  | 0, x => by
      intro h
      have hv : (volumeGNS 0).veq x (volumeGNS 0).zero := by
        simpa [VacuumPerp, vacuumCoordinate, volumeGNS, qWeightGNS] using h
      have hB : ((volumeGNS 0).B x x).eqv 0 :=
        Q'.eqv_trans _ _ _ ((volumeGNS 0).B_diag_congr hv)
          ((volumeGNS 0).B_zero_left (volumeGNS 0).zero)
      have hR : ((eighth * eighth) * (volumeGNS 0).B x x).eqv 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (eighth * eighth) _ _ hB)
          (Q'.mul_zero_eqv _)
      exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hB)
        (Q'.le_of_eqv (Q'.eqv_symm hR))
  | n + 1, x => by
      intro h
      have hfirst : VacuumPerp x.1 := by
        simpa [VacuumPerp, vacuumCoordinate] using h
      have h0 := volumeTransfer_uniform_vacuumPerp n x.1 hfirst
      have h1 := Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
        (B_eighth_square_of_le (volumeGNS n)
          (volumeTransfer_contraction n x.2.1))
        (Q'.le_of_lt fundamentalMatrixWeight_pos)
      have h2 := Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
        (B_eighth_square_of_le (volumeGNS n)
          (volumeTransfer_contraction n x.2.2.1))
        (Q'.le_of_lt fundamentalMatrixWeight_pos)
      have h3 := Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
        (B_eighth_square_of_le (volumeGNS n)
          (volumeTransfer_contraction n x.2.2.2.1))
        (Q'.le_of_lt fundamentalMatrixWeight_pos)
      have h4 := Q'.mul_le_mul_of_nonneg_left _ _ fundamentalMatrixWeight
        (B_eighth_square_of_le (volumeGNS n)
          (volumeTransfer_contraction n x.2.2.2.2))
        (Q'.le_of_lt fundamentalMatrixWeight_pos)
      simp only [volumeGNS, volumeTransfer, extendFive, gnsProduct, matrixScaled,
        scaleGNS]
      have hs := Q'.add_le_add h0
        (Q'.add_le_add h1 (Q'.add_le_add h2 (Q'.add_le_add h3 h4)))
      refine Q'.le_trans' _
        ((eighth * eighth) * (volumeGNS n).B x.1 x.1 +
          (fundamentalMatrixWeight * ((eighth * eighth) * (volumeGNS n).B x.2.1 x.2.1) +
            (fundamentalMatrixWeight * ((eighth * eighth) * (volumeGNS n).B x.2.2.1 x.2.2.1) +
              (fundamentalMatrixWeight *
                  ((eighth * eighth) * (volumeGNS n).B x.2.2.2.1 x.2.2.2.1) +
                fundamentalMatrixWeight *
                  ((eighth * eighth) * (volumeGNS n).B x.2.2.2.2 x.2.2.2.2))))) _ hs ?_
      exact Q'.le_of_eqv
        (five_factor (eighth * eighth) fundamentalMatrixWeight
          ((volumeGNS n).B x.1 x.1)
          ((volumeGNS n).B x.2.1 x.2.1)
          ((volumeGNS n).B x.2.2.1 x.2.2.1)
          ((volumeGNS n).B x.2.2.2.1 x.2.2.2.1)
          ((volumeGNS n).B x.2.2.2.2 x.2.2.2.2))

end YMGap.Continuum.SU2PeterWeylVolumeGNS

#print axioms YMGap.Continuum.SU2PeterWeylVolumeGNS.scaleGNS
#print axioms YMGap.Continuum.SU2PeterWeylVolumeGNS.oneVolume_B_matches_plaquette
#print axioms YMGap.Continuum.SU2PeterWeylVolumeGNS.oneVolume_transfer_matches
#print axioms YMGap.Continuum.SU2PeterWeylVolumeGNS.B_smul_diag
#print axioms YMGap.Continuum.SU2PeterWeylVolumeGNS.B_eighth_smul_le
#print axioms YMGap.Continuum.SU2PeterWeylVolumeGNS.volumeTransfer_contraction
#print axioms YMGap.Continuum.SU2PeterWeylVolumeGNS.volumeTransfer_uniform_vacuumPerp
