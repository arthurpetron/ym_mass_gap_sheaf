/-
# A same-state finite-character Wilson compression with eigenvalue one half

The pure-product `halfReferenceWeight` pilots collapse because their Wilson
form sees only one total-character coordinate.  This module replaces that
rank-one carrier by the exact group algebra of the Klein four group.  Its
reference functional is coefficient extraction at the identity, i.e. the
finite-group Haar/character functional, and convolution makes

    I0(a* a) = a_e^2 + a_a^2 + a_b^2 + a_c^2.

The actual `ReferenceWeight` is reweighted by the non-unit kernel

    w = delta_e + (1/2) delta_c.

Its weighted form is positive by an explicit rational sum of squares.  The
group automorphism interchanging `a` and `b` fixes `w`, hence is an exact
state-preserving ambient time action on the SAME interacting Wilson GNS.
Compressing it to the positive-time plane spanned by `delta_e` and `delta_a`
gives

    T delta_e = delta_e,       T delta_a = (1/2) delta_a.

The plane Gram matrix is the identity, so the excited coordinate is retained
and the compression is not rank one.  Every identity is derived from the
finite convolution table and exact `Q'` arithmetic; no operator property or
measured constant is assumed.

Honest scope: this is a finite nontrivial-transfer mechanism test on a genuine
non-unit `ReferenceWeight`, not the SU(2) plaquette state.  The remaining
physical step is to replace the Klein character table by the finite SU(2)
Peter--Weyl/matrix-coefficient resolution of the interacting Wilson action
while preserving the same compression identities uniformly in volume.
-/

import YMGap.Continuum.PositiveTimeCompressedTransfer
import YMGap.Continuum.ReferenceWeightTimeGeometry
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.KleinCharacterWilsonCompression

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.PlaquetteReweight
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 2000000

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

/-! ## The exact Klein-four character algebra -/

/-- Coefficients of `delta_e, delta_a, delta_b, delta_c` in `Q'[V_4]`. -/
abbrev KVec := Q' × (Q' × (Q' × Q'))

def kzero : KVec := (0, (0, (0, 0)))
def kone : KVec := (1, (0, (0, 0)))

def kadd (x y : KVec) : KVec :=
  (x.1 + y.1, (x.2.1 + y.2.1,
    (x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)))

def kneg (x : KVec) : KVec :=
  (-x.1, (-x.2.1, (-x.2.2.1, -x.2.2.2)))

def ksmul (s : Q') (x : KVec) : KVec :=
  (s * x.1, (s * x.2.1, (s * x.2.2.1, s * x.2.2.2)))

/-- Convolution in `Q'[V_4]`, in the order `(e,a,b,c)` with `ab=c`. -/
def kmul (x y : KVec) : KVec :=
  ( x.1 * y.1 + (x.2.1 * y.2.1 +
      (x.2.2.1 * y.2.2.1 + x.2.2.2 * y.2.2.2)),
    ( x.1 * y.2.1 + (x.2.1 * y.1 +
        (x.2.2.1 * y.2.2.2 + x.2.2.2 * y.2.2.1)),
      ( x.1 * y.2.2.1 + (x.2.2.1 * y.1 +
          (x.2.1 * y.2.2.2 + x.2.2.2 * y.2.1)),
        x.1 * y.2.2.2 + (x.2.2.2 * y.1 +
          (x.2.1 * y.2.2.1 + x.2.2.1 * y.2.1)))))

/-- All elements of `V_4` are self-inverse, so the real group-algebra star is
the identity. -/
def kstar (x : KVec) : KVec := x

def kleinAlg : ObsAlg where
  carrier := KVec
  one := kone
  mul := kmul
  star := kstar

private theorem qmul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## Finite Haar state and the non-unit interacting weight -/

/-- Finite-group Haar in the convolution picture: coefficient at `delta_e`. -/
def kleinHaar : ProbFunctional kleinAlg where
  E := fun x => x.1
  normalized := rfl
  positive := by
    intro x
    change (0 : Q') ≤
      x.1 * x.1 + (x.2.1 * x.2.1 +
        (x.2.2.1 * x.2.2.1 + x.2.2.2 * x.2.2.2))
    exact Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg x.1)
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg x.2.1)
        (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg x.2.2.1)
          (SumOfSquares.q_mul_self_nonneg x.2.2.2)))

def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The non-unit positive convolution kernel `delta_e + (1/2) delta_c`. -/
def kleinWeight : KVec := (1, (0, (0, half)))

/-- Twice the weighted quadratic form, displayed as four rational squares. -/
def doubledSOS (x : KVec) : Q' :=
  (x.1 + x.2.2.2) * (x.1 + x.2.2.2) +
    ((x.1 * x.1 + x.2.2.2 * x.2.2.2) +
      ((x.2.1 + x.2.2.1) * (x.2.1 + x.2.2.1) +
        (x.2.1 * x.2.1 + x.2.2.1 * x.2.2.1)))

/-- The exact weighted quadratic form as a visibly nonnegative SOS. -/
def weightedSOS (x : KVec) : Q' := half * doubledSOS x

private def weightedRawExpr : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 2)
      (.add (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 1))
          (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))))
    (.add (.mul (.var 0) (.var 3))
      (.add (.mul (.var 3) (.var 0))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1)))))

private def weightedSOSExpr : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.var 0) (.var 3)) (.add (.var 0) (.var 3)))
    (.add
      (.add (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))
      (.add
        (.mul (.add (.var 1) (.var 2)) (.add (.var 1) (.var 2)))
        (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))))

private theorem weighted_expr_normal :
    RingNormaliser.normalize weightedRawExpr =
      RingNormaliser.normalize weightedSOSExpr := by decide

private theorem rawDoubled_eq_sos (x : KVec) :
    (2 : Q') * (kmul x x).1 + (kmul x x).2.2.2 ≈ doubledSOS x := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    weightedRawExpr weightedSOSExpr weighted_expr_normal
    (fun i => if i = 0 then x.1 else if i = 1 then x.2.1 else
      if i = 2 then x.2.2.1 else x.2.2.2)
  simpa [RingNormaliser.eval, weightedRawExpr, weightedSOSExpr,
    kmul, doubledSOS] using h

private theorem half_two_mul (q : Q') : half * ((2 : Q') * q) ≈ q := by
  have htwo : half * (2 : Q') ≈ 1 := by decide
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half 2 q)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ q htwo)
    (Q'.one_mul_eqv q)

private theorem rawWeighted_eq_sos (x : KVec) :
    (kmul x x).1 + half * (kmul x x).2.2.2 ≈ weightedSOS x := by
  let q0 := (kmul x x).1
  let q3 := (kmul x x).2.2.2
  refine Q'.eqv_trans _ (half * ((2 : Q') * q0) + half * q3) _
    (QPoly.q_add_congr (Q'.eqv_symm (half_two_mul q0)) (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ (half * ((2 : Q') * q0 + q3)) _
    (Q'.eqv_symm (Q'.mul_add_eqv half ((2 : Q') * q0) q3)) ?_
  exact Q'.mul_eqv_congr_left half _ _ (rawDoubled_eq_sos x)

private theorem weight_left_form (z : KVec) :
    (kmul kleinWeight z).1 ≈ z.1 + half * z.2.2.2 := by
  unfold kmul kleinWeight
  ring_qeqv

theorem weightedSOS_nonneg (x : KVec) : (0 : Q') ≤ weightedSOS x := by
  unfold weightedSOS doubledSOS
  apply Q'.mul_nonneg _ _ (by decide)
  exact Q'.zero_le_add _ _
    (SumOfSquares.q_mul_self_nonneg (x.1 + x.2.2.2))
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg x.1)
        (SumOfSquares.q_mul_self_nonneg x.2.2.2))
      (Q'.zero_le_add _ _
        (SumOfSquares.q_mul_self_nonneg (x.2.1 + x.2.2.1))
        (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg x.2.1)
          (SumOfSquares.q_mul_self_nonneg x.2.2.1))))

theorem weighted_form_eq_sos (x : KVec) :
    kleinHaar.E (kleinAlg.mul kleinWeight
      (kleinAlg.mul (kleinAlg.star x) x)) ≈ weightedSOS x := by
  change (kmul kleinWeight (kmul x x)).1 ≈ weightedSOS x
  exact Q'.eqv_trans _ _ _ (weight_left_form (kmul x x))
    (rawWeighted_eq_sos x)

/-- The actual non-unit interacting finite character state.  Its partition
function is strictly `1`, while its weighted positivity is derived from the
four rational squares above. -/
def kleinReferenceWeight : ReferenceWeight kleinAlg where
  I₀ := kleinHaar
  w := kleinWeight
  Z := kleinHaar.E (kleinAlg.mul kleinWeight kleinAlg.one)
  Z_eq := rfl
  Z_pos := by decide
  weighted_pos := by
    intro x
    exact Q'.le_trans' _ _ _ (weightedSOS_nonneg x)
      (Q'.le_of_eqv (Q'.eqv_symm (weighted_form_eq_sos x)))

theorem kleinWeight_nonunit : kleinReferenceWeight.w ≠ kleinAlg.one := by
  intro h
  have h3 := congrArg (fun x : KVec => x.2.2.2) h
  exact (by decide : ¬ (half = (0 : Q'))) h3

theorem partition_eqv_one : kleinReferenceWeight.Z ≈ 1 := by decide

theorem partition_recip_eqv_one : recip kleinReferenceWeight.Z ≈ 1 := by
  have hprod : recip kleinReferenceWeight.Z * kleinReferenceWeight.Z ≈ 1 :=
    recip_mul_eqv_one kleinReferenceWeight.Z_pos
  have hcollapse : recip kleinReferenceWeight.Z * kleinReferenceWeight.Z ≈
      recip kleinReferenceWeight.Z :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (recip kleinReferenceWeight.Z) _ _ partition_eqv_one)
      (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcollapse) hprod

/-- The normalized interacting expectation is the two-term finite character
sum `x_e + (1/2)x_c`. -/
theorem interacting_expectation (x : KVec) :
    kleinReferenceWeight.E_Λ x ≈ x.1 + half * x.2.2.2 := by
  change
    (1 * x.1 + (0 * x.2.1 + (0 * x.2.2.1 + half * x.2.2.2))) *
        recip kleinReferenceWeight.Z ≈ x.1 + half * x.2.2.2
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (1 * x.1 + (0 * x.2.1 + (0 * x.2.2.1 + half * x.2.2.2)))
      _ _ partition_recip_eqv_one) ?_
  ring_qeqv

/-! ## The exact Wilson carrier on the same interacting state -/

def kleinModule : WilsonGNSData.CarrierModule kleinAlg where
  veq := fun x y => x.1 ≈ y.1 ∧ x.2.1 ≈ y.2.1 ∧
    x.2.2.1 ≈ y.2.2.1 ∧ x.2.2.2 ≈ y.2.2.2
  veq_refl := fun x => ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩
  veq_symm := fun h => ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2.1,
    Q'.eqv_symm h.2.2.1, Q'.eqv_symm h.2.2.2⟩
  veq_trans := fun h k =>
    ⟨Q'.eqv_trans _ _ _ h.1 k.1,
      Q'.eqv_trans _ _ _ h.2.1 k.2.1,
      Q'.eqv_trans _ _ _ h.2.2.1 k.2.2.1,
      Q'.eqv_trans _ _ _ h.2.2.2 k.2.2.2⟩
  zero := kzero
  add := kadd
  neg := kneg
  smul := ksmul
  add_congr := by
    intro a a' b b' ha hb
    exact ⟨QPoly.q_add_congr ha.1 hb.1,
      QPoly.q_add_congr ha.2.1 hb.2.1,
      QPoly.q_add_congr ha.2.2.1 hb.2.2.1,
      QPoly.q_add_congr ha.2.2.2 hb.2.2.2⟩
  neg_congr := by
    intro a a' h
    exact ⟨Q'.neg_eqv_congr _ _ h.1, Q'.neg_eqv_congr _ _ h.2.1,
      Q'.neg_eqv_congr _ _ h.2.2.1, Q'.neg_eqv_congr _ _ h.2.2.2⟩
  smul_congr := by
    intro s a a' h
    exact ⟨Q'.mul_eqv_congr_left s _ _ h.1,
      Q'.mul_eqv_congr_left s _ _ h.2.1,
      Q'.mul_eqv_congr_left s _ _ h.2.2.1,
      Q'.mul_eqv_congr_left s _ _ h.2.2.2⟩
  add_assoc := fun a b c =>
    ⟨Q'.add_assoc_eqv _ _ _, Q'.add_assoc_eqv _ _ _,
      Q'.add_assoc_eqv _ _ _, Q'.add_assoc_eqv _ _ _⟩
  add_comm := fun a b =>
    ⟨Q'.add_comm_eqv _ _, Q'.add_comm_eqv _ _,
      Q'.add_comm_eqv _ _, Q'.add_comm_eqv _ _⟩
  zero_add := fun a =>
    ⟨QPoly.q_zero_add_eqv _, QPoly.q_zero_add_eqv _,
      QPoly.q_zero_add_eqv _, QPoly.q_zero_add_eqv _⟩
  neg_add := fun a =>
    ⟨Q'.neg_add_self_eqv _, Q'.neg_add_self_eqv _,
      Q'.neg_add_self_eqv _, Q'.neg_add_self_eqv _⟩
  mul_congr := by
    intro a a' b b' ha hb
    unfold kleinAlg kmul
    exact
      ⟨QPoly.q_add_congr (qmul_congr ha.1 hb.1)
          (QPoly.q_add_congr (qmul_congr ha.2.1 hb.2.1)
            (QPoly.q_add_congr (qmul_congr ha.2.2.1 hb.2.2.1)
              (qmul_congr ha.2.2.2 hb.2.2.2))),
        QPoly.q_add_congr (qmul_congr ha.1 hb.2.1)
          (QPoly.q_add_congr (qmul_congr ha.2.1 hb.1)
            (QPoly.q_add_congr (qmul_congr ha.2.2.1 hb.2.2.2)
              (qmul_congr ha.2.2.2 hb.2.2.1))),
        QPoly.q_add_congr (qmul_congr ha.1 hb.2.2.1)
          (QPoly.q_add_congr (qmul_congr ha.2.2.1 hb.1)
            (QPoly.q_add_congr (qmul_congr ha.2.1 hb.2.2.2)
              (qmul_congr ha.2.2.2 hb.2.1))),
        QPoly.q_add_congr (qmul_congr ha.1 hb.2.2.2)
          (QPoly.q_add_congr (qmul_congr ha.2.2.2 hb.1)
            (QPoly.q_add_congr (qmul_congr ha.2.1 hb.2.2.1)
              (qmul_congr ha.2.2.1 hb.2.1)))⟩
  star_congr := fun h => h
  star_add := fun _ _ => ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩
  star_smul := fun _ _ => ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩
  mul_add_right := by
    intro a b c
    unfold kleinAlg kmul kadd
    exact ⟨by ring_qeqv, by ring_qeqv, by ring_qeqv, by ring_qeqv⟩
  smul_mul := by
    intro s a b
    unfold kleinAlg kmul ksmul
    exact ⟨by ring_qeqv, by ring_qeqv, by ring_qeqv, by ring_qeqv⟩

theorem expectation_congr {x y : KVec} (h : kleinModule.veq x y) :
    kleinReferenceWeight.E_Λ x ≈ kleinReferenceWeight.E_Λ y := by
  refine Q'.eqv_trans _ _ _ (interacting_expectation x) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr h.1 (Q'.mul_eqv_congr_left half _ _ h.2.2.2)) ?_
  exact Q'.eqv_symm (interacting_expectation y)

theorem expectation_add (x y : KVec) :
    kleinReferenceWeight.E_Λ (kleinModule.add x y) ≈
      kleinReferenceWeight.E_Λ x + kleinReferenceWeight.E_Λ y := by
  refine Q'.eqv_trans _ _ _ (interacting_expectation _) ?_
  refine Q'.eqv_trans _ _ _ (show
      (x.1 + y.1) + half * (x.2.2.2 + y.2.2.2) ≈
        (x.1 + half * x.2.2.2) + (y.1 + half * y.2.2.2) by
      change (kleinModule.add x y).1 +
        half * (kleinModule.add x y).2.2.2 ≈ _
      unfold kleinModule kadd
      ring_qeqv) ?_
  exact Q'.eqv_symm
    (QPoly.q_add_congr (interacting_expectation x) (interacting_expectation y))

theorem expectation_smul (s : Q') (x : KVec) :
    kleinReferenceWeight.E_Λ (kleinModule.smul s x) ≈
      s * kleinReferenceWeight.E_Λ x := by
  refine Q'.eqv_trans _ _ _ (interacting_expectation _) ?_
  refine Q'.eqv_trans _ _ _ (show
      s * x.1 + half * (s * x.2.2.2) ≈
        s * (x.1 + half * x.2.2.2) by
      change (kleinModule.smul s x).1 +
        half * (kleinModule.smul s x).2.2.2 ≈ _
      unfold kleinModule ksmul
      ring_qeqv) ?_
  exact Q'.eqv_symm (Q'.mul_eqv_congr_left s _ _ (interacting_expectation x))

private theorem interacting_product_comm (x y : KVec) :
    (kmul x y).1 + half * (kmul x y).2.2.2 ≈
      (kmul y x).1 + half * (kmul y x).2.2.2 := by
  apply QPoly.q_add_congr
  · unfold kmul
    exact QPoly.q_add_congr (Q'.mul_comm_eqv _ _)
      (QPoly.q_add_congr (Q'.mul_comm_eqv _ _)
        (QPoly.q_add_congr (Q'.mul_comm_eqv _ _) (Q'.mul_comm_eqv _ _)))
  · apply Q'.mul_eqv_congr_left
    unfold kmul
    ring_qeqv

theorem expectation_conj (x y : KVec) :
    kleinReferenceWeight.E_Λ (kleinAlg.mul (kleinAlg.star x) y) ≈
      kleinReferenceWeight.E_Λ (kleinAlg.mul (kleinAlg.star y) x) := by
  refine Q'.eqv_trans _ _ _ (interacting_expectation _) ?_
  refine Q'.eqv_trans _ _ _ (interacting_product_comm x y) ?_
  exact Q'.eqv_symm (interacting_expectation _)

def kleinWilson : WilsonGNSData kleinAlg :=
  WilsonGNSData.ofReferenceWeight kleinReferenceWeight kleinModule
    expectation_congr expectation_add expectation_smul expectation_conj

abbrev kleinGNS : GNSData := kleinWilson.toGNSData

/-! ## Genuine time automorphism and the exact interacting Gram form -/

/-- The nontrivial automorphism of `V_4` interchanging `a` and `b`. -/
def swapAB (x : KVec) : KVec := (x.1, (x.2.2.1, (x.2.1, x.2.2.2)))

theorem swapAB_involutive (x : KVec) : swapAB (swapAB x) = x := rfl

/-- Time is a convolution-algebra automorphism in the carrier setoid.  The
minimal `ObsHom` interface asks for structural equality of unreduced `Q'`
representatives, which is intentionally stronger than rational equality; the
physical carrier law is therefore stated at its correct semantic equality. -/
theorem swapAB_mul_veq (x y : KVec) :
    kleinModule.veq (swapAB (kleinAlg.mul x y))
      (kleinAlg.mul (swapAB x) (swapAB y)) := by
  unfold kleinModule swapAB kleinAlg kmul
  refine ⟨?_, ?_, ?_, ?_⟩
  · ring_qeqv
  · exact Q'.eqv_refl _
  · exact Q'.eqv_refl _
  · ring_qeqv

theorem interacting_expectation_swap (x : KVec) :
    kleinReferenceWeight.E_Λ (swapAB x) ≈ kleinReferenceWeight.E_Λ x := by
  exact Q'.eqv_trans _ _ _ (interacting_expectation (swapAB x))
    (Q'.eqv_symm (interacting_expectation x))

/-- Closed form of the SAME interacting Wilson Gram matrix. -/
def interactingForm (x y : KVec) : Q' :=
  x.1 * y.1 + (x.2.1 * y.2.1 +
    (x.2.2.1 * y.2.2.1 + x.2.2.2 * y.2.2.2)) +
  half * (x.1 * y.2.2.2 + (x.2.2.2 * y.1 +
    (x.2.1 * y.2.2.1 + x.2.2.1 * y.2.1)))

theorem klein_B_eq_form (x y : KVec) :
    kleinGNS.B x y ≈ interactingForm x y := by
  refine Q'.eqv_trans _ _ _ (interacting_expectation _) ?_
  change (kmul x y).1 + half * (kmul x y).2.2.2 ≈ interactingForm x y
  exact Q'.eqv_refl _

theorem interactingForm_swap (x y : KVec) :
    interactingForm (swapAB x) (swapAB y) ≈ interactingForm x y := by
  unfold interactingForm swapAB
  ring_qeqv

def kleinAmbient : AmbientTimeReflection where
  space := kleinGNS
  tau := swapAB
  tauInv := swapAB
  theta := id
  tau_map_veq := by
    intro x y h
    exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  tau_map_add := by
    intro x y
    exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩
  tau_map_neg := by
    intro x
    exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩
  tau_map_smul := by
    intro s x
    exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩
  tau_left_inv := fun x => by rw [swapAB_involutive]; exact kleinGNS.veq_refl x
  tau_right_inv := fun x => by rw [swapAB_involutive]; exact kleinGNS.veq_refl x
  tau_isometry := by
    intro x y
    exact Q'.eqv_trans _ _ _ (klein_B_eq_form (swapAB x) (swapAB y))
      (Q'.eqv_trans _ _ _ (interactingForm_swap x y)
        (Q'.eqv_symm (klein_B_eq_form x y)))
  theta_involutive := fun x => kleinGNS.veq_refl x
  theta_time_inverse := fun x => kleinGNS.veq_refl (swapAB x)

/-! ## Same-state positive-time compression -/

/-- The positive plane has orthonormal basis `(delta_e, delta_a)`. -/
abbrev positivePlane : GNSData :=
  PositiveTimeCompressedTransfer.positivePlane

def embedPlane (x : Q' × Q') : KVec := (x.1, (x.2, (0, 0)))

/-- The exact orthogonal projection for the interacting form. -/
def projectPlane (x : KVec) : Q' × Q' :=
  (x.1 + half * x.2.2.2, x.2.1 + half * x.2.2.1)

def transferPlane (x : Q' × Q') : Q' × Q' := (x.1, half * x.2)

def residualPlane (x : Q' × Q') : KVec :=
  (0, (-(half * x.2), (x.2, 0)))

def planeCoordinate (x : Q' × Q') : Nat → Q'
  | 0 => x.1
  | _ + 1 => x.2

def planeModeWeight : Nat → Q'
  | 0 => 1
  | _ + 1 => half

def kleinCompression : PositiveTimeTransfer kleinAmbient where
  positive := positivePlane
  embed := embedPlane
  project := projectPlane
  transfer := transferPlane
  residual := residualPlane
  embed_form := by
    intro x y
    refine Q'.eqv_trans _ _ _ (klein_B_eq_form _ _) ?_
    change interactingForm (embedPlane x) (embedPlane y) ≈
      (1 * (x.1 * y.1) + 1 * (x.2 * y.2))
    unfold interactingForm embedPlane
    ring_qeqv
  reflected_form := by
    intro x y
    change kleinGNS.B (embedPlane x) (embedPlane y) ≈ positivePlane.B x y
    refine Q'.eqv_trans _ _ _ (klein_B_eq_form _ _) ?_
    change interactingForm (embedPlane x) (embedPlane y) ≈
      (1 * (x.1 * y.1) + 1 * (x.2 * y.2))
    unfold interactingForm embedPlane
    ring_qeqv
  project_embed := by
    intro x
    refine ⟨?_, ?_⟩
    · change x.1 + half * 0 ≈ x.1
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left x.1 _ _ (QPoly.q_mul_zero half))
        (QPoly.q_add_zero_eqv x.1)
    · change x.2 + half * 0 ≈ x.2
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left x.2 _ _ (QPoly.q_mul_zero half))
        (QPoly.q_add_zero_eqv x.2)
  transfer_projected_time := by
    intro x
    change positivePlane.veq (transferPlane x)
      (projectPlane (swapAB (embedPlane x)))
    refine ⟨?_, ?_⟩
    · change x.1 ≈ x.1 + half * 0
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left x.1 _ _ (QPoly.q_mul_zero half))
        (QPoly.q_add_zero_eqv x.1))
    · change half * x.2 ≈ 0 + half * x.2
      exact Q'.eqv_symm (QPoly.q_zero_add_eqv (half * x.2))
  transfer_map_veq := by
    intro x y h
    exact ⟨h.1, Q'.mul_eqv_congr_left half _ _ h.2⟩
  transfer_map_zero :=
    ⟨Q'.eqv_refl _, by
      change half * (0 : Q') ≈ 0
      exact QPoly.q_mul_zero half⟩
  transfer_map_add := by
    intro x y
    refine ⟨Q'.eqv_refl _, ?_⟩
    change half * (x.2 + y.2) ≈ half * x.2 + half * y.2
    ring_qeqv
  transfer_map_neg := by
    intro x
    refine ⟨Q'.eqv_refl _, ?_⟩
    change half * (-x.2) ≈ -(half * x.2)
    exact Q'.mul_neg_eqv half x.2
  transfer_map_smul := by
    intro s x
    refine ⟨Q'.eqv_refl _, ?_⟩
    change half * (s * x.2) ≈ s * (half * x.2)
    ring_qeqv
  compressed_decomposition := by
    intro x
    change kleinModule.veq (swapAB (embedPlane x))
      (kadd (embedPlane (transferPlane x)) (residualPlane x))
    refine ⟨?_, ?_, ?_, ?_⟩
    · change x.1 ≈ x.1 + 0
      exact Q'.eqv_symm (QPoly.q_add_zero_eqv x.1)
    · change 0 ≈ half * x.2 + -(half * x.2)
      exact Q'.eqv_symm (Q'.add_neg_self_eqv (half * x.2))
    · change x.2 ≈ 0 + x.2
      exact Q'.eqv_symm (QPoly.q_zero_add_eqv x.2)
    · change (0 : Q') ≈ (0 : Q') + (0 : Q')
      exact Q'.eqv_symm (QPoly.q_zero_add_eqv (0 : Q'))
  compressed_orthogonal := by
    intro x
    refine Q'.eqv_trans _ _ _ (klein_B_eq_form _ _) ?_
    unfold interactingForm embedPlane transferPlane residualPlane
    refine Q'.eqv_trans _
      (-(half * ((half * x.2) * x.2)) +
        half * ((half * x.2) * x.2)) _ (by ring_qeqv) ?_
    exact Q'.neg_add_self_eqv (half * ((half * x.2) * x.2))
  modeCount := 2
  coordinate := planeCoordinate
  modeWeight := planeModeWeight
  modeWeight_nonneg := by
    intro i
    cases i with
    | zero => decide
    | succ _ => change (0 : Q') ≤ half; decide
  transfer_weightedGram := by
    intro x y
    change
      (1 * (x.1 * y.1) + 1 * ((half * x.2) * y.2)) ≈
        ((0 + 1 * (x.1 * y.1)) + half * (x.2 * y.2))
    ring_qeqv

/-! ## Non-rank-one coordinate and strict spectrum -/

def vacuumMode : positivePlane.V := (1, 0)
def excitedMode : positivePlane.V := (0, 1)

theorem retained_gram_vacuum :
    positivePlane.B vacuumMode vacuumMode ≈ 1 := by decide

theorem retained_gram_cross :
    positivePlane.B vacuumMode excitedMode ≈ 0 := by decide

theorem retained_gram_excited :
    positivePlane.B excitedMode excitedMode ≈ 1 := by decide

/-- The retained two-coordinate Gram determinant is exactly one, so this is
not another rank-one pure-product carrier. -/
theorem retained_gram_determinant_one :
    positivePlane.B vacuumMode vacuumMode *
        positivePlane.B excitedMode excitedMode +
      -(positivePlane.B vacuumMode excitedMode *
        positivePlane.B excitedMode vacuumMode) ≈ 1 := by decide

theorem transfer_vacuum_eigen :
    positivePlane.veq (transferPlane vacuumMode) vacuumMode := by
  exact ⟨by decide, by decide⟩

theorem transfer_excited_half_eigen :
    positivePlane.veq (transferPlane excitedMode)
      (positivePlane.smul half excitedMode) := by
  exact ⟨by decide, by decide⟩

theorem half_strict : (0 : Q') < half ∧ half < (1 : Q') := by decide

theorem excited_qmk_ne_zero :
    positivePlane.qmk excitedMode ≠ positivePlane.qmk positivePlane.zero := by
  intro h
  have hr : positivePlane.rad excitedMode positivePlane.zero := Quotient.exact h
  have hnot : ¬ positivePlane.rad excitedMode positivePlane.zero := by
    unfold GNSData.rad GNSData.sub positivePlane
      PositiveTimeCompressedTransfer.positivePlane
      PositiveTimeCompressedTransfer.gnsProduct
      PositiveTimeCompressedTransfer.unitQGNS excitedMode
    decide
  exact hnot hr

theorem excited_qmk_ne_vacuum :
    positivePlane.qmk excitedMode ≠ positivePlane.qmk vacuumMode := by
  intro h
  have hr : positivePlane.rad excitedMode vacuumMode := Quotient.exact h
  have hnot : ¬ positivePlane.rad excitedMode vacuumMode := by
    unfold GNSData.rad GNSData.sub positivePlane
      PositiveTimeCompressedTransfer.positivePlane
      PositiveTimeCompressedTransfer.gnsProduct
      PositiveTimeCompressedTransfer.unitQGNS excitedMode vacuumMode
    decide
  exact hnot hr

/-- The compressed transfer is genuinely nonidentity already on the retained
carrier, with exact positive eigenvalue `1/2`. -/
theorem transfer_nonidentity : transferPlane ≠ id := by
  intro h
  have hv := congrFun h excitedMode
  have h2 := congrArg Prod.snd hv
  exact (by decide : ¬ (half = (1 : Q'))) h2

end YMGap.Continuum.KleinCharacterWilsonCompression

#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.kleinReferenceWeight
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.kleinWeight_nonunit
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.kleinWilson
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.swapAB_mul_veq
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.kleinAmbient
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.kleinCompression
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.retained_gram_determinant_one
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.transfer_excited_half_eigen
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.excited_qmk_ne_zero
#print axioms YMGap.Continuum.KleinCharacterWilsonCompression.transfer_nonidentity
