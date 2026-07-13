/-
# Completed mixed-label transvectant recoupling

The first genuinely mixed SU(2) associator in the binary-form substrate has
external twice-spin labels `(2,2,1)`, total label `1`, source channels `0,2`,
and target channels `1,3`.  Its rational coefficient rows are supplied by the
all-order Cayley-transvectant factorial formula and the already checked nested
transvectant identities:

    [ -2/3  1/3 ]
    [  4/3  1/3 ].

Those rows alone are not a unitary matrix in the naive Euclidean metric.  This
file derives the missing metric independently, by an exact finite
Hilbert--Schmidt contraction of the binary-form maps.  In the monomial basis
`x^i y^(n-i)`, the invariant squared norm is `1 / choose(n,i)`.  The resulting
channel Gram forms are

    source: diag(96,192),       physical target: diag(72,576).

For denominator-free completion coordinates we store three times each target
coefficient.  The target chart then has form `diag(8,64)` and the transpose
coefficient map is the integer matrix `[[-2,4],[1,1]]`.  We descend this exact
isometry through `Quotient.sound` to the constructive completions.

Honest scope: this is one non-fundamental mixed-label F move.  The all-label
coefficient formula is upstream, but an all-label invariant Gram formula and
arbitrary-tree completion coherence remain separate residuals.
-/

import YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis
import YMGap.Continuum.SU2FourValentRecouplingCompleted

namespace YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted

set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis
open YMGap.Continuum.SU2SpinOneLabelWiredPentagon

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl
private theorem three_num_cast : (3 : Q').num = 3 := rfl
private theorem three_den_cast : ((3 : Q').den : Int) = 1 := rfl
private theorem four_num_cast : (4 : Q').num = 4 := rfl
private theorem four_den_cast : ((4 : Q').den : Int) = 1 := rfl
private theorem q72_num_cast : (72 : Q').num = 72 := rfl
private theorem q72_den_cast : ((72 : Q').den : Int) = 1 := rfl
private theorem q96_num_cast : (96 : Q').num = 96 := rfl
private theorem q96_den_cast : ((96 : Q').den : Int) = 1 := rfl
private theorem q192_num_cast : (192 : Q').num = 192 := rfl
private theorem q192_den_cast : ((192 : Q').den : Int) = 1 := rfl
private theorem q576_num_cast : (576 : Q').num = 576 := rfl
private theorem q576_den_cast : ((576 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               two_num_cast, two_den_cast, three_num_cast, three_den_cast,
               four_num_cast, four_den_cast, q72_num_cast, q72_den_cast,
               q96_num_cast, q96_den_cast, q192_num_cast, q192_den_cast,
               q576_num_cast, q576_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero, Int.reduceMul,
               Int.reduceAdd, Int.reduceNeg];
             ac_rfl))

/-! ## The coefficient source remains the all-order transvectant calculus -/

/-- The coefficient engine used below is the universal monomial formula, not
a table postulated specifically for the mixed block. -/
theorem mixed_coefficient_source_all_order (m n k i j s : Nat) :
    (transvect m n k (tprod (mono i) (mono j)) s).eqv
      (if s + k = i + j then transvectFactorialCoeff m n k i j else 0) :=
  transvect_monomial_factorial_formula m n k i j s

/-- The two mixed associator rows are literal identities of trilinear
transvectant maps. -/
theorem mixed221_recoupling_rows :
    TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 0)
        (fun x y z => lin2Form (-twoThirds) oneThird
          (triRight 2 2 1 1 1 x y z) (triRight 2 2 1 1 3 x y z)) ∧
    TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 2)
        (fun x y z => lin2Form fourThirds oneThird
          (triRight 2 2 1 1 1 x y z) (triRight 2 2 1 1 3 x y z)) :=
  ⟨mixed221_assoc_e0, mixed221_assoc_e2⟩

/-- Choice-free coordinate sections exist for all four trivalent channels
appearing in the mixed move. -/
def mixed221ChannelCoordinates :
    TrivalentCoordinateBasis 2 2 0 ×
      (TrivalentCoordinateBasis 2 2 2 ×
        (TrivalentCoordinateBasis 2 1 1 ×
          TrivalentCoordinateBasis 2 1 3)) :=
  (admissibleTrivalentCoordinateBasis 2 2 0 (by decide),
    admissibleTrivalentCoordinateBasis 2 2 2 (by decide),
    admissibleTrivalentCoordinateBasis 2 1 1 (by decide),
    admissibleTrivalentCoordinateBasis 2 1 3 (by decide))

/-! ## Exact invariant Hilbert--Schmidt contraction -/

/-- Invariant squared norm of `x^i y^(n-i)` in `Sym^n(Q'^2)`.
The constructor stores the positive denominator minus one. -/
def symMonomialNormSq (n i : Nat) : Q' :=
  if i ≤ n then
    Q'.mkN (tvFact i * tvFact (n - i)) (tvFact n - 1)
  else 0

/-- Exact Hilbert--Schmidt contraction of two trilinear binary-form maps.
The three `tvBinomQ` factors are the reciprocal input monomial norms; the
output factor is the invariant target monomial norm. -/
def triMapInner (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun k => finSum (fun s =>
    tvBinomQ a i * tvBinomQ b j * tvBinomQ c k *
      symMonomialNormSq d s *
        (L (mono i) (mono j) (mono k) s *
          R (mono i) (mono j) (mono k) s)) (d + 1)) (c + 1)) (b + 1)) (a + 1)

/-- The invariant monomial metric on precisely the degrees used by the mixed
block.  This is a finite rational identity, not a numerical approximation. -/
theorem mixed_monomial_norms_exact :
    symMonomialNormSq 0 0 ≈ 1 ∧
    symMonomialNormSq 1 0 ≈ 1 ∧
    symMonomialNormSq 1 1 ≈ 1 ∧
    symMonomialNormSq 2 0 ≈ 1 ∧
    symMonomialNormSq 2 1 ≈ Q'.mkPos 1 2 (by decide) ∧
    symMonomialNormSq 2 2 ≈ 1 := by
  decide

/-- Exact Gram matrices of the two bracketings.  Distinct intermediate
irreducible labels are orthogonal, and the unnormalized transvectants account
for the unequal diagonal weights. -/
theorem mixed221_transvectant_gram_exact :
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 0) (triLeft 2 2 1 1 0) ≈ 96 ∧
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 0) (triLeft 2 2 1 1 2) ≈ 0 ∧
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 2) (triLeft 2 2 1 1 0) ≈ 0 ∧
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 2) (triLeft 2 2 1 1 2) ≈ 192 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 1) (triRight 2 2 1 1 1) ≈ 72 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 1) (triRight 2 2 1 1 3) ≈ 0 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 3) (triRight 2 2 1 1 1) ≈ 0 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 3) (triRight 2 2 1 1 3) ≈ 576 := by
  decide

/-! ## The two dense GNS channel spaces -/

private def source0Line : GNSData := qWeightGNS 96 (by decide)
private def source2Line : GNSData := qWeightGNS 192 (by decide)
private def target1Line : GNSData := qWeightGNS 8 (by decide)
private def target3Line : GNSData := qWeightGNS 64 (by decide)

abbrev mixedSourceGNS : GNSData := gnsProduct source0Line source2Line
abbrev mixedTargetGNS : GNSData := gnsProduct target1Line target3Line

def channel0 : Q' × Q' := (1, 0)
def channel2 : Q' × Q' := (0, 1)
/-- The target chart stores three times the physical transvectant coefficient. -/
def channel1 : Q' × Q' := (3, 0)
def channel3 : Q' × Q' := (0, 3)

theorem mixed221_gns_gram_exact :
    mixedSourceGNS.B channel0 channel0 ≈ 96 ∧
    mixedSourceGNS.B channel0 channel2 ≈ 0 ∧
    mixedSourceGNS.B channel2 channel0 ≈ 0 ∧
    mixedSourceGNS.B channel2 channel2 ≈ 192 ∧
    mixedTargetGNS.B channel1 channel1 ≈ 72 ∧
    mixedTargetGNS.B channel1 channel3 ≈ 0 ∧
    mixedTargetGNS.B channel3 channel1 ≈ 0 ∧
    mixedTargetGNS.B channel3 channel3 ≈ 576 := by
  decide

/-- The finite transvectant contraction and the GNS forms agree on every
channel basis pairing. -/
theorem transvectant_and_gns_gram_agree :
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 0) (triLeft 2 2 1 1 0) ≈
        mixedSourceGNS.B channel0 channel0 ∧
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 0) (triLeft 2 2 1 1 2) ≈
        mixedSourceGNS.B channel0 channel2 ∧
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 2) (triLeft 2 2 1 1 0) ≈
        mixedSourceGNS.B channel2 channel0 ∧
    triMapInner 2 2 1 1 (triLeft 2 2 1 1 2) (triLeft 2 2 1 1 2) ≈
        mixedSourceGNS.B channel2 channel2 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 1) (triRight 2 2 1 1 1) ≈
        mixedTargetGNS.B channel1 channel1 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 1) (triRight 2 2 1 1 3) ≈
        mixedTargetGNS.B channel1 channel3 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 3) (triRight 2 2 1 1 1) ≈
        mixedTargetGNS.B channel3 channel1 ∧
    triMapInner 2 2 1 1 (triRight 2 2 1 1 3) (triRight 2 2 1 1 3) ≈
        mixedTargetGNS.B channel3 channel3 := by
  exact ⟨Q'.eqv_trans _ 96 _ mixed221_transvectant_gram_exact.1
      (Q'.eqv_symm mixed221_gns_gram_exact.1),
    Q'.eqv_trans _ 0 _ mixed221_transvectant_gram_exact.2.1
      (Q'.eqv_symm mixed221_gns_gram_exact.2.1),
    Q'.eqv_trans _ 0 _ mixed221_transvectant_gram_exact.2.2.1
      (Q'.eqv_symm mixed221_gns_gram_exact.2.2.1),
    Q'.eqv_trans _ 192 _ mixed221_transvectant_gram_exact.2.2.2.1
      (Q'.eqv_symm mixed221_gns_gram_exact.2.2.2.1),
    Q'.eqv_trans _ 72 _ mixed221_transvectant_gram_exact.2.2.2.2.1
      (Q'.eqv_symm mixed221_gns_gram_exact.2.2.2.2.1),
    Q'.eqv_trans _ 0 _ mixed221_transvectant_gram_exact.2.2.2.2.2.1
      (Q'.eqv_symm mixed221_gns_gram_exact.2.2.2.2.2.1),
    Q'.eqv_trans _ 0 _ mixed221_transvectant_gram_exact.2.2.2.2.2.2.1
      (Q'.eqv_symm mixed221_gns_gram_exact.2.2.2.2.2.2.1),
    Q'.eqv_trans _ 576 _ mixed221_transvectant_gram_exact.2.2.2.2.2.2.2
      (Q'.eqv_symm mixed221_gns_gram_exact.2.2.2.2.2.2.2)⟩

/-! ## Dense mixed-label F move in the denominator-free target chart -/

/-- The physical coefficient map, retained to state the normalization fence. -/
def mixedPhysicalRecoupling (x : Q' × Q') : Q' × Q' :=
  ((-twoThirds) * x.1 + fourThirds * x.2,
    oneThird * x.1 + oneThird * x.2)

/-- The target chart stores three times the physical target coefficients, so
the transpose of the transvectant row matrix is integral. -/
def mixedRecoupling (x : Q' × Q') : Q' × Q' :=
  ((-2) * x.1 + 4 * x.2, x.1 + x.2)

/-- On the two source channel vectors, division of the integral chart by
three recovers exactly the two transvectant associator rows. -/
theorem mixedRecoupling_basis_rows :
    oneThird * (mixedRecoupling channel0).1 ≈ -twoThirds ∧
    oneThird * (mixedRecoupling channel0).2 ≈ oneThird ∧
    oneThird * (mixedRecoupling channel2).1 ≈ fourThirds ∧
    oneThird * (mixedRecoupling channel2).2 ≈ oneThird := by
  decide

private def unitLine : GNSData := qWeightGNS 1 (by decide)
private abbrev unitPairGNS : GNSData := gnsProduct unitLine unitLine

/-- Normalization fence: the literal rational coefficient matrix is not an
isometry for the naive unit metric.  The derived channel Gram weights above
are essential. -/
theorem physical_block_not_unit_isometry :
    ¬ unitPairGNS.B (mixedPhysicalRecoupling channel0)
          (mixedPhysicalRecoupling channel0) ≈
        unitPairGNS.B channel0 channel0 := by
  decide

theorem mixedRecoupling_map_veq {a b : Q' × Q'}
    (h : mixedSourceGNS.veq a b) :
    mixedTargetGNS.veq (mixedRecoupling a) (mixedRecoupling b) :=
  ⟨QPoly.q_add_congr
      (Q'.mul_eqv_congr_left (-2) _ _ h.1)
      (Q'.mul_eqv_congr_left 4 _ _ h.2),
    QPoly.q_add_congr h.1 h.2⟩

theorem mixedRecoupling_map_sub (a b : Q' × Q') :
    mixedTargetGNS.veq
      (mixedRecoupling (mixedSourceGNS.sub a b))
      (mixedTargetGNS.sub (mixedRecoupling a) (mixedRecoupling b)) := by
  unfold mixedRecoupling mixedSourceGNS mixedTargetGNS gnsProduct source0Line
    source2Line target1Line target3Line qWeightGNS GNSData.sub
  constructor <;> ring_qeqv

private def mixedNormPolyLeft : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.add
    (.mul (.const (-2)) x) (.mul (.const 4) y)
  let q := RingNormaliser.PolyExpr.add x y
  .add (.mul (.const 8) (.mul p p))
    (.mul (.const 64) (.mul q q))

private def mixedNormPolyRight : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  .add (.mul (.const 96) (.mul x x))
    (.mul (.const 192) (.mul y y))

private theorem mixedNormPoly_normal :
    RingNormaliser.normalize mixedNormPolyLeft =
      RingNormaliser.normalize mixedNormPolyRight := by
  decide

private theorem mixed_norm_identity (x y : Q') :
    8 * (((-2) * x + 4 * y) * ((-2) * x + 4 * y)) +
        64 * ((x + y) * (x + y)) ≈
      96 * (x * x) + 192 * (y * y) := by
  have hp := RingNormaliser.poly_identity_of_normal_eq
    mixedNormPolyLeft mixedNormPolyRight mixedNormPoly_normal
    (fun | 0 => x | _ => y)
  simpa [mixedNormPolyLeft, mixedNormPolyRight, RingNormaliser.eval] using hp

/-- Correctly weighted dense norm preservation. -/
theorem mixedRecoupling_norm (a : Q' × Q') :
    mixedTargetGNS.B (mixedRecoupling a) (mixedRecoupling a) ≈
      mixedSourceGNS.B a a := by
  unfold mixedRecoupling mixedSourceGNS mixedTargetGNS gnsProduct source0Line
    source2Line target1Line target3Line qWeightGNS
  exact mixed_norm_identity a.1 a.2

theorem mixedRecoupling_distSq_eqv (a b : Q' × Q') :
    mixedTargetGNS.distSqQ (mixedRecoupling a) (mixedRecoupling b) ≈
      mixedSourceGNS.distSqQ a b := by
  have hsub := mixedRecoupling_map_sub a b
  refine Q'.eqv_trans _
    (mixedTargetGNS.B
      (mixedRecoupling (mixedSourceGNS.sub a b))
      (mixedRecoupling (mixedSourceGNS.sub a b))) _ ?_ ?_
  · exact Q'.eqv_symm (mixedTargetGNS.B_diag_congr hsub)
  · exact mixedRecoupling_norm (mixedSourceGNS.sub a b)

/-! ## Descent to the constructive completions -/

def applyMixedRecouplingCauchy
    (x : CauchyGNS mixedSourceGNS) : CauchyGNS mixedTargetGNS where
  seq := fun n => mixedRecoupling (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (mixedRecoupling_distSq_eqv (x.seq p) (x.seq q)))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyMixedRecouplingCauchy_null
    {x y : CauchyGNS mixedSourceGNS} (h : CauchyNull mixedSourceGNS x y) :
    CauchyNull mixedTargetGNS
      (applyMixedRecouplingCauchy x) (applyMixedRecouplingCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (Q'.le_of_eqv (mixedRecoupling_distSq_eqv (x.seq n) (y.seq n))) (hN n hn)⟩

def completedMixedRecoupling :
    GNSCompletionSpace mixedSourceGNS → GNSCompletionSpace mixedTargetGNS :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid mixedTargetGNS)
      (applyMixedRecouplingCauchy x))
    (fun _ _ h => Quotient.sound (applyMixedRecouplingCauchy_null h))

theorem completedMixedRecoupling_embed (a : Q' × Q') :
    completedMixedRecoupling (embedV mixedSourceGNS a) =
      embedV mixedTargetGNS (mixedRecoupling a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem completedMixedRecoupling_norm
    (x : GNSCompletionSpace mixedSourceGNS) :
    mixedTargetGNS.cinnerCompl
        (completedMixedRecoupling x) (completedMixedRecoupling x) =
      mixedSourceGNS.cinnerCompl x x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (mixedTargetGNS.cInnerSeq
        (applyMixedRecouplingCauchy u) (applyMixedRecouplingCauchy u) n))
    (bSeq := fun n => CReal.ofQ' (mixedSourceGNS.cInnerSeq u u n))
    (fun n => PositiveTimeCompression.lifted_eqv
      (mixedRecoupling_norm (u.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

end YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted

#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.mixed_coefficient_source_all_order
#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.mixed221_recoupling_rows
#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.mixed221_transvectant_gram_exact
#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.transvectant_and_gns_gram_agree
#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.physical_block_not_unit_isometry
#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.mixedRecoupling_norm
#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.completedMixedRecoupling
#print axioms YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted.completedMixedRecoupling_norm
