/-
# Constructive refresh contraction for finite positive kernels

BF4 can be stated without logarithms, projective suprema, an eigenvector
selection, or a spectral theorem.  Suppose a finite Markov kernel has an
explicit input-independent positive summand

    K(x,y) = epsilon * reference(y)
             + (1 - epsilon) * residual(x,y),

where the residual kernel is again row-normalized and
`0 < epsilon <= 1`.  For two source weights of equal total mass, the
reference terms cancel exactly.  Positivity and row normalization of the
residual then give

    ||pK - qK||_1 <= (1 - epsilon) ||p - q||_1.

This module proves that statement using only finite exact-rational algebra.
The proof is intuitionistic in the repository's strong sense: every
constant is data, all sums are finite, and there is no `Classical.*`,
choice, excluded middle on arbitrary propositions, compactness argument,
logarithm, square root, `sorry`, or custom axiom.

The theorem is an algebraic BF4 bridge, not an inhabitant of the physical
BF4 gate.  The open Yang--Mills content is to construct the refresh summand
from the exact grouped all-label Haar/fusion block with a coefficient whose
product over fixed physical distance stays strictly below one.
-/

import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.ConstructiveRefreshContraction

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## Finite masses, pushforwards, and the `l¹` distance -/

/-- Exact total of a finite weight. -/
def finiteMass {State : Type}
    (states : List State) (weight : State → Q') : Q' :=
  listQSum weight states

/-- Exact finite matrix pushforward. -/
def finiteKernelPushforward {Source Target : Type}
    (sources : List Source) (weight : Source → Q')
    (kernel : Source → Target → Q') (target : Target) : Q' :=
  listQSum (fun source => weight source * kernel source target) sources

/-- Exact `l¹` distance between two finite weights. -/
def finiteL1Distance {State : Type}
    (states : List State) (left right : State → Q') : Q' :=
  listQSum (fun state => Q'.abs (left state + (-right state))) states

theorem finiteL1Distance_nonnegative {State : Type}
    (states : List State) (left right : State → Q') :
    (0 : Q') ≤ finiteL1Distance states left right := by
  unfold finiteL1Distance
  exact listQSum_nonnegative_on _ states
    (fun state _ => Q'.abs_nonneg (left state + (-right state)))

theorem finiteKernelPushforward_total
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (weight : Source → Q') (kernel : Source → Target → Q')
    (rowNormalized :
      ∀ source, source ∈ sources →
        listQSum (kernel source) targets ≈ 1) :
    finiteMass targets
        (finiteKernelPushforward sources weight kernel) ≈
      finiteMass sources weight := by
  unfold finiteMass finiteKernelPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target => weight source * kernel source target)
          targets)
      sources) _ ?_ ?_
  · exact listQSum_swap
      (fun source target => weight source * kernel source target)
      sources targets
  apply listQSum_congr_on
  intro source hsource
  refine Q'.eqv_trans _
    (weight source * listQSum (kernel source) targets) _ ?_ ?_
  · exact listQSum_mul_left
      (weight source) (kernel source) targets
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (weight source) _ _
      (rowNormalized source hsource))
    (Q'.mul_one_eqv (weight source))

/-! ## A residual Markov kernel is `l¹`-nonexpansive -/

private theorem abs_right_weighted_sub_le
    (left right weight : Q') (hweight : (0 : Q') ≤ weight) :
    Q'.abs (left * weight + (-(right * weight))) ≤
      weight * Q'.abs (left + (-right)) := by
  have hreorder :
      left * weight + (-(right * weight)) ≈
        weight * left + (-(weight * right)) := by
    exact Q'.add_eqv_congr'
      (Q'.mul_comm_eqv left weight)
      (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv right weight))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (abs_eqv_congr hreorder)) ?_
  have hbound := abs_common_mul_sub_le
    weight left right (Q'.abs (left + (-right)))
    (Q'.le_refl' _)
  rw [abs_of_nonneg hweight] at hbound
  exact hbound

private theorem cancel_common_factor
    (common rate left right : Q') :
    (common + rate * left) + (-(common + rate * right)) ≈
      rate * (left + (-right)) := by
  have hneg :
      -(common + rate * right) ≈
        -common + -(rate * right) :=
    Q'.neg_add_eqv common (rate * right)
  refine Q'.eqv_trans _
    ((common + rate * left) +
      (-common + -(rate * right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left
      (common + rate * left) _ _ hneg
  refine Q'.eqv_trans _
    ((common + -common) +
      (rate * left + -(rate * right))) _ ?_ ?_
  · exact Q'.add_swap_inner
      common (rate * left) (-common) (-(rate * right))
  refine Q'.eqv_trans _
    (0 + (rate * left + -(rate * right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _
      (rate * left + -(rate * right))
      (Q'.add_neg_self_eqv common)
  refine Q'.eqv_trans _
    (rate * left + -(rate * right)) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (Q'.zero_add' (rate * left + -(rate * right)))
  refine Q'.eqv_trans _
    (rate * left + rate * (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (rate * left) _ _
      (Q'.eqv_symm (Q'.mul_neg_eqv rate right))
  · exact Q'.eqv_symm (Q'.mul_add_eqv rate left (-right))

/-- Every finite nonnegative row-stochastic kernel is nonexpansive in
`l¹`.  Source weights may be signed; no Jordan decomposition is used. -/
theorem finiteMarkov_l1_nonexpansive
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (kernel : Source → Target → Q')
    (nonnegative :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          (0 : Q') ≤ kernel source target)
    (rowNormalized :
      ∀ source, source ∈ sources →
        listQSum (kernel source) targets ≈ 1)
    (left right : Source → Q') :
    finiteL1Distance targets
        (finiteKernelPushforward sources left kernel)
        (finiteKernelPushforward sources right kernel) ≤
      finiteL1Distance sources left right := by
  let sourceError : Source → Q' := fun source =>
    Q'.abs (left source + (-right source))
  let targetError : Target → Q' := fun target =>
    Q'.abs
      (finiteKernelPushforward sources left kernel target +
        (-finiteKernelPushforward sources right kernel target))
  have hrow :
      ∀ target, target ∈ targets →
        targetError target ≤
          listQSum
            (fun source => kernel source target * sourceError source)
            sources := by
    intro target htarget
    unfold targetError finiteKernelPushforward
    refine Q'.le_trans' _ _ _
      (abs_listQSum_sub_le
        (fun source => left source * kernel source target)
        (fun source => right source * kernel source target)
        sources) ?_
    apply listQSum_mono
    intro source hsource
    exact abs_right_weighted_sub_le
      (left source) (right source) (kernel source target)
      (nonnegative source hsource target htarget)
  have hsumRows :
      listQSum targetError targets ≤
        listQSum
          (fun target =>
            listQSum
              (fun source => kernel source target * sourceError source)
              sources)
          targets :=
    listQSum_mono targetError _ targets hrow
  have hswap :
      listQSum
          (fun target =>
            listQSum
              (fun source => kernel source target * sourceError source)
              sources)
          targets ≈
        listQSum
          (fun source =>
            listQSum
              (fun target => kernel source target * sourceError source)
              targets)
          sources :=
    listQSum_swap
      (fun source target => kernel source target * sourceError source)
      sources targets
  have hcollapse :
      listQSum
          (fun source =>
            listQSum
              (fun target => kernel source target * sourceError source)
              targets)
          sources ≈
        listQSum sourceError sources := by
    apply listQSum_congr_on
    intro source hsource
    refine Q'.eqv_trans _
      (listQSum (kernel source) targets * sourceError source) _
      (listQSum_mul_right
        (kernel source) (sourceError source) targets) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (sourceError source)
        (rowNormalized source hsource))
      (Q'.one_mul_eqv (sourceError source))
  unfold finiteL1Distance
  change listQSum targetError targets ≤ listQSum sourceError sources
  exact Q'.le_trans' _ _ _ hsumRows
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hswap hcollapse))

/-! ## Explicit refresh decompositions -/

/-- Witness-bearing finite Doeblin/refresh decomposition.

The `reference` is deliberately required to be an explicit normalized
weight even though its positivity is not needed for the cancellation
lemma.  These fields are the data a physical Haar/fusion construction must
actually emit. -/
structure FiniteRefreshCertificate
    {Source Target : Type}
    (sources : List Source) (targets : List Target) : Type where
  epsilon : Q'
  epsilon_positive : (0 : Q') < epsilon
  epsilon_le_one : epsilon ≤ (1 : Q')
  reference : Target → Q'
  reference_nonnegative :
    ∀ target, target ∈ targets → (0 : Q') ≤ reference target
  reference_normalized :
    listQSum reference targets ≈ 1
  residual : Source → Target → Q'
  residual_nonnegative :
    ∀ source, source ∈ sources →
      ∀ target, target ∈ targets →
        (0 : Q') ≤ residual source target
  residual_row_normalized :
    ∀ source, source ∈ sources →
      listQSum (residual source) targets ≈ 1

namespace FiniteRefreshCertificate

/-- The residual coefficient `1 - epsilon`. -/
def rate
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets) : Q' :=
  (1 : Q') + -certificate.epsilon

theorem rate_nonnegative
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets) :
    (0 : Q') ≤ certificate.rate :=
  Q'.sub_nonneg_of_le certificate.epsilon_le_one

private theorem one_sub_lt_one {epsilon : Q'}
    (hpositive : (0 : Q') < epsilon) :
    (1 : Q') + -epsilon < (1 : Q') := by
  show ((1 : Q') + -epsilon).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -epsilon).den : Int)
  have hnum : (0 : Int) < epsilon.num := Q'.num_pos_of_pos hpositive
  change
    (((1 : Int) * (epsilon.den : Int) + (-epsilon.num) * (1 : Int)) *
      (1 : Int)) <
      ((1 : Int) *
        (((1 : Nat) * epsilon.den : Nat) : Int))
  push_cast
  omega

theorem rate_lt_one
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets) :
    certificate.rate < (1 : Q') :=
  one_sub_lt_one certificate.epsilon_positive

/-- The kernel reconstructed from the refresh packet and its residual. -/
def kernel
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets)
    (source : Source) (target : Target) : Q' :=
  certificate.epsilon * certificate.reference target +
    certificate.rate * certificate.residual source target

theorem kernel_nonnegative
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets)
    (source : Source) (hsource : source ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    (0 : Q') ≤ certificate.kernel source target := by
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt certificate.epsilon_positive)
      (certificate.reference_nonnegative target htarget))
    (Q'.mul_nonneg _ _
      certificate.rate_nonnegative
      (certificate.residual_nonnegative source hsource target htarget))

theorem rate_add_epsilon_eqv_one
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets) :
    certificate.epsilon + certificate.rate ≈ 1 := by
  unfold rate
  refine Q'.eqv_trans _
    ((certificate.epsilon + 1) + -certificate.epsilon) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_assoc_eqv
        certificate.epsilon 1 (-certificate.epsilon))
  refine Q'.eqv_trans _
    ((1 + certificate.epsilon) + -certificate.epsilon) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-certificate.epsilon)
      (Q'.add_comm_eqv certificate.epsilon 1)
  refine Q'.eqv_trans _
    (1 + (certificate.epsilon + -certificate.epsilon)) _ ?_ ?_
  · exact Q'.add_assoc_eqv 1 certificate.epsilon (-certificate.epsilon)
  refine Q'.eqv_trans _ (1 + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left 1 _ _
      (Q'.add_neg_self_eqv certificate.epsilon)
  · exact Q'.eqv_of_eq (Q'.add_zero' 1)

theorem kernel_row_normalized
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets)
    (source : Source) (hsource : source ∈ sources) :
    listQSum (certificate.kernel source) targets ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        certificate.epsilon * certificate.reference target)
      targets +
      listQSum
        (fun target =>
          certificate.rate * certificate.residual source target)
        targets) _ ?_ ?_
  · exact listQSum_add _ _ targets
  refine Q'.eqv_trans _
    (certificate.epsilon * listQSum certificate.reference targets +
      certificate.rate *
        listQSum (certificate.residual source) targets) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (listQSum_mul_left
        certificate.epsilon certificate.reference targets)
      (listQSum_mul_left
        certificate.rate (certificate.residual source) targets)
  refine Q'.eqv_trans _
    (certificate.epsilon * 1 + certificate.rate * 1) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left certificate.epsilon _ _
        certificate.reference_normalized)
      (Q'.mul_eqv_congr_left certificate.rate _ _
        (certificate.residual_row_normalized source hsource))
  refine Q'.eqv_trans _
    (certificate.epsilon + certificate.rate) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_one_eqv certificate.epsilon)
      (Q'.mul_one_eqv certificate.rate)
  · exact certificate.rate_add_epsilon_eqv_one

private theorem pushforward_split
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets)
    (weight : Source → Q') (target : Target) :
    finiteKernelPushforward sources weight certificate.kernel target ≈
      (certificate.epsilon * certificate.reference target) *
          finiteMass sources weight +
        certificate.rate *
          finiteKernelPushforward
            sources weight certificate.residual target := by
  unfold finiteKernelPushforward kernel finiteMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (certificate.epsilon * certificate.reference target) *
            weight source +
          certificate.rate *
            (weight source * certificate.residual source target))
      sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    ac_qeqv
  refine Q'.eqv_trans _
    (listQSum
        (fun source =>
          (certificate.epsilon * certificate.reference target) *
            weight source)
        sources +
      listQSum
        (fun source =>
          certificate.rate *
            (weight source * certificate.residual source target))
        sources) _ ?_ ?_
  · exact listQSum_add _ _ sources
  exact Q'.add_eqv_congr'
    (listQSum_mul_left
      (certificate.epsilon * certificate.reference target)
      weight sources)
    (listQSum_mul_left certificate.rate
      (fun source => weight source * certificate.residual source target)
      sources)

private theorem pushforward_difference_cancels_reference
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets)
    (left right : Source → Q')
    (equalMass :
      finiteMass sources left ≈ finiteMass sources right)
    (target : Target) :
    finiteKernelPushforward sources left certificate.kernel target +
        (-finiteKernelPushforward sources right certificate.kernel target) ≈
      certificate.rate *
        (finiteKernelPushforward
            sources left certificate.residual target +
          (-finiteKernelPushforward
            sources right certificate.residual target)) := by
  let common := certificate.epsilon * certificate.reference target
  let leftResidual :=
    finiteKernelPushforward sources left certificate.residual target
  let rightResidual :=
    finiteKernelPushforward sources right certificate.residual target
  have hleft := certificate.pushforward_split left target
  have hright := certificate.pushforward_split right target
  have hcommon :
      common * finiteMass sources left ≈
        common * finiteMass sources right :=
    Q'.mul_eqv_congr_left common _ _ equalMass
  refine Q'.eqv_trans _
    ((common * finiteMass sources left +
        certificate.rate * leftResidual) +
      -(common * finiteMass sources right +
        certificate.rate * rightResidual)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      hleft (Q'.neg_eqv_congr _ _ hright)
  refine Q'.eqv_trans _
    ((common * finiteMass sources right +
        certificate.rate * leftResidual) +
      -(common * finiteMass sources right +
        certificate.rate * rightResidual)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hcommon (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  · exact cancel_common_factor
      (common * finiteMass sources right)
      certificate.rate leftResidual rightResidual

/-- Constructive BF4 algebra: an explicit refresh packet contracts all
equal-mass source weights by the exact rational rate `1 - epsilon`. -/
theorem l1_contraction
    {Source Target : Type}
    {sources : List Source} {targets : List Target}
    (certificate : FiniteRefreshCertificate sources targets)
    (left right : Source → Q')
    (equalMass :
      finiteMass sources left ≈ finiteMass sources right) :
    finiteL1Distance targets
        (finiteKernelPushforward sources left certificate.kernel)
        (finiteKernelPushforward sources right certificate.kernel) ≤
      certificate.rate * finiteL1Distance sources left right := by
  let residualLeft :=
    finiteKernelPushforward sources left certificate.residual
  let residualRight :=
    finiteKernelPushforward sources right certificate.residual
  have hpoint :
      ∀ target, target ∈ targets →
        Q'.abs
          (finiteKernelPushforward sources left certificate.kernel target +
            (-finiteKernelPushforward
              sources right certificate.kernel target)) ≤
          certificate.rate *
            Q'.abs (residualLeft target + (-residualRight target)) := by
    intro target _
    have hcancel :=
      certificate.pushforward_difference_cancels_reference
        left right equalMass target
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (abs_eqv_congr hcancel)) ?_
    have hmul := abs_mul_le certificate.rate
      (residualLeft target + (-residualRight target))
    rw [abs_of_nonneg certificate.rate_nonnegative] at hmul
    exact hmul
  have hsum :
      finiteL1Distance targets
          (finiteKernelPushforward sources left certificate.kernel)
          (finiteKernelPushforward sources right certificate.kernel) ≤
        listQSum
          (fun target =>
            certificate.rate *
              Q'.abs (residualLeft target + (-residualRight target)))
          targets := by
    unfold finiteL1Distance
    exact listQSum_mono _ _ targets hpoint
  have hfactor :
      listQSum
          (fun target =>
            certificate.rate *
              Q'.abs (residualLeft target + (-residualRight target)))
          targets ≈
        certificate.rate *
          finiteL1Distance targets residualLeft residualRight := by
    exact listQSum_mul_left certificate.rate
      (fun target =>
        Q'.abs (residualLeft target + (-residualRight target)))
      targets
  have hresidual :
      finiteL1Distance targets residualLeft residualRight ≤
        finiteL1Distance sources left right :=
    finiteMarkov_l1_nonexpansive
      sources targets certificate.residual
      certificate.residual_nonnegative
      certificate.residual_row_normalized left right
  refine Q'.le_trans' _ _ _ hsum ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hresidual
    certificate.rate_nonnegative

end FiniteRefreshCertificate

#print axioms finiteMarkov_l1_nonexpansive
#print axioms finiteKernelPushforward_total
#print axioms FiniteRefreshCertificate.rate_lt_one
#print axioms FiniteRefreshCertificate.kernel_nonnegative
#print axioms FiniteRefreshCertificate.kernel_row_normalized
#print axioms FiniteRefreshCertificate.l1_contraction

end YMGap.Continuum.ConstructiveRefreshContraction
