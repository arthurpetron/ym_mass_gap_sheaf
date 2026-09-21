/-
# Linear multi-step increments in the SAME original Wilson joint state

Reflection-positive moment convexity and stationarity imply
`E[(X₀-Xₙ)²] ≤ n E[(X₀-X₁)²]`. The existing adjacent-increment estimate
then gives `24*n*L²*(1-w)` for a fixed fundamental loop of length L at every
strictly padded width and every `0<w<1`. No small-nome guard is used.

These are lattice-time steps, not physical time. The estimates do not
construct a spatial/scaling limit, a nonzero limiting variance, a physical
Hamiltonian or a mass gap.
-/
import YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4WilsonAllNomeTimeIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_square_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeLoop_edges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (includedLoop_edges_active)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
open YMGap.Continuum.BF4WilsonAllNomeKineticIncrement

attribute [local irreducible] originalJointLimit originalWindowScalar baseLinks

def timeDifference {width : Nat} (loop : SourceLoop width) (n : Nat) : WindowExpression width :=
  difference (.loop 0 loop 1) (.loop n loop 1)

def timeSquare {width : Nat} (loop : SourceLoop width) (n : Nat) : WindowExpression width :=
  .mul (timeDifference loop n) (timeDifference loop n)

theorem timeSquare_within {width : Nat} (loop : SourceLoop width) (n : Nat) :
    Within n (timeSquare loop n) :=
  ⟨⟨Nat.zero_le _, Nat.le_refl _⟩, ⟨Nat.zero_le _, Nat.le_refl _⟩⟩

def timeIncrement {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n (timeSquare loop n) (timeSquare_within loop n)

theorem timeIncrement_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) :
    timeIncrement hw0 hw1 loop 1 = incrementLimit hw0 hw1 loop := rfl

private theorem qring (a b : PolyExpr) (h : normalize a = normalize b) (env : Nat → Q') :
    (eval env a).eqv (eval env b) := poly_identity_of_normal_eq a b h env

/-- Exact polarization in the original state, including n=0. -/
theorem timeIncrement_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    Equiv (timeIncrement hw0 hw1 loop n)
      (CReal.mul (ofQ' 2) (CReal.sub (lagMoment hw0 hw1 loop 0) (lagMoment hw0 hw1 loop n))) := by
  have he := joint_difference_product hw0 hw1 n
    (.loop 0 loop 1) (.loop n loop 1) (.loop 0 loop 1) (.loop n loop 1)
    (Nat.zero_le _) (Nat.le_refl _) (Nat.zero_le _) (Nat.le_refl _)
  have hc := joint_congr hw0 hw1 n
    (.mul (.loop 0 loop 1) (.loop n loop 1)) (.mul (.loop n loop 1) (.loop 0 loop 1))
    ⟨Nat.zero_le _, Nat.le_refl _⟩ ⟨Nat.le_refl _, Nat.zero_le _⟩
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0))
      (by decide) (fun | 0 => sourcePolynomial (.loop 0 loop 1) | _ => sourcePolynomial (.loop n loop 1)))
  have h00 := pair_lag hw0 hw1 loop n 0 0 (Nat.le_refl _) (Nat.zero_le _)
  have hnn := pair_lag hw0 hw1 loop n n n (Nat.le_refl _) (Nat.le_refl _)
  have hn0 := pair_lag hw0 hw1 loop n 0 n (Nat.zero_le _) (Nat.le_refl _)
  have hp := equiv_add (equiv_sub h00 (Equiv.trans hc hn0)) (equiv_sub hnn hn0)
  simp only [Nat.sub_self, Nat.sub_zero] at hp
  exact Equiv.trans he (Equiv.trans hp (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    qring (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => (lagMoment hw0 hw1 loop 0).approx k | _ => (lagMoment hw0 hw1 loop n).approx k))))

theorem timeIncrement_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    leEv (ofQ' 0) (timeIncrement hw0 hw1 loop n) := by
  apply leEv_of_ofQ'_limit_le (convergesTo_const _)
    (originalJoint_diagonal_converges hw0 hw1 n _ (timeSquare_within loop n))
  intro epsilon he
  refine ⟨0, fun stage _ => ?_⟩
  have h := windowRatio_square_nonnegative hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) stage n stage
    (source_supported n (timeDifference loop n) ⟨Nat.zero_le _, Nat.le_refl _⟩)
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (originalWindowScalar_pin hw0 hw1 n _ (timeSquare_within loop n) stage stage stage))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)))

/-- Linear in elapsed lattice steps, not the quadratic triangle bound. -/
theorem timeIncrement_linear {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    leEv (timeIncrement hw0 hw1 loop n)
      (CReal.mul (ofQ' (Q'.ofNat n)) (incrementLimit hw0 hw1 loop)) := by
  have h := leEv_smul_nonneg (by decide : (0 : Q') ≤ 2)
    (lagMoment_endpoint_bound hw0 hw1 loop n)
  have hr : Equiv
      (CReal.mul (ofQ' 2) (CReal.mul (ofQ' (Q'.ofNat n))
        (CReal.sub (lagMoment hw0 hw1 loop 0) (lagMoment hw0 hw1 loop 1))))
      (CReal.mul (ofQ' (Q'.ofNat n)) (CReal.mul (ofQ' 2)
        (CReal.sub (lagMoment hw0 hw1 loop 0) (lagMoment hw0 hw1 loop 1)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun k =>
      qring (.mul (.const 2) (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.mul (.const 2) (.var 1))) (by decide)
        (fun | 0 => Q'.ofNat n
             | _ => (CReal.sub (lagMoment hw0 hw1 loop 0) (lagMoment hw0 hw1 loop 1)).approx k))
  exact leEv_trans (leEv_of_equiv (timeIncrement_pin hw0 hw1 loop n))
    (leEv_trans h (leEv_trans (leEv_of_equiv hr)
      (leEv_smul_nonneg (Q'.ofNat_nonneg n) (leEv_of_equiv (timeIncrement_pin hw0 hw1 loop 1).symm))))

theorem timeIncrement_nome_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) (n : Nat) :
    leEv (timeIncrement hw0 hw1 loop n)
      (ofQ' (Q'.ofNat n * (24 * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) * (1 + -w)))) :=
  leEv_trans (timeIncrement_linear hw0 hw1 loop n)
    (leEv_trans (leEv_smul_nonneg (Q'.ofNat_nonneg n) (joint_increment_nome_bound hw0 hw1 loop hactive))
      (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))))

/-- Uniform in strictly padded width for a fixed literal loop and elapsed
step count. Each width/nome still has its own original joint state. -/
theorem padded_timeIncrement_nome_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (loop : SourceLoop base) (n : Nat) :
    leEv (timeIncrement hw0 hw1
      (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop) n)
      (ofQ' (Q'.ofNat n * (24 * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) * (1 + -w)))) := by
  have h := timeIncrement_nome_bound hw0 hw1
    (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop)
    (includedLoop_edges_active hwidth loop) n
  rw [includeLoop_edges (Nat.le_of_lt hwidth) loop] at h
  exact h

end YMGap.Continuum.BF4WilsonAllNomeTimeIncrement

#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeDifference
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeSquare
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeSquare_within
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeIncrement
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeIncrement_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeIncrement_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeIncrement_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeIncrement_linear
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.timeIncrement_nome_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeIncrement.padded_timeIncrement_nome_bound
