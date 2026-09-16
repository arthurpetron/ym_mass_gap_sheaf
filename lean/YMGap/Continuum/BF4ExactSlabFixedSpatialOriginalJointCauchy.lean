/-
# Joint heat-cutoff and boundary-time convergence of the ORIGINAL scalar

The actual time-Cauchy modulus is independent of late heat cutoff. At one
fixed intermediate time the original finiteCauchy supplies cutoff control.
Three comparisons through that SAME intermediate chain yield a rectangular
two-parameter Cauchy bound. No cutoff estimate uniform in time is assumed.

An explicit diagonal then constructs the common CReal limit. The original
selected action, probe recoding, partition and terminal spatial weight are
unchanged. Nome and spatial width remain fixed; no stationary/bulk state,
reflected OS theory, width/spacing-uniform estimate or physical gap follows.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit (endpointInsertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteCauchy)

local infix:50 " ≃ " => Q'.eqv

/-- The pre-existing cutoff modulus of the SAME fixed-time original action.
The face-membership guard enters time comparison, not this cutoff datum. -/
def originalCutoffCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (steps : Nat) :
    QCauchy (fun stage => originalTimeScalar hw0 hw1 width fs stage steps) :=
  finiteCauchy w hw0 hw1 (width+steps) (chainIds (width+steps) width 0 steps)
    (fun _ hi => chainIds_physical hi) (endpointInsertion (width+steps) 0 steps fs [])

-- Subsequent arguments use the proved scalar laws, not expanding Haar sums.
attribute [local irreducible] originalTimeScalar

/-- One common comparison time, computed at one quarter of the error budget. -/
def jointTimeThreshold {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (epsilon : Q') : Nat :=
  boundaryTimeModulus hw0 hw1 width fs (HalfPow.half * (HalfPow.half * epsilon))

/-- Cutoff control is requested at the displayed fixed intermediate time,
not uniformly over an unbounded family of time lengths. -/
def jointCutoffThreshold {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (epsilon : Q') : Nat :=
  (originalCutoffCauchy hw0 hw1 width fs (jointTimeThreshold hw0 hw1 width fs epsilon)).M
    (HalfPow.half * (HalfPow.half * epsilon))

/-- Executable threshold for the diagonal, retaining both parameter budgets. -/
def jointModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (epsilon : Q') : Nat :=
  max (jointTimeThreshold hw0 hw1 width fs epsilon)
    (jointCutoffThreshold hw0 hw1 width fs epsilon)

-- Treat the proved numerical moduli as data, not as expanded action formulas.
attribute [local irreducible] boundaryTimeModulus originalCutoffCauchy

private theorem three_quarter_chain (epsilon : Q') (he : (0 : Q') < epsilon)
    (u v x z : Q')
    (hu : u ≤ v + HalfPow.half * (HalfPow.half * epsilon))
    (hv : v ≤ x + HalfPow.half * (HalfPow.half * epsilon))
    (hx : x ≤ z + HalfPow.half * (HalfPow.half * epsilon)) : u ≤ z + epsilon := by
  let q := HalfPow.half * (HalfPow.half * epsilon)
  have hq : (0 : Q') ≤ q := Q'.le_of_lt
    (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he))
  have h1 := Q'.le_trans' _ _ _ hu (Q'.add_le_add_right _ _ q hv)
  have h2 := Q'.le_trans' _ _ _ h1
    (Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hx))
  have h3 := Q'.le_trans' _ _ _ h2 (Q'.add_le_self_of_nonneg _ q hq)
  have hfour : (((z+q)+q)+q)+q ≃ z+epsilon := by
    have hqq : q+q ≃ HalfPow.half*epsilon := ExpNeg.two_halves (HalfPow.half*epsilon)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((z+q)+q) q q) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (q+q) (Q'.add_assoc_eqv z q q)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z (q+q) (q+q)) ?_
    exact Q'.add_eqv_congr_left z _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hqq hqq) (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv hfour)

/-- A genuine rectangular bound in two independent indices. The proof passes
through one original chain at the computed intermediate time. -/
theorem originalJoint_rectangle {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k n j m : Nat)
    (hk : jointCutoffThreshold hw0 hw1 width fs epsilon ≤ k)
    (hn : jointTimeThreshold hw0 hw1 width fs epsilon ≤ n)
    (hj : jointCutoffThreshold hw0 hw1 width fs epsilon ≤ j)
    (hm : jointTimeThreshold hw0 hw1 width fs epsilon ≤ m) :
    originalTimeScalar hw0 hw1 width fs k n ≤ originalTimeScalar hw0 hw1 width fs j m + epsilon ∧
      originalTimeScalar hw0 hw1 width fs j m ≤ originalTimeScalar hw0 hw1 width fs k n + epsilon := by
  let delta := HalfPow.half * (HalfPow.half * epsilon)
  have hd : (0 : Q') < delta := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)
  let a := jointTimeThreshold hw0 hw1 width fs epsilon
  have hleft := (originalTimeCauchy hw0 hw1 width fs hfs k).bound
    delta hd n a hn (Nat.le_refl _)
  have hmiddle := (originalCutoffCauchy hw0 hw1 width fs a).bound delta hd k j hk hj
  have hright := (originalTimeCauchy hw0 hw1 width fs hfs j).bound
    delta hd a m (Nat.le_refl _) hm
  exact ⟨three_quarter_chain epsilon he _ _ _ _ hleft.1 hmiddle.1 hright.1,
    three_quarter_chain epsilon he _ _ _ _ hright.2 hmiddle.2 hleft.2⟩

/-- Constructive Cauchy data for the literal original diagonal, no choice
of subsequence or additional analytic input. -/
def originalJointCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    QCauchy (fun s => originalTimeScalar hw0 hw1 width fs s s) where
  M := jointModulus hw0 hw1 width fs
  bound := fun epsilon he i j hi hj =>
    originalJoint_rectangle hw0 hw1 width fs hfs epsilon he i i j j
      (Nat.le_trans (Nat.le_max_right _ _) hi) (Nat.le_trans (Nat.le_max_left _ _) hi)
      (Nat.le_trans (Nat.le_max_right _ _) hj) (Nat.le_trans (Nat.le_max_left _ _) hj)

/-- The common fixed-width original boundary scalar after both indices recede. -/
def originalJointLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) : CReal :=
  ofQ'CauchySeq _ (originalJointCauchy hw0 hw1 width fs hfs)

theorem originalJoint_diagonal_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    ConvergesTo (fun s => ofQ' (originalTimeScalar hw0 hw1 width fs s s))
      (originalJointLimit hw0 hw1 width fs hfs) :=
  convergesTo_ofQ'CauchySeq _ (originalJointCauchy hw0 hw1 width fs hfs)

/-- The joint limit controls the whole late rectangle, not only its diagonal.
All raw and representative thresholds are explicit functions above. -/
theorem originalJoint_approx {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k n p : Nat)
    (hk : jointCutoffThreshold hw0 hw1 width fs epsilon ≤ k)
    (hn : jointTimeThreshold hw0 hw1 width fs epsilon ≤ n)
    (hp : jointModulus hw0 hw1 width fs epsilon ≤ p) :
    originalTimeScalar hw0 hw1 width fs k n ≤
        (originalJointLimit hw0 hw1 width fs hfs).approx p + epsilon ∧
      (originalJointLimit hw0 hw1 width fs hfs).approx p ≤
        originalTimeScalar hw0 hw1 width fs k n + epsilon := by
  let c := originalJointCauchy hw0 hw1 width fs hfs
  let s := QMhat _ c p
  have hs : jointModulus hw0 hw1 width fs epsilon ≤ s :=
    Nat.le_trans hp (self_le_QMhat _ c p)
  exact originalJoint_rectangle hw0 hw1 width fs hfs epsilon he k n s s hk hn
    (Nat.le_trans (Nat.le_max_right _ _) hs) (Nat.le_trans (Nat.le_max_left _ _) hs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.originalCutoffCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.jointTimeThreshold
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.jointCutoffThreshold
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.jointModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.originalJoint_rectangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.originalJointCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.originalJointLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.originalJoint_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy.originalJoint_approx
