/-
Track 11.7-fusion / R3i -- Dirichlet decomposition of the physical parity
head.

The sparse channel formula admits a second exact reduction.  Twice the bare
head slack is the difference of a two-step path energy and three adjacent
path energies, plus four explicit endpoint squares.  The retuned head follows
once (i) the two-step energy pays the adjacent energy and (ii) the endpoint
reserve pays the small `1-q^5` debt.  These are true positive-energy targets,
not restatements of the original coefficient inequality.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeadLinearCertificate
import YMGap.Continuum.AllWindowCorrDirichlet
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2BlockCompatibleHeadDirichletCompiler

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.EndpointCutoffTailFormula
open YMGap.Continuum.P2RetunedEdgeFormula
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private def q2 : Q' := Q'.ofNat 2
private def q3 : Q' := Q'.ofNat 3
private def q6 : Q' := Q'.ofNat 6

/-- Distance-two path energy on the same coefficient string. -/
def headTwoStepEnergy (w : Q') (N : Nat) : Q' :=
  fsum (fun a =>
    dirichletTerm (coeffW w a) (coeffW w (a + 2))) (N - 1)

/-- Boundary term in the doubled sparse-head identity.  The definition is
used only with `2 <= N`, so both predecessor indices are genuine. -/
def headBoundary (w : Q') (N : Nat) : Q' :=
  coeffW w 0 * coeffW w 0 +
    q2 * (coeffW w 1 * coeffW w 1) +
    q2 * (coeffW w (N - 1) * coeffW w (N - 1)) +
    (-(coeffW w N * coeffW w N))

/-- Bare, unretuned slack between three adjacent bands and channel two. -/
def headBareSlack (w : Q') (N : Nat) : Q' :=
  q3 * adjCorr w N + (-channelTwoFormula w N)

private def headStepIncrement (w : Q') (M : Nat) : Q' :=
  q2 *
    (q3 * (coeffW w (M + 2) * coeffW w (M + 3)) +
      (-(coeffW w (M + 3) * coeffW w (M + 3) +
        q2 * (coeffW w (M + 1) * coeffW w (M + 3)))))

private theorem headBareSlack_step (w : Q') (M : Nat) :
    q2 * headBareSlack w (M + 3) ≈
      q2 * headBareSlack w (M + 2) + headStepIncrement w M := by
  unfold headBareSlack headStepIncrement adjCorr channelTwoFormula
    channelTwoDiag channelTwoJump q2 q3
  simp only [show M + 3 - 1 = (M + 1) + 1 by omega,
    show M + 2 - 1 = M + 1 by omega, fsum, Nat.add_assoc,
    Nat.reduceAdd]
  ring_qeqv

private def energyIncrementL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  let dir (a b : RingNormaliser.PolyExpr) :=
    .add (.add (.mul b b) (.neg (.mul a b)))
      (.add (.mul a a) (.neg (.mul a b)))
  .add
    (.add (.mul (.const 2) (dir x z))
      (.neg (.mul (.const 3) (dir y z))))
    (.add
      (.add (.mul (.const 3) (.mul y y))
        (.neg (.mul (.const 2) (.mul x x))))
      (.neg (.mul z z)))

private def energyIncrementR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  .mul (.const 2)
    (.add (.mul (.const 3) (.mul y z))
      (.neg (.add (.mul z z) (.mul (.const 2) (.mul x z)))))

private theorem energyIncrement_normal :
    RingNormaliser.normalize energyIncrementL =
      RingNormaliser.normalize energyIncrementR := by decide

private theorem energyIncrement_eqv (x y z : Q') :
    q2 * dirichletTerm x z +
        (-(q3 * dirichletTerm y z)) +
        (q3 * (y * y) + (-(q2 * (x * x))) + (-(z * z))) ≈
      q2 * (q3 * (y * z) + (-(z * z + q2 * (x * z)))) := by
  simpa [energyIncrementL, energyIncrementR, RingNormaliser.eval,
    dirichletTerm, q2, q3] using
    (RingNormaliser.poly_identity_of_normal_eq
      energyIncrementL energyIncrementR energyIncrement_normal
      (fun | 0 => x | 1 => y | _ => z))

private def boundaryStepL : RingNormaliser.PolyExpr :=
  let c0 := RingNormaliser.PolyExpr.var 0
  let c1 := RingNormaliser.PolyExpr.var 1
  let y := RingNormaliser.PolyExpr.var 3
  let z := RingNormaliser.PolyExpr.var 4
  .add
    (.add
      (.add (.mul c0 c0) (.mul (.const 2) (.mul c1 c1)))
      (.mul (.const 2) (.mul y y)))
    (.neg (.mul z z))

private def boundaryStepR : RingNormaliser.PolyExpr :=
  let c0 := RingNormaliser.PolyExpr.var 0
  let c1 := RingNormaliser.PolyExpr.var 1
  let x := RingNormaliser.PolyExpr.var 2
  let y := RingNormaliser.PolyExpr.var 3
  let z := RingNormaliser.PolyExpr.var 4
  .add
    (.add
      (.add
        (.add (.mul c0 c0) (.mul (.const 2) (.mul c1 c1)))
        (.mul (.const 2) (.mul x x)))
      (.neg (.mul y y)))
    (.add
      (.add (.mul (.const 3) (.mul y y))
        (.neg (.mul (.const 2) (.mul x x))))
      (.neg (.mul z z)))

private theorem boundaryStep_normal :
    RingNormaliser.normalize boundaryStepL =
      RingNormaliser.normalize boundaryStepR := by decide

private theorem boundaryStep_eqv (c0 c1 x y z : Q') :
    c0 * c0 + q2 * (c1 * c1) + q2 * (y * y) + (-(z * z)) ≈
      (c0 * c0 + q2 * (c1 * c1) + q2 * (x * x) + (-(y * y))) +
        (q3 * (y * y) + (-(q2 * (x * x))) + (-(z * z))) := by
  simpa [boundaryStepL, boundaryStepR, RingNormaliser.eval, q2, q3] using
    (RingNormaliser.poly_identity_of_normal_eq
      boundaryStepL boundaryStepR boundaryStep_normal
      (fun | 0 => c0 | 1 => c1 | 2 => x | 3 => y | _ => z))

private def energySplitL : RingNormaliser.PolyExpr :=
  .add
    (.add
      (.mul (.const 2) (.add (.var 0) (.var 3)))
      (.neg (.mul (.const 3) (.add (.var 1) (.var 4)))))
    (.add (.var 2) (.var 5))

private def energySplitR : RingNormaliser.PolyExpr :=
  .add
    (.add
      (.add (.mul (.const 2) (.var 0))
        (.neg (.mul (.const 3) (.var 1))))
      (.var 2))
    (.add
      (.add (.mul (.const 2) (.var 3))
        (.neg (.mul (.const 3) (.var 4))))
      (.var 5))

private theorem energySplit_normal :
    RingNormaliser.normalize energySplitL =
      RingNormaliser.normalize energySplitR := by decide

private theorem energySplit_eqv (E2 E1 B inc2 inc1 incB : Q') :
    q2 * (E2 + inc2) + (-(q3 * (E1 + inc1))) + (B + incB) ≈
      (q2 * E2 + (-(q3 * E1)) + B) +
        (q2 * inc2 + (-(q3 * inc1)) + incB) := by
  simpa [energySplitL, energySplitR, RingNormaliser.eval, q2, q3] using
    (RingNormaliser.poly_identity_of_normal_eq
      energySplitL energySplitR energySplit_normal
      (fun | 0 => E2 | 1 => E1 | 2 => B | 3 => inc2 | 4 => inc1 | _ => incB))

private theorem headTwoStepEnergy_step (w : Q') (M : Nat) :
    headTwoStepEnergy w (M + 3) ≈
      headTwoStepEnergy w (M + 2) +
        dirichletTerm (coeffW w (M + 1)) (coeffW w (M + 3)) := by
  unfold headTwoStepEnergy
  rw [show M + 3 - 1 = (M + 1) + 1 by omega, fsum_succ,
    show M + 2 - 1 = M + 1 by omega,
    show M + 1 + 2 = M + 3 by omega]
  exact Q'.eqv_refl _

private theorem adjacentEnergy_step (w : Q') (M : Nat) :
    dirichletEnergy w (M + 3) ≈
      dirichletEnergy w (M + 2) +
        dirichletTerm (coeffW w (M + 2)) (coeffW w (M + 3)) := by
  unfold dirichletEnergy
  rw [show M + 3 = (M + 2) + 1 by omega, fsum_succ,
    show M + 2 + 1 = M + 3 by omega]
  exact Q'.eqv_refl _

private theorem headBoundary_step (w : Q') (M : Nat) :
    headBoundary w (M + 3) ≈
      headBoundary w (M + 2) +
        (q3 * (coeffW w (M + 2) * coeffW w (M + 2)) +
          (-(q2 * (coeffW w (M + 1) * coeffW w (M + 1)))) +
          (-(coeffW w (M + 3) * coeffW w (M + 3)))) := by
  unfold headBoundary
  simpa only [show M + 3 - 1 = M + 2 by omega,
    show M + 2 - 1 = M + 1 by omega] using
    boundaryStep_eqv (coeffW w 0) (coeffW w 1)
      (coeffW w (M + 1)) (coeffW w (M + 2)) (coeffW w (M + 3))

private theorem headIncrement_step (w : Q') (M : Nat) :
    q2 * dirichletTerm (coeffW w (M + 1)) (coeffW w (M + 3)) +
        (-(q3 * dirichletTerm (coeffW w (M + 2)) (coeffW w (M + 3)))) +
        (q3 * (coeffW w (M + 2) * coeffW w (M + 2)) +
          (-(q2 * (coeffW w (M + 1) * coeffW w (M + 1)))) +
          (-(coeffW w (M + 3) * coeffW w (M + 3)))) ≈
      headStepIncrement w M := by
  unfold headStepIncrement
  exact energyIncrement_eqv _ _ _

private theorem energyAssembly_eqv
    {E2' E2 E1' E1 B' B inc2 inc1 incB inc : Q'}
    (hE2 : E2' ≈ E2 + inc2)
    (hE1 : E1' ≈ E1 + inc1)
    (hB : B' ≈ B + incB)
    (hinc : q2 * inc2 + (-(q3 * inc1)) + incB ≈ inc) :
    q2 * E2' + (-(q3 * E1')) + B' ≈
      (q2 * E2 + (-(q3 * E1)) + B) + inc := by
  refine Q'.eqv_trans _
    (q2 * (E2 + inc2) + (-(q3 * (E1 + inc1))) + (B + incB)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left q2 _ _ hE2)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left q3 _ _ hE1)))
      hB
  · refine Q'.eqv_trans _
      ((q2 * E2 + (-(q3 * E1)) + B) +
        (q2 * inc2 + (-(q3 * inc1)) + incB)) _
      (energySplit_eqv E2 E1 B inc2 inc1 incB) ?_
    exact Q'.add_eqv_congr_left _ _ _ hinc

private theorem headEnergyBoundary_step (w : Q') (M : Nat) :
    q2 * headTwoStepEnergy w (M + 3) +
        (-(q3 * dirichletEnergy w (M + 3))) +
        headBoundary w (M + 3) ≈
      (q2 * headTwoStepEnergy w (M + 2) +
        (-(q3 * dirichletEnergy w (M + 2))) +
        headBoundary w (M + 2)) +
          headStepIncrement w M := by
  exact energyAssembly_eqv
    (headTwoStepEnergy_step w M) (adjacentEnergy_step w M)
    (headBoundary_step w M) (headIncrement_step w M)

private def headBaseL : RingNormaliser.PolyExpr :=
  let x0 := RingNormaliser.PolyExpr.var 0
  let x1 := RingNormaliser.PolyExpr.var 1
  let x2 := RingNormaliser.PolyExpr.var 2
  .mul (.const 2)
    (.add
      (.mul (.const 3) (.add (.mul x0 x1) (.mul x1 x2)))
      (.neg
        (.add (.add (.mul x1 x1) (.mul x2 x2))
          (.mul (.const 2) (.mul x0 x2)))))

private def headBaseR : RingNormaliser.PolyExpr :=
  let x0 := RingNormaliser.PolyExpr.var 0
  let x1 := RingNormaliser.PolyExpr.var 1
  let x2 := RingNormaliser.PolyExpr.var 2
  let dir (a b : RingNormaliser.PolyExpr) :=
    .add (.add (.mul b b) (.neg (.mul a b)))
      (.add (.mul a a) (.neg (.mul a b)))
  .add
    (.add
      (.mul (.const 2) (dir x0 x2))
      (.neg (.mul (.const 3) (.add (dir x0 x1) (dir x1 x2)))))
    (.add
      (.add
        (.add (.mul x0 x0) (.mul (.const 2) (.mul x1 x1)))
        (.mul (.const 2) (.mul x1 x1)))
      (.neg (.mul x2 x2)))

private theorem headBase_normal :
    RingNormaliser.normalize headBaseL =
      RingNormaliser.normalize headBaseR := by decide

private theorem headBase_eqv (x0 x1 x2 : Q') :
    q2 *
        (q3 * (x0 * x1 + x1 * x2) +
          (-(x1 * x1 + x2 * x2 + q2 * (x0 * x2)))) ≈
      q2 * dirichletTerm x0 x2 +
          (-(q3 * (dirichletTerm x0 x1 + dirichletTerm x1 x2))) +
          (x0 * x0 + q2 * (x1 * x1) + q2 * (x1 * x1) + (-(x2 * x2))) := by
  simpa [headBaseL, headBaseR, RingNormaliser.eval, dirichletTerm, q2, q3] using
    (RingNormaliser.poly_identity_of_normal_eq
      headBaseL headBaseR headBase_normal
      (fun | 0 => x0 | 1 => x1 | _ => x2))

/-- **Exact all-cutoff sparse-head Dirichlet identity.** -/
theorem twice_headBareSlack_eqv_energy_boundary (w : Q') : forall M : Nat,
    q2 * headBareSlack w (M + 2) ≈
      q2 * headTwoStepEnergy w (M + 2) +
        (-(q3 * dirichletEnergy w (M + 2))) +
        headBoundary w (M + 2)
  | 0 => by
      unfold headBareSlack headTwoStepEnergy headBoundary adjCorr
        channelTwoFormula channelTwoDiag channelTwoJump dirichletEnergy
      simp only [fsum, Q'.zero_add']
      exact headBase_eqv (coeffW w 0) (coeffW w 1) (coeffW w 2)
  | M + 1 => by
      have ih := twice_headBareSlack_eqv_energy_boundary w M
      refine Q'.eqv_trans _ _ _ (headBareSlack_step w M) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (headStepIncrement w M) ih) ?_
      exact Q'.eqv_symm (headEnergyBoundary_step w M)

/-- The exact retune debt removed from `3*A` when `q^5` replaces one. -/
def headRetuneDebt (w : Q') (N : Nat) : Q' :=
  q6 * (((1 : Q') + (-qpow (p2RetunedWeight w) 5)) * adjCorr w N)

/-- Retune debt for an arbitrary explicit head power.  Keeping the power as
data lets the same Dirichlet identity serve both the canonical retune and the
heat-matched half-time factor `w^3`. -/
def headPowerDebt (rho w : Q') (N : Nat) : Q' :=
  Q'.ofNat 6 * (((1 : Q') + (-rho)) * adjCorr w N)

private def retuneSlackL : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 2)
      (.add (.mul (.const 3) (.var 0)) (.neg (.var 1))))
    (.neg
      (.mul (.const 6)
        (.mul (.add (.const 1) (.neg (.var 2))) (.var 0))))

private def retuneSlackR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 2)
      (.mul (.mul (.const 3) (.var 2)) (.var 0)))
    (.neg (.mul (.const 2) (.var 1)))

private theorem retuneSlack_normal :
    RingNormaliser.normalize retuneSlackL =
      RingNormaliser.normalize retuneSlackR := by decide

private theorem retuneSlack_eqv (A C q5 : Q') :
    q2 * (q3 * A + (-C)) +
        (-(q6 * (((1 : Q') + (-q5)) * A))) ≈
      q2 * (q3 * q5 * A) + (-(q2 * C)) := by
  simpa [retuneSlackL, retuneSlackR, RingNormaliser.eval, q2, q3, q6,
    show Q'.ofInt 1 = Q'.ofNat 1 from rfl,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl,
    show Q'.ofInt 6 = Q'.ofNat 6 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      retuneSlackL retuneSlackR retuneSlack_normal
      (fun | 0 => A | 1 => C | _ => q5))

private def boxScaleL : RingNormaliser.PolyExpr :=
  .mul (.const 2) (.mul (.mul (.const 3) (.var 0)) (.var 1))

private def boxScaleR : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.mul (.const 3) (.mul (.const 2) (.var 1)))

private theorem boxScale_normal :
    RingNormaliser.normalize boxScaleL =
      RingNormaliser.normalize boxScaleR := by decide

private theorem boxScale_eqv (q5 A : Q') :
    q2 * (q3 * q5 * A) ≈ q5 * (Q'.ofNat 3 * (Q'.ofNat 2 * A)) := by
  simpa [boxScaleL, boxScaleR, RingNormaliser.eval, q2, q3,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      boxScaleL boxScaleR boxScale_normal
      (fun | 0 => q5 | _ => A))

/-- Honest positive-energy data sufficient for the sparse parity head. -/
structure P2RetunedHeadDirichletData (N : Nat) (w : Q') : Type where
  cutoff : 2 <= N
  energy : q3 * dirichletEnergy w N <= q2 * headTwoStepEnergy w N
  boundary : headRetuneDebt w N <= headBoundary w N

/-- Positive-energy data for a caller-supplied head power.  This is a strict
generalization of `P2RetunedHeadDirichletData`: the common energy comparison
is unchanged, while the endpoint reserve pays the exact selected debt. -/
structure P2HeadPowerDirichletData (N : Nat) (w rho : Q') : Type where
  cutoff : 2 <= N
  energy : q3 * dirichletEnergy w N <= q2 * headTwoStepEnergy w N
  boundary : headPowerDebt rho w N <= headBoundary w N

/-- The sparse-head Dirichlet identity compiled at an arbitrary explicit
power.  This is the proof-about-computation theorem used by the physical
half-time head: no coefficient scan depends on the cutoff. -/
theorem boxHead_of_powerDirichletData {N : Nat} {w rho : Q'}
    (D : P2HeadPowerDirichletData N w rho) :
    dimQ 1 * boxSum w N 2 <= rho * (dimQ 2 * boxSum w N 1) := by
  let A := adjCorr w N
  let C := channelTwoFormula w N
  have hidentity := twice_headBareSlack_eqv_energy_boundary w (N - 2)
  have hcut := D.cutoff
  have hN : N - 2 + 2 = N := by omega
  rw [hN] at hidentity
  have henergyNonneg : (0 : Q') <=
      q2 * headTwoStepEnergy w N + (-(q3 * dirichletEnergy w N)) := by
    exact Q'.sub_nonneg_of_le D.energy
  have hboundaryNonneg : (0 : Q') <=
      headBoundary w N + (-headPowerDebt rho w N) := by
    exact Q'.sub_nonneg_of_le D.boundary
  have hsumNonneg : (0 : Q') <=
      (q2 * headTwoStepEnergy w N +
        (-(q3 * dirichletEnergy w N))) +
        (headBoundary w N + (-headPowerDebt rho w N)) :=
    Q'.zero_le_add _ _ henergyNonneg hboundaryNonneg
  have hslackNonneg : (0 : Q') <=
      q2 * (q3 * A + (-C)) + (-headPowerDebt rho w N) := by
    let E := q2 * headTwoStepEnergy w N + (-(q3 * dirichletEnergy w N))
    let B := headBoundary w N
    let debt := -headPowerDebt rho w N
    have hgroup : E + (B + debt) ≈ (E + B) + debt :=
      Q'.eqv_symm (Q'.add_assoc_eqv E B debt)
    have hid : (E + B) + debt ≈ q2 * headBareSlack w N + debt :=
      Q'.add_eqv_congr_right _ _ debt (Q'.eqv_symm hidentity)
    have hdef : q2 * headBareSlack w N + debt ≈
        q2 * (q3 * A + (-C)) + debt := by
      unfold headBareSlack A C
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ hsumNonneg
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hgroup
        (Q'.eqv_trans _ _ _ hid hdef)))
  have hcore : C <= q3 * rho * A := by
    have hscaledNonneg : (0 : Q') <=
        q2 * (q3 * rho * A) + (-(q2 * C)) := by
      exact Q'.le_trans' _ _ _ hslackNonneg
        (Q'.le_of_eqv (by
          unfold headPowerDebt A
          exact retuneSlack_eqv _ _ _))
    have hscaled : q2 * C <= q2 * (q3 * rho * A) :=
      Q'.le_of_sub_nonneg hscaledNonneg
    exact Q'.le_of_mul_le_mul_left hscaled (by decide)
  have hbox1 := boxSum_one_eq_twice_adjCorr w N
  have hbox2 := boxSum_two_eq_formula w N
  have hdim :
      q2 * (q3 * rho * A) ≈
        rho * (dimQ 2 * boxSum w N 1) := by
    unfold dimQ q2 q3
    refine Q'.eqv_trans _
      (rho * (Q'.ofNat 3 * (Q'.ofNat 2 * A))) _
      (boxScale_eqv rho A) ?_
    exact Q'.mul_eqv_congr_left rho _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _
        (Q'.eqv_symm hbox1))
  have hleft : dimQ 1 * boxSum w N 2 ≈ q2 * C := by
    unfold dimQ q2 C
    exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hbox2
  have hscaledCore := Q'.mul_le_mul_of_nonneg_left _ _ q2 hcore (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaledCore
      (Q'.le_of_eqv hdim))

/-- The two positive-energy inequalities compile to the exact weighted-box
head used by the parity-strand automaton. -/
theorem boxHead_of_dirichletData {N : Nat} {w : Q'}
    (D : P2RetunedHeadDirichletData N w) :
    dimQ 1 * boxSum w N 2 <=
      qpow (p2RetunedWeight w) 5 * (dimQ 2 * boxSum w N 1) := by
  let A := adjCorr w N
  let C := channelTwoFormula w N
  let q5 := qpow (p2RetunedWeight w) 5
  have hidentity := twice_headBareSlack_eqv_energy_boundary w (N - 2)
  have hcut := D.cutoff
  have hN : N - 2 + 2 = N := by omega
  rw [hN] at hidentity
  have henergyNonneg : (0 : Q') <=
      q2 * headTwoStepEnergy w N + (-(q3 * dirichletEnergy w N)) := by
    exact Q'.sub_nonneg_of_le D.energy
  have hboundaryNonneg : (0 : Q') <=
      headBoundary w N + (-headRetuneDebt w N) := by
    exact Q'.sub_nonneg_of_le D.boundary
  have hsumNonneg : (0 : Q') <=
      (q2 * headTwoStepEnergy w N +
        (-(q3 * dirichletEnergy w N))) +
        (headBoundary w N + (-headRetuneDebt w N)) :=
    Q'.zero_le_add _ _ henergyNonneg hboundaryNonneg
  have hslackNonneg : (0 : Q') <=
      q2 * (q3 * A + (-C)) + (-headRetuneDebt w N) := by
    let E := q2 * headTwoStepEnergy w N + (-(q3 * dirichletEnergy w N))
    let B := headBoundary w N
    let debt := -headRetuneDebt w N
    have hgroup : E + (B + debt) ≈ (E + B) + debt :=
      Q'.eqv_symm (Q'.add_assoc_eqv E B debt)
    have hid : (E + B) + debt ≈ q2 * headBareSlack w N + debt :=
      Q'.add_eqv_congr_right _ _ debt (Q'.eqv_symm hidentity)
    have hdef : q2 * headBareSlack w N + debt ≈
        q2 * (q3 * A + (-C)) + debt := by
      unfold headBareSlack A C
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ hsumNonneg
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hgroup
        (Q'.eqv_trans _ _ _ hid hdef)))
  have hcore : C <= q3 * q5 * A := by
    have hscaledNonneg : (0 : Q') <=
        q2 * (q3 * q5 * A) + (-(q2 * C)) := by
      exact Q'.le_trans' _ _ _ hslackNonneg
        (Q'.le_of_eqv (by
          unfold headRetuneDebt A q5
          exact retuneSlack_eqv _ _ _))
    have hscaled : q2 * C <= q2 * (q3 * q5 * A) :=
      Q'.le_of_sub_nonneg hscaledNonneg
    exact Q'.le_of_mul_le_mul_left hscaled (by decide)
  have hbox1 := boxSum_one_eq_twice_adjCorr w N
  have hbox2 := boxSum_two_eq_formula w N
  have hdim :
      q2 * (q3 * q5 * A) ≈
        q5 * (dimQ 2 * boxSum w N 1) := by
    unfold dimQ q2 q3
    refine Q'.eqv_trans _
      (q5 * (Q'.ofNat 3 * (Q'.ofNat 2 * A))) _
      (boxScale_eqv q5 A) ?_
    exact Q'.mul_eqv_congr_left q5 _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _
        (Q'.eqv_symm hbox1))
  have hleft : dimQ 1 * boxSum w N 2 ≈ q2 * C := by
    unfold dimQ q2 C
    exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hbox2
  have hscaledCore := Q'.mul_le_mul_of_nonneg_left _ _ q2 hcore (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaledCore
      (Q'.le_of_eqv hdim))

#print axioms twice_headBareSlack_eqv_energy_boundary
#print axioms boxHead_of_powerDirichletData
#print axioms boxHead_of_dirichletData

end YMGap.Continuum.P2BlockCompatibleHeadDirichletCompiler
