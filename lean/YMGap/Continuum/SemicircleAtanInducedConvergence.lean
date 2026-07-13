/-
# Constructive convergence of the induced Möbius atan partition

The transformed left sums need no independent compactness argument.  Their
right sums are squeezed by the source right sums, their left sums dominate the
source left sums, and the already-proved induced Darboux gap supplies the only
error.  Consequently any quantitative vanishing modulus for that gap makes
the induced sums converge to the existing rational endpoint integral.

This is the finite-to-limit change-of-variables half of rational atan
addition.  Identifying the same induced limit with the difference of the two
endpoint integrals remains a separate common-refinement/additivity step.
-/

import YMGap.Continuum.SemicircleAtanMachinMesh

namespace YMGap.Continuum.SemicircleAtanInducedConvergence

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanTransformedSqueeze
open YMGap.Continuum.SemicircleAtanInducedGap
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.SemicircleAtanMachinMesh

private theorem two_num_cast : ((2 : Q').num) = 2 := rfl
private theorem two_den_cast : (((2 : Q').den : Int)) = 1 := rfl

/-- The left Darboux sums on the Möbius image of the source grid. -/
def inducedLeftSeq
    (R S A B : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) : Nat → CReal :=
  fun N => CReal.ofQ'
    (inducedLeftGridSum R S A B (N+1) hS hB (Nat.succ_pos N) hbranch)

private theorem half_le_self (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    HalfPow.half * epsilon ≤ epsilon := by
  let q := HalfPow.half * epsilon
  have hq0 : (0 : Q') ≤ q :=
    Q'.le_of_lt (ExpNeg.half_mul_pos epsilon hepsilon)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg q q hq0)
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

private theorem sourceRight_le_scaledLeft
    (A B m n : Nat) (hB : 0 < B) (hm : 0 < m) (hn : 0 < n) :
    sourceRightGridSum A B m hB hm ≤ scaledLeftSum A B n hB hn := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (sourceRightGridSum_eqv_scaledRightSum A B m hB hm))
    (scaledRightSum_le_scaledLeftSum_cross A B m n hB hm hn)

private theorem scaledLeft_le_inducedLeft_add_mesh
    (R S A B m n : Nat) (hS : 0 < S) (hB : 0 < B)
    (hm : 0 < m) (hn : 0 < n) (hbranch : R*A < S*B) :
    scaledLeftSum A B m hB hm ≤
      inducedLeftGridSum R S A B n hS hB hn hbranch +
        scaledMesh A B m hB hm := by
  have hcross := scaledLeftSum_le_other_add_mesh A B m n hB hm hn
  have hsource := sourceLeftGridSum_le_inducedLeftGridSum
    R S A B n hS hB hn hbranch
  have hscaledSource : scaledLeftSum A B n hB hn ≤
      inducedLeftGridSum R S A B n hS hB hn hbranch :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (sourceLeftGridSum_eqv_scaledLeftSum A B n hB hn))
      hsource
  exact Q'.le_trans' _ _ _ hcross
    (Q'.add_le_add_right _ _ _ hscaledSource)

/-- **Induced-partition convergence from the explicit gap modulus.**

The hypothesis is exactly the quantitative fact later discharged by each of
the four Machin mesh estimates.  No weak-existence or choice principle is
used: the proof gives a stage and an approximation stage directly. -/
theorem inducedLeftSeq_converges_of_gap_vanishes
    (R S A B : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B)
    (hgap : ∀ epsilon : Q', (0 : Q') < epsilon →
      ∃ Nstage : Nat, ∀ N : Nat, Nstage ≤ N →
        inducedMeshBound R S A B (N+1) hS hB (Nat.succ_pos N) hbranch * 2 ≤
          epsilon) :
    CReal.ConvergesTo (inducedLeftSeq R S A B hS hB hbranch)
      (rationalAtanIntegral A B hB) := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  have hqle : q ≤ epsilon := half_le_self epsilon hepsilon
  obtain ⟨Nstage, hNstage⟩ := hgap q hqpos
  refine ⟨Nstage, fun N hN => ?_⟩
  let m : Nat := N + 1
  have hm : 0 < m := Nat.succ_pos N
  have hgapN := hNstage N hN
  refine ⟨2*A*q.den, fun n hn => ?_⟩
  have hnpos : 0 < n+1 := Nat.succ_pos n
  have hnNat : 2*A*q.den ≤ B*(n+1) := by
    calc
      2*A*q.den ≤ n := hn
      _ ≤ n+1 := Nat.le_succ n
      _ = 1*(n+1) := (Nat.one_mul _).symm
      _ ≤ B*(n+1) := Nat.mul_le_mul_right (n+1) hB
  have hmeshN : scaledMesh A B (n+1) hB hnpos ≤ q :=
    scaledMesh_succ_le hqpos A B n hB hnNat
  constructor
  · have hindGap := inducedLeft_le_right_add_two_mesh
      R S A B m hS hB hm hbranch
    have hrightSource := inducedRightGridSum_le_sourceRightGridSum
      R S A B m hS hB hm hbranch
    have hrightTarget := sourceRight_le_scaledLeft A B m (n+1) hB hm hnpos
    have hright : inducedRightGridSum R S A B m hS hB hm hbranch ≤
        scaledLeftSum A B (n+1) hB hnpos :=
      Q'.le_trans' _ _ _ hrightSource hrightTarget
    have h1 := Q'.le_trans' _ _ _ hindGap
      (Q'.add_le_add_right _ _ _ hright)
    have h2 := Q'.add_le_add_left
      (scaledLeftSum A B (n+1) hB hnpos) _ _ hgapN
    exact Q'.le_trans' _ _ _ h1
      (Q'.le_trans' _ _ _ h2
        (Q'.add_le_add_left
          (scaledLeftSum A B (n+1) hB hnpos) _ _ hqle))
  · have hleft := scaledLeft_le_inducedLeft_add_mesh
      R S A B (n+1) m hS hB hnpos hm hbranch
    exact Q'.le_trans' _ _ _ hleft
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left
          (inducedLeftGridSum R S A B m hS hB hm hbranch) _ _ hmeshN)
        (Q'.add_le_add_left
          (inducedLeftGridSum R S A B m hS hB hm hbranch) _ _ hqle))

private theorem invNat_mul_two_eqv_two_over (n : Nat) (hn : 0 < n) :
    (invNat n hn * 2).eqv (Q'.mkPos 2 n hn) := by
  show (invNat n hn * 2).num * ((Q'.mkPos 2 n hn).den : Int) =
    (Q'.mkPos 2 n hn).num * ((invNat n hn * 2).den : Int)
  unfold invNat
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    two_num_cast, two_den_cast, Int.mul_one, Int.one_mul]

private theorem gap_vanishes_of_mesh_le_invNat
    (R S A B : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B)
    (hmesh : ∀ n : Nat, ∀ hn : 0 < n,
      inducedMeshBound R S A B n hS hB hn hbranch ≤ invNat n hn) :
    ∀ epsilon : Q', (0 : Q') < epsilon →
      ∃ Nstage : Nat, ∀ N : Nat, Nstage ≤ N →
        inducedMeshBound R S A B (N+1) hS hB (Nat.succ_pos N) hbranch * 2 ≤
          epsilon := by
  intro epsilon hepsilon
  refine ⟨2*epsilon.den, fun N hN => ?_⟩
  have hcut : 2*epsilon.den ≤ N+1 := Nat.le_trans hN (Nat.le_succ N)
  have htwo : Q'.mkPos 2 (N+1) (Nat.succ_pos N) ≤ epsilon :=
    SemicircleRationalPolygon.two_over_succ_le hepsilon hcut
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ 2
    (hmesh (N+1) (Nat.succ_pos N)) (by decide : (0 : Q') ≤ 2)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (invNat_mul_two_eqv_two_over (N+1) (Nat.succ_pos N))) htwo)

/-- First branch of the exact Machin path: the induced partition from
`1/239` along `117/598` converges to the source endpoint integral. -/
theorem first_inducedLeftSeq_converges :
    CReal.ConvergesTo
      (inducedLeftSeq 1 239 117 598 (by decide) (by decide) (by decide))
      (rationalAtanIntegral 117 598 (by decide)) := by
  apply inducedLeftSeq_converges_of_gap_vanishes
  exact gap_vanishes_of_mesh_le_invNat 1 239 117 598
    (by decide) (by decide) (by decide)
    (fun n hn => first_inducedMesh_le_invNat n hn)

/-- Second branch of the exact Machin path. -/
theorem second_inducedLeftSeq_converges :
    CReal.ConvergesTo
      (inducedLeftSeq 117 598 1 5 (by decide) (by decide) (by decide))
      (rationalAtanIntegral 1 5 (by decide)) := by
  apply inducedLeftSeq_converges_of_gap_vanishes
  exact gap_vanishes_of_mesh_le_invNat 117 598 1 5
    (by decide) (by decide) (by decide)
    (fun n hn => second_inducedMesh_le_invNat n hn)

/-- Third branch of the exact Machin path. -/
theorem third_inducedLeftSeq_converges :
    CReal.ConvergesTo
      (inducedLeftSeq 1183 2873 1 5 (by decide) (by decide) (by decide))
      (rationalAtanIntegral 1 5 (by decide)) := by
  apply inducedLeftSeq_converges_of_gap_vanishes
  exact gap_vanishes_of_mesh_le_invNat 1183 2873 1 5
    (by decide) (by decide) (by decide)
    (fun n hn => third_inducedMesh_le_invNat n hn)

/-- Fourth branch of the exact Machin path. -/
theorem fourth_inducedLeftSeq_converges :
    CReal.ConvergesTo
      (inducedLeftSeq 4394 6591 1 5 (by decide) (by decide) (by decide))
      (rationalAtanIntegral 1 5 (by decide)) := by
  apply inducedLeftSeq_converges_of_gap_vanishes
  exact gap_vanishes_of_mesh_le_invNat 4394 6591 1 5
    (by decide) (by decide) (by decide)
    (fun n hn => fourth_inducedMesh_le_invNat n hn)

end YMGap.Continuum.SemicircleAtanInducedConvergence

#print axioms YMGap.Continuum.SemicircleAtanInducedConvergence.inducedLeftSeq_converges_of_gap_vanishes
#print axioms YMGap.Continuum.SemicircleAtanInducedConvergence.first_inducedLeftSeq_converges
#print axioms YMGap.Continuum.SemicircleAtanInducedConvergence.second_inducedLeftSeq_converges
#print axioms YMGap.Continuum.SemicircleAtanInducedConvergence.third_inducedLeftSeq_converges
#print axioms YMGap.Continuum.SemicircleAtanInducedConvergence.fourth_inducedLeftSeq_converges
