/-
# Constructive rational atan addition from joined Darboux partitions

The finite common-refinement bracket is lifted here to constructive reals.
The only quantitative input is the vanishing mesh bound already consumed by
the Mobius-induced convergence theorem.  Thus one certificate simultaneously
proves convergence of the transformed source grid and the rational atan
addition identity.
-/

import YMGap.Continuum.SemicircleAtanFiniteMeshBridge
import YMGap.Continuum.SemicircleAtanInducedConvergence
import YMGap.Continuum.SemicircleAtanEndpointSeriesConvergence
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.SemicircleAtanAddition

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanTransformedSqueeze
open YMGap.Continuum.SemicircleAtanInducedGap
open YMGap.Continuum.SemicircleAtanInducedConvergence
open YMGap.Continuum.SemicircleAtanFiniteMeshBridge
open YMGap.Continuum.SemicircleAtanMachinPath
open YMGap.Continuum.SemicircleAtanMachinMesh
open YMGap.Continuum.SemicircleAtanMobiusKernel
open YMGap.Continuum.SemicircleAtanDarboux
open YMGap.Continuum.SemicircleAtanEndpointSeriesConvergence

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem two_num_cast : ((2 : Q').num) = 2 := rfl
private theorem two_den_cast : (((2 : Q').den : Int)) = 1 := rfl
private theorem four_num_cast : ((4 : Q').num) = 4 := rfl
private theorem four_den_cast : (((4 : Q').den : Int)) = 1 := rfl
private theorem sixteen_num_cast : ((16 : Q').num) = 16 := rfl
private theorem sixteen_den_cast : (((16 : Q').den : Int)) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, two_num_cast, two_den_cast, four_num_cast,
               four_den_cast, sixteen_num_cast, sixteen_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero, Int.mul_assoc,
               Int.mul_comm, Int.mul_left_comm];
             omega))

/-- The joined left quadrature, represented as the sum of its two constructive
real point masses.  Its approximation is definitionally the sum of the direct
and Mobius-induced left Darboux sums. -/
def joinedLeftSeq
    (R S A B : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) (N : Nat) : CReal :=
  CReal.add (rationalAtanSeq R S hS N)
    (inducedLeftSeq R S A B hS hB hbranch N)

private theorem creal_equiv_refl (x : CReal) : CReal.Equiv x x := by
  intro epsilon hepsilon
  refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
  · exact Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon)
  · exact Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon)

private theorem cadd_assoc (A B C : CReal) :
    CReal.Equiv (CReal.add (CReal.add A B) C)
      (CReal.add A (CReal.add B C)) :=
  TrigAdd.equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n))

private theorem cadd_comm (A B : CReal) :
    CReal.Equiv (CReal.add A B) (CReal.add B A) :=
  TrigAdd.equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (A.approx n) (B.approx n))

private theorem cadd_zero (A : CReal) :
    CReal.Equiv (CReal.add A CReal.czero) A :=
  TrigAdd.equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))

private theorem cadd_neg_self (A : CReal) :
    CReal.Equiv (CReal.add A (CReal.neg A)) CReal.czero :=
  TrigAdd.equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n))

private theorem addRightCancel {A B C : CReal}
    (h : CReal.Equiv (CReal.add A C) (CReal.add B C)) : CReal.Equiv A B :=
  CReal.Equiv.trans (CReal.Equiv.symm (cadd_zero A))
    (CReal.Equiv.trans
      (CReal.add_congr_right (CReal.Equiv.symm (cadd_neg_self C)))
      (CReal.Equiv.trans (CReal.Equiv.symm (cadd_assoc A C (CReal.neg C)))
        (CReal.Equiv.trans (CReal.add_congr_left h)
          (CReal.Equiv.trans (cadd_assoc B C (CReal.neg C))
            (CReal.Equiv.trans (CReal.add_congr_right (cadd_neg_self C))
              (cadd_zero B))))))

private theorem addLeftCancel {A B C : CReal}
    (h : CReal.Equiv (CReal.add C A) (CReal.add C B)) : CReal.Equiv A B :=
  addRightCancel ((cadd_comm A C).trans (h.trans (cadd_comm B C).symm))

private theorem cadd_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A B) (CReal.add A' B') :=
  (CReal.add_congr_left hA).trans (CReal.add_congr_right hB)

private theorem invNat_mul_two_eqv_two_over (n : Nat) (hn : 0 < n) :
    (invNat n hn * 2).eqv (Q'.mkPos 2 n hn) := by
  show (invNat n hn * 2).num * ((Q'.mkPos 2 n hn).den : Int) =
    (Q'.mkPos 2 n hn).num * ((invNat n hn * 2).den : Int)
  unfold invNat
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    two_num_cast, two_den_cast, Int.mul_one, Int.one_mul]

/-- A pointwise `1/n` bound gives the exact vanishing modulus required by the
joined-partition limit theorem. -/
theorem inducedGap_vanishes_of_mesh_le_invNat
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

/-- The joined left quadrature converges to the direct integral at the
tangent-addition endpoint.  The proof is an exact Darboux squeeze:

* joined right is below target left;
* target right is below joined left;
* the direct-source, induced, and target Darboux gaps vanish with explicit
  rational stages.
-/
theorem joinedLeftSeq_converges_to_target
    (R S A B T U : Nat)
    (hS : 0 < S) (hB : 0 < B) (hU : 0 < U)
    (hbranch : R*A < S*B)
    (htarget : (tanAdd (rat R S hS) (rat A B hB)
      (endpointReserve_pos R S A B hS hB hbranch)).eqv (rat T U hU))
    (hgap : ∀ epsilon : Q', (0 : Q') < epsilon →
      ∃ Nstage : Nat, ∀ N : Nat, Nstage ≤ N →
        inducedMeshBound R S A B (N+1) hS hB (Nat.succ_pos N) hbranch * 2 ≤
          epsilon) :
    CReal.ConvergesTo (joinedLeftSeq R S A B hS hB hbranch)
      (rationalAtanIntegral T U hU) := by
  intro epsilon hepsilon
  let q : Q' := half * epsilon
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨Ngap, hNgap⟩ := hgap q hqpos
  refine ⟨max (2*R*q.den) Ngap, fun N hN => ?_⟩
  have hNR : 2*R*q.den ≤ N :=
    Nat.le_trans (Nat.le_max_left _ _) hN
  have hNG : Ngap ≤ N :=
    Nat.le_trans (Nat.le_max_right _ _) hN
  have hsourceNat : 2*R*q.den ≤ S*(N+1) := by
    calc
      2*R*q.den ≤ N := hNR
      _ ≤ N+1 := Nat.le_succ N
      _ = 1*(N+1) := (Nat.one_mul _).symm
      _ ≤ S*(N+1) := Nat.mul_le_mul_right (N+1) hS
  have hsourceMesh :
      scaledMesh R S (N+1) hS (Nat.succ_pos N) ≤ q :=
    scaledMesh_succ_le hqpos R S N hS hsourceNat
  have hinducedMesh :
      inducedMeshBound R S A B (N+1) hS hB (Nat.succ_pos N) hbranch * 2 ≤ q :=
    hNgap N hNG
  refine ⟨2*T*epsilon.den, fun n hn => ?_⟩
  have htargetNat : 2*T*epsilon.den ≤ U*(n+1) := by
    calc
      2*T*epsilon.den ≤ n := hn
      _ ≤ n+1 := Nat.le_succ n
      _ = 1*(n+1) := (Nat.one_mul _).symm
      _ ≤ U*(n+1) := Nat.mul_le_mul_right (n+1) hU
  have htargetMesh :
      scaledMesh T U (n+1) hU (Nat.succ_pos n) ≤ epsilon :=
    scaledMesh_succ_le hepsilon T U n hU htargetNat
  change
    scaledLeftSum R S (N+1) hS (Nat.succ_pos N) +
          inducedLeftGridSum R S A B (N+1) hS hB
            (Nat.succ_pos N) hbranch ≤
        scaledLeftSum T U (n+1) hU (Nat.succ_pos n) + epsilon ∧
      scaledLeftSum T U (n+1) hU (Nat.succ_pos n) ≤
        scaledLeftSum R S (N+1) hS (Nat.succ_pos N) +
            inducedLeftGridSum R S A B (N+1) hS hB
              (Nat.succ_pos N) hbranch + epsilon
  constructor
  · have hsGap := scaledLeftSum_le_right_add_mesh
      R S (N+1) hS (Nat.succ_pos N)
    have hiGap := inducedLeft_le_right_add_two_mesh
      R S A B (N+1) hS hB (Nat.succ_pos N) hbranch
    have hsGapQ :
        scaledLeftSum R S (N+1) hS (Nat.succ_pos N) ≤
          scaledRightSum R S (N+1) hS (Nat.succ_pos N) + q :=
      Q'.le_trans' _ _ _ hsGap
        (Q'.add_le_add_left _ _ _ hsourceMesh)
    have hiGapQ :
        inducedLeftGridSum R S A B (N+1) hS hB
            (Nat.succ_pos N) hbranch ≤
          inducedRightGridSum R S A B (N+1) hS hB
            (Nat.succ_pos N) hbranch + q :=
      Q'.le_trans' _ _ _ hiGap
        (Q'.add_le_add_left _ _ _ hinducedMesh)
    have hsum := Q'.add_le_add hsGapQ hiGapQ
    have hregroup := Q'.regroup
      (scaledRightSum R S (N+1) hS (Nat.succ_pos N))
      (inducedRightGridSum R S A B (N+1) hS hB
        (Nat.succ_pos N) hbranch) q
    have hcross := joinedRight_le_targetLeft
      R S A B T U N N n hS hB hU hbranch htarget
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ (q+q) hcross)
          (Q'.le_of_eqv
            (Q'.add_eqv_congr_left
              (scaledLeftSum T U (n+1) hU (Nat.succ_pos n))
              (q+q) epsilon (ExpNeg.two_halves epsilon)))))
  · have htGap := scaledLeftSum_le_right_add_mesh
      T U (n+1) hU (Nat.succ_pos n)
    have hcross := targetRight_le_joinedLeft
      R S A B T U N N n hS hB hU hbranch htarget
    exact Q'.le_trans' _ _ _ htGap
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left _ _ _ htargetMesh)
        (Q'.add_le_add_right _ _ epsilon hcross))

/-- **Constructive rational atan addition.**  If the Mobius image mesh has a
vanishing exact-rational bound and its endpoint is `T/U`, then the sum of the
two rational atan integrals equals the target integral as a constructive real.
-/
theorem rationalAtan_add_eqv_of_gap_vanishes
    (R S A B T U : Nat)
    (hS : 0 < S) (hB : 0 < B) (hU : 0 < U)
    (hbranch : R*A < S*B)
    (htarget : (tanAdd (rat R S hS) (rat A B hB)
      (endpointReserve_pos R S A B hS hB hbranch)).eqv (rat T U hU))
    (hgap : ∀ epsilon : Q', (0 : Q') < epsilon →
      ∃ Nstage : Nat, ∀ N : Nat, Nstage ≤ N →
        inducedMeshBound R S A B (N+1) hS hB (Nat.succ_pos N) hbranch * 2 ≤
          epsilon) :
    CReal.Equiv
      (CReal.add (rationalAtanIntegral R S hS)
        (rationalAtanIntegral A B hB))
      (rationalAtanIntegral T U hU) := by
  have hsource := rationalAtanSeq_converges R S hS
  have hinduced := inducedLeftSeq_converges_of_gap_vanishes
    R S A B hS hB hbranch hgap
  have hsum :
      CReal.ConvergesTo (joinedLeftSeq R S A B hS hB hbranch)
        (CReal.add (rationalAtanIntegral R S hS)
          (rationalAtanIntegral A B hB)) :=
    TrigAddCReal.convergesTo_add hsource hinduced
  have htargetConv := joinedLeftSeq_converges_to_target
    R S A B T U hS hB hU hbranch htarget hgap
  exact CReal.Equiv_of_limit_of_equal
    (fun N => creal_equiv_refl (joinedLeftSeq R S A B hS hB hbranch N))
    hsum htargetConv

/-- First exact Machin-path addition:
`I(1/239) + I(117/598) = I(1/5)`. -/
theorem first_path_rationalAtan_add :
    CReal.Equiv
      (CReal.add (rationalAtanIntegral 1 239 (by decide))
        (rationalAtanIntegral 117 598 (by decide)))
      (rationalAtanIntegral 1 5 (by decide)) := by
  apply rationalAtan_add_eqv_of_gap_vanishes
  · simpa [twoThirtyNinth, slopeOne, fifth] using
      tanAdd_twoThirtyNinth_slopeOne_eqv_fifth
  · exact inducedGap_vanishes_of_mesh_le_invNat
      1 239 117 598 (by decide) (by decide) (by decide)
      (fun n hn => first_inducedMesh_le_invNat n hn)

/-- Second exact Machin-path addition. -/
theorem second_path_rationalAtan_add :
    CReal.Equiv
      (CReal.add (rationalAtanIntegral 117 598 (by decide))
        (rationalAtanIntegral 1 5 (by decide)))
      (rationalAtanIntegral 1183 2873 (by decide)) := by
  apply rationalAtan_add_eqv_of_gap_vanishes
  · simpa [slopeOne, fifth, slopeTwo] using
      tanAdd_slopeOne_fifth_eqv_slopeTwo
  · exact inducedGap_vanishes_of_mesh_le_invNat
      117 598 1 5 (by decide) (by decide) (by decide)
      (fun n hn => second_inducedMesh_le_invNat n hn)

/-- Third exact Machin-path addition. -/
theorem third_path_rationalAtan_add :
    CReal.Equiv
      (CReal.add (rationalAtanIntegral 1183 2873 (by decide))
        (rationalAtanIntegral 1 5 (by decide)))
      (rationalAtanIntegral 4394 6591 (by decide)) := by
  apply rationalAtan_add_eqv_of_gap_vanishes
  · simpa [slopeTwo, fifth, slopeThree] using
      tanAdd_slopeTwo_fifth_eqv_slopeThree
  · exact inducedGap_vanishes_of_mesh_le_invNat
      1183 2873 1 5 (by decide) (by decide) (by decide)
      (fun n hn => third_inducedMesh_le_invNat n hn)

/-- Final exact Machin-path addition, reaching the unit endpoint. -/
theorem fourth_path_rationalAtan_add :
    CReal.Equiv
      (CReal.add (rationalAtanIntegral 4394 6591 (by decide))
        (rationalAtanIntegral 1 5 (by decide)))
      (rationalAtanIntegral 1 1 (by decide)) := by
  apply rationalAtan_add_eqv_of_gap_vanishes
  · simpa [slopeThree, fifth] using
      tanAdd_slopeThree_fifth_eqv_one
  · exact inducedGap_vanishes_of_mesh_le_invNat
      4394 6591 1 5 (by decide) (by decide) (by decide)
      (fun n hn => fourth_inducedMesh_le_invNat n hn)

private theorem q_machin_reassociate (p x f : Q') :
    (p + (((x + f) + f) + f)).eqv ((((p + x) + f) + f) + f) := by
  ring_qeqv

private theorem c_machin_reassociate (P X F : CReal) :
    CReal.Equiv
      (CReal.add P
        (CReal.add (CReal.add (CReal.add X F) F) F))
      (CReal.add
        (CReal.add (CReal.add (CReal.add P X) F) F) F) :=
  TrigAdd.equiv_of_approx_eqv
    (fun n => q_machin_reassociate (P.approx n) (X.approx n) (F.approx n))

/-- Composition of the four branch-safe additions.  This is the exact endpoint
form of Machin's relation before the two reciprocal endpoint integrals are
identified with their paired series. -/
theorem machin_endpoint_relation :
    CReal.Equiv
      (CReal.add
        (rationalAtanIntegral 1 239 (by decide))
        (rationalAtanIntegral 1 1 (by decide)))
      (CReal.add
        (CReal.add
          (CReal.add
            (rationalAtanIntegral 1 5 (by decide))
            (rationalAtanIntegral 1 5 (by decide)))
          (rationalAtanIntegral 1 5 (by decide)))
        (rationalAtanIntegral 1 5 (by decide))) := by
  let P := rationalAtanIntegral 1 239 (by decide)
  let X := rationalAtanIntegral 117 598 (by decide)
  let F := rationalAtanIntegral 1 5 (by decide)
  let Y := rationalAtanIntegral 1183 2873 (by decide)
  let Z := rationalAtanIntegral 4394 6591 (by decide)
  let O := rationalAtanIntegral 1 1 (by decide)
  change CReal.Equiv (CReal.add P O)
    (CReal.add (CReal.add (CReal.add F F) F) F)
  have h1 : CReal.Equiv (CReal.add P X) F := first_path_rationalAtan_add
  have h2 : CReal.Equiv (CReal.add X F) Y := second_path_rationalAtan_add
  have h3 : CReal.Equiv (CReal.add Y F) Z := third_path_rationalAtan_add
  have h4 : CReal.Equiv (CReal.add Z F) O := fourth_path_rationalAtan_add
  have hlong :
      CReal.Equiv
        (CReal.add (CReal.add (CReal.add X F) F) F) O :=
    (CReal.add_congr_left (CReal.add_congr_left h2)).trans
      ((CReal.add_congr_left h3).trans h4)
  have hreplace :
      CReal.Equiv
        (CReal.add (CReal.add (CReal.add (CReal.add P X) F) F) F)
        (CReal.add (CReal.add (CReal.add F F) F) F) :=
    CReal.add_congr_left
      (CReal.add_congr_left (CReal.add_congr_left h1))
  exact (CReal.add_congr_right hlong.symm).trans
    ((c_machin_reassociate P X F).trans hreplace)

/-- The same endpoint relation with the unit endpoint replaced by the original
unit Darboux integral. -/
theorem machin_integral_relation :
    CReal.Equiv
      (CReal.add
        (rationalAtanIntegral 1 239 (by decide)) atanIntegral)
      (CReal.add
        (CReal.add
          (CReal.add
            (rationalAtanIntegral 1 5 (by decide))
            (rationalAtanIntegral 1 5 (by decide)))
          (rationalAtanIntegral 1 5 (by decide)))
        (rationalAtanIntegral 1 5 (by decide))) := by
  have hunit := CReal.add_congr_right
    (x := rationalAtanIntegral 1 239 (by decide))
    rationalAtanIntegral_one_one_eqv
  exact hunit.symm.trans machin_endpoint_relation

private theorem doubled_series_halfPi_relation :
    CReal.Equiv
      (CReal.add
        (CReal.mul (CReal.ofQ' (2 : Q')) Constructive.Pi.at239)
        Constructive.Pi.halfPi)
      (CReal.add
        (CReal.add
          (CReal.add
            (CReal.mul (CReal.ofQ' (2 : Q')) Constructive.Pi.at5)
            (CReal.mul (CReal.ofQ' (2 : Q')) Constructive.Pi.at5))
          (CReal.mul (CReal.ofQ' (2 : Q')) Constructive.Pi.at5))
        (CReal.mul (CReal.ofQ' (2 : Q')) Constructive.Pi.at5)) := by
  apply TrigAdd.equiv_of_approx_eqv
  intro n
  change
    ((2 : Q') * Constructive.Pi.at239.approx n +
      Constructive.Pi.halfPi.approx n).eqv
      ((((2 : Q') * Constructive.Pi.at5.approx n +
          (2 : Q') * Constructive.Pi.at5.approx n) +
        (2 : Q') * Constructive.Pi.at5.approx n) +
        (2 : Q') * Constructive.Pi.at5.approx n)
  rw [Constructive.Pi.halfPi_approx, Constructive.Pi.pi_approx]
  ring_qeqv

/-- The Machin definition itself gives the same four-endpoint relation with
`halfPi` on the left. -/
theorem machin_halfPi_relation :
    CReal.Equiv
      (CReal.add
        (rationalAtanIntegral 1 239 (by decide)) Constructive.Pi.halfPi)
      (CReal.add
        (CReal.add
          (CReal.add
            (rationalAtanIntegral 1 5 (by decide))
            (rationalAtanIntegral 1 5 (by decide)))
          (rationalAtanIntegral 1 5 (by decide)))
        (rationalAtanIntegral 1 5 (by decide))) := by
  have hP := rationalAtanIntegral_one_239_eq_two_at239
  have hF := rationalAtanIntegral_one_five_eq_two_at5
  have hFF := cadd_congr hF hF
  have hFFF := cadd_congr hFF hF
  have hFFFF := cadd_congr hFFF hF
  exact (CReal.add_congr_left hP).trans
    (doubled_series_halfPi_relation.trans hFFFF.symm)

/-- **The branch-controlled Machin value theorem.**  The constructive Darboux
integral of `2/(1+x^2)` on `[0,1]` is exactly the project's Machin `pi/2`.
This closes the value residual explicitly left open by
`SemicircleAtanDarboux`. -/
theorem atanIntegral_eq_halfPi :
    CReal.Equiv atanIntegral Constructive.Pi.halfPi :=
  addLeftCancel (machin_integral_relation.trans machin_halfPi_relation.symm)

private theorem chain2gen {q epsilon : Q'} (htwo : (q + q).eqv epsilon)
    {u v w : Q'} (huv : u ≤ v + q) (hvw : v ≤ w + q) :
    u ≤ w + epsilon := by
  have h1 : u ≤ (w + q) + q :=
    Q'.le_trans' _ _ _ huv (Q'.add_le_add_right _ _ q hvw)
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv w q q))
      (Q'.le_of_eqv (Q'.add_eqv_congr_left w _ _ htwo)))

/-- Transport a constructive-real sequence limit along an `Equiv` of limits. -/
theorem convergesTo_of_equiv {s : Nat → CReal} {L L' : CReal}
    (hconv : CReal.ConvergesTo s L) (hLL' : CReal.Equiv L L') :
    CReal.ConvergesTo s L' := by
  intro epsilon hepsilon
  let q : Q' := half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  have htwo : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  obtain ⟨Nstage, hstage⟩ := hconv q hq
  obtain ⟨Nequiv, hequiv⟩ := hLL' q hq
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napx, happ⟩ := hstage N hN
  refine ⟨max Napx Nequiv, fun n hn => ?_⟩
  have hnA : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnE : Nequiv ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hs1, hs2⟩ := happ n hnA
  obtain ⟨he1, he2⟩ := hequiv n hnE
  exact ⟨chain2gen htwo hs1 he1, chain2gen htwo he2 hs2⟩

/-- The original unit arctangent Riemann sequence now converges to Machin
`pi/2`, not merely to an abstract Cauchy real. -/
theorem atanRiemannSeq_converges_halfPi :
    CReal.ConvergesTo
      SemicircleRationalPolygon.atanRiemannSeq Constructive.Pi.halfPi :=
  convergesTo_of_equiv atanRiemannSeq_converges atanIntegral_eq_halfPi

/-- The rational inscribed-polygon sequence also converges to Machin `pi/2`.
The remaining semicircle task is to compare this sequence with `seqSemi`. -/
theorem polygonSeq_converges_halfPi :
    CReal.ConvergesTo
      SemicircleRationalPolygon.polygonSeq Constructive.Pi.halfPi :=
  convergesTo_of_equiv polygonSeq_converges atanIntegral_eq_halfPi

end YMGap.Continuum.SemicircleAtanAddition

#print axioms YMGap.Continuum.SemicircleAtanAddition.joinedLeftSeq_converges_to_target
#print axioms YMGap.Continuum.SemicircleAtanAddition.rationalAtan_add_eqv_of_gap_vanishes
#print axioms YMGap.Continuum.SemicircleAtanAddition.inducedGap_vanishes_of_mesh_le_invNat
#print axioms YMGap.Continuum.SemicircleAtanAddition.first_path_rationalAtan_add
#print axioms YMGap.Continuum.SemicircleAtanAddition.second_path_rationalAtan_add
#print axioms YMGap.Continuum.SemicircleAtanAddition.third_path_rationalAtan_add
#print axioms YMGap.Continuum.SemicircleAtanAddition.fourth_path_rationalAtan_add
#print axioms YMGap.Continuum.SemicircleAtanAddition.machin_endpoint_relation
#print axioms YMGap.Continuum.SemicircleAtanAddition.machin_integral_relation
#print axioms YMGap.Continuum.SemicircleAtanAddition.machin_halfPi_relation
#print axioms YMGap.Continuum.SemicircleAtanAddition.atanIntegral_eq_halfPi
#print axioms YMGap.Continuum.SemicircleAtanAddition.convergesTo_of_equiv
#print axioms YMGap.Continuum.SemicircleAtanAddition.atanRiemannSeq_converges_halfPi
#print axioms YMGap.Continuum.SemicircleAtanAddition.polygonSeq_converges_halfPi
