/-
# Uniform mesh moduli for the four branch-safe Machin substitutions

The endpoint Mobius reserve is independent of the partition size.  This file
factors the induced mesh exactly as a fixed rational coefficient times `1/n`
and checks, in the four certified Machin cells, that the coefficient is at
most one.  Thus every transformed Darboux gap is bounded by `2/n`.
-/

import YMGap.Continuum.SemicircleAtanInducedGap

namespace YMGap.Continuum.SemicircleAtanMachinMesh

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanMachinPath
open YMGap.Continuum.SemicircleAtanRationalEndpoint
open YMGap.Continuum.SemicircleAtanMobiusKernel
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanTransformedSqueeze
open YMGap.Continuum.SemicircleAtanInducedGap

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : (((1 : Q').den : Int)) = 1 := rfl

def endpointReserve
    (R S A B : Nat) (hS : 0 < S) (hB : 0 < B) : Q' :=
  mobiusDen (rat R S hS) (rat A B hB)

theorem endpointReserve_pos
    (R S A B : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) :
    (0 : Q') < endpointReserve R S A B hS hB := by
  show (0 : Int) *
      ((endpointReserve R S A B hS hB).den : Int) <
    (endpointReserve R S A B hS hB).num * (1 : Int)
  unfold endpointReserve mobiusDen rat
  simp only [Q'.add_num_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.neg_den, neg_num_cast, one_num, one_den,
    Q'.mkPos_num, Q'.mkPos_den]
  simp only [Int.zero_mul, Int.mul_one, Int.one_mul]
  have hi : ((R*A : Nat) : Int) < ((S*B : Nat) : Int) := by
    exact_mod_cast hbranch
  omega

theorem gridReserve_eqv_endpoint
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n) :
    (gridReserve R S A B n hS hB hn).eqv
      (endpointReserve R S A B hS hB) := by
  unfold gridReserve endpointReserve mobiusDen
  refine Q'.add_eqv_congr_left 1 _ _ ?_
  refine Q'.neg_eqv_congr _ _ ?_
  exact Q'.mul_eqv_congr_left (rat R S hS) _ _
    (gridNode_endpoint_eqv A B n hB hn)

def invNat (n : Nat) (hn : 0 < n) : Q' := Q'.mkPos 1 n hn

theorem gridMesh_eqv_endpoint_mul_invNat
    (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    (gridMesh A B n hB hn).eqv (rat A B hB * invNat n hn) := by
  show (gridMesh A B n hB hn).num *
      ((rat A B hB * invNat n hn).den : Int) =
    (rat A B hB * invNat n hn).num *
      ((gridMesh A B n hB hn).den : Int)
  unfold gridMesh rat invNat
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  ac_rfl

private theorem divPos_eqv_divPos_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : (p*q').eqv (p'*q)) :
    (Q'.divPos p q hq).eqv (Q'.divPos p' q' hq') := by
  let c := Q'.divPos p' q' hq'
  have hright : ((c*q)*q').eqv (p'*q) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : (p*q').eqv ((c*q)*q') :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p.eqv (c*q) := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c*q) q'
  apply Q'.mul_left_cancel_of_pos hq
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q (Q'.divPos p q hq)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p q hq) ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.mul_comm_eqv c q

def inducedMeshCoefficient
    (R S A B : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) : Q' :=
  let r := rat R S hS
  let e := endpointReserve R S A B hS hB
  Q'.divPos (((1 : Q') + r*r) * rat A B hB) (e*e)
    (Q'.mul_pos (endpointReserve_pos R S A B hS hB hbranch)
      (endpointReserve_pos R S A B hS hB hbranch))

theorem inducedMeshBound_factor
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    (inducedMeshBound R S A B n hS hB hn hbranch).eqv
      (inducedMeshCoefficient R S A B hS hB hbranch * invNat n hn) := by
  let r := rat R S hS
  let C := (1 : Q') + r*r
  let g := gridReserve R S A B n hS hB hn
  let e := endpointReserve R S A B hS hB
  let mesh := gridMesh A B n hB hn
  let a := rat A B hB
  let u := invNat n hn
  have hg : (0 : Q') < g := gridReserve_pos R S A B n hS hB hn hbranch
  have he : (0 : Q') < e := endpointReserve_pos R S A B hS hB hbranch
  have hge : g.eqv e := gridReserve_eqv_endpoint R S A B n hS hB hn
  have hsq : (g*g).eqv (e*e) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right g e g hge) ?_
    exact Q'.mul_eqv_congr_left e g e hge
  have hden :
    (Q'.divPos (C*mesh) (g*g) (Q'.mul_pos hg hg)).eqv
        (Q'.divPos (C*mesh) (e*e) (Q'.mul_pos he he)) := by
    apply divPos_eqv_divPos_of_cross
    exact Q'.mul_eqv_congr_left (C*mesh) _ _ (Q'.eqv_symm hsq)
  have hmesh : mesh.eqv (a*u) :=
    gridMesh_eqv_endpoint_mul_invNat A B n hB hn
  have hnum : (C*mesh).eqv ((C*a)*u) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left C _ _ hmesh) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv C a u)
  have hnumDiv :
      (Q'.divPos (C*mesh) (e*e) (Q'.mul_pos he he)).eqv
        (Q'.divPos ((C*a)*u) (e*e) (Q'.mul_pos he he)) := by
    show ((C*mesh) * Q'.recipPos (e*e) (Q'.mul_pos he he)).eqv
      (((C*a)*u) * Q'.recipPos (e*e) (Q'.mul_pos he he))
    exact Q'.mul_eqv_congr_right _ _ _ hnum
  have hfactor :
      (Q'.divPos ((C*a)*u) (e*e) (Q'.mul_pos he he)).eqv
        (Q'.divPos (C*a) (e*e) (Q'.mul_pos he he) * u) := by
    show (((C*a)*u) * Q'.recipPos (e*e) (Q'.mul_pos he he)).eqv
      (((C*a) * Q'.recipPos (e*e) (Q'.mul_pos he he)) * u)
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (C*a) u _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (C*a) _ _ (Q'.mul_comm_eqv u _)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (C*a) _ u)
  unfold inducedMeshBound inducedMeshCoefficient
  exact Q'.eqv_trans _ _ _ hden (Q'.eqv_trans _ _ _ hnumDiv hfactor)

theorem first_mesh_coefficient_le_one :
    inducedMeshCoefficient 1 239 117 598 (by decide) (by decide) (by decide) ≤ 1 := by
  unfold inducedMeshCoefficient endpointReserve mobiusDen rat
  decide

theorem second_mesh_coefficient_le_one :
    inducedMeshCoefficient 117 598 1 5 (by decide) (by decide) (by decide) ≤ 1 := by
  unfold inducedMeshCoefficient endpointReserve mobiusDen rat
  decide

theorem third_mesh_coefficient_le_one :
    inducedMeshCoefficient 1183 2873 1 5 (by decide) (by decide) (by decide) ≤ 1 := by
  unfold inducedMeshCoefficient endpointReserve mobiusDen rat
  decide

theorem fourth_mesh_coefficient_le_one :
    inducedMeshCoefficient 4394 6591 1 5 (by decide) (by decide) (by decide) ≤ 1 := by
  unfold inducedMeshCoefficient endpointReserve mobiusDen rat
  decide

private theorem inducedMeshBound_le_invNat_of_coeff
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B)
    (hc : inducedMeshCoefficient R S A B hS hB hbranch ≤ 1) :
    inducedMeshBound R S A B n hS hB hn hbranch ≤ invNat n hn := by
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (invNat n hn) hc (by
    unfold invNat
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (inducedMeshBound_factor R S A B n hS hB hn hbranch))
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv (invNat n hn))))

theorem first_inducedMesh_le_invNat (n : Nat) (hn : 0 < n) :
    inducedMeshBound 1 239 117 598 n (by decide) (by decide) hn (by decide) ≤
      invNat n hn :=
  inducedMeshBound_le_invNat_of_coeff _ _ _ _ _ _ _ _ _
    first_mesh_coefficient_le_one

theorem second_inducedMesh_le_invNat (n : Nat) (hn : 0 < n) :
    inducedMeshBound 117 598 1 5 n (by decide) (by decide) hn (by decide) ≤
      invNat n hn :=
  inducedMeshBound_le_invNat_of_coeff _ _ _ _ _ _ _ _ _
    second_mesh_coefficient_le_one

theorem third_inducedMesh_le_invNat (n : Nat) (hn : 0 < n) :
    inducedMeshBound 1183 2873 1 5 n (by decide) (by decide) hn (by decide) ≤
      invNat n hn :=
  inducedMeshBound_le_invNat_of_coeff _ _ _ _ _ _ _ _ _
    third_mesh_coefficient_le_one

theorem fourth_inducedMesh_le_invNat (n : Nat) (hn : 0 < n) :
    inducedMeshBound 4394 6591 1 5 n (by decide) (by decide) hn (by decide) ≤
      invNat n hn :=
  inducedMeshBound_le_invNat_of_coeff _ _ _ _ _ _ _ _ _
    fourth_mesh_coefficient_le_one

private theorem inducedGap_le_two_invNat_of_mesh
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B)
    (hm : inducedMeshBound R S A B n hS hB hn hbranch ≤ invNat n hn) :
    inducedLeftGridSum R S A B n hS hB hn hbranch ≤
      inducedRightGridSum R S A B n hS hB hn hbranch + invNat n hn * 2 := by
  have hgap := inducedLeft_le_right_add_two_mesh
    R S A B n hS hB hn hbranch
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ 2 hm
    (by decide : (0 : Q') ≤ 2)
  exact Q'.le_trans' _ _ _ hgap (Q'.add_le_add_left _ _ _ hmul)

theorem first_inducedGap_le_two_invNat (n : Nat) (hn : 0 < n) :
    inducedLeftGridSum 1 239 117 598 n (by decide) (by decide) hn (by decide) ≤
      inducedRightGridSum 1 239 117 598 n (by decide) (by decide) hn (by decide) +
        invNat n hn * 2 :=
  inducedGap_le_two_invNat_of_mesh _ _ _ _ _ _ _ _ _
    (first_inducedMesh_le_invNat n hn)

theorem second_inducedGap_le_two_invNat (n : Nat) (hn : 0 < n) :
    inducedLeftGridSum 117 598 1 5 n (by decide) (by decide) hn (by decide) ≤
      inducedRightGridSum 117 598 1 5 n (by decide) (by decide) hn (by decide) +
        invNat n hn * 2 :=
  inducedGap_le_two_invNat_of_mesh _ _ _ _ _ _ _ _ _
    (second_inducedMesh_le_invNat n hn)

theorem third_inducedGap_le_two_invNat (n : Nat) (hn : 0 < n) :
    inducedLeftGridSum 1183 2873 1 5 n (by decide) (by decide) hn (by decide) ≤
      inducedRightGridSum 1183 2873 1 5 n (by decide) (by decide) hn (by decide) +
        invNat n hn * 2 :=
  inducedGap_le_two_invNat_of_mesh _ _ _ _ _ _ _ _ _
    (third_inducedMesh_le_invNat n hn)

theorem fourth_inducedGap_le_two_invNat (n : Nat) (hn : 0 < n) :
    inducedLeftGridSum 4394 6591 1 5 n (by decide) (by decide) hn (by decide) ≤
      inducedRightGridSum 4394 6591 1 5 n (by decide) (by decide) hn (by decide) +
        invNat n hn * 2 :=
  inducedGap_le_two_invNat_of_mesh _ _ _ _ _ _ _ _ _
    (fourth_inducedMesh_le_invNat n hn)

end YMGap.Continuum.SemicircleAtanMachinMesh

#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.gridReserve_eqv_endpoint
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.inducedMeshBound_factor
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.first_mesh_coefficient_le_one
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.second_mesh_coefficient_le_one
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.third_mesh_coefficient_le_one
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.fourth_mesh_coefficient_le_one
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.first_inducedMesh_le_invNat
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.second_inducedMesh_le_invNat
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.third_inducedMesh_le_invNat
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.fourth_inducedMesh_le_invNat
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.first_inducedGap_le_two_invNat
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.second_inducedGap_le_two_invNat
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.third_inducedGap_le_two_invNat
#print axioms YMGap.Continuum.SemicircleAtanMachinMesh.fourth_inducedGap_le_two_invNat
