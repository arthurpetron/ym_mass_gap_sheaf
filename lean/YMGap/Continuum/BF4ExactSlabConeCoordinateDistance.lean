/-
# Coordinate separation for the original conditional-sweep cone

One Ward-star step changes each link-base coordinate by at most one.  Thus a
link reached after `R` cone expansions is at coordinate distance at most `R`
from an original support link.  The existing rooted probe carriers convert
this into an explicit root-distance obstruction to cone/test contact.

This is finite lattice geometry.  It supplies the separation premise of the
same-action covariance/sweep identity, but no contraction or decay estimate.
-/

import YMGap.Continuum.BF4ExactSlabEightLayerCone
import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
import YMGap.Continuum.BF4ExactSlabConditionalCovariance

namespace YMGap.Continuum.BF4ExactSlabConeCoordinateDistance

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe (fullData)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem face_link_coordinate (p : Z4Plaq) (link : Z4Link)
    (hlink : link ∈ edgesOf p) (m : Dir4) :
    natDist (cPlaq p m) (vComp link.1 m) ≤ 1 ∧
      natDist (vComp link.1 m) (cPlaq p m) ≤ 1 := by
  have h := edge_base_comp hlink m
  constructor <;> rcases h with h | h <;> simp only [natDist, h] <;> omega

/-- A literal Ward-star adjacency changes each link-base coordinate by at
most one, even when the two links have different directions. -/
theorem near_coordinate (extent : Nat) (i j : Z4Link)
    (hnear : Near extent i j) (m : Dir4) :
    natDist (vComp i.1 m) (vComp j.1 m) ≤ 1 := by
  rcases (near_iff extent i j).mp hnear with heq | ⟨id, _, hi, hj⟩
  · subst j
    rw [natDist_self]
    exact Nat.zero_le 1
  · have hpi := edge_base_comp hi m
    have hpj := edge_base_comp hj m
    rcases hpi with hpi | hpi <;> rcases hpj with hpj | hpj <;>
      simp only [natDist, hpi, hpj] <;> omega

/-- Every reached link has an ORIGINAL support link within `R` coordinate
steps.  The witness is used only to prove the subsequent separation bound. -/
theorem grow_coordinate (extent R : Nat) (support : List Z4Link) (j : Z4Link)
    (hj : j ∈ grow extent R support) :
    ∃ i : Z4Link, i ∈ support ∧
      ∀ m : Dir4, natDist (vComp i.1 m) (vComp j.1 m) ≤ R := by
  induction R generalizing support with
  | zero =>
      exact ⟨j, hj, fun _ => by rw [natDist_self]; exact Nat.le_refl 0⟩
  | succ R ih =>
      change j ∈ grow extent R (expand extent support) at hj
      obtain ⟨k, hk, hkj⟩ := ih (expand extent support) hj
      obtain ⟨i, hi, hik⟩ := (mem_expand extent support k).mp hk
      refine ⟨i, hi, fun m => ?_⟩
      have hstep := near_coordinate extent i k hik m
      have htail := hkj m
      have htriangle := natDist_triangle (vComp i.1 m) (vComp k.1 m) (vComp j.1 m)
      omega

/-- Cone contact forces a bounded distance between the ACTUAL rooted probe
carriers.  The two carrier-size terms account for their literal face animals;
no analytic estimate or replacement support is used. -/
theorem contact_root_bound {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right) (extent R : Nat)
    (j : Z4Link) (hj : j ∈ grow extent R left) (hjq : j ∈ right) :
    linfDist P.animal.root Q.animal.root ≤
      R + P.animal.support.length + Q.animal.support.length := by
  obtain ⟨i, hi, hij⟩ := grow_coordinate extent R left j hj
  obtain ⟨p, hp, hpi⟩ := List.mem_flatMap.mp (P.covers i hi)
  obtain ⟨q, hq, hqj⟩ := List.mem_flatMap.mp (Q.covers j hjq)
  have hrootP := rootedAnimal_linf_size_floor P.animal p hp
  have hrootQ := rootedAnimal_linf_size_floor Q.animal q hq
  have hcoord (m : Dir4) :
      natDist (cPlaq P.animal.root m) (cPlaq Q.animal.root m) ≤
        R + P.animal.support.length + Q.animal.support.length := by
    have ha := le_linfDist_comp P.animal.root p m
    have hb := (face_link_coordinate p i hpi m).1
    have hc := hij m
    have hd := (face_link_coordinate q j hqj m).2
    have he := le_linfDist_comp Q.animal.root q m
    have he' : natDist (cPlaq q m) (cPlaq Q.animal.root m) =
        natDist (cPlaq Q.animal.root m) (cPlaq q m) := by
      simp only [natDist]
      omega
    have h1 := natDist_triangle (cPlaq P.animal.root m) (cPlaq p m) (vComp i.1 m)
    have h2 := natDist_triangle (cPlaq P.animal.root m) (vComp i.1 m) (vComp j.1 m)
    have h3 := natDist_triangle (cPlaq P.animal.root m) (vComp j.1 m) (cPlaq q m)
    have h4 := natDist_triangle (cPlaq P.animal.root m) (cPlaq q m) (cPlaq Q.animal.root m)
    omega
  exact linfDist_le P.animal.root Q.animal.root _
    (hcoord .x0) (hcoord .x1) (hcoord .x2) (hcoord .x3)

/-- A root separation exceeding the explicit eight-layer cone radius plus
the two literal carrier sizes keeps the cone disjoint from the test support.
This is exactly the geometric premise of the checked covariance/sweep pin. -/
theorem grow_disjoint_of_root_far {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right) (extent rounds : Nat)
    (hfar : 8 * rounds + P.animal.support.length + Q.animal.support.length <
      linfDist P.animal.root Q.animal.root) :
    LinksDisjoint (grow extent (8 * rounds) left) right := by
  intro j hj hq
  have h := contact_root_bound P Q extent (8 * rounds) j hj hq
  omega

section Covariance

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage rounds : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

/-- The actual finite normalized covariance equals its `rounds`-fold
conditional-sweep pairing whenever the literal rooted carriers have the
displayed coordinate separation.  This uses no spatial contraction. -/
theorem covariance_as_sweep_pairing_of_root_far {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right) (p q : (F).V)
    (hp : LinkLocal extent left p.val) (hq : LinkLocal extent right q.val)
    (hfar : 8 * rounds + P.animal.support.length + Q.animal.support.length <
      linfDist P.animal.root Q.animal.root) :
    Quotient.mk crealSetoid
      (ofQ' (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)) =
      RCscale (inversePartition hw0 hw1 extent stage)
        ((F).cinnerCompl
          (runLayers hw0 hw1 K extent hK (cycles rounds)
            (embedV F (centered hw0 hw1 extent stage p)))
          (embedV F (centered hw0 hw1 extent stage q))) :=
  covariance_as_sweep_pairing hw0 hw1 extent stage rounds left right p q hp hq
    (grow_disjoint_of_root_far P Q extent rounds hfar)

end Covariance

#print axioms near_coordinate
#print axioms grow_coordinate
#print axioms contact_root_bound
#print axioms grow_disjoint_of_root_far
#print axioms covariance_as_sweep_pairing_of_root_far

end YMGap.Continuum.BF4ExactSlabConeCoordinateDistance
