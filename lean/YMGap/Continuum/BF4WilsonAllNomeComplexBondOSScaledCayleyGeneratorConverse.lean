/-
# Resolvent reconstruction of the original rational infinitesimal graph

The SAME original positive resolvent intertwines the actual Cayley group.
A supplied right-rational tangent therefore transports to the resolvent image.
That image is an original graph input; its checked tangent and physical
uniqueness pin its output. The unit graph inverse then computes the desired
maximal-domain witness. No adjoint-pairing limit, spectral theorem, representative
choice or new analytic premise is needed.

This is a right-rational infinitesimal-domain converse at fixed nome/width,
with the exact -2i phase. Full-real differentiability, physical clock/spacing,
nontrivial continuum survival and the Clay mass gap are not asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventLimit

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGeneratorConverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain Point input output ofPoint)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData
  (RightTangent rightQuotient slope ofPointTangent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation (pairResolvent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventTangent
  (onePos pairResolvent_add pairResolvent_realScale pairResolvent_imagScale
    pairResolvent_diff unitDomain unitDomain_input unitDomain_graph_sum)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventLimit
  (limitMap_pairResolvent_commute pairResolvent_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement (add_left_cancel)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "J" => pairResolvent hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1

theorem rightQuotient_pairResolvent (s t : Q') (hs : (0 : Q') < s)
    (ht : (0 : Q') < t) (u : H) :
    rightQuotient hw0 hw1 t ht (J s hs u) = J s hs (rightQuotient hw0 hw1 t ht u) := by
  unfold rightQuotient
  rw [limitMap_pairResolvent_commute,← pairResolvent_diff,← pairResolvent_realScale]

/-- The ORIGINAL contraction transports the supplied radius without loss. -/
def transportTangent (s : Q') (hs : (0 : Q') < s) (u v : H)
    (P : RightTangent hw0 hw1 u v) :
    RightTangent hw0 hw1 (J s hs u) (J s hs v) where
  radius := P.radius
  positive := P.positive
  bound := by
    intro e he t ht htr
    rw [rightQuotient_pairResolvent]
    change RCle
      (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
        (J s hs (rightQuotient hw0 hw1 t ht u))
        (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.imagScale hw0 hw1 (-2) (J s hs v))) _
    rw [← pairResolvent_imagScale]
    exact RCle_trans
      (pairResolvent_distance_bound hw0 hw1 s hs _ _) (P.bound e he t ht htr)

private theorem resolvent_output_point (u v : H) (P : RightTangent hw0 hw1 u v)
    (p : Point hw0 hw1 (width := width))
    (hp : In (ofPoint hw0 hw1 p) = J 1 onePos u) :
    J 1 onePos v = Out (ofPoint hw0 hw1 p) := by
  have PT := transportTangent hw0 hw1 1 onePos u v P
  rw [← hp] at PT
  exact RightTangent.unique hw0 hw1 PT (ofPointTangent hw0 hw1 p)

/-- Quotient induction occurs only in this equality proof. The represented
test radius is never selected as data from an arbitrary quotient class. -/
theorem resolvent_output (u v : H) (P : RightTangent hw0 hw1 u v)
    (d : D) (hd : In d = J 1 onePos u) : J 1 onePos v = Out d := by
  rcases d with ⟨a,b⟩
  revert hd
  refine Quotient.inductionOn₂ a b ?_
  intro p q hp
  exact resolvent_output_point hw0 hw1 u v P (p,q) hp

/-- The computational witness depends on u and v, not erased tangent rates. -/
def reconstructedDomain (u v : H) : D := unitDomain hw0 hw1 (A u v)

theorem reconstructedDomain_input (u v : H) (P : RightTangent hw0 hw1 u v) :
    In (reconstructedDomain hw0 hw1 u v) = u := by
  have ho := resolvent_output hw0 hw1 u v P (unitDomain hw0 hw1 u)
    (unitDomain_input hw0 hw1 u)
  have h := unitDomain_graph_sum hw0 hw1 u
  rw [unitDomain_input,← ho] at h
  unfold reconstructedDomain
  rw [unitDomain_input,pairResolvent_add]
  exact h

theorem reconstructedDomain_output (u v : H) (P : RightTangent hw0 hw1 u v) :
    Out (reconstructedDomain hw0 hw1 u v) = v := by
  apply add_left_cancel hw0 hw1 u
  have h := unitDomain_graph_sum hw0 hw1 (A u v)
  change A (In (reconstructedDomain hw0 hw1 u v))
    (Out (reconstructedDomain hw0 hw1 u v)) = A u v at h
  rwa [reconstructedDomain_input hw0 hw1 u v P] at h

/-- A supplied actual rational tangent reconstructs BOTH pins of an ORIGINAL
maximal physical-domain class, without an assumed domain or surrogate graph. -/
def ofRightTangent (u v : H) (P : RightTangent hw0 hw1 u v) :
    Σ' d : D, (In d = u) ×' (Out d = v) :=
  ⟨reconstructedDomain hw0 hw1 u v,reconstructedDomain_input hw0 hw1 u v P,
    reconstructedDomain_output hw0 hw1 u v P⟩

#print axioms rightQuotient_pairResolvent
#print axioms transportTangent
#print axioms resolvent_output
#print axioms reconstructedDomain
#print axioms reconstructedDomain_input
#print axioms reconstructedDomain_output
#print axioms ofRightTangent

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGeneratorConverse
