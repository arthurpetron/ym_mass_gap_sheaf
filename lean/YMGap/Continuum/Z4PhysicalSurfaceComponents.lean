/-
# Constructive link-connected components of finite-box Z4 face supports

The generic finite Boolean-graph component engine is specialized here to the
actual physical incidence relation of the finite Z4 packet graph.  Two
numerical plaquette identifiers are adjacent exactly when one of the box's
distinct physical links occurs in both incident-plaquette lists.

For every cutoff-one physical labelling, `surfaceComponents` therefore gives
an explicit finite family covering its excited plaquette identifiers.  The
family carries Type-level internal chains and is pairwise link-separated,
pairwise disjoint, and duplicate-free.
-/

import YMGap.Continuum.FiniteBoolGraphComponents

namespace YMGap.Continuum.Z4PhysicalSurfaceComponents

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

/-! ## 1. The exact finite-box face adjacency -/

def shareListedPhysicalLinkB (n left right : Nat) : List Z4Link → Bool
  | [] => false
  | link :: rest =>
      (decide (left ∈ incidentPlaqIds n link) &&
          decide (right ∈ incidentPlaqIds n link)) ||
        shareListedPhysicalLinkB n left right rest

theorem shareListedPhysicalLinkB_symm (n left right : Nat) :
    ∀ links,
      shareListedPhysicalLinkB n left right links =
        shareListedPhysicalLinkB n right left links
  | [] => rfl
  | link :: rest => by
      simp only [shareListedPhysicalLinkB]
      rw [shareListedPhysicalLinkB_symm n left right rest]
      cases decide (left ∈ incidentPlaqIds n link) <;>
        cases decide (right ∈ incidentPlaqIds n link) <;> rfl

theorem shareListedPhysicalLinkB_true_of_mem
    {n left right : Nat} {link : Z4Link} :
    ∀ {links : List Z4Link}, link ∈ links →
      left ∈ incidentPlaqIds n link →
      right ∈ incidentPlaqIds n link →
      shareListedPhysicalLinkB n left right links = true
  | [], hmem, _, _ => absurd hmem List.not_mem_nil
  | head :: rest, hmem, hleft, hright => by
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst head
        simp [shareListedPhysicalLinkB, hleft, hright]
      · have ih := shareListedPhysicalLinkB_true_of_mem hrest hleft hright
        simp [shareListedPhysicalLinkB, ih]

def faceLinkAdjacentB (n left right : Nat) : Bool :=
  shareListedPhysicalLinkB n left right (distinctBoxLinks n)

theorem faceLinkAdjacentB_symm (n left right : Nat) :
    faceLinkAdjacentB n left right = faceLinkAdjacentB n right left :=
  shareListedPhysicalLinkB_symm n left right (distinctBoxLinks n)

theorem faceLinkAdjacentB_symmetric (n : Nat) :
    SymmetricAdj (faceLinkAdjacentB n) :=
  faceLinkAdjacentB_symm n

theorem faceLinkAdjacentB_true_of_link
    {n left right : Nat} {link : Z4Link}
    (hlink : link ∈ distinctBoxLinks n)
    (hleft : left ∈ incidentPlaqIds n link)
    (hright : right ∈ incidentPlaqIds n link) :
    faceLinkAdjacentB n left right = true :=
  shareListedPhysicalLinkB_true_of_mem hlink hleft hright

private theorem enumerateFrom_snd_mem {α : Type} (start : Nat) :
    ∀ {xs : List α} {indexed : Nat × α},
      indexed ∈ enumerateFrom start xs → indexed.2 ∈ xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: rest, indexed, hmem => by
      simp only [enumerateFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem head
          (enumerateFrom_snd_mem (start + 1) hrest)

theorem enumerate_snd_mem {α : Type} {xs : List α}
    {indexed : Nat × α} (hmem : indexed ∈ enumerate xs) :
    indexed.2 ∈ xs :=
  enumerateFrom_snd_mem 0 hmem

/-! ## 2. The explicit component family -/

private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

theorem excitedPlaquetteIds_nodup (n : Nat) (physical : EdgeLabelling) :
    (excitedPlaquetteIds n physical).Nodup := by
  unfold excitedPlaquetteIds physicalFaceEdges
  exact List.filter_sublist.nodup (range_nodup (plaquetteEdgeCount n))

def surfaceComponents (n : Nat) (physical : EdgeLabelling) :
    List (List Nat) :=
  graphComponents (faceLinkAdjacentB n) (excitedPlaquetteIds n physical)

theorem surfaceComponents_cover (n : Nat) (physical : EdgeLabelling) :
    Covers (excitedPlaquetteIds n physical)
      (surfaceComponents n physical) :=
  graphComponents_covers (faceLinkAdjacentB n)
    (excitedPlaquetteIds n physical)

def surfaceComponents_allConnected (n : Nat) (physical : EdgeLabelling) :
    AllConnected (faceLinkAdjacentB n) (surfaceComponents n physical) :=
  graphComponents_allConnected (faceLinkAdjacentB n)
    (faceLinkAdjacentB_symmetric n) (excitedPlaquetteIds n physical)

theorem surfaceComponents_distinctSeparated
    (n : Nat) (physical : EdgeLabelling) :
    DistinctSeparated (faceLinkAdjacentB n)
      (surfaceComponents n physical) :=
  graphComponents_distinctSeparated (faceLinkAdjacentB n)
    (faceLinkAdjacentB_symmetric n) (excitedPlaquetteIds n physical)

theorem surfaceComponents_distinctDisjoint
    (n : Nat) (physical : EdgeLabelling) :
    DistinctDisjoint (surfaceComponents n physical) :=
  graphComponents_distinctDisjoint (faceLinkAdjacentB n)
    (excitedPlaquetteIds_nodup n physical)

theorem surfaceComponents_nodup (n : Nat) (physical : EdgeLabelling) :
    (surfaceComponents n physical).Nodup :=
  graphComponents_nodup (faceLinkAdjacentB n)
    (excitedPlaquetteIds_nodup n physical)

end YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponents.faceLinkAdjacentB_true_of_link
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponents.surfaceComponents_cover
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponents.surfaceComponents_allConnected
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponents.surfaceComponents_distinctSeparated
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponents.surfaceComponents_distinctDisjoint
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponents.surfaceComponents_nodup
