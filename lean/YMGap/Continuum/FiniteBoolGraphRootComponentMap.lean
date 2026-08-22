/-
# Root-component transport along finite Boolean graph maps

A root-preserving map of finite Boolean graphs sends every vertex connected
to the source root into the component of the target root, provided it maps
source vertices to target vertices and preserves true adjacency.  The proof
recurses over the explicit `ChainIn` witness carried by the constructive
component compiler.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteBoolGraphRootComponent

namespace YMGap.Continuum.FiniteBoolGraphRootComponentMap

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent

/-- The exact data needed to map one rooted finite Boolean graph into
another.  Injectivity is deliberately not required for component inclusion. -/
structure RootedFiniteBoolGraphHom
    {Source Target : Type}
    [DecidableEq Source] [DecidableEq Target]
    (sourceAdj : Source → Source → Bool)
    (sourceVertices : List Source) (sourceRoot : Source)
    (targetAdj : Target → Target → Bool)
    (targetVertices : List Target) (targetRoot : Target) : Type where
  toFun : Source → Target
  map_root : toFun sourceRoot = targetRoot
  map_vertex : ∀ source,
    source ∈ sourceVertices → toFun source ∈ targetVertices
  map_edge : ∀ source next,
    source ∈ sourceVertices → next ∈ sourceVertices →
      sourceAdj source next = true →
        targetAdj (toFun source) (toFun next) = true

namespace RootedFiniteBoolGraphHom

variable
    {Source Target : Type}
    [DecidableEq Source] [DecidableEq Target]
    {sourceAdj : Source → Source → Bool}
    {sourceVertices : List Source} {sourceRoot : Source}
    {targetAdj : Target → Target → Bool}
    {targetVertices : List Target} {targetRoot : Target}

/-- Recursion over a source-component chain.  If the mapped initial point is
already in the target root component, edge preservation keeps every
successive mapped point there. -/
def mapChainEnd_mem_targetRootComponent
    (hom : RootedFiniteBoolGraphHom
      sourceAdj sourceVertices sourceRoot
      targetAdj targetVertices targetRoot)
    (htargetSym : SymmetricAdj targetAdj)
    (hsourceRoot : sourceRoot ∈ sourceVertices)
    (htargetRoot : targetRoot ∈ targetVertices) :
    ∀ {source target : Source},
      source ∈ sourceVertices →
      hom.toFun source ∈
        rootComponent targetAdj targetVertices targetRoot →
      ChainIn sourceAdj
        (rootComponent sourceAdj sourceVertices sourceRoot)
        source target →
      hom.toFun target ∈
        rootComponent targetAdj targetVertices targetRoot
  | _, _, _, hsourceMapped, ChainIn.refl _ => hsourceMapped
  | source, _, hsourceVertex, hsourceMapped,
      ChainIn.step (b := next) hedge hnextComponent rest => by
      have hnextVertex : next ∈ sourceVertices :=
        rootComponent_subset sourceAdj hsourceRoot hnextComponent
      have hnextMappedVertex : hom.toFun next ∈ targetVertices :=
        hom.map_vertex next hnextVertex
      have hmappedEdge :
          targetAdj (hom.toFun source) (hom.toFun next) = true :=
        hom.map_edge source next hsourceVertex hnextVertex hedge
      have hnextMappedComponent : hom.toFun next ∈
          rootComponent targetAdj targetVertices targetRoot :=
        rootComponent_closed_under_edge targetAdj htargetSym
          htargetRoot hsourceMapped hnextMappedVertex hmappedEdge
      exact mapChainEnd_mem_targetRootComponent hom htargetSym
        hsourceRoot htargetRoot hnextVertex hnextMappedComponent rest

/-- A rooted finite-graph homomorphism sends the complete source root
component into the target root component. -/
theorem map_mem_targetRootComponent
    (hom : RootedFiniteBoolGraphHom
      sourceAdj sourceVertices sourceRoot
      targetAdj targetVertices targetRoot)
    (hsourceSym : SymmetricAdj sourceAdj)
    (htargetSym : SymmetricAdj targetAdj)
    (hsourceRoot : sourceRoot ∈ sourceVertices)
    (htargetRoot : targetRoot ∈ targetVertices)
    {point : Source}
    (hpoint : point ∈
      rootComponent sourceAdj sourceVertices sourceRoot) :
    hom.toFun point ∈
      rootComponent targetAdj targetVertices targetRoot := by
  have hrootSourceComponent : sourceRoot ∈
      rootComponent sourceAdj sourceVertices sourceRoot :=
    root_mem_rootComponent sourceAdj hsourceRoot
  have hchain : ChainIn sourceAdj
      (rootComponent sourceAdj sourceVertices sourceRoot)
      sourceRoot point :=
    rootComponent_connected sourceAdj hsourceSym hsourceRoot
      sourceRoot point hrootSourceComponent hpoint
  have hrootTargetComponent : hom.toFun sourceRoot ∈
      rootComponent targetAdj targetVertices targetRoot := by
    rw [hom.map_root]
    exact root_mem_rootComponent targetAdj htargetRoot
  exact hom.mapChainEnd_mem_targetRootComponent htargetSym
    hsourceRoot htargetRoot hsourceRoot hrootTargetComponent hchain

end RootedFiniteBoolGraphHom

end YMGap.Continuum.FiniteBoolGraphRootComponentMap

#print axioms
  YMGap.Continuum.FiniteBoolGraphRootComponentMap.RootedFiniteBoolGraphHom.mapChainEnd_mem_targetRootComponent
#print axioms
  YMGap.Continuum.FiniteBoolGraphRootComponentMap.RootedFiniteBoolGraphHom.map_mem_targetRootComponent
