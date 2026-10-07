/-
# Torus RP (d9u): relabelling the link order by a block involution

If a block involution `σ` on `n` blocks sends each plaquette's link indices in `L` to those in `L'`
(`(plaqIdx L p).map σ.map = plaqIdx L' p`), then `reindex σ (Π_ps T_K[L])` is PE to `Π_ps T_K[L']`
(`relabel_prod`), hence `∫ Π T_K[L] = ∫ Π T_K[L']` (`relabel_haar`). This is the single-involution step
of the bridge from the `torusLinks` order to the RP layout order; chaining steps for a general
permutation is not yet done.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPReindex
import YMGap.Continuum.SU2TorusRPSplitTK
import YMGap.Continuum.SU2TorusRPCompOn

namespace YMGap.Continuum.SU2TorusRPRelabel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx imgTK subst_prod)
open YMGap.Continuum.SU2TorusRPCore (Sup)

variable {n : Nat} (L L' : List Z4Link) (N : Nat) (β : Q') (K : Nat)

theorem imgTK_eq (σ : QuaternionBlockInvolution n) (p : Z4Plaq)
    (h : (plaqIdx L N p).map σ.map = plaqIdx L' N p) :
    imgTK L N β K (fun b => PolyQuaternion.coordinateVariable (σ.map b)) p =
      YMGap.Continuum.SU2WilsonPolymerIdentity.TK L' N β K p := by
  unfold plaqIdx at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  unfold imgTK YMGap.Continuum.SU2TorusRPSplitTK.imgWord YMGap.Continuum.SU2WilsonPolymerIdentity.TK
    YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.linkVar
  simp only []
  rw [h1, h2, h3, h4]

theorem img_prod (σ : QuaternionBlockInvolution n) : ∀ ps : List Z4Plaq,
    (∀ p ∈ ps, (plaqIdx L N p).map σ.map = plaqIdx L' N p) →
    prodPoly (imgTK L N β K (fun b => PolyQuaternion.coordinateVariable (σ.map b))) ps =
      prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L' N β K) ps
  | [], _ => rfl
  | p :: ps, h => by
    show polyMul _ _ = polyMul _ _
    rw [imgTK_eq L L' N β K σ p (h p (List.mem_cons_self ..)),
      img_prod σ ps fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem relabel_prod (σ : QuaternionBlockInvolution n) (ps : List Z4Plaq)
    (hlt : ∀ p ∈ ps, ∀ b ∈ plaqIdx L N p, b < n)
    (h : ∀ p ∈ ps, (plaqIdx L N p).map σ.map = plaqIdx L' N p) :
    PE n (reindexQuaternionPolynomial σ (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L N β K) ps))
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L' N β K) ps) := by
  have := subst_prod L N β K (YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub σ)
    (fun b => PolyQuaternion.coordinateVariable (σ.map b))
    (fun b hb => YMGap.Continuum.SU2TorusRPReindex.reindex_coord σ b hb) ps hlt
  rw [img_prod L L' N β K σ ps h] at this
  exact this

theorem relabel_haar (σ : QuaternionBlockInvolution n) (ps : List Z4Plaq)
    (hlt : ∀ p ∈ ps, ∀ b ∈ plaqIdx L N p, b < n)
    (h : ∀ p ∈ ps, (plaqIdx L N p).map σ.map = plaqIdx L' N p)
    (hS : Sup n (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L N β K) ps)) :
    (quaternionHaar n (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L N β K) ps)).eqv
      (quaternionHaar n (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L' N β K) ps)) :=
  YMGap.Continuum.SU2TorusRPCompOn.haar_step _
    (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaar_reindex σ _ hS)
    (relabel_prod L L' N β K σ ps hlt h)

end YMGap.Continuum.SU2TorusRPRelabel

#print axioms YMGap.Continuum.SU2TorusRPRelabel.relabel_prod
#print axioms YMGap.Continuum.SU2TorusRPRelabel.relabel_haar
