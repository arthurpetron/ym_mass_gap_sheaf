/-
# Torus RP (d9x): single-involution relabelling carrying an observable

`relabel_haarX`: under the hypotheses of `relabel_haar`, for any supported `X`,
`∫ X · Π T_K[L] = ∫ (reindex σ X) · Π T_K[L']`. Chaining it along `List.Perm` (composing the reindexings) and
matching Θ is not yet done.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPRelabel
import YMGap.Continuum.SU2TorusRPSupTK

namespace YMGap.Continuum.SU2TorusRPRelabelX

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx)
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul)

variable {n : Nat} (L L' : List Z4Link) (N : Nat) (β : Q') (K : Nat)

theorem relabel_haarX (σ : QuaternionBlockInvolution n) (ps : List Z4Plaq)
    (hlt : ∀ p ∈ ps, ∀ b ∈ plaqIdx L N p, b < n)
    (h : ∀ p ∈ ps, (plaqIdx L N p).map σ.map = plaqIdx L' N p) (X : RatPoly) (hX : Sup n X) :
    (quaternionHaar n (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L N β K) ps))).eqv
      (quaternionHaar n (polyMul (reindexQuaternionPolynomial σ X)
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L' N β K) ps))) :=
  YMGap.Continuum.SU2TorusRPCompOn.haar_step _
    (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaar_reindex σ _
      (sup_mul hX (YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK L N β K ps hlt)))
    (pe_trans n ((YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub σ).mul _ _)
      (YMGap.Continuum.SU2TorusRPSubst.pe_mul2 n (pe_refl n _)
        (YMGap.Continuum.SU2TorusRPRelabel.relabel_prod L L' N β K σ ps hlt h)))

end YMGap.Continuum.SU2TorusRPRelabelX

#print axioms YMGap.Continuum.SU2TorusRPRelabelX.relabel_haarX
