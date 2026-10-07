/-
# Torus RP (d9h): support of Wilson plaquette factors

* `sup_chiPow`, `sup_wilsonPoly`: `Sup a` passes from `x` to `χ₁^k(x)` and to `wilsonPoly x c K`.
* `sup_TK`: if all four link blocks of `p` are `< a`, then `Sup a (T_K p)`; `sup_prodTK` for products.
This discharges `hWp` once the `pos` plaquettes have their links in `P`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayoutMaster
import YMGap.Continuum.SU2TorusRPCrossCoord

namespace YMGap.Continuum.SU2TorusRPSupTK

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul sup_one)
open YMGap.Continuum.SU2TorusRPCompOn (sup_add sup_smul)
open YMGap.Continuum.SU2TorusRPCrossCoord (supQ_cv supQ_mul supQ_conj)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly chiPow)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx)

theorem sup_chiPow {a : Nat} {x : RatPoly} (hx : Sup a x) : ∀ k, Sup a (chiPow x k)
  | 0 => sup_one a
  | k + 1 => by
    show Sup a (polyMul (characterPolynomial x 1) (chiPow x k))
    exact sup_mul (show Sup a (polySmul 2 x) from sup_smul 2 hx) (sup_chiPow hx k)

theorem sup_wilsonPoly {a : Nat} {x : RatPoly} (hx : Sup a x) (c : Nat → Q') : ∀ K, Sup a (wilsonPoly x c K)
  | 0 => sup_smul _ (sup_chiPow hx 0)
  | K + 1 => sup_add (sup_wilsonPoly hx c K) (sup_smul _ (sup_chiPow hx _))

theorem sup_TK {a : Nat} (links : List Z4Link) (N : Nat) (β : Q') (K : Nat) (p : Z4Plaq)
    (hp : ∀ b ∈ plaqIdx links N p, b < a) :
    Sup a (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K p) := by
  unfold YMGap.Continuum.SU2WilsonPolymerIdentity.TK YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord
    YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.linkVar
  refine sup_wilsonPoly ?_ _ K
  exact (supQ_mul (supQ_mul (supQ_cv (hp _ (List.mem_cons_self ..)))
      (supQ_cv (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    (supQ_mul (supQ_conj (supQ_cv (hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
      (supQ_conj (supQ_cv (hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))).1

theorem sup_prodTK {a : Nat} (links : List Z4Link) (N : Nat) (β : Q') (K : Nat) :
    ∀ ps : List Z4Plaq, (∀ p ∈ ps, ∀ b ∈ plaqIdx links N p, b < a) →
      Sup a (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)
  | [], _ => sup_one a
  | p :: ps, h => sup_mul (sup_TK links N β K p (h p (List.mem_cons_self ..)))
      (sup_prodTK links N β K ps fun q hq => h q (List.mem_cons_of_mem _ hq))

end YMGap.Continuum.SU2TorusRPSupTK

#print axioms YMGap.Continuum.SU2TorusRPSupTK.sup_wilsonPoly
#print axioms YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK
