/-
# Torus RP (d7c): factorisation of the split torus product on the split carrier

`split_factor`: if `ps ~ pos ++ mir pos ++ cross`, the split image leaves the `pos` and mirror plaquettes
unchanged, and the links of `pos` are half-swap admissible (`HD`), then on `a + a` blocks
  `Π_ps T_K[split] ≈PE (Π_pos T_K · thetaH (Π_pos T_K)) · Π_cross T_K[split]`,
which is exactly the `hfac` hypothesis of `torus_rp_master` (with `σ = halfSwap a`, `G = T_K[split]`).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPHalfSwap

namespace YMGap.Continuum.SU2TorusRPSplitFactor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_symm pe_refl pe_mulL pe_mulR)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPSplitTK (imgTK)
open YMGap.Continuum.SU2TorusRPHalfSwap (thetaH HD thetaH_like)

theorem prodPoly_eq_foldr (F : Z4Plaq → RatPoly) : ∀ cs : List Z4Plaq,
    prodPoly F cs = cs.foldr (fun c Y => polyMul (F c) Y) polyOne
  | [] => rfl
  | c :: cs => by
      show polyMul (F c) (prodPoly F cs) = polyMul (F c) (cs.foldr (fun c Y => polyMul (F c) Y) polyOne)
      rw [prodPoly_eq_foldr F cs]

theorem split_factor {M : Nat} (hM : 1 ≤ M) (a : Nat) (Tb : Nat → Bool) (links : List Z4Link) (β : Q') (K : Nat)
    (img : Nat → PolyQuaternion) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hpos : ∀ p ∈ pos, p.1.1 < 2 * M ∧ ∀ ℓ ∈ plaqLinks (2 * M) p, HD a Tb links M ℓ)
    (himg : ∀ q ∈ pos ++ pos.map (mir M),
      imgTK links (2 * M) β K img q = YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K q) :
    PE (a + a) (prodPoly (imgTK links (2 * M) β K img) ps)
      (polyMul (polyMul (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K) pos)
          (thetaH a Tb (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K) pos)))
        (prodPoly (imgTK links (2 * M) β K img) cross)) := by
  refine pe_trans _ (YMGap.Continuum.SU2TorusRPFactor.prod_perm _ _ hperm)
    (pe_trans _ (YMGap.Continuum.SU2TorusRPFactor.prod_append _ _ _ _) (pe_mulR _ _ ?_))
  have hc : PE (a + a) (prodPoly (imgTK links (2 * M) β K img) (pos ++ pos.map (mir M)))
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K) (pos ++ pos.map (mir M))) :=
    YMGap.Continuum.SU2TorusRPSplitTK.prod_congr _ fun q hq => by rw [himg q hq]; exact pe_refl _ _
  refine pe_trans _ hc (pe_trans _ (YMGap.Continuum.SU2TorusRPFactor.prod_append _ _ _ _) (pe_mulL _ _ ?_))
  exact pe_symm _ (YMGap.Continuum.SU2TorusRPThetaAbs.thetaL_prod hM (thetaH_like a Tb links M) β K pos hpos)

end YMGap.Continuum.SU2TorusRPSplitFactor

#print axioms YMGap.Continuum.SU2TorusRPSplitFactor.split_factor
#print axioms YMGap.Continuum.SU2TorusRPSplitFactor.prodPoly_eq_foldr
