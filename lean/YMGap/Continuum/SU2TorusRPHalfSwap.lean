/-
# Torus RP (d7b): the half-swap Θ on the split carrier is Θ-like

`halfSwap a`: the block involution `k ↔ k + a` on `a + a` blocks. `thetaH a Tb := sign(conjSel Tb) ∘ reindex
(halfSwap a)` is exactly the `Θ` of `torus_rp_master`. `thetaH_like`: it is `ThetaLike` for the links `ℓ` with
`idx ℓ < a`, `idx (Θℓ) = idx ℓ + a` and `Tb (idx ℓ + a) = isT ℓ.2`. Hence (with `thetaL_prod`)
`thetaH (Π_pos T_K) ≈PE Π_{mir pos} T_K` on the split carrier.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPThetaAbs

namespace YMGap.Continuum.SU2TorusRPHalfSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub qpe_trans)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPThetaAbs (ThetaLike)

def hsMap (a k : Nat) : Nat := if k < a then k + a else if k < a + a then k - a else k

def halfSwap (a : Nat) : QuaternionBlockInvolution (a + a) where
  map := hsMap a
  map_lt k hk := by
    unfold hsMap
    by_cases h : k < a
    · rw [if_pos h]; omega
    · rw [if_neg h, if_pos hk]; omega
  involutive k hk := by
    unfold hsMap
    by_cases h : k < a
    · rw [if_pos h, if_neg (by omega), if_pos (by omega)]; omega
    · rw [if_neg h, if_pos hk, if_pos (by omega)]; omega

theorem halfSwap_low (a k : Nat) (hk : k < a) : (halfSwap a).map k = k + a := by
  show hsMap a k = _; unfold hsMap; rw [if_pos hk]

def thetaH (a : Nat) (Tb : Nat → Bool) (X : RatPoly) : RatPoly :=
  signSelectedPolynomial (4 * (a + a)) (conjSel Tb) (reindexQuaternionPolynomial (halfSwap a) X)

theorem thetaH_ring (a : Nat) (Tb : Nat → Bool) : RingSub (a + a) (thetaH a Tb) :=
  YMGap.Continuum.SU2TorusRPConj.ringSub_comp (S := signSelectedPolynomial (4 * (a + a)) (conjSel Tb))
    (R := reindexQuaternionPolynomial (halfSwap a)) (YMGap.Continuum.SU2TorusRPConj.conj_ringSub _ _ _)
    (YMGap.Continuum.SU2TorusRPConjCongr.conj_peCongr _ _ _) (YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub _)

theorem thetaH_coord (a : Nat) (Tb : Nat → Bool) (b : Nat) (hb : b < a) :
    QPE (a + a) (qsub (thetaH a Tb) (PolyQuaternion.coordinateVariable b))
      (if Tb (b + a) then PolyQuaternion.conj (PolyQuaternion.coordinateVariable (b + a))
        else PolyQuaternion.coordinateVariable (b + a)) := by
  have hr := YMGap.Continuum.SU2TorusRPReindex.reindex_coord (halfSwap a) b (by omega)
  rw [halfSwap_low a b hb] at hr
  have hc : ∀ {X Y : RatPoly}, PE (a + a) X Y →
      PE (a + a) (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) X) (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) Y) :=
    fun h => YMGap.Continuum.SU2TorusRPConjCongr.conj_peCongr (a + a) (4 * (a + a)) (conjSel Tb) h
  have hcoord := YMGap.Continuum.SU2TorusRPThetaConj.conj_coord (a + a) Tb (b + a) (by omega)
  refine qpe_trans (r := qsub (signSelectedPolynomial (4 * (a + a)) (conjSel Tb)) (PolyQuaternion.coordinateVariable (b + a)))
    ⟨hc hr.s, hc hr.i, hc hr.j, hc hr.k⟩ ?_
  rw [hcoord]
  exact YMGap.Continuum.SU2TorusRPCrossC.qpe_refl _ _

/-- Admissible positive links for the half-swap Θ. -/
def HD (a : Nat) (Tb : Nat → Bool) (links : List Z4Link) (M : Nat) (ℓ : Z4Link) : Prop :=
  links.idxOf ℓ < a ∧ links.idxOf (reflLink M ℓ) = links.idxOf ℓ + a ∧ Tb (links.idxOf ℓ + a) = isT ℓ.2

theorem thetaH_like (a : Nat) (Tb : Nat → Bool) (links : List Z4Link) (M : Nat) :
    ThetaLike (a + a) (thetaH a Tb) links M (HD a Tb links M) where
  ring := thetaH_ring a Tb
  spatial ℓ h hs := by
    have hc := thetaH_coord a Tb _ h.1
    rw [h.2.2, hs, if_neg (by decide)] at hc
    unfold linkVar; rw [h.2.1]; exact hc
  temporal v h := by
    have hc := thetaH_coord a Tb _ h.1
    rw [h.2.2, show isT (v, Dir4.x0).2 = true from rfl, if_pos rfl] at hc
    unfold linkVar; rw [h.2.1]; exact hc

end YMGap.Continuum.SU2TorusRPHalfSwap

#print axioms YMGap.Continuum.SU2TorusRPHalfSwap.thetaH_like
