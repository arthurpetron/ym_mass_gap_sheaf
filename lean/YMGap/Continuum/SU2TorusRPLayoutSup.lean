/-
# Torus RP (d9j): integrand support on the layout; `torus_rp_layout''`

* `sup_mono`, `sup_sign`: support is monotone in the block count and kept by `signSelectedPolynomial`.
* `hsup_lay`: `Sup (2a) (X · ∏_ps T_K)` for `X = Θ_H F · F`, `Sup a F`, `ps` in the box.
* `torus_rp_layout''`: `torus_rp_layout'` with `hsup` discharged. The only analytic hypothesis left is `hXfix`
  (the split chain fixes `X`), plus the choice of `P, C` and the integrand bridge.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPLayoutBounds
import YMGap.Continuum.SU2ReindexPECongr

namespace YMGap.Continuum.SU2TorusRPLayoutSup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side)
open YMGap.Continuum.SU2TorusRPLayoutChain (layChain)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPHalfSwap (halfSwap)
open YMGap.Continuum.SU2TorusRPLayoutMaster (a_pos)

theorem sup_mono {a b : Nat} (h : a ≤ b) {p : RatPoly} (hp : Sup a p) : Sup b p := fun s hs => by
  have := hp s hs; omega

theorem sup_sign {a : Nat} (N : Nat) (S : Nat → Bool) {p : RatPoly} (hp : Sup a p) :
    Sup a (signSelectedPolynomial N S p) := fun s hs => by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact hp t ht

variable {M : Nat} (hM : 1 ≤ M) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
  (hC : C.Nodup)
  (hCcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .cross → ℓ ∈ C)
  (hPcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .pos → ℓ ∈ P)
  (hPbox : ∀ x ∈ P, InBox (2 * M) x.1)

include hM hCcov hPcov in
theorem hsup_lay (β : Q') (K : Nat) (ps : List Z4Plaq) (hpsbox : ∀ p ∈ ps, InBox (2 * M) p.1)
    (F : RatPoly) (hF : Sup (P.length + C.length) F) :
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks
      ((P.length + C.length) + (P.length + C.length) - 1 + 1)
      (polyMul (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
        (conjSel (layT (P ++ C ++ P.map (reflLink M))))
        (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F)
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps)) := by
  refine sup_mul (sup_mul (sup_mono (by omega) (sup_sign _ _
    (YMGap.Continuum.SU2ReindexPECongr.sup_reindex (halfSwap (P.length + C.length)) F)))
    (sup_mono (by omega) hF)) ?_
  exact YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK _ _ β K ps fun p hp =>
    YMGap.Continuum.SU2TorusRPLayoutBounds.hps_lay hM P C hCcov hPcov p (hpsbox p hp)

include hM hC hCcov hPcov hPbox in
/-- `torus_rp_layout'` with `hsup` discharged: only `hXfix` remains. -/
theorem torus_rp_layout'' {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ plaqSide M p = .pos)
    (hcross : ∀ q ∈ cross, InBox (2 * M) q.1 ∧ plaqSide M q = .cross) (hCne : C ≠ [])
    (hpsbox : ∀ p ∈ ps, InBox (2 * M) p.1)
    (hb : 0 < (P.length + C.length) + (P.length + C.length) - 1)
    (F : RatPoly) (hF : Sup (P.length + C.length) F)
    (hXfix : PE ((P.length + C.length) + (P.length + C.length) - 1 + 1)
      (applySelectedTranslationSteps hb (layChain M P C hnd (a_pos P C hCne))
        (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
          (conjSel (layT (P ++ C ++ P.map (reflLink M))))
          (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F))
      (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
          (conjSel (layT (P ++ C ++ P.map (reflLink M))))
          (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F)) :
    (0 : Q') ≤ quaternionHaar ((P.length + C.length) + (P.length + C.length))
      (polyMul (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
          (conjSel (layT (P ++ C ++ P.map (reflLink M))))
          (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F)
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps)) :=
  YMGap.Continuum.SU2TorusRPLayoutBounds.torus_rp_layout' hM P C hnd hC hCcov hPcov hPbox hβ K ps pos cross hperm
    hposP hcross hCne hpsbox hb F hF _ rfl hXfix (hsup_lay hM P C hCcov hPcov β K ps hpsbox F hF)

end YMGap.Continuum.SU2TorusRPLayoutSup

#print axioms YMGap.Continuum.SU2TorusRPLayoutSup.hsup_lay
#print axioms YMGap.Continuum.SU2TorusRPLayoutSup.torus_rp_layout''
