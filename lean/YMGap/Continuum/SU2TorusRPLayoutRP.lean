/-
# Torus RP (d9n): reflection positivity on the layout, all analytic hypotheses discharged

`torus_rp_lay`: on `L = P ++ C ++ Θ P` (`a = |P| + |C|`, `N = 2M`), for every `F` supported on the first `|P|`
blocks,
  `0 ≤ ∫ (Θ_H F · F) · ∏_ps T_K`,
given only combinatorial/geometric data: `L` nodup, `C` nodup and nonempty, `C ⊇` in-box crossing links, `P ⊇` in-box
`pos` links, `P` in the box, `ps ~ pos ++ mir pos ++ cross` with `pos` in-box `pos` plaquettes, `cross` in-box
crossing plaquettes, `ps` in the box, `β ≥ 0`.

Still open: choosing `P, C, pos, cross` from the actual torus (`ps` = all torus plaquettes) and the bridge from the
torus integrand/observables to this layout form.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPChainFix

namespace YMGap.Continuum.SU2TorusRPLayoutRP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPCore (Sup)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPHalfSwap (halfSwap)

theorem torus_rp_lay {M : Nat} (hM : 1 ≤ M) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
    (hC : C.Nodup) (hCne : C ≠ [])
    (hCcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .cross → ℓ ∈ C)
    (hPcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .pos → ℓ ∈ P)
    (hPbox : ∀ x ∈ P, InBox (2 * M) x.1)
    {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ plaqSide M p = .pos)
    (hcross : ∀ q ∈ cross, InBox (2 * M) q.1 ∧ plaqSide M q = .cross)
    (hpsbox : ∀ p ∈ ps, InBox (2 * M) p.1)
    (F : RatPoly) (hF : Sup P.length F) :
    (0 : Q') ≤ quaternionHaar ((P.length + C.length) + (P.length + C.length))
      (polyMul (polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
          (conjSel (layT (P ++ C ++ P.map (reflLink M))))
          (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F)
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps)) := by
  have ha := YMGap.Continuum.SU2TorusRPLayoutMaster.a_pos P C hCne
  have hb : 0 < (P.length + C.length) + (P.length + C.length) - 1 := by
    cases C with
    | nil => exact absurd rfl hCne
    | cons c C => simp only [List.length_cons]; omega
  exact YMGap.Continuum.SU2TorusRPLayoutSup.torus_rp_layout'' hM P C hnd hC hCcov hPcov hPbox hβ K ps pos cross
    hperm hposP hcross hCne hpsbox hb F (YMGap.Continuum.SU2TorusRPLayoutSup.sup_mono (Nat.le_add_right _ _) hF)
    (YMGap.Continuum.SU2TorusRPChainFix.lay_fix M P C hnd ha hC hCne hb F hF)

end YMGap.Continuum.SU2TorusRPLayoutRP

#print axioms YMGap.Continuum.SU2TorusRPLayoutRP.torus_rp_lay
