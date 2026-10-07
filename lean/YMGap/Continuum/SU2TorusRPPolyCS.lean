/-
# Torus RP (f0): RP and Cauchy–Schwarz for all `PtSup` polynomials (SU(2), truncated `T_K` weight, fixed `K`)

Proved: `torus_rp_poly : TorusRPPoly` and `torus_cs_poly : TorusCS`. Route: a `PtSup` polynomial `F` is
`PE`-equal to `eval (obsOf F)` (`obsOf_pe`), and `obsOf F` lies on `Pt M` (`obsOf_on`). `rpB` respects `PE` in both
arguments (`rpB_pe`, through `thetaT_pe`), so the `Obs` results `torus_rp` and `torus_cs_obs` carry over.
This is SU(2) only. J04 (all compact simple groups) remains OPEN.
-/

import YMGap.Continuum.SU2TorusRPObsOf

namespace YMGap.Continuum.SU2TorusRPPolyCS

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_symm pe_haar)
open YMGap.Continuum.SU2TorusRPSubst (pe_mul2)
open YMGap.Continuum.SU2TorusRPObs (eval)
open YMGap.Continuum.SU2TorusRPCore (Sup)
open YMGap.Continuum.SU2TorusRPCSShape (rpB PtSup TorusRPPoly TorusCS)
open YMGap.Continuum.SU2TorusRPObsOf (obsOf obsOf_pe obsOf_on)

variable {M : Nat} (hM : 1 ≤ M) (β : Q') (K : Nat)

theorem rpB_pe {F F' G G' : RatPoly} (hF : Sup (torusLinks (2 * M)).length F) (hF' : Sup (torusLinks (2 * M)).length F')
    (hFF : PE (torusLinks (2 * M)).length F F') (hGG : PE (torusLinks (2 * M)).length G G') :
    (rpB hM β K F G).eqv (rpB hM β K F' G') :=
  pe_haar _ (pe_mul2 _ (pe_mul2 _ (YMGap.Continuum.SU2TorusRPSym.thetaT_pe hM hF hF' hFF) hGG) (pe_refl _ _))

theorem ptSup_sup {F : RatPoly} (h : PtSup (M := M) F) : Sup (torusLinks (2 * M)).length F :=
  fun t ht => (h t ht).1

theorem obsOf_pe' {F : RatPoly} (h : PtSup (M := M) F) :
    PE (torusLinks (2 * M)).length (eval (torusLinks (2 * M)) (obsOf (torusLinks (2 * M)) F)) F :=
  obsOf_pe _ (torusLinks_nodup _) _ F fun t ht => (h t ht).1

theorem obsOf_on' {F : RatPoly} (h : PtSup (M := M) F) :
    YMGap.Continuum.SU2TorusRPObs.OnLinks (· ∈ YMGap.Continuum.SU2TorusRPChoosePC.Pt M) (obsOf (torusLinks (2 * M)) F) :=
  obsOf_on _ _ F fun t ht => (h t ht).2

theorem sup_obsOf {F : RatPoly} (h : PtSup (M := M) F) :
    Sup (torusLinks (2 * M)).length (eval (torusLinks (2 * M)) (obsOf (torusLinks (2 * M)) F)) :=
  YMGap.Continuum.SU2TorusRPSym.sup_eval _
    (YMGap.Continuum.SU2TorusRPHW.onLinks_mono (fun ℓ hℓ =>
      (YMGap.Continuum.SU2TorusRPTorusZ.mem_tl ℓ).2 ((YMGap.Continuum.SU2TorusRPChoosePC.mem_Pt ℓ).1 hℓ).1) _ (obsOf_on' h))

/-- Back-substitution: `rpB` of `PtSup` polynomials equals `rpB` of their `obsOf` observables. -/
theorem rpB_obsOf {F G : RatPoly} (hF : PtSup (M := M) F) (hG : PtSup (M := M) G) :
    (rpB hM β K F G).eqv (rpB hM β K (eval (torusLinks (2 * M)) (obsOf (torusLinks (2 * M)) F))
      (eval (torusLinks (2 * M)) (obsOf (torusLinks (2 * M)) G))) :=
  rpB_pe hM β K (ptSup_sup hF) (sup_obsOf hF) (pe_symm _ (obsOf_pe' hF)) (pe_symm _ (obsOf_pe' hG))

theorem torus_rp_poly {β : Q'} (hβ : (0 : Q') ≤ β) : TorusRPPoly hM β K := fun F hF =>
  Q'.le_trans' _ _ _ (YMGap.Continuum.SU2TorusRPHW.torus_rp hM hβ K _ (obsOf_on' hF))
    (Q'.le_of_eqv (Q'.eqv_symm (rpB_obsOf hM β K hF hF)))

theorem torus_cs_poly {β : Q'} (hβ : (0 : Q') ≤ β) : TorusCS hM β K := fun F G hF hG => by
  have hcs := YMGap.Continuum.SU2TorusRPCSObs.torus_cs_obs hM hβ K _ _ (obsOf_on' hF) (obsOf_on' hG)
  have h1 := rpB_obsOf hM β K hF hG
  have h2 := rpB_obsOf hM β K hF hF
  have h3 := rpB_obsOf hM β K hG hG
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h1)
    (Q'.mul_eqv_congr_left _ _ _ h1))) (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv ?_))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h2) (Q'.mul_eqv_congr_left _ _ _ h3))

end YMGap.Continuum.SU2TorusRPPolyCS

#print axioms YMGap.Continuum.SU2TorusRPPolyCS.torus_rp_poly
#print axioms YMGap.Continuum.SU2TorusRPPolyCS.torus_cs_poly
