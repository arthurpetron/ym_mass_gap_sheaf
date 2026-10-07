/-
# Torus RP (e3): discharge of the `hW` target `TorusRP`

`torus_rp hM hβ K : TorusRP hM β K`. This is reflection positivity for the torus measure with the truncated T_K
weight (fixed K) (`wilsonA` weights) on `torusLinks (2M)` order, with Θ = `thetaPoly` on `torusLinks` and observables on positive links.

The chain: `torus_X` moves to layout order; `rcomp_imgR`/`like_obs` match the torus Θ with the layout `thetaH`
on observables; `haar_drop'` passes from `|L|` to `a+a` blocks; `torus_rp_lay` closes.
-/

import YMGap.Continuum.SU2TorusRPMatch
import YMGap.Continuum.SU2TorusRPLayoutRPL
import YMGap.Continuum.SU2TorusRPLayoutFactor

namespace YMGap.Continuum.SU2TorusRPHW

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl pe_symm pe_haar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPSubst (pe_mul2)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPChoosePC (Pt Ct mem_Pt mem_Ct)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul)
open YMGap.Continuum.SU2TorusRPKernel (SupQ)
open YMGap.Continuum.SU2TorusRPObs (Obs evalI eval OnLinks sub_evalI thetaT tl_cl TorusRP)
open YMGap.Continuum.SU2TorusRPMatch (imgR sup_evalI like_obs)

theorem onLinks_mono {P Q : Z4Link → Prop} (h : ∀ ℓ, P ℓ → Q ℓ) : ∀ e : Obs, OnLinks P e → OnLinks Q e
  | .const _, _ => trivial
  | .var ℓ _, hp => h ℓ hp
  | .add a b, hp => ⟨onLinks_mono h a hp.1, onLinks_mono h b hp.2⟩
  | .mul a b, hp => ⟨onLinks_mono h a hp.1, onLinks_mono h b hp.2⟩
  | .neg a, hp => onLinks_mono h a hp

theorem supQ_lv {n : Nat} (L : List Z4Link) (ℓ : Z4Link) (h : ℓ ∈ L) (hn : L.length = n) : SupQ n (linkVar L ℓ) :=
  YMGap.Continuum.SU2TorusRPCrossCoord.supQ_cv (hn ▸ YMGap.Continuum.SU2TorusRPSwap.idx_lt ℓ L h)

theorem supQ_imgR {n M : Nat} (L : List Z4Link) (ℓ : Z4Link) (h : reflLink M ℓ ∈ L) (hn : L.length = n) :
    SupQ n (imgR L M ℓ) := by
  unfold imgR
  cases YMGap.Continuum.SU2TorusRPThetaTK.isT ℓ.2
  · exact supQ_lv L _ h hn
  · exact YMGap.Continuum.SU2TorusRPCrossCoord.supQ_conj (supQ_lv L _ h hn)

variable {M : Nat} (hM : 1 ≤ M)

/-- **`hW` discharged:** RP for the actual torus `T_K` measure. -/
theorem torus_rp {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) : TorusRP hM β K := by
  intro e he
  have hP : ∀ ℓ, ℓ ∈ Pt M → ℓ ∈ torusLinks (2 * M) := fun ℓ h =>
    (YMGap.Continuum.SU2TorusRPTorusZ.mem_tl ℓ).2 ((mem_Pt ℓ).1 h).1
  have hperm := YMGap.Continuum.SU2TorusRPTorusZ.lay_perm hM
  have hlen : (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).length = (torusLinks (2 * M)).length := hperm.length_eq.symm
  have hinL : ∀ ℓ, ℓ ∈ torusLinks (2 * M) → ℓ ∈ Pt M ++ Ct M ++ (Pt M).map (reflLink M) := fun ℓ h => hperm.mem_iff.1 h
  have onT := onLinks_mono hP e he
  -- supports
  have sT : Sup (torusLinks (2 * M)).length (eval (torusLinks (2 * M)) e) :=
    sup_evalI _ _ (fun ℓ h => supQ_lv _ ℓ (hP ℓ h) rfl) e he
  have sTh : Sup (torusLinks (2 * M)).length (thetaT hM (eval (torusLinks (2 * M)) e)) :=
    YMGap.Continuum.SU2TorusRPLayoutSup.sup_sign _ _ (YMGap.Continuum.SU2ReindexPECongr.sup_reindex _ _)
  have sIt : Sup (torusLinks (2 * M)).length (evalI (imgR (torusLinks (2 * M)) M) e) :=
    sup_evalI _ _ (fun ℓ h => supQ_imgR _ ℓ (tl_cl hM ℓ (hP ℓ h)) rfl) e he
  have sIL : Sup (torusLinks (2 * M)).length (evalI (imgR (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) M) e) :=
    sup_evalI _ _ (fun ℓ h => supQ_imgR _ ℓ (hinL _ (tl_cl hM ℓ (hP ℓ h))) hlen) e he
  have sL : Sup (torusLinks (2 * M)).length (eval (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) e) :=
    sup_evalI _ _ (fun ℓ h => supQ_lv _ ℓ (hinL ℓ (hP ℓ h)) hlen) e he
  have sLP : Sup (Pt M).length (eval (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) e) :=
    sup_evalI _ _ (fun ℓ h => YMGap.Continuum.SU2TorusRPCrossCoord.supQ_cv
      (YMGap.Continuum.SU2TorusRPTorusX.pos_idx ℓ h)) e he
  have sPi : Sup (torusLinks (2 * M)).length (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK
      (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) (2 * M) β K) (torusPlaquettes (2 * M))) :=
    YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK _ _ β K _ fun p hp => hlen ▸
      YMGap.Continuum.SU2TorusRPSwap.plaqIdx_lt _ _ p fun ℓ hℓ =>
        hinL ℓ (YMGap.Continuum.SU2TorusRPTorusZ.plaqL_mem hM p hp ℓ hℓ)
  -- step 1: layout order
  obtain ⟨r, hr, hint⟩ := YMGap.Continuum.SU2TorusRPTorusX.torus_X hM β K
  have h1 := hint _ (sup_mul sTh sT)
  -- step 2: match Θ on the torus side
  have hR := YMGap.Continuum.SU2TorusRPPermCoord.rcomp_ringSub r
  have hA : PE (torusLinks (2 * M)).length (YMGap.Continuum.SU2TorusRPPermX.rcomp r (thetaT hM (eval (torusLinks (2 * M)) e)))
      (evalI (imgR (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) M) e) :=
    pe_trans _ (YMGap.Continuum.SU2TorusRPMatch.rcomp_pe r sTh sIt
        (like_obs (YMGap.Continuum.SU2TorusRPMatch.thetaT_like hM) e onT))
      (sub_evalI hR (· ∈ Pt M) _ _ (fun ℓ h => YMGap.Continuum.SU2TorusRPMatch.rcomp_imgR r hr ℓ (tl_cl hM ℓ (hP ℓ h))) e he)
  have hB := YMGap.Continuum.SU2TorusRPObs.rcomp_obs r hr e onT
  have h2 := pe_haar (torusLinks (2 * M)).length (pe_mul2 _ (pe_trans _ (hR.mul _ _) (pe_mul2 _ hA hB))
    (pe_refl _ (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK
      (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) (2 * M) β K) (torusPlaquettes (2 * M)))))
  -- step 3: blocks |L| → a + a
  have hn2 : ((Pt M).length + (Ct M).length) + ((Pt M).length + (Ct M).length) =
      (torusLinks (2 * M)).length + (Ct M).length := by
    rw [← hlen, List.length_append, List.length_append, List.length_map]; omega
  have h3 := YMGap.Continuum.SU2TorusRPLayoutRPL.haar_drop' _ _ _ hn2 _
    (YMGap.Continuum.SU2TorusRPLayoutRPL.van_sup (sup_mul (sup_mul sIL sL) sPi))
  -- step 4: layout Θ
  have hHD : OnLinks (YMGap.Continuum.SU2TorusRPHalfSwap.HD ((Pt M).length + (Ct M).length)
      (YMGap.Continuum.SU2TorusRPLayoutT.layT (Pt M ++ Ct M ++ (Pt M).map (reflLink M)))
      (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) M) e :=
    onLinks_mono (fun ℓ h => YMGap.Continuum.SU2TorusRPLayoutT.lay_HD M (Pt M) (Ct M)
      (YMGap.Continuum.SU2TorusRPChoosePC.lay_nodup hM) ℓ h
      (YMGap.Continuum.SU2TorusRPLayoutFactor.hinjP hM (Pt M) (fun x hx => ((mem_Pt x).1 hx).1) ℓ
        ((mem_Pt ℓ).1 h).1)) e he
  have h4 := pe_haar _ (pe_mul2 _ (pe_mul2 _ (like_obs (YMGap.Continuum.SU2TorusRPHalfSwap.thetaH_like _ _ _ M) e hHD)
    (pe_refl _ (eval (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) e)))
    (pe_refl _ (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK
      (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) (2 * M) β K) (torusPlaquettes (2 * M)))))
  have h5 := YMGap.Continuum.SU2TorusRPLayoutRP.torus_rp_lay hM (Pt M) (Ct M)
    (YMGap.Continuum.SU2TorusRPChoosePC.lay_nodup hM) YMGap.Continuum.SU2TorusRPChoosePC.Ct_nodup
    (YMGap.Continuum.SU2TorusRPChoosePC.Ct_ne hM)
    (fun ℓ hb hs => (mem_Ct ℓ).mpr ⟨hb, hs⟩) (fun ℓ hb hs => (mem_Pt ℓ).mpr ⟨hb, hs⟩)
    (fun x hx => ((mem_Pt x).mp hx).1) hβ K _ _ _ (YMGap.Continuum.SU2TorusRPPlaqSplit.plaq_perm hM)
    (fun p hp => (YMGap.Continuum.SU2TorusRPPlaqSplit.mem_posT p).mp hp)
    (fun q hq => (YMGap.Continuum.SU2TorusRPPlaqSplit.mem_crossT q).mp hq)
    (fun p hp => (YMGap.Continuum.SU2TorusRPPlaqSplit.mem_tp p).mp hp) _ sLP
  refine Q'.le_trans' _ _ _ h5 (Q'.le_of_eqv ?_)
  exact Q'.eqv_trans _ _ _ h4 (Q'.eqv_trans _ _ _ h3
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm h2) (Q'.eqv_symm h1)))

end YMGap.Continuum.SU2TorusRPHW

#print axioms YMGap.Continuum.SU2TorusRPHW.torus_rp
