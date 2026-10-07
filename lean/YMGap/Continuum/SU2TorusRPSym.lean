/-
# Torus RP (f3): Θ-symmetry of the RP form on link observables

`rpB_symm`: `rpB (eval e) (eval e') ≈ rpB (eval e') (eval e)` for observables on torus links. The proof uses
Θ-invariance of Haar (`theta_haar`), `Θ Π T_K = Π T_K[mir]` (`theta_prod`) with `tp.map mir ~ tp` (`tp_mir_perm`),
and `Θ∘Θ ≡ id` on observables (`theta2_obs`). Everything is real: Θ's quaternion conjugation on time links is an
involution, so there is no complex conjugate.

**OPEN: the bilinear expansion into `quad`, and `TorusCS`, `TorusRPPoly`.**
-/

import YMGap.Continuum.SU2TorusRPCSShape
import YMGap.Continuum.SU2TorusRPCSRat
import YMGap.Continuum.SU2TorusRPFactor

namespace YMGap.Continuum.SU2TorusRPSym

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl pe_symm pe_haar pe_comm pe_mulR pe_mulL)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub qpe_trans qpe_conj qconj_sub pe_mul2)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul)
open YMGap.Continuum.SU2TorusRPObs (Obs evalI eval OnLinks sub_evalI thetaT tl_cl)
open YMGap.Continuum.SU2TorusRPMatch (imgR like_obs like_img sup_evalI)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)

theorem polyNeg2 : ∀ X : RatPoly, polyNeg (polyNeg X) = X
  | [] => rfl
  | (m, c) :: X => by
    obtain ⟨num, d⟩ := c
    show (m, (⟨-(-num), d⟩ : Q')) :: polyNeg (polyNeg X) = _
    rw [Int.neg_neg, polyNeg2 X]

theorem qconj2 {n : Nat} (q : PolyQuaternion) : QPE n (PolyQuaternion.conj (PolyQuaternion.conj q)) q := by
  refine ⟨pe_refl n _, ?_, ?_, ?_⟩
  · show PE n (polyNeg (polyNeg q.iPart)) _; rw [polyNeg2]; exact pe_refl n _
  · show PE n (polyNeg (polyNeg q.jPart)) _; rw [polyNeg2]; exact pe_refl n _
  · show PE n (polyNeg (polyNeg q.kPart)) _; rw [polyNeg2]; exact pe_refl n _

variable {M : Nat} (hM : 1 ≤ M)

theorem thetaT_sup (X : RatPoly) : Sup (torusLinks (2 * M)).length (thetaT hM X) :=
  YMGap.Continuum.SU2TorusRPLayoutSup.sup_sign _ _ (YMGap.Continuum.SU2ReindexPECongr.sup_reindex _ _)

theorem thetaT_pe {X Y : RatPoly} (hX : Sup (torusLinks (2 * M)).length X) (hY : Sup (torusLinks (2 * M)).length Y) (h : PE (torusLinks (2 * M)).length X Y) :
    PE (torusLinks (2 * M)).length (thetaT hM X) (thetaT hM Y) :=
  YMGap.Continuum.SU2TorusRPConjCongr.conj_peCongr _ _ _
    (YMGap.Continuum.SU2ReindexPECongr.pe_reindex _ (by exact hX) (by exact hY) h)

theorem supQ_lv (ℓ : Z4Link) (h : ℓ ∈ torusLinks (2 * M)) : YMGap.Continuum.SU2TorusRPKernel.SupQ (torusLinks (2 * M)).length (linkVar (torusLinks (2 * M)) ℓ) :=
  YMGap.Continuum.SU2TorusRPHW.supQ_lv (torusLinks (2 * M)) ℓ h rfl

theorem sup_eval (e : Obs) (he : OnLinks (· ∈ torusLinks (2 * M)) e) : Sup (torusLinks (2 * M)).length (eval (torusLinks (2 * M)) e) :=
  sup_evalI _ _ (fun ℓ h => supQ_lv ℓ h) e he

theorem theta_imgR (ℓ : Z4Link) (h : ℓ ∈ torusLinks (2 * M)) : QPE (torusLinks (2 * M)).length (qsub (thetaT hM) (imgR (torusLinks (2 * M)) M ℓ)) (linkVar (torusLinks (2 * M)) ℓ) := by
  have hr := tl_cl hM ℓ h
  have hl := like_img (YMGap.Continuum.SU2TorusRPMatch.thetaT_like hM) _ hr
  have hinv := YMGap.Continuum.SU2TorusRPGeom.refl_invol hM ℓ (YMGap.Continuum.SU2TorusRPObs.tl_box ℓ h)
  have hd := YMGap.Continuum.SU2TorusRPLayoutT.refl_dir M ℓ
  unfold imgR at hl ⊢
  rw [hinv, hd] at hl
  cases hT : YMGap.Continuum.SU2TorusRPThetaTK.isT ℓ.2
  · rw [hT] at hl; exact hl
  · rw [hT] at hl
    exact qpe_trans (qconj_sub (YMGap.Continuum.SU2TorusRPMatch.thetaT_like hM).ring _)
      (qpe_trans (qpe_conj hl) (qconj2 _))

theorem theta2_obs (e : Obs) (he : OnLinks (· ∈ torusLinks (2 * M)) e) :
    PE (torusLinks (2 * M)).length (thetaT hM (thetaT hM (eval (torusLinks (2 * M)) e))) (eval (torusLinks (2 * M)) e) := by
  have h1 := like_obs (YMGap.Continuum.SU2TorusRPMatch.thetaT_like hM) e he
  have sI : Sup (torusLinks (2 * M)).length (evalI (imgR (torusLinks (2 * M)) M) e) :=
    sup_evalI _ _ (fun ℓ h => YMGap.Continuum.SU2TorusRPHW.supQ_imgR (torusLinks (2 * M)) ℓ (tl_cl hM ℓ h) rfl) e he
  exact pe_trans _ (thetaT_pe hM (thetaT_sup hM _) sI h1)
    (sub_evalI (YMGap.Continuum.SU2TorusRPMatch.thetaT_like hM).ring (· ∈ torusLinks (2 * M)) _ _ (fun ℓ h => theta_imgR hM ℓ h) e he)

include hM in
theorem mir_box (p : Z4Plaq) (h : InBox (2 * M) p.1) : InBox (2 * M) (mir M p).1 := by
  rw [YMGap.Continuum.SU2TorusRPMirInv.mir_eq]
  exact YMGap.Continuum.SU2TorusRPMirGeom.refl_box hM _ h

include hM in
theorem tp_mir_perm : ((torusPlaquettes (2 * M)).map (mir M)).Perm (torusPlaquettes (2 * M)) := by
  have mt := fun p => YMGap.Continuum.SU2TorusRPPlaqSplit.mem_tp (M := M) p
  refine YMGap.Continuum.SU2TorusRPPermExt.perm_ext' _ _ ?_ (torusPlaquettes_nodup _) fun p => ⟨fun h => ?_, fun h => ?_⟩
  · refine YMGap.Continuum.SU2TorusRPPlaqSplit.nodup_map_on _ _ (fun x hx y hy e => ?_) (torusPlaquettes_nodup _)
    rw [← YMGap.Continuum.SU2TorusRPMirInv.mir_invol hM x ((mt x).1 hx), e,
      YMGap.Continuum.SU2TorusRPMirInv.mir_invol hM y ((mt y).1 hy)]
  · obtain ⟨q, hq, e⟩ := List.mem_map.1 h
    rw [← e]; exact (mt _).2 (mir_box hM q ((mt q).1 hq))
  · have hb := (mt p).1 h
    exact List.mem_map.2 ⟨mir M p, (mt _).2 (mir_box hM p hb), YMGap.Continuum.SU2TorusRPMirInv.mir_invol hM p hb⟩

end YMGap.Continuum.SU2TorusRPSym

#print axioms YMGap.Continuum.SU2TorusRPSym.theta2_obs
#print axioms YMGap.Continuum.SU2TorusRPSym.tp_mir_perm
