/-
# Torus RP (e2): reflection matching on link observables

* `sup_evalI`: support of evaluated observables.
* `imgR L M ℓ`: the Θ-image of the link variable `ℓ`, which is `linkVar L (Θℓ)`, conjugated on temporal links.
* `like_img`: any `ThetaLike` substitution sends `linkVar L ℓ` to `imgR L M ℓ`, so `like_obs` gives
  `S (eval L e) ≡ evalI (imgR L M) e`.
* `thetaT_like`: the torus Θ (`thetaT`) is `ThetaLike` on `torusLinks` for every link.
* `rcomp_imgR`: the torus→layout reindexing sends `imgR torusLinks` to `imgR layout`.
* `rcomp_pe`: `rcomp r` respects `PE` on supported polynomials.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPObs
import YMGap.Continuum.SU2TorusRPHalfSwap
import YMGap.Continuum.SU2TorusRPLayoutSup

namespace YMGap.Continuum.SU2TorusRPMatch

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub qpe_trans qpe_conj qconj_sub)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPChoosePC (Pt Ct)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPThetaAbs (ThetaLike)
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul sup_one)
open YMGap.Continuum.SU2TorusRPKernel (SupQ)
open YMGap.Continuum.SU2TorusRPObs (Obs evalI eval OnLinks comp sub_evalI)
open YMGap.Continuum.SU2TorusRPPermX (rcomp imap rcomp_sup)

theorem sup_evalI {n : Nat} (P : Z4Link → Prop) (img : Z4Link → PolyQuaternion) (himg : ∀ ℓ, P ℓ → SupQ n (img ℓ)) :
    ∀ e : Obs, OnLinks P e → Sup n (evalI img e)
  | .const c, _ => YMGap.Continuum.SU2TorusRPCompOn.sup_smul c (sup_one n)
  | .var ℓ k, h => by
    have hq := himg ℓ h
    show Sup n (comp (img ℓ) k)
    cases k with
    | zero => exact hq.1
    | succ k => cases k with
      | zero => exact hq.2.1
      | succ k => cases k with
        | zero => exact hq.2.2.1
        | succ k => exact hq.2.2.2
  | .add a b, h => YMGap.Continuum.SU2TorusRPCompOn.sup_add (sup_evalI P img himg a h.1) (sup_evalI P img himg b h.2)
  | .mul a b, h => sup_mul (sup_evalI P img himg a h.1) (sup_evalI P img himg b h.2)
  | .neg a, h => YMGap.Continuum.SU2TorusRPCompOn.sup_neg (sup_evalI P img himg a h)

def imgR (L : List Z4Link) (M : Nat) (ℓ : Z4Link) : PolyQuaternion :=
  if isT ℓ.2 then PolyQuaternion.conj (linkVar L (reflLink M ℓ)) else linkVar L (reflLink M ℓ)

theorem like_img {n : Nat} {S : RatPoly → RatPoly} {L : List Z4Link} {M : Nat} {D : Z4Link → Prop}
    (hS : ThetaLike n S L M D) (ℓ : Z4Link) (hD : D ℓ) : QPE n (qsub S (linkVar L ℓ)) (imgR L M ℓ) := by
  obtain ⟨v, d⟩ := ℓ
  cases d with
  | x0 => exact hS.temporal v hD
  | x1 => exact hS.spatial _ hD rfl
  | x2 => exact hS.spatial _ hD rfl
  | x3 => exact hS.spatial _ hD rfl

theorem like_obs {n : Nat} {S : RatPoly → RatPoly} {L : List Z4Link} {M : Nat} {D : Z4Link → Prop}
    (hS : ThetaLike n S L M D) (e : Obs) (he : OnLinks D e) : PE n (S (eval L e)) (evalI (imgR L M) e) :=
  sub_evalI hS.ring D _ _ (fun ℓ h => like_img hS ℓ h) e he

variable {M : Nat} (hM : 1 ≤ M)

theorem thetaT_like : ThetaLike (torusLinks (2 * M)).length (YMGap.Continuum.SU2TorusRPObs.thetaT hM)
    (torusLinks (2 * M)) M (· ∈ torusLinks (2 * M)) where
  ring := YMGap.Continuum.SU2TorusRPThetaTK.theta_ringSub hM _ _ _ _
  spatial ℓ h hs := YMGap.Continuum.SU2TorusRPThetaTK.theta_spatial_link hM _ _ _ _ h hs
  temporal v h := YMGap.Continuum.SU2TorusRPThetaTime.theta_temporal_link hM _ _ _ _ v h

theorem rcomp_pe {n : Nat} : ∀ (r : List (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.QuaternionBlockInvolution n))
    {X Y : RatPoly}, Sup n X → Sup n Y → PE n X Y → PE n (rcomp r X) (rcomp r Y)
  | [], _, _, _, _, h => h
  | σ :: r, _, _, hX, hY, h =>
    YMGap.Continuum.SU2ReindexPECongr.pe_reindex σ (rcomp_sup r _ hX) (rcomp_sup r _ hY) (rcomp_pe r hX hY h)

theorem rcomp_imgR (r : List (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.QuaternionBlockInvolution
      (torusLinks (2 * M)).length))
    (hr : ∀ ℓ, imap r ((torusLinks (2 * M)).idxOf ℓ) = (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).idxOf ℓ)
    (ℓ : Z4Link) (hℓ : reflLink M ℓ ∈ torusLinks (2 * M)) :
    QPE (torusLinks (2 * M)).length (qsub (rcomp r) (imgR (torusLinks (2 * M)) M ℓ))
      (imgR (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) M ℓ) := by
  have hc := (YMGap.Continuum.SU2TorusRPPermCoord.rcomp_coord r _
    (YMGap.Continuum.SU2TorusRPSwap.idx_lt _ _ hℓ)).2
  rw [hr] at hc
  unfold imgR linkVar
  cases isT ℓ.2
  · exact hc
  · exact qpe_trans (qconj_sub (YMGap.Continuum.SU2TorusRPPermCoord.rcomp_ringSub r) _) (qpe_conj hc)

end YMGap.Continuum.SU2TorusRPMatch

#print axioms YMGap.Continuum.SU2TorusRPMatch.like_obs
#print axioms YMGap.Continuum.SU2TorusRPMatch.thetaT_like
#print axioms YMGap.Continuum.SU2TorusRPMatch.rcomp_imgR
#print axioms YMGap.Continuum.SU2TorusRPMatch.sup_evalI
