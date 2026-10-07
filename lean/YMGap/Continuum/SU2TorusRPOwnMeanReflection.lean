/-
# Reflection of the actual torus Wilson OWN mean

The explicit torus reflection preserves the SAME finite Wilson weight.
Haar invariance then identifies the OWN means of a physical spatial
plaquette and its mirror, and reflection transports their actual centered
characters in Haar-context equivalence.

This supplies the reflection/mean ingredient of `SU2ClusterBridge.hcov`.
Translated OWN means, positive-time support and the time-shift pairing
remain separate. No analytic estimate, RP assembly or continuum claim is
proved here.
-/

import YMGap.Continuum.SU2WilsonCenteredCovariance
import YMGap.Continuum.SU2TorusRPObservableReflection

namespace YMGap.Continuum.SU2TorusRPOwnMeanReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq dirsOf)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_haar pe_append)
open YMGap.Continuum.SU2TorusRPSubst (pe_mul2 pe_smul)
open YMGap.Continuum.SU2TorusRPObs (thetaT tl_box tl_cl)
open YMGap.Continuum.SU2TorusRPBil (hR)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir theta_prod theta_haar)
open YMGap.Continuum.SU2TorusRPSym (tp_mir_perm)
open YMGap.Continuum.SU2TorusRPFactor (prod_perm)
open YMGap.Continuum.SU2TorusRPTorusZ (plaqL_mem)
open YMGap.Continuum.SU2TorusRPSwap (plaqIdx_lt)
open YMGap.Continuum.SU2TorusRPPlaqSplit (mem_tp)
open YMGap.Continuum.SU2TorusRPCore (Sup sup_mul)
open YMGap.Continuum.SU2TorusRPCompOn (sup_smul)
open YMGap.Continuum.SU2TorusRPCrossCoord (supQ_cv supQ_mul supQ_conj)
open YMGap.Continuum.SU2TorusRPSupTK (sup_prodTK)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (plaqWord linkVar)
open YMGap.Continuum.SU2WilsonPolymerIdentity (TK)
open YMGap.Continuum.SU2WilsonObsActivity (chi)
open YMGap.Continuum.SU2LinkDecaySharpInst (betaS)
open YMGap.Continuum.SU2WilsonCenteredCovariance
  (weight ownMean centeredCharacter)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2TorusRPKernel (pe_of_coeff)

local infix:50 " ≈ " => Q'.eqv

variable {M : Nat} (hM : 1 ≤ M) (K : Nat)

local notation "Ls" => torusLinks (2 * M)
local notation "Ps" => torusPlaquettes (2 * M)

include hM in
/-- A physical torus character is supported on the actual torus link blocks. -/
theorem character_supported (p : Z4Plaq) (hp : p ∈ Ps) :
    Sup (Ls).length (chi Ls (2 * M) p) := by
  have hi := plaqIdx_lt Ls (2 * M) p (plaqL_mem hM p hp)
  change Sup (Ls).length (polySmul 2 (plaqWord Ls (2 * M) p).scalar)
  refine sup_smul 2 ?_
  unfold plaqWord linkVar
  exact (supQ_mul
    (supQ_mul (supQ_cv (hi _ (List.mem_cons_self ..)))
      (supQ_cv (hi _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    (supQ_mul
      (supQ_conj (supQ_cv (hi _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
      (supQ_conj (supQ_cv (hi _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))).1

/-- Reflection preserves the actual `betaS` Wilson product, in every Haar
multiplicative context. The proof includes the temporal plaquette factors. -/
theorem theta_weight :
    PE (Ls).length (thetaT hM (weight Ls (2 * M) K Ps))
      (weight Ls (2 * M) K Ps) := by
  change PE (Ls).length
    (thetaT hM (prodPoly (TK Ls (2 * M) betaS K) Ps))
    (prodPoly (TK Ls (2 * M) betaS K) Ps)
  exact pe_trans _
    (theta_prod hM Ls (torusLinks_nodup _) tl_box (tl_cl hM) betaS K Ps
      (fun p hp => ⟨((mem_tp p).mp hp).1, plaqL_mem hM p hp⟩))
    (prod_perm (Ls).length (TK Ls (2 * M) betaS K) (tp_mir_perm hM))

private theorem theta_character (p : Z4Plaq) (hp : p ∈ Ps)
    (hsp : isT (dirsOf p.2).1 = false) :
    PE (Ls).length (thetaT hM (chi Ls (2 * M) p))
      (chi Ls (2 * M) (mir M p)) := by
  have hm : mir M p = (YMGap.Continuum.SU2TorusRPGeom.rv M p.1, p.2) := by
    unfold mir
    rw [hsp]
    rfl
  rw [hm]
  exact YMGap.Continuum.SU2TorusRPObservableReflection.theta_chi_spatial
    hM Ls (torusLinks_nodup _) tl_box (tl_cl hM) p.1 p.2 hsp
    (plaqL_mem hM p hp)

include hM in
/-- The actual spatial root and its mirror have the SAME OWN mean, using
the unchanged `ZW … []` reciprocal. No mean invariance is assumed. -/
theorem ownMean_mirror (p : Z4Plaq) (hp : p ∈ Ps)
    (hsp : isT (dirsOf p.2).1 = false) :
    ownMean Ls (2 * M) K Ps p ≈
      ownMean Ls (2 * M) K Ps (mir M p) := by
  have hw : Sup (Ls).length (weight Ls (2 * M) K Ps) :=
    sup_prodTK Ls (2 * M) betaS K Ps
      (fun r hr => plaqIdx_lt Ls (2 * M) r (plaqL_mem hM r hr))
  have hs := sup_mul (character_supported hM p hp) hw
  have hi := theta_haar hM Ls (torusLinks_nodup _) tl_box (tl_cl hM)
    (polyMul (chi Ls (2 * M) p) (weight Ls (2 * M) K Ps)) hs
  have he : PE (Ls).length
      (thetaT hM (polyMul (chi Ls (2 * M) p) (weight Ls (2 * M) K Ps)))
      (polyMul (chi Ls (2 * M) (mir M p)) (weight Ls (2 * M) K Ps)) :=
    pe_trans _ ((hR hM).mul _ _)
      (pe_mul2 _ (theta_character hM p hp hsp) (theta_weight hM K))
  unfold ownMean
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hi) (pe_haar _ he))

/-- Reflection transports the actual OWN-centered character to its
OWN-centered mirror, in the context equivalence needed by `rpB`. -/
theorem theta_centeredCharacter (p : Z4Plaq) (hp : p ∈ Ps)
    (hsp : isT (dirsOf p.2).1 = false) :
    PE (Ls).length (thetaT hM (centeredCharacter Ls (2 * M) K Ps p))
      (centeredCharacter Ls (2 * M) K Ps (mir M p)) := by
  unfold centeredCharacter
  refine pe_trans _ ((hR hM).add _ _)
    (pe_append _ (theta_character hM p hp hsp) ?_)
  refine pe_trans _ ((hR hM).smul _ _)
    (pe_trans _ (pe_smul _ _ (hR hM).one) ?_)
  exact pe_of_coeff _ (RatPolyCoeffEqv.smul_coefficient
    (Q'.neg_eqv_congr _ _ (ownMean_mirror hM K p hp hsp)) polyOne)

end YMGap.Continuum.SU2TorusRPOwnMeanReflection

#print axioms YMGap.Continuum.SU2TorusRPOwnMeanReflection.character_supported
#print axioms YMGap.Continuum.SU2TorusRPOwnMeanReflection.theta_weight
#print axioms YMGap.Continuum.SU2TorusRPOwnMeanReflection.ownMean_mirror
#print axioms YMGap.Continuum.SU2TorusRPOwnMeanReflection.theta_centeredCharacter
