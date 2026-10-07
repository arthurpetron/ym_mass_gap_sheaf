/-
# Time translation of the SAME finite torus Wilson OWN mean

The actual finite link list is permuted by the explicit inverse time shift.
The existing supported Haar relabelling theorem then transports a physical
plaquette character. Its new link indices are exactly the old shifted indices;
the full Wilson weight, including temporal plaquettes, is unchanged up to PE.

This proves the one-point translation identity needed by
`SU2ClusterBridge.hcov`, without assuming equality of means. The partition
reciprocal is literally unchanged, so no reciprocal cancellation is used.
RP/time-pairing assembly, all-vector estimates and continuum limits remain
separate obligations.
-/

import YMGap.Continuum.SU2TorusLinksTimeShift
import YMGap.Continuum.SU2TorusRPOwnMeanReflection

namespace YMGap.Continuum.SU2TorusOwnMeanTimeShift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion characterPolynomial)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_trans pe_haar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2TorusRPSubst
  (QPE qsub qpe_mul qpe_conj pe_smul pe_mul2)
open YMGap.Continuum.SU2TorusRPPermX (rcomp imap perm_haarX)
open YMGap.Continuum.SU2TorusRPPermCoord (rcomp_coord rcomp_ringSub)
open YMGap.Continuum.SU2TorusRPObservableReflection (chi_word_sub)
open YMGap.Continuum.SU2TorusRPSwap (plaqL plaqIdx_lt)
open YMGap.Continuum.SU2TorusRPTorusZ (plaqL_mem)
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar plaqWord)
open YMGap.Continuum.SU2WilsonObsActivity (chi)
open YMGap.Continuum.SU2WilsonPolymerIdentity (TK)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly)
open YMGap.Continuum.SU2WilsonActivity (wilsonA)
open YMGap.Continuum.SU2LinkDecaySharpInst (betaS)
open YMGap.Continuum.SU2WilsonCenteredCovariance (weight ownMean)
open YMGap.Continuum.SU2TimeShift (shv wordI tAdd_vs)
open YMGap.Continuum.SU2TorusLinksTimeShift
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (QuaternionBlockInvolution)

local infix:50 " ≈ " => Q'.eqv

private theorem rcomp_link {n : Nat} (L L' : List Z4Link)
    (r : List (QuaternionBlockInvolution n)) (ℓ : Z4Link)
    (hlt : L.idxOf ℓ < n) (hi : imap r (L.idxOf ℓ) = L'.idxOf ℓ) :
    QPE n (qsub (rcomp r) (linkVar L ℓ)) (linkVar L' ℓ) := by
  have h := (rcomp_coord r (L.idxOf ℓ) hlt).2
  rw [hi] at h
  exact h

/-- The existing link-order relabelling transports the actual fundamental
character, with physical link coverage retained. -/
theorem rcomp_character (L L' : List Z4Link)
    (r : List (QuaternionBlockInvolution L.length)) (N : Nat) (p : Z4Plaq)
    (hL : ∀ ℓ ∈ plaqL N p, ℓ ∈ L)
    (hi : ∀ ℓ, imap r (L.idxOf ℓ) = L'.idxOf ℓ) :
    PE L.length (rcomp r (chi L N p)) (chi L' N p) := by
  have hl := plaqIdx_lt L N p hL
  have h1 := rcomp_link L L' r _ (hl _ (List.mem_cons_self ..)) (hi _)
  have h2 := rcomp_link L L' r _
    (hl _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (hi _)
  have h3 := rcomp_link L L' r _
    (hl _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (hi _)
  have h4 := rcomp_link L L' r _
    (hl _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) (hi _)
  unfold chi YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqCharacter plaqWord
  exact pe_trans _ (chi_word_sub (rcomp_ringSub r) _ _ _ _)
    (pe_smul _ 2 (qpe_mul (qpe_mul h1 h2)
      (qpe_mul (qpe_conj h3) (qpe_conj h4))).s)

private theorem word_shift (N : Nat) (L : List Z4Link) (t : Nat) (p : Z4Plaq) :
    plaqWord L N (shv N t p) = wordI N (fun ℓ => L.idxOf (shv N t ℓ)) p := by
  obtain ⟨v, P⟩ := p
  unfold plaqWord linkVar wordI shv
  rw [tAdd_vs, tAdd_vs]

variable {M : Nat} (hM : 1 ≤ M) (K t : Nat)

local notation "Ls" => torusLinks (2 * M)
local notation "Ps" => torusPlaquettes (2 * M)
local notation "Li" => List.map (shv (2 * M) (2 * M - t % (2 * M))) (torusLinks (2 * M))

include hM

/-- The inverse-shifted link order gives exactly the original translated
plaquette word, not a new action or a new observable. -/
theorem inverseShift_word (p : Z4Plaq) (hp : p ∈ Ps) :
    plaqWord Li (2 * M) p = plaqWord Ls (2 * M) (shv (2 * M) t p) := by
  have hN : 0 < 2 * M := by omega
  have hl := plaqL_mem hM p hp
  have hi := fun ℓ hℓ => inverseShift_idxOf hN t ℓ (hl ℓ hℓ)
  rw [word_shift]
  unfold plaqWord linkVar wordI
  rw [hi _ (List.mem_cons_self ..),
    hi _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
    hi _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
    hi _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))]

omit hM in
private theorem prod_map (F : Z4Plaq → RatPoly) (s : Z4Plaq → Z4Plaq) :
    ∀ P : List Z4Plaq, prodPoly (fun p => F (s p)) P = prodPoly F (P.map s)
  | [] => rfl
  | p :: P => by
      change polyMul (F (s p)) (prodPoly (fun p => F (s p)) P) =
        polyMul (F (s p)) (prodPoly F (P.map s))
      rw [prod_map F s P]

/-- Relabelling by inverse translation preserves the full finite Wilson
weight, including all temporal plaquettes. -/
theorem inverseShift_weight :
    PE (Ls).length (weight Li (2 * M) K Ps) (weight Ls (2 * M) K Ps) := by
  change PE (Ls).length (prodPoly (TK Li (2 * M) betaS K) Ps)
    (prodPoly (TK Ls (2 * M) betaS K) Ps)
  have he : PE (Ls).length (prodPoly (TK Li (2 * M) betaS K) Ps)
      (prodPoly (fun p => TK Ls (2 * M) betaS K (shv (2 * M) t p)) Ps) :=
    YMGap.Continuum.SU2TorusRPSplitTK.prod_congr Ps (fun p hp => by
      unfold TK
      rw [inverseShift_word hM t p hp]
      exact pe_refl _ _)
  rw [prod_map (TK Ls (2 * M) betaS K) (shv (2 * M) t) Ps] at he
  exact pe_trans _ he (YMGap.Continuum.SU2TorusRPFactor.prod_perm _ _
    (torusPlaquettes_timeShift_perm (by omega) t))

/-- Translation invariance of the unnormalized actual character moment.
The permutation witness is used only inside this propositional equality. -/
theorem character_moment_timeShift (p : Z4Plaq) (hp : p ∈ Ps) :
    quaternionHaar (Ls).length
      (polyMul (chi Ls (2 * M) p) (weight Ls (2 * M) K Ps)) ≈
    quaternionHaar (Ls).length
      (polyMul (chi Ls (2 * M) (shv (2 * M) t p)) (weight Ls (2 * M) K Ps)) := by
  obtain ⟨r, hi, hh⟩ := perm_haarX (2 * M) betaS K Ps
    (torusLinks_inverseTimeShift_perm (by omega) t).symm rfl
    (torusLinks_nodup _) (fun q hq => plaqL_mem hM q hq)
  have hs := YMGap.Continuum.SU2TorusRPOwnMeanReflection.character_supported hM p hp
  have hm := hh (chi Ls (2 * M) p) hs
  have hc := rcomp_character Ls Li r (2 * M) p (plaqL_mem hM p hp) hi
  have hs' : chi Li (2 * M) p = chi Ls (2 * M) (shv (2 * M) t p) := by
    unfold chi YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqCharacter
    rw [inverseShift_word hM t p hp]
  rw [hs'] at hc
  exact Q'.eqv_trans _ _ _ hm
    (pe_haar _ (pe_mul2 _ hc (inverseShift_weight hM K t)))

/-- Actual OWN means are invariant under every periodic time translation.
Both sides use the SAME unchanged partition reciprocal. -/
theorem ownMean_timeShift (p : Z4Plaq) (hp : p ∈ Ps) :
    ownMean Ls (2 * M) K Ps p ≈
      ownMean Ls (2 * M) K Ps (shv (2 * M) t p) := by
  unfold ownMean
  exact Q'.mul_eqv_congr_right _ _ _ (character_moment_timeShift hM K t p hp)

end YMGap.Continuum.SU2TorusOwnMeanTimeShift

#print axioms YMGap.Continuum.SU2TorusOwnMeanTimeShift.rcomp_character
#print axioms YMGap.Continuum.SU2TorusOwnMeanTimeShift.inverseShift_word
#print axioms YMGap.Continuum.SU2TorusOwnMeanTimeShift.inverseShift_weight
#print axioms YMGap.Continuum.SU2TorusOwnMeanTimeShift.character_moment_timeShift
#print axioms YMGap.Continuum.SU2TorusOwnMeanTimeShift.ownMean_timeShift
