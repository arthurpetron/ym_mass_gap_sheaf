/-
# Torus RP (d9z): coordinate action of a composed reindexing

`rcomp_coord`: for `b < n`, `imap r b < n` and `rcomp r` sends the coordinate quaternion `cv b` to `cv (imap r b)`
up to `PE`. With `perm_haarX`, a torus observable written in `torusLinks` coordinates becomes one written in
layout coordinates. Matching Θ is not yet done.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPPermX
import YMGap.Continuum.SU2TorusRPCrossCoord

namespace YMGap.Continuum.SU2TorusRPPermCoord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (QuaternionBlockInvolution)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub qpe_trans)
open YMGap.Continuum.SU2TorusRPPermX (rcomp imap rcomp_sup)
open YMGap.Continuum.SU2ReindexPECongr (pe_reindex)

variable {n : Nat}

theorem rcomp_coord : ∀ (r : List (QuaternionBlockInvolution n)) (b : Nat), b < n →
    imap r b < n ∧
      QPE n (qsub (rcomp r) (PolyQuaternion.coordinateVariable b))
        (PolyQuaternion.coordinateVariable (imap r b))
  | [], b, hb => ⟨hb, ⟨pe_refl n _, pe_refl n _, pe_refl n _, pe_refl n _⟩⟩
  | σ :: r, b, hb => by
    obtain ⟨hl, hq⟩ := rcomp_coord r b hb
    have hs := YMGap.Continuum.SU2TorusRPCrossCoord.supQ_cv hb
    have ht := YMGap.Continuum.SU2TorusRPCrossCoord.supQ_cv hl
    refine ⟨σ.map_lt _ hl, qpe_trans ?_ (YMGap.Continuum.SU2TorusRPReindex.reindex_coord σ _ hl)⟩
    exact ⟨pe_reindex σ (rcomp_sup r _ hs.1) ht.1 hq.s, pe_reindex σ (rcomp_sup r _ hs.2.1) ht.2.1 hq.i,
      pe_reindex σ (rcomp_sup r _ hs.2.2.1) ht.2.2.1 hq.j, pe_reindex σ (rcomp_sup r _ hs.2.2.2) ht.2.2.2 hq.k⟩

open YMGap.Continuum.SU2TorusRPSubst (RingSub)
open YMGap.Continuum.SU2HaarAlgebra (pe_trans)
open YMGap.Continuum.SU2ReindexPECongr (sup_reindex)
open YMGap.Continuum.SU2TorusRPCompOn (sup_add sup_smul sup_neg)
open YMGap.Continuum.SU2TorusRPCore (sup_mul sup_one)

/-- `rcomp r` is a ring substitution up to `PE`. -/
theorem rcomp_ringSub : ∀ r : List (QuaternionBlockInvolution n), RingSub n (rcomp r)
  | [] => ⟨fun _ _ => pe_refl n _, fun _ _ => pe_refl n _, fun _ _ => pe_refl n _, fun _ => pe_refl n _,
      pe_refl n _⟩
  | [σ] => YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub σ
  | σ :: τ :: r => by
    have ih := rcomp_ringSub (τ :: r)
    have hS := YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub σ
    have hs : ∀ X, YMGap.Continuum.SU2TorusRPCore.Sup n (rcomp (τ :: r) X) := fun X => sup_reindex τ _
    exact
      { mul := fun p q => pe_trans n (pe_reindex σ (hs _) (sup_mul (hs p) (hs q)) (ih.mul p q)) (hS.mul _ _)
        add := fun p q => pe_trans n (pe_reindex σ (hs _) (sup_add (hs p) (hs q)) (ih.add p q)) (hS.add _ _)
        smul := fun c p => pe_trans n (pe_reindex σ (hs _) (sup_smul c (hs p)) (ih.smul c p)) (hS.smul _ _)
        neg := fun p => pe_trans n (pe_reindex σ (hs _) (sup_neg (hs p)) (ih.neg p)) (hS.neg _)
        one := pe_trans n (pe_reindex σ (hs _) (sup_one n) ih.one) hS.one }

end YMGap.Continuum.SU2TorusRPPermCoord

#print axioms YMGap.Continuum.SU2TorusRPPermCoord.rcomp_coord
#print axioms YMGap.Continuum.SU2TorusRPPermCoord.rcomp_ringSub
