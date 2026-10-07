/-
# Torus RP (d9z''): torus-order integrals with an observable, in layout order

`torus_X`: there is a list `r` of block involutions with `imap r (idx_{torusLinks} ℓ) = idx_L ℓ` (where `L` is the
layout `Pt ++ Ct ++ Θ Pt`), and with `rcomp r` a `RingSub` sending `cv b ↦ cv (imap r b)` (`rcomp_ringSub`,
`rcomp_coord`), such that `∫_{|torusLinks|} X·Π_{torusPlaquettes} T_K[torusLinks] = ∫ (rcomp r X)·Π T_K[L]` for every
supported `X`. Still open: showing that `rcomp r (Θ_torus G · G)` has the layout RP form, and then `hW`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPTorusZ
import YMGap.Continuum.SU2TorusRPPermCoord

namespace YMGap.Continuum.SU2TorusRPTorusX

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (QuaternionBlockInvolution)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPChoosePC (Pt Ct)
open YMGap.Continuum.SU2TorusRPPermX (rcomp imap)
open YMGap.Continuum.SU2TorusRPCore (Sup)

variable {M : Nat} (hM : 1 ≤ M)

include hM in
theorem torus_X (β : Q') (K : Nat) :
    ∃ r : List (QuaternionBlockInvolution (torusLinks (2 * M)).length),
      (∀ ℓ, imap r ((torusLinks (2 * M)).idxOf ℓ) = (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).idxOf ℓ) ∧
      ∀ X, Sup (torusLinks (2 * M)).length X →
        (quaternionHaar (torusLinks (2 * M)).length (polyMul X
          (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks (2 * M)) (2 * M) β K)
            (torusPlaquettes (2 * M))))).eqv
        (quaternionHaar (torusLinks (2 * M)).length (polyMul (rcomp r X)
          (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) (2 * M) β K)
            (torusPlaquettes (2 * M))))) :=
  YMGap.Continuum.SU2TorusRPPermX.perm_haarX (2 * M) β K _ (YMGap.Continuum.SU2TorusRPTorusZ.lay_perm hM) rfl
    (torusLinks_nodup _) (YMGap.Continuum.SU2TorusRPTorusZ.plaqL_mem hM)

/-- Positive links land in the first `|Pt|` layout blocks, so under `imap r` a torus observable on positive links
becomes one on the first `|Pt|` blocks. -/
theorem pos_idx (ℓ : Z4Link) (h : ℓ ∈ Pt M) :
    (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).idxOf ℓ < (Pt M).length := by
  rw [List.append_assoc]
  exact (YMGap.Continuum.SU2TorusRPSwap.idx_mem ℓ _ [] (Pt M) h).2

theorem pos_imap (r : List (QuaternionBlockInvolution (torusLinks (2 * M)).length))
    (hr : ∀ ℓ, imap r ((torusLinks (2 * M)).idxOf ℓ) = (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).idxOf ℓ)
    (ℓ : Z4Link) (h : ℓ ∈ Pt M) : imap r ((torusLinks (2 * M)).idxOf ℓ) < (Pt M).length := by
  rw [hr]; exact pos_idx ℓ h

end YMGap.Continuum.SU2TorusRPTorusX

#print axioms YMGap.Continuum.SU2TorusRPTorusX.torus_X
#print axioms YMGap.Continuum.SU2TorusRPTorusX.pos_imap
