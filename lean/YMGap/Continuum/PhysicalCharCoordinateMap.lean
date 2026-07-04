/-
**Milestone 11.16(A): inhabiting `PhysicalCharacterCoordinateMap` at the
character model.**

`PhysicalWilsonBridge.PhysicalCharacterCoordinateMap H op w t ht N` is the
Type-level datum (the two diagonal Schur / Peter–Weyl identities realized inside
the completed GNS inner product `H.hilbert.cinner`) that, via
`physicalCharacterDiagResolution`, discharges the ENTIRE arbitrary-`x`
`CharacterDiagResolution op rcScaleResidualPlus w N` and fires the operator-form
gap.  The structure is parametric in `H`.

This module CLOSES the datum, in equality form, at the CHARACTER MODEL
`H = charComplete t ht N`, `op = charTransfer w hw0 hw1 t ht N`, by reusing the
already-proved, axiom-clean fields from `WilsonSchurIdentities`:

  * `coord      := charCoord N`;
  * `schur_self := charSchurSelf t ht N`   (a pure `RCfinSum`↔`csum` repackaging);
  * `schur_T    := charSchurT w hw0 hw1 t ht N`   (via `q_rearrange_schurT`).

The field types match verbatim up to the definitional unfolding
`charCoord N x i ≡ x i.val` and `(charComplete …).hilbert.cinner ≡
(charHilbert …).cinner`.  No new mathematics: the payoff
`physicalCharCoordFormGap` reproduces the pre-existing
`WilsonSchurIdentities.wilsonSchurFormGap` THROUGH the named milestone-A
intermediary (`physicalCharacterDiagResolution` ∘ `physicalWilsonFormGap`).

# Honest scope

  * **CLOSED (equality form):** milestone A — `PhysicalCharacterCoordinateMap` is
    inhabited at the character model; the whole `CharacterDiagResolution` and the
    operator-form gap fire on `vac⊥`.
  * **NOT closed (unchanged):** inhabiting the datum at the PHYSICAL rational-`E_Λ`
    Wilson `H`.  There `schur_self` demands a rational class equal to an irrational
    `Σ ⟦reflWeight·c²⟧` — the load-bearing obstruction
    `PhysicalWilsonBridge.HeatKernelReferenceWeight`, deliberately NOT inhabited
    (and NOT touched here).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`, no
`native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.PhysicalWilsonBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.RCScaleClose
open YMGap.Continuum.WilsonCharBridge
open YMGap.Continuum.WilsonSchurIdentities
open YMGap.Continuum.PhysicalWilsonBridge

namespace YMGap.Continuum.PhysicalCharCoordinateMap

/-- **Milestone 11.16(A): the physical character coordinate map, INHABITED at the
character model.**  The three fields of `PhysicalCharacterCoordinateMap` on
`H = charComplete t ht N`, `op = charTransfer w hw0 hw1 t ht N` are exactly the
already-proved, axiom-clean `charCoord` / `charSchurSelf` / `charSchurT`.  The
`schur_self`/`schur_T` equalities match the structure fields verbatim up to the
definitional unfolding `charCoord N x i ≡ x i.val`.  No new content. -/
def physicalCharCoordMap
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) :
    PhysicalCharacterCoordinateMap
      (charComplete t ht N) (charTransfer w hw0 hw1 t ht N) w t ht N where
  coord      := charCoord N
  schur_self := charSchurSelf t ht N
  schur_T    := charSchurT w hw0 hw1 t ht N

/-- **The whole `CharacterDiagResolution` discharged at the character model.**
Feeds the inhabited coordinate map into `physicalCharacterDiagResolution`; the
entire arbitrary-`x` Parseval datum on the character `cinner` is now closed. -/
def physicalCharCoordDiagResolution
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) :
    CharacterDiagResolution (charTransfer w hw0 hw1 t ht N) rcScaleResidualPlus w N :=
  physicalCharacterDiagResolution (charTransfer w hw0 hw1 t ht N) w t ht N
    (physicalCharCoordMap w hw0 hw1 t ht N)

/-- **Milestone-A payoff: the operator-form gap through the named intermediary.**
Composes `physicalWilsonFormGap` with the inhabited coordinate map and the proved
scalar monotonicity `rscale_mono`: on `vac⊥`, `⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩`.
Reproduces `WilsonSchurIdentities.wilsonSchurFormGap` via the milestone-A datum
`PhysicalCharacterCoordinateMap`. -/
def physicalCharCoordFormGap
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) :
    TransferFormGapResidual
      (excitedCharSpectralGapData (charTransfer w hw0 hw1 t ht N) w hw0 hw1 N) :=
  physicalWilsonFormGap (charTransfer w hw0 hw1 t ht N) w t ht hw0 hw1 N
    rscale_mono
    (physicalCharCoordMap w hw0 hw1 t ht N)

end YMGap.Continuum.PhysicalCharCoordinateMap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PhysicalCharCoordinateMap.physicalCharCoordMap
#print axioms YMGap.Continuum.PhysicalCharCoordinateMap.physicalCharCoordDiagResolution
#print axioms YMGap.Continuum.PhysicalCharCoordinateMap.physicalCharCoordFormGap
