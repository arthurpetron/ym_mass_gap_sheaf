/-
The corrected R3 analytic atom: the `RC`-order ↔ rational-`distSqQ` modulus bridge.

# What this module discharges

`Continuum/WilsonLinearFC.lean` names R3 as the single blocking analytic residual
for the CONTINUOUS functional calculus: converting an `RC`-order self-inner bound
`RCle ‖z‖²_RC (ofQ' B)` into an eventual rational squared-distance modulus at
representatives (the datum that builds `PolyImageCauchy` and passes self-adjointness
/ norm bounds through the carrier limit).

The `RCDistBridge.toDistSqModulus` field there is stated on the RAW completed inner
product `cinnerCompl x y` yet claims to extract `distSqQ (x.seq n) (y.seq n)`.  Those
two objects are NOT equal: `⟨x,y⟩ ≠ ‖x − y‖²`.  The HONEST bridge must be stated on
the DIFFERENCE `cSub ⟦u⟧ ⟦v⟧`, and the extracted index is REINDEXED by `QMhat`
(the cofinal directed-core selector of `ofQ'CauchySeq`).

This module states and PROVES that corrected difference-form bridge.  Its content
rests on one definitional identity — the self-inner product of a difference IS the
`CReal` limit of the rational squared-distance sequence:

    cinnerRep (u−v) (u−v)  =  ofQ'CauchySeq (n ↦ distSqQ (uₙ) (vₙ))

(by `rfl`, since `distSqQ a b := B (sub a b) (sub a b)` and
`(cAddCauchy u (cNegCauchy v)).seq n = sub (uₙ) (vₙ)`) — plus the `RCle`↔`leEv`
computation rule and the constant-approximation of `ofQ'`.  No Cauchy–Schwarz, no
`sqrt`, no `RC` product is needed for the difference-form bridge.

# Genuine content proved here (green)

  * `Q'.le_of_forall_pos_add` — the rational Archimedean upper bound
    `(∀ ε>0, p ≤ q + ε) → p ≤ q`, a one-shot instance of `le_of_le_add_mul_invSucc`.
  * `RCofQ'_le_reflect` — reflects `RCle ⟦ofQ' p⟧ ⟦ofQ' q⟧` back to `p ≤ q`
    (the converse of the already-present forward `ofQ'_le_ofQ'`).
  * `cinnerRep_subCauchy` / `cinnerCompl_cSub` — the definitional (C) identity, at
    the representative and the completion level.
  * `distSqQ_modulus_of_RCle` — the corrected difference-form R3 bridge.
  * `rcDistBridge` — a genuine inhabitant of the corrected bridge interface
    `RCDistBridgeCorrected`.

# What remains cross-module (out of scope here, NOT a residual of R3)

The consuming assembly `polyApply_psub` / `polyNormBound` / `carrierLimit`
(`Continuum/ContinuousFCCarrierLimit.lean`, `Continuum/ContinuousFunctionalCalculusForm.lean`)
is pure plumbing over already-proved lemmas; it needs `polyApply` run over a
`LinearTransferOperator` (which supplies `T_smul`), not an `AdditiveTransferOperator`.
That operator-type switch lives in those modules, not here.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.SelfAdjointHamiltonian

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress

/-! ## Atom (A): the rational Archimedean upper bound -/

namespace YMGap.Constructive.Q'

/-- **Rational Archimedean upper bound.**  If `p ≤ q + ε` for every positive `ε`,
then `p ≤ q`.  A one-shot instance of `le_of_le_add_mul_invSucc` (coefficient `1`),
specialising `ε := 1/(N+1)` and using `1·(1/(N+1)) ≃ 1/(N+1)`. -/
theorem le_of_forall_pos_add {p q : Q'}
    (h : ∀ ε : Q', (0 : Q') < ε → p ≤ q + ε) : p ≤ q := by
  refine Q'.le_of_le_add_mul_invSucc p q 1 ?_
  intro N
  have hle : p ≤ q + Q'.invSucc N := h (Q'.invSucc N) (Q'.invSucc_pos N)
  have hY : (Q'.ofNat 1 * Q'.invSucc N).eqv (Q'.invSucc N) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (Q'.invSucc N) (by decide))
      (Q'.one_mul_eqv (Q'.invSucc N))
  have hb : (q + Q'.invSucc N).eqv (q + Q'.ofNat 1 * Q'.invSucc N) :=
    Q'.add_eqv_congr_left q (Q'.invSucc N) (Q'.ofNat 1 * Q'.invSucc N) (Q'.eqv_symm hY)
  exact le_of_le_eqv hle hb

end YMGap.Constructive.Q'

namespace YMGap.Continuum.GNSQuotient

namespace GNSData

variable (D : GNSData)

/-! ## Atom (B): reflecting the constant `RC` order back to `Q'` -/

/-- **`RCle`-reflection for constants.**  `RCle ⟦ofQ' p⟧ ⟦ofQ' q⟧` forces `p ≤ q`.
The converse of the forward embedding `ofQ'_le_ofQ' ∘ leEv_of_le`. -/
theorem RCofQ'_le_reflect {p q : Q'}
    (h : CReal.RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' p))
                    (Quotient.mk CReal.crealSetoid (CReal.ofQ' q))) : p ≤ q := by
  rw [CReal.RCle_mk] at h
  refine Q'.le_of_forall_pos_add ?_
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact hN N (Nat.le_refl N)

/-! ## (C) The difference-inner identity

`subCauchy u v` is the pointwise difference `u − v = u + (−v)`.  Because
`distSqQ a b := B (sub a b) (sub a b)` and `(subCauchy u v).seq n = sub (uₙ) (vₙ)`
definitionally, the representative inner-product sequence of `(u−v)` against itself
IS the rational squared-distance sequence — no Cauchy–Schwarz needed. -/

/-- The pointwise difference of two Cauchy representatives, `u − v := u + (−v)`. -/
def subCauchy (u v : CauchyGNS D) : CauchyGNS D := D.cAddCauchy u (D.cNegCauchy v)

/-- The rep-level inner-product sequence of the difference against itself IS the
rational squared-distance sequence (definitional). -/
theorem cInnerSeq_subCauchy (u v : CauchyGNS D) :
    D.cInnerSeq (D.subCauchy u v) (D.subCauchy u v)
      = fun n => D.distSqQ (u.seq n) (v.seq n) := rfl

/-- The `QCauchy` witness for the rational squared-distance sequence (reused verbatim
from the difference's inner-product Cauchy modulus). -/
def distSqSeqCauchy (u v : CauchyGNS D) :
    CReal.QCauchy (fun n => D.distSqQ (u.seq n) (v.seq n)) :=
  D.cInnerQCauchy (D.subCauchy u v) (D.subCauchy u v)

/-- The cofinal `QMhat` reindexing that `ofQ'CauchySeq` applies to the
squared-distance sequence. -/
def reindex (u v : CauchyGNS D) (n : Nat) : Nat :=
  CReal.QMhat (fun k => D.distSqQ (u.seq k) (v.seq k)) (D.distSqSeqCauchy u v) n

/-- **(C1) — representative level.**  The completed self-inner product of the
difference is the `CReal` limit of the rational squared-distance sequence. -/
theorem cinnerRep_subCauchy (u v : CauchyGNS D) :
    D.cinnerRep (D.subCauchy u v) (D.subCauchy u v)
      = CReal.ofQ'CauchySeq (fun n => D.distSqQ (u.seq n) (v.seq n))
          (D.distSqSeqCauchy u v) := rfl

/-- **(C2) — completion level.**  On `cSub ⟦u⟧ ⟦v⟧` the completed inner product is
the class of the `CReal` limit of the squared-distance sequence. -/
theorem cinnerCompl_cSub (u v : CauchyGNS D) :
    D.cinnerCompl
        (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v))
        (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v))
      = Quotient.mk CReal.crealSetoid
          (CReal.ofQ'CauchySeq (fun n => D.distSqQ (u.seq n) (v.seq n))
            (D.distSqSeqCauchy u v)) := rfl

/-! ## (D) The corrected difference-form R3 bridge -/

/-- **R3, corrected.**  If the completed self-inner product of the difference
`u − v` is `RCle` a constant rational bound `Bq`, then at representatives (along
the cofinal `QMhat` reindexing) the rational squared distance is eventually
`≤ Bq + ε` for every `ε > 0`.

Proof: rewrite the LHS by the definitional identity (C2), collapse `RCle ⟦·⟧ ⟦·⟧`
to `leEv` (`RCle_mk`), and read off `leEv` — whose approximations are exactly
`distSqQ (u_{QMhat n}) (v_{QMhat n})` on the left and the constant `Bq` on the
right. -/
theorem distSqQ_modulus_of_RCle (u v : CauchyGNS D) (Bq : Q')
    (h : CReal.RCle
          (D.cinnerCompl
            (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v))
            (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v)))
          (Quotient.mk CReal.crealSetoid (CReal.ofQ' Bq))) :
    ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      D.distSqQ (u.seq (D.reindex u v n)) (v.seq (D.reindex u v n)) ≤ Bq + ε := by
  rw [D.cinnerCompl_cSub u v, CReal.RCle_mk] at h
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => hN n hn⟩

/-! ## The inhabited corrected bridge interface -/

/-- **The corrected R3 interface** (the honest replacement for
`WilsonLinearFC.RCDistBridge.toDistSqModulus`): stated on the DIFFERENCE `cSub`
and with the `QMhat`-reindexed representative index. -/
structure RCDistBridgeCorrected (D : GNSData) : Type where
  /-- From a difference-form `RC`-order bound to the reindexed rational
  squared-distance modulus at representatives. -/
  toDistSqModulus :
    ∀ (u v : CauchyGNS D) (Bq : Q'),
      CReal.RCle
        (D.cinnerCompl
          (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v))
          (D.cSub (Quotient.mk (cauchySetoid D) u) (Quotient.mk (cauchySetoid D) v)))
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' Bq)) →
      ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        D.distSqQ (u.seq (D.reindex u v n)) (v.seq (D.reindex u v n)) ≤ Bq + ε

/-- **The corrected R3 bridge is genuinely inhabited** (not a named residual). -/
def rcDistBridge : RCDistBridgeCorrected D :=
  ⟨D.distSqQ_modulus_of_RCle⟩

end GNSData

end YMGap.Continuum.GNSQuotient

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.le_of_forall_pos_add
#print axioms YMGap.Continuum.GNSQuotient.GNSData.RCofQ'_le_reflect
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerRep_subCauchy
#print axioms YMGap.Continuum.GNSQuotient.GNSData.cinnerCompl_cSub
#print axioms YMGap.Continuum.GNSQuotient.GNSData.distSqQ_modulus_of_RCle
#print axioms YMGap.Continuum.GNSQuotient.GNSData.rcDistBridge
