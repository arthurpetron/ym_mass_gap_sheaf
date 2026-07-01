/-
Track B+RepTheory / R2 — **upgrading the O(4)-restoration rotation slot from a
non-invertible `*`-ENDOMORPHISM to a genuine invertible order-4 `*`-AUTOMORPHISM.**

# What this closes

`O4ClauseStrength.lean` (residual #1, lines 31–36) supplies the strong O(4)-restoration
certificate `StrongO4Restoration` with the spin-doubling endomorphism `doubleHom :
χ_s ↦ χ_{2s}` in the rotation slot.  `doubleHom` is a genuine NON-identity unital
`*`-hom, but it is NOT invertible — it has no two-sided `ObsHom` inverse, so it is not
a `*`-automorphism, and it does not model a bona-fide H(4) lattice rotation (which
PERMUTES the directed edges at a site and has order 4).

This module supplies the missing object: on the **4-directed-edge product algebra**
`prodCharAlg4` (componentwise from `charAlg`, one `Nat` spin index per directed edge
`+x,+y,−x,−y`), the **cyclic edge shift** `rot4 : (a,b,c,d) ↦ (d,a,b,c)` is a genuine
invertible order-4 `*`-automorphism:

  * `rot4Inv = rot4³ : (a,b,c,d) ↦ (b,c,d,a)` is a two-sided `ObsHom` inverse
    (`rot4_leftInv`, `rot4_rightInv`) — the exact property `doubleHom` lacks;
  * `rot4⁴ = id` (`rot4_order4`), and the order is EXACTLY 4 (`rot4_order_exactly4`,
    `decide` on the orbit of `(1,0,0,0)`), a genuine non-trivial permutation.

All hom laws and the invertibility/order-4 laws are `rfl` (the componentwise shift
commutes with the componentwise Clebsch–Gordan product / unit / involution).

# The anisotropy content (reusing the O4ClauseStrength pipeline verbatim)

`prodCharFunc wx wy` is the anisotropic product heat-kernel functional: x-slots (1,3)
carry weight `wx`, y-slots (2,4) carry `wy`.  The named anisotropy defect
`anisoDefect (prodCharFunc wx wy) rot4 genX4` with `genX4 = χ₄` on the +x edge has the
closed form `|dimQ 4 · wy²⁴ − dimQ 4 · wx²⁴| = 5·|wy²⁴ − wx²⁴|` (`c4 4 = 24`): the
rotation moves the χ₄ excitation from an x-slot to a y-slot, exposing the weight
mismatch.  It is strictly positive iff `wx ≠ wy` and `→ 0` as `wy → wx`
(isotropization under blocking).  Concretely `wx = 1/2`, `wy = 1/3` gives a closed
strictly-positive `Q'`.  The entire `anisoDefect → anisoDecay →
rubricO4Restoration_of_strong` pipeline is reused unchanged; no new analytic content.

The upgraded certificate `StrongO4RestorationAut` extends `StrongO4Restoration` with
the two-sided inverse and order-4 data, and fires the same Clay clause through the
inherited base.

# Honest residuals (frontier UNCHANGED — do not overclaim)

This closes residual #1 only (invertible order-4 `*`-automorphism permuting edge
generators).  Residual #2 (the physical Davoudi–Savage O(a²) isotropization running is
a MODEL schedule via `anisoDecay`; `O4RestorationProgress.CouplingRunning.betaDrop_nonneg`
untouched) and the Hasenbusch–Vicari AF/Gaussian-UV caveat are UNCHANGED.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'`/`Nat`/`Prod` arithmetic and the reused proved AF-decay pipeline; every
load-bearing law is `rfl`/`decide`.  All witnesses are `Type`-level data.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.
-/

import YMGap.Continuum.O4ClauseStrength

namespace YMGap.Continuum.H4RotationAuto

open YMGap.Constructive
open YMGap.Continuum.ObservableMeasure (ProbFunctional ObsAlg ObsHom)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.O4ClauseStrength

/-! ## 1. The 4-directed-edge product algebra (componentwise from `charAlg`) -/

/-- The observable `*`-algebra of the four directed edges `(+x, +y, −x, −y)` at a
site: carrier `Nat × Nat × Nat × Nat` (one SU(2) spin index per directed edge), unit
`(χ_0,χ_0,χ_0,χ_0)`, componentwise Clebsch–Gordan product, and `star = id` (real
characters componentwise). -/
def prodCharAlg4 : ObsAlg where
  carrier := Nat × Nat × Nat × Nat
  one     := (0, 0, 0, 0)
  mul     := fun (a,b,c,d) (a',b',c',d') =>
               (charAlg.mul a a', charAlg.mul b b', charAlg.mul c c', charAlg.mul d d')
  star    := fun x => x

/-! ## 2. The rotation, its two-sided inverse, and genuine order 4 -/

/-- **The H(4) cyclic edge shift** `(a,b,c,d) ↦ (d,a,b,c)` as a unital `*`-hom.  All
three hom laws are `rfl` (the shift commutes with the componentwise product / unit /
involution). -/
def rot4 : ObsHom prodCharAlg4 prodCharAlg4 where
  map := fun (a,b,c,d) => (d,a,b,c)
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

/-- **The inverse rotation** `rot4³ : (a,b,c,d) ↦ (b,c,d,a)` — a bona-fide two-sided
`ObsHom` inverse of `rot4`. -/
def rot4Inv : ObsHom prodCharAlg4 prodCharAlg4 where
  map := fun (a,b,c,d) => (b,c,d,a)
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

/-- `rot4Inv ∘ rot4 = id` — the left inverse law (`rfl`, componentwise). -/
theorem rot4_leftInv : ∀ x, rot4Inv.map (rot4.map x) = x := fun _ => rfl

/-- `rot4 ∘ rot4Inv = id` — the right inverse law (`rfl`, componentwise).  Together
with `rot4_leftInv` this is the two-sided invertibility that `doubleHom` lacks. -/
theorem rot4_rightInv : ∀ x, rot4.map (rot4Inv.map x) = x := fun _ => rfl

/-- `rot4⁴ = id` — genuine order 4 (`rfl`, componentwise). -/
theorem rot4_order4 : ∀ x, rot4.map (rot4.map (rot4.map (rot4.map x))) = x := fun _ => rfl

/-- `rot4` is a genuinely non-trivial permutation: it moves `(χ_1,χ_0,χ_0,χ_0)`. -/
theorem rot4_nontrivial : ∃ x, rot4.map x ≠ x :=
  ⟨(1,0,0,0), by
    show ((0:Nat),(1:Nat),(0:Nat),(0:Nat)) ≠ ((1:Nat),(0:Nat),(0:Nat),(0:Nat))
    decide⟩

/-- **The order is EXACTLY 4** (not merely `≤ 4`): the three non-identity iterates of
`rot4` on `(χ_1,χ_0,χ_0,χ_0)` are all distinct from the start. -/
theorem rot4_order_exactly4 :
    rot4.map (1,0,0,0) ≠ (1,0,0,0)
  ∧ rot4.map (rot4.map (1,0,0,0)) ≠ (1,0,0,0)
  ∧ rot4.map (rot4.map (rot4.map (1,0,0,0))) ≠ (1,0,0,0) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((0:Nat),(1:Nat),(0:Nat),(0:Nat)) ≠ ((1:Nat),(0:Nat),(0:Nat),(0:Nat)); decide
  · show ((0:Nat),(0:Nat),(1:Nat),(0:Nat)) ≠ ((1:Nat),(0:Nat),(0:Nat),(0:Nat)); decide
  · show ((0:Nat),(0:Nat),(0:Nat),(1:Nat)) ≠ ((1:Nat),(0:Nat),(0:Nat),(0:Nat)); decide

/-! ## 3. The anisotropic product heat-kernel functional -/

/-- The **anisotropic product heat-kernel functional**: x-slots (1,3) carry weight
`wx`, y-slots (2,4) carry `wy`.  Each factor is the diagonal SU(2) heat-kernel value
`dimQ s · w^{C₄(s)}`; the product is normalized (`= 1` at the unit) and positive on
`a*·a` (`star = id` sends each slot to `χ_0`, so every factor is nonnegative). -/
def prodCharFunc (wx wy : Q') (hx : (0:Q') ≤ wx) (hy : (0:Q') ≤ wy) :
    ProbFunctional prodCharAlg4 where
  E := fun (a,b,c,d) => (dimQ a * qpow wx (c4 a)) * (dimQ b * qpow wy (c4 b))
                       * (dimQ c * qpow wx (c4 c)) * (dimQ d * qpow wy (c4 d))
  normalized := by
    show (dimQ 0 * qpow wx (c4 0)) * (dimQ 0 * qpow wy (c4 0))
       * (dimQ 0 * qpow wx (c4 0)) * (dimQ 0 * qpow wy (c4 0)) = 1
    rw [dimQ_zero, c4_zero, qpow_zero wx, qpow_zero wy]
    decide
  positive := fun (a,b,c,d) => by
    show (0:Q') ≤
        (dimQ (charAlg.mul a a) * qpow wx (c4 (charAlg.mul a a)))
      * (dimQ (charAlg.mul b b) * qpow wy (c4 (charAlg.mul b b)))
      * (dimQ (charAlg.mul c c) * qpow wx (c4 (charAlg.mul c c)))
      * (dimQ (charAlg.mul d d) * qpow wy (c4 (charAlg.mul d d)))
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (dimQ_nonneg _) (qpow_nonneg wx hx _))
          (Q'.mul_nonneg _ _ (dimQ_nonneg _) (qpow_nonneg wy hy _)))
        (Q'.mul_nonneg _ _ (dimQ_nonneg _) (qpow_nonneg wx hx _)))
      (Q'.mul_nonneg _ _ (dimQ_nonneg _) (qpow_nonneg wy hy _))

/-! ## 4. The L=4 generator and the named anisotropy defect -/

/-- The designated L=4 first-cubic-harmonic generator `χ_4` on the `+x` edge. -/
def genX4 : prodCharAlg4.carrier := (4, 0, 0, 0)

/-- The named anisotropy defect of `prodCharFunc` under the invertible rotation
`rot4` at `genX4`: `rot4` moves the χ₄ excitation from an x-slot to a y-slot, giving
the closed form `5·|wy²⁴ − wx²⁴|` (`c4 4 = 24`). -/
def prodAniso (wx wy : Q') (hx : (0:Q') ≤ wx) (hy : (0:Q') ≤ wy) : Q' :=
  anisoDefect (prodCharFunc wx wy hx hy) rot4 genX4

/-- Concrete x-weight `wx = 1/2` (`= heatWeight`). -/
def wX : Q' := Q'.mkPos 1 2 (by decide)
/-- Concrete y-weight `wy = 1/3` (`≠ wX`, so the anisotropy is strictly positive). -/
def wY : Q' := Q'.mkPos 1 3 (by decide)

theorem hwX : (0:Q') ≤ wX := by decide
theorem hwY : (0:Q') ≤ wY := by decide

theorem prodAniso_nonneg : (0:Q') ≤ prodAniso wX wY hwX hwY :=
  anisoDefect_nonneg _ _ _

set_option maxRecDepth 20000 in
/-- **Genuine positivity**: `prodAniso = 5·((1/2)²⁴ − (1/3)²⁴) > 0`.  The rotation
really breaks the anisotropic functional at the L=4 channel. -/
theorem prodAniso_pos : (0:Q') < prodAniso wX wY hwX hwY := by decide

/-! ## 5. The upgraded certificate: `StrongO4Restoration` + invertibility -/

/-- **Strong O(4)-restoration certificate WITH invertibility.**  Extends the base
`StrongO4Restoration` with a two-sided `ObsHom` inverse `rInv` of the rotation `r` and
a proof that `r` has order 4 — upgrading the rotation slot from a non-invertible
`*`-endomorphism to a genuine invertible order-4 `*`-automorphism. -/
structure StrongO4RestorationAut : Type 1 extends StrongO4Restoration where
  rInv       : ObsHom toStrongO4Restoration.A toStrongO4Restoration.A
  r_leftInv  : ∀ a, rInv.map (r.map a) = a
  r_rightInv : ∀ a, r.map (rInv.map a) = a
  r_order4   : ∀ a, r.map (r.map (r.map (r.map a))) = a

/-- The Clay clause fires through the inherited base certificate (wiring unchanged). -/
theorem rubricO4Restoration_of_strongAut (S : StrongO4RestorationAut) :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  rubricO4Restoration_of_strong S.toStrongO4Restoration

/-- **Concrete inhabitant**: the invertible order-4 rotation `rot4` on the
4-directed-edge product algebra, dropped into the rotation slot in place of the
non-invertible `doubleHom`. -/
def strongAut_prodCharAlg4 : StrongO4RestorationAut where
  toStrongO4Restoration :=
    { A := prodCharAlg4
      E := prodCharFunc wX wY hwX hwY
      r := rot4
      g := genX4
      r_nontrivial     := rot4_nontrivial
      D                := anisoDecay (prodAniso wX wY hwX hwY) prodAniso_nonneg
      coeff0_eqv_aniso := anisoDecay_coeff0_eqv _ prodAniso_nonneg
      aniso_pos        := prodAniso_pos }
  rInv       := rot4Inv
  r_leftInv  := rot4_leftInv
  r_rightInv := rot4_rightInv
  r_order4   := rot4_order4

/-- **Non-vacuity capstone**: the strengthened Clay clause fires from a certificate
whose rotation is a genuinely invertible order-4 `*`-automorphism. -/
theorem rubricO4Restoration_strong_prodCharAlg4 :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  rubricO4Restoration_of_strongAut strongAut_prodCharAlg4

/-- **The exposed content**: strictly-positive L=4 anisotropy of a genuinely
invertible order-4 rotation, decaying to 0. -/
theorem strongAut_content :
    (0:Q') < O4RestorationAF.breakCoeff strongAut_prodCharAlg4.D 0
  ∧ (O4RestorationAF.breakCoeff strongAut_prodCharAlg4.D 0).eqv (prodAniso wX wY hwX hwY)
  ∧ (∀ a, rot4Inv.map (rot4.map a) = a)
  ∧ (∀ a, rot4.map (rot4.map (rot4.map (rot4.map a))) = a)
  ∧ (∃ a, rot4.map a ≠ a)
  ∧ (∀ ε:Q', 0 < ε → ∃ N, ∀ k, N ≤ k →
        O4RestorationAF.breakCoeff strongAut_prodCharAlg4.D k < ε) := by
  have h := strong_defect_is_positive_aniso strongAut_prodCharAlg4.toStrongO4Restoration
  exact ⟨h.1, h.2.1, rot4_leftInv, rot4_order4, rot4_nontrivial, h.2.2.2⟩

/-! ## Axiom-dependency gates (AGENTS.md Rules 1, 8) -/

#print axioms prodCharAlg4
#print axioms rot4
#print axioms rot4Inv
#print axioms rot4_leftInv
#print axioms rot4_rightInv
#print axioms rot4_order4
#print axioms rot4_nontrivial
#print axioms rot4_order_exactly4
#print axioms prodCharFunc
#print axioms prodAniso_nonneg
#print axioms prodAniso_pos
#print axioms rubricO4Restoration_of_strongAut
#print axioms strongAut_prodCharAlg4
#print axioms rubricO4Restoration_strong_prodCharAlg4
#print axioms strongAut_content

end YMGap.Continuum.H4RotationAuto
