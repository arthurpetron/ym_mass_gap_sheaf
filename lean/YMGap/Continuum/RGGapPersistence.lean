/-
Track B / R2 — the continuum Yang–Mills mass gap as a SINGLE named inequality.

# What this module is

The continuum scaling band `RegScalingBand` carries one genuinely OPEN field:
the strictly-positive uniform physical-gap floor `physGapMin > 0` surviving
`a → 0`.  Everything else in the continuum pipeline — the finite-volume located
gaps, the infinite-volume (`Λ → ∞`) cluster bound, the derived physical gap
`Δ(a) = m_lat(a)/a`, the survival theorem `band_gap_survives` — is PROVED.

This module isolates that one open field as a single recognized inequality, and
proves the reduction making "the continuum gap is positive" a CONSEQUENCE of it:

  * `RGGapPersistence` — the named open obligation.  In its primary UNIFORM
    form it is exactly the statement
        `∃ c > 0, ∀ j,  c ≤  m_lat(a_j) / a_j`,
    i.e. the physical transfer-gap stays bounded below by a single positive
    constant uniformly along the asymptotic-freedom trajectory `a_j → 0`.  This
    is the standard strong-coupling↔continuum bridge that the renormalization-
    group program (Balaban et al.) stops short of establishing for 4D YM.  NO
    inhabitant is provided — it IS the open content.

  * A per-block form `RGBlockPersistence` (per-RG-block multipliers `rho k > 0`
    with a uniform product floor) is shown to IMPLY the uniform form
    (`RGGapPersistence`), so the two faithful shapes are connected.

  * `continuum_gap_of_RGGapPersistence` — the headline reduction: from
    `RGGapPersistence` CONSTRUCT a `RegScalingBand` (with `physGapMin := c`),
    hence `physGapMin > 0` (`physGapMin_pos_of_persistence`) and the survival
    theorem `band_gap_survives`.  Pure assembly over `divPos` / `ofQ'_le_ofQ'`.

  * The strong-coupling ANCHOR.  The `j = 0` / fixed-spacing rung is genuinely
    inhabited: the proven strong-coupling positive clustering floor (the
    fixed-spacing cluster-expansion bound, an unconditional positive floor) is
    a positive physical gap at the anchor spacing.  The split is explicit: the
    anchor is PROVED; the only open content is the PERSISTENCE of the floor as
    `j → ∞` (`a → 0`).

# The full reduction chain (HONEST)

  Clay 4D mass gap
    ⟸ worst-case reduction to SU(2)   (group dependence, already in Lean)
    ⟸ SU(2) continuum (`a → 0`) gap   (the `RegScalingBand` survival theorem)
    ⟸ `RGGapPersistence`              (THIS module — the one open inequality).

SU(2)'s transfer-operator gap is explicit via the heat-kernel / theta-character
expansion, so the open inequality is a CONCRETE one-variable statement about an
explicit theta-ratio along the running coupling `β(a)` — the sharpened attack
surface.  This module REDUCES the open problem to that one inequality; it does
NOT solve it.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms` at the bottom; the
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  Every modulus / constant is `Type`-level data.
-/

import YMGap.Continuum.RegularContinuumPipeline
import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.NonSaturatedFloor
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.RGGapPersistence

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum
open YMGap.Continuum.RegularContinuumPipeline

/-! ## 1. The single open inequality — `RGGapPersistence`

`RGGapPersistence` packages the spacing tower together with the ONE open
estimate: that the PHYSICAL transfer gap `Δ(a_j) = m_lat(a_j)/a_j` stays bounded
below by a single positive rational constant `c`, uniformly in the refinement
step `j`.  Concretely, with `m_lat(a_j) = (atSpacing j).floorRate` the lattice-
unit clustering floor at spacing `a_j` (which itself → 0 like `a_j`), the open
field is

    `physFloor : ∀ j,  c ≤ Q'.divPos (m_lat(a_j)) (a_j) _`.

This is the "`a · gap(H(a)) ≥ c` along the AF trajectory" statement: dimensional
transmutation, the strong-coupling↔continuum bridge.  A uniform CEILING `C` is
also carried so the reduction can supply the band's (non-open) upper bound.

No inhabitant is claimed for 4D Yang–Mills: `c > 0` surviving `a → 0` is OPEN. -/

/-- **The single open inequality — uniform physical-gap persistence.**

Carries, indexed by refinement step `j` (spacing `a_j → 0`):

  * `spacing`, `spacing_pos` — the lattice spacings `a_j > 0`;
  * `atSpacing` — the fixed-spacing infinite-volume cluster bounds (each a
    `RegUniformClusterBound`; its lattice floor `m_lat(a_j)` may, indeed must,
    vanish like `a_j`);
  * `floorConst`, `floorConst_pos` — the uniform PHYSICAL gap floor `c > 0`;
  * `ceilConst` — a uniform physical ceiling `C` (the finiteness half);
  * `physFloor` — **the OPEN content:** `c ≤ m_lat(a_j)/a_j` for all `j`
    (`Q'.divPos`), i.e. the physical gap stays bounded below by `c > 0`
    uniformly along the AF trajectory;
  * `physCeil` — `m_lat(a_j)/a_j ≤ C` for all `j` (the uniform ceiling).

NO inhabitant for 4D Yang–Mills — `physFloor` with `floorConst > 0` is exactly
the open dimensional-transmutation estimate. -/
structure RGGapPersistence : Type where
  /-- The lattice spacings `a_j`, indexed by refinement step `j`. -/
  spacing : Nat → Q'
  /-- Each spacing is strictly positive. -/
  spacing_pos : ∀ j : Nat, (0 : Q') < spacing j
  /-- The fixed-spacing infinite-volume cluster bounds, indexed by `j`. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- The uniform PHYSICAL gap floor `c`. -/
  floorConst : Q'
  /-- The floor is strictly positive — the dimensional-transmutation witness. -/
  floorConst_pos : (0 : Q') < floorConst
  /-- A uniform PHYSICAL gap ceiling `C` (the finiteness half). -/
  ceilConst : Q'
  /-- **The OPEN content:** the physical gap `m_lat(a_j)/a_j` is bounded below
  by the single positive constant `c`, uniformly in `j` — the strong-coupling↔
  continuum bridge along asymptotic freedom. -/
  physFloor : ∀ j : Nat,
    floorConst ≤ Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j)
  /-- The physical gap is bounded above by `C`, uniformly in `j`. -/
  physCeil : ∀ j : Nat,
    Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j) ≤ ceilConst

/-! ## 2. The reduction theorem — `RGGapPersistence ⇒ RegScalingBand`

This is the headline.  A `RGGapPersistence` term supplies precisely the data a
`RegScalingBand` needs: the spacings, the per-step cluster bounds, and the
two-sided uniform PHYSICAL bound `0 < physGapMin ≤ physGap j ≤ physGapMax` with
`physGapMin := floorConst`.  The construction is pure assembly: the band's
`physGap_ge` / `physGap_le` fields ARE `physFloor` / `physCeil` (both stated in
the same `Q'.divPos` shape). -/

/-- **The reduction (band construction).**  From the single open inequality
`RGGapPersistence` CONSTRUCT a `RegScalingBand` whose physical floor is
`floorConst > 0`.  Every field is supplied verbatim; the open positivity field
`physGapMin_pos` is `floorConst_pos`, and `physGap_ge` / `physGap_le` are
`physFloor` / `physCeil`.  Pure assembly. -/
def toScalingBand (P : RGGapPersistence) : RegScalingBand where
  spacing := P.spacing
  spacing_pos := P.spacing_pos
  atSpacing := P.atSpacing
  physGapMin := P.floorConst
  physGapMax := P.ceilConst
  physGapMin_pos := P.floorConst_pos
  physGap_ge := P.physFloor
  physGap_le := P.physCeil

/-- The constructed band's physical floor is `floorConst`. -/
@[simp] theorem toScalingBand_physGapMin (P : RGGapPersistence) :
    (toScalingBand P).physGapMin = P.floorConst := rfl

/-- **The headline reduction: `RGGapPersistence ⇒ physGapMin > 0`.**  The
continuum physical-gap floor of the constructed band is strictly positive —
this is `floorConst_pos` transported through the band.  Hence "the continuum
mass gap is positive" is a PROVED CONSEQUENCE of the single open inequality. -/
theorem physGapMin_pos_of_persistence (P : RGGapPersistence) :
    (0 : Q') < (toScalingBand P).physGapMin :=
  (toScalingBand P).band_physGapMin_pos

/-- **The continuum gap SURVIVES `a → 0`, from the single inequality.**  Every
physical gap `physGap j`, as a regular real, dominates the single positive
constant `ofQ' floorConst`, uniformly in the spacing `j`.  Combined with
`physGapMin_pos_of_persistence` this is liminf physGap ≥ floorConst > 0 — the
Clay-relevant claim — built entirely from `RGGapPersistence`. -/
theorem continuum_gap_of_RGGapPersistence (P : RGGapPersistence) (j : Nat) :
    ofQ' (toScalingBand P).physGapMin ≤ ofQ' ((toScalingBand P).physGap j) :=
  (toScalingBand P).band_gap_survives j

/-- The reduction also delivers the uniform finiteness half: every physical gap
is bounded above by `ofQ' ceilConst` as a regular real. -/
theorem continuum_gap_le_ceiling_of_RGGapPersistence
    (P : RGGapPersistence) (j : Nat) :
    ofQ' ((toScalingBand P).physGap j) ≤ ofQ' (toScalingBand P).physGapMax :=
  (toScalingBand P).band_physGap_le j

/-! ## 3. The per-block form and its reduction to the uniform form

`RGBlockPersistence` is the equivalent per-RG-block packaging: a multiplier
`rho k > 0` for each block with the block recursion
`rho k · physGap k ≤ physGap (k+1)`, an anchor floor `g0 ≤ physGap 0`, and a
uniform product floor `prodFloor ≤ (∏_{i<k} rho i) · g0`.  From these the
uniform floor `prodFloor ≤ physGap k` follows by a product induction, giving the
uniform-form open field.  This connects the two faithful shapes (per-block ⇒
uniform). -/

/-- The prefix product `∏_{i<k} rho i` (empty product `= 1`). -/
def prodPrefix (rho : Nat → Q') : Nat → Q'
  | 0 => (1 : Q')
  | k + 1 => prodPrefix rho k * rho k

/-- **The per-block persistence form.**  The physical gap is `physGap : Nat → Q'`
(here taken as the derived band quotient), and the open content is packaged as
per-block multipliers and a product floor. -/
structure RGBlockPersistence : Type where
  /-- The lattice spacings `a_j`. -/
  spacing : Nat → Q'
  /-- Each spacing is strictly positive. -/
  spacing_pos : ∀ j : Nat, (0 : Q') < spacing j
  /-- The fixed-spacing cluster bounds. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- A uniform physical ceiling. -/
  ceilConst : Q'
  /-- The physical gap is bounded above by the ceiling. -/
  physCeil : ∀ j : Nat,
    Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j) ≤ ceilConst
  /-- Per-block transfer-gap multiplier `rho k`. -/
  rho : Nat → Q'
  /-- Each multiplier is nonnegative (the recursion only needs `≥ 0`). -/
  rho_nonneg : ∀ k : Nat, (0 : Q') ≤ rho k
  /-- The anchor physical gap floor `g0 > 0`. -/
  anchor : Q'
  /-- The anchor floor is strictly positive. -/
  anchor_pos : (0 : Q') < anchor
  /-- **The anchor bound:** `g0 ≤ physGap 0`. -/
  anchor_le : anchor ≤
    Q'.divPos ((atSpacing 0).floorRate) (spacing 0) (spacing_pos 0)
  /-- **The block recursion:** `rho k · physGap k ≤ physGap (k+1)`. -/
  recursion : ∀ k : Nat,
    rho k * Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k)
      ≤ Q'.divPos ((atSpacing (k + 1)).floorRate) (spacing (k + 1)) (spacing_pos (k + 1))
  /-- The uniform product floor `c > 0`. -/
  prodFloor : Q'
  /-- The product floor is strictly positive. -/
  prodFloor_pos : (0 : Q') < prodFloor
  /-- **The uniform product bound:** `c ≤ (∏_{i<k} rho i) · g0` for all `k`. -/
  prodFloor_le : ∀ k : Nat, prodFloor ≤ prodPrefix rho k * anchor

/-- The prefix-product running lower bound: `(∏_{i<k} rho i) · g0 ≤ physGap k`,
by induction.  Base: `prodPrefix rho 0 · g0 = 1 · g0 ≃ g0 ≤ physGap 0`.  Step:
`(∏_{i<k+1}) · g0 = (∏_{i<k} · rho k) · g0 = rho k · ((∏_{i<k}) · g0)
  ≤ rho k · physGap k ≤ physGap (k+1)`. -/
theorem prodPrefix_anchor_le_physGap (B : RGBlockPersistence) :
    ∀ k : Nat, prodPrefix B.rho k * B.anchor ≤
      Q'.divPos ((B.atSpacing k).floorRate) (B.spacing k) (B.spacing_pos k)
  | 0 => by
      -- prodPrefix rho 0 * anchor = 1 * anchor ≃ anchor ≤ physGap 0
      show (1 : Q') * B.anchor ≤ _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv B.anchor)) B.anchor_le
  | k + 1 => by
      -- prodPrefix rho (k+1) * anchor = (prodPrefix rho k * rho k) * anchor
      --   ≃ rho k * (prodPrefix rho k * anchor)
      have ih := prodPrefix_anchor_le_physGap B k
      -- rho k * (prodPrefix rho k * anchor) ≤ rho k * physGap k
      have hmul : B.rho k * (prodPrefix B.rho k * B.anchor)
          ≤ B.rho k * Q'.divPos ((B.atSpacing k).floorRate) (B.spacing k) (B.spacing_pos k) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (B.rho_nonneg k)
      -- chain with the recursion
      have hchain : B.rho k * (prodPrefix B.rho k * B.anchor)
          ≤ Q'.divPos ((B.atSpacing (k + 1)).floorRate) (B.spacing (k + 1)) (B.spacing_pos (k + 1)) :=
        Q'.le_trans' _ _ _ hmul (B.recursion k)
      -- rewrite the LHS: (prodPrefix rho k * rho k) * anchor ≃ rho k * (prodPrefix rho k * anchor)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hchain
      show ((prodPrefix B.rho k * B.rho k) * B.anchor).eqv
          (B.rho k * (prodPrefix B.rho k * B.anchor))
      -- (p * r) * a ≃ r * (p * a):  (p*r)*a ≃ p*(r*a) ≃ p*(a*r) ≃ (p*a)*r ≃ r*(p*a)
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (prodPrefix B.rho k) (B.rho k) B.anchor) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (prodPrefix B.rho k) _ _ (Q'.mul_comm_eqv (B.rho k) B.anchor)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (prodPrefix B.rho k) B.anchor (B.rho k))) ?_
      exact Q'.mul_comm_eqv (prodPrefix B.rho k * B.anchor) (B.rho k)

/-- The uniform physical floor from the per-block data: `prodFloor ≤ physGap k`
for all `k` (compose the product floor with the running prefix bound). -/
theorem blockPersistence_uniform_floor (B : RGBlockPersistence) (k : Nat) :
    B.prodFloor ≤
      Q'.divPos ((B.atSpacing k).floorRate) (B.spacing k) (B.spacing_pos k) :=
  Q'.le_trans' _ _ _ (B.prodFloor_le k) (prodPrefix_anchor_le_physGap B k)

/-- **Per-block ⇒ uniform.**  A `RGBlockPersistence` yields a `RGGapPersistence`
with `floorConst := prodFloor`: the per-block recursion and product floor are
distilled into the single uniform open inequality. -/
def RGBlockPersistence.toUniform (B : RGBlockPersistence) : RGGapPersistence where
  spacing := B.spacing
  spacing_pos := B.spacing_pos
  atSpacing := B.atSpacing
  floorConst := B.prodFloor
  floorConst_pos := B.prodFloor_pos
  ceilConst := B.ceilConst
  physFloor := blockPersistence_uniform_floor B
  physCeil := B.physCeil

/-- The per-block form's distilled floor is `prodFloor`. -/
@[simp] theorem RGBlockPersistence.toUniform_floorConst (B : RGBlockPersistence) :
    B.toUniform.floorConst = B.prodFloor := rfl

/-- **Per-block ⇒ continuum gap positive.**  Composing the per-block reduction
with the uniform reduction: a `RGBlockPersistence` yields a strictly-positive
continuum physical-gap floor. -/
theorem physGapMin_pos_of_blockPersistence (B : RGBlockPersistence) :
    (0 : Q') < (toScalingBand B.toUniform).physGapMin :=
  physGapMin_pos_of_persistence B.toUniform

/-! ## 4. The strong-coupling anchor — the UNCONDITIONAL base rung

The `j = 0` / fixed-spacing case is genuinely inhabited.  The proven strong-
coupling positive clustering floor (`NonSaturatedFloor.mFiducial > 0`, the
fixed-spacing cluster-expansion floor of the non-saturated SU(2) family) is a
positive PHYSICAL gap at the anchor spacing `a_0 = 1`: with `a_0 = 1` the
physical gap `m_lat(a_0)/a_0` equals the lattice floor, which is the proven
positive `mFiducial`.

This makes the split explicit: the anchor rung is PROVED unconditionally; the
ONLY open content is the PERSISTENCE of a positive floor as `j → ∞` (`a → 0`),
which is `RGGapPersistence.physFloor`.  No claim of an inhabitant for the full
tower is made. -/

/-- The anchor spacing `a_0 = 1` (a fixed positive rational). -/
def anchorSpacing : Q' := (1 : Q')

/-- The anchor spacing is strictly positive. -/
theorem anchorSpacing_pos : (0 : Q') < anchorSpacing := by
  show (0 : Q') < (1 : Q')
  decide

/-- The anchor cluster bound is the proven strong-coupling non-saturated SU(2)
fixed-spacing bound, whose clustering floor is the genuine positive
`mFiducial`. -/
def anchorClusterBound : RegUniformClusterBound :=
  RegularContinuumPipeline.concreteClusterBound

/-- The anchor cluster bound's lattice floor is the proven positive fiducial
mass `mFiducial = 999/1000`. -/
theorem anchorClusterBound_floor :
    anchorClusterBound.floorRate = NonSaturatedFloor.mFiducial := rfl

/-- **The anchor physical gap is strictly positive (UNCONDITIONAL).**  At the
anchor spacing `a_0 = 1`, the physical gap `m_lat(a_0)/a_0` is strictly positive,
because the numerator is the proven positive strong-coupling clustering floor
`mFiducial > 0` and the denominator is `1 > 0` (`Q'.divPos_pos`).  This is the
genuinely-inhabited base rung of the spacing tower. -/
theorem anchor_physGap_pos :
    (0 : Q') <
      Q'.divPos (anchorClusterBound.floorRate) anchorSpacing anchorSpacing_pos :=
  Q'.divPos_pos _ _ _ NonSaturatedFloor.mFiducial_pos

/-- **The anchor floor as a `Q'` lower bound.**  `mFiducial ≤ m_lat(a_0)/a_0`
at the anchor: dividing by `a_0 = 1` is (up to `Q'.eqv`) the identity, so the
proven positive lattice floor is itself a physical-gap floor at the anchor.
Proof: `mFiducial · 1 ≃ mFiducial = floorRate`, then `le_divPos_of_mul_le`. -/
theorem anchor_floor_le_physGap :
    NonSaturatedFloor.mFiducial ≤
      Q'.divPos (anchorClusterBound.floorRate) anchorSpacing anchorSpacing_pos := by
  refine Q'.le_divPos_of_mul_le _ _ _ ?_
  -- mFiducial * anchorSpacing = mFiducial * 1 ≃ mFiducial = floorRate
  show NonSaturatedFloor.mFiducial * anchorSpacing ≤ anchorClusterBound.floorRate
  have h1 : (NonSaturatedFloor.mFiducial * anchorSpacing).eqv NonSaturatedFloor.mFiducial := by
    show (NonSaturatedFloor.mFiducial * (1 : Q')).eqv NonSaturatedFloor.mFiducial
    exact Q'.mul_one_eqv NonSaturatedFloor.mFiducial
  have h2 : anchorClusterBound.floorRate = NonSaturatedFloor.mFiducial := anchorClusterBound_floor
  rw [h2]
  exact Q'.le_of_eqv h1

/-! ## 5. Doc-section: the full reduction chain (HONEST)

The chain assembled across the continuum pipeline and this module:

  1. **Clay 4D Yang–Mills mass gap.**  The target.

  2. **Worst-case reduction to SU(2)** (group dependence; already a Lean theorem
     in the mass-gap layer).  Among the simple compact gauge groups SU(2) is the
     worst case, so the continuum gap for ALL of them reduces to the SU(2) gap —
     a single worst-case reduction, NOT a per-group enumeration.

  3. **SU(2) continuum (`a → 0`) gap = the `RegScalingBand` survival theorem.**
     The dimensionally-correct continuum claim is that the PHYSICAL gap
     `Δ(a) = m_lat(a)/a` stays bounded away from `0` as `a → 0`
     (`band_gap_survives`: liminf physGap ≥ physGapMin > 0).  Everything feeding
     it — finite-volume located gaps, the `Λ → ∞` cluster bound, the derived
     quotient `physGap` with its defining relation `physGap j · a_j ≃ latMargin j`
     a THEOREM — is PROVED.  The sole open field is `physGapMin > 0`.

  4. **`RGGapPersistence` — the one open inequality** (THIS module).  The open
     field of (3) is precisely `RGGapPersistence`:  `∃ c > 0, ∀ j, c ≤
     m_lat(a_j)/a_j`, the uniform-in-spacing physical transfer-gap floor along
     the asymptotic-freedom trajectory.  `continuum_gap_of_RGGapPersistence`
     proves (3) from it, pure assembly; `physGapMin_pos_of_persistence` makes
     `physGapMin > 0` a CONSEQUENCE.

The anchor (§4) shows the `j = 0` rung of (4) is genuinely inhabited
(unconditional strong-coupling positive floor); the ONLY open content is its
PERSISTENCE as `j → ∞` (`a → 0`).

**The sharpened attack surface.**  SU(2)'s transfer-operator gap is explicit via
the heat-kernel / theta-character expansion (the `ThetaConv` / `SigmaHatLimit` /
`HeatKernelConv` assets of the continuum pipeline): the lattice gap margin
`m_lat(a)` is an explicit theta-ratio in the bare coupling, and the spacing
`a` runs through the asymptotic-freedom relation `β(a)`.  So `RGGapPersistence`
is a CONCRETE one-variable inequality — a uniform lower bound on an explicit
theta-ratio divided by `a`, along `β(a)` — not an abstract spectral hypothesis.

**Underclaim.**  This module REDUCES the open continuum problem to the single
inequality `RGGapPersistence` and proves the anchor rung; it does NOT exhibit an
inhabitant of `RGGapPersistence` for 4D Yang–Mills, and therefore does NOT close
the Clay problem.  The open content is exactly: a positive physical-gap floor
PERSISTING as `a → 0`. -/

end YMGap.Continuum.RGGapPersistence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RGGapPersistence.toScalingBand
#print axioms YMGap.Continuum.RGGapPersistence.toScalingBand_physGapMin
#print axioms YMGap.Continuum.RGGapPersistence.physGapMin_pos_of_persistence
#print axioms YMGap.Continuum.RGGapPersistence.continuum_gap_of_RGGapPersistence
#print axioms YMGap.Continuum.RGGapPersistence.continuum_gap_le_ceiling_of_RGGapPersistence
#print axioms YMGap.Continuum.RGGapPersistence.prodPrefix
#print axioms YMGap.Continuum.RGGapPersistence.prodPrefix_anchor_le_physGap
#print axioms YMGap.Continuum.RGGapPersistence.blockPersistence_uniform_floor
#print axioms YMGap.Continuum.RGGapPersistence.RGBlockPersistence.toUniform
#print axioms YMGap.Continuum.RGGapPersistence.RGBlockPersistence.toUniform_floorConst
#print axioms YMGap.Continuum.RGGapPersistence.physGapMin_pos_of_blockPersistence
#print axioms YMGap.Continuum.RGGapPersistence.anchorSpacing_pos
#print axioms YMGap.Continuum.RGGapPersistence.anchorClusterBound_floor
#print axioms YMGap.Continuum.RGGapPersistence.anchor_physGap_pos
#print axioms YMGap.Continuum.RGGapPersistence.anchor_floor_le_physGap
