/-
# Exact anchor half-coupling factorization for adjacent-even reflection

At the strong-coupling anchor used by the adjacent-even slab,

    anchorCoupling = 1/400 = (1/20)^2.

This leaf records that square at the three levels needed by a later
positive-time trajectory gluing argument:

  * the exact rational coupling and all of its Casimir powers;
  * the physical Peter--Weyl coefficient after the exact Schur
    `1 / dim` contraction; and
  * a finite diagonal half-kernel whose two halves compose to the full
    contracted link entry, independently of the chosen cutoff once the
    source mode is present.

The half-kernel is deliberately indexed by all `Nat` modes and the composition
is an explicit `fsum` over `0, ..., cutoff`.  This makes the statement usable
inside later finite trajectory sums without identifying a new state space or
changing the existing adjacent-even interfaces.

Honest scope: these are exact scalar, modewise, and finite diagonal-convolution
identities.  They do not identify the full reflected slab with a product of
independent link kernels, do not construct the missing common-middle feature
map, and do not prove the global physical SOS or any Clay-frontier bundle.

Constructive contract: pure `Q'` / `Nat`; no `Classical`, `sorry`, `admit`,
custom axiom, or `native_decide`.  Every load-bearing theorem is axiom-gated.
-/

import YMGap.Continuum.FusedFreeSplit
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.Z4StrongCouplingParametricAnchor

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact square root of the anchor coupling -/

/-- The positive-time half-coupling.  Its square is the existing
`anchorCoupling = 1/400`. -/
def halfAnchorCoupling : Q' := Q'.mkPos 1 20 (by decide)

/-- The half-coupling lies strictly inside the heat-kernel window. -/
theorem halfAnchorCoupling_window :
    (0 : Q') < halfAnchorCoupling ∧ halfAnchorCoupling < (1 : Q') := by
  decide

/-- The exact rational identity `1/400 = (1/20) * (1/20)`. -/
theorem anchorCoupling_eqv_halfAnchorCoupling_sq :
    anchorCoupling ≈ halfAnchorCoupling * halfAnchorCoupling := by
  decide

/-- Local constructive congruence of the strict-fold power in its base. -/
private theorem qpow_eqv_congr_local {a b : Q'} (h : a ≈ b) :
    ∀ exponent, qpow a exponent ≈ qpow b exponent
  | 0 => Q'.eqv_refl _
  | exponent + 1 => by
      show qpow a exponent * a ≈ qpow b exponent * b
      refine Q'.eqv_trans _ (qpow b exponent * a) _
        (Q'.mul_eqv_congr_right _ _ a
          (qpow_eqv_congr_local h exponent)) ?_
      exact Q'.mul_eqv_congr_left (qpow b exponent) a b h

/-- Every anchor power is the square of the corresponding half-anchor power.
This is the mode-independent algebraic input for the Casimir specialization. -/
theorem anchorQpow_eqv_halfAnchorSquare (exponent : Nat) :
    qpow anchorCoupling exponent ≈
      qpow halfAnchorCoupling exponent * qpow halfAnchorCoupling exponent := by
  refine Q'.eqv_trans _
    (qpow (halfAnchorCoupling * halfAnchorCoupling) exponent) _ ?_ ?_
  · exact qpow_eqv_congr_local
      anchorCoupling_eqv_halfAnchorCoupling_sq exponent
  · exact qpow_mul_self halfAnchorCoupling exponent

/-! ## 2. Modewise Peter--Weyl / Schur factorization -/

/-- One positive-time half-link amplitude in spin channel `spin`.  The Schur
`1 / dim` contraction has already removed the character dimension, leaving
the physical heat-kernel eigenvalue `(1/20)^(spin*(spin+2))`. -/
def anchorHalfSchurAmplitude (spin : Nat) : Q' :=
  physLinkWeight halfAnchorCoupling spin

/-- The chosen half amplitude is exactly one half-coupling link followed by
the genuine Peter--Weyl matrix-coefficient contraction. -/
theorem anchorHalfSchurAmplitude_eqv_contractedLinkEntry (spin : Nat) :
    anchorHalfSchurAmplitude spin ≈
      contractedLinkEntry halfAnchorCoupling spin spin :=
  Q'.eqv_symm (contractedLinkEntry_diag halfAnchorCoupling spin)

/-- Every half-link amplitude is nonnegative. -/
theorem anchorHalfSchurAmplitude_nonnegative (spin : Nat) :
    (0 : Q') ≤ anchorHalfSchurAmplitude spin := by
  unfold anchorHalfSchurAmplitude physLinkWeight
  exact qpow_nonneg halfAnchorCoupling
    (Q'.le_of_lt halfAnchorCoupling_window.1) (c4 spin)

/-- The physical anchor link weight factors modewise as the square of the
positive-time half-link amplitude. -/
theorem anchorPhysLinkWeight_eqv_halfSchurSquare (spin : Nat) :
    physLinkWeight anchorCoupling spin ≈
      anchorHalfSchurAmplitude spin * anchorHalfSchurAmplitude spin := by
  unfold physLinkWeight anchorHalfSchurAmplitude
  exact anchorQpow_eqv_halfAnchorSquare (c4 spin)

/-- Before the Schur contraction, the full heat-kernel character coefficient
is the representation dimension times the square of the half-link amplitude. -/
theorem anchorCoefficient_eqv_dim_mul_halfSchurSquare (spin : Nat) :
    coeffW anchorCoupling spin ≈
      dimQ spin *
        (anchorHalfSchurAmplitude spin * anchorHalfSchurAmplitude spin) := by
  rw [coeffW_eq_dim_mul_phys]
  exact Q'.mul_eqv_congr_left (dimQ spin) _ _
    (anchorPhysLinkWeight_eqv_halfSchurSquare spin)

/-- After the exact Schur contraction, the diagonal full link entry is the
square of the two half-link amplitudes. -/
theorem anchorContractedLinkEntry_diag_eqv_halfSchurSquare (spin : Nat) :
    contractedLinkEntry anchorCoupling spin spin ≈
      anchorHalfSchurAmplitude spin * anchorHalfSchurAmplitude spin :=
  Q'.eqv_trans _ _ _
    (contractedLinkEntry_diag anchorCoupling spin)
    (anchorPhysLinkWeight_eqv_halfSchurSquare spin)

/-! ## 3. A diagonal half-kernel for finite trajectory gluing -/

/-- The positive-time half-kernel.  It is diagonal in the Schur channel and
places the half-link amplitude on that diagonal.  The orientation of the
indicator is chosen so that an intermediate-mode sum is a direct
`delta_fsum` collapse. -/
def anchorHalfSchurKernel (source target : Nat) : Q' :=
  (if target = source then (1 : Q') else 0) *
    anchorHalfSchurAmplitude source

/-- Exact diagonal value of the half-kernel. -/
theorem anchorHalfSchurKernel_diag (spin : Nat) :
    anchorHalfSchurKernel spin spin ≈ anchorHalfSchurAmplitude spin := by
  unfold anchorHalfSchurKernel
  rw [if_pos rfl]
  exact Q'.one_mul_eqv _

/-- Exact off-diagonal vanishing of the half-kernel. -/
theorem anchorHalfSchurKernel_off {source target : Nat}
    (h : target ≠ source) :
    anchorHalfSchurKernel source target ≈ 0 := by
  unfold anchorHalfSchurKernel
  rw [if_neg h]
  exact Q'.zero_mul_eqv _

/-- The half-kernel is pointwise nonnegative. -/
theorem anchorHalfSchurKernel_nonnegative (source target : Nat) :
    (0 : Q') ≤ anchorHalfSchurKernel source target := by
  unfold anchorHalfSchurKernel
  by_cases h : target = source
  · rw [if_pos h]
    exact Q'.mul_nonneg _ _ (by decide)
      (anchorHalfSchurAmplitude_nonnegative source)
  · rw [if_neg h]
    exact Q'.mul_nonneg _ _ (by decide)
      (anchorHalfSchurAmplitude_nonnegative source)

/-- The diagonal half-kernel is symmetric up to rational equivalence. -/
theorem anchorHalfSchurKernel_symmetric (source target : Nat) :
    anchorHalfSchurKernel source target ≈
      anchorHalfSchurKernel target source := by
  by_cases h : source = target
  · subst target
    exact Q'.eqv_refl _
  · exact Q'.eqv_trans _ 0 _
      (anchorHalfSchurKernel_off (Ne.symm h))
      (Q'.eqv_symm (anchorHalfSchurKernel_off h))

/-- Finite matrix composition of the two half-kernels, summing the intermediate
Schur mode over `0, ..., cutoff`. -/
def anchorHalfSchurComposition (cutoff source target : Nat) : Q' :=
  fsum
    (fun middle =>
      anchorHalfSchurKernel source middle *
        anchorHalfSchurKernel middle target)
    (cutoff + 1)

private theorem anchorHalfSchurComposition_term_eqv
    (source target middle : Nat) :
    anchorHalfSchurKernel source middle *
        anchorHalfSchurKernel middle target ≈
      (if middle = source then (1 : Q') else 0) *
        (anchorHalfSchurAmplitude source *
          anchorHalfSchurKernel middle target) := by
  unfold anchorHalfSchurKernel
  exact Q'.mul_assoc_eqv _ _ _

/-- The finite intermediate-mode sum collapses to its unique diagonal mode as
soon as the source mode lies below the cutoff. -/
theorem anchorHalfSchurComposition_collapse
    {cutoff source : Nat} (hsource : source ≤ cutoff) (target : Nat) :
    anchorHalfSchurComposition cutoff source target ≈
      anchorHalfSchurAmplitude source *
        anchorHalfSchurKernel source target := by
  unfold anchorHalfSchurComposition
  refine Q'.eqv_trans _
    (fsum
      (fun middle =>
        (if middle = source then (1 : Q') else 0) *
          (anchorHalfSchurAmplitude source *
            anchorHalfSchurKernel middle target))
      (cutoff + 1)) _ ?_ ?_
  · exact fsum_eqv_congr'
      (fun middle =>
        anchorHalfSchurComposition_term_eqv source target middle)
      (cutoff + 1)
  · exact delta_fsum
      (fun middle =>
        anchorHalfSchurAmplitude source *
          anchorHalfSchurKernel middle target)
      source (cutoff + 1) (by omega)

/-- The composed half-kernel is pointwise nonnegative. -/
theorem anchorHalfSchurComposition_nonnegative
    (cutoff source target : Nat) :
    (0 : Q') ≤ anchorHalfSchurComposition cutoff source target := by
  unfold anchorHalfSchurComposition
  exact fsum_nonneg
    (fun middle =>
      Q'.mul_nonneg _ _
        (anchorHalfSchurKernel_nonnegative source middle)
        (anchorHalfSchurKernel_nonnegative middle target))
    (cutoff + 1)

/-- On the diagonal, the finite half-kernel composition is exactly the square
of the modewise half-link amplitude. -/
theorem anchorHalfSchurComposition_diag
    {cutoff spin : Nat} (hspin : spin ≤ cutoff) :
    anchorHalfSchurComposition cutoff spin spin ≈
      anchorHalfSchurAmplitude spin * anchorHalfSchurAmplitude spin :=
  Q'.eqv_trans _ _ _
    (anchorHalfSchurComposition_collapse hspin spin)
    (Q'.mul_eqv_congr_left (anchorHalfSchurAmplitude spin) _ _
      (anchorHalfSchurKernel_diag spin))

/-- Off the diagonal, the finite half-kernel composition vanishes. -/
theorem anchorHalfSchurComposition_off
    {cutoff source target : Nat} (hsource : source ≤ cutoff)
    (hoff : source ≠ target) :
    anchorHalfSchurComposition cutoff source target ≈ 0 := by
  refine Q'.eqv_trans _
    (anchorHalfSchurAmplitude source * anchorHalfSchurKernel source target)
    0 (anchorHalfSchurComposition_collapse hsource target) ?_
  refine Q'.eqv_trans _ (anchorHalfSchurAmplitude source * 0) _ ?_
    (Q'.mul_zero_eqv _)
  exact Q'.mul_eqv_congr_left (anchorHalfSchurAmplitude source) _ _
    (anchorHalfSchurKernel_off (Ne.symm hoff))

/-- Once the selected source channel is present, enlarging or shrinking the
finite intermediate-mode cutoff does not change the composed kernel. -/
theorem anchorHalfSchurComposition_cutoff_stable
    {cutoff₁ cutoff₂ source : Nat}
    (hsource₁ : source ≤ cutoff₁) (hsource₂ : source ≤ cutoff₂)
    (target : Nat) :
    anchorHalfSchurComposition cutoff₁ source target ≈
      anchorHalfSchurComposition cutoff₂ source target :=
  Q'.eqv_trans _
    (anchorHalfSchurAmplitude source *
      anchorHalfSchurKernel source target) _
    (anchorHalfSchurComposition_collapse hsource₁ target)
    (Q'.eqv_symm
      (anchorHalfSchurComposition_collapse hsource₂ target))

/-! ## 4. Full finite Schur wiring at the anchor -/

/-- **Exact finite half-kernel wiring.**  If the source mode occurs in the
intermediate cutoff, the full anchor-coupling link followed by its exact Schur
contraction equals the composition of two `1/20` half-kernels for every source
and target channel.

This theorem includes both diagonal and off-diagonal channels.  It remains a
single-link Schur identity; no independence or product decomposition across
the links and shared faces of the physical slab is asserted. -/
theorem anchorContractedLinkEntry_eqv_halfSchurComposition
    {cutoff source target : Nat} (hsource : source ≤ cutoff) :
    contractedLinkEntry anchorCoupling source target ≈
      anchorHalfSchurComposition cutoff source target := by
  by_cases hdiag : source = target
  · subst target
    exact Q'.eqv_trans _
      (anchorHalfSchurAmplitude source * anchorHalfSchurAmplitude source) _
      (anchorContractedLinkEntry_diag_eqv_halfSchurSquare source)
      (Q'.eqv_symm (anchorHalfSchurComposition_diag hsource))
  · exact Q'.eqv_trans _ 0 _
      (contractedLinkEntry_off (w := anchorCoupling) hdiag)
      (Q'.eqv_symm
        (anchorHalfSchurComposition_off hsource hdiag))

/-! ## 5. Honest status -/

/-!
PROVED here (constructively):

  * `anchorCoupling_eqv_halfAnchorCoupling_sq` and
    `anchorQpow_eqv_halfAnchorSquare` -- the exact `1/20` square at every power;
  * `anchorCoefficient_eqv_dim_mul_halfSchurSquare` and
    `anchorContractedLinkEntry_diag_eqv_halfSchurSquare` -- the modewise
    Peter--Weyl coefficient and exact Schur-contracted forms;
  * `anchorHalfSchurComposition_collapse`, its diagonal/off-diagonal forms and
    cutoff stability -- the finite intermediate-mode gluing calculus;
  * `anchorContractedLinkEntry_eqv_halfSchurComposition` -- complete single-link
    wiring of the anchor entry through the two half-kernels.

OPEN and intentionally untouched: the physical slab's shared-face incidence
couplings, a common-middle feature representation for the reachable endpoint
matrix, and therefore the global adjacent-even physical SOS/PSD theorem.  This
leaf supplies an exact local coefficient factor for that future gluing; it does
not supply the gluing itself.
-/

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.halfAnchorCoupling_window
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorCoupling_eqv_halfAnchorCoupling_sq
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorQpow_eqv_halfAnchorSquare
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurAmplitude_eqv_contractedLinkEntry
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurAmplitude_nonnegative
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorPhysLinkWeight_eqv_halfSchurSquare
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorCoefficient_eqv_dim_mul_halfSchurSquare
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorContractedLinkEntry_diag_eqv_halfSchurSquare
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurKernel_diag
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurKernel_off
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurKernel_nonnegative
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurKernel_symmetric
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurComposition_collapse
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurComposition_nonnegative
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurComposition_diag
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurComposition_off
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorHalfSchurComposition_cutoff_stable
#print axioms YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorHalfCouplingFactorization.anchorContractedLinkEntry_eqv_halfSchurComposition
