/-
# Positive grouped Feynman--Kac convergence from a spacing modulus

`BF4GroupedFeynmanKacHarnack` proves a projective window for nonconstant
interior weights, while `SU2NonlinearFiveFusionCompletion` proves cutoff
convergence of the genuine fivefold fusion observable at fixed heat nome.
This module supplies one quantitative sufficient continuity bridge between
those two kinds of result.

For normalized positive spatial weights

    0 <= V_a(y) <= 1,        1 <= V_a(y) + omega(a),

a path with `p` interior insertions loses at most `p * omega(a)`.  If the
bare grouped kinetic kernel has ceiling `B`, then pointwise

    K_V <= K_0 <= K_V + (p * omega(a)) * B.

Consequently any convergent bare-kernel sequence and its fully interleaved
positive Feynman--Kac sequence have the same constructive-real limit once an
explicit modulus proves

    (p * omega(a_n)) * B -> 0.

The final theorem applies this general two-sided continuity principle to the
existing cutoff-free nonlinear five-fusion limit.  It isolates one explicit
sufficient Yang--Mills estimate: an action-derived positive kernel may be
compared two-sidedly with the canonical five-fusion observable with a
spacing-dependent error tending to zero.  The physical kernel could instead
converge only after source/target profile cancellation, so this absolute
criterion is not asserted to be necessary.  Positivity alone cannot provide
it, as the spike fence in `BF4GroupedFeynmanKacHarnack` shows.

No new spectral or continuum assumption is hidden here.  All convergence
thresholds are supplied as explicit `Nat`-valued moduli.

## Dependency gate

Constructive `Nat`/`Q'`/`CReal` mathematics only.
-/

import YMGap.Continuum.BF4GroupedFeynmanKacHarnack
import YMGap.Continuum.SU2NonlinearFiveFusionCompletion

namespace YMGap.Continuum.BF4PositiveKernelSpacingConvergence

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt
open YMGap.Continuum.SU2NonlinearFiveFusionCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Linear loss along a positive path -/

private theorem ofNat_succ_mul_eqv (n : Nat) (delta : Q') :
    Q'.ofNat (n + 1) * delta ≈
      Q'.ofNat n * delta + delta := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (Q'.ofNat (n + 1))
      (Q'.ofNat n + Q'.ofNat 1)
      delta
      (Q'.ofNat_add_eqv n 1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv
      (Q'.ofNat n) (Q'.ofNat 1) delta) ?_
  exact Q'.add_eqv_congr_left
    (Q'.ofNat n * delta)
    (Q'.ofNat 1 * delta) delta
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (Q'.ofNat 1) 1 delta (by decide))
      (Q'.one_mul_eqv delta))

/-- If every normalized positive weight is within `delta` below one, the
product along a path of length `p` is within `p * delta` below one. -/
theorem pathPotentialProduct_unit_deficit
    {State : Type} (potential : State → Q') (delta : Q')
    (delta_nonnegative : (0 : Q') ≤ delta)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (potential_le_one :
      ∀ state, potential state ≤ (1 : Q'))
    (one_le_potential_add_delta :
      ∀ state, (1 : Q') ≤ potential state + delta) :
    ∀ path : List State,
      (1 : Q') ≤
        pathPotentialProduct potential path +
          Q'.ofNat path.length * delta
  | [] => by
      change (1 : Q') ≤ 1 + Q'.ofNat 0 * delta
      exact Q'.add_le_self_of_nonneg 1
        (Q'.ofNat 0 * delta)
        (Q'.mul_nonneg _ _
          (ExpNeg.ofNat_nonneg' 0) delta_nonnegative)
  | state :: tail => by
      let value := potential state
      let product := pathPotentialProduct potential tail
      let loss := Q'.ofNat tail.length * delta
      have hinductive : (1 : Q') ≤ product + loss :=
        pathPotentialProduct_unit_deficit
          potential delta delta_nonnegative
          potential_nonnegative potential_le_one
          one_le_potential_add_delta tail
      have hvalueNonnegative : (0 : Q') ≤ value :=
        potential_nonnegative state
      have hlossNonnegative : (0 : Q') ≤ loss :=
        Q'.mul_nonneg _ _
          (ExpNeg.ofNat_nonneg' tail.length)
          delta_nonnegative
      have hscaled :
          value * 1 ≤ value * (product + loss) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          hinductive hvalueNonnegative
      have hvalueLoss :
          value * loss ≤ (1 : Q') * loss :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (potential_le_one state) hlossNonnegative
      have hvalueToProductLoss :
          value ≤ value * product + loss := by
        exact Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.mul_one_eqv value))
          (Q'.le_trans' _ _ _ hscaled
            (Q'.le_trans' _ _ _
              (Q'.le_of_eqv
                (Q'.mul_add_eqv value product loss))
              (Q'.add_le_add_left
                (value * product) (value * loss) loss
                (Q'.le_trans' _ _ _ hvalueLoss
                  (Q'.le_of_eqv
                    (Q'.one_mul_eqv loss))))))
      have hadd :
          value + delta ≤
            (value * product + loss) + delta :=
        Q'.add_le_add_right _ _ delta
          hvalueToProductLoss
      have hraw :
          (1 : Q') ≤
            (value * product + loss) + delta :=
        Q'.le_trans' _ _ _
          (one_le_potential_add_delta state) hadd
      have hreindex :
          (value * product + loss) + delta ≈
            value * product +
              Q'.ofNat (tail.length + 1) * delta := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv
            (value * product) loss delta) ?_
        exact Q'.add_eqv_congr_left
          (value * product)
          (loss + delta)
          (Q'.ofNat (tail.length + 1) * delta)
          (Q'.eqv_symm
            (ofNat_succ_mul_eqv tail.length delta))
      exact Q'.le_trans' _ _ _
        hraw (Q'.le_of_eqv hreindex)

/-- The same normalized hypotheses bound every path product above by one. -/
theorem pathPotentialProduct_le_one
    {State : Type} (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (potential_le_one :
      ∀ state, potential state ≤ (1 : Q')) :
    ∀ path : List State,
      pathPotentialProduct potential path ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | state :: tail => by
      change
        potential state *
            pathPotentialProduct potential tail ≤ (1 : Q')
      have hproductNonnegative :
          (0 : Q') ≤ pathPotentialProduct potential tail :=
        pathPotentialProduct_nonnegative
          potential_nonnegative tail
      have hmul :
          potential state *
              pathPotentialProduct potential tail ≤
            (1 : Q') * 1 :=
        Q'.mul_le_mul_of_nonneg
          (potential_le_one state)
          (pathPotentialProduct_le_one
            potential potential_nonnegative
            potential_le_one tail)
          Q'.zero_le_one hproductNonnegative
      exact Q'.le_trans' _ _ _
        hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-! ## 2. Quantitative continuity of the positive grouped kernel -/

private theorem listQSum_mono_on
    {A : Type} (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
        listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_on lower upper tail
          (fun x hx =>
            hbound x (List.mem_cons_of_mem head hx)))

/-- A normalized positive potential can only decrease the grouped kinetic
kernel. -/
theorem feynmanKacPathKernel_le_grouped
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (potential_le_one :
      ∀ state, potential state ≤ (1 : Q'))
    (source : Source) (target : Target) :
    feynmanKacPathKernel
        paths kineticWeight potential source target ≤
      groupedPathKernel paths kineticWeight source target := by
  unfold feynmanKacPathKernel groupedPathKernel
  apply listQSum_mono_on
  intro path hpath
  have hproductNonnegative :
      (0 : Q') ≤ pathPotentialProduct potential path :=
    pathPotentialProduct_nonnegative
      potential_nonnegative path
  have hscaled :
      kineticWeight source target path *
          pathPotentialProduct potential path ≤
        kineticWeight source target path * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (pathPotentialProduct_le_one
        potential potential_nonnegative
        potential_le_one path)
      (kinetic_nonnegative source target path hpath)
  exact Q'.le_trans' _ _ _
    hscaled
    (Q'.le_of_eqv
      (Q'.mul_one_eqv
        (kineticWeight source target path)))

/-- Linear lower continuity bound before inserting a kinetic ceiling:
`K_0 <= K_V + p*delta*K_0`. -/
theorem grouped_le_feynmanKac_add_linear_loss
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (interiorCount : Nat) (delta : Q')
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths →
        path.length = interiorCount)
    (delta_nonnegative : (0 : Q') ≤ delta)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (potential_le_one :
      ∀ state, potential state ≤ (1 : Q'))
    (one_le_potential_add_delta :
      ∀ state, (1 : Q') ≤ potential state + delta)
    (source : Source) (target : Target) :
    groupedPathKernel paths kineticWeight source target ≤
      feynmanKacPathKernel
          paths kineticWeight potential source target +
        (Q'.ofNat interiorCount * delta) *
          groupedPathKernel
            paths kineticWeight source target := by
  let loss := Q'.ofNat interiorCount * delta
  have hsum :
      listQSum
          (kineticWeight source target) paths ≤
        listQSum
          (fun path =>
            kineticWeight source target path *
                pathPotentialProduct potential path +
              loss * kineticWeight source target path)
          paths := by
    apply listQSum_mono_on
    intro path hpath
    have hpathDeficit :
        (1 : Q') ≤
          pathPotentialProduct potential path + loss := by
      have hraw :=
        pathPotentialProduct_unit_deficit
          potential delta delta_nonnegative
          potential_nonnegative potential_le_one
          one_le_potential_add_delta path
      unfold loss
      rwa [fixed_length path hpath] at hraw
    have hkineticNonnegative :
        (0 : Q') ≤ kineticWeight source target path :=
      kinetic_nonnegative source target path hpath
    have hscaled :
        kineticWeight source target path * 1 ≤
          kineticWeight source target path *
            (pathPotentialProduct potential path + loss) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hpathDeficit hkineticNonnegative
    have hreindex :
        kineticWeight source target path *
            (pathPotentialProduct potential path + loss) ≈
          kineticWeight source target path *
              pathPotentialProduct potential path +
            loss * kineticWeight source target path := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv
          (kineticWeight source target path)
          (pathPotentialProduct potential path) loss) ?_
      exact Q'.add_eqv_congr_left
        (kineticWeight source target path *
          pathPotentialProduct potential path)
        (kineticWeight source target path * loss)
        (loss * kineticWeight source target path)
        (Q'.mul_comm_eqv
          (kineticWeight source target path) loss)
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (Q'.mul_one_eqv
          (kineticWeight source target path)))
      (Q'.le_trans' _ _ _
        hscaled (Q'.le_of_eqv hreindex))
  have hdecompose :
      listQSum
          (fun path =>
            kineticWeight source target path *
                pathPotentialProduct potential path +
              loss * kineticWeight source target path)
          paths ≈
        feynmanKacPathKernel
            paths kineticWeight potential source target +
          loss *
            groupedPathKernel
              paths kineticWeight source target := by
    refine Q'.eqv_trans _ _ _
      (listQSum_add
        (fun path =>
          kineticWeight source target path *
            pathPotentialProduct potential path)
        (fun path =>
          loss * kineticWeight source target path)
        paths) ?_
    exact Q'.add_eqv_congr_left
      (feynmanKacPathKernel
        paths kineticWeight potential source target)
      (listQSum
        (fun path =>
          loss * kineticWeight source target path)
        paths)
      (loss *
        groupedPathKernel
          paths kineticWeight source target)
      (listQSum_mul_left
        loss (kineticWeight source target) paths)
  exact Q'.le_trans' _ _ _
    hsum (Q'.le_of_eqv hdecompose)

/-- **Direct positive-kernel continuity estimate.**  If the bare grouped
kernel is bounded by `kineticCeiling`, its fully interleaved positive
Feynman--Kac deformation differs from it by at most
`(p * delta) * kineticCeiling`, division-free and pointwise. -/
theorem grouped_feynmanKac_two_sided_spacing_bound
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight : Source → Target → List State → Q')
    (potential : State → Q')
    (interiorCount : Nat) (delta kineticCeiling : Q')
    (kinetic_nonnegative :
      ∀ source target path,
        path ∈ paths →
          (0 : Q') ≤ kineticWeight source target path)
    (fixed_length :
      ∀ path, path ∈ paths →
        path.length = interiorCount)
    (delta_nonnegative : (0 : Q') ≤ delta)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (potential_le_one :
      ∀ state, potential state ≤ (1 : Q'))
    (one_le_potential_add_delta :
      ∀ state, (1 : Q') ≤ potential state + delta)
    (kinetic_ceiling :
      ∀ source target,
        groupedPathKernel paths kineticWeight source target ≤
          kineticCeiling)
    (source : Source) (target : Target) :
    feynmanKacPathKernel
        paths kineticWeight potential source target ≤
      groupedPathKernel paths kineticWeight source target ∧
    groupedPathKernel paths kineticWeight source target ≤
      feynmanKacPathKernel
          paths kineticWeight potential source target +
        (Q'.ofNat interiorCount * delta) *
          kineticCeiling := by
  refine
    ⟨feynmanKacPathKernel_le_grouped
      paths kineticWeight potential
      kinetic_nonnegative potential_nonnegative
      potential_le_one source target, ?_⟩
  have hraw :=
    grouped_le_feynmanKac_add_linear_loss
      paths kineticWeight potential interiorCount delta
      kinetic_nonnegative fixed_length delta_nonnegative
      potential_nonnegative potential_le_one
      one_le_potential_add_delta source target
  have hlossNonnegative :
      (0 : Q') ≤ Q'.ofNat interiorCount * delta :=
    Q'.mul_nonneg _ _
      (ExpNeg.ofNat_nonneg' interiorCount)
      delta_nonnegative
  have hscaledCeiling :
      (Q'.ofNat interiorCount * delta) *
          groupedPathKernel paths kineticWeight source target ≤
        (Q'.ofNat interiorCount * delta) *
          kineticCeiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (kinetic_ceiling source target)
      hlossNonnegative
  exact Q'.le_trans' _ _ _
    hraw
    (Q'.add_le_add_left
      (feynmanKacPathKernel
        paths kineticWeight potential source target)
      ((Q'.ofNat interiorCount * delta) *
        groupedPathKernel paths kineticWeight source target)
      ((Q'.ofNat interiorCount * delta) *
        kineticCeiling)
      hscaledCeiling)

/-! ## 3. An explicit spacing modulus gives constructive convergence -/

/-- A choice-free, explicit convergence modulus for an error evaluated along
a lattice-spacing sequence.  This is data, not a Prop-level extracted
subsequence. -/
structure SpacingErrorModulus
    (spacing : Nat → Q') (errorAt : Q' → Q') : Type where
  stage : Q' → Nat
  eventually_le :
    ∀ ε : Q', (0 : Q') < ε →
      ∀ n : Nat, stage ε ≤ n →
        errorAt (spacing n) ≤ ε

/-- Generic two-sided continuity principle for rational kernels.  A physical
sequence below a convergent bare sequence and within an explicitly vanishing
one-sided error has the same constructive-real limit. -/
theorem convergesTo_of_two_sided_spacing_error
    (bare physical : Nat → Q')
    (spacing : Nat → Q') (errorAt : Q' → Q')
    (errorModulus : SpacingErrorModulus spacing errorAt)
    (physical_le_bare :
      ∀ n, physical n ≤ bare n)
    (bare_le_physical_add_error :
      ∀ n, bare n ≤ physical n + errorAt (spacing n))
    (limit : CReal)
    (bare_converges :
      CReal.ConvergesTo
        (fun n => CReal.ofQ' (bare n)) limit) :
    CReal.ConvergesTo
      (fun n => CReal.ofQ' (physical n)) limit := by
  intro ε hε
  let halfEpsilon := HalfPow.half * ε
  have hhalfPositive : (0 : Q') < halfEpsilon :=
    ExpNeg.half_mul_pos ε hε
  have hhalfNonnegative : (0 : Q') ≤ halfEpsilon :=
    Q'.le_of_lt hhalfPositive
  have hhalfLeEpsilon : halfEpsilon ≤ ε := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        halfEpsilon halfEpsilon hhalfNonnegative)
      (Q'.le_of_eqv
        (ExpNeg.two_halves ε))
  obtain ⟨bareStage, hbareStage⟩ :=
    bare_converges halfEpsilon hhalfPositive
  let physicalStage :=
    max bareStage (errorModulus.stage halfEpsilon)
  refine ⟨physicalStage, fun n hn => ?_⟩
  have hnBare : bareStage ≤ n :=
    Nat.le_trans
      (Nat.le_max_left _ _) hn
  have hnError :
      errorModulus.stage halfEpsilon ≤ n :=
    Nat.le_trans
      (Nat.le_max_right _ _) hn
  have herror :
      errorAt (spacing n) ≤ halfEpsilon :=
    errorModulus.eventually_le
      halfEpsilon hhalfPositive n hnError
  obtain ⟨approxStage, happrox⟩ :=
    hbareStage n hnBare
  refine ⟨approxStage, fun k hk => ?_⟩
  obtain ⟨hbareUpper, hbareLower⟩ :=
    happrox k hk
  change
    bare n ≤ limit.approx k + halfEpsilon
      at hbareUpper
  change
    limit.approx k ≤ bare n + halfEpsilon
      at hbareLower
  change
    physical n ≤ limit.approx k + ε ∧
      limit.approx k ≤ physical n + ε
  constructor
  · exact Q'.le_trans' _ _ _
      (physical_le_bare n)
      (Q'.le_trans' _ _ _
        hbareUpper
        (Q'.add_le_add_left
          (limit.approx k)
          halfEpsilon ε hhalfLeEpsilon))
  · have hreplace :
        bare n + halfEpsilon ≤
          (physical n + errorAt (spacing n)) +
            halfEpsilon :=
      Q'.add_le_add_right _ _ halfEpsilon
        (bare_le_physical_add_error n)
    have herrorReplace :
        (physical n + errorAt (spacing n)) +
            halfEpsilon ≤
          (physical n + halfEpsilon) +
            halfEpsilon :=
      Q'.add_le_add_right _ _ halfEpsilon
        (Q'.add_le_add_left
          (physical n)
          (errorAt (spacing n))
          halfEpsilon herror)
    exact Q'.le_trans' _ _ _
      hbareLower
      (Q'.le_trans' _ _ _
        hreplace
        (Q'.le_trans' _ _ _
          herrorReplace
          (Q'.le_of_eqv
            (Q'.eqv_trans _ _ _
              (Q'.add_assoc_eqv
                (physical n)
                halfEpsilon halfEpsilon)
              (Q'.add_eqv_congr_left
                (physical n)
                (halfEpsilon + halfEpsilon)
                ε
                (ExpNeg.two_halves ε))))))

/-- **Positive grouped Feynman--Kac convergence.**

For a possibly cutoff-dependent path expansion, normalized interior weights
with spacing oscillation `omega(a_n)`, a uniform kinetic ceiling `B`, and an
explicit modulus for

    ((p * omega(a_n)) * B) -> 0,

the physical interleaved kernel converges entrywise to exactly the same
constructive-real limit as the bare grouped kinetic kernel. -/
theorem feynmanKacPathKernel_converges_of_spacing_oscillation
    {Source Target State : Type}
    (paths : Nat → List (List State))
    (kineticWeight :
      Nat → Source → Target → List State → Q')
    (potential : Nat → State → Q')
    (spacing : Nat → Q') (oscillation : Q' → Q')
    (interiorCount : Nat) (kineticCeiling : Q')
    (kinetic_nonnegative :
      ∀ n source target path,
        path ∈ paths n →
          (0 : Q') ≤
            kineticWeight n source target path)
    (fixed_length :
      ∀ n path, path ∈ paths n →
        path.length = interiorCount)
    (oscillation_nonnegative :
      ∀ n, (0 : Q') ≤ oscillation (spacing n))
    (potential_nonnegative :
      ∀ n state, (0 : Q') ≤ potential n state)
    (potential_le_one :
      ∀ n state, potential n state ≤ (1 : Q'))
    (one_le_potential_add_oscillation :
      ∀ n state,
        (1 : Q') ≤
          potential n state + oscillation (spacing n))
    (kinetic_ceiling :
      ∀ n source target,
        groupedPathKernel
            (paths n) (kineticWeight n) source target ≤
          kineticCeiling)
    (errorModulus :
      SpacingErrorModulus spacing
        (fun a =>
          (Q'.ofNat interiorCount * oscillation a) *
            kineticCeiling))
    (source : Source) (target : Target)
    (limit : CReal)
    (bare_converges :
      CReal.ConvergesTo
        (fun n =>
          CReal.ofQ'
            (groupedPathKernel
              (paths n) (kineticWeight n)
              source target))
        limit) :
    CReal.ConvergesTo
      (fun n =>
        CReal.ofQ'
          (feynmanKacPathKernel
            (paths n) (kineticWeight n)
            (potential n) source target))
      limit := by
  apply convergesTo_of_two_sided_spacing_error
    (bare := fun n =>
      groupedPathKernel
        (paths n) (kineticWeight n) source target)
    (physical := fun n =>
      feynmanKacPathKernel
        (paths n) (kineticWeight n)
        (potential n) source target)
    spacing
    (fun a =>
      (Q'.ofNat interiorCount * oscillation a) *
        kineticCeiling)
    errorModulus
  · intro n
    exact
      (grouped_feynmanKac_two_sided_spacing_bound
        (paths n) (kineticWeight n) (potential n)
        interiorCount (oscillation (spacing n))
        kineticCeiling
        (kinetic_nonnegative n)
        (fixed_length n)
        (oscillation_nonnegative n)
        (potential_nonnegative n)
        (potential_le_one n)
        (one_le_potential_add_oscillation n)
        (kinetic_ceiling n)
        source target).1
  · intro n
    exact
      (grouped_feynmanKac_two_sided_spacing_bound
        (paths n) (kineticWeight n) (potential n)
        interiorCount (oscillation (spacing n))
        kineticCeiling
        (kinetic_nonnegative n)
        (fixed_length n)
        (oscillation_nonnegative n)
        (potential_nonnegative n)
        (potential_le_one n)
        (one_le_potential_add_oscillation n)
        (kinetic_ceiling n)
        source target).2
  · exact bare_converges

/-! ## 4. Consumer for the completed nonlinear five-fusion observable -/

/-- **Nonlinear five-fusion positive-kernel convergence.**

The canonical rational five-holonomy Haar squares already converge to
`nonlinearFiveHeatHSSq D`.  Therefore any action-derived positive-kernel
observable that lies below those canonical terms and whose deficit has an
explicit spacing modulus converges to the same cutoff-free limit.

The two comparison inequalities and the modulus are exactly the open inputs
for this sufficient positive-kernel route.  This theorem does not assert that
the present repository has constructed the action-derived kernel or that its
spatial weights are uniformly close to one. -/
theorem nonlinearFivePositiveKernel_converges_of_spacing_error
    (D : NonlinearFiveHeatData)
    (physical : Nat → Q')
    (spacing : Nat → Q') (errorAt : Q' → Q')
    (errorModulus :
      SpacingErrorModulus spacing errorAt)
    (physical_le_canonical :
      ∀ N,
        physical N ≤
          nonlinearFiveHaarL2SqQ D.q N)
    (canonical_le_physical_add_error :
      ∀ N,
        nonlinearFiveHaarL2SqQ D.q N ≤
          physical N + errorAt (spacing N)) :
    CReal.ConvergesTo
      (fun N => CReal.ofQ' (physical N))
      (nonlinearFiveHeatHSSq D) := by
  exact convergesTo_of_two_sided_spacing_error
    (fun N => nonlinearFiveHaarL2SqQ D.q N)
    physical spacing errorAt errorModulus
    physical_le_canonical
    canonical_le_physical_add_error
    (nonlinearFiveHeatHSSq D)
    (nonlinearFiveCanonicalQ_converges D)

end YMGap.Continuum.BF4PositiveKernelSpacingConvergence

#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.pathPotentialProduct_unit_deficit
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.pathPotentialProduct_le_one
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.feynmanKacPathKernel_le_grouped
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.grouped_le_feynmanKac_add_linear_loss
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.grouped_feynmanKac_two_sided_spacing_bound
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.SpacingErrorModulus
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.convergesTo_of_two_sided_spacing_error
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.feynmanKacPathKernel_converges_of_spacing_oscillation
#print axioms YMGap.Continuum.BF4PositiveKernelSpacingConvergence.nonlinearFivePositiveKernel_converges_of_spacing_error
