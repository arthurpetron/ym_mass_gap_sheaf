/-
# Three successive physical Schur moves on a valence-six bulk chain

The six-valent production link carries five external factors in the left
tree

  ((((a b) c) d) e) -> f.

Its first four factors form exactly the valence-five chain ending at `z`, so
the two-level normalized transport already proved there can be reused.  For
each dependent two-level target, the outer fusion step of its second right
channel is `a ((b c) d) -> z`.  Together with the retained production suffix
`z e -> f`, it constructs a third physical left channel.  The final Schur
row yields the fully right-associated tree `a (((b c) d) e) -> f`.

This module enumerates the resulting three-level finite tower and proves
exact normalization.  It is the local analytic recoupling law for the
six-valent bulk carrier, not yet its global lattice product or Gibbs-weight
comparison.

Constructive contract: exact `Q'`, finite lists, no choice, no `Classical`,
no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport

namespace YMGap.Continuum.SU2ValenceSixIteratedSchurTransport

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Reuse the first two dependent moves -/

/-- The first four inputs of a valence-six chain form a valence-five chain
with final output `z`. -/
def FixedLeftCGValenceSix.valenceFivePrefix {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f) :
    FixedLeftCGValenceFive a b c d chain.z :=
  { x := chain.x
    y := chain.y
    first := chain.first
    second := chain.second
    third := chain.third }

theorem FixedLeftCGValenceSix.valenceFivePrefix_labels
    {a b c d e f : Nat} (chain : FixedLeftCGValenceSix a b c d e f) :
    (FixedLeftCGValenceSix.valenceFivePrefix chain).x = chain.x ∧
      (FixedLeftCGValenceSix.valenceFivePrefix chain).y = chain.y := by
  exact ⟨rfl, rfl⟩

/-! ## 2. The third physical left channel -/

/-- The second right target's outer step ends at `z`; fusing that with the
retained last factor `e` and output `f` gives the third Schur input. -/
def valenceSixThirdLeftChannel {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (prior : ValenceFiveRightTreeTarget
      (FixedLeftCGValenceSix.valenceFivePrefix chain)) :
    FixedLeftCGChannel a prior.second.intermediate e f :=
  fixedLeftChannelOfFusion a prior.second.intermediate e f chain.z
    (fixedRight_outer_fusionOK prior.second) chain.fourth.fusionOK

theorem valenceSixThirdLeftChannel_intermediate {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (prior : ValenceFiveRightTreeTarget
      (FixedLeftCGValenceSix.valenceFivePrefix chain)) :
    (valenceSixThirdLeftChannel chain prior).intermediate = chain.z := by
  exact fixedLeftChannelOfFusion_intermediate
    a prior.second.intermediate e f chain.z
    (fixedRight_outer_fusionOK prior.second) chain.fourth.fusionOK

/-! ## 3. The complete three-level target tower -/

structure ValenceSixRightTreeTarget {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f) where
  prior : ValenceFiveRightTreeTarget
    (FixedLeftCGValenceSix.valenceFivePrefix chain)
  third : FixedRightCGChannel a prior.second.intermediate e f

def valenceSixRightTreeTargets {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f) :
    List (ValenceSixRightTreeTarget chain) :=
  (valenceFiveRightTreeTargets
    (FixedLeftCGValenceSix.valenceFivePrefix chain)).flatMap fun prior =>
    (physicalSchurRightTargets
      (valenceSixThirdLeftChannel chain prior)).map fun third =>
        { prior := prior, third := third }

def valenceSixIteratedSchurKernelAt {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) : Q' :=
  valenceFiveIteratedSchurKernelAt
      (FixedLeftCGValenceSix.valenceFivePrefix chain) target.prior *
    physicalSchurRecouplingKernelAt
      (valenceSixThirdLeftChannel chain target.prior) target.third

theorem valenceSixIteratedSchurKernelAt_nonnegative
    {a b c d e f : Nat} (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) :
    (0 : Q') ≤ valenceSixIteratedSchurKernelAt chain target := by
  exact Q'.mul_nonneg _ _
    (valenceFiveIteratedSchurKernelAt_nonnegative
      (FixedLeftCGValenceSix.valenceFivePrefix chain) target.prior)
    (physicalSchurRecouplingKernelAt_nonnegative
      (valenceSixThirdLeftChannel chain target.prior) target.third)

private theorem thirdFiber_mass
    {a b c d e f : Nat} (chain : FixedLeftCGValenceSix a b c d e f)
    (prior : ValenceFiveRightTreeTarget
      (FixedLeftCGValenceSix.valenceFivePrefix chain)) :
    listQSum (valenceSixIteratedSchurKernelAt chain)
        ((physicalSchurRightTargets
          (valenceSixThirdLeftChannel chain prior)).map fun third =>
            ({ prior := prior, third := third } :
              ValenceSixRightTreeTarget chain)) ≈
      valenceFiveIteratedSchurKernelAt
        (FixedLeftCGValenceSix.valenceFivePrefix chain) prior := by
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (valenceFiveIteratedSchurKernelAt
        (FixedLeftCGValenceSix.valenceFivePrefix chain) prior *
      listQSum
        (physicalSchurRecouplingKernelAt
          (valenceSixThirdLeftChannel chain prior))
        (physicalSchurRightTargets
          (valenceSixThirdLeftChannel chain prior))) _ ?_ ?_
  · exact listQSum_mul_left
      (valenceFiveIteratedSchurKernelAt
        (FixedLeftCGValenceSix.valenceFivePrefix chain) prior)
      (physicalSchurRecouplingKernelAt
        (valenceSixThirdLeftChannel chain prior))
      (physicalSchurRightTargets
        (valenceSixThirdLeftChannel chain prior))
  · exact Q'.eqv_trans _
      (valenceFiveIteratedSchurKernelAt
        (FixedLeftCGValenceSix.valenceFivePrefix chain) prior * 1) _
      (Q'.mul_eqv_congr_left
        (valenceFiveIteratedSchurKernelAt
          (FixedLeftCGValenceSix.valenceFivePrefix chain) prior) _ _
        (physicalSchurRecoupling_list_row_normalized
          (valenceSixThirdLeftChannel chain prior)))
      (Q'.mul_one_eqv _)

/-- **The complete three-level bulk recoupling tower has exact mass one.** -/
theorem valenceSixIteratedSchurKernel_row_normalized
    {a b c d e f : Nat} (chain : FixedLeftCGValenceSix a b c d e f) :
    listQSum (valenceSixIteratedSchurKernelAt chain)
      (valenceSixRightTreeTargets chain) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (valenceFiveIteratedSchurKernelAt
        (FixedLeftCGValenceSix.valenceFivePrefix chain))
      (valenceFiveRightTreeTargets
        (FixedLeftCGValenceSix.valenceFivePrefix chain))) _ ?_ ?_
  · exact Q'.eqv_trans _
      (listQSum
        (fun prior =>
          listQSum (valenceSixIteratedSchurKernelAt chain)
            ((physicalSchurRightTargets
              (valenceSixThirdLeftChannel chain prior)).map fun third =>
                ({ prior := prior, third := third } :
                  ValenceSixRightTreeTarget chain)))
        (valenceFiveRightTreeTargets
          (FixedLeftCGValenceSix.valenceFivePrefix chain))) _
      (listQSum_flatMap
        (valenceSixIteratedSchurKernelAt chain)
        (fun prior =>
          (physicalSchurRightTargets
            (valenceSixThirdLeftChannel chain prior)).map fun third =>
              ({ prior := prior, third := third } :
                ValenceSixRightTreeTarget chain))
        (valenceFiveRightTreeTargets
          (FixedLeftCGValenceSix.valenceFivePrefix chain)))
      (listQSum_congr
        (fun prior => thirdFiber_mass chain prior)
        (valenceFiveRightTreeTargets
          (FixedLeftCGValenceSix.valenceFivePrefix chain)))
  · exact valenceFiveIteratedSchurKernel_row_normalized
      (FixedLeftCGValenceSix.valenceFivePrefix chain)

/-! ## 4. Observable pushforward -/

def valenceSixIteratedSchurExpectation {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (observable : ValenceSixRightTreeTarget chain → Q') : Q' :=
  listQSum
    (fun target => valenceSixIteratedSchurKernelAt chain target *
      observable target)
    (valenceSixRightTreeTargets chain)

theorem valenceSixIteratedSchurExpectation_one
    {a b c d e f : Nat} (chain : FixedLeftCGValenceSix a b c d e f) :
    valenceSixIteratedSchurExpectation chain (fun _ => 1) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (valenceSixIteratedSchurKernelAt chain)
      (valenceSixRightTreeTargets chain)) _ ?_
    (valenceSixIteratedSchurKernel_row_normalized chain)
  exact listQSum_congr
    (fun target => Q'.mul_one_eqv
      (valenceSixIteratedSchurKernelAt chain target))
    (valenceSixRightTreeTargets chain)

#print axioms FixedLeftCGValenceSix.valenceFivePrefix
#print axioms valenceSixThirdLeftChannel
#print axioms valenceSixThirdLeftChannel_intermediate
#print axioms valenceSixIteratedSchurKernelAt_nonnegative
#print axioms valenceSixIteratedSchurKernel_row_normalized
#print axioms valenceSixIteratedSchurExpectation_one

end YMGap.Continuum.SU2ValenceSixIteratedSchurTransport
