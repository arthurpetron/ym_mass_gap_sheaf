/-
# Two successive physical Schur moves on a valence-five chain

A production valence-five link has four external factors and the left tree

  (((a b) c) d) -> e.

The first physical Schur row changes `((a b) c) -> y` into
`(a (b c)) -> y`.  For each resulting right channel, its outer step
`a (b c) -> y` combines with the retained production suffix `y d -> e` to
form a new physical left channel.  A second Schur row then produces the fully
right-associated tree `a ((b c) d) -> e`.

The second target type and row depend on the first recoupling target.  This
module enumerates that finite tower literally and proves that the product
kernel has exact mass one.

No Gibbs weight, global link product, OS form bound, or continuum claim is
made here.

Constructive contract: exact `Q'`, finite lists, no choice, no `Classical`,
no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
import YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The second physical left channel depends on the first target -/

/-- After the first reassociation, fuse `a` with the new `(b,c)` channel to
the retained prefix output `y`, then fuse `y` with `d` to `e`. -/
def valenceFiveSecondLeftChannel {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e)
    (first : FixedRightCGChannel a b c chain.y) :
    FixedLeftCGChannel a first.intermediate d e :=
  fixedLeftChannelOfFusion a first.intermediate d e chain.y
    (fixedRight_outer_fusionOK first) chain.third.fusionOK

theorem valenceFiveSecondLeftChannel_intermediate {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e)
    (first : FixedRightCGChannel a b c chain.y) :
    (valenceFiveSecondLeftChannel chain first).intermediate = chain.y := by
  exact fixedLeftChannelOfFusion_intermediate
    a first.intermediate d e chain.y
    (fixedRight_outer_fusionOK first) chain.third.fusionOK

/-! ## 2. A literal dependent tower of fully right-associated targets -/

/-- One fully right-associated target retains both dependent Schur choices:
the `(b,c)` channel and then the `((b,c),d)` channel. -/
structure ValenceFiveRightTreeTarget {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e) where
  first : FixedRightCGChannel a b c chain.y
  second : FixedRightCGChannel a first.intermediate d e

/-- The complete finite target tower. -/
def valenceFiveRightTreeTargets {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e) :
    List (ValenceFiveRightTreeTarget chain) :=
  (physicalSchurRightTargets chain.prefixChannel).flatMap fun first =>
    (physicalSchurRightTargets
      (valenceFiveSecondLeftChannel chain first)).map fun second =>
        { first := first, second := second }

/-- Product of the first and conditional second physical Schur
probabilities. -/
def valenceFiveIteratedSchurKernelAt {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e)
    (target : ValenceFiveRightTreeTarget chain) : Q' :=
  physicalSchurRecouplingKernelAt chain.prefixChannel target.first *
    physicalSchurRecouplingKernelAt
      (valenceFiveSecondLeftChannel chain target.first) target.second

theorem valenceFiveIteratedSchurKernelAt_nonnegative
    {a b c d e : Nat} (chain : FixedLeftCGValenceFive a b c d e)
    (target : ValenceFiveRightTreeTarget chain) :
    (0 : Q') ≤ valenceFiveIteratedSchurKernelAt chain target := by
  exact Q'.mul_nonneg _ _
    (physicalSchurRecouplingKernelAt_nonnegative
      chain.prefixChannel target.first)
    (physicalSchurRecouplingKernelAt_nonnegative
      (valenceFiveSecondLeftChannel chain target.first) target.second)

private theorem secondFiber_mass
    {a b c d e : Nat} (chain : FixedLeftCGValenceFive a b c d e)
    (first : FixedRightCGChannel a b c chain.y) :
    listQSum (valenceFiveIteratedSchurKernelAt chain)
        ((physicalSchurRightTargets
          (valenceFiveSecondLeftChannel chain first)).map fun second =>
            ({ first := first, second := second } :
              ValenceFiveRightTreeTarget chain)) ≈
      physicalSchurRecouplingKernelAt chain.prefixChannel first := by
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (physicalSchurRecouplingKernelAt chain.prefixChannel first *
      listQSum
        (physicalSchurRecouplingKernelAt
          (valenceFiveSecondLeftChannel chain first))
        (physicalSchurRightTargets
          (valenceFiveSecondLeftChannel chain first))) _ ?_ ?_
  · exact listQSum_mul_left
      (physicalSchurRecouplingKernelAt chain.prefixChannel first)
      (physicalSchurRecouplingKernelAt
        (valenceFiveSecondLeftChannel chain first))
      (physicalSchurRightTargets
        (valenceFiveSecondLeftChannel chain first))
  · exact Q'.eqv_trans _
      (physicalSchurRecouplingKernelAt chain.prefixChannel first * 1) _
      (Q'.mul_eqv_congr_left
        (physicalSchurRecouplingKernelAt chain.prefixChannel first) _ _
        (physicalSchurRecoupling_list_row_normalized
          (valenceFiveSecondLeftChannel chain first)))
      (Q'.mul_one_eqv _)

/-- **The two dependent Schur moves have exact total mass one.** -/
theorem valenceFiveIteratedSchurKernel_row_normalized
    {a b c d e : Nat} (chain : FixedLeftCGValenceFive a b c d e) :
    listQSum (valenceFiveIteratedSchurKernelAt chain)
      (valenceFiveRightTreeTargets chain) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (physicalSchurRecouplingKernelAt chain.prefixChannel)
      (physicalSchurRightTargets chain.prefixChannel)) _ ?_ ?_
  · exact Q'.eqv_trans _
      (listQSum
        (fun first =>
          listQSum (valenceFiveIteratedSchurKernelAt chain)
            ((physicalSchurRightTargets
              (valenceFiveSecondLeftChannel chain first)).map fun second =>
                ({ first := first, second := second } :
                  ValenceFiveRightTreeTarget chain)))
        (physicalSchurRightTargets chain.prefixChannel)) _
      (listQSum_flatMap
        (valenceFiveIteratedSchurKernelAt chain)
        (fun first =>
          (physicalSchurRightTargets
            (valenceFiveSecondLeftChannel chain first)).map fun second =>
              ({ first := first, second := second } :
                ValenceFiveRightTreeTarget chain))
        (physicalSchurRightTargets chain.prefixChannel))
      (listQSum_congr
        (fun first => secondFiber_mass chain first)
        (physicalSchurRightTargets chain.prefixChannel))
  · exact physicalSchurRecoupling_list_row_normalized chain.prefixChannel

/-! ## 3. Observable pushforward -/

def valenceFiveIteratedSchurExpectation {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e)
    (observable : ValenceFiveRightTreeTarget chain → Q') : Q' :=
  listQSum
    (fun target => valenceFiveIteratedSchurKernelAt chain target *
      observable target)
    (valenceFiveRightTreeTargets chain)

theorem valenceFiveIteratedSchurExpectation_one
    {a b c d e : Nat} (chain : FixedLeftCGValenceFive a b c d e) :
    valenceFiveIteratedSchurExpectation chain (fun _ => 1) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (valenceFiveIteratedSchurKernelAt chain)
      (valenceFiveRightTreeTargets chain)) _ ?_
    (valenceFiveIteratedSchurKernel_row_normalized chain)
  exact listQSum_congr
    (fun target => Q'.mul_one_eqv
      (valenceFiveIteratedSchurKernelAt chain target))
    (valenceFiveRightTreeTargets chain)

#print axioms valenceFiveSecondLeftChannel
#print axioms valenceFiveSecondLeftChannel_intermediate
#print axioms valenceFiveIteratedSchurKernelAt_nonnegative
#print axioms valenceFiveIteratedSchurKernel_row_normalized
#print axioms valenceFiveIteratedSchurExpectation_one

end YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport
