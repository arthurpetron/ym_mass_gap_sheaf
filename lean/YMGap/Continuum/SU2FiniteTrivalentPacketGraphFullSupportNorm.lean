/-
# Full-support norm formulas for finite trivalent packet graphs

The actual finite-graph operator was initially written as a sum over the
list obtained by filtering the bounded Cartesian labellings through the
physical projector.  That is convenient for locating the spectrum, but it
is inconvenient for comparing different cutoffs or graph volumes because
the filtered index list changes.

Here the same exact norms are rewritten as sums over *all* bounded edge
labellings.  The already-constructed gauge/vacuum projector makes every
unphysical summand exactly zero.  Thus future cutoff and volume maps may use
one explicit Cartesian domain without choosing or matching retained-mode
indices.

Honest scope: this is a finite exact reindexing theorem.  It supplies the
stable summation presentation needed by directed limits; it does not itself
construct a thermodynamic or continuum limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

set_option maxHeartbeats 800000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## Generic finite-list summation lemmas -/

def listQSum {A : Type} (f : A → Q') : List A → Q'
  | [] => 0
  | x :: xs => f x + listQSum f xs

theorem listQSum_congr {A : Type} {f g : A → Q'}
    (h : ∀ x, f x ≈ g x) : ∀ xs, listQSum f xs ≈ listQSum g xs
  | [] => Q'.eqv_refl 0
  | x :: xs => Q'.add_eqv_congr' (h x) (listQSum_congr h xs)

private theorem fsum_head_tail (f : Nat → Q') : ∀ n,
    fsum f (n + 1) ≈ f 0 + fsum (fun i => f (i + 1)) n
  | 0 => by
      change (0 + f 0) ≈ f 0 + 0
      exact Q'.eqv_trans _ (f 0) _
        (Q'.eqv_of_eq (Q'.zero_add' _))
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))
  | n + 1 => by
      rw [fsum_succ, fsum_succ]
      exact Q'.eqv_trans _
        ((f 0 + fsum (fun i => f (i + 1)) n) + f (n + 1)) _
        (Q'.add_eqv_congr' (fsum_head_tail f n) (Q'.eqv_refl _))
        (Q'.add_assoc_eqv _ _ _)

private theorem supportLabel_cons_zero (x : EdgeLabelling)
    (xs : List EdgeLabelling) : supportLabel (x :: xs) 0 = x := by
  rfl

private theorem supportLabel_cons_succ (x : EdgeLabelling)
    (xs : List EdgeLabelling) (i : Nat) :
    supportLabel (x :: xs) (i + 1) = supportLabel xs i := by
  unfold supportLabel
  simp

/-- Indexed `fsum` over `supportLabel` is exactly the structural list sum.
This removes all dependence on the particular retained-mode indices. -/
theorem fsum_supportLabel_eq_listQSum (f : EdgeLabelling → Q') : ∀ support,
    fsum (fun i => f (supportLabel support i)) support.length ≈
      listQSum f support
  | [] => Q'.eqv_refl 0
  | x :: xs => by
      change fsum (fun i => f (supportLabel (x :: xs) i)) (xs.length + 1) ≈
        f x + listQSum f xs
      refine Q'.eqv_trans _
        (f (supportLabel (x :: xs) 0) +
          fsum (fun i => f (supportLabel (x :: xs) (i + 1))) xs.length) _
        (fsum_head_tail (fun i => f (supportLabel (x :: xs) i)) xs.length) ?_
      rw [supportLabel_cons_zero]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _
          (fsum (fun i => f (supportLabel xs i)) xs.length) _
          (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _
            (fun i => by
              rw [supportLabel_cons_succ]
              exact Q'.eqv_refl _) xs.length)
          (fsum_supportLabel_eq_listQSum f xs))

/-- Filtering is equivalent to retaining the original list and replacing
every rejected term by exact zero. -/
theorem listQSum_filter (f : EdgeLabelling → Q')
    (p : EdgeLabelling → Bool) : ∀ xs,
    listQSum f (xs.filter p) ≈
      listQSum (fun x => if p x then f x else 0) xs
  | [] => Q'.eqv_refl 0
  | x :: xs => by
      cases hp : p x with
      | false =>
          simp only [List.filter, hp, Bool.false_eq_true, if_false, listQSum]
          exact Q'.eqv_trans _
            (listQSum (fun y => if p y then f y else 0) xs) _
            (listQSum_filter f p xs)
            (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
      | true =>
          simp only [List.filter, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter f p xs)

/-! ## Full Cartesian formulas for the exact graph norms -/

def projectedSquare {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling) : Q' :=
  let a := packetGraphProjectedAmplitude edges vertices packet label
  a * a

def transferredProjectedSquare {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling) : Q' :=
  let y := graphTransfer edges
    (packetGraphProjectedAmplitude edges vertices packet) label
  y * y

theorem projectedSquare_zero_of_unphysical {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    (h : graphPhysicalB edges vertices label = false) :
    projectedSquare edges vertices packet label ≈ 0 := by
  unfold projectedSquare packetGraphProjectedAmplitude
    graphGaugeVacuumProject
  rw [if_neg (by simpa using h)]
  exact Q'.mul_zero_eqv 0

theorem transferredProjectedSquare_zero_of_unphysical {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    (h : graphPhysicalB edges vertices label = false) :
    transferredProjectedSquare edges vertices packet label ≈ 0 := by
  unfold transferredProjectedSquare packetGraphProjectedAmplitude
    graphTransfer graphGaugeVacuumProject
  rw [if_neg (by simpa using h)]
  exact Q'.eqv_trans _ ((graphEigen edges label * 0) * 0) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
    (Q'.mul_zero_eqv _)

def packetGraphFullExactNorm {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : Q' :=
  listQSum (projectedSquare edges vertices packet)
    (boundedEdgeLabellings K edges)

def packetGraphFullTransferredNorm {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : Q' :=
  listQSum (transferredProjectedSquare edges vertices packet)
    (boundedEdgeLabellings K edges)

private theorem projected_filter_eq_full {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    listQSum (projectedSquare edges vertices packet)
        (physicalEdgeLabellings K edges vertices) ≈
      packetGraphFullExactNorm edges vertices packet := by
  unfold physicalEdgeLabellings packetGraphFullExactNorm
  refine Q'.eqv_trans _
    (listQSum
      (fun label => if graphPhysicalB edges vertices label then
        projectedSquare edges vertices packet label else 0)
      (boundedEdgeLabellings K edges)) _
    (listQSum_filter _ _ _) ?_
  apply listQSum_congr
  intro label
  cases h : graphPhysicalB edges vertices label with
  | false =>
      exact Q'.eqv_symm
        (projectedSquare_zero_of_unphysical edges vertices packet label h)
  | true =>
      exact Q'.eqv_refl _

private theorem transferred_filter_eq_full {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    listQSum (transferredProjectedSquare edges vertices packet)
        (physicalEdgeLabellings K edges vertices) ≈
      packetGraphFullTransferredNorm edges vertices packet := by
  unfold physicalEdgeLabellings packetGraphFullTransferredNorm
  refine Q'.eqv_trans _
    (listQSum
      (fun label => if graphPhysicalB edges vertices label then
        transferredProjectedSquare edges vertices packet label else 0)
      (boundedEdgeLabellings K edges)) _
    (listQSum_filter _ _ _) ?_
  apply listQSum_congr
  intro label
  cases h : graphPhysicalB edges vertices label with
  | false =>
      exact Q'.eqv_symm
        (transferredProjectedSquare_zero_of_unphysical
          edges vertices packet label h)
  | true =>
      exact Q'.eqv_refl _

/-- The exact time-zero norm is the complete Cartesian sum; no matching of
filtered physical-mode indices is required. -/
theorem packetGraphExactNorm_eq_full {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    packetGraphExactNorm edges vertices packet ≈
      packetGraphFullExactNorm edges vertices packet := by
  unfold packetGraphExactNorm finiteNetworkFamilyNorm packetGraphModeWeight
    physicalModeLabel
  change fsum
      (fun i => projectedSquare edges vertices packet
        (supportLabel (physicalEdgeLabellings K edges vertices) i))
      (physicalEdgeLabellings K edges vertices).length ≈
    packetGraphFullExactNorm edges vertices packet
  exact Q'.eqv_trans _
    (listQSum (projectedSquare edges vertices packet)
      (physicalEdgeLabellings K edges vertices)) _
    (fsum_supportLabel_eq_listQSum _ _)
    (projected_filter_eq_full edges vertices packet)

/-- The explicit transferred norm has the same complete Cartesian
presentation, again with exact-zero unphysical terms. -/
theorem packetGraphOperatorTransferredNorm_eq_full {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) :
    packetGraphOperatorTransferredNorm edges vertices packet ≈
      packetGraphFullTransferredNorm edges vertices packet := by
  unfold packetGraphOperatorTransferredNorm physicalModeLabel
  change fsum
      (fun i => transferredProjectedSquare edges vertices packet
        (supportLabel (physicalEdgeLabellings K edges vertices) i))
      (physicalEdgeLabellings K edges vertices).length ≈
    packetGraphFullTransferredNorm edges vertices packet
  exact Q'.eqv_trans _
    (listQSum (transferredProjectedSquare edges vertices packet)
      (physicalEdgeLabellings K edges vertices)) _
    (fsum_supportLabel_eq_listQSum _ _)
    (transferred_filter_eq_full edges vertices packet)

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.fsum_supportLabel_eq_listQSum
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.listQSum_filter
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.projectedSquare_zero_of_unphysical
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.transferredProjectedSquare_zero_of_unphysical
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.packetGraphExactNorm_eq_full
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.packetGraphOperatorTransferredNorm_eq_full
