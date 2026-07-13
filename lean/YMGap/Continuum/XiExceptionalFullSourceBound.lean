/-
# Full exceptional source bound

The subtype enumeration attaches the actual membership proof to every
exceptional occurrence pair.  Its value projection is exactly the filtered
exceptional source list, so duplicate-freeness and the weighted sum descend
constructively.  The path-safe singleton injection then bounds the complete
exceptional source sum by the connecting-chain carrier times `XiR`.
-/

import YMGap.Continuum.XiExceptionalPathSafeSummation

namespace YMGap.Continuum.XiExceptionalFullSourceBound

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathSafeExactWeight
open YMGap.Continuum.XiExceptionalPathSafeSummation

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def fullExceptionalSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (ExceptionalSourceEntry Gamma qP b1 b2) :=
  (exceptionalSourceCodes Gamma qP b1 b2).attach

private theorem map_attach_val : ∀ xs : List alpha,
    xs.attach.map (fun x => x.1) = xs
  | xs => List.attach_map_subtype_val xs

private theorem nodup_of_map_nodup (f : alpha → beta) :
    ∀ xs : List alpha, (xs.map f).Nodup → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hp := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      constructor
      · intro hx
        exact hp.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)
      · exact nodup_of_map_nodup f xs hp.2

theorem fullExceptionalSource_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (fullExceptionalSource Gamma qP b1 b2).Nodup := by
  apply nodup_of_map_nodup (fun entry => entry.1)
  rw [show (fullExceptionalSource Gamma qP b1 b2).map
      (fun entry => entry.1) = exceptionalSourceCodes Gamma qP b1 b2 by
    exact map_attach_val (exceptionalSourceCodes Gamma qP b1 b2)]
  exact exceptionalSourceCodes_nodup Gamma qP b1 b2

theorem fullExceptionalSource_weight_eq
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum (pathSafeSourceWeight w qP b1 b2 Gamma label)
        (fullExceptionalSource Gamma qP b1 b2) =
      qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) := by
  rw [show exceptionalSourceCodes Gamma qP b1 b2 =
      (fullExceptionalSource Gamma qP b1 b2).map (fun entry => entry.1) by
    exact (map_attach_val (exceptionalSourceCodes Gamma qP b1 b2)).symm]
  rw [qListSum_map]
  rfl

theorem full_exceptional_source_le_chain_mul_XiR
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (hfacts : ∀ entry, entry ∈ fullExceptionalSource Gamma qP b1 b2 →
      PathSafeRoutedFacts Gamma qP b1 b2 entry) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) ≤
      connectingChainMajorant w qP b1 b2 Gamma label *
        XiR w qP Gamma label := by
  have hglobal := pathSafe_region_global_bound hw Gamma qP b1 b2 label
    (fullExceptionalSource Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2) hfacts
  rw [fullExceptionalSource_weight_eq] at hglobal
  exact Q'.le_trans' _ _ _ hglobal
    (Q'.le_of_eqv
      (occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
        w qP b1 b2 Gamma label))

#print axioms fullExceptionalSource_nodup
#print axioms fullExceptionalSource_weight_eq
#print axioms full_exceptional_source_le_chain_mul_XiR

end YMGap.Continuum.XiExceptionalFullSourceBound
