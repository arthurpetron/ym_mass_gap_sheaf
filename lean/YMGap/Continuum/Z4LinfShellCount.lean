/-
# Finite L-infinity shell counting

Every nodup finite face list has at most the explicit translated-box size in
each L-infinity shell.  This is only a finite lattice counting statement; no
geometric summability or thermodynamic limit is asserted.
-/

import YMGap.Continuum.Z4LinfFiniteRegion
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.Z4LinfShellCount

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.Z4LinfFiniteRegion (region mem_region_of_linf region_length)
open YMGap.Continuum.CayleyPruferInjection (nodup_subset_length_le)

theorem ball_count (root : Z4Plaq) (radius : Nat) (faces : List Z4Plaq)
    (hfaces : faces.Nodup) :
    (faces.filter (fun face => decide (linfDist root face ≤ radius))).length ≤
      (2*radius+1)^4*6 := by
  have hlen := nodup_subset_length_le
    (faces.filter (fun face => decide (linfDist root face ≤ radius)))
    (region root radius) (hfaces.filter _) (by
      intro face hface
      exact mem_region_of_linf root face radius (of_decide_eq_true (List.mem_filter.mp hface).2))
  rw [region_length] at hlen
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul] using hlen

theorem shell_count_le (root : Z4Plaq) (faces : List Z4Plaq)
    (hfaces : faces.Nodup) (n : Nat) :
    (faces.filter (fun face => decide (linfDist root face = n))).length ≤
      ((2*n+1)*(2*n+1)*(2*n+1)*(2*n+1))*6 := by
  have hlen := nodup_subset_length_le
    (faces.filter (fun face => decide (linfDist root face = n)))
    (region root n) (hfaces.filter _) (by
      intro face hface
      have hf := List.mem_filter.mp hface
      apply mem_region_of_linf root face n
      exact Nat.le_of_eq (of_decide_eq_true hf.2))
  rw [region_length] at hlen
  exact hlen

end YMGap.Continuum.Z4LinfShellCount

#print axioms YMGap.Continuum.Z4LinfShellCount.shell_count_le
#print axioms YMGap.Continuum.Z4LinfShellCount.ball_count
