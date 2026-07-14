/-
# Sharp fuel fence for the cross-conflict ear

The endpoint-preserving cross ear absorbs two new occurrences but inserts
four walk vertices.  Consequently, when the original path already uses all
but two ambient occurrences, the ear has length `N + 2` and cannot fit even
the sharp old-carrier capacity `N + 1`.
-/

import YMGap.Continuum.XiExceptionalCrossConflictEar

namespace YMGap.Continuum.XiExceptionalCrossEarFuelFence

open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalCrossConflictEar

theorem endpointCrossEar_length_eq_ambient_add_two
    {a : Type} {edge : a -> a -> Bool}
    {x pivot y : a}
    (pre : CWalk edge x pivot) (suf : CWalk edge pivot y)
    (u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (hvu : edge v u = true) (hup : edge u pivot = true)
    (N : Nat)
    (htight : (pre.append suf).vertices.length + 2 = N) :
    (CWalk.endpointCrossEar pre suf u v hpu huv hvu hup).vertices.length =
      N + 2 := by
  rw [CWalk.endpointCrossEar_vertices_length]
  omega

/-- Exact carrier-capacity obstruction: `N+2` vertices cannot inhabit the
sharp `N+1` walk window. -/
theorem endpointCrossEar_not_in_sharp_capacity_of_tight
    {a : Type} {edge : a -> a -> Bool}
    {x pivot y : a}
    (pre : CWalk edge x pivot) (suf : CWalk edge pivot y)
    (u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (hvu : edge v u = true) (hup : edge u pivot = true)
    (N : Nat)
    (htight : (pre.append suf).vertices.length + 2 = N) :
    ¬ ((CWalk.endpointCrossEar pre suf u v hpu huv hvu hup).vertices.length
      ≤ N + 1) := by
  rw [endpointCrossEar_length_eq_ambient_add_two pre suf u v
    hpu huv hvu hup N htight]
  omega

/-- The minimal actual size from the four-occurrence fence: a two-vertex
base becomes a six-vertex ear, strictly beyond the sharp capacity five. -/
theorem two_vertex_crossEar_length_six
    {a : Type} {edge : a -> a -> Bool}
    {x pivot y : a}
    (pre : CWalk edge x pivot) (suf : CWalk edge pivot y)
    (u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (hvu : edge v u = true) (hup : edge u pivot = true)
    (hbase : (pre.append suf).vertices.length = 2) :
    (CWalk.endpointCrossEar pre suf u v hpu huv hvu hup).vertices.length = 6 := by
  rw [CWalk.endpointCrossEar_vertices_length, hbase]

theorem six_not_le_five : ¬ (6 ≤ 5) := by omega

#print axioms endpointCrossEar_length_eq_ambient_add_two
#print axioms endpointCrossEar_not_in_sharp_capacity_of_tight
#print axioms two_vertex_crossEar_length_six
#print axioms six_not_le_five

end YMGap.Continuum.XiExceptionalCrossEarFuelFence
