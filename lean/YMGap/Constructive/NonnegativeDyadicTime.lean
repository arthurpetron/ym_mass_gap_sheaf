/-
# Nonnegative dyadic time, with explicit mesh presentations

A mesh point carries `steps / 2^depth`. Cross multiplication defines its
semantic equality; addition computes a common mesh. All arithmetic is on
natural numbers. The quotient supplies representation-independent indexing,
while supplied mesh points remain available as computational data. No
representative is selected from a quotient, and no analytic input is assumed.
-/

import Init

namespace YMGap.Constructive.NonnegativeDyadicTime

set_option autoImplicit false

structure MeshPoint where
  depth : Nat
  steps : Nat

def Equivalent (p q : MeshPoint) : Prop := p.steps * 2^q.depth = q.steps * 2^p.depth

theorem equivalent_refl (p : MeshPoint) : Equivalent p p := rfl

theorem equivalent_symm {p q : MeshPoint} (h : Equivalent p q) : Equivalent q p := h.symm

theorem equivalent_trans {p q r : MeshPoint} (h : Equivalent p q) (k : Equivalent q r) :
    Equivalent p r := by
  apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < (2 : Nat)))
  calc
    2^q.depth * (p.steps * 2^r.depth) = (p.steps * 2^q.depth) * 2^r.depth := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ = (q.steps * 2^p.depth) * 2^r.depth := congrArg (fun n => n * 2^r.depth) h
    _ = (q.steps * 2^r.depth) * 2^p.depth := by
      exact (Nat.mul_assoc _ _ _).trans
        ((congrArg (fun n => q.steps * n) (Nat.mul_comm _ _)).trans (Nat.mul_assoc _ _ _).symm)
    _ = (r.steps * 2^q.depth) * 2^p.depth := congrArg (fun n => n * 2^p.depth) k
    _ = 2^q.depth * (r.steps * 2^p.depth) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def meshSetoid : Setoid MeshPoint where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

def Time : Type := Quotient meshSetoid

def embed (p : MeshPoint) : Time := Quotient.mk meshSetoid p

theorem embed_eq_iff (p q : MeshPoint) : embed p = embed q ↔ Equivalent p q :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

def refine (p : MeshPoint) (extra : Nat) : MeshPoint :=
  ⟨p.depth + extra, p.steps * 2^extra⟩

theorem refine_equivalent (p : MeshPoint) (extra : Nat) : Equivalent (refine p extra) p := by
  simp only [Equivalent, refine, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]

theorem embed_refine (p : MeshPoint) (extra : Nat) : embed (refine p extra) = embed p :=
  Quotient.sound (refine_equivalent p extra)

def addMesh (p q : MeshPoint) : MeshPoint :=
  ⟨p.depth + q.depth, p.steps * 2^q.depth + q.steps * 2^p.depth⟩

theorem addMesh_congr {p p' q q' : MeshPoint} (hp : Equivalent p p') (hq : Equivalent q q') :
    Equivalent (addMesh p q) (addMesh p' q') := by
  have h := congrArg (fun n => n * (2^q.depth * 2^q'.depth)) hp
  have k := congrArg (fun n => n * (2^p.depth * 2^p'.depth)) hq
  simpa only [Equivalent, addMesh, Nat.pow_add, Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (congrArg (fun n => n + (q.steps * 2^q'.depth) * (2^p.depth * 2^p'.depth)) h).trans
        (congrArg (fun n => (p'.steps * 2^p.depth) * (2^q.depth * 2^q'.depth) + n) k)

def add : Time → Time → Time :=
  Quotient.lift₂ (fun p q => embed (addMesh p q))
    (fun _ _ _ _ hp hq => Quotient.sound (addMesh_congr hp hq))

theorem add_embed (p q : MeshPoint) : add (embed p) (embed q) = embed (addMesh p q) := rfl

def zero : Time := embed ⟨0,0⟩

def whole (n : Nat) : Time := embed ⟨0,n⟩

theorem add_comm (s t : Time) : add s t = add t s := by
  refine Quotient.inductionOn₂ s t ?_
  intro p q
  apply Quotient.sound
  change Equivalent (addMesh p q) (addMesh q p)
  simp only [Equivalent, addMesh, Nat.add_comm]

theorem add_assoc (s t u : Time) : add (add s t) u = add s (add t u) := by
  refine Quotient.inductionOn₃ s t u ?_
  intro p q r
  apply Quotient.sound
  change Equivalent (addMesh (addMesh p q) r) (addMesh p (addMesh q r))
  simp only [Equivalent, addMesh, Nat.pow_add, Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem zero_add (t : Time) : add zero t = t := by
  refine Quotient.inductionOn t ?_
  intro p
  apply Quotient.sound
  change Equivalent (addMesh ⟨0,0⟩ p) p
  simp only [Equivalent, addMesh, Nat.zero_add, Nat.zero_mul, Nat.pow_zero, Nat.mul_one]

theorem add_zero (t : Time) : add t zero = t := (add_comm t zero).trans (zero_add t)

theorem whole_zero : whole 0 = zero := rfl

theorem whole_add (m n : Nat) : whole (m+n) = add (whole m) (whole n) := by
  apply Quotient.sound
  change Equivalent ⟨0,m+n⟩ (addMesh ⟨0,m⟩ ⟨0,n⟩)
  simp only [Equivalent, addMesh, Nat.zero_add, Nat.pow_zero, Nat.mul_one]

/-- Addition on one supplied mesh has precisely the expected step count. -/
theorem same_mesh_add (depth m n : Nat) :
    add (embed ⟨depth,m⟩) (embed ⟨depth,n⟩) = embed ⟨depth,m+n⟩ := by
  apply Quotient.sound
  change Equivalent (addMesh ⟨depth,m⟩ ⟨depth,n⟩) ⟨depth,m+n⟩
  simp only [Equivalent, addMesh, Nat.pow_add, Nat.add_mul, Nat.mul_assoc]

end YMGap.Constructive.NonnegativeDyadicTime

#print axioms YMGap.Constructive.NonnegativeDyadicTime.MeshPoint
#print axioms YMGap.Constructive.NonnegativeDyadicTime.Equivalent
#print axioms YMGap.Constructive.NonnegativeDyadicTime.equivalent_refl
#print axioms YMGap.Constructive.NonnegativeDyadicTime.equivalent_symm
#print axioms YMGap.Constructive.NonnegativeDyadicTime.equivalent_trans
#print axioms YMGap.Constructive.NonnegativeDyadicTime.meshSetoid
#print axioms YMGap.Constructive.NonnegativeDyadicTime.Time
#print axioms YMGap.Constructive.NonnegativeDyadicTime.embed
#print axioms YMGap.Constructive.NonnegativeDyadicTime.embed_eq_iff
#print axioms YMGap.Constructive.NonnegativeDyadicTime.refine
#print axioms YMGap.Constructive.NonnegativeDyadicTime.refine_equivalent
#print axioms YMGap.Constructive.NonnegativeDyadicTime.embed_refine
#print axioms YMGap.Constructive.NonnegativeDyadicTime.addMesh
#print axioms YMGap.Constructive.NonnegativeDyadicTime.addMesh_congr
#print axioms YMGap.Constructive.NonnegativeDyadicTime.add
#print axioms YMGap.Constructive.NonnegativeDyadicTime.add_embed
#print axioms YMGap.Constructive.NonnegativeDyadicTime.zero
#print axioms YMGap.Constructive.NonnegativeDyadicTime.whole
#print axioms YMGap.Constructive.NonnegativeDyadicTime.add_comm
#print axioms YMGap.Constructive.NonnegativeDyadicTime.add_assoc
#print axioms YMGap.Constructive.NonnegativeDyadicTime.zero_add
#print axioms YMGap.Constructive.NonnegativeDyadicTime.add_zero
#print axioms YMGap.Constructive.NonnegativeDyadicTime.whole_zero
#print axioms YMGap.Constructive.NonnegativeDyadicTime.whole_add
#print axioms YMGap.Constructive.NonnegativeDyadicTime.same_mesh_add
