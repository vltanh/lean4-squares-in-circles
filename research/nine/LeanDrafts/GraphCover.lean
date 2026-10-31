import Std

/-!
# Six-body graph/load cover — uncompiled implementation draft

This file was not compiled: the editing environment has no Lean executable.
The proposed proofs use only ordinary `decide`, hence ordinary kernel reduction.
No geometry, original gate closure, graph-planarity classification, or portability
result is claimed by this file. The nine chord graph types are inputs.

Each mask is a natural number below 64. Bit i denotes the actual vertex i.
`permutation` ranges over all six rotations and six reflections. `stabilizes`
checks the FULL chorded graph, so it does not discard any positive edge.

`necessary` uses a deliberately elementary necessary relaxation of the original
loaded-path-forest/complement-connected conditions: maximum degree two, no
triangle, fewer edges than vertices, and at most one edge for three loads.
A physical caller still has to prove these conditions and the original loading
and short-chord-bypass lemmas. Coverage here does not supply that caller.
-/

namespace SquaresInCircles.Nine.GraphCoverDraft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def vertices : List Nat := [0, 1, 2, 3, 4, 5]

def pairs : List (Nat × Nat) :=
  vertices.flatMap fun i =>
    (vertices.filter fun j => decide (i < j)).map fun j => (i, j)

def triples : List (Nat × Nat × Nat) :=
  vertices.flatMap fun i => vertices.flatMap fun j =>
    (vertices.filter fun k => decide (i < j ∧ j < k)).map fun k => (i, j, k)

def chords : List (List (Nat × Nat)) :=
  [[], [(0, 2)], [(0, 3)], [(0, 2), (0, 3)],
   [(0, 2), (0, 4)], [(0, 2), (3, 5)],
   [(0, 2), (0, 3), (0, 4)], [(0, 2), (0, 3), (3, 5)],
   [(0, 2), (0, 4), (2, 4)]]

def edge (g i j : Nat) : Bool :=
  (i != j) &&
    ((j == (i + 1) % 6) || (i == (j + 1) % 6) ||
     (chords.getD g []).any fun p =>
       ((i == p.1) && (j == p.2)) || ((i == p.2) && (j == p.1)))

def has (mask i : Nat) : Bool := (mask / (2 ^ i)) % 2 == 1

def count (mask : Nat) : Nat := (vertices.filter fun i => has mask i).length

def degree (g mask i : Nat) : Nat :=
  (vertices.filter fun j => has mask j && edge g i j).length

def edgeCount (g mask : Nat) : Nat :=
  (pairs.filter fun p => has mask p.1 && has mask p.2 && edge g p.1 p.2).length

def hasTriangle (g mask : Nat) : Bool :=
  triples.any fun t =>
    has mask t.1 && has mask t.2.1 && has mask t.2.2 &&
    edge g t.1 t.2.1 && edge g t.1 t.2.2 && edge g t.2.1 t.2.2

def forced (g i : Nat) : Bool :=
  let d := degree g 63 i
  let n := (pairs.filter fun p =>
    edge g i p.1 && edge g i p.2 && edge g p.1 p.2).length
  ((d == 2) && decide (1 ≤ n)) || ((d == 3) && decide (2 ≤ n))

def permutation (s i : Nat) : Nat :=
  if s < 6 then (i + s) % 6 else (s - 6 + 6 - i) % 6

def stabilizes (g s : Nat) : Bool :=
  pairs.all fun p => edge g p.1 p.2 == edge g (permutation s p.1) (permutation s p.2)

def moved (mask s : Nat) : Nat :=
  vertices.foldl (fun acc i =>
    if has mask i then acc + 2 ^ permutation s i else acc) 0

def inOrbit (g mask target : Nat) : Bool :=
  (List.range 12).any fun s => stabilizes g s && (moved mask s == target)

-- Table order: none, 02, 03, 02+03, 02+04, 02+35,
--              02+03+04, 02+03+35, 02+04+24.
-- The 40 entries include the two separately proved bare-cycle exits.
def table : List (List Nat) :=
  [[11, 21, 15, 23, 27, 31],
   [19, 26, 42, 27, 43, 51, 58, 59],
   [19, 21, 22, 23, 39, 27, 54, 55],
   [22, 38, 30, 46, 54, 62],
   [38, 42, 43, 46, 54, 62],
   [27, 51], [62], [54], [42, 43]]

def necessary (g mask : Nat) : Bool :=
  let k := count mask
  let e := edgeCount g mask
  decide (3 ≤ k ∧ k ≤ 5) &&
  vertices.all (fun i => !(forced g i) || has mask i) &&
  vertices.all (fun i => !(has mask i) || decide (degree g mask i ≤ 2)) &&
  !(hasTriangle g mask) && decide (e < k) &&
  ((k != 3) || decide (e ≤ 1)) &&
  ((g != 5) || ((has mask 0 || has mask 2) && (has mask 3 || has mask 5))) &&
  ((g != 1) || !(inOrbit g mask 11))

def represented (g mask : Nat) : Bool :=
  (table.getD g []).any fun target => inOrbit g mask target

def Cover (g : Nat) : Prop :=
  ∀ mask : Fin 64, necessary g mask.val = true → represented g mask.val = true

-- Split into nine small finite obligations rather than one expanded proof.
theorem cover_none : Cover 0 := by decide
theorem cover_02 : Cover 1 := by decide
theorem cover_03 : Cover 2 := by decide
theorem cover_0203 : Cover 3 := by decide
theorem cover_0204 : Cover 4 := by decide
theorem cover_0235 : Cover 5 := by decide
theorem cover_fan : Cover 6 := by decide
theorem cover_chord_path : Cover 7 := by decide
theorem cover_central_triangle : Cover 8 := by decide

theorem dihedral_injective :
    ∀ s : Fin 12, ∀ i j : Fin 6,
      permutation s.val i.val = permutation s.val j.val → i = j := by decide

theorem forty_representatives : (table.map List.length).foldl (· + ·) 0 = 40 := by decide

def survivingTable : List (List Nat) :=
  table.zipIdx |>.map fun row =>
    if row.2 == 0 then row.1.filter (fun mask => mask != 11 && mask != 15) else row.1

theorem thirty_eight_after_bare_exits :
    (survivingTable.map List.length).foldl (· + ·) 0 = 38 := by decide

#print axioms cover_none
#print axioms cover_02
#print axioms cover_03
#print axioms cover_0203
#print axioms cover_0204
#print axioms cover_0235
#print axioms cover_fan
#print axioms cover_chord_path
#print axioms cover_central_triangle

end SquaresInCircles.Nine.GraphCoverDraft
