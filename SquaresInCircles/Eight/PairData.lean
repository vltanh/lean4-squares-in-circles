module

public meta import Lean
public import SquaresInCircles.Eight.Arithmetic.PairCover

/-!
# Reading the coverage trees of a pair table

`pair_trees% "file.trees"` is the `List PairTree` of the trees in the file, one tree per line,
in prefix order: `0` is a gap leaf, `1 lo hi` a trim to `[lo, hi]`, `2`, `3` and `4` bisect the
source tangent, the target tangent and the angle, and `5` is a row leaf. The term is built
directly from raw literals. A path is relative to the directory of the Lean file that uses it.
-/

public meta section
open Lean Elab Term

namespace SquaresInCircles.Eight.PairData
open SquaresInCircles.Eight.Arithmetic.PairCover

/-- The tree whose prefix code starts at position `i`, and the position after it. -/
partial def treeExpr (v : Array Nat) (i : Nat) : TermElabM (Expr × Nat) := do
  let some tag := v[i]? | throwError "pair trees: truncated tree"
  match tag with
  | 0 => return (Lean.mkConst ``PairTree.gap, i + 1)
  | 1 =>
      let some lo := v[i + 1]? | throwError "pair trees: truncated trim"
      let some hi := v[i + 2]? | throwError "pair trees: truncated trim"
      let (t, j) ← treeExpr v (i + 3)
      return (mkApp3 (Lean.mkConst ``PairTree.trim) (mkRawNatLit lo) (mkRawNatLit hi) t, j)
  | 2 | 3 | 4 =>
      let (l, j) ← treeExpr v (i + 1)
      let (r, k) ← treeExpr v j
      let c := if tag == 2 then ``PairTree.source else if tag == 3 then ``PairTree.target
        else ``PairTree.angle
      return (mkApp2 (Lean.mkConst c) l r, k)
  | 5 => return (Lean.mkConst ``PairTree.row, i + 1)
  | _ => throwError "pair trees: unknown tag {tag}"

syntax (name := pairTrees) "pair_trees% " str : term

@[term_elab pairTrees] def elabPairTrees : TermElab := fun stx _ => do
  let `(pair_trees% $path:str) := stx | throwUnsupportedSyntax
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let text ← IO.FS.readFile (dir / path.getString)
  let ty := Lean.mkConst ``PairTree
  let mut trees := #[]
  for line in (text.splitOn "\n").filter (fun l => !l.isEmpty) do
    let mut v := #[]
    for s in line.splitOn " " do
      if !s.isEmpty then
        let some n := s.toNat? | throwError "pair trees: not a natural number: {s}"
        v := v.push n
    let (t, j) ← treeExpr v 0
    if j != v.size then throwError "pair trees: extra tokens in a line"
    trees := trees.push t
  return trees.toList.foldr
    (fun x acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) ty)

end SquaresInCircles.Eight.PairData
