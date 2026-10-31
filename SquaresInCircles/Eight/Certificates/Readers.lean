module

public import SquaresInCircles.Eight.Arithmetic.PairCover
public meta import Lean

/-!
# Reading certificate rows and coverage trees

The integer, natural-number and tree readers elaborate data into ordinary constructors.
Paths are relative to the source file using the notation. All mathematical properties are
proved by the certificate checks.
-/

public meta section

/-! # Eight squares: integer data files

`int_rows% "file"` is the `List (List Int)` whose rows are the nonempty lines of `file`, each a
list of decimal integers separated by single spaces; `int_rows% "file" a b` keeps the rows
`a, …, b - 1`, counted from `0`. `nat_rows%` is the same for natural numbers, with values
`List (List ℕ)`, and a negative entry is an error. With `↦ f` at the end, each line `n₁ … nₖ`
becomes `f n₁ … nₖ` instead of a list, so that a row is read without decoding a list. If the
last parameter of `f` is a list of numbers, a line `n₁ … nₖ m₁ … mⱼ` with `k` the number of the
other parameters becomes `f n₁ … nₖ [m₁, …, mⱼ]`, so lines may differ in length. The values of
`f` must be data, not proofs. The path is relative to the directory of the source file that uses
the notation.

The term is built directly from raw literals: a natural number is a raw literal, and an integer
is `Int.ofNat n` or `Int.negSucc n` with `n` a raw literal. No numeral is elaborated, and the
kernel reads each number in constant time. The notation produces data only; every property of
the rows is a separate theorem.

A module using the notation reads each of its files once, when it is elaborated, so it must be
rebuilt after a file changes. The generated tables of `Generated/Affine/`, `Generated/Owner/` and
`Generated/Pairs/` read their data from `data/eight/` in this way. -/

open Lean Elab Term

namespace SquaresInCircles.Eight.IntRows

/-- The integer `z` as a constructor applied to a raw natural-number literal. -/
def intLit (z : Int) : Expr :=
  if 0 ≤ z then mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit z.toNat)
  else mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit (z.natAbs - 1))

/-- The list `[x₀, …, xₙ]` of elements of type `ty`. -/
def listLit (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [.zero]) ty)

/-- The integers of one line, separated by single spaces. -/
def parseLine (n : Nat) (line : String) : Except String (List Int) :=
  (line.splitOn " ").mapM fun s =>
    match s.toInt? with
    | some z => .ok z
    | none => .error s!"line {n + 1}: not an integer: {s}"

/-- The nonempty lines of the data files read so far by this process, by path: a module reads
each of its files once, however many ranges of it it uses. -/
initialize linesCache : IO.Ref (Std.HashMap String (Array String)) ← IO.mkRef {}

/-- The nonempty lines of `file`. -/
def fileLines (file : System.FilePath) : TermElabM (Array String) := do
  if let some lines := (← linesCache.get)[file.toString]? then
    return lines
  let text ← try IO.FS.readFile file
    catch e => throwError "cannot read {file}: {e.toMessageData}"
  let lines := ((text.splitOn "\n").filter (· ≠ "")).toArray
  linesCache.modify (·.insert file.toString lines)
  return lines

/-- The lines `a, …, b - 1` (all lines without a range) of the file `path`, relative to the
directory of the current source file, as lists of integers. -/
def readRows (path : String) (a b : Option Nat) : TermElabM (List (List Int)) := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let file := dir / path
  let lines ← fileLines file
  let (first, lines) := match a, b with
    | some a, some b => (a, (lines.extract a b).toList)
    | _, _ => (0, lines.toList)
  match lines.zipIdx.mapM fun (l, n) => parseLine (first + n) l with
  | .ok rows => pure rows
  | .error e => throwError "{file}: {e}"

/-- `int_rows% "file" a b ↦ f`: the rows `a, …, b - 1` of the integer data file, as lists or
through `f`. -/
syntax (name := intRows) "int_rows% " str (ppSpace num ppSpace num)? (" ↦ " term)? : term
/-- `nat_rows% "file" a b ↦ f`: the rows `a, …, b - 1` of the natural-number data file, as lists
or through `f`. -/
syntax (name := natRows) "nat_rows% " str (ppSpace num ppSpace num)? (" ↦ " term)? : term

/-- The list of the rows, each a list of literals or, given `f`, `f` applied to its literals. -/
def rowsLit (ty : Expr) (lit : Int → Expr) (rows : List (List Int)) (f : Option Term) :
    TermElabM Expr := do
  match f with
  | none =>
    return listLit (mkApp (Lean.mkConst ``List [.zero]) ty) (rows.map (listLit ty ∘ List.map lit))
  | some f =>
    let fn ← instantiateMVars (← elabTerm f none)
    if fn.hasMVar then throwError "the row function must be fully elaborated: {fn}"
    -- the number of parameters of `f`, and whether the last one takes the rest of a line
    let (arity, tail) ← Meta.forallTelescope (← Meta.inferType fn) fun xs _ => do
      let some last := xs.back? | return (0, false)
      let lastTy ← Meta.inferType last
      return (xs.size, lastTy.isAppOfArity ``List 1 && lastTy.appArg! == ty)
    let apps ← rows.mapM fun r => do
      if tail then
        if r.length + 1 < arity then throwError "a row has fewer than {arity - 1} numbers"
        let rest := listLit ty ((r.drop (arity - 1)).map lit)
        return mkAppN fn ((r.take (arity - 1)).map lit ++ [rest]).toArray
      else
        return mkAppN fn (r.map lit).toArray
    let some first := apps.head? | throwError "no rows"
    let rowTy ← Meta.inferType first
    let u ← Meta.getLevel rowTy
    let .succ v := u | throwError "rows must be data, not propositions"
    for app in apps do Meta.check app
    return apps.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [v]) rowTy x acc)
      (mkApp (Lean.mkConst ``List.nil [v]) rowTy)

/-- The elaborator of `int_rows%`. -/
@[term_elab intRows] def elabIntRows : TermElab := fun stx _ => do
  let `(int_rows% $path:str $[$a:num $b:num]? $[↦ $f]?) := stx | throwUnsupportedSyntax
  let rows ← readRows path.getString (a.map (·.getNat)) (b.map (·.getNat))
  rowsLit (Lean.mkConst ``Int) intLit rows f

/-- The elaborator of `nat_rows%`; it rejects a negative entry. -/
@[term_elab natRows] def elabNatRows : TermElab := fun stx _ => do
  let `(nat_rows% $path:str $[$a:num $b:num]? $[↦ $f]?) := stx | throwUnsupportedSyntax
  let rows ← readRows path.getString (a.map (·.getNat)) (b.map (·.getNat))
  if rows.any (·.any (· < 0)) then throwError "nat_rows%: {path.getString}: negative entry"
  rowsLit (Lean.mkConst ``Nat) (mkRawNatLit ∘ Int.toNat) rows f

end SquaresInCircles.Eight.IntRows

/-! # Eight squares: reading the coverage trees

`pair_trees% "file.trees"` is the `List PairTree` (`Arithmetic/PairCover.lean`) of the trees in
the file, one tree per nonempty line. A tree is written in prefix order as natural numbers
separated by spaces: `0` is a gap leaf, `1 lo hi t` a trim to `[lo, hi]` followed by its subtree
`t`, `2 l r`, `3 l r` and `4 l r` bisect the source tangent, the target tangent and the angle,
followed by the subtrees `l` and `r` of the lower and the upper half, and `5` is a row leaf. A
token that is not a natural number, an unknown tag, a truncated tree or extra tokens on a line
are errors. The term is built directly from raw literals, with no numeral elaborated. The path
is relative to the directory of the Lean file that uses the notation, and the file is read when
that file is elaborated.

`scripts/eight/pair_tables.py` writes the trees of a pair table to `data/eight/pairs/`, one for
each half of each problem, in the order in which `problemsCheck` consumes them. -/

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

/-- `pair_trees% "file.trees"`: the list of the coverage trees written in the file, one per
line. -/
syntax (name := pairTrees) "pair_trees% " str : term

/-- The elaborator of `pair_trees%`: it reads the file and builds the list of its trees. -/
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
