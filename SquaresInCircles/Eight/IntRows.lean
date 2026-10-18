module

public meta import Lean

/-!
# Integer data files

`int_rows% "file"` is the `List (List Int)` whose rows are the lines of `file`,
each a list of decimal integers separated by spaces; `int_rows% "file" a b`
keeps the rows `a, …, b - 1`. `nat_rows%` is the same for natural numbers,
with values `List (List ℕ)`. With `↦ f` at the end, each line `n₁ … nₖ` becomes
`f n₁ … nₖ` instead of a list, so that a row is read without decoding a list.
If the last parameter of `f` is a list of numbers, a line `n₁ … nₖ m₁ … mⱼ` with
`k` the number of the other parameters becomes `f n₁ … nₖ [m₁, …, mⱼ]`, so lines
may differ in length. The path is relative to the directory of the source file
that uses the notation.

The term is built directly from raw literals: a natural number is a raw
literal, and an integer is `Int.ofNat n` or `Int.negSucc n` with `n` a raw
literal. No numeral is elaborated, and the kernel reads each number in constant
time. The notation produces data only; every property of the rows is a
separate theorem.

A module using the notation reads the file when it is elaborated, so it must be
rebuilt after the file changes.
-/

public meta section
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

syntax (name := intRows) "int_rows% " str (ppSpace num ppSpace num)? (" ↦ " term)? : term
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

@[term_elab intRows] def elabIntRows : TermElab := fun stx _ => do
  let `(int_rows% $path:str $[$a:num $b:num]? $[↦ $f]?) := stx | throwUnsupportedSyntax
  let rows ← readRows path.getString (a.map (·.getNat)) (b.map (·.getNat))
  rowsLit (Lean.mkConst ``Int) intLit rows f

@[term_elab natRows] def elabNatRows : TermElab := fun stx _ => do
  let `(nat_rows% $path:str $[$a:num $b:num]? $[↦ $f]?) := stx | throwUnsupportedSyntax
  let rows ← readRows path.getString (a.map (·.getNat)) (b.map (·.getNat))
  if rows.any (·.any (· < 0)) then throwError "nat_rows%: {path.getString}: negative entry"
  rowsLit (Lean.mkConst ``Nat) (mkRawNatLit ∘ Int.toNat) rows f

end SquaresInCircles.Eight.IntRows
