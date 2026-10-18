module

public meta import Lean
public meta import Init.System.FilePath
public import SquaresInCircles.Eight.Arithmetic.AffineTableData

/-!
# Data-only notation for the original rational affine tables

`affine_rows%` reads the retained research JSON and elaborates only a list of
row constructors. It generates no theorem, axiom, proof tactic, or successful
verification result. Subsequent ordinary Lean proofs check the rows and their
complete geometric coverage against the independently declared metadata.

The reader accepts integers and rational strings, never floating-point
approximations. It rejects malformed fields, zero denominators, unknown arc
identifiers, duplicate identifiers, invalid signs, axes and support modes.

The input path is relative to the module using the notation. A missing file
is an error. When a JSON input changes, rebuild its importing module: no
incremental-build dependency tracking for external files is claimed here.
-/

public meta section
open Lean Elab Term
namespace SquaresInCircles.Eight.AffineDataReader

private def require {α : Type} (x : Except String α) : TermElabM α :=
  match x with
  | .ok a => pure a
  | .error message => throwError "affine table: {message}"

private def field (j : Json) (key : String) : TermElabM Json :=
  require (j.getObjVal? key)

private def nat (j : Json) : TermElabM Nat := require j.getNat?

/-- Only parsed integers are interpolated into the generated Lean syntax. -/
private def rationalString (s : String) : TermElabM String := do
  let parts := s.splitOn "/"
  match parts with
  | [a] =>
      let some n := a.toInt? | throwError "invalid integer in affine table: {s}"
      return "(" ++ toString n ++ ")"
  | [a,b] =>
      let some n := a.toInt? | throwError "invalid rational numerator: {s}"
      let some d := b.toNat? | throwError "invalid rational denominator: {s}"
      if d = 0 then throwError "zero rational denominator in affine table"
      return "(" ++ toString n ++ "/" ++ toString d ++ ")"
  | _ => throwError "expected an exact integer or rational, not a decimal: {s}"

private def rational (j : Json) : TermElabM String := do
  match j with
  | .str s => rationalString s
  | _ => return "(" ++ toString (← require j.getInt?) ++ ")"

private def optional (j : Json) (key : String) (fallback : Json) : Json :=
  match j.getObjVal? key with
  | .ok value => value
  | .error _ => fallback

private def rowSyntax (ids : Std.HashMap Nat Nat) (gamma : Array Json) (r : Json) :
    TermElabM String := do
  discard <| require r.getObj?
  let edge ← nat (← field r "edge")
  if edge ≥ 7 then throwError "affine edge is outside Fin 7"
  let sourceId ← nat (← field r "source")
  let targetId ← nat (← field r "target")
  let some source := ids.get? sourceId | throwError "unknown affine source arc {sourceId}"
  let some target := ids.get? targetId | throwError "unknown affine target arc {targetId}"
  let axis ← nat (← field r "axis")
  let axis ← match axis with
    | 1 => pure ".one" | 2 => pure ".two" | 3 => pure ".three" | 4 => pure ".four"
    | _ => throwError "invalid affine axis"
  let quarter ← nat (← field r "k")
  let sign ← require (← field r "r").getInt?
  if sign ≠ -1 ∧ sign ≠ 1 then throwError "invalid affine angular sign"
  let lo ← rational (← field r "lo")
  let hi ← rational (← field r "hi")
  let multiplier ← rational (← field r "lambda")
  let mode ← require (← field r "mode").getStr?
  if !(mode == "lower" || mode == "upper" || mode == "endpoints" || mode == "circle") then
    throwError "invalid affine support mode {mode}"
  let radical ← rational (optional r "h" (toJson (1 : Nat)))
  let lower ← rational (optional r "gamma" gamma[edge]!)
  return "⟨" ++ String.intercalate "," [toString edge, toString source, toString target,
    axis, toString quarter, (if sign = 1 then "true" else "false"),
    "⟨" ++ lo ++ "," ++ hi ++ "⟩", multiplier, "." ++ mode, radical, lower] ++ "⟩"

syntax (name := affineRows) "affine_rows% " str " rows " num : term

@[term_elab affineRows] def elabAffineRows : TermElab := fun stx expectedType? => do
  let `(affine_rows% $path:str rows $count:num) := stx | throwUnsupportedSyntax
  let content ← elabTerm (← `(include_str $path)) (some (mkConst ``String))
  let .lit (.strVal text) := content | throwError "affine input did not elaborate to text"
  let data ← require (Json.parse text)
  let arcs ← require (← field data "arcs").getArr?
  let rows ← require (← field data "rows").getArr?
  let gamma ← require (← field data "gamma").getArr?
  if gamma.size ≠ 7 then throwError "affine table must specify seven edge targets"
  if rows.size ≠ count.getNat then
    throwError "affine row count changed: expected {count.getNat}, found {rows.size}"
  let mut ids : Std.HashMap Nat Nat := {}
  for i in [:arcs.size] do
    let id ← nat (← field arcs[i]! "id")
    if ids.contains id then throwError "duplicate affine arc identifier {id}"
    ids := ids.insert id i
  let mut literals : Array String := #[]
  for r in rows do
    literals := literals.push (← rowSyntax ids gamma r)
  let text := "([" ++ String.intercalate ",\n" literals.toList ++
    "] : List SquaresInCircles.Eight.Arithmetic.AffineTableRow)"
  let parsed ← require (Parser.runParserCategory (← getEnv) `term text)
  elabTerm parsed expectedType?

end SquaresInCircles.Eight.AffineDataReader
