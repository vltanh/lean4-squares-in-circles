module

public import SquaresInCircles.Eight.Arithmetic.PairCover
public meta import SquaresInCircles.Eight.Certificates.Readers
public meta import SquaresInCircles.Eight.Certificates.Data
public meta import Lean.Elab.Command

/-!
# Checking certificate tables

`checked_rows` checks a block of rows in small parts and assembles their proofs.
`checked_pair_table` checks a pair table's context, labels, rows and coverage trees,
then applies the shared soundness theorem. Both commands generate ordinary definitions
and kernel-checked proofs.
-/

public meta section

/-! # Checking a block of certificate rows

`checked_rows parts using ctx from "file" first last by size` reads the indicated rows,
splits them into blocks, and proves that each block passes `checkRows`. It then assembles
`parts : List (List AffineRow)` and `parts_check`. The splitting controls kernel reduction
cost; the mathematics is the single `checkRows` soundness theorem.

The command only generates ordinary definitions and proofs by `decide +kernel`. Its input
contains data and block boundaries, never assumed propositions or externally checked proofs. -/

open Lean Elab Command

namespace SquaresInCircles.Eight

syntax (name := checkedRows) "checked_rows " ident " using " term " from " str
  ppSpace num ppSpace num " by " num : command

@[command_elab checkedRows] def elabCheckedRows : CommandElab := fun stx => do
  let `(checked_rows $name:ident using $ctx:term from $path:str $first:num $last:num
      by $size:num) := stx | throwUnsupportedSyntax
  let start := first.getNat
  let stop := last.getNat
  let step := size.getNat
  if step == 0 || stop < start then throwError "invalid certificate block bounds"
  let mut parts : Array (TSyntax `ident) := #[]
  let mut proofs : Array (TSyntax `ident) := #[]
  let mut a := start
  while a < stop do
    let b := min (a + step) stop
    let part := mkIdent (name.getId.appendAfter s!"_part{parts.size}")
    let proof := mkIdent (part.getId.appendAfter "_check")
    let lo := Syntax.mkNumLit (toString a)
    let hi := Syntax.mkNumLit (toString b)
    elabCommand (← `(noncomputable def $part :
        List SquaresInCircles.Eight.Arithmetic.AffineRow :=
      nat_rows% $path $lo $hi ↦ SquaresInCircles.Eight.Arithmetic.AffineRow.ofData))
    elabCommand (← `(theorem $proof :
        SquaresInCircles.Eight.Arithmetic.checkRows $ctx $part = true := by decide +kernel))
    parts := parts.push part
    proofs := proofs.push proof
    a := b
  elabCommand (← `(noncomputable def $name :
      List (List SquaresInCircles.Eight.Arithmetic.AffineRow) := [$parts,*]))
  let proof := mkIdent (name.getId.appendAfter "_check")
  let args ← (#[name] ++ proofs).mapM fun p => `(Parser.Tactic.simpLemma| $p:term)
  elabCommand (← `(theorem $proof :
      ($name).all (SquaresInCircles.Eight.Arithmetic.checkRows $ctx) = true := by
    simp only [$args,*, List.all_cons, List.all_nil, Bool.and_true]))

end SquaresInCircles.Eight

/-! # One proof for every pair table

A pair certificate has four obligations: its context encloses the arcs, the affine labels
bound the quadratic labels, every row holds, and the subdivision trees cover every problem.
`checked_pair_table` writes those four kernel-checked proofs and applies `PairCover.table_sound`.
The command reads only data; the problem statement is supplied as a Lean expression. -/

open Lean Elab Command

namespace SquaresInCircles.Eight

syntax (name := checkedPairTable) "checked_pair_table " str ppSpace str
  ppSpace term:arg ppSpace term:arg ppSpace term:arg ppSpace term:arg : command

private def pairHeader (path : String) : CommandElabM (Nat × Nat) := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let text ← IO.FS.readFile (dir / path)
  let fields := (text.splitOn "\n").head!.splitOn " "
  match fields with
  | [d, n] =>
    let some d := d.toNat? | throwError "invalid denominator in {path}"
    let some n := n.toNat? | throwError "invalid count in {path}"
    return (d, n)
  | _ => throwError "invalid certificate header in {path}"

/-- These are the public declarations of a table, shared by all command invocations. -/
private def emitPair (stx : Syntax) : CommandElabM Unit :=
  elabCommand (stx.rewriteBottomUp fun s => match s with
    | .ident info raw name _ =>
      let n := name.eraseMacroScopes
      let names := [`table, `specs, `problems, `ctx, `ctx_scalars, `ctx_valid,
        `labels_check, `rowParts, `rowParts_check, `data, `data_check, `all_row_claims,
        `trees, `trees_check, `sound]
      if names.any (·.isPrefixOf n) then .ident info raw n [] else s
    | _ => s)

@[command_elab checkedPairTable] def elabCheckedPairTable : CommandElab := fun stx => do
  let `(checked_pair_table $path:str $metadata:str
      $radius:term $charge:term $target:term $problems:term) := stx | throwUnsupportedSyntax
  let arcsPath := Syntax.mkStrLit (path.getString ++ ".arcs")
  let rowsPath := Syntax.mkStrLit (path.getString ++ ".rows")
  let treesPath := Syntax.mkStrLit (path.getString ++ ".trees")
  let (den, arcs) ← pairHeader arcsPath.getString
  let (rowDen, rows) ← pairHeader rowsPath.getString
  if den == 0 || den != rowDen then throwError "inconsistent pair-table denominators"
  let dn := Syntax.mkNumLit (toString den)
  let an := Syntax.mkNumLit (toString arcs)
  emitPair (← `(noncomputable def table : Arithmetic.AffineTableMeta :=
    { radius := $radius
      arcs := pair_arcs% $metadata
      cuts := fun _ => ⟨0, 1⟩
      word := fun _ => 0
      charge := fun _ => $charge
      target := fun _ => $target
      differenceRange := fun _ => ⟨0, 1⟩
      allowedAxes := fun _ => [] }))
  emitPair (← `(noncomputable def specs : List (Arithmetic.QuadLabel × Bool) :=
    pair_labels% $metadata))
  emitPair (← `(noncomputable def problems : List Arithmetic.PairCover.PairProblem :=
    $problems))
  let mut groups : Array (TSyntax `term) := #[]
  for a in [: (arcs + 31) / 32] do
    let lo := Syntax.mkNumLit (toString (8 + 32 * a))
    let hi := Syntax.mkNumLit (toString (8 + min (32 * (a + 1)) arcs))
    groups := groups.push (← `(int_rows% $arcsPath $lo $hi ↦ Arithmetic.ArcBox.ofData))
  emitPair (← `(noncomputable def ctx : Arithmetic.TableCtx :=
    ⟨$dn, $an, [$groups,*],
      int_rows% $arcsPath 1 8 ↦ fun (a b _c _d : Int) => (⟨a, b⟩ : Arithmetic.Fixed.FI),
      int_rows% $arcsPath 1 8 ↦ fun (_a _b c d : Int) => (⟨c, d⟩ : Arithmetic.Fixed.FI)⟩))
  emitPair (← `(theorem ctx_scalars : ctx.checkScalars table = true := by decide +kernel))
  let mut blocks : Array (TSyntax `term) := #[]
  let mut proofs : Array (TSyntax `ident) := #[]
  for i in [: (arcs + 119) / 120] do
    let a := Syntax.mkNumLit (toString (120 * i))
    let c := Syntax.mkNumLit (toString (min 120 (arcs - 120 * i)))
    let name := mkIdent (Name.mkSimple s!"ctx_boxes_{i}")
    emitPair (← `(theorem $name :
        Arithmetic.boxesRange table.radius table.arcs ctx.boxes $a $c = true := by
      decide +kernel))
    blocks := blocks.push (← `(($a, $c)))
    proofs := proofs.push name
  let mut proof ← `(True.intro)
  for p in proofs.reverse do proof ← `(And.intro $p $proof)
  emitPair (← `(theorem ctx_valid : ctx.Valid table :=
    Arithmetic.TableCtx.valid_of ctx_scalars (blocks := [$blocks,*]) (by decide +kernel)
      (by simpa only [Arithmetic.AllBlocks] using $proof)))
  emitPair (← `(theorem labels_check :
      Arithmetic.labelsCheck table.radius ctx.boxes 0 table.arcs specs = true := by
    decide +kernel))
  let stop := Syntax.mkNumLit (toString (rows + 1))
  emitPair (← `(checked_rows rowParts using ctx from $rowsPath 1 $stop by 100))
  emitPair (← `(noncomputable def data : List Arithmetic.AffineRow := rowParts.flatten))
  emitPair (← `(theorem data_check : Arithmetic.checkRows ctx data = true := by
    simpa only [data, Arithmetic.checkRows_flatten] using rowParts_check))
  emitPair (← `(theorem all_row_claims :
      ∀ x ∈ data, (x.toTableRow table ctx.den).Claim table :=
    fun x hx => Arithmetic.checkRow_claim ctx_valid (Arithmetic.checkRows_sound data_check x hx)))
  emitPair (← `(noncomputable def trees : List Arithmetic.PairCover.PairTree :=
    pair_trees% $treesPath))
  emitPair (← `(theorem trees_check :
      Arithmetic.PairCover.problemsCheck table ctx specs problems trees data = true := by
    decide +kernel))
  emitPair (← `(theorem sound : ∀ P ∈ problems, P.Holds table.radius ctx.den :=
    Arithmetic.PairCover.table_sound ctx_valid labels_check all_row_claims trees_check))

end SquaresInCircles.Eight
