module

public import SquaresInCircles.Eight.Arithmetic.AffineTableData
public import SquaresInCircles.Eight.Arithmetic.RowCover
public import SquaresInCircles.Eight.Arithmetic.LabelRelax
public meta import SquaresInCircles.Eight.Arithmetic.Interval
public meta import SquaresInCircles.Eight.Arithmetic.AffineArc
public meta import SquaresInCircles.Eight.Arithmetic.AffineTableData
public meta import SquaresInCircles.Eight.Arithmetic.RowCover
public meta import SquaresInCircles.Eight.Arithmetic.LabelRelax
public meta import Lean
public meta import Mathlib.Tactic.ToExpr

/-!
# Exact certificate metadata

The shared JSON readers supply rational table metadata, fixed-point affine contexts and
quadratic pair labels. Parsing supplies data; context, row and coverage theorems prove
all its mathematical properties.
-/

public meta section

/-! # Exact table metadata

`certificate_data% "file"` reads a typed JSON description of rational table data and
elaborates it to ordinary Lean constructors. Rationals are strings such as `"7/12"`;
finite functions are arrays of exactly the required length. Parsing supplies data only.
The existing context, row and coverage theorems still prove every required property. -/

open Lean Elab Term

namespace SquaresInCircles.Eight.CertificateData
open Arithmetic

instance : FromJson Rat where
  fromJson? j := do
    let s ← j.getStr?
    match s.splitOn "/" with
    | [n] =>
      let some n := n.toInt? | throw "invalid rational numerator"
      return n
    | [n, d] =>
      let some n := n.toInt? | throw "invalid rational numerator"
      let some d := d.toNat? | throw "invalid rational denominator"
      if d == 0 then throw "zero rational denominator"
      return n / (d : Rat)
    | _ => throw "expected an integer or a rational n/d"

instance (n : Nat) : FromJson (Fin n) where
  fromJson? j := do
    let v : Nat ← fromJson? j
    if h : v < n then return ⟨v, h⟩ else throw "finite index out of range"

instance {α : Type} [FromJson α] (n : Nat) : FromJson (Fin n → α) where
  fromJson? j := do
    let xs : Array α ← fromJson? j
    if h : xs.size = n then
      return fun i => xs[i.val]'(h.symm ▸ i.isLt)
    else throw "incorrect finite-array length"

instance : FromJson ForwardAxis where
  fromJson? j := do
    match ← j.getStr? with
    | "one" => return .one
    | "two" => return .two
    | "three" => return .three
    | "four" => return .four
    | _ => throw "invalid separating axis"

deriving instance ToExpr for ForwardAxis
deriving instance FromJson for QInterval, AffineLabel, ArcData, AffineTableMeta
deriving instance ToExpr for QInterval
deriving instance ToExpr for AffineLabel
deriving instance ToExpr for ArcData
deriving instance ToExpr for AffineTableMeta

def readJson (path : String) : TermElabM Json := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let text ← IO.FS.readFile (dir / path)
  match Json.parse text with
  | .ok j => return j
  | .error e => throwError "{path}: {e}"

def decode (α : Type) [FromJson α] [ToExpr α] (j : Json) : TermElabM Expr :=
  match fromJson? j with
  | .ok x => return toExpr (x : α)
  | .error e => throwError "invalid certificate data: {e}"

syntax (name := certificateData) "certificate_data% " str : term

@[term_elab certificateData] def elabCertificateData : TermElab := fun stx expected => do
  let `(certificate_data% $path:str) := stx | throwUnsupportedSyntax
  let some ty := expected | throwError "certificate_data% needs an expected data type"
  let ty ← instantiateMVars ty
  let j ← readJson path.getString
  if ty.isConstOf ``AffineTableMeta then decode AffineTableMeta j
  else throwError "unsupported certificate data type: {ty}"

end SquaresInCircles.Eight.CertificateData

/-! # Fixed-point metadata of affine certificates

These fields describe the state chains and angle intervals. The context and coverage
theorems check their meaning against the exact arcs and the certificate rows. -/

open Lean Elab Term

namespace SquaresInCircles.Eight.CertificateData
open Arithmetic

deriving instance FromJson for Fixed.FI
deriving instance ToExpr for Fixed.FI

syntax (name := affineField) "affine_field% " str ppSpace str : term

@[term_elab affineField] def elabAffineField : TermElab := fun stx _ => do
  let `(affine_field% $path:str $field:str) := stx | throwUnsupportedSyntax
  let j ← readJson path.getString
  let j ← match j.getObjVal? field.getString with
    | .ok j => pure j
    | .error e => throwError "invalid affine context data: {e}"
  match field.getString with
  | "states" => decode (List (List (List Nat))) j
  | "gap" => decode Fixed.FI j
  | "base" => decode (List Fixed.FI) j
  | "dLo" | "dHi" => decode (List Int) j
  | _ => throwError "unknown affine context field: {field.getString}"

end SquaresInCircles.Eight.CertificateData

/-! # Exact quadratic labels for pair certificates

This reader elaborates the rational labels to ordinary constructors. Their inequalities
are still proved by `labelsCheck`; parsing contributes no mathematical assumptions. -/

open Lean Elab Term

namespace SquaresInCircles.Eight.CertificateData
open Arithmetic

deriving instance FromJson for QuadLabel
deriving instance ToExpr for QuadLabel

syntax (name := pairLabels) "pair_labels% " str : term
syntax (name := pairArcs) "pair_arcs% " str : term

def readPairField (path field : String) : TermElabM Json := do
  match (← readJson path).getObjVal? field with
  | .ok j => return j
  | .error e => throwError "invalid pair certificate: {e}"

@[term_elab pairArcs] def elabPairArcs : TermElab := fun stx _ => do
  let `(pair_arcs% $path:str) := stx | throwUnsupportedSyntax
  decode (List ArcData) (← readPairField path.getString "arcs")

@[term_elab pairLabels] def elabPairLabels : TermElab := fun stx _ => do
  let `(pair_labels% $path:str) := stx | throwUnsupportedSyntax
  decode (List (QuadLabel × Bool)) (← readPairField path.getString "labels")

end SquaresInCircles.Eight.CertificateData
