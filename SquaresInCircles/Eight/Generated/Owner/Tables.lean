module

public import SquaresInCircles.Eight.Candidate.DualCheck
meta import SquaresInCircles.Eight.IntRows

/-! # Owner tables

The 7 owner tables of the mixed mode, with 489 rows, read from `data/eight/owner/mixed*.txt`, one
file per table. For each table the kernel evaluates that every row passes `Line.check` and that the
intervals cover the half-angle chart (`coverCheck`). -/

@[expose] public section
noncomputable section
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable000`. -/
noncomputable def mixed000Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed000.txt" ↦ Line.ofNats

theorem mixed000_rows :
    mixed000Lines.all (Line.check .mixed ![0, 0, 0, 2, 0, 2, 0] .zero) = true := by
  decide +kernel

theorem mixed000_cover : coverCheck mixed000Lines = true := by decide +kernel

def mixedTable000 : OwnerTable :=
  .ofLines .mixed ![0, 0, 0, 2, 0, 2, 0] mixed000Lines mixed000_rows mixed000_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable003`. -/
noncomputable def mixed003Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed003.txt" ↦ Line.ofNats

theorem mixed003_rows :
    mixed003Lines.all (Line.check .mixed ![0, 1, 0, 2, 0, 2, 0] .zero) = true := by
  decide +kernel

theorem mixed003_cover : coverCheck mixed003Lines = true := by decide +kernel

def mixedTable003 : OwnerTable :=
  .ofLines .mixed ![0, 1, 0, 2, 0, 2, 0] mixed003Lines mixed003_rows mixed003_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable004`. -/
noncomputable def mixed004Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed004.txt" ↦ Line.ofNats

theorem mixed004_rows :
    mixed004Lines.all (Line.check .mixed ![0, 1, 0, 2, 0, 2, 1] .zero) = true := by
  decide +kernel

theorem mixed004_cover : coverCheck mixed004Lines = true := by decide +kernel

def mixedTable004 : OwnerTable :=
  .ofLines .mixed ![0, 1, 0, 2, 0, 2, 1] mixed004Lines mixed004_rows mixed004_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable007`. -/
noncomputable def mixed007Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed007.txt" ↦ Line.ofNats

theorem mixed007_rows :
    mixed007Lines.all (Line.check .mixed ![0, 2, 0, 2, 0, 2, 0] .zero) = true := by
  decide +kernel

theorem mixed007_cover : coverCheck mixed007Lines = true := by decide +kernel

def mixedTable007 : OwnerTable :=
  .ofLines .mixed ![0, 2, 0, 2, 0, 2, 0] mixed007Lines mixed007_rows mixed007_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable008`. -/
noncomputable def mixed008Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed008.txt" ↦ Line.ofNats

theorem mixed008_rows :
    mixed008Lines.all (Line.check .mixed ![0, 2, 0, 2, 0, 2, 1] .zero) = true := by
  decide +kernel

theorem mixed008_cover : coverCheck mixed008Lines = true := by decide +kernel

def mixedTable008 : OwnerTable :=
  .ofLines .mixed ![0, 2, 0, 2, 0, 2, 1] mixed008Lines mixed008_rows mixed008_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable011`. -/
noncomputable def mixed011Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed011.txt" ↦ Line.ofNats

theorem mixed011_rows :
    mixed011Lines.all (Line.check .mixed ![0, 3, 0, 2, 0, 2, 0] .zero) = true := by
  decide +kernel

theorem mixed011_cover : coverCheck mixed011Lines = true := by decide +kernel

def mixedTable011 : OwnerTable :=
  .ofLines .mixed ![0, 3, 0, 2, 0, 2, 0] mixed011Lines mixed011_rows mixed011_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable012`. -/
noncomputable def mixed012Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed012.txt" ↦ Line.ofNats

theorem mixed012_rows :
    mixed012Lines.all (Line.check .mixed ![0, 3, 0, 2, 0, 2, 1] .zero) = true := by
  decide +kernel

theorem mixed012_cover : coverCheck mixed012Lines = true := by decide +kernel

def mixedTable012 : OwnerTable :=
  .ofLines .mixed ![0, 3, 0, 2, 0, 2, 1] mixed012Lines mixed012_rows mixed012_cover

end SquaresInCircles.Eight.Generated.Owner
