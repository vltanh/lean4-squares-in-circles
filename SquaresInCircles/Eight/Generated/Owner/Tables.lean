module

public import SquaresInCircles.Eight.Candidate.DualCheck
meta import SquaresInCircles.Eight.IntRows

/-! # Owner tables

The 8 owner tables of the quarter mode and the 15 of the mixed mode, with 345 and 729 rows, read
from `data/eight/owner/quarter*.txt` and `mixed*.txt`, one file per table. For each table the kernel
evaluates that every row passes `Line.check` and that the intervals cover the half-angle chart
(`coverCheck`). -/

@[expose] public section
noncomputable section
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable004`. -/
noncomputable def quarter004Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter004.txt" ↦ Line.ofNats

theorem quarter004_rows :
    quarter004Lines.all (Line.check .quarter ![0, 0, 0, 0, 0, 2, 0] .zero) = true := by
  decide +kernel

theorem quarter004_cover : coverCheck quarter004Lines = true := by decide +kernel

def quarterTable004 : OwnerTable :=
  .ofLines .quarter ![0, 0, 0, 0, 0, 2, 0] quarter004Lines quarter004_rows quarter004_cover

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable005`. -/
noncomputable def quarter005Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter005.txt" ↦ Line.ofNats

theorem quarter005_rows :
    quarter005Lines.all (Line.check .quarter ![0, 0, 0, 0, 0, 2, 1] .zero) = true := by
  decide +kernel

theorem quarter005_cover : coverCheck quarter005Lines = true := by decide +kernel

def quarterTable005 : OwnerTable :=
  .ofLines .quarter ![0, 0, 0, 0, 0, 2, 1] quarter005Lines quarter005_rows quarter005_cover

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable006`. -/
noncomputable def quarter006Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter006.txt" ↦ Line.ofNats

theorem quarter006_rows :
    quarter006Lines.all (Line.check .quarter ![0, 0, 0, 0, 0, 2, 2] .zero) = true := by
  decide +kernel

theorem quarter006_cover : coverCheck quarter006Lines = true := by decide +kernel

def quarterTable006 : OwnerTable :=
  .ofLines .quarter ![0, 0, 0, 0, 0, 2, 2] quarter006Lines quarter006_rows quarter006_cover

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable007`. -/
noncomputable def quarter007Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter007.txt" ↦ Line.ofNats

theorem quarter007_rows :
    quarter007Lines.all (Line.check .quarter ![0, 0, 0, 0, 0, 2, 3] .zero) = true := by
  decide +kernel

theorem quarter007_cover : coverCheck quarter007Lines = true := by decide +kernel

def quarterTable007 : OwnerTable :=
  .ofLines .quarter ![0, 0, 0, 0, 0, 2, 3] quarter007Lines quarter007_rows quarter007_cover

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable016`. -/
noncomputable def quarter016Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter016.txt" ↦ Line.ofNats

theorem quarter016_rows :
    quarter016Lines.all (Line.check .quarter ![0, 1, 0, 0, 0, 2, 0] .zero) = true := by
  decide +kernel

theorem quarter016_cover : coverCheck quarter016Lines = true := by decide +kernel

def quarterTable016 : OwnerTable :=
  .ofLines .quarter ![0, 1, 0, 0, 0, 2, 0] quarter016Lines quarter016_rows quarter016_cover

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable017`. -/
noncomputable def quarter017Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter017.txt" ↦ Line.ofNats

theorem quarter017_rows :
    quarter017Lines.all (Line.check .quarter ![0, 1, 0, 0, 0, 2, 1] .zero) = true := by
  decide +kernel

theorem quarter017_cover : coverCheck quarter017Lines = true := by decide +kernel

def quarterTable017 : OwnerTable :=
  .ofLines .quarter ![0, 1, 0, 0, 0, 2, 1] quarter017Lines quarter017_rows quarter017_cover

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable018`. -/
noncomputable def quarter018Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter018.txt" ↦ Line.ofNats

theorem quarter018_rows :
    quarter018Lines.all (Line.check .quarter ![0, 1, 0, 0, 0, 2, 2] .zero) = true := by
  decide +kernel

theorem quarter018_cover : coverCheck quarter018Lines = true := by decide +kernel

def quarterTable018 : OwnerTable :=
  .ofLines .quarter ![0, 1, 0, 0, 0, 2, 2] quarter018Lines quarter018_rows quarter018_cover

set_option maxRecDepth 100000 in
/-- The rows of `quarterTable019`. -/
noncomputable def quarter019Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/quarter019.txt" ↦ Line.ofNats

theorem quarter019_rows :
    quarter019Lines.all (Line.check .quarter ![0, 1, 0, 0, 0, 2, 3] .zero) = true := by
  decide +kernel

theorem quarter019_cover : coverCheck quarter019Lines = true := by decide +kernel

def quarterTable019 : OwnerTable :=
  .ofLines .quarter ![0, 1, 0, 0, 0, 2, 3] quarter019Lines quarter019_rows quarter019_cover

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
/-- The rows of `mixedTable001`. -/
noncomputable def mixed001Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed001.txt" ↦ Line.ofNats

theorem mixed001_rows :
    mixed001Lines.all (Line.check .mixed ![0, 0, 0, 2, 0, 2, 2] .zero) = true := by
  decide +kernel

theorem mixed001_cover : coverCheck mixed001Lines = true := by decide +kernel

def mixedTable001 : OwnerTable :=
  .ofLines .mixed ![0, 0, 0, 2, 0, 2, 2] mixed001Lines mixed001_rows mixed001_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable002`. -/
noncomputable def mixed002Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed002.txt" ↦ Line.ofNats

theorem mixed002_rows :
    mixed002Lines.all (Line.check .mixed ![0, 0, 0, 2, 0, 2, 3] .zero) = true := by
  decide +kernel

theorem mixed002_cover : coverCheck mixed002Lines = true := by decide +kernel

def mixedTable002 : OwnerTable :=
  .ofLines .mixed ![0, 0, 0, 2, 0, 2, 3] mixed002Lines mixed002_rows mixed002_cover

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
/-- The rows of `mixedTable005`. -/
noncomputable def mixed005Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed005.txt" ↦ Line.ofNats

theorem mixed005_rows :
    mixed005Lines.all (Line.check .mixed ![0, 1, 0, 2, 0, 2, 2] .zero) = true := by
  decide +kernel

theorem mixed005_cover : coverCheck mixed005Lines = true := by decide +kernel

def mixedTable005 : OwnerTable :=
  .ofLines .mixed ![0, 1, 0, 2, 0, 2, 2] mixed005Lines mixed005_rows mixed005_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable006`. -/
noncomputable def mixed006Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed006.txt" ↦ Line.ofNats

theorem mixed006_rows :
    mixed006Lines.all (Line.check .mixed ![0, 1, 0, 2, 0, 2, 3] .zero) = true := by
  decide +kernel

theorem mixed006_cover : coverCheck mixed006Lines = true := by decide +kernel

def mixedTable006 : OwnerTable :=
  .ofLines .mixed ![0, 1, 0, 2, 0, 2, 3] mixed006Lines mixed006_rows mixed006_cover

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
/-- The rows of `mixedTable009`. -/
noncomputable def mixed009Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed009.txt" ↦ Line.ofNats

theorem mixed009_rows :
    mixed009Lines.all (Line.check .mixed ![0, 2, 0, 2, 0, 2, 2] .zero) = true := by
  decide +kernel

theorem mixed009_cover : coverCheck mixed009Lines = true := by decide +kernel

def mixedTable009 : OwnerTable :=
  .ofLines .mixed ![0, 2, 0, 2, 0, 2, 2] mixed009Lines mixed009_rows mixed009_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable010`. -/
noncomputable def mixed010Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed010.txt" ↦ Line.ofNats

theorem mixed010_rows :
    mixed010Lines.all (Line.check .mixed ![0, 2, 0, 2, 0, 2, 3] .zero) = true := by
  decide +kernel

theorem mixed010_cover : coverCheck mixed010Lines = true := by decide +kernel

def mixedTable010 : OwnerTable :=
  .ofLines .mixed ![0, 2, 0, 2, 0, 2, 3] mixed010Lines mixed010_rows mixed010_cover

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

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable013`. -/
noncomputable def mixed013Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed013.txt" ↦ Line.ofNats

theorem mixed013_rows :
    mixed013Lines.all (Line.check .mixed ![0, 3, 0, 2, 0, 2, 2] .zero) = true := by
  decide +kernel

theorem mixed013_cover : coverCheck mixed013Lines = true := by decide +kernel

def mixedTable013 : OwnerTable :=
  .ofLines .mixed ![0, 3, 0, 2, 0, 2, 2] mixed013Lines mixed013_rows mixed013_cover

set_option maxRecDepth 100000 in
/-- The rows of `mixedTable014`. -/
noncomputable def mixed014Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/mixed014.txt" ↦ Line.ofNats

theorem mixed014_rows :
    mixed014Lines.all (Line.check .mixed ![0, 3, 0, 2, 0, 2, 3] .zero) = true := by
  decide +kernel

theorem mixed014_cover : coverCheck mixed014Lines = true := by decide +kernel

def mixedTable014 : OwnerTable :=
  .ofLines .mixed ![0, 3, 0, 2, 0, 2, 3] mixed014Lines mixed014_rows mixed014_cover

end SquaresInCircles.Eight.Generated.Owner
