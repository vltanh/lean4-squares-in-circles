module

public import SquaresInCircles.Eight.Candidate.DualCheck
meta import SquaresInCircles.Eight.IntRows

/-! # Tilt bundles

The tilt bundles of the two tails `[0, 1001/20000]` and `[2/25, 3/8]` of the positive half-angle
chart, 22 and 19 of them, with 861 rows, read from `data/eight/owner/tilt*.txt`, one file per bundle
with one row for each error alternative. For each bundle the kernel evaluates `bundleCheck`: every
row passes `Line.check`. -/

@[expose] public section
noncomputable section
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle018` on `[0, 1/1280]`, in the order of `Alternative.index`. -/
noncomputable def tilt018Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt018.txt" ↦ Line.ofNats

theorem tilt018_check : bundleCheck tilt018Lines = true := by decide +kernel

def tiltBundle018 : TiltBundle := .ofLines tilt018Lines tilt018_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle019` on `[1/1280, 1/640]`, in the order of `Alternative.index`. -/
noncomputable def tilt019Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt019.txt" ↦ Line.ofNats

theorem tilt019_check : bundleCheck tilt019Lines = true := by decide +kernel

def tiltBundle019 : TiltBundle := .ofLines tilt019Lines tilt019_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle020` on `[1/640, 1/320]`, in the order of `Alternative.index`. -/
noncomputable def tilt020Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt020.txt" ↦ Line.ofNats

theorem tilt020_check : bundleCheck tilt020Lines = true := by decide +kernel

def tiltBundle020 : TiltBundle := .ofLines tilt020Lines tilt020_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle021` on `[1/320, 3/640]`, in the order of `Alternative.index`. -/
noncomputable def tilt021Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt021.txt" ↦ Line.ofNats

theorem tilt021_check : bundleCheck tilt021Lines = true := by decide +kernel

def tiltBundle021 : TiltBundle := .ofLines tilt021Lines tilt021_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle022` on `[3/640, 1/160]`, in the order of `Alternative.index`. -/
noncomputable def tilt022Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt022.txt" ↦ Line.ofNats

theorem tilt022_check : bundleCheck tilt022Lines = true := by decide +kernel

def tiltBundle022 : TiltBundle := .ofLines tilt022Lines tilt022_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle023` on `[1/160, 3/320]`, in the order of `Alternative.index`. -/
noncomputable def tilt023Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt023.txt" ↦ Line.ofNats

theorem tilt023_check : bundleCheck tilt023Lines = true := by decide +kernel

def tiltBundle023 : TiltBundle := .ofLines tilt023Lines tilt023_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle024` on `[3/320, 1/80]`, in the order of `Alternative.index`. -/
noncomputable def tilt024Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt024.txt" ↦ Line.ofNats

theorem tilt024_check : bundleCheck tilt024Lines = true := by decide +kernel

def tiltBundle024 : TiltBundle := .ofLines tilt024Lines tilt024_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle025` on `[1/80, 1/64]`, in the order of `Alternative.index`. -/
noncomputable def tilt025Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt025.txt" ↦ Line.ofNats

theorem tilt025_check : bundleCheck tilt025Lines = true := by decide +kernel

def tiltBundle025 : TiltBundle := .ofLines tilt025Lines tilt025_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle026` on `[1/64, 3/160]`, in the order of `Alternative.index`. -/
noncomputable def tilt026Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt026.txt" ↦ Line.ofNats

theorem tilt026_check : bundleCheck tilt026Lines = true := by decide +kernel

def tiltBundle026 : TiltBundle := .ofLines tilt026Lines tilt026_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle027` on `[3/160, 7/320]`, in the order of `Alternative.index`. -/
noncomputable def tilt027Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt027.txt" ↦ Line.ofNats

theorem tilt027_check : bundleCheck tilt027Lines = true := by decide +kernel

def tiltBundle027 : TiltBundle := .ofLines tilt027Lines tilt027_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle028` on `[7/320, 1/40]`, in the order of `Alternative.index`. -/
noncomputable def tilt028Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt028.txt" ↦ Line.ofNats

theorem tilt028_check : bundleCheck tilt028Lines = true := by decide +kernel

def tiltBundle028 : TiltBundle := .ofLines tilt028Lines tilt028_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle029` on `[1/40, 9/320]`, in the order of `Alternative.index`. -/
noncomputable def tilt029Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt029.txt" ↦ Line.ofNats

theorem tilt029_check : bundleCheck tilt029Lines = true := by decide +kernel

def tiltBundle029 : TiltBundle := .ofLines tilt029Lines tilt029_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle030` on `[9/320, 1/32]`, in the order of `Alternative.index`. -/
noncomputable def tilt030Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt030.txt" ↦ Line.ofNats

theorem tilt030_check : bundleCheck tilt030Lines = true := by decide +kernel

def tiltBundle030 : TiltBundle := .ofLines tilt030Lines tilt030_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle031` on `[1/32, 11/320]`, in the order of `Alternative.index`. -/
noncomputable def tilt031Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt031.txt" ↦ Line.ofNats

theorem tilt031_check : bundleCheck tilt031Lines = true := by decide +kernel

def tiltBundle031 : TiltBundle := .ofLines tilt031Lines tilt031_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle032` on `[11/320, 3/80]`, in the order of `Alternative.index`. -/
noncomputable def tilt032Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt032.txt" ↦ Line.ofNats

theorem tilt032_check : bundleCheck tilt032Lines = true := by decide +kernel

def tiltBundle032 : TiltBundle := .ofLines tilt032Lines tilt032_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle033` on `[3/80, 13/320]`, in the order of `Alternative.index`. -/
noncomputable def tilt033Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt033.txt" ↦ Line.ofNats

theorem tilt033_check : bundleCheck tilt033Lines = true := by decide +kernel

def tiltBundle033 : TiltBundle := .ofLines tilt033Lines tilt033_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle034` on `[13/320, 7/160]`, in the order of `Alternative.index`. -/
noncomputable def tilt034Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt034.txt" ↦ Line.ofNats

theorem tilt034_check : bundleCheck tilt034Lines = true := by decide +kernel

def tiltBundle034 : TiltBundle := .ofLines tilt034Lines tilt034_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle035` on `[7/160, 29/640]`, in the order of `Alternative.index`. -/
noncomputable def tilt035Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt035.txt" ↦ Line.ofNats

theorem tilt035_check : bundleCheck tilt035Lines = true := by decide +kernel

def tiltBundle035 : TiltBundle := .ofLines tilt035Lines tilt035_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle036` on `[29/640, 3/64]`, in the order of `Alternative.index`. -/
noncomputable def tilt036Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt036.txt" ↦ Line.ofNats

theorem tilt036_check : bundleCheck tilt036Lines = true := by decide +kernel

def tiltBundle036 : TiltBundle := .ofLines tilt036Lines tilt036_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle037` on `[3/64, 31/640]`, in the order of `Alternative.index`. -/
noncomputable def tilt037Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt037.txt" ↦ Line.ofNats

theorem tilt037_check : bundleCheck tilt037Lines = true := by decide +kernel

def tiltBundle037 : TiltBundle := .ofLines tilt037Lines tilt037_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle038` on `[31/640, 1/20]`, in the order of `Alternative.index`. -/
noncomputable def tilt038Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt038.txt" ↦ Line.ofNats

theorem tilt038_check : bundleCheck tilt038Lines = true := by decide +kernel

def tiltBundle038 : TiltBundle := .ofLines tilt038Lines tilt038_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle039` on `[1/20, 1001/20000]`, in the order of `Alternative.index`. -/
noncomputable def tilt039Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt039.txt" ↦ Line.ofNats

theorem tilt039_check : bundleCheck tilt039Lines = true := by decide +kernel

def tiltBundle039 : TiltBundle := .ofLines tilt039Lines tilt039_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle040` on `[2/25, 33/400]`, in the order of `Alternative.index`. -/
noncomputable def tilt040Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt040.txt" ↦ Line.ofNats

theorem tilt040_check : bundleCheck tilt040Lines = true := by decide +kernel

def tiltBundle040 : TiltBundle := .ofLines tilt040Lines tilt040_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle041` on `[33/400, 17/200]`, in the order of `Alternative.index`. -/
noncomputable def tilt041Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt041.txt" ↦ Line.ofNats

theorem tilt041_check : bundleCheck tilt041Lines = true := by decide +kernel

def tiltBundle041 : TiltBundle := .ofLines tilt041Lines tilt041_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle042` on `[17/200, 7/80]`, in the order of `Alternative.index`. -/
noncomputable def tilt042Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt042.txt" ↦ Line.ofNats

theorem tilt042_check : bundleCheck tilt042Lines = true := by decide +kernel

def tiltBundle042 : TiltBundle := .ofLines tilt042Lines tilt042_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle043` on `[7/80, 9/100]`, in the order of `Alternative.index`. -/
noncomputable def tilt043Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt043.txt" ↦ Line.ofNats

theorem tilt043_check : bundleCheck tilt043Lines = true := by decide +kernel

def tiltBundle043 : TiltBundle := .ofLines tilt043Lines tilt043_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle044` on `[9/100, 19/200]`, in the order of `Alternative.index`. -/
noncomputable def tilt044Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt044.txt" ↦ Line.ofNats

theorem tilt044_check : bundleCheck tilt044Lines = true := by decide +kernel

def tiltBundle044 : TiltBundle := .ofLines tilt044Lines tilt044_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle045` on `[19/200, 1/10]`, in the order of `Alternative.index`. -/
noncomputable def tilt045Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt045.txt" ↦ Line.ofNats

theorem tilt045_check : bundleCheck tilt045Lines = true := by decide +kernel

def tiltBundle045 : TiltBundle := .ofLines tilt045Lines tilt045_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle046` on `[1/10, 17/160]`, in the order of `Alternative.index`. -/
noncomputable def tilt046Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt046.txt" ↦ Line.ofNats

theorem tilt046_check : bundleCheck tilt046Lines = true := by decide +kernel

def tiltBundle046 : TiltBundle := .ofLines tilt046Lines tilt046_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle047` on `[17/160, 9/80]`, in the order of `Alternative.index`. -/
noncomputable def tilt047Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt047.txt" ↦ Line.ofNats

theorem tilt047_check : bundleCheck tilt047Lines = true := by decide +kernel

def tiltBundle047 : TiltBundle := .ofLines tilt047Lines tilt047_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle048` on `[9/80, 1/8]`, in the order of `Alternative.index`. -/
noncomputable def tilt048Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt048.txt" ↦ Line.ofNats

theorem tilt048_check : bundleCheck tilt048Lines = true := by decide +kernel

def tiltBundle048 : TiltBundle := .ofLines tilt048Lines tilt048_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle049` on `[1/8, 3/20]`, in the order of `Alternative.index`. -/
noncomputable def tilt049Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt049.txt" ↦ Line.ofNats

theorem tilt049_check : bundleCheck tilt049Lines = true := by decide +kernel

def tiltBundle049 : TiltBundle := .ofLines tilt049Lines tilt049_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle050` on `[3/20, 7/40]`, in the order of `Alternative.index`. -/
noncomputable def tilt050Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt050.txt" ↦ Line.ofNats

theorem tilt050_check : bundleCheck tilt050Lines = true := by decide +kernel

def tiltBundle050 : TiltBundle := .ofLines tilt050Lines tilt050_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle051` on `[7/40, 1/5]`, in the order of `Alternative.index`. -/
noncomputable def tilt051Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt051.txt" ↦ Line.ofNats

theorem tilt051_check : bundleCheck tilt051Lines = true := by decide +kernel

def tiltBundle051 : TiltBundle := .ofLines tilt051Lines tilt051_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle052` on `[1/5, 9/40]`, in the order of `Alternative.index`. -/
noncomputable def tilt052Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt052.txt" ↦ Line.ofNats

theorem tilt052_check : bundleCheck tilt052Lines = true := by decide +kernel

def tiltBundle052 : TiltBundle := .ofLines tilt052Lines tilt052_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle053` on `[9/40, 1/4]`, in the order of `Alternative.index`. -/
noncomputable def tilt053Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt053.txt" ↦ Line.ofNats

theorem tilt053_check : bundleCheck tilt053Lines = true := by decide +kernel

def tiltBundle053 : TiltBundle := .ofLines tilt053Lines tilt053_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle054` on `[1/4, 11/40]`, in the order of `Alternative.index`. -/
noncomputable def tilt054Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt054.txt" ↦ Line.ofNats

theorem tilt054_check : bundleCheck tilt054Lines = true := by decide +kernel

def tiltBundle054 : TiltBundle := .ofLines tilt054Lines tilt054_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle055` on `[11/40, 3/10]`, in the order of `Alternative.index`. -/
noncomputable def tilt055Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt055.txt" ↦ Line.ofNats

theorem tilt055_check : bundleCheck tilt055Lines = true := by decide +kernel

def tiltBundle055 : TiltBundle := .ofLines tilt055Lines tilt055_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle056` on `[3/10, 13/40]`, in the order of `Alternative.index`. -/
noncomputable def tilt056Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt056.txt" ↦ Line.ofNats

theorem tilt056_check : bundleCheck tilt056Lines = true := by decide +kernel

def tiltBundle056 : TiltBundle := .ofLines tilt056Lines tilt056_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle057` on `[13/40, 7/20]`, in the order of `Alternative.index`. -/
noncomputable def tilt057Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt057.txt" ↦ Line.ofNats

theorem tilt057_check : bundleCheck tilt057Lines = true := by decide +kernel

def tiltBundle057 : TiltBundle := .ofLines tilt057Lines tilt057_check

set_option maxRecDepth 100000 in
/-- The rows of `tiltBundle058` on `[7/20, 3/8]`, in the order of `Alternative.index`. -/
noncomputable def tilt058Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/tilt058.txt" ↦ Line.ofNats

theorem tilt058_check : bundleCheck tilt058Lines = true := by decide +kernel

def tiltBundle058 : TiltBundle := .ofLines tilt058Lines tilt058_check

end SquaresInCircles.Eight.Generated.Owner
