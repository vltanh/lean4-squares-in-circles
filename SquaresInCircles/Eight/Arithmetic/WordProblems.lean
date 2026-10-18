module

public import SquaresInCircles.Eight.BoundaryGeometry

/-!
# The labels and targets of the six wrong quarter words

The three common increment costs and the two role-label systems are kept
separate. The first wrong word uses `c+p*a+sigma*q*b`; the second uses
`sigma*(c+p*a+q*b+r*b^2+s*a*b)`.

The core side and corner are separate closed source and target branches.
The pair tables of `WordGeometry` prove the pair inequalities of these labels.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.WordProblems
open Arithmetic

def sign (positive : Bool) : ℚ := if positive then 1 else -1

def transverseBox : RadialKind→ QInterval
  | .outer => ⟨0,9/10⟩
  | .coreSide => ⟨0,1/2⟩
  | .coreCorner => ⟨1/2,14/25⟩

noncomputable def primaryValue (kind : RadialKind) (b : ℝ) : ℝ :=
  match kind with
  | .outer => Real.sqrt ((9789/2500)-(b+1/2)^2)-1/2
  | .coreSide => 7/12
  | .coreCorner => 1/2+Real.sqrt ((1/144)-(b-1/2)^2)

lemma actual_primary {a b : ℝ} (k : RadialKind) (ha : 1/2<a)
    (hb : 0≤b) (hba : b≤a) (hs : BoundaryState Q0 k a b) :
    a=primaryValue k b ∧ (transverseBox k).Mem b := by
  cases k with
  | outer =>
      have he : (a+1/2)^2+(b+1/2)^2=9789/2500 := by
        simpa [BoundaryState,SquaresInCircles.phi,Q0] using hs
      have hnon : 0≤(9789/2500:ℝ)-(b+1/2)^2 := by linarith [sq_nonneg (a+1/2)]
      have hroot := Real.sq_sqrt hnon
      have hroot0 := Real.sqrt_nonneg ((9789/2500:ℝ)-(b+1/2)^2)
      have hbu : b<9/10 := by nlinarith only [sq_nonneg (a-b), hba, he, ha]
      exact ⟨by dsimp [primaryValue]; nlinarith only [he, hroot, ha, hroot0],
        by norm_num [transverseBox,QInterval.Mem]; exact ⟨hb,hbu.le⟩⟩
  | coreSide =>
      obtain ⟨hA,hB⟩ := hs
      exact ⟨hA,by norm_num [transverseBox,QInterval.Mem]; exact ⟨hb,hB⟩⟩
  | coreCorner =>
      obtain ⟨hB,he⟩ := hs
      have hnon : 0≤(1/144:ℝ)-(b-1/2)^2 := by linarith [sq_nonneg (a-1/2)]
      have hroot := Real.sq_sqrt hnon
      have hroot0 := Real.sqrt_nonneg ((1/144:ℝ)-(b-1/2)^2)
      have hbu : b<14/25 := by nlinarith only [sq_nonneg (a-b), hba, he, ha]
      exact ⟨by dsimp [primaryValue]; nlinarith only [he, hroot, ha, hroot0],
        by norm_num [transverseBox,QInterval.Mem]; exact ⟨hB,hbu.le⟩⟩

def commonGamma (k : Fin 3) : ℚ := ![391/400,157/200,163/200] k

inductive WrongWord | short | second
  deriving DecidableEq, Repr

instance : Fintype WrongWord where
  elems := {.short, .second}
  complete x := by cases x <;> decide

def wrongWord : WrongWord→ QuarterWord
  | .short => ![0,0,1,0,1,1,1]
  | .second => ![0,0,1,1,0,1,1]

def allowed (w : WrongWord) (i : Vertex) (σ τ : Bool) : Prop :=
  (i=0→σ=true) ∧ (i=2→σ=false) ∧
  (next i=0→τ=true) ∧ (next i=2→τ=false) ∧
  (wrongWord w i=0→¬(σ=false ∧ τ=true))
instance (w : WrongWord) (i : Vertex) (σ τ : Bool) : Decidable (allowed w i σ τ) := by
  unfold allowed; infer_instance

/-- Exact coefficients from `short_hand_labels.json`, denominator 100000.
The missing signs at roles 0 and 2 are unreachable by `allowed`; zeros keep
the lookup total and do not certify either excluded sign. -/
def shortCoefficients : Vertex→ Fin 2→ Fin 2→ Fin 3→ℤ :=
  ![![![![0,0,0],![0,0,94766]],![![0,0,0],![3177,0,108816]]],![![![24463,-13422,103828],![6130,0,99940]],![![-14041,0,62095],![25648,0,62095]]],![![![-2623,9133,88074],![0,0,0]],![![11680,0,113855],![0,0,0]]],![![![50866,-33147,113360],![-68803,51554,119909]],![![-15540,0,62750],![4149,0,104729]]],![![![-23483,19335,76744],![6294,0,71553]],![![3897,0,104073],![25812,0,58829]]],![![![29579,-20967,83048],![2448,0,86884]],![![1027,0,95269],![2448,0,99195]]],![![![-18660,18602,80996],![-20704,21826,83472]],![![7651,0,99173],![9072,0,95324]]]]

/-- Exact quadratic coefficients with the source reflection identity expanded.
The entire signed polynomial is multiplied by sigma for this label system. -/
def secondCoefficients : Vertex→ Fin 2→ Fin 2→ Fin 5→ℤ :=
  ![![![![394,0,33945,0,39635],![2478,0,93015,2363,-11055]],![![19911,0,63607,0,0],![125,0,103981,0,0]]],![![![0,-26,83194,-11864,17627],![0,-26,83194,-11864,17627]],![![19555,0,63132,0,0],![19555,0,63132,0,0]]],![![![2478,0,93015,2363,-11055],![394,0,33945,0,39635]],![![125,0,103981,0,0],![19911,0,63607,0,0]]],![![![1670,0,242322,-91744,-95769],![0,-1025,16031,0,63457]],![![22042,-34492,98439,-5334,0],![-1449,0,104240,0,0]]],![![![0,-2112,29090,0,44642],![3965,0,385510,-149748,-189442]],![![16823,0,62312,0,0],![4970,0,94831,0,0]]],![![![3965,0,385510,-149748,-189442],![0,-2112,29090,0,44642]],![![4970,0,94831,0,0],![16823,0,62312,0,0]]],![![![0,-1025,16031,0,63457],![1670,0,242322,-91744,-95769]],![![-1449,0,104240,0,0],![22042,-34492,98439,-5334,0]]]]

def radialIndex (kind : RadialKind) : Fin 2 := if kind=.outer then 0 else 1
def signIndex (σ : Bool) : Fin 2 := if σ then 1 else 0

def wrongGamma (w : WrongWord) (i : Vertex) : ℚ :=
  if w=.short ∧ i=2 then 359/400 else 17953/20000

set_option maxRecDepth 200000 in
theorem all_original_case_count (w : WrongWord) :
    (Finset.univ.filter (fun p : Vertex×Bool×Bool => allowed w p.1 p.2.1 p.2.2)).card=19 := by
  cases w <;> decide

end SquaresInCircles.Eight.WordProblems
