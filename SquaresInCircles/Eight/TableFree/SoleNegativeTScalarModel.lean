module

public import SquaresInCircles.Eight.TableFree.SolePositiveTOrdinaryData

/-!
# The 34 intrinsic sole-E negative-T endpoint scalars

Uncompiled source. The only new interval endpoint is the genuine TD
negative-error cap .3. The base coefficient families are unchanged.
The sorted-D reserve is introduced after the G/E split; the shifted D
charge retains coefficient c instead of the positive-T scalar enlargement.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTScalarModel
open SoleTScalarModel SolePositiveTOrdinaryData PositiveAngularEnvelope SingleAngleConcavity

inductive Row where
  | ehLowDiagonal | ehMiddleDiagonal | ehMiddleShifted (i : Fin 4)
  | ehHighShifted (i : Fin 4) | deLowDiagonal | deLowShifted (i : Fin 3)
  | deHighShifted (i : Fin 3)
  deriving DecidableEq, Fintype

structure Case where
  row : Row
  atG : Bool
  deriving DecidableEq, Fintype

def family : Row → Family
  | .ehLowDiagonal => .ehLow
  | .ehMiddleDiagonal | .ehMiddleShifted _ => .ehMiddle
  | .ehHighShifted _ => .ehHigh
  | .deLowDiagonal | .deLowShifted _ => .deLow
  | .deHighShifted _ => .deHigh

def left : Row → ℚ
  | .ehLowDiagonal | .deLowDiagonal => 0
  | .ehMiddleDiagonal => 1/5
  | .ehMiddleShifted _ | .deLowShifted _ => 3/10
  | .ehHighShifted _ | .deHighShifted _ => 7/20

def right : Row → ℚ
  | .ehLowDiagonal => 1/5
  | .ehMiddleDiagonal | .deLowDiagonal => 3/10
  | .ehMiddleShifted _ | .deLowShifted _ => 7/20
  | .ehHighShifted _ | .deHighShifted _ => 7/10

def shifted : Row → Bool
  | .ehLowDiagonal | .ehMiddleDiagonal | .deLowDiagonal => false
  | _ => true

def index : Row → Fin 4
  | .ehMiddleShifted i | .ehHighShifted i => i
  | .deLowShifted i | .deHighShifted i => ⟨i.val,lt_trans i.isLt (by decide : 3<4)⟩
  | _ => 0

def domain (r : Row) : Set ℝ := Icc (left r:ℝ) (right r:ℝ)
def scalar (s : Case) : ScalarCase := ⟨family s.row,true,s.atG,index s.row⟩
def angle (r : Row) (t : ℝ) : ℝ := if shifted r then t-3/10 else 0
def removed (r : Row) (t : ℝ) : ℝ := if shifted r then 3/10 else t
def correction (s : Case) (t : ℝ) : ℝ :=
  if family s.row=.ehMiddle ∨ family s.row=.ehHigh then
    (8/25)*(c (family s.row) t 0-p (scalar s) t 0)^2 else 0
def coefficient (s : Case) (t : ℝ) : ℝ :=
  if index s.row=3 then c (family s.row) t 0 else nu (scalar s) t 0
def square (s : Case) (t : ℝ) (i : Fin 4) : ℝ :=
  first (scalar s) t 0 i^2+second (scalar s) t 0 i^2-
    if i=index s.row then 2*first (scalar s) t 0 i*second (scalar s) t 0 i*Real.sin (angle s.row t) else 0

def value (s : Case) (R M t : ℝ) : ℝ :=
  k (family s.row) t 0*primaryCoefficient R (g (family s.row) t) (x (scalar s) t 0)+
    3*c (family s.row) t 0+2*ell (family s.row) t 0+eTerm (scalar s) R M t 0+
    correction s t+(21/20)*c (family s.row) t 0*removed s.row t+
    coefficient s t*(Real.cos (angle s.row t)-1)-R*∑i,Real.sqrt (square s t i)

theorem interval_order (r : Row) : 0≤left r ∧ left r<right r ∧ right r≤7/10 := by
  cases r <;> norm_num [left,right]

theorem family_mem {r : Row} {t : ℝ} (ht : t∈domain r) :
    t∈SoleTScalarModel.domain (family r) := by
  cases r <;> norm_num [domain,left,right,SoleTScalarModel.domain,
    SoleTScalarModel.left,SoleTScalarModel.right,family] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem angles {r : Row} {t : ℝ} (ht : t∈domain r) :
    t∈Icc 0 frameCap ∧ angle r t∈Icc 0 frameCap ∧ removed r t∈Icc 0 (3/10:ℝ) := by
  have hf := SoleTScalarModel.angle (family_mem ht)
  refine ⟨hf,?_,?_⟩ <;> cases r <;>
    norm_num [domain,left,right,angle,removed,shifted,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem correction_nonneg (s : Case) (t : ℝ) : 0≤correction s t := by
  dsimp [correction]
  split_ifs
  · positivity
  · exact le_rfl

theorem square_nonneg (s : Case) {t : ℝ} (ht : t∈domain s.row) (i : Fin 4) :
    0≤square s t i := by
  have hf := family_mem ht
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angles ht).1.1⟩
  obtain ⟨hn,hm,hp,ha,hb⟩ := weights_positive (scalar s) hf hz
  dsimp [square]
  split_ifs
  · have hh := mul_nonneg (mul_pos (ha i) (hb i)).le
      (sub_nonneg.mpr (Real.sin_le_one (angle s.row t)))
    nlinarith [sq_nonneg (first (scalar s) t 0 i-second (scalar s) t 0 i)]
  · positivity

theorem scalar_identity (s : Case) (R M t : ℝ) :
    value s R M t=baseline (scalar s) R M t 0+correction s t+
      (21/20)*c (family s.row) t 0*removed s.row t+
      Vnu R (small (scalar s) t 0 (index s.row)) (large (scalar s) t 0 (index s.row))
        (coefficient s t) (angle s.row t) := by
  rw [Vnu,norm_eq,norm_eq]
  cases s.row <;> try (rename_i i; fin_cases i)
  all_goals
    simp [value,baseline,square,index,scalar,family,SoleTScalarModel.x,SoleTScalarModel.e,
      n,m,p,first,second,primaryCoefficient,Fin.sum_univ_succ,pairNorm,Real.sin_neg]
    ring

end SquaresInCircles.Eight.TableFree.SoleNegativeTScalarModel
