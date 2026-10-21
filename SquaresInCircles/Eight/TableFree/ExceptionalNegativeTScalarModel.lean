module

public import SquaresInCircles.Eight.TableFree.ExceptionalEBalanced

/-!
# The forty-four exceptional negative-T endpoint scalars

Uncompiled source. The ten intrinsic intervals are precisely the family
changes and the two genuine secant caps in the hand proof. A diagonal
row has one scalar; a shifted row has the H, A and B alternatives. Both
primary faces are retained, including their different H force pair.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTScalarModel
open ExceptionalECoefficients ExceptionalContactStress ExceptionalContactSupport
open SingleAngleConcavity

inductive Row where
  | tdLowZero | tdLowReturn | tdMiddleDiagonal
  | tdMiddle (i : Fin 3) | tdHigh (i : Fin 3)
  | btLowDiagonal | btLowZero (i : Fin 3) | btLowReturn (i : Fin 3)
  | btMiddle (i : Fin 3) | btHigh (i : Fin 3)
  deriving DecidableEq, Fintype

structure Case where
  row : Row
  atG : Bool
  deriving DecidableEq, Fintype

def band : Row → Band
  | .tdLowZero | .tdLowReturn | .btLowDiagonal | .btLowZero _ | .btLowReturn _ => .low
  | .tdMiddleDiagonal | .tdMiddle _ | .btMiddle _ => .middle
  | .tdHigh _ | .btHigh _ => .high

def isTD : Row → Bool
  | .tdLowZero | .tdLowReturn | .tdMiddleDiagonal | .tdMiddle _ | .tdHigh _ => true
  | _ => false

def diagonal : Row → Bool
  | .tdLowZero | .tdLowReturn | .tdMiddleDiagonal | .btLowDiagonal => true
  | _ => false

def index : Row → Fin 3
  | .tdMiddle i | .tdHigh i | .btLowZero i | .btLowReturn i | .btMiddle i | .btHigh i => i
  | _ => 0

def origin : Row → ℚ
  | .tdLowZero | .btLowDiagonal => 0
  | .tdLowReturn | .btLowReturn _ => 4/25
  | .tdMiddleDiagonal | .btMiddle _ => 9/50
  | .tdMiddle _ => 3/10
  | .tdHigh _ | .btHigh _ => 7/20
  | .btLowZero _ => 9/100

def length : Row → ℚ
  | .tdLowZero => 1/10
  | .tdLowReturn | .btLowReturn _ => 1/50
  | .tdMiddleDiagonal => 3/25
  | .tdMiddle _ => 1/20
  | .tdHigh _ | .btHigh _ => 7/20
  | .btLowDiagonal => 9/100
  | .btLowZero _ => 1/100
  | .btMiddle _ => 17/100

def domain (r : Row) : Set ℝ := Set.Icc (origin r:ℝ) ((origin r+length r):ℝ)
def cap (r : Row) : ℚ := if isTD r then 3/10 else 9/100
def removed (r : Row) (t : ℝ) : ℝ := if diagonal r then t else (cap r:ℝ)
def angle (r : Row) (t : ℝ) : ℝ := t-removed r t
def g (a : ℝ) : ℝ := 13/12-a/5+(8/25)*a^2
def slope (r : Row) (t : ℝ) : ℝ := if isTD r then g (removed r t) else 21/20
def correction (r : Row) (t : ℝ) : ℝ :=
  if isTD r && decide (band r≠.low) then (8/25)*(c (band r) t-1)^2 else 0

def first (s : Case) (t sn cs : ℝ) : Fin 4 → ℝ :=
  ![if s.atG then 1 else cs+eta (band s.row) t*sn,
    k (band s.row) t,ell (band s.row) t,1]
def second (s : Case) (t sn cs : ℝ) : Fin 4 → ℝ :=
  ![if s.atG then k (band s.row) t*(cs+eta (band s.row) t*sn) else k (band s.row) t,
    ell (band s.row) t,c (band s.row) t,c (band s.row) t]
def nu (r : Row) (t : ℝ) : Fin 3 → ℝ := ![53/50,ell (band r) t,c (band r) t]

def outside (s : Case) (t sn cs sd cd : ℝ) : ℝ :=
  (if s.atG then 3+2*ell (band s.row) t+3*c (band s.row) t+
      k (band s.row) t*(1+2*cs+(1+2*eta (band s.row) t)*sn)
    else 3*k (band s.row) t+2*ell (band s.row) t+3*c (band s.row) t+
      1+2*cs+(1+2*eta (band s.row) t)*sn)+
    correction s.row t+c (band s.row) t*slope s.row t*removed s.row t+
    (if diagonal s.row then 0 else nu s.row t (index s.row)*(cd-1))

def squared (s : Case) (t sn cs sd : ℝ) (i : Fin 4) : ℝ :=
  (first s t sn cs i)^2+(second s t sn cs i)^2-
    (if !diagonal s.row && decide (i.val=(index s.row).val)
      then 2*first s t sn cs i*second s t sn cs i*sd else 0)
def square (s : Case) (t sn cs sd : ℝ) (i : Fin 5) : ℝ :=
  if hi : i.val<4 then squared s t sn cs sd ⟨i.val,hi⟩ else 1+(eta (band s.row) t)^2
def weight (s : Case) (t sn : ℝ) (i : Fin 5) : ℝ :=
  if i.val<4 then 1 else if s.atG then k (band s.row) t*sn else sn
def rowSum (s : Case) (t sn cs sd : ℝ) : ℝ :=
  ∑i : Fin 5,weight s t sn i*Real.sqrt (square s t sn cs sd i)
def value (s : Case) (R t : ℝ) : ℝ :=
  outside s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) (Real.cos (angle s.row t))-
    R*rowSum s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t))

def baseline (s : Case) (R t : ℝ) : ℝ :=
  if s.atG then ExceptionalContactSupport.atG R (k (band s.row) t) (ell (band s.row) t)
    (c (band s.row) t) (eta (band s.row) t) t
  else ExceptionalContactSupport.atE R (k (band s.row) t) (ell (band s.row) t)
    (c (band s.row) t) (eta (band s.row) t) t
def charge (s : Case) (R t d : ℝ) (i : Fin 3) : ℝ :=
  Vnu R (first s t (Real.sin t) (Real.cos t) ⟨i.val,by omega⟩)
    (second s t (Real.sin t) (Real.cos t) ⟨i.val,by omega⟩) (nu s.row t i) d

theorem length_pos (r : Row) : 0<length r := by cases r <;> norm_num [length]

theorem family_domain {r : Row} {t : ℝ} (ht : t∈domain r) :
    t∈ExceptionalECoefficients.domain (band r) := by
  cases r <;> norm_num [domain,ExceptionalECoefficients.domain,origin,length,band,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem angles {r : Row} {t : ℝ} (ht : t∈domain r) :
    t∈Set.Icc 0 frameCap ∧ removed r t∈Set.Icc 0 (cap r:ℝ) ∧
      angle r t∈Set.Icc 0 frameCap ∧ removed r t=min t (cap r:ℝ) := by
  cases r <;> norm_num [domain,origin,length,removed,diagonal,cap,isTD,angle,frameCap] at ht ⊢ <;>
    (repeat' constructor) <;> first | linarith [ht.1,ht.2] |
      exact (min_eq_left (by linarith [ht.2])).symm |
      exact (min_eq_right (by linarith [ht.1])).symm

theorem correction_nonneg (r : Row) (t : ℝ) : 0≤correction r t := by
  unfold correction
  split_ifs <;> positivity

theorem local_parameter {r : Row} {t : ℝ} (ht : t∈domain r) :
    t-(origin r:ℝ)∈Set.Icc 0 (length r:ℝ) := by
  dsimp [domain] at ht
  push_cast at ht
  constructor <;> linarith [ht.1,ht.2]

theorem value_identity (s : Case) (R t : ℝ) :
    value s R t=baseline s R t+correction s.row t+
      c (band s.row) t*slope s.row t*removed s.row t+
      charge s R t (angle s.row t) (index s.row) := by
  rcases s with ⟨r,face⟩
  cases r <;> cases face <;> first
    | (simp [value,outside,rowSum,square,squared,weight,first,second,nu,baseline,charge,
        band,isTD,diagonal,index,angle,removed,cap,Vnu,ExceptionalContactSupport.atG,ExceptionalContactSupport.atE,
        contactScalar,tilt,PositiveAngularEnvelope.pairNorm,Real.sin_neg,Fin.sum_univ_succ]; ring)
    | (rename_i i; fin_cases i <;>
        simp [value,outside,rowSum,square,squared,weight,first,second,nu,baseline,charge,
          band,isTD,diagonal,index,angle,removed,cap,Vnu,ExceptionalContactSupport.atG,ExceptionalContactSupport.atE,
          contactScalar,tilt,PositiveAngularEnvelope.pairNorm,Real.sin_neg,Fin.sum_univ_succ] <;> ring)

theorem baseline_actual (s : Case) {R t : ℝ} (ht : t∈Set.Icc 0 frameCap) :
    baseline s R t=ExceptionalContactSupport.baseline R (k (band s.row) t)
      (ell (band s.row) t) (c (band s.row) t) (eta (band s.row) t)
      (if s.atG then t else 0) (if s.atG then 0 else t) := by
  cases h : s.atG <;> simp [baseline,h,baseline_at_G ht,baseline_at_E ht]

theorem scalar_count : Fintype.card Case=44 := by decide

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTScalarModel
