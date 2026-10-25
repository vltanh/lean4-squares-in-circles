module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.Exceptional.ContactSupport

/-!
# Eight squares: the forty-four exceptional negative-T endpoint scalars

The ten intervals are cut at the changes of coefficient family and at the two secant caps. A
diagonal row has one scalar, a shifted row has the H, A and B alternatives (`Row`, `Case`). Both
primary faces are kept, with their different force pairs on H, and each scalar splits into the
baseline, the correction, the removed secant part and the charge (`value_identity`).
-/

section
/-!
## Continuous rational weights outside the exceptional critical strip

The low polynomial family is defined on the entire
[0,.18] interval, although its strict scalar exclusion is used only
on [0,.1] and [.16,.18]. The middle and high families cover the full
remaining intervals. No partition of geometric states is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalECoefficients
open ExceptionalContactStress

inductive Band where
  | low | middle | high
  deriving DecidableEq

instance : Fintype Band where
  elems := {.low, .middle, .high}
  complete x := by cases x <;> decide

def domain : Band → Set ℝ
  | .low => Icc 0 (9/50)
  | .middle => Icc (9/50) (7/20)
  | .high => Icc (7/20) frameCap

def k : Band → ℝ → ℝ
  | .low,t => 17253/20000+(67/100)*t+(27/100)*t^2
  | _,_ => 1

def ell : Band → ℝ → ℝ
  | .low,t => 50521/100000+(21/25)*t+t^2/2
  | .middle,t => 551/1000+(67/100)*t+(21/100)*t^2
  | .high,t => 7/10+(8/25)*t

def c : Band → ℝ → ℝ
  | .low,t => 17253/20000+(18/25)*t+(3/10)*t^2
  | .middle,t => 891/1000+(16/25)*t+t^2/50
  | .high,_ => 113/100

def eta : Band → ℝ → ℝ
  | .low,t => 131/500+(19/100)*t+(2/25)*t^2
  | .middle,t => 61/200-t/50+(7/200)*t^2
  | .high,t => 27/100+(2/25)*t

theorem angle {b : Band} {t : ℝ} (ht : t∈domain b) : t∈Icc 0 frameCap := by
  cases b <;> norm_num [domain,frameCap] at ht ⊢ <;> constructor <;> linarith [ht.1,ht.2]

theorem low_bounds {t : ℝ} (ht : t∈domain .low) :
    17253/20000≤k .low t ∧ k .low t<1 ∧ k .low t≤c .low t ∧ c .low t<501/500 ∧
    1/2<ell .low t ∧ ell .low t<673/1000 ∧ ell .low t≤(18/25)*k .low t ∧
    329/1000<c .low t-ell .low t ∧
    131/500≤eta .low t ∧ eta .low t<299/1000 := by
  have ht0 : 0≤t := ht.1
  have ht1 : t≤9/50 := ht.2
  have ht2 : t^2≤81/2500 := by nlinarith
  have hts : 0≤t^2 := sq_nonneg t
  dsimp only [k,c,ell,eta]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem low_correlations {t : ℝ} (ht : t∈domain .low) :
    (117/200+(7/20)*t)*c .low t≤ell .low t ∧
    ell .low t≤(337/500)*c .low t ∧
    c .low t-k .low t=t/20+(3/100)*t^2 ∧
    c .low t-k .low t≤(111/2000)*t := by
  have ht0 : 0≤t := ht.1
  have ht1 : t≤9/50 := ht.2
  have ht2 : t^2≤(9/50)*t := by nlinarith
  have ht2' : t^2≤81/2500 := by nlinarith
  have ht3 : t^3≤(9/50)*t^2 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht2)]
  have hts : 0≤t^2 := sq_nonneg t
  dsimp only [k,c,ell]
  refine ⟨?_,?_,?_,?_⟩
  · linarith
  · linarith
  · ring
  · linarith

theorem balanced_bounds {b : Band} {t : ℝ} (hb : b≠.low) (ht : t∈domain b) :
    k b t=1 ∧ 2/3<ell b t ∧ ell b t<1 ∧ 1<c b t ∧ c b t≤113/100 ∧
      (2/3)*c b t≤ell b t ∧ 149/500≤eta b t ∧ eta b t≤163/500 := by
  cases b
  · exact (hb rfl).elim
  · have ht0 : 9/50≤t := ht.1
    have ht1 : t≤7/20 := ht.2
    have ht2 : t^2≤49/400 := by nlinarith
    have ht2' : 81/2500≤t^2 := by nlinarith
    dsimp only [k,ell,c,eta]
    refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith [sq_nonneg (t-2/7)]
  · have ht0 : 7/20≤t := ht.1
    have ht1 : t≤7/10 := ht.2
    dsimp only [k,ell,c,eta]
    refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem ranges {b : Band} {t : ℝ} (ht : t∈domain b) :
    k b t∈Icc (431/500:ℝ) 1 ∧ 0<ell b t ∧ ell b t<1 ∧
    0<c b t ∧ c b t<1131/1000 ∧ eta b t∈Icc (1/4:ℝ) (327/1000) := by
  by_cases hb : b=.low
  · subst b
    rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,⟨?_,?_⟩⟩ <;> linarith
  · rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
    rw [hk]
    refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,⟨?_,?_⟩⟩ <;> linarith

theorem low_tilt {t s : ℝ} (ht : t∈domain .low) (hs : s∈Icc 0 t) :
    1≤tilt (eta .low t) s ∧ tilt (eta .low t) s<21/20 := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  exact ⟨SoleLowCoefficientBounds.tilted_lower
    ⟨by linarith,by linarith⟩ ⟨hs.1,by linarith [hs.2,ht.2]⟩,
    SoleLowCoefficientBounds.tilted_upper ⟨by linarith,by linarith⟩⟩

/-- The coarse .95 lower bound is enough for the complete balanced
ordinary envelope, including the two-angle H block. -/
theorem balanced_tilt {b : Band} {t s : ℝ} (hb : b≠.low) (ht : t∈domain b)
    (hs : s∈Icc 0 t) : 19/20<tilt (eta b t) s ∧ tilt (eta b t) s<53/50 := by
  rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans (angle ht).2⟩
  have hh : (19/20:ℝ)<Real.cos s+(149/500)*Real.sin s := by
    have hz := trig_concave_gt (α := (0:ℝ)) (A := (149/500:ℝ)) (B := (1:ℝ))
      (m := (19/20:ℝ)) (l := (0:ℝ)) (u := frameCap)
      (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hs'
      (by norm_num)
      (by have hc := (transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
          have hsn := OrdinaryNegativeEnvelope.cap_sin_lower
          nlinarith)
    simpa only [zero_mul,one_mul,zero_add,add_comm] using hz
  have hm := mul_le_mul_of_nonneg_right he0 (transport_trig hs').2.2.1
  refine ⟨by dsimp [tilt]; linarith,?_⟩
  exact SoleBalancedCoefficients.tilted_upper ⟨by linarith,by linarith⟩

theorem tilt_pos {b : Band} {t s : ℝ} (ht : t∈domain b) (hs : s∈Icc 0 t) :
    0<tilt (eta b t) s := by
  by_cases hb : b=.low
  · subst b
    linarith [(low_tilt ht hs).1]
  · linarith [(balanced_tilt hb ht hs).1]

theorem contactScalar_le_three {R eta t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (heta : eta≤327/1000)
    (ht : t∈Icc 0 frameCap) : ExceptionalContactSupport.contactScalar R eta t≤3 := by
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hs0 := Real.sqrt_nonneg (1+eta^2)
  have hs2 := Real.sq_sqrt (show 0≤1+eta^2 by positivity)
  have hs1 : 1≤Real.sqrt (1+eta^2) := by nlinarith [sq_nonneg eta]
  have hm := mul_le_mul_of_nonneg_left hs1 hR
  have hcoef : 1+2*eta-R*Real.sqrt (1+eta^2)<0 := by linarith
  have hsin := (transport_trig ht).2.2.1
  have hprod := mul_nonpos_of_nonpos_of_nonneg hcoef.le hsin
  dsimp [ExceptionalContactSupport.contactScalar]
  linarith [Real.cos_le_one t]

end SquaresInCircles.Eight.ExceptionalECoefficients
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTScalarModel
open ExceptionalECoefficients ExceptionalContactStress ExceptionalContactSupport
open SingleAngleConcavity

inductive Row where
  | tdLowZero | tdLowReturn | tdMiddleDiagonal
  | tdMiddle (i : Fin 3) | tdHigh (i : Fin 3)
  | btLowDiagonal | btLowZero (i : Fin 3) | btLowReturn (i : Fin 3)
  | btMiddle (i : Fin 3) | btHigh (i : Fin 3)
  deriving DecidableEq

instance : Fintype Row where
  elems := {.tdLowZero, .tdLowReturn, .tdMiddleDiagonal, .btLowDiagonal} ∪
    Finset.univ.image Row.tdMiddle ∪
    Finset.univ.image Row.tdHigh ∪
    Finset.univ.image Row.btLowZero ∪
    Finset.univ.image Row.btLowReturn ∪
    Finset.univ.image Row.btMiddle ∪
    Finset.univ.image Row.btHigh
  complete x := by cases x <;> simp

structure Case where
  row : Row
  atG : Bool
  deriving DecidableEq

instance : Fintype Case :=
  Fintype.ofEquiv (Row × Bool)
    ⟨fun p => ⟨p.1, p.2⟩, fun a => (a.row, a.atG), fun _ => rfl, fun _ => rfl⟩

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

def outside (s : Case) (t sn cs _sd cd : ℝ) : ℝ :=
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
    (repeat' constructor) <;> linarith [ht.1,ht.2]

theorem local_parameter {r : Row} {t : ℝ} (ht : t∈domain r) :
    t-(origin r:ℝ)∈Set.Icc 0 (length r:ℝ) := by
  dsimp [domain] at ht
  constructor <;> linarith [ht.1,ht.2]

theorem value_identity (s : Case) (R t : ℝ) :
    value s R t=baseline s R t+correction s.row t+
      c (band s.row) t*slope s.row t*removed s.row t+
      charge s R t (angle s.row t) (index s.row) := by
  rcases s with ⟨r, face⟩
  unfold value rowSum square squared weight charge baseline
  simp only [Fin.sum_univ_five]
  cases hdg : diagonal r
  · generalize hj : index r = j
    have hout : outside ⟨r, face⟩ t (Real.sin t) (Real.cos t) (Real.sin (angle r t))
        (Real.cos (angle r t)) = (if face then 3+2*ell (band r) t+3*c (band r) t+
          k (band r) t*(1+2*Real.cos t+(1+2*eta (band r) t)*Real.sin t)
        else 3*k (band r) t+2*ell (band r) t+3*c (band r) t+1+2*Real.cos t+
          (1+2*eta (band r) t)*Real.sin t)+correction r t+c (band r) t*slope r t*removed r t+
        nu r t j*(Real.cos (angle r t)-1) := by
      simp [outside, hdg, hj]
    rw [hout]
    fin_cases j <;> cases face <;>
      simp [first, second, nu, Vnu, ExceptionalContactSupport.atG, ExceptionalContactSupport.atE,
        ExceptionalContactSupport.contactScalar, ExceptionalContactStress.tilt,
        PositiveAngularEnvelope.pairNorm, Real.sin_neg] <;> ring_nf
  · have ha : angle r t = 0 := by simp [angle, removed, hdg]
    have hout : outside ⟨r, face⟩ t (Real.sin t) (Real.cos t) (Real.sin (angle r t))
        (Real.cos (angle r t)) = (if face then 3+2*ell (band r) t+3*c (band r) t+
          k (band r) t*(1+2*Real.cos t+(1+2*eta (band r) t)*Real.sin t)
        else 3*k (band r) t+2*ell (band r) t+3*c (band r) t+1+2*Real.cos t+
          (1+2*eta (band r) t)*Real.sin t)+correction r t+c (band r) t*slope r t*removed r t := by
      simp [outside, hdg]
    rw [hout, ha]
    cases face <;>
      simp [first, second, nu, Vnu, ExceptionalContactSupport.atG, ExceptionalContactSupport.atE,
        ExceptionalContactSupport.contactScalar, ExceptionalContactStress.tilt,
        PositiveAngularEnvelope.pairNorm] <;> ring_nf

end SquaresInCircles.Eight.ExceptionalNegativeTScalarModel
end
end
end
