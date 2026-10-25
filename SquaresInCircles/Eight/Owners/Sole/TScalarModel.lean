module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the five continuous sole-E coefficient families with a T primary

The primary total is `t`; `z` is the actual positive
T-primary error. The other two nonnegative primary errors are split at
the two endpoints of their fixed-total interval. Both T owner rows and
all four actual negative indices have explicit scalar formulas.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleTScalarModel

inductive Family where
  | ehLow | ehMiddle | ehHigh | deLow | deHigh
  deriving DecidableEq

instance : Fintype Family where
  elems := {.ehLow, .ehMiddle, .ehHigh, .deLow, .deHigh}
  complete x := by cases x <;> decide

def left : Family → ℚ
  | .ehLow | .deLow => 0
  | .ehMiddle => 1/5
  | .ehHigh | .deHigh => 7/20

def right : Family → ℚ
  | .ehLow => 1/5
  | .ehMiddle | .deLow => 7/20
  | .ehHigh | .deHigh => 7/10

def domain (f : Family) : Set ℝ := Icc (left f:ℝ) (right f:ℝ)

def isDE : Family → Bool
  | .deLow | .deHigh => true
  | _ => false

def tiltedE : Family → Bool
  | .ehLow | .ehMiddle => true
  | _ => false

def K : Family → ℝ → ℝ
  | .ehLow,t => 17253/20000+11/20*t+3/10*t^2
  | .ehMiddle,t => 983/1000+1/10*(t-1/5)-3/10*(t-1/5)^2
  | .ehHigh,t => 1017/1000-1/50*t
  | .deLow,t => 53/50-1/10*t
  | .deHigh,t => 107/100-3/25*t

def L : Family → ℝ → ℝ
  | .ehLow,t => 50521/100000+823/1000*t+7/10*t^2
  | .ehMiddle,t => 349/500+9/10*(t-1/5)-(t-1/5)^2
  | .ehHigh,t => 7/10+9/25*t
  | .deLow,t => 113/200+3/4*t
  | .deHigh,t => 77/100+1/5*t

def C : Family → ℝ → ℝ
  | .ehLow,t => K .ehLow t+3/10*t
  | .ehMiddle,t => 209/200+13/20*(t-1/5)-3/2*(t-1/5)^2
  | .ehHigh,_ => 113/100
  | .deLow,t => 903/1000+13/20*t
  | .deHigh,_ => 113/100

def g : Family → ℝ → ℝ
  | .ehLow,_ | .deLow,_ => 8/25
  | .ehMiddle,_ => 31/100
  | .ehHigh,t => 27/100+2/25*t
  | .deHigh,t => 3/10+1/20*t

def epsilon : Family → ℝ → ℝ
  | .ehLow,t => 131/500+267/1000*t+1/10*t^2
  | .ehMiddle,t => 319/1000+1/5*(t-1/5)
  | _,_ => 0

def k (f : Family) (t z : ℝ) : ℝ := K f t+3/50*z
def ell (f : Family) (t z : ℝ) : ℝ := L f t-23/100*z
def c (f : Family) (t z : ℝ) : ℝ := C f t-53/100*z
def eta (t : ℝ) : ℝ := 1/4+33/100*t
def lambda (f : Family) : ℝ := if isDE f then 5/4 else 1

structure ScalarCase where
  family : Family
  td : Bool
  atG : Bool
  negative : Fin 4
  deriving DecidableEq

instance : Fintype ScalarCase :=
  Fintype.ofEquiv (Family × Bool × Bool × Fin 4)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun a => (a.family, a.td, a.atG, a.negative), fun _ => rfl, fun _ => rfl⟩

def x (s : ScalarCase) (t z : ℝ) : ℝ := if s.atG then t-z else 0
def e (s : ScalarCase) (t z : ℝ) : ℝ := if s.atG then 0 else t-z
def n (s : ScalarCase) (t z : ℝ) : ℝ :=
  k s.family t z*(Real.cos (x s t z)+g s.family t*Real.sin (x s t z))
def m (s : ScalarCase) (t z : ℝ) : ℝ :=
  c s.family t z*(Real.cos z+eta t*Real.sin z)
def p (s : ScalarCase) (t z : ℝ) : ℝ :=
  if tiltedE s.family then Real.cos (e s t z)+epsilon s.family t*Real.sin (e s t z) else 1

def first (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ![lambda s.family,k s.family t z,ell s.family t z,p s t z]
def second (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ![n s t z,ell s.family t z,if s.td then m s t z else c s.family t z,
    if s.td then c s.family t z else m s t z]
def nu (s : ScalarCase) (t z : ℝ) : ℝ :=
  ![if isDE s.family then 5/4 else n s t z,ell s.family t z,
    if s.td then m s t z else ell s.family t z,1131/1000] s.negative

def square (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  first s t z i^2+second s t z i^2-
    if i=s.negative then 2*first s t z i*second s t z i*Real.sin t else 0

def primaryCoefficient (R v a : ℝ) : ℝ :=
  1+2*Real.cos a+(1+2*v-R*Real.sqrt (1+v^2))*Real.sin a

def eTerm (s : ScalarCase) (R M t z : ℝ) : ℝ :=
  if tiltedE s.family then primaryCoefficient R (epsilon s.family t) (e s t z)
  else if isDE s.family then
    1+Real.cos (e s t z)/2+(1-M)*Real.sin (e s t z)+3/2*(5/4)
  else 3+Real.sin (e s t z)-2*R*Real.sin (e s t z/2)

def value (s : ScalarCase) (R M t z : ℝ) : ℝ :=
  k s.family t z*primaryCoefficient R (g s.family t) (x s t z)+
    c s.family t z*primaryCoefficient R (eta t) z+2*ell s.family t z+
    eTerm s R M t z+nu s t z*(Real.cos t-1)-R*∑ i,Real.sqrt (square s t z i)

def radiusUpper : ℚ := 989385433/500000000
def axisUpper : ℚ := 1914558470771/1000000000000

theorem interval_order (f : Family) : 0≤left f ∧ left f<right f ∧ right f≤7/10 := by
  cases f <;> norm_num [left,right]

theorem angle {f : Family} {t : ℝ} (ht : t∈domain f) : t∈Icc 0 frameCap := by
  have ho := interval_order f
  have hl : (0:ℝ)≤(left f:ℝ) := by exact_mod_cast ho.1
  have hu : (right f:ℝ)≤(7/10:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr ho.2.2
    simpa using h
  exact ⟨hl.trans ht.1,ht.2.trans (by simpa [frameCap] using hu)⟩

theorem split_angles (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) :
    z∈Icc 0 frameCap ∧ x s t z∈Icc 0 frameCap ∧ e s t z∈Icc 0 frameCap := by
  have ht' := angle ht
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht'.2⟩
  have hgap : t-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [ht'.2,hz.1]⟩
  have hzero : (0:ℝ)∈Icc 0 frameCap := ⟨le_rfl,by norm_num [frameCap]⟩
  refine ⟨hz',?_,?_⟩ <;> dsimp [x,e] <;> split_ifs <;> assumption

theorem coefficient_positive {f : Family} {t z : ℝ}
    (ht : t∈domain f) (hz : z∈Icc 0 t) :
    0<k f t z ∧ 0<ell f t z ∧ 0<c f t z ∧
      0≤g f t ∧ 0≤epsilon f t ∧ 0≤eta t := by
  have htz := angle ht
  have hz0 := hz.1
  have hzt := hz.2
  have ht0 := htz.1
  have hsq0 := sq_nonneg t
  have hmid : (t-1/5)^2≤1/4 := by
    have h2 := htz.2
    dsimp [frameCap] at h2
    nlinarith
  cases f <;> norm_num [domain,left,right] at ht <;>
    obtain ⟨ht1,ht2⟩ := ht <;>
    dsimp [k,ell,c,K,L,C,g,epsilon,eta] <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem weights_positive (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) :
    0<n s t z ∧ 0< m s t z ∧ 0<p s t z ∧
      (∀ i,0<first s t z i) ∧ (∀ i,0<second s t z i) := by
  obtain ⟨hk,hl,hc,hg,he,hη⟩ := coefficient_positive ht hz
  obtain ⟨hz',hx,he'⟩ := split_angles s ht hz
  have hn : 0<n s t z := by
    dsimp [n]
    exact mul_pos hk (add_pos_of_pos_of_nonneg
      (by linarith [(transport_trig hx).1]) (mul_nonneg hg (transport_trig hx).2.2.1))
  have hm : 0< m s t z := by
    dsimp [m]
    exact mul_pos hc (add_pos_of_pos_of_nonneg
      (by linarith [(transport_trig hz').1]) (mul_nonneg hη (transport_trig hz').2.2.1))
  have hp : 0<p s t z := by
    dsimp [p]
    split_ifs
    · exact add_pos_of_pos_of_nonneg (by linarith [(transport_trig he').1])
        (mul_nonneg he (transport_trig he').2.2.1)
    · norm_num
  refine ⟨hn,hm,hp,?_,?_⟩
  · intro i
    fin_cases i <;> simp only [first,
      ]
    · dsimp [lambda]; split_ifs <;> norm_num
    · exact hk
    · exact hl
    · exact hp
  · intro i
    fin_cases i <;> simp only [second,
      ]
    · exact hn
    · exact hl
    · split_ifs <;> assumption
    · split_ifs <;> assumption

theorem square_nonneg (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) : 0≤ square s t z i := by
  obtain ⟨hn,hm,hp,ha,hb⟩ := weights_positive s ht hz
  dsimp [square]
  split_ifs
  · have hc := mul_nonneg (mul_pos (ha i) (hb i)).le
      (sub_nonneg.mpr (Real.sin_le_one t))
    nlinarith [sq_nonneg (first s t z i-second s t z i)]
  · rw [sub_zero]
    positivity

theorem radius_upper : Real.sqrt qTrial<(radiusUpper:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤qTrial by norm_num [qTrial])
  have hn := Real.sqrt_nonneg qTrial
  norm_num [radiusUpper,qTrial] at *
  nlinarith

theorem axis_upper : Real.sqrt (qTrial-1/4)<(axisUpper:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤qTrial-1/4 by norm_num [qTrial])
  have hn := Real.sqrt_nonneg (qTrial-1/4)
  norm_num [axisUpper,qTrial] at *
  nlinarith

end SquaresInCircles.Eight.SoleTScalarModel
