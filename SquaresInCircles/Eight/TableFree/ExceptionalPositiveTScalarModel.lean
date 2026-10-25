module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTSupport
public import SquaresInCircles.Eight.TableFree.SoleTScalarModel

/-!
# The four whole-domain positive-T exceptional-contact scalar families

Uncompiled transcription of the outside-strip hand proof, equations
(5), (6), (9), and (31)--(32), with the extra H coefficient from the
unaligned-contact proof. The Boolean `hCoefficient` selects the two
literal H coefficients n and p; their minimum is the valid max(p,n)
ordinary charge. No ordinary signed angle is erased by this selection.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTScalarModel
open ExceptionalContactStress

inductive Family where
  | lowZero | lowAfter | middle | high
  deriving DecidableEq

instance : Fintype Family where
  elems := {.lowZero, .lowAfter, .middle, .high}
  complete x := by cases x <;> decide

def left : Family → ℚ
  | .lowZero => 0
  | .lowAfter => 4/25
  | .middle => 9/50
  | .high => 7/20
def right : Family → ℚ
  | .lowZero => 1/10
  | .lowAfter => 9/50
  | .middle => 7/20
  | .high => 7/10
def domain (f : Family) : Set ℝ := Icc (left f:ℝ) (right f:ℝ)

def K : Family → ℝ → ℝ
  | .lowZero,t | .lowAfter,t => 17253/20000+67/100*t+27/100*t^2
  | .middle,_ | .high,_ => 1
def L : Family → ℝ → ℝ
  | .lowZero,t | .lowAfter,t => 50521/100000+21/25*t+t^2/2
  | .middle,t => 551/1000+67/100*t+21/100*t^2
  | .high,t => 7/10+8/25*t
def C : Family → ℝ → ℝ
  | .lowZero,t | .lowAfter,t => 17253/20000+18/25*t+3/10*t^2
  | .middle,t => 891/1000+16/25*t+t^2/50
  | .high,_ => 113/100
def eta : Family → ℝ → ℝ
  | .lowZero,t | .lowAfter,t => 131/500+19/100*t+2/25*t^2
  | .middle,t => 61/200-t/50+7/200*t^2
  | .high,t => 27/100+2/25*t

def k (f : Family) (t z : ℝ) : ℝ := K f t+3/50*z
def ell (f : Family) (t z : ℝ) : ℝ := L f t-23/100*z
def c (f : Family) (t z : ℝ) : ℝ := C f t-53/100*z

structure ScalarCase where
  family : Family
  td : Bool
  atG : Bool
  negative : Fin 4
  hCoefficient : Bool
  deriving DecidableEq

instance : Fintype ScalarCase :=
  Fintype.ofEquiv (Family × Bool × Bool × Fin 4 × Bool)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩, fun a => (a.family, a.td, a.atG, a.negative, a.hCoefficient), fun _ => rfl, fun _ => rfl⟩

def x (s : ScalarCase) (t z : ℝ) : ℝ := if s.atG then t-z else 0
def e (s : ScalarCase) (t z : ℝ) : ℝ := if s.atG then 0 else t-z
def n (s : ScalarCase) (t z : ℝ) : ℝ := k s.family t z*tilt (eta s.family t) (x s t z)
def m (s : ScalarCase) (t z : ℝ) : ℝ := c s.family t z*tilt (eta s.family t) z
def p (s : ScalarCase) (t z : ℝ) : ℝ := tilt (eta s.family t) (e s t z)
def first (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ![p s t z,k s.family t z,ell s.family t z,1]
def second (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ![n s t z,ell s.family t z,if s.td then m s t z else c s.family t z,
    if s.td then c s.family t z else m s t z]
def nu (s : ScalarCase) (t z : ℝ) : ℝ :=
  ![if s.hCoefficient then p s t z else n s t z,ell s.family t z,
    if s.td then m s t z+(if s.family=.high then 3/100 else 0) else ell s.family t z,
    if s.td then c s.family t z else m s t z] s.negative
def square (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  first s t z i^2+second s t z i^2-
    if i=s.negative then 2*first s t z i*second s t z i*Real.sin t else 0
def value (s : ScalarCase) (R t z : ℝ) : ℝ :=
  k s.family t z*ExceptionalContactSupport.contactScalar R (eta s.family t) (x s t z)+
    c s.family t z*ExceptionalContactSupport.contactScalar R (eta s.family t) z+
    2*ell s.family t z+ExceptionalContactSupport.contactScalar R (eta s.family t) (e s t z)+
    nu s t z*(Real.cos t-1)-R*∑i,Real.sqrt (square s t z i)

abbrev radiusUpper : ℚ := SoleTScalarModel.radiusUpper

theorem interval_order (f : Family) : 0≤left f ∧ left f<right f ∧ right f≤7/10 := by
  cases f <;> norm_num [left,right]
theorem angle {f : Family} {t : ℝ} (ht : t∈domain f) : t∈Icc 0 frameCap := by
  have ho := interval_order f
  have hl : (0:ℝ)≤(left f:ℝ) := by exact_mod_cast ho.1
  have hu : (right f:ℝ)≤7/10 := by
    have := (Rat.cast_le (K := ℝ)).mpr ho.2.2; push_cast at this; exact this
  have h2 := ht.2
  refine ⟨hl.trans ht.1, ?_⟩
  simp only [frameCap]
  linarith
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
    0<k f t z ∧ 0<ell f t z ∧ 0<c f t z ∧ 0≤eta f t := by
  have htz := angle ht
  simp only [frameCap] at htz
  cases f <;> norm_num [domain,left,right] at ht <;>
    dsimp [k,ell,c,K,L,C,eta] <;>
    refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [hz.1,hz.2,htz.1,htz.2,sq_nonneg t]

theorem split_bounds {f : Family} {t z : ℝ}
    (ht : t∈domain f) (hz : z∈Icc 0 t) :
    k f t z∈Icc (431/500:ℝ) (521/500) ∧
      eta f t∈Icc (1/4:ℝ) (327/1000) := by
  cases f <;> norm_num [domain,left,right] at ht <;>
    dsimp [k,K,eta] <;> refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    nlinarith [hz.1,hz.2,sq_nonneg t]

theorem weights_positive (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) :
    0<n s t z ∧ 0< m s t z ∧ 0<p s t z ∧
      (∀ i,0<first s t z i) ∧ (∀ i,0<second s t z i) := by
  obtain ⟨hk,hl,hc,hη⟩ := coefficient_positive ht hz
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have htilt {a : ℝ} (ha : a∈Icc 0 frameCap) : 0<tilt (eta s.family t) a := by
    dsimp [tilt]
    exact add_pos_of_pos_of_nonneg (by linarith [(transport_trig ha).1])
      (mul_nonneg hη (transport_trig ha).2.2.1)
  have hn : 0<n s t z := mul_pos hk (htilt hx)
  have hm : 0 < m s t z := mul_pos hc (htilt hz')
  have hp : 0<p s t z := htilt he
  refine ⟨hn,hm,hp,?_,?_⟩
  · intro i; fin_cases i <;> simp_all [first]
  · intro i; fin_cases i <;> simp [second] <;> first | assumption | (split_ifs <;> assumption)

theorem square_nonneg (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) : 0≤ square s t z i := by
  obtain ⟨_,_,_,ha,hb⟩ := weights_positive s ht hz
  dsimp [square]
  split_ifs
  · have hh := mul_nonneg (mul_pos (ha i) (hb i)).le
      (sub_nonneg.mpr (Real.sin_le_one t))
    nlinarith [sq_nonneg (first s t z i-second s t z i)]
  · rw [sub_zero]; positivity

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTScalarModel
