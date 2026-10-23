module

public import SquaresInCircles.Eight.TableFree.ExceptionalContactBlocks

/-!
# Continuous rational weights outside the exceptional critical strip

Uncompiled source. The low polynomial family is defined on the entire
[0,.18] interval, although its strict scalar exclusion is used only
on [0,.1] and [.16,.18]. The middle and high families cover the full
remaining intervals. No partition of geometric states is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ExceptionalECoefficients
open ExceptionalContactStress

inductive Band where
  | low | middle | high
  deriving DecidableEq, Fintype

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
  dsimp [k,c,ell,eta]
  repeat' constructor <;> nlinarith

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
  dsimp [k,c,ell]
  repeat' constructor <;> nlinarith [sq_nonneg t]

theorem balanced_bounds {b : Band} {t : ℝ} (hb : b≠.low) (ht : t∈domain b) :
    k b t=1 ∧ 2/3<ell b t ∧ ell b t<1 ∧ 1<c b t ∧ c b t≤113/100 ∧
      (2/3)*c b t≤ell b t ∧ 149/500≤eta b t ∧ eta b t≤163/500 := by
  cases b
  · exact (hb rfl).elim
  · have ht0 : 9/50≤t := ht.1
    have ht1 : t≤7/20 := ht.2
    have ht2 : t^2≤49/400 := by nlinarith
    have ht2' : 81/2500≤t^2 := by nlinarith
    dsimp [k,ell,c,eta]
    repeat' constructor <;> first | rfl | nlinarith [sq_nonneg (t-2/7)]
  · have ht0 : 7/20≤t := ht.1
    have ht1 : t≤7/10 := ht.2
    dsimp [k,ell,c,eta]
    repeat' constructor <;> first | rfl | nlinarith

theorem ranges {b : Band} {t : ℝ} (ht : t∈domain b) :
    k b t∈Icc (431/500:ℝ) 1 ∧ 0<ell b t ∧ ell b t<1 ∧
    0<c b t ∧ c b t<1131/1000 ∧ eta b t∈Icc (1/4:ℝ) (327/1000) := by
  by_cases hb : b=.low
  · subst b
    rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    repeat' constructor <;> linarith
  · rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
    rw [hk]
    repeat' constructor <;> linarith

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

end SquaresInCircles.Eight.TableFree.ExceptionalECoefficients
