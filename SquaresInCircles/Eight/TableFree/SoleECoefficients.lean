module

public import SquaresInCircles.Eight.TableFree.SoleAngleGrowth
public import SquaresInCircles.Eight.TableFree.PositiveStressCoefficients

/-!
# The three analytic sole-E coefficient families

Uncompiled source. These are polynomial formulas on three complete
overlapping closed intervals. The overlap is intentional: either stress
is valid at a shared endpoint. The total primary angle is the parameter;
the coefficients remain fixed when that total is split.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleECoefficients
open SecondaryEStress

inductive Band where
  | low | middle | high
  deriving DecidableEq

instance : Fintype Band where
  elems := {.low, .middle, .high}
  complete x := by cases x <;> decide

def domain : Band → Set ℝ
  | .low => Icc 0 (1/5)
  | .middle => Icc (1/5) (7/20)
  | .high => Icc (7/20) frameCap

def k : Band → ℝ → ℝ
  | .low,t => 17253/20000+11/20*t+3/10*t^2
  | .middle,t => 983/1000+1/10*(t-1/5)-3/10*(t-1/5)^2
  | .high,t => 1017/1000-1/50*t

def c : Band → ℝ → ℝ
  | .low,t => k .low t+3/10*t
  | .middle,t => 209/200+13/20*(t-1/5)-3/2*(t-1/5)^2
  | .high,_ => 113/100

def ell : Band → ℝ → ℝ
  | .low,t => 50521/100000+823/1000*t+7/10*t^2
  | .middle,t => 349/500+9/10*(t-1/5)-(t-1/5)^2
  | .high,t => 7/10+9/25*t

def g : Band → ℝ → ℝ
  | .low,_ => 8/25
  | .middle,_ => 31/100
  | .high,t => 27/100+2/25*t

def eta : Band → ℝ → ℝ
  | .low,t => 131/500+267/1000*t+1/10*t^2
  | .middle,t => 319/1000+1/5*(t-1/5)
  | .high,_ => 7/20

def n (b : Band) (t x : ℝ) : ℝ := tiltedWeight (k b t) (g b t) x

def p (b : Band) (t e : ℝ) : ℝ :=
  if b=.high then 1 else Real.cos e+eta b t*Real.sin e

def r (b : Band) (e : ℝ) : ℝ :=
  if b=.high then 1 else Real.cos e+(7/10)*Real.sin e

def choose (t : ℝ) : Band := if t≤1/5 then .low else if t≤7/20 then .middle else .high

theorem choose_mem {t : ℝ} (ht : t∈Icc 0 frameCap) : t∈domain (choose t) := by
  dsimp [choose]
  split_ifs with h1 h2
  · exact ⟨ht.1,h1⟩
  · exact ⟨by linarith,h2⟩
  · exact ⟨by linarith,ht.2⟩

theorem angle {b : Band} {t : ℝ} (ht : t∈domain b) : t∈Icc 0 frameCap := by
  cases b <;> dsimp [domain,frameCap] at ht ⊢ <;> constructor <;> linarith [ht.1,ht.2]

theorem low_bounds {t : ℝ} (ht : t∈domain .low) :
    17253/20000≤k .low t ∧ k .low t<197/200 ∧
    k .low t≤c .low t ∧ c .low t<209/200 ∧
    50521/100000≤ell .low t ∧ ell .low t<349/500 ∧
    ell .low t<k .low t ∧ c .low t≤2*ell .low t ∧
    131/500≤eta .low t ∧ eta .low t<8/25 := by
  have ht0 : 0≤t := ht.1
  have htu : t≤1/5 := ht.2
  have hsq : t^2≤t/5 := by nlinarith
  have hsq0 := sq_nonneg t
  dsimp [k,c,ell,eta]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem low_correlations {t : ℝ} (ht : t∈domain .low) :
    (117/200+7/20*t)*c .low t≤ell .low t ∧
    ell .low t<(669/1000)*c .low t ∧
    ell .low t<(18/25)*k .low t ∧
    173/500<c .low t-ell .low t := by
  have ht0 : 0≤t := ht.1
  have htu : t≤1/5 := ht.2
  have hsq : t^2≤t/5 := by nlinarith
  have hsq0 := sq_nonneg t
  have htail := mul_nonneg (sq_nonneg t)
    (show 0≤(227/1000 : ℝ)-(21/200)*t by linarith)
  dsimp [k,c,ell]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem middle_bounds {t : ℝ} (ht : t∈domain .middle) :
    983/1000≤k .middle t ∧ k .middle t<1 ∧
    209/200≤c .middle t ∧ c .middle t<111/100 ∧
    349/500≤ell .middle t ∧ ell .middle t<811/1000 ∧
    ell .middle t<k .middle t ∧
    (2/3)*c .middle t≤ell .middle t ∧
    319/1000≤eta .middle t ∧ eta .middle t<7/20 := by
  have hz0 : 0≤t-1/5 := by linarith [ht.1]
  have hzu : t-1/5≤3/20 := by linarith [ht.2]
  have hz2 : (t-1/5)^2≤(3/20)*(t-1/5) := by nlinarith
  have hcmax := mul_nonneg (show 0≤3/20-(t-1/5) by linarith)
    (show 0≤13/20-(3/2)*((t-1/5)+3/20) by linarith)
  have hlmax := mul_nonneg (show 0≤3/20-(t-1/5) by linarith)
    (show 0≤9/10-((t-1/5)+3/20) by linarith)
  have hsq0 := sq_nonneg (t-1/5)
  dsimp [k,c,ell,eta]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem high_bounds {t : ℝ} (ht : t∈domain .high) :
    1003/1000≤k .high t ∧ k .high t≤101/100 ∧
    c .high t=113/100 ∧
    413/500≤ell .high t ∧ ell .high t≤119/125 ∧
    ell .high t<k .high t ∧
    (2/3)*c .high t≤ell .high t ∧
    149/500≤g .high t ∧ g .high t≤163/500 := by
  have ht0 : 7/20≤t := ht.1
  have htu : t≤7/10 := ht.2
  dsimp [k,c,ell,g]
  refine ⟨?_,?_,rfl,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem positive {b : Band} {t : ℝ} (ht : t∈domain b) :
    0<k b t ∧ 0<ell b t ∧ 0<c b t ∧ 0≤g b t ∧ 0≤eta b t := by
  cases b
  · have hh := low_bounds ht
    dsimp [g]
    exact ⟨by linarith [hh.1],by linarith [hh.2.2.2.2.1],
      by linarith [hh.1,hh.2.2.1],by norm_num,by linarith [hh.2.2.2.2.2.2.2.2.1]⟩
  · have hh := middle_bounds ht
    dsimp [g]
    exact ⟨by linarith [hh.1],by linarith [hh.2.2.2.2.1],
      by linarith [hh.2.2.1],by norm_num,by linarith [hh.2.2.2.2.2.2.2.2.1]⟩
  · have hh := high_bounds ht
    exact ⟨by linarith [hh.1],by linarith [hh.2.2.2.1],
      by rw [hh.2.2.1]; norm_num,by linarith [hh.2.2.2.2.2.2.2.1],by norm_num [eta]⟩

theorem weights_positive {b : Band} {t x e : ℝ} (ht : t∈domain b)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) : 0<n b t x ∧ 0<p b t e ∧ 0<r b e := by
  obtain ⟨hk,hl,hc,hg,heta⟩ := positive ht
  have hd := angle ht
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hd.2⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans hd.2⟩
  have hcx : 0<Real.cos x := by linarith [(transport_trig hx').1]
  have hce : 0<Real.cos e := by linarith [(transport_trig he').1]
  have hsx := (transport_trig hx').2.2.1
  have hse := (transport_trig he').2.2.1
  refine ⟨?_,?_,?_⟩
  · exact mul_pos hk (add_pos_of_pos_of_nonneg hcx (mul_nonneg hg hsx))
  · dsimp [p]
    split_ifs
    · norm_num
    · exact add_pos_of_pos_of_nonneg hce (mul_nonneg heta hse)
  · dsimp [r]
    split_ifs
    · norm_num
    · exact add_pos_of_pos_of_nonneg hce (mul_nonneg (by norm_num) hse)

end SquaresInCircles.Eight.TableFree.SoleECoefficients
