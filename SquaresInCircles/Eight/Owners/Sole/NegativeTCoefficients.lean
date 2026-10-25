module

public import SquaresInCircles.Eight.Owners.Sole.NegativeTSplit
public import SquaresInCircles.Eight.Owners.Sole.PositiveTOrdinaryData

/-!
# Eight squares: coefficient domains after a negative T primary

The four unchanged pairs use the sole-E families at `z = 0` (`oldV`, `old_cap`). Only the negative
BT row uses its secant at `9/100` in a positive ordinary coefficient (`changed_B_domain`,
`changed_B_cost`); the weaker scalar enlargement to `3/10` never bounds that changed pair. The gain
slope `21/20` of the negative primary exceeds every such cost (`gain_exceeds_cost`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTCoefficients
open SoleTScalarModel SolePositiveTOrdinaryData SolePositiveTCoefficients
open PositiveAngularEnvelope SingleAngleConcavity

def face (f : Family) (atG : Bool) : ScalarCase := ⟨f,true,atG,0⟩
def first (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  SoleTScalarModel.first (face f atG) t 0 i
def second (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  SoleTScalarModel.second (face f atG) t 0 i
def small (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  min (first f atG t i) (second f atG t i)
def large (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  max (first f atG t i) (second f atG t i)
def nu (f : Family) (atG : Bool) (t : ℝ) : Fin 4 → ℝ :=
  ![if isDE f then lambda f else n (face f atG) t 0,
    ell f t 0,c f t 0,max (p (face f atG) t 0) (c f t 0)]
def oldV (f : Family) (atG : Bool) (R t v : ℝ) (i : Fin 4) : ℝ :=
  Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) v
def single (f : Family) (td : Bool) : Fin 4 → Bool := ![!isDE f,true,!td,true]
def gamma : Family → ℝ
  | .ehLow => 2289/4000
  | .ehMiddle => 76/125
  | .ehHigh => 619/1000
  | .deLow | .deHigh => 109/160

theorem zero_mem {f : Family} {t : ℝ} (ht : t∈domain f) : (0:ℝ)∈Icc 0 t :=
  ⟨le_rfl,(angle ht).1⟩

theorem pairs (f : Family) (atG : Bool) (t : ℝ) :
    first f atG t=![lambda f,k f t 0,ell f t 0,p (face f atG) t 0] ∧
    second f atG t=![n (face f atG) t 0,ell f t 0,c f t 0,c f t 0] := by
  have hm : m (face f atG) t 0=c f t 0 := by simp [m,face]
  refine ⟨rfl,?_⟩
  show ![n (face f atG) t 0,ell f t 0,m (face f atG) t 0,c f t 0]=_
  rw [hm]

theorem positive {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) (i : Fin 4) :
    0<first f atG t i ∧ 0<second f atG t i ∧ 0<small f atG t i := by
  have hh := weights_positive (face f atG) ht (zero_mem ht)
  exact ⟨hh.2.2.2.1 i,hh.2.2.2.2 i,lt_min (hh.2.2.2.1 i) (hh.2.2.2.2 i)⟩

theorem half_ratio {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) (i : Fin 4) :
    large f atG t i≤2*small f atG t i :=
  SolePositiveTCoefficients.half_ratio (face f atG) ht (zero_mem ht) i

theorem old_cap {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) (i : Fin 4) :
    large f atG t i≤(SolePositiveTCoefficients.cap f:ℝ) :=
  pair_upper (face f atG) ht (zero_mem ht) i

theorem nu_between (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) :
    small f atG t i≤nu f atG t i ∧ nu f atG t i≤large f atG t i := by
  fin_cases i <;> cases f <;>
    simp [nu,small,large,first,second,face,SoleTScalarModel.first,SoleTScalarModel.second,
      lambda,isDE,m]

theorem c_ge_ell {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    ell f t 0≤c f t 0 := by
  simpa [face,m] using m_ge_ell (face f atG) ht (zero_mem ht)

theorem B_ratio {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    (117/200)*c f t 0≤ell f t 0 := by
  have hh := ratio_lower (face f atG) ht (zero_mem ht) 2
  have he := c_ge_ell atG ht
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have ht0 := (angle ht).1
  have hm : m (face f atG) t 0=c f t 0 := by simp [m,face]
  have h1 : SoleTScalarModel.first (face f atG) t 0 2=ell f t 0 := rfl
  have h2 : SoleTScalarModel.second (face f atG) t 0 2=c f t 0 := hm
  rw [h1,h2,max_eq_right he,min_eq_left he] at hh
  have hr : (117/200:ℝ)≤ratio (face f atG).family t 2 := by
    show (117/200:ℝ)≤ratio f t 2
    cases f <;> norm_num [ratio] <;> linarith
  have hp := mul_le_mul_of_nonneg_right hr hc.le
  linarith

theorem p_half_c {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    p (face f atG) t 0≤2*c f t 0 := by
  have hh := half_ratio atG ht 3
  have hlo := le_max_left (p (face f atG) t 0) (c f t 0)
  have hhi := min_le_right (p (face f atG) t 0) (c f t 0)
  change max (p (face f atG) t 0) (c f t 0)≤
    2*min (p (face f atG) t 0) (c f t 0) at hh
  linarith

theorem tilt_ge_one {e ε : ℝ} (he : e∈Icc 0 (7/20:ℝ)) (hε : 1/4≤ε) :
    1≤Real.cos e+ε*Real.sin e := by
  have he' : e∈Icc 0 frameCap := ⟨he.1,by norm_num [frameCap]; linarith [he.2]⟩
  have hsin := (transport_trig he').2.2.1
  have hm := mul_le_mul_of_nonneg_right hε hsin
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hs := Real.sin_ge_sub_cube he.1
  have he2 : e^2≤(7/20)*e := by nlinarith [he.1,he.2]
  have he3 : e^3≤(49/400)*e := by
    have hh := mul_le_mul_of_nonneg_right he2 he.1
    nlinarith
  linarith

theorem p_ge_one {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    1≤p (face f atG) t 0 := by
  have hb := SolePositiveTSplitModel.bounds ht (zero_mem ht)
  by_cases he : tiltedE f=true
  · have hlen : t≤7/20 := by simpa only [sub_zero] using hb.tilted_length he
    have ht' : t∈Icc 0 (7/20:ℝ) := ⟨(angle ht).1,hlen⟩
    have he' : SoleTScalarModel.e (face f atG) t 0∈Icc 0 (7/20:ℝ) := by
      cases atG
      · simpa [SoleTScalarModel.e,face] using ht'
      · norm_num [SoleTScalarModel.e,face]
    have hh := tilt_ge_one he' (hb.tilted_epsilon he).1
    show 1≤(if tiltedE f then Real.cos (SoleTScalarModel.e (face f atG) t 0)+
      epsilon f t*Real.sin (SoleTScalarModel.e (face f atG) t 0) else 1)
    simp only [he,↓reduceIte]
    exact hh
  · show 1≤(if tiltedE f then Real.cos (SoleTScalarModel.e (face f atG) t 0)+
      epsilon f t*Real.sin (SoleTScalarModel.e (face f atG) t 0) else 1)
    have he' : tiltedE f=false := by simpa using he
    simp only [he',Bool.false_eq_true,↓reduceIte,le_refl]

theorem EH_A_bounds {f : Family} (hEH : isDE f=false) {t : ℝ}
    (ht : t∈domain f) : k f t 0+ell f t 0≤2 ∧ 11*k f t 0+ell f t 0≤12 := by
  have ht' := angle ht
  cases f <;> norm_num [isDE] at hEH <;>
    norm_num [domain,left,right] at ht <;> dsimp [k,ell,K,L] <;>
    constructor <;> nlinarith [ht.1,ht.2,sq_nonneg t,sq_nonneg (t-1/5),
      mul_nonneg (show 0≤t by linarith [ht'.1])
        (show 0≤7/10-t by linarith [ht'.2])]

theorem middle_base {t : ℝ} (ht : t∈domain .ehMiddle) :
    983/1000≤k .ehMiddle t 0 ∧ 209/200≤c .ehMiddle t 0 ∧
      ell .ehMiddle t 0≤k .ehMiddle t 0 ∧
      (2/3)*k .ehMiddle t 0≤ell .ehMiddle t 0 ∧
      (2/3)*c .ehMiddle t 0≤ell .ehMiddle t 0 := by
  have hw : t-1/5∈Icc 0 (3/20:ℝ) := by
    norm_num [domain,left,right] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hw2 : (t-1/5)^2≤(3/20)*(t-1/5) := by nlinarith [hw.1,hw.2]
  dsimp [k,ell,c,K,L,C]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [hw.1,hw.2,sq_nonneg (t-1/5)]

theorem middle_sorted (atG : Bool) {t : ℝ} (ht : t∈domain .ehMiddle) :
    p (face .ehMiddle atG) t 0≤c .ehMiddle t 0 ∧
      p (face .ehMiddle atG) t 0≤53/50 := by
  have ht' : t∈Icc (1/5:ℝ) (7/20) := by
    have h := ht
    norm_num [domain,left,right] at h
    exact h
  have hε : epsilon .ehMiddle t∈Icc 0 (349/1000:ℝ) := by
    dsimp [epsilon]
    constructor <;> linarith [ht'.1,ht'.2]
  have hp0 := (weights_positive (face .ehMiddle atG) ht (zero_mem ht)).2.2.1
  have hpdef : p (face .ehMiddle atG) t 0=Real.cos (SoleTScalarModel.e (face .ehMiddle atG) t 0)+
      epsilon .ehMiddle t*Real.sin (SoleTScalarModel.e (face .ehMiddle atG) t 0) := by
    simp [p,face,tiltedE]
  have hpSquare : (p (face .ehMiddle atG) t 0)^2≤1+(epsilon .ehMiddle t)^2 := by
    have hh := sq_nonneg (epsilon .ehMiddle t*Real.cos (SoleTScalarModel.e (face .ehMiddle atG) t 0)-
      Real.sin (SoleTScalarModel.e (face .ehMiddle atG) t 0))
    have htrig := Real.sin_sq_add_cos_sq (SoleTScalarModel.e (face .ehMiddle atG) t 0)
    rw [hpdef]
    nlinarith
  have hpUpper : p (face .ehMiddle atG) t 0≤53/50 := by
    have hε2 := pow_le_pow_left₀ hε.1 hε.2 2
    nlinarith
  refine ⟨?_,hpUpper⟩
  rw [hpdef]
  cases atG
  · have hc := cos_upper_four (show 0≤t by linarith [ht'.1])
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le (by linarith [ht'.1] : 0≤t)) hε.1
    have ht2 : t^2≤49/400 := by nlinarith [ht'.1,ht'.2]
    have ht4 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)
    have hinterval := mul_nonneg (sub_nonneg.mpr ht'.1) (sub_nonneg.mpr ht'.2)
    have hev : SoleTScalarModel.e (face .ehMiddle false) t 0=t := by simp [SoleTScalarModel.e,face]
    rw [hev]
    dsimp [c,C,epsilon]
    dsimp [epsilon] at hs
    nlinarith
  · have hc := (middle_base ht).2.1
    have hev : SoleTScalarModel.e (face .ehMiddle true) t 0=0 := by simp [SoleTScalarModel.e,face]
    rw [hev]
    simp only [Real.cos_zero,Real.sin_zero,mul_zero,add_zero]
    linarith

theorem correction_domain {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) (hf : f=.ehMiddle ∨ f=.ehHigh) :
    p (face f atG) t 0≤c f t 0 ∧
      Real.sqrt ((p (face f atG) t 0)^2+(c f t 0)^2)≤307/200 := by
  have hp0 := (weights_positive (face f atG) ht (zero_mem ht)).2.2.1
  have hc0 := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hroot : (307/200:ℝ)=Real.sqrt ((307/200)^2) := by
    rw [Real.sqrt_sq]; norm_num
  rcases hf with rfl | rfl
  · have hp := middle_sorted atG ht
    have hh := old_cap atG ht 3
    have hmax := le_max_right (p (face .ehMiddle atG) t 0) (c .ehMiddle t 0)
    have hpr := pairs .ehMiddle atG t
    simp only [large,hpr.1,hpr.2] at hh
    have hcap' : (cap .ehMiddle:ℝ)=111/100 := by norm_num [cap]
    rw [hcap'] at hh
    have hh' : max (p (face .ehMiddle atG) t 0) (c .ehMiddle t 0)≤111/100 := hh
    have hc : c .ehMiddle t 0≤111/100 := hmax.trans hh'
    have hp2 := pow_le_pow_left₀ hp0.le hp.2 2
    have hc2 := pow_le_pow_left₀ hc0.le hc 2
    refine ⟨hp.1,?_⟩
    rw [hroot]
    exact Real.sqrt_le_sqrt (by linarith)
  · have hpv : p (face .ehHigh atG) t 0=1 := by simp [p,face,tiltedE]
    have hcv : c .ehHigh t 0=113/100 := by simp [c,C]
    rw [hpv,hcv,hroot]
    exact ⟨by norm_num,Real.sqrt_le_sqrt (by norm_num)⟩

theorem secant_upper {s : ℝ} (hs : s∈Icc 0 (9/100:ℝ)) :
    1/Real.cos s≤20000/19919 := by
  have hs2 : s^2≤81/10000 := by nlinarith [hs.1,hs.2]
  have hc : (19919/20000:ℝ)≤Real.cos s := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hcp : 0<Real.cos s := by linarith
  apply (div_le_iff₀ hcp).2
  linarith

theorem changed_B_domain {f : Family} (atG : Bool) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈Icc 0 (9/100:ℝ)) :
    0<ell f t 0 ∧ ell f t 0≤c f t 0/Real.cos s ∧
      c f t 0/Real.cos s≤2*ell f t 0 := by
  obtain ⟨hk,hl,hc,_,_,_⟩ := coefficient_positive ht (zero_mem ht)
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hsec := SoleNegativeTSplit.secant_nonneg hs'
  have he : c f t 0/Real.cos s=c f t 0*(1/Real.cos s) := by ring
  have hcsec : c f t 0≤c f t 0/Real.cos s := by
    have hh := mul_nonneg hc.le hsec.2
    rw [he]
    linarith
  have hu := mul_le_mul_of_nonneg_left (secant_upper hs) hc.le
  have hr := B_ratio atG ht
  exact ⟨hl,(c_ge_ell atG ht).trans hcsec,by rw [he]; linarith⟩

theorem gain_exceeds_cost {f : Family} {t : ℝ} (ht : t∈domain f) :
    gamma f<(21/20)*c f t 0 := by
  cases f <;> norm_num [domain,left,right] at ht <;> dsimp [gamma,c,C,K] <;>
    nlinarith [ht.1,ht.2,sq_nonneg t,sq_nonneg (t-1/5),
      mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

def cUpper : Family → ℝ
  | .ehLow => 209/200
  | .ehMiddle => 111/100
  | .ehHigh | .deHigh => 113/100
  | .deLow => 1131/1000

theorem c_upper {f : Family} {t : ℝ} (ht : t∈domain f) : c f t 0≤cUpper f := by
  cases f <;> norm_num [domain,left,right] at ht <;> dsimp [cUpper,c,C,K] <;>
    nlinarith [ht.1,ht.2,sq_nonneg t,sq_nonneg (t-1/5),
      mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

theorem old_cost {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) : (109/200)*large f atG t i≤gamma f := by
  have hh := mul_le_mul_of_nonneg_left (old_cap atG ht i)
    (by norm_num : (0:ℝ)≤109/200)
  cases f <;> norm_num [cap,gamma] at hh ⊢ <;> linarith

theorem changed_B_cost {f : Family} {t s : ℝ}
    (ht : t∈domain f) (hs : s∈Icc 0 (9/100:ℝ)) :
    (109/200)*(c f t 0/Real.cos s)≤gamma f := by
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcU := c_upper ht
  have hu := mul_le_mul hcU (secant_upper hs)
    (SoleNegativeTSplit.secant_nonneg hs').1.le
    (show 0≤cUpper f by cases f <;> norm_num [cUpper])
  have he : c f t 0*(1/Real.cos s)=c f t 0/Real.cos s := by ring
  rw [he] at hu
  cases f <;> norm_num [cUpper,gamma] at hu ⊢ <;> linarith

theorem D_linear_cost {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) : (2/5)*p (face f atG) t 0≤gamma f := by
  have hh := old_cap atG ht 3
  have hp := le_max_left (p (face f atG) t 0) (c f t 0)
  change max (p (face f atG) t 0) (c f t 0)≤(cap f:ℝ) at hh
  have hpu : p (face f atG) t 0≤(cap f:ℝ) := hp.trans hh
  cases f <;> norm_num [cap,gamma] at hpu ⊢ <;> linarith

theorem D_full_cost {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) : (109/200)*p (face f atG) t 0≤gamma f := by
  have hh := old_cost atG ht 3
  have hp := mul_le_mul_of_nonneg_left
    (le_max_left (p (face f atG) t 0) (c f t 0))
    (by norm_num : (0:ℝ)≤109/200)
  change (109/200)*max (p (face f atG) t 0) (c f t 0)≤gamma f at hh
  exact hp.trans hh

end SquaresInCircles.Eight.SoleNegativeTCoefficients
