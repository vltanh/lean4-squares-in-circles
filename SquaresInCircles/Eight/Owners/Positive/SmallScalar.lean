module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.SecantGainPolynomial
public import SquaresInCircles.Eight.Words.Short.SecantGain

/-!
# Eight squares: strict convexity of the positive small-side scalar at the source circle

The middle point need only be contained in q;
it is not raised to that circle.  Consequently T can slightly exceed one.
The bounds T≤1.08 and 1−2VT/W≥4999/47875 still give F''≥3/50
on the complete feasible interval.  This allows the eventual alignment
to decrease the original A primary and retain every original circle loss.
-/

section
/-!
## The uniform common secant gain for actual negative primaries

The polynomial reserve is transferred through a proved
second-order radical bound to the original trigonometric gain. Monotonicity
then covers every actual q≤qCap and every coefficient at least .863.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveSecantGain
open GlobalGA PositiveStressCoefficients

/-- A positive-square proof of the second-order radical upper bound. -/
theorem sqrt_sub_upper {v u : ℝ} (hv : 0<v) (hu : 0≤u) (huv : u≤v^2) :
    Real.sqrt (v^2-u)≤v-u/(2*v)-u^2/(8*v^3) := by
  let m := v-u/(2*v)-u^2/(8*v^3)
  have hu2 := pow_le_pow_left₀ hu huv 2
  have hprod := mul_le_mul_of_nonneg_right huv (sq_nonneg v)
  have hmId : 8*v^3*m=8*v^4-4*u*v^2-u^2 := by
    dsimp [m]
    field_simp [hv.ne']
    ring
  have hm : 0< m := by
    have hv4 : 0<v^4 := pow_pos hv 4
    have hprodpos : 0<8*v^3*m := by nlinarith
    exact (mul_pos_iff_of_pos_left (by positivity : 0<8*v^3)).1 hprodpos
  have hid : m^2-(v^2-u)=u^3*(8*v^2+u)/(64*v^6) := by
    dsimp [m]
    field_simp [hv.ne']
    ring
  have hrest : 0≤u^3*(8*v^2+u)/(64*v^6) := by positivity
  have hsq := Real.sq_sqrt (sub_nonneg.mpr huv)
  have hs0 := Real.sqrt_nonneg (v^2-u)
  nlinarith

theorem coefficient_squares :
    qCap*(1+k^2)<(104551/40000 : ℝ)^2 ∧
      4*(111571/200000 : ℝ)^2*(1+k^2)<qCap*k^4 ∧
      64*(59531/1000000 : ℝ)^2*(1+k^2)^3<qCap*k^8 := by
  norm_num [qCap,k]

theorem radical_coefficients :
    Real.sqrt qCap*Real.sqrt (1+k^2)-1<64551/40000 ∧
      (111571/200000 : ℝ)<Real.sqrt qCap*k^2/(2*Real.sqrt (1+k^2)) ∧
      (59531/1000000 : ℝ)<Real.sqrt qCap*k^4/(8*(Real.sqrt (1+k^2))^3) := by
  have hR0 : 0<Real.sqrt qCap := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hV0 : 0<Real.sqrt (1+k^2) := Real.sqrt_pos.mpr (by positivity)
  have hR := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hV := Real.sq_sqrt (show 0≤1+k^2 by positivity)
  have h1 : (Real.sqrt qCap*Real.sqrt (1+k^2))^2=qCap*(1+k^2) := by rw [mul_pow,hR,hV]
  have h2 : (Real.sqrt qCap*k^2)^2=qCap*k^4 := by rw [mul_pow,hR]; ring
  have h3 : (Real.sqrt qCap*k^4)^2=qCap*k^8 := by rw [mul_pow,hR]; ring
  have hD2 : (2*Real.sqrt (1+k^2)*(111571/200000 : ℝ))^2=
      4*(111571/200000 : ℝ)^2*(1+k^2) := by
    nlinarith [hV]
  have hV6 : (Real.sqrt (1+k^2))^6=(1+k^2)^3 := by
    rw [show (Real.sqrt (1+k^2))^6=((Real.sqrt (1+k^2))^2)^3 by ring,hV]
  have hD3 : (8*(Real.sqrt (1+k^2))^3*(59531/1000000 : ℝ))^2=
      64*(59531/1000000 : ℝ)^2*(1+k^2)^3 := by
    calc
      _ = 64*(59531/1000000 : ℝ)^2*(Real.sqrt (1+k^2))^6 := by ring
      _ = _ := by rw [hV6]
  refine ⟨?_,?_,?_⟩
  · have hm := mul_pos hR0 hV0
    have := lt_of_pow_lt_pow_left₀ 2 (by norm_num)
      (show (Real.sqrt qCap*Real.sqrt (1+k^2))^2<(104551/40000 : ℝ)^2 by
        rw [h1]; exact coefficient_squares.1)
    linarith
  · apply (lt_div_iff₀ (by positivity : 0<2*Real.sqrt (1+k^2))).2
    have hm : 0≤Real.sqrt qCap*k^2 := by positivity
    have := lt_of_pow_lt_pow_left₀ 2 hm
      (show (2*Real.sqrt (1+k^2)*(111571/200000 : ℝ))^2<(Real.sqrt qCap*k^2)^2 by
        rw [hD2,h2]; exact coefficient_squares.2.1)
    linarith
  · apply (lt_div_iff₀ (by positivity : 0<8*(Real.sqrt (1+k^2))^3)).2
    have hm : 0≤Real.sqrt qCap*k^4 := by positivity
    have := lt_of_pow_lt_pow_left₀ 2 hm
      (show (8*(Real.sqrt (1+k^2))^3*(59531/1000000 : ℝ))^2<(Real.sqrt qCap*k^4)^2 by
        rw [hD3,h3]; exact coefficient_squares.2.2)
    linarith

theorem radical_gain_lower {s : ℝ} (_hs : s∈Icc 0 frameCap) :
    (111571/200000)*(Real.sin s)^2+(59531/1000000)*(Real.sin s)^4≤
      Real.sqrt qCap*(Real.sqrt (1+k^2)-Real.sqrt (gainRadicand k s)) := by
  have hV := Real.sq_sqrt (show 0≤1+k^2 by positivity)
  have hV0 : 0<Real.sqrt (1+k^2) := Real.sqrt_pos.mpr (by positivity)
  have hu : 0≤k^2*(Real.sin s)^2 := by positivity
  have hsin2 : (Real.sin s)^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.cos s)]
  have huv : k^2*(Real.sin s)^2≤(Real.sqrt (1+k^2))^2 := by
    have hm := mul_le_mul_of_nonneg_left hsin2 (sq_nonneg k)
    nlinarith
  have hsqrt := sqrt_sub_upper hV0 hu huv
  have he : (Real.sqrt (1+k^2))^2-k^2*(Real.sin s)^2=gainRadicand k s := by
    rw [hV]
    dsimp [gainRadicand]
    linear_combination (-k^2)*(Real.sin_sq_add_cos_sq s)
  rw [he] at hsqrt
  have hm := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg qCap)
  have h2 := mul_le_mul_of_nonneg_right radical_coefficients.2.1.le (sq_nonneg (Real.sin s))
  have h4 := mul_le_mul_of_nonneg_right radical_coefficients.2.2.le (by positivity : (0:ℝ)≤(Real.sin s)^4)
  have hid : Real.sqrt qCap*(k^2*(Real.sin s)^2/(2*Real.sqrt (1+k^2)))=
      (Real.sqrt qCap*k^2/(2*Real.sqrt (1+k^2)))*(Real.sin s)^2 := by ring
  have hid2 : Real.sqrt qCap*((k^2*(Real.sin s)^2)^2/(8*(Real.sqrt (1+k^2))^3))=
      (Real.sqrt qCap*k^4/(8*(Real.sqrt (1+k^2))^3))*(Real.sin s)^4 := by ring
  nlinarith [hid,hid2]

theorem base_strict_gain {s : ℝ} (hs : s∈Ioc 0 frameCap) :
    (103/100)*s<secantGain qCap k s := by
  obtain ⟨hc,hc1,hs0,hsu,hsc⟩ := transport_trig (Ioc_subset_Icc_self hs)
  have hcpos : 0<Real.cos s := by linarith
  have hrad := radical_gain_lower (Ioc_subset_Icc_self hs)
  have hcoeff := mul_le_mul_of_nonneg_right radical_coefficients.1.le (sub_nonneg.mpr hc1)
  have htrig := SecantGainPolynomial.trigonometric_positive hs
  have hid : (secantGain qCap k s-(103/100)*s)*Real.cos s=
      (13/12)*Real.sin s-(103/100)*s*Real.cos s-
        (Real.sqrt qCap*Real.sqrt (1+k^2)-1)*(1-Real.cos s)+
          Real.sqrt qCap*(Real.sqrt (1+k^2)-Real.sqrt (gainRadicand k s)) := by
    dsimp [secantGain]
    field_simp [hcpos.ne']
    ring
  have hp : 0<(secantGain qCap k s-(103/100)*s)*Real.cos s := by rw [hid]; linarith
  have := (mul_pos_iff_of_pos_right hcpos).1 hp
  linarith

theorem norm_increment_antitone {a b w : ℝ} (ha : 0≤a) (hab : a≤b) (hw : 1≤w) :
    Real.sqrt (w^2+b^2)-Real.sqrt (1+b^2)≤
      Real.sqrt (w^2+a^2)-Real.sqrt (1+a^2) := by
  have hb : 0≤b := ha.trans hab
  have hab2 := pow_le_pow_left₀ ha hab 2
  have hw2 : 1≤w^2 := by nlinarith
  have hA := Real.sq_sqrt (show 0≤w^2+a^2 by positivity)
  have hB := Real.sq_sqrt (show 0≤1+a^2 by positivity)
  have hC := Real.sq_sqrt (show 0≤w^2+b^2 by positivity)
  have hD := Real.sq_sqrt (show 0≤1+b^2 by positivity)
  have hAB := Real.sqrt_le_sqrt (show 1+a^2≤w^2+a^2 by linarith)
  have hAC := Real.sqrt_le_sqrt (show w^2+a^2≤w^2+b^2 by linarith)
  have hBD := Real.sqrt_le_sqrt (show 1+a^2≤1+b^2 by linarith)
  have hsum := add_le_add hAC hBD
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hAB)
  have hden : 0<Real.sqrt (w^2+b^2)+Real.sqrt (1+b^2) := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  nlinarith

/-- Smaller original radii and larger force coefficients only increase
the secant gain. -/
theorem gain_comparison {q a s : ℝ} (_hq : 0≤q) (hQ : q≤qCap)
    (ha : k≤a) (hs : s∈Icc 0 frameCap) :
    secantGain qCap k s≤ secantGain q a s := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hcu := Real.cos_le_one s
  have hw : 1≤1/Real.cos s := (le_div_iff₀ hc).2 (by simpa using hcu)
  have hn := norm_increment_antitone (show 0≤k by norm_num [k]) ha hw
  have hR := Real.sqrt_le_sqrt hQ
  have ha0 : 0≤a := (show 0≤k by norm_num [k]).trans ha
  have hdelta : 0≤Real.sqrt ((1/Real.cos s)^2+a^2)-Real.sqrt (1+a^2) := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    nlinarith
  have hprod := mul_le_mul hR hn hdelta (Real.sqrt_nonneg qCap)
  rw [secantGain_eq_secant_expression qCap k hc,secantGain_eq_secant_expression q a hc]
  nlinarith

theorem strict_gain {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : k≤a) (hs : s∈Ioc 0 frameCap) :
    (103/100)*s<secantGain q a s :=
  (base_strict_gain hs).trans_le (gain_comparison hq hQ ha (Ioc_subset_Icc_self hs))

theorem negative_TD_gain {q d t : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (hd : d∈Icc 0 frameCap) (ht : t∈Ioc 0 frameCap) :
    lambdaN d*t<cN d*secantGain q (1/cN d) t := by
  have hc0 : 0<cN d := by
    have hh := coefficient_bounds hd
    dsimp [cN,frameCap] at *
    nlinarith [hd.1,hd.2]
  have hcoeff := ShortSecantGain.negative_family_slopes hd
  have hg := mul_lt_mul_of_pos_left (strict_gain hq hQ hcoeff.2.2.2.1.le ht) hc0
  have hl := mul_lt_mul_of_pos_right hcoeff.2.1 ht.1
  nlinarith

end SquaresInCircles.Eight.PositiveSecantGain
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveSmallScalar

def V (P Y z : ℝ) : ℝ := P*Real.cos z-Y*Real.sin z
def U (P Y z : ℝ) : ℝ := P*Real.sin z+Y*Real.cos z
def W (q P Y z : ℝ) : ℝ := Real.sqrt (q-(V P Y z)^2)
def T (q P Y z : ℝ) : ℝ := W q P Y z-U P Y z
def T1 (q P Y z : ℝ) : ℝ := -V P Y z*T q P Y z/W q P Y z
def T2 (q P Y z : ℝ) : ℝ :=
  T q P Y z*(q*U P Y z+(V P Y z)^2*W q P Y z)/(W q P Y z)^3
def F (q P Y Θ h : ℝ) : ℝ :=
  Real.sin h*(T q P Y (Θ+h)-1)+1-Real.cos h
def F1 (q P Y Θ h : ℝ) : ℝ :=
  Real.cos h*(T q P Y (Θ+h)-1)+Real.sin h*(T1 q P Y (Θ+h)+1)
def F2 (q P Y Θ h : ℝ) : ℝ :=
  Real.cos h*(1+2*T1 q P Y (Θ+h))+
    Real.sin h*(1-T q P Y (Θ+h)+T2 q P Y (Θ+h))

structure CapData (q P Y : ℝ) : Prop where
  P_mem : P∈Icc (1/2 : ℝ) (397/500)
  Y_mem : Y∈Icc (167/200 : ℝ) 1
  circle : (P+1)^2+Y^2≤q
  ceiling : q≤qCap

theorem rotation_identity (P Y z : ℝ) :
    (V P Y z)^2+(U P Y z)^2=P^2+Y^2 := by
  dsimp [V,U]
  linear_combination (P^2+Y^2)*(Real.sin_sq_add_cos_sq z)

theorem inverse_identity (P Y Θ h : ℝ) :
    V P Y Θ=Real.cos h*V P Y (Θ+h)+Real.sin h*U P Y (Θ+h) := by
  have hc := Real.cos_sub (Θ+h) h
  have hs := Real.sin_sub (Θ+h) h
  rw [show Θ+h-h=Θ by ring] at hc hs
  dsimp [V,U]
  rw [hc,hs]
  ring

theorem V_hasDerivAt (P Y z : ℝ) : HasDerivAt (V P Y) (-U P Y z) z := by
  have h := ((Real.hasDerivAt_cos z).const_mul P).sub ((Real.hasDerivAt_sin z).const_mul Y)
  have hf : V P Y=fun x => P*Real.cos x-Y*Real.sin x := rfl
  rw [hf]
  exact h.congr_deriv (by simp only [U]; ring)

theorem U_hasDerivAt (P Y z : ℝ) : HasDerivAt (U P Y) (V P Y z) z := by
  have h := ((Real.hasDerivAt_sin z).const_mul P).add ((Real.hasDerivAt_cos z).const_mul Y)
  have hf : U P Y=fun x => P*Real.sin x+Y*Real.cos x := rfl
  rw [hf]
  exact h.congr_deriv (by simp only [V]; ring)

theorem W_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(V P Y z)^2) :
    HasDerivAt (W q P Y) (V P Y z*U P Y z/W q P Y z) z := by
  have hw : W q P Y z≠0 := (Real.sqrt_pos.2 hr).ne'
  have hh := (((V_hasDerivAt P Y z).pow 2).const_sub q).sqrt hr.ne'
  have hf : W q P Y=fun x => Real.sqrt (q-(V P Y x)^2) := rfl
  rw [hf]
  refine hh.congr_deriv ?_
  dsimp [W] at hw ⊢
  field_simp

theorem T_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(V P Y z)^2) :
    HasDerivAt (T q P Y) (T1 q P Y z) z := by
  have hw : W q P Y z≠0 := (Real.sqrt_pos.2 hr).ne'
  convert (W_hasDerivAt hr).sub (U_hasDerivAt P Y z) using 1
  · rfl
  · dsimp [T1,T]
    field_simp [hw]
    ring

theorem T1_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(V P Y z)^2) :
    HasDerivAt (T1 q P Y) (T2 q P Y z) z := by
  have hw : W q P Y z≠0 := (Real.sqrt_pos.2 hr).ne'
  have hw2 : (W q P Y z)^2=q-(V P Y z)^2 := Real.sq_sqrt hr.le
  have hh := (((V_hasDerivAt P Y z).neg).mul (T_hasDerivAt hr)).div
    (W_hasDerivAt hr) hw
  convert hh using 1
  · rfl
  · dsimp [T2,T1]
    field_simp [hw]
    nlinarith [congrArg (fun r : ℝ => T q P Y z*U P Y z*r) hw2]

theorem F_hasDerivAt {q P Y Θ h : ℝ} (hr : 0<q-(V P Y (Θ+h))^2) :
    HasDerivAt (F q P Y Θ) (F1 q P Y Θ h) h := by
  have hlin : HasDerivAt (fun x : ℝ => Θ+x) 1 h := (hasDerivAt_id' h).const_add Θ
  have ht0 := (T_hasDerivAt hr).comp h hlin
  have ht : HasDerivAt (fun x => T q P Y (Θ+x)) (T1 q P Y (Θ+h)*1) h := ht0
  have hF := (((Real.hasDerivAt_sin h).mul (ht.sub_const 1)).add_const 1).sub
    (Real.hasDerivAt_cos h)
  exact hF.congr_deriv (by simp only [F1]; ring)

theorem F1_hasDerivAt {q P Y Θ h : ℝ} (hr : 0<q-(V P Y (Θ+h))^2) :
    HasDerivAt (F1 q P Y Θ) (F2 q P Y Θ h) h := by
  have hlin : HasDerivAt (fun x : ℝ => Θ+x) 1 h := (hasDerivAt_id' h).const_add Θ
  have ht0 := (T_hasDerivAt hr).comp h hlin
  have ht : HasDerivAt (fun x => T q P Y (Θ+x)) (T1 q P Y (Θ+h)*1) h := ht0
  have ht10 := (T1_hasDerivAt hr).comp h hlin
  have ht1 : HasDerivAt (fun x => T1 q P Y (Θ+x)) (T2 q P Y (Θ+h)*1) h := ht10
  have hF := ((Real.hasDerivAt_cos h).mul (ht.sub_const 1)).add
    ((Real.hasDerivAt_sin h).mul (ht1.add_const 1))
  exact hF.congr_deriv (by simp only [F2]; ring)

theorem V_upper {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) : V P Y z≤P := by
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one z)
    (show 0≤P by linarith [I.P_mem.1])
  have hs := mul_nonneg (show 0≤Y by linarith [I.Y_mem.1]) (transport_trig hz).2.2.1
  dsimp [V]
  linarith

theorem V_antitone {q P Y : ℝ} (I : CapData q P Y) :
    AntitoneOn (V P Y) (Icc 0 frameCap) := by
  intro x hx y hy hxy
  have hc := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.cos_anti hx hy hxy)
    (show 0≤P by linarith [I.P_mem.1])
  have hs := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.sin_mono hx hy hxy)
    (show 0≤Y by linarith [I.Y_mem.1])
  dsimp [V]
  linarith

theorem contact_angle_short {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : z<2/5 := by
  by_contra! hlong
  have hs := CorrelatedSameBlock.sin_mono
    (show (2/5 : ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hlong
  have hsin : 19/50<Real.sin z := by
    have hh := Real.sin_ge_sub_cube (show (0:ℝ)≤2/5 by norm_num)
    norm_num at hh
    linarith
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one z)
    (show 0≤P by linarith [I.P_mem.1])
  have hsy := mul_le_mul_of_nonneg_right I.Y_mem.1 (transport_trig hz).2.2.1
  dsimp [V] at hV
  nlinarith [I.P_mem.2]

structure PointBounds (q P Y z : ℝ) : Prop where
  radicand_pos : 0<q-(V P Y z)^2
  W_pos : 0<W q P Y z
  T_pos : 0<T q P Y z
  T_upper : T q P Y z≤27/25
  coefficient_lower : 4999/47875≤1+2*T1 q P Y z
  T2_nonneg : 0≤T2 q P Y z

theorem point_bounds {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : PointBounds q P Y z := by
  have ht := transport_trig hz
  have hU0 : 0≤U P Y z := by
    dsimp [U]
    exact add_nonneg (mul_nonneg (by linarith [I.P_mem.1]) ht.2.2.1)
      (mul_nonneg (by linarith [I.Y_mem.1]) (by linarith [ht.1]))
  have hVU := rotation_identity P Y z
  have hVp := V_upper I hz
  have hVp2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hVp 2
  have hUY : Y≤U P Y z := by nlinarith [I.Y_mem.1]
  have hr : 0<q-(V P Y z)^2 := by nlinarith [I.circle,I.P_mem.1,sq_nonneg (U P Y z)]
  have hw : 0<W q P Y z := Real.sqrt_pos.2 hr
  have hw2 : (W q P Y z)^2=q-(V P Y z)^2 := Real.sq_sqrt hr.le
  have hUw : U P Y z<W q P Y z := by nlinarith [I.circle,I.P_mem.1]
  have hT : 0<T q P Y z := sub_pos.mpr hUw
  have hwu : W q P Y z<383/200 := by
    have hV2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num) hV 2
    have hq := I.ceiling
    dsimp [qCap] at hq
    nlinarith
  have hTu : T q P Y z≤27/25 := by dsimp [T]; linarith [I.Y_mem.1]
  have hTw : T q P Y z≤(216/383)*W q P Y z := by
    dsimp [T]
    linarith [I.Y_mem.1]
  have hVT := mul_le_mul (hVp.trans I.P_mem.2) hTw hT.le (by norm_num : (0:ℝ)≤397/500)
  have hratio : V P Y z*T q P Y z/W q P Y z≤(397/500)*(216/383) := by
    apply (div_le_iff₀ hw).2
    nlinarith
  have hcoef : 4999/47875≤1+2*T1 q P Y z := by
    have he : T1 q P Y z=-(V P Y z*T q P Y z/W q P Y z) := by dsimp [T1]; ring
    rw [he]
    linarith
  have hq0 : 0≤q := by nlinarith [I.circle,sq_nonneg (P+1),sq_nonneg Y]
  have hT2 : 0≤T2 q P Y z := by
    dsimp [T2]
    exact div_nonneg (mul_nonneg hT.le
      (add_nonneg (mul_nonneg hq0 hU0) (mul_nonneg (sq_nonneg _) hw.le)))
      (pow_nonneg hw.le 3)
  exact ⟨hr,hw,hT,hTu,hcoef,hT2⟩

/-- A strictly positive uniform curvature remains even without lifting A
to its containing circle.  The small negative part 1−T costs at most .032. -/
theorem curvature_lower {q P Y Θ h : ℝ} (I : CapData q P Y)
    (hh : h∈Icc 0 (2/5 : ℝ)) (hz : Θ+h∈Icc 0 frameCap)
    (hV : 1/2≤V P Y (Θ+h)) : 3/50≤F2 q P Y Θ h := by
  have B := point_bounds I hz hV
  have ht : h∈Icc 0 frameCap := by dsimp [frameCap]; exact ⟨hh.1,by linarith [hh.2]⟩
  have hsin : 0≤Real.sin h := (transport_trig ht).2.2.1
  have hs : Real.sin h≤2/5 := (Real.sin_le hh.1).trans hh.2
  have hc : 23/25≤Real.cos h := by
    have h2 := pow_le_pow_left₀ hh.1 hh.2 2
    norm_num at h2
    linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
  have hm := mul_le_mul hc B.coefficient_lower
    (by norm_num : (0:ℝ)≤4999/47875) (by linarith : 0≤Real.cos h)
  have hn := mul_le_mul_of_nonneg_left
    (show -(2/25 : ℝ)≤1-T q P Y (Θ+h)+T2 q P Y (Θ+h) by
      linarith [B.T_upper,B.T2_nonneg]) hsin
  dsimp [F2]
  nlinarith

/-- The end of the entire feasible hard-angle interval is obtained by
the intermediate value theorem.  Its sole defining contact is V=1/2. -/
theorem contact_endpoint {q P Y z : ℝ} (I : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) :
    ∃ Z, z≤Z ∧ Z<2/5 ∧ V P Y Z=1/2 ∧
      ∀ x∈Icc 0 Z,1/2≤V P Y x := by
  have hzshort := contact_angle_short I hz hV
  have hright : V P Y (2/5)<1/2 := by
    by_contra! hbad
    exact (lt_irrefl (2/5 : ℝ)) (contact_angle_short I
      (by norm_num [frameCap]) hbad)
  obtain ⟨Z,hZ,heq⟩ := intermediate_value_Icc hzshort.le
    (show ContinuousOn (fun x => -V P Y x) (Icc z (2/5)) by unfold V; fun_prop)
    (show -(1/2 : ℝ)∈Icc (-V P Y z) (-V P Y (2/5)) by constructor <;> linarith)
  have hZE : V P Y Z=1/2 := by linarith
  have hZu : Z<2/5 := by
    apply lt_of_le_of_ne hZ.2
    intro he
    rw [he] at hZE
    linarith
  refine ⟨Z,hZ.1,hZu,hZE,?_⟩
  intro x hx
  have hZi : Z∈Icc 0 frameCap := by
    dsimp [frameCap]
    exact ⟨by linarith [hz.1,hZ.1],by linarith⟩
  have hxi : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hZi.2⟩
  simpa only [hZE] using V_antitone I hxi hZi hx.2

end SquaresInCircles.Eight.PositiveSmallScalar
end
end
end
