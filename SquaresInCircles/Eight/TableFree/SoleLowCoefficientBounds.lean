module

public import SquaresInCircles.Eight.TableFree.SoleLowChargeBounds

/-!
# Low-family coefficients at every original split

Uncompiled source. The two split coordinates range independently over
[0,t]; imposing x+e=t later only narrows this domain. In particular the
E coefficient in the sole-DE stress is allowed up to 28/25. None of
these inequalities changes an original point or replaces its radius.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleLowCoefficientBounds
open SoleECoefficients SoleLowChargeBounds SecondaryEStress

theorem tilted_mono {a : ℝ} (ha : a∈Icc (1/4 : ℝ) (7/10)) :
    MonotoneOn (fun s => Real.cos s+a*Real.sin s) (Icc (0:ℝ) (1/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · intro s _
    exact (Real.hasDerivAt_cos s).add ((Real.hasDerivAt_sin s).const_mul a)
  · intro s hs
    have hs' := Ioo_subset_Icc_self hs
    have hc : (49/50 : ℝ)≤Real.cos s := by linarith [(short_trig hs').2,hs'.2]
    have hsin := Real.sin_le hs'.1
    have hm := mul_le_mul ha.1 hc (by norm_num : (0:ℝ)≤49/50)
      (show 0≤a by linarith [ha.1])
    nlinarith [hs'.2]

theorem tilted_lower {a s : ℝ} (ha : a∈Icc (1/4 : ℝ) (7/10))
    (hs : s∈Icc 0 (1/5 : ℝ)) : 1≤Real.cos s+a*Real.sin s := by
  have hm := tilted_mono ha (show (0:ℝ)∈Icc 0 (1/5 : ℝ) by norm_num) hs hs.1
  simpa using hm

theorem tilted_upper {a s : ℝ} (ha : a∈Icc 0 (8/25 : ℝ)) :
    Real.cos s+a*Real.sin s<21/20 := by
  have hid : (Real.cos s+a*Real.sin s)^2+(Real.sin s-a*Real.cos s)^2=
      (1+a^2)*((Real.sin s)^2+(Real.cos s)^2) := by ring
  rw [Real.sin_sq_add_cos_sq] at hid
  have ha2 : a^2≤(8/25 : ℝ)^2 := by nlinarith [ha.1,ha.2]
  nlinarith [sq_nonneg (Real.sin s-a*Real.cos s)]

theorem split_bounds {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    k .low t≤n .low t x ∧ n .low t x<21/20 ∧
    1≤p .low t e ∧ p .low t e<21/20 ∧
    1≤r .low e ∧ r .low e<28/25 := by
  have hx' : x∈Icc 0 (1/5 : ℝ) := ⟨hx.1,hx.2.trans ht.2⟩
  have he' : e∈Icc 0 (1/5 : ℝ) := ⟨he.1,he.2.trans ht.2⟩
  have hp := positive ht
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hnlo := mul_le_mul_of_nonneg_left
    (tilted_lower (a := 8/25) (by norm_num) hx') hp.1.le
  have hnhi := mul_lt_mul_of_pos_left
    (tilted_upper (a := 8/25) (s := x) (by norm_num)) hp.1
  have hplo := tilted_lower (a := eta .low t) (by constructor <;> linarith) he'
  have hphi := tilted_upper (a := eta .low t) (s := e) ⟨hp.2.2.2.2,heta1.le⟩
  have hrlo := tilted_lower (a := 7/10) (by norm_num) he'
  have hrmono := tilted_mono (a := 7/10) (by norm_num) he'
    (show (1/5 : ℝ)∈Icc 0 (1/5 : ℝ) by norm_num) he'.2
  have hrc := cos_upper_four (x := (1/5 : ℝ)) (by norm_num)
  have hrs := sin_upper_five (x := (1/5 : ℝ)) (by norm_num)
  norm_num at hrc hrs
  dsimp [n,p,r,g,tiltedWeight]
  repeat' constructor <;> nlinarith

theorem coarse_upper {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    k .low t≤1+(7/10)*t ∧ ell .low t≤1+(7/10)*t ∧
    c .low t≤1+(7/10)*t ∧ n .low t x≤1+(7/10)*t ∧
    p .low t e≤1+(7/10)*t ∧ r .low e≤1+(7/10)*t := by
  have hp := positive ht
  have hd := angle ht
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hd.2⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans hd.2⟩
  have hsx := (transport_trig hx').2.2.1
  have hse := (transport_trig he').2.2.1
  have hcx := Real.cos_le_one x
  have hce := Real.cos_le_one e
  have hsxu := Real.sin_le hx.1
  have hseu := Real.sin_le he.1
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hc : c .low t≤1+(7/10)*t := by
    have ht2 : t^2≤1/25 := by nlinarith [ht.1,ht.2]
    dsimp [c,k]
    nlinarith [ht.1,ht.2]
  have hnbase : 0≤Real.cos x+(8/25)*Real.sin x := by
    have hco := (transport_trig hx').1
    nlinarith
  have hn := mul_le_mul_of_nonneg_right (show k .low t≤1 by linarith) hnbase
  have hpeta := mul_le_mul_of_nonneg_right heta1.le hse
  refine ⟨hkc.trans hc,hlk.le.trans (hkc.trans hc),hc,?_,?_,?_⟩
  · dsimp [n,g,tiltedWeight]
    nlinarith [hx.2,ht.1]
  · simp only [p,show Band.low≠Band.high by decide,if_false]
    nlinarith [he.2,ht.1]
  · simp only [r,show Band.low≠Band.high by decide,if_false]
    nlinarith [he.2]

theorem wide_pair_H {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    base≤min (if de then r .low e else 1) (n .low t x) ∧
      max (if de then r .low e else 1) (n .low t x)∈Icc 1 (28/25 : ℝ) := by
  have hb := split_bounds ht hx he
  have hk := (low_bounds ht).1
  cases de <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    constructor
  · exact le_min (by norm_num [base]) (by dsimp [base]; linarith)
  · exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith [hb.2.1])⟩
  · exact le_min (by dsimp [base]; linarith [hb.2.2.2.2.1]) (by dsimp [base]; linarith)
  · exact ⟨hb.2.2.2.2.1.trans (le_max_left _ _),max_le hb.2.2.2.2.2.le (by linarith [hb.2.1])⟩

theorem wide_pair_D {de : Bool} {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    base≤min (if de then 1 else p .low t e) (c .low t) ∧
      max (if de then 1 else p .low t e) (c .low t)∈Icc 1 (28/25 : ℝ) := by
  have hb := split_bounds ht hx he
  have hk := (low_bounds ht).1
  have hkc := (low_bounds ht).2.2.1
  have hc := (low_bounds ht).2.2.2.1
  cases de <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    constructor
  · exact le_min (by dsimp [base]; linarith [hb.2.2.1]) (by dsimp [base]; linarith)
  · exact ⟨hb.2.2.1.trans (le_max_left _ _),max_le (by linarith [hb.2.2.2.1]) (by linarith)⟩
  · exact le_min (by norm_num [base]) (by dsimp [base]; linarith)
  · exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith)⟩

end SquaresInCircles.Eight.TableFree.SoleLowCoefficientBounds
