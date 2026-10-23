module

public import SquaresInCircles.Eight.TableFree.SoleOrdinaryData
public import SquaresInCircles.Eight.TableFree.SoleBalancedPolynomials

/-!
# Original-split coefficient bounds in the middle and high families

Uncompiled source. The bounds cover all x,e in [0,t], so no optimizing
split is assumed. The high H upper bound uses the correlated polynomial
family; the low endpoint of that H pair follows from whole-arc harmonic
concavity. The middle sole-DE coefficient retains its larger 59/50 cap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleBalancedCoefficients
open SoleECoefficients SoleOrdinaryData SecondaryEStress

theorem cosine_quadratic {s : ℝ} (hs : 0≤s) : 1-s^2/2≤Real.cos s := by
  have hh := nonneg_of_deriv_nonneg (fun x => Real.cos x-1+x^2/2)
    (by fun_prop) (by norm_num)
    (fun x hx => by simp (disch := fun_prop); linarith [Real.sin_le hx]) hs
  linarith

theorem tilted_lower {a s : ℝ} (ha : 31/100≤a) (hs : s∈Icc 0 (7/20 : ℝ)) :
    1≤Real.cos s+a*Real.sin s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hs0 := (transport_trig hs').2.2.1
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := cosine_quadratic hs.1
  have hsq := mul_le_mul_of_nonneg_left hs.2 hs.1
  have hsq' : s^2≤49/400 := by nlinarith [hs.1,hs.2]
  have hcube := mul_le_mul_of_nonneg_right hsq' hs.1
  have hm := mul_le_mul_of_nonneg_right ha hs0
  nlinarith

theorem tilted_square (a s : ℝ) :
    (Real.cos s+a*Real.sin s)^2≤1+a^2 := by
  have hid : (Real.cos s+a*Real.sin s)^2+(Real.sin s-a*Real.cos s)^2=
      (1+a^2)*((Real.sin s)^2+(Real.cos s)^2) := by ring
  rw [Real.sin_sq_add_cos_sq] at hid
  nlinarith [sq_nonneg (Real.sin s-a*Real.cos s)]

theorem tilted_upper {a s : ℝ} (ha : a∈Icc 0 (7/20 : ℝ)) :
    Real.cos s+a*Real.sin s<53/50 := by
  have hs := tilted_square a s
  have ha2 : a^2≤49/400 := by nlinarith [ha.1,ha.2]
  nlinarith

theorem r_mono : MonotoneOn (fun s : ℝ => Real.cos s+(7/10)*Real.sin s) (Icc 0 (7/20)) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · intro s _
    exact (Real.hasDerivAt_cos s).add ((Real.hasDerivAt_sin s).const_mul (7/10))
  · intro s hs
    have hsin := Real.sin_le hs.1.le
    have hcos := cosine_quadratic hs.1.le
    have hs2 : s^2≤49/400 := by nlinarith [hs.1,hs.2]
    nlinarith [hs.2]

theorem middle_split {t x e : ℝ} (ht : t∈domain .middle)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    k .middle t≤n .middle t x ∧ n .middle t x<53/50 ∧
    1≤p .middle t e ∧ p .middle t e<53/50 ∧
    1≤r .middle e ∧ r .middle e<59/50 := by
  have hx' : x∈Icc 0 (7/20 : ℝ) := ⟨hx.1,hx.2.trans ht.2⟩
  have he' : e∈Icc 0 (7/20 : ℝ) := ⟨he.1,he.2.trans ht.2⟩
  have hp := SoleECoefficients.positive ht
  rcases middle_bounds ht with ⟨hk0,hk1,hc0,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hnlo := mul_le_mul_of_nonneg_left (tilted_lower (a := 31/100) le_rfl hx') hp.1.le
  have hnhi := mul_lt_mul_of_pos_left (tilted_upper (a := 31/100) (s := x) (by norm_num)) hp.1
  have hplo := tilted_lower (a := eta .middle t) (by linarith) he'
  have hphi := tilted_upper (a := eta .middle t) (s := e) ⟨hp.2.2.2.2,heta1.le⟩
  have hrlo := tilted_lower (a := 7/10) (by norm_num) he'
  have hrhi := r_mono he' (show (7/20 : ℝ)∈Icc 0 (7/20 : ℝ) by norm_num) he'.2
  have hc := cos_upper_four (x := (7/20 : ℝ)) (by norm_num)
  have hs := sin_upper_five (x := (7/20 : ℝ)) (by norm_num)
  norm_num at hc hs
  dsimp [n,p,r,g,tiltedWeight]
  repeat' constructor <;> nlinarith

theorem high_n {t x : ℝ} (ht : t∈domain .high) (hx : x∈Icc 0 t) :
    19/20<n .high t x ∧ n .high t x<53/50 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  rcases high_bounds ht with ⟨hklo,hkhi,hc,hl0,hl1,hlk,hcl,hglo,hghi⟩
  have hk0 := (SoleECoefficients.positive ht).1
  have hg0 := (SoleECoefficients.positive ht).2.2.2.1
  have hh : (19/20 : ℝ)<Real.cos x+(149/500)*Real.sin x := by
    have hz := trig_concave_gt (α := (0:ℝ)) (A := (149/500 : ℝ)) (B := (1:ℝ))
      (m := (19/20 : ℝ)) (l := (0:ℝ)) (u := frameCap)
      (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hx'
      (by norm_num)
      (by have hc := (transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
          have hs := OrdinaryNegativeEnvelope.cap_sin_lower
          nlinarith)
    simpa only [zero_mul,one_mul,zero_add,add_comm] using hz
  have hm := mul_le_mul_of_nonneg_right hglo (transport_trig hx').2.2.1
  have htilt : 19/20<Real.cos x+g .high t*Real.sin x := by linarith
  have hkm := mul_le_mul_of_nonneg_right (show (1:ℝ)≤k .high t by linarith [hklo])
    (show 0≤Real.cos x+g .high t*Real.sin x by linarith)
  have hsq := mul_le_mul_of_nonneg_left (tilted_square (g .high t) x) (sq_nonneg (k .high t))
  have hcorr := SoleBalancedPolynomials.high_norm_square ht
  dsimp [n,tiltedWeight]
  constructor
  · nlinarith
  · nlinarith

theorem ratio_from_interval {a b lo hi : ℝ} (ha : a∈Icc lo hi) (hb : b∈Icc lo hi)
    (hr : (2/3)*hi≤lo) : (2/3)*max a b≤min a b := by
  have hmax := max_le ha.2 hb.2
  have hmin := le_min ha.1 hb.1
  linarith

theorem middle_conditions {de : Bool} {t x e : ℝ} (ht : t∈domain .middle)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    (∀ i,(2/3)*large .middle de t x e i≤small .middle de t x e i) ∧
    (∀ i,(983/1000 : ℝ)≤large .middle de t x e i ∧ large .middle de t x e i≤59/50) := by
  obtain ⟨hnlo,hnhi,hplo,hphi,hrlo,hrhi⟩ := middle_split ht hx he
  rcases middle_bounds ht with ⟨hk0,hk1,hc0,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hHn : n .middle t x∈Icc (983/1000 : ℝ) (59/50) := ⟨hk0.trans hnlo,by linarith⟩
  have hHr : (if de then r .middle e else 1)∈Icc (983/1000 : ℝ) (59/50) := by
    cases de <;> simp only [Bool.false_eq_true,if_false,if_true] <;> constructor <;> linarith
  have hDp : (if de then 1 else p .middle t e)∈Icc (1:ℝ) (111/100) := by
    cases de <;> simp only [Bool.false_eq_true,if_false,if_true] <;> constructor <;> linarith
  have hDc : c .middle t∈Icc (1:ℝ) (111/100) := ⟨by linarith,hc1.le⟩
  constructor
  · intro i
    fin_cases i
    · exact ratio_from_interval hHr hHn (by norm_num)
    · simpa [small,large,alpha,beta,min_eq_left hlk.le,max_eq_right hlk.le] using
        (show (2/3)*k .middle t≤ell .middle t by linarith)
    · simpa [small,large,alpha,beta,min_eq_left (ell_le_k_c ht).2,
        max_eq_right (ell_le_k_c ht).2] using hcl
    · exact ratio_from_interval hDp hDc (by norm_num)
  · intro i
    fin_cases i
    · exact ⟨hHr.1.trans (le_max_left _ _),max_le hHr.2 hHn.2⟩
    · simpa [large,alpha,beta,max_eq_right hlk.le] using ⟨hk0,show k .middle t≤59/50 by linarith⟩
    · simpa [large,alpha,beta,max_eq_right (ell_le_k_c ht).2] using
        ⟨show 983/1000≤c .middle t by linarith,show c .middle t≤59/50 by linarith⟩
    · exact ⟨(show (983/1000 : ℝ)≤c .middle t by linarith).trans (le_max_right _ _),
        (max_le hDp.2 hDc.2).trans (by norm_num)⟩

theorem high_conditions {de : Bool} {t x e : ℝ} (ht : t∈domain .high)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    (∀ i,(2/3)*large .high de t x e i≤small .high de t x e i) ∧
    (∀ i,(1:ℝ)≤large .high de t x e i ∧ large .high de t x e i≤113/100) := by
  obtain ⟨hnlo,hnhi⟩ := high_n ht hx
  rcases high_bounds ht with ⟨hk0,hk1,hc,hl0,hl1,hlk,hcl,hg0,hg1⟩
  have hH := ratio_from_interval
    (show (1:ℝ)∈Icc (19/20 : ℝ) (53/50) by norm_num)
    (show n .high t x∈Icc (19/20 : ℝ) (53/50) from ⟨hnlo.le,hnhi.le⟩) (by norm_num)
  constructor
  · intro i
    fin_cases i
    · cases de <;> simpa [small,large,alpha,beta,r] using hH
    · simpa [small,large,alpha,beta,min_eq_left hlk.le,max_eq_right hlk.le] using
        (show (2/3)*k .high t≤ell .high t by linarith)
    · simpa [small,large,alpha,beta,min_eq_left (ell_le_k_c ht).2,
        max_eq_right (ell_le_k_c ht).2] using hcl
    · cases de <;> norm_num [small,large,alpha,beta,p,hc]
  · intro i
    fin_cases i
    · cases de <;> simp only [large,alpha,beta,r,if_true,if_false,
        Bool.false_eq_true,Matrix.cons_val_zero] <;>
        exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith)⟩
    · simpa [large,alpha,beta,max_eq_right hlk.le] using
        ⟨show (1:ℝ)≤k .high t by linarith,show k .high t≤113/100 by linarith⟩
    · simpa [large,alpha,beta,max_eq_right (ell_le_k_c ht).2,hc] using
        (show (1:ℝ)≤113/100 ∧ (113/100 : ℝ)≤113/100 by norm_num)
    · cases de <;> norm_num [large,alpha,beta,p,hc]

end SquaresInCircles.Eight.TableFree.SoleBalancedCoefficients
