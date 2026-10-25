module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeData

/-!
# Eight squares: the actual fixed-source rotation on the original circle

The parameter `k` is `1/2` minus the fixed source secondary coordinate.
The same exact rotation describes the short-source cut, the zero-source
contact and the source-diagonal contact.  The formulas below include
the two derivatives needed for their whole-arc curvature arguments.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve

open CommonQuarter CorePairGeometry Arithmetic

def z (k φ : ℝ) : ℝ := k+Real.sin φ
def y (k φ : ℝ) : ℝ := Real.sqrt (Q0-(z k φ)^2)
def u (k φ : ℝ) : ℝ := z k φ*Real.sin φ+y k φ*Real.cos φ
def w (k φ : ℝ) : ℝ := y k φ*Real.sin φ-z k φ*Real.cos φ
def target (k φ : ℝ) : ℝ := w k φ-1/2
def f (k φ : ℝ) : ℝ := 1-Real.cos φ/y k φ
def fp (k φ : ℝ) : ℝ :=
  (Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2))/(y k φ)^3
def yp (k φ : ℝ) : ℝ := -z k φ*Real.cos φ/y k φ
def ypp (k φ : ℝ) : ℝ :=
  z k φ*Real.sin φ/y k φ-Q0*(Real.cos φ)^2/(y k φ)^3
def up (k φ : ℝ) : ℝ := -w k φ*f k φ
def upp (k φ : ℝ) : ℝ := -u k φ*(f k φ)^2-w k φ*fp k φ
def bp (k φ : ℝ) : ℝ := u k φ*f k φ
def bpp (k φ : ℝ) : ℝ := -w k φ*(f k φ)^2+u k φ*fp k φ
def quotient (k φ : ℝ) : ℝ := y k φ/u k φ
def quotientFirst (k φ : ℝ) : ℝ :=
  yp k φ/u k φ-y k φ*up k φ/(u k φ)^2
def quotientSecond (k φ : ℝ) : ℝ :=
  ypp k φ/u k φ-2*yp k φ*up k φ/(u k φ)^2-
    y k φ*upp k φ/(u k φ)^2+2*y k φ*(up k φ)^2/(u k φ)^3

def Domain (k φ : ℝ) : Prop := k∈Icc (-2/5) (1/2) ∧ Lower φ

lemma z_bounds {k φ : ℝ} (h : Domain k φ) : (9/25:ℝ)<z k φ ∧ z k φ≤3/2 := by
  have ht := lower_trig h.2
  dsimp [z]
  constructor <;> linarith [h.1.1,h.1.2,ht.1,ht.2.1]

lemma y_data {k φ : ℝ} (h : Domain k φ) :
    (129/100:ℝ)<y k φ ∧ (y k φ)^2+(z k φ)^2=Q0 := by
  have hz := z_bounds h
  have hsq : (z k φ)^2≤(3/2:ℝ)^2 := by nlinarith
  have hrad : 0<Q0-(z k φ)^2 := by norm_num [Q0]; linarith
  have hp : 0<y k φ := Real.sqrt_pos.2 hrad
  have he : (y k φ)^2=Q0-(z k φ)^2 := Real.sq_sqrt hrad.le
  constructor
  · norm_num [Q0] at he
    nlinarith
  · linarith

lemma u_positive {k φ : ℝ} (h : Domain k φ) : 0<u k φ := by
  have ht := lower_trig h.2
  have hfirst := mul_pos (by linarith [(z_bounds h).1] : 0<z k φ)
    (by linarith [ht.1] : 0<Real.sin φ)
  have hsecond := mul_nonneg (by linarith [(y_data h).1] : 0≤y k φ) ht.2.2.1
  dsimp [u]
  linarith

lemma w_positive {k φ : ℝ} (h : Domain k φ) : 0<w k φ := by
  have ht := lower_trig h.2
  have hz := z_bounds h
  have hy := y_data h
  have hs : (19121/25000:ℝ)^2<(Real.sin φ)^2 := by nlinarith [ht.1]
  have hsum : z k φ≤Real.sin φ+1/2 := by dsimp [z]; linarith [h.1.2]
  have hprod := mul_nonneg (sub_nonneg.mpr hsum)
    (show 0≤Real.sin φ+1/2+z k φ by linarith [ht.1,hz.1])
  have hgap : 0<Q0*(Real.sin φ)^2-(z k φ)^2 := by
    norm_num [Q0]
    nlinarith [ht.2.1]
  have he : (y k φ*Real.sin φ)^2-(z k φ*Real.cos φ)^2=
      Q0*(Real.sin φ)^2-(z k φ)^2 := by
    linear_combination (Real.sin φ)^2*hy.2-(z k φ)^2*(Real.sin_sq_add_cos_sq φ)
  have ha := mul_pos (by linarith [hy.1] : 0<y k φ)
    (by linarith [ht.1] : 0<Real.sin φ)
  have hb := mul_nonneg (by linarith [hz.1] : 0≤z k φ) ht.2.2.1
  dsimp [w]
  by_contra hh
  have hle : y k φ*Real.sin φ≤z k φ*Real.cos φ := by linarith
  have hsq := pow_le_pow_left₀ ha.le hle 2
  nlinarith

lemma circle {k φ : ℝ} (h : Domain k φ) :
    (u k φ)^2+(w k φ)^2=Q0 := by
  have hy := (y_data h).2
  dsimp [u,w]
  linear_combination ((y k φ)^2+(z k φ)^2)*(Real.sin_sq_add_cos_sq φ)+hy

lemma f_bounds {k φ : ℝ} (h : Domain k φ) : 0<f k φ ∧ f k φ≤1 := by
  have hy := (y_data h).1
  have ht := lower_trig h.2
  have hp : 0<y k φ := by linarith
  have hlo : Real.cos φ/y k φ<1 := (div_lt_one hp).2 (by linarith [ht.2.2.2.1])
  have hhi : 0≤Real.cos φ/y k φ := div_nonneg ht.2.2.1 hp.le
  dsimp [f]
  exact ⟨by linarith,by linarith⟩

lemma fp_positive {k φ : ℝ} (h : Domain k φ) : 0<fp k φ := by
  have ht := lower_trig h.2
  have hk : k^2≤(1/4:ℝ) := by nlinarith [h.1.1,h.1.2]
  have hs : (Real.sin φ)^2≤1 := by nlinarith [ht.1,ht.2.1]
  have hdrop := mul_nonneg (by linarith [ht.1] : 0≤Real.sin φ)
    (sub_nonneg.mpr hk)
  have hlast := mul_le_mul_of_nonneg_right h.1.2
    (show 0≤1+(Real.sin φ)^2 by positivity)
  have hnum : 0<Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2) := by
    norm_num [Q0]
    nlinarith [ht.1]
  exact div_pos hnum (pow_pos (by linarith [(y_data h).1] : 0<y k φ) 3)

lemma z_hasDerivAt (k φ : ℝ) : HasDerivAt (z k) (Real.cos φ) φ :=
  (Real.hasDerivAt_sin φ).const_add k

lemma y_hasDerivAt {k φ : ℝ} (h : Domain k φ) : HasDerivAt (y k) (yp k φ) φ := by
  have hy := y_data h
  have hrad : Q0-(z k φ)^2≠0 := by nlinarith [hy.1,hy.2]
  have hp : y k φ≠0 := by linarith [hy.1]
  have hd := (((z_hasDerivAt k φ).pow 2).const_sub Q0).sqrt hrad
  convert hd using 1
  · funext t
    simp only [y,Pi.pow_apply]
  · have hyy : Real.sqrt (Q0-(z k φ)^2)=y k φ := rfl
    simp only [Pi.pow_apply,hyy,Nat.cast_ofNat]
    dsimp only [yp]
    field_simp
    ring

lemma f_hasDerivAt {k φ : ℝ} (h : Domain k φ) : HasDerivAt (f k) (fp k φ) φ := by
  have hy := y_data h
  have hp : y k φ≠0 := by linarith [hy.1]
  have hd := ((Real.hasDerivAt_cos φ).div (y_hasDerivAt h) hp).const_sub 1
  have hN : Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2)=
      Real.sin φ*(y k φ)^2-z k φ*(Real.cos φ)^2 := by
    have h2 : (y k φ)^2+(k+Real.sin φ)^2=Q0 := hy.2
    simp only [z]
    linear_combination (-(Real.sin φ))*h2+(k+Real.sin φ)*(Real.sin_sq_add_cos_sq φ)
  convert hd using 1
  · rfl
  · dsimp only [fp,yp]
    rw [hN]
    field_simp
    ring

lemma u_hasDerivAt {k φ : ℝ} (h : Domain k φ) : HasDerivAt (u k) (up k φ) φ := by
  have hp : y k φ≠0 := by linarith [(y_data h).1]
  have hd := ((z_hasDerivAt k φ).mul (Real.hasDerivAt_sin φ)).add
    ((y_hasDerivAt h).mul (Real.hasDerivAt_cos φ))
  convert hd using 1
  · funext t
    simp only [u,Pi.add_apply,Pi.mul_apply]
  · dsimp only [up,w,f,yp]
    field_simp
    ring

lemma w_hasDerivAt {k φ : ℝ} (h : Domain k φ) : HasDerivAt (w k) (bp k φ) φ := by
  have hp : y k φ≠0 := by linarith [(y_data h).1]
  have hd := ((y_hasDerivAt h).mul (Real.hasDerivAt_sin φ)).sub
    ((z_hasDerivAt k φ).mul (Real.hasDerivAt_cos φ))
  convert hd using 1
  · funext t
    simp only [w,Pi.sub_apply,Pi.mul_apply]
  · dsimp only [bp,u,f,yp]
    field_simp
    ring

lemma target_hasDerivAt {k φ : ℝ} (h : Domain k φ) :
    HasDerivAt (target k) (bp k φ) φ := (w_hasDerivAt h).sub_const (1/2)

lemma yp_hasDerivAt {k φ : ℝ} (h : Domain k φ) : HasDerivAt (yp k) (ypp k φ) φ := by
  have hy := y_data h
  have hp : y k φ≠0 := by linarith [hy.1]
  have hd := ((((z_hasDerivAt k φ).neg).mul (Real.hasDerivAt_cos φ)).div
    (y_hasDerivAt h) hp)
  convert hd using 1
  · rfl
  · simp only [Pi.neg_apply,Pi.mul_apply]
    dsimp only [ypp,yp]
    field_simp
    linear_combination (Real.cos φ)^2*hy.2

lemma up_hasDerivAt {k φ : ℝ} (h : Domain k φ) : HasDerivAt (up k) (upp k φ) φ := by
  convert ((w_hasDerivAt h).neg).mul (f_hasDerivAt h) using 1
  · funext t
    simp only [up,Pi.mul_apply,Pi.neg_apply]
  · simp only [Pi.neg_apply]
    dsimp only [upp,bp]
    ring

lemma bp_hasDerivAt {k φ : ℝ} (h : Domain k φ) : HasDerivAt (bp k) (bpp k φ) φ := by
  convert (u_hasDerivAt h).mul (f_hasDerivAt h) using 1
  · funext t
    simp only [bp,Pi.mul_apply]
  · dsimp only [bpp,up]
    ring

lemma quotient_hasDerivAt {k φ : ℝ} (h : Domain k φ) :
    HasDerivAt (quotient k) (quotientFirst k φ) φ := by
  have hp := (u_positive h).ne'
  convert (y_hasDerivAt h).div (u_hasDerivAt h) hp using 1
  · funext t
    simp only [quotient,Pi.div_apply]
  · dsimp only [quotientFirst]
    field_simp

lemma quotientFirst_hasDerivAt {k φ : ℝ} (h : Domain k φ) :
    HasDerivAt (quotientFirst k) (quotientSecond k φ) φ := by
  have hp := (u_positive h).ne'
  have hd := ((yp_hasDerivAt h).div (u_hasDerivAt h) hp).sub
    (((y_hasDerivAt h).mul (up_hasDerivAt h)).div
      ((u_hasDerivAt h).pow 2) (pow_ne_zero 2 hp))
  convert hd using 1
  · funext t
    simp only [quotientFirst,Pi.sub_apply,Pi.div_apply,Pi.mul_apply,Pi.pow_apply]
  · simp only [Pi.mul_apply,Pi.pow_apply,Nat.cast_ofNat]
    dsimp only [quotientSecond]
    field_simp
    ring

lemma yp_nonpositive {k φ : ℝ} (h : Domain k φ) : yp k φ≤0 := by
  have hz : 0≤z k φ := by linarith [(z_bounds h).1]
  have hc := (lower_trig h.2).2.2.1
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hc)
    (by linarith [(y_data h).1])

lemma up_negative {k φ : ℝ} (h : Domain k φ) : up k φ<0 :=
  mul_neg_of_neg_of_pos (neg_neg_of_pos (w_positive h)) (f_bounds h).1

lemma bp_positive {k φ : ℝ} (h : Domain k φ) : 0<bp k φ :=
  mul_pos (u_positive h) (f_bounds h).1

lemma y_antitone {k : ℝ} (hk : k∈Icc (-2/5) (1/2)) :
    AntitoneOn (y k) (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (y_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun t ht => y_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun t ht => yp_nonpositive ⟨hk,Ioo_subset_Icc_self ht⟩)

lemma u_antitone {k : ℝ} (hk : k∈Icc (-2/5) (1/2)) :
    AntitoneOn (u k) (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (u_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun t ht => u_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun t ht => (up_negative ⟨hk,Ioo_subset_Icc_self ht⟩).le)

lemma target_monotone {k : ℝ} (hk : k∈Icc (-2/5) (1/2)) :
    MonotoneOn (target k) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (target_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun t ht => target_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun t ht => (bp_positive ⟨hk,Ioo_subset_Icc_self ht⟩).le)

lemma f_monotone {k : ℝ} (hk : k∈Icc (-2/5) (1/2)) :
    MonotoneOn (f k) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (f_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun t ht => f_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun t ht => (fp_positive ⟨hk,Ioo_subset_Icc_self ht⟩).le)

end SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve
