module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameDiagonalReferences

/-!
# The full early source-diagonal geometry

Uncompiled transcription of equation (10). The actual rotated circle
is used from its initial event through .3. Its support-factor derivative
increases on that complete interval, giving B' > .91 and B'' < .2.
The initial speed is bounded by .942 at the actual event.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open SecondWord.SameZero.PJ.Diagonal (z₀)

lemma early_angle {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    x∈Icc start (7/10) := by
  have hge := (event_geometry he).1.1
  exact ⟨hge.1.trans hx.1,by linarith [hx.2]⟩

lemma early_geometry {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) : Geometry x := by
  have heG := event_geometry he
  have hxa := early_angle he hx
  have hm := SecondWord.SameZero.PJ.Diagonal.height_monotone heG.1.1 hxa hx.1
  have h0 : SecondWord.SameZero.PJ.Diagonal.height e=0 := heG.2
  rw [h0] at hm
  exact ⟨hxa,hm⟩

lemma early_Z {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    0<Z x ∧ Z x<(293/1000:ℝ) := by
  have hr := SecondWord.SameZero.PJ.Diagonal.radical_data (early_angle he hx)
  have hs := Real.sin_le (show 0≤x from (Event.angle_mem he).1.trans hx.1)
  have hz : 0<Z x := by
    dsimp [Z,SecondWord.SameZero.PJ.Diagonal.Z,z₀]
    linarith [ShortMixedZero.fine_diagonal_bounds.1,hx.2]
  exact ⟨hz,hr.2.1⟩

lemma early_Y {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (1957/1000:ℝ)<Y x := by
  have hinit : (1957/1000:ℝ)<Y e := by
    have hbox : (1957/1000:ℝ)<(eventY he).lo := by
      dsimp [eventY,eventRad,eventZ,Event.eventSin]
      diagonal_reference_arithmetic
    exact hbox.trans_le (eventY he).mem.1
  have hm : MonotoneOn Y (Icc e (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => (SecondWord.SameZero.PJ.Diagonal.Y_hasDerivAt
        (early_angle he hu)).continuousAt.continuousWithinAt)
      (fun u hu => SecondWord.SameZero.PJ.Diagonal.Y_hasDerivAt
        (early_angle he (Ioo_subset_Icc_self hu)))
      (fun u hu => by
        have hz := (early_Z he (Ioo_subset_Icc_self hu)).1
        have hy := (SecondWord.SameZero.PJ.Diagonal.radical_data
          (early_angle he (Ioo_subset_Icc_self hu))).2.2.1
        have hc := (positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem
          (early_angle he (Ioo_subset_Icc_self hu)))).1
        exact div_nonneg (mul_nonneg hz.le (by linarith)) (by linarith))
  exact hinit.trans_le (hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1)

lemma early_coordinates {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (37/20:ℝ)<horizontal x ∧ horizontal x<383/200 ∧
      (1/2:ℝ)≤vertical x ∧ (4919/10000:ℝ)<factor x := by
  have hxa := early_angle he hx
  have hg := early_geometry he hx
  have hU := SecondWord.SameZero.PJ.Diagonal.horizontal_antitone hxa
    (by norm_num [start,SecondWord.SameZero.PJ.Diagonal.start]) hx.2
  have hUl := three_tenths.1.trans_le hU
  have hUu := (SecondWord.SameZero.PJ.Diagonal.whole_bounds hxa).2.1
  have hV : (1/2:ℝ)≤vertical x := by
    have hg2 : 0≤SecondWord.SameZero.PJ.Diagonal.height x := hg.2
    simp only [SecondWord.SameZero.PJ.Diagonal.height] at hg2
    show (1/2:ℝ)≤SecondWord.SameZero.PJ.Diagonal.vertical x
    linarith
  have hcos : Real.cos x<(9943/10000:ℝ) := by
    have helo : Event.lo≤x := he.1.1.le.trans hx.1
    have hh := cos_anti (by norm_num [Event.lo])
      (SecondWord.SameZero.PJ.Diagonal.angle_mem hxa) helo
    have ht := HighOrderTaylor.cos_le_C16 (show 0≤Event.lo by norm_num [Event.lo])
    have href : HighOrderTaylor.C16 Event.lo<(9943/10000:ℝ) := by
      norm_num [Event.lo,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8]
    exact hh.trans_lt (ht.trans_lt href)
  have hy := early_Y he hx
  have hratio : Real.cos x/Y x<(5081/10000:ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<Y x)).2
    linarith
  refine ⟨hUl,hUu,hV,?_⟩
  show (4919/10000:ℝ)<SecondWord.SameZero.PJ.Diagonal.factor x
  simp only [SecondWord.SameZero.PJ.Diagonal.factor]
  have hr : Real.cos x/SecondWord.SameZero.PJ.Diagonal.Y x<(5081/10000:ℝ) := hratio
  linarith

def factorDD (x : ℝ) : ℝ := Real.cos x/(Y x)^5*
  ((Y x)^4-((Real.cos x)^2+3*Z x*Real.sin x)*(Y x)^2-3*(Z x)^2*(Real.cos x)^2)

lemma factorD_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt factorD (factorDD x) x := by
  have hY := SecondWord.SameZero.PJ.Diagonal.Y_hasDerivAt hx
  have hy : 0<Y x := by linarith [(SecondWord.SameZero.PJ.Diagonal.radical_data hx).2.2.1]
  have hc := (SecondWord.SameZero.PJ.Diagonal.radical_data hx).2.2.2.2
  have ht := Real.sin_sq_add_cos_sq x
  have hn : HasDerivAt (fun y => Real.sin y*(Q0-1-z₀^2)+z₀*(1+(Real.sin y)^2))
      (Real.cos x*(Q0-1-z₀^2+2*z₀*Real.sin x)) x := by
    have h := ((Real.hasDerivAt_sin x).mul_const (Q0-1-z₀^2)).fun_add
      ((((Real.hasDerivAt_sin x).fun_pow 2).const_add 1).const_mul z₀)
    convert h using 1
    push_cast
    ring
  have key : Real.cos x*(Q0-1-z₀^2+2*z₀*Real.sin x)*(Y x)^2-
      3*(Real.sin x*(Q0-1-z₀^2)+z₀*(1+(Real.sin x)^2))*Z x*Real.cos x=
      Real.cos x*((Y x)^4-((Real.cos x)^2+3*Z x*Real.sin x)*(Y x)^2-
        3*(Z x)^2*(Real.cos x)^2) := by
    simp only [Z,SecondWord.SameZero.PJ.Diagonal.Z] at hc ⊢
    linear_combination Real.cos x*((Y x)^2+3*(z₀-Real.sin x)^2)*ht+
      Real.cos x*(3*(z₀-Real.sin x)*Real.sin x-(Y x)^2)*hc
  refine (hn.fun_div (hY.fun_pow 3) (pow_ne_zero 3 hy.ne')).congr_deriv ?_
  have hY0 : SecondWord.SameZero.PJ.Diagonal.Y x≠0 := hy.ne'
  rw [show ∀ a : ℝ, (a*SecondWord.SameZero.PJ.Diagonal.Y x^3-
      (Real.sin x*(Q0-1-z₀^2)+z₀*(1+(Real.sin x)^2))*
        (((3:ℕ):ℝ)*SecondWord.SameZero.PJ.Diagonal.Y x^(3-1)*
          (SecondWord.SameZero.PJ.Diagonal.Z x*Real.cos x/SecondWord.SameZero.PJ.Diagonal.Y x)))/
      (SecondWord.SameZero.PJ.Diagonal.Y x^3)^2=
      (a*(Y x)^2-3*(Real.sin x*(Q0-1-z₀^2)+z₀*(1+(Real.sin x)^2))*Z x*Real.cos x)/(Y x)^5
    from fun a => by field_simp; push_cast; ring]
  rw [key]
  simp only [factorDD]
  ring

lemma factorDD_positive {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    0<factorDD x := by
  have hxa := early_angle he hx
  have hz := early_Z he hx
  have hy := early_Y he hx
  have tr := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hxa)
  have hs : Real.sin x<(37/125:ℝ) := by
    have hm := sin_mono (SecondWord.SameZero.PJ.Diagonal.angle_mem hxa) (by norm_num) hx.2
    linarith [Unfavorable.initial_trig.2.1]
  have hz2 : (Z x)^2<(43/500:ℝ) := by nlinarith [hz.1,hz.2]
  have hc2 : (Real.cos x)^2≤1 := by nlinarith [tr.1,tr.2.1]
  have hzc := mul_le_mul hz2.le hc2 (sq_nonneg (Real.cos x)) (by norm_num)
  have hzs := mul_le_mul hz.2.le hs.le tr.2.2.1 (by norm_num)
  have hcoef : (Real.cos x)^2+3*Z x*Real.sin x<(1261/1000:ℝ) := by nlinarith
  have hY2 : (3829/1000:ℝ)<(Y x)^2 := by nlinarith
  have hupper := mul_le_mul_of_nonneg_right hcoef.le (sq_nonneg (Y x))
  have hproduct := mul_nonneg
    (show 0≤(Y x)^2-3829/1000 by linarith)
    (show 0≤(Y x)^2+3829/1000-1261/1000 by nlinarith)
  have hbrace : 0<(Y x)^4-((Real.cos x)^2+3*Z x*Real.sin x)*(Y x)^2-
      3*(Z x)^2*(Real.cos x)^2 := by nlinarith
  dsimp [factorDD]
  exact mul_pos (div_pos (by linarith [tr.1]) (pow_pos (by linarith : 0<Y x) 5)) hbrace

lemma early_factorD_upper {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    factorD x<(81/500:ℝ) := by
  have hm : MonotoneOn factorD (Icc e (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => (factorD_hasDerivAt (early_angle he hu)).continuousAt.continuousWithinAt)
      (fun u hu => factorD_hasDerivAt (early_angle he (Ioo_subset_Icc_self hu)))
      (fun u hu => (factorDD_positive he (Ioo_subset_Icc_self hu)).le)
  exact (hm hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2).trans_lt three_tenths.2.1

lemma factorD_positive {x : ℝ} (hx : x∈Icc start (7/10)) : 0<factorD x := by
  have hr := SecondWord.SameZero.PJ.Diagonal.radical_data hx
  have tr := positive_trig (SecondWord.SameZero.PJ.Diagonal.angle_mem hx)
  have hz : 0<z₀ ∧ z₀<(2/5:ℝ) := by
    dsimp [z₀]
    constructor <;> linarith [ShortMixedZero.fine_diagonal_bounds.1,ShortMixedZero.fine_diagonal_bounds.2]
  have hcoef : 0<Q0-1-z₀^2 := by norm_num [Q0]; nlinarith
  have h1 := mul_nonneg tr.2.2.1 hcoef.le
  have h2 := mul_pos hz.1 (show 0<1+(Real.sin x)^2 by nlinarith [sq_nonneg (Real.sin x)])
  exact div_pos (by linarith) (pow_pos (by linarith [hr.2.2.1]) 3)

lemma early_speed_acceleration {e x : ℝ} (he : Event.IsEvent e) (hx : x∈Icc e (3/10)) :
    (91/100:ℝ)<speed x ∧ acceleration x<(1/5:ℝ) := by
  have hc := early_coordinates he hx
  have hfd := early_factorD_upper he hx
  have hfd0 := factorD_positive (early_angle he hx)
  have hp := mul_lt_mul'' hc.1 hc.2.2.2 (by norm_num) (by norm_num)
  have hf2 : (4919/10000:ℝ)^2≤(factor x)^2 := by nlinarith [hc.2.2.2]
  have hneg := mul_le_mul hc.2.2.1 hf2 (by norm_num) (by linarith [hc.2.2.1])
  have hpos := mul_le_mul hc.2.1.le hfd.le hfd0.le (by norm_num)
  show (91/100:ℝ)<SecondWord.SameZero.PJ.Diagonal.speed x ∧
    SecondWord.SameZero.PJ.Diagonal.acceleration x<(1/5:ℝ)
  simp only [SecondWord.SameZero.PJ.Diagonal.speed,
    SecondWord.SameZero.PJ.Diagonal.acceleration]
  exact ⟨by linarith,by linarith⟩

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Diagonal
