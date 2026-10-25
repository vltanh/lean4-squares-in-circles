module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: the derivative along each actual fixed-source contact

The coefficient `g` is a fixed source-label derivative.  Two ordinary
chain rules give the exact curvature of the target derivative.  The
quotient estimate discards only two terms of known sign from the
physical circle formula.  These identities apply to both the short
source and the zero-source boundary.
-/

section
/-!
## The complete lower target-secondary owner for positive edge three

One concave derivative bound moves the original source to the axial
end of the circle.  The resulting angle function has curvature greater
than `.44`; its single reference at `1.04` gives a strict global reserve.
No angle or coordinate subdivision is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def projectedSlope (b : ℝ) : ℝ :=
  VLabel.d1 b+(147/125)*(19121/25000)*ratio b-(147/125)*(16106/25000)
def projectedSlopeFirst (b : ℝ) : ℝ :=
  VLabel.d2 b+(147/125)*(19121/25000)*ratioD b
def projectedSlopeSecond (b : ℝ) : ℝ :=
  VLabel.d3 b+(147/125)*(19121/25000)*ratioDD b

lemma projectedSlope_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projectedSlope (projectedSlopeFirst b) b := by
  convert ((VLabel.d1_hasDerivAt (outer_domain hb)).add
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
      ((147/125)*(19121/25000)))).sub_const ((147/125)*(16106/25000)) using 1
  · funext t
    simp only [projectedSlope,Pi.add_apply]
  · rfl

lemma projectedSlopeFirst_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projectedSlopeFirst (projectedSlopeSecond b) b := by
  convert (VLabel.d2_hasDerivAt (outer_domain hb)).add
    ((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_mul
      ((147/125)*(19121/25000))) using 1
  · funext t
    simp only [projectedSlopeFirst,Pi.add_apply]
  · rfl

lemma projectedSlopeSecond_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    projectedSlopeSecond b<0 := by
  have he := VLabel.third_numerator (outer_domain hb)
  have hp := pow_pos (U_positive (outer_domain hb)) 5
  have hDD : ratioDD b*(U b)^5=3*Q0*W b := by
    show 3*Q0*W b/(U b)^5*(U b)^5=3*Q0*W b
    exact div_mul_cancel₀ _ hp.ne'
  have hh := (UW_bounds hb).2.2
  have hnum : projectedSlopeSecond b*(U b)^5=
      3*Q0*(-(63457/100000)*Q0+
        ((65507/200000)+(147/125)*(19121/25000))*W b) := by
    dsimp only [projectedSlopeSecond]
    rw [show VLabel.s=63457/100000 from rfl,show VLabel.p=-1025/100000 from rfl] at he
    linear_combination he+((147/125)*(19121/25000))*hDD
  have hneg : 3*Q0*(-(63457/100000)*Q0+
      ((65507/200000)+(147/125)*(19121/25000))*W b)<0 := by
    norm_num [Q0]
    linarith [hh.2]
  by_contra hc
  have hm := mul_nonneg (le_of_not_gt hc) hp.le
  linarith

lemma projectedSlope_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (31/100:ℝ)<projectedSlope b := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) projectedSlope :=
    concave_of_deriv2
      (fun t ht => projectedSlope_hasDerivAt ht)
      (fun t ht => projectedSlopeFirst_hasDerivAt ht)
      (fun t ht => (projectedSlopeSecond_negative ht).le)
  have hz : (31/100:ℝ)<projectedSlope 0 := by
    dsimp [projectedSlope]
    linarith [V_zero_first_lower,(outer_ratio_bounds outer_zero_mem).1]
  have hd : (31/100:ℝ)<projectedSlope outerDiagonal := by
    rw [projectedSlope,V_first_diagonal,ratio_diagonal]
    norm_num
  have hh := hc.min_le_of_mem_Icc outer_zero_mem
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb
  exact (lt_min hz hd).trans_le hh

lemma actual_projectedSlope {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : Lower φ) :
    0<VLabel.d1 b+(147/125)*ratio b*Real.sin φ-(147/125)*Real.cos φ := by
  have ht := lower_trig hφ
  have hr := (ShortOuterOne.SameContact.ratio_pos (outer_domain hb)).le
  have hh := mul_nonneg hr (sub_nonneg.mpr ht.1.le)
  have he := projectedSlope_lower hb
  dsimp [projectedSlope] at he
  nlinarith

lemma source_projection_minimum {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : Lower φ) :
    V 0-(147/125)*outerAxial*Real.sin φ≤
      V b-(147/125)*arc b*Real.sin φ-(147/125)*b*Real.cos φ := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun y => V y-(147/125)*arc y*Real.sin φ-(147/125)*y*Real.cos φ)
        (VLabel.d1 t+(147/125)*ratio t*Real.sin φ-(147/125)*Real.cos φ) t := by
    convert ((VLabel.outer_hasDerivAt (outer_domain ht)).sub
      (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain ht)).const_mul
        (147/125)).mul_const (Real.sin φ))).sub
      (((hasDerivAt_id' t).const_mul (147/125)).mul_const (Real.cos φ)) using 1
    · funext y
      simp only [V,Pi.sub_apply]
    · ring
  have hm : MonotoneOn
      (fun y => V y-(147/125)*arc y*Real.sin φ-(147/125)*y*Real.cos φ)
      (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun _ ht => (hd ht).continuousAt.continuousWithinAt)
      (fun _ ht => hd (Ioo_subset_Icc_self ht))
      (fun _ ht => (actual_projectedSlope (Ioo_subset_Icc_self ht) hφ).le)
  have hh := hm outer_zero_mem hb hb.1
  simpa only [ShortOuterOne.SameContact.arc_zero,mul_zero,zero_mul,sub_zero] using hh

def projectionScalar (φ : ℝ) : ℝ :=
  φ+V 0-793/20000+147/250+(147/250)*Real.cos φ-
    (147/125)*(outerAxial-1/2)*Real.sin φ
def projectionFirst (φ : ℝ) : ℝ :=
  1-(147/250)*Real.sin φ-(147/125)*(outerAxial-1/2)*Real.cos φ
def projectionSecond (φ : ℝ) : ℝ :=
  -(147/250)*Real.cos φ+(147/125)*(outerAxial-1/2)*Real.sin φ

lemma projectionScalar_hasDerivAt (φ : ℝ) :
    HasDerivAt projectionScalar (projectionFirst φ) φ := by
  convert (((((hasDerivAt_id' φ).add_const (V 0)).sub_const (793/20000)).add_const
    (147/250)).add ((Real.hasDerivAt_cos φ).const_mul (147/250))).sub
    ((Real.hasDerivAt_sin φ).const_mul ((147/125)*(outerAxial-1/2))) using 1
  · funext t
    simp only [projectionScalar,Pi.add_apply,Pi.sub_apply]
  · dsimp only [projectionFirst]
    ring

lemma projectionFirst_hasDerivAt (φ : ℝ) :
    HasDerivAt projectionFirst (projectionSecond φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (147/250)).const_sub 1).sub
    ((Real.hasDerivAt_cos φ).const_mul ((147/125)*(outerAxial-1/2))) using 1
  · funext t
    simp only [projectionFirst,Pi.sub_apply]
  · dsimp only [projectionSecond]
    ring

lemma projectionSecond_lower {φ : ℝ} (hφ : Lower φ) :
    (11/25:ℝ)<projectionSecond φ := by
  have ht := lower_trig hφ
  have hp := mul_le_mul
    (show (1829/2000:ℝ)≤outerAxial-1/2 by linarith [fine_outer_endpoint_bounds.1])
    ht.1.le (by norm_num : (0:ℝ)≤19121/25000)
    (by linarith [fine_outer_endpoint_bounds.1] : 0≤outerAxial-1/2)
  dsimp [projectionSecond]
  norm_num at hp
  linarith [ht.2.2.2.1]

lemma projection_reference_angle : Lower (26/25) := by
  refine ⟨?_,?_⟩
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · linarith [pi_hand_enclosure.1]

lemma projection_reference_trig :
    (215601/250000:ℝ)<Real.sin (26/25) ∧ Real.sin (26/25)<172481/200000 ∧
    (25311/50000:ℝ)<Real.cos (26/25) ∧ Real.cos (26/25)<506221/1000000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤26/25 by norm_num)
  have hsu := sin_le_sin9 (show (0:ℝ)≤26/25 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤26/25 by norm_num)
  have hcu := cos_le_cos12 (show (0:ℝ)≤26/25 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hsu hc hcu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma projection_references :
    (9439/10000:ℝ)<projectionScalar (26/25) ∧
      |projectionFirst (26/25)|<13/250 := by
  have ht := projection_reference_trig
  have ha : (36583/40000:ℝ)<outerAxial-1/2 ∧ outerAxial-1/2<57161/62500 := by
    constructor <;> linarith [ShortOuterZero.fine_axial_bounds.1,
      ShortOuterZero.fine_axial_bounds.2]
  have hsu := mul_le_mul ha.2.le ht.2.1.le
    (by linarith [ht.1] : 0≤Real.sin (26/25)) (by norm_num : (0:ℝ)≤57161/62500)
  have hcl := mul_le_mul ha.1.le ht.2.2.1.le
    (by norm_num : (0:ℝ)≤25311/50000) (by linarith [ha.1] : 0≤outerAxial-1/2)
  have hcu := mul_le_mul ha.2.le ht.2.2.2.le
    (by linarith [ht.2.2.1] : 0≤Real.cos (26/25))
    (by norm_num : (0:ℝ)≤57161/62500)
  dsimp [projectionScalar,projectionFirst]
  constructor
  · nlinarith [V_zero_bounds.1,ht.2.2.1]
  · rw [abs_lt]
    constructor <;> nlinarith [ht.1,ht.2.1]

theorem projectionScalar_lower {φ : ℝ} (hφ : Lower φ) :
    (588/625:ℝ)<projectionScalar φ := by
  have ht := curvature_tangent (κ := (11/25:ℝ)) hφ projection_reference_angle
    (fun t _ => projectionScalar_hasDerivAt t)
    (fun t _ => projectionFirst_hasDerivAt t)
    (fun t ht => (projectionSecond_lower ht).le)
  have hd := abs_lt.mp projection_references.2
  have hdsq : (projectionFirst (26/25))^2<(13/250:ℝ)^2 := by nlinarith
  nlinarith [projection_references.1,
    sq_nonneg ((11/25)*(φ-26/25)+projectionFirst (26/25))]

theorem original_lower_target_secondary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 φ) :
    (588/625:ℝ)<value b B φ := by
  have hcut := lower_target_secondary_cut hφ hm
  have hL := L_axial_line (NegativeTwo.source_mem ht)
  have hsource := source_projection_minimum (NegativeTwo.source_mem hs) hφ
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hsource
  have hbase := projectionScalar_lower hφ
  dsimp [projectionScalar,value] at *
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end

section
/-!
## The actual fixed-source rotation on the original circle

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
    (fun _ ht => (y_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun _ ht => y_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun _ ht => yp_nonpositive ⟨hk,Ioo_subset_Icc_self ht⟩)

lemma u_antitone {k : ℝ} (hk : k∈Icc (-2/5) (1/2)) :
    AntitoneOn (u k) (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ ht => (u_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun _ ht => u_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun _ ht => (up_negative ⟨hk,Ioo_subset_Icc_self ht⟩).le)

lemma target_monotone {k : ℝ} (hk : k∈Icc (-2/5) (1/2)) :
    MonotoneOn (target k) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ht => (target_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun _ ht => target_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun _ ht => (bp_positive ⟨hk,Ioo_subset_Icc_self ht⟩).le)

lemma f_monotone {k : ℝ} (hk : k∈Icc (-2/5) (1/2)) :
    MonotoneOn (f k) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ht => (f_hasDerivAt ⟨hk,ht⟩).continuousAt.continuousWithinAt)
    (fun _ ht => f_hasDerivAt ⟨hk,Ioo_subset_Icc_self ht⟩)
    (fun _ ht => (fp_positive ⟨hk,Ioo_subset_Icc_self ht⟩).le)

end SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve
end
end
end

section
/-!
## Physical realization and uniqueness of the fixed-source contact

The rotation curve is identified with the original outer-circle chart
whenever its target is on that arc.  Conversely, every original contact
with the fixed source equals this curve.  The derivative quotient is
therefore the actual original cost derivative, with no contact witness
or minimizer premise.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma rotation_z (k φ : ℝ) :
    u k φ*Real.sin φ-w k φ*Real.cos φ=z k φ := by
  dsimp [u,w]
  linear_combination z k φ*(Real.sin_sq_add_cos_sq φ)

lemma rotation_y (k φ : ℝ) :
    u k φ*Real.cos φ+w k φ*Real.sin φ=y k φ := by
  dsimp [u,w]
  linear_combination y k φ*(Real.sin_sq_add_cos_sq φ)

lemma target_W (k φ : ℝ) : W (target k φ)=w k φ := by
  dsimp [target,W]
  ring

lemma target_U {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) : U (target k φ)=u k φ := by
  have hc := UW_circle (outer_domain hb)
  rw [target_W] at hc
  have hp := U_positive (outer_domain hb)
  have hq := u_positive h
  nlinarith [circle h]

lemma target_ratio {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) : ratio (target k φ)=w k φ/u k φ := by
  change W (target k φ)/U (target k φ)=_
  rw [target_W,target_U h hb]

lemma contact {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.source (target k φ) φ=1/2-k := by
  have he := rotation_z k φ
  dsimp [FirstContact.source]
  rw [target_U h hb,target_W]
  dsimp [z] at he
  linarith

lemma contact_slope {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.sourceFirst (target k φ) φ=quotient k φ := by
  have hp := (u_positive h).ne'
  have he := rotation_y k φ
  dsimp [FirstContact.sourceFirst,quotient]
  rw [target_ratio h hb]
  field_simp [hp]
  linarith

lemma unique_target {k B φ : ℝ} (h : Domain k φ)
    (hB : B∈Icc 0 outerDiagonal)
    (he : FirstContact.source B φ=1/2-k) : B=target k φ := by
  have htr := lower_trig h.2
  have hproj : U B*Real.sin φ-W B*Real.cos φ=z k φ := by
    dsimp [FirstContact.source,z] at *
    linarith
  have hrot : (U B*Real.cos φ+W B*Real.sin φ)^2+
      (U B*Real.sin φ-W B*Real.cos φ)^2=Q0 := by
    linear_combination ((U B)^2+(W B)^2)*(Real.sin_sq_add_cos_sq φ)+
      UW_circle (outer_domain hB)
  rw [hproj] at hrot
  have hpos : 0<U B*Real.cos φ+W B*Real.sin φ := by
    have hp := mul_nonneg (U_positive (outer_domain hB)).le htr.2.2.1
    have hq := mul_pos (show 0<W B by dsimp [W]; linarith [hB.1])
      (by linarith [htr.1] : 0<Real.sin φ)
    linarith
  have hy : U B*Real.cos φ+W B*Real.sin φ=y k φ := by
    nlinarith [(y_data h).1,(y_data h).2]
  have hw : W B=w k φ := by
    dsimp [w]
    rw [←hy,←hproj]
    linear_combination -(W B)*(Real.sin_sq_add_cos_sq φ)
  dsimp [W] at hw
  dsimp [target]
  linarith

lemma contact_derivative {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.first (target k φ) φ=
      VLabel.d1 (1/2-k)*quotient k φ-LLabel.d1 (target k φ) := by
  rw [FirstContact.first,contact h hb,contact_slope h hb]

lemma fp_monotone {k : ℝ} (hk : k∈Icc 0 (1/2)) :
    MonotoneOn (fp k) (Icc lowerAngle (Real.pi/2)) := by
  intro φ hφ ψ hψ horder
  have hk' : k∈Icc (-2/5:ℝ) (1/2) := ⟨by linarith [hk.1],hk.2⟩
  have hs := lower_sin_monotone hφ hψ horder
  have hy := y_antitone hk' hφ hψ horder
  have hφtr := lower_trig hφ
  have hψtr := lower_trig hψ
  have hkprod := mul_nonneg hk.1 (sub_nonneg.mpr hk.2)
  have hk2 : k^2≤(1/4:ℝ) := by nlinarith
  have hsum : 0≤Real.sin ψ+Real.sin φ := by linarith [hφtr.1,hψtr.1]
  have hprod := mul_le_mul hk.2 (show Real.sin ψ+Real.sin φ≤2 by
      linarith [hφtr.2.1,hψtr.2.1]) hsum (by norm_num : (0:ℝ)≤1/2)
  have hfactor : 0≤Q0-1-k^2-k*(Real.sin ψ+Real.sin φ) := by
    norm_num [Q0]
    nlinarith
  have hN : Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2)≤
      Real.sin ψ*(Q0-1-k^2)-k*(1+(Real.sin ψ)^2) := by
    have hh := mul_nonneg (sub_nonneg.mpr hs) hfactor
    nlinarith
  have hyp : 0<y k φ := by linarith [(y_data ⟨hk',hφ⟩).1]
  have hyq : 0<y k ψ := by linarith [(y_data ⟨hk',hψ⟩).1]
  have hcube := pow_le_pow_left₀ hyq.le hy 3
  have hNpos : 0≤Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2) := by
    have hh := fp_positive (show Domain k φ from ⟨hk',hφ⟩)
    dsimp [fp] at hh
    have hn := (lt_div_iff₀ (pow_pos hyp 3)).mp hh
    simpa only [zero_mul] using hn.le
  dsimp [fp]
  apply (div_le_div_iff₀ (pow_pos hyp 3) (pow_pos hyq 3)).2
  have hp := mul_nonneg hNpos (sub_nonneg.mpr hcube)
  have hq := mul_nonneg (sub_nonneg.mpr hN) (pow_nonneg hyp.le 3)
  nlinarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve

open CommonQuarter CorePairGeometry Arithmetic

def slope (g k φ : ℝ) : ℝ := g*quotient k φ-LLabel.d1 (target k φ)
def slopeFirst (g k φ : ℝ) : ℝ :=
  g*quotientFirst k φ-LLabel.d2 (target k φ)*bp k φ
def slopeSecond (g k φ : ℝ) : ℝ :=
  g*quotientSecond k φ-LLabel.d3 (target k φ)*(bp k φ)^2-
    LLabel.d2 (target k φ)*bpp k φ

lemma slope_hasDerivAt {k φ : ℝ} (g : ℝ) (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    HasDerivAt (slope g k) (slopeFirst g k φ) φ := by
  convert ((quotient_hasDerivAt h).const_mul g).sub
    ((LLabel.d1_hasDerivAt (outer_domain hb)).comp φ (target_hasDerivAt h))
      using 1
  · funext t
    simp only [slope,Pi.sub_apply,Function.comp_apply]
  · dsimp only [slopeFirst]

lemma slopeFirst_hasDerivAt {k φ : ℝ} (g : ℝ) (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    HasDerivAt (slopeFirst g k) (slopeSecond g k φ) φ := by
  have hd := ((quotientFirst_hasDerivAt h).const_mul g).sub
    (((LLabel.d2_hasDerivAt (outer_domain hb)).comp φ
      (target_hasDerivAt h)).mul (bp_hasDerivAt h))
  convert hd using 1
  · funext t
    simp only [slopeFirst,Pi.sub_apply,Pi.mul_apply,Function.comp_apply]
  · simp only [Function.comp_apply]
    dsimp only [slopeSecond]
    ring

def quotientUpper (k φ : ℝ) : ℝ :=
  z k φ*Real.sin φ/(y k φ*u k φ)+y k φ*(f k φ)^2/u k φ+
    y k φ*w k φ*fp k φ/(u k φ)^2+
      2*y k φ*(w k φ)^2*(f k φ)^2/(u k φ)^3

lemma quotientSecond_le {k φ : ℝ} (h : Domain k φ) :
    quotientSecond k φ≤quotientUpper k φ := by
  have hy : 0<y k φ := by linarith [(y_data h).1]
  have hu := u_positive h
  have he : quotientUpper k φ-quotientSecond k φ=
      Q0*(Real.cos φ)^2/((y k φ)^3*u k φ)+
        2*yp k φ*up k φ/(u k φ)^2 := by
    dsimp [quotientUpper,quotientSecond,ypp,upp,up]
    field_simp [hy.ne',hu.ne']
    ring
  have hfirst : 0≤Q0*(Real.cos φ)^2/((y k φ)^3*u k φ) := by
    have hq : 0<Q0 := by norm_num [Q0]
    positivity
  have hprod := mul_nonneg_of_nonpos_of_nonpos (yp_nonpositive h) (up_negative h).le
  have hsecond : 0≤2*yp k φ*up k φ/(u k φ)^2 := by
    apply div_nonneg
    · nlinarith
    · positivity
  linarith

lemma quotient_positive {k φ : ℝ} (h : Domain k φ) : 0<quotient k φ :=
  div_pos (by linarith [(y_data h).1]) (u_positive h)

lemma original_slope {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.first (target k φ) φ=slope (VLabel.d1 (1/2-k)) k φ :=
  contact_derivative h hb

lemma original_slope_of_lower {g k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal)
    (hg : g≤VLabel.d1 (1/2-k)) :
    slope g k φ≤FirstContact.first (target k φ) φ := by
  rw [original_slope h hb]
  dsimp [slope]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right hg (quotient_positive h).le) _

lemma opposite_product_upper {x y : ℝ}
    (hx : x∈Icc (-(567/500:ℝ)) (19/10))
    (hy : y∈Icc (-(69/200:ℝ)) (373/500)) : -x*y<(847/1000:ℝ) := by
  by_cases hxs : 0≤x
  · by_cases hys : 0≤y
    · have hh := mul_nonneg hxs hys
      nlinarith
    · have hh := mul_le_mul hx.2
        (show -y≤69/200 by linarith [hy.1])
        (neg_nonneg.mpr (le_of_not_ge hys)) (by norm_num : (0:ℝ)≤19/10)
      nlinarith
  · by_cases hys : 0≤y
    · have hh := mul_le_mul (show -x≤567/500 by linarith [hx.1]) hy.2 hys
        (by norm_num : (0:ℝ)≤567/500)
      nlinarith
    · have hh := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hxs) (le_of_not_ge hys)
      nlinarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve
end
end
end
