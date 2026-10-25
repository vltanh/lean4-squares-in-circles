module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryFirstStrip

/-!
# The zero-source boundary of the first negative secondary strip

Uncompiled transcription of the moving boundary in Section 5 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
The target coordinates come from the exact original target circle.
Their derivative gives precisely transport formula (21), so this whole
boundary increases from its aligned endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.FirstStrip.Zero
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open SecondWord (U W)

def Z (x : ℝ) : ℝ := 1/2+Real.cos x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Z x*Real.cos x+Y x*Real.sin x
def vertical (x : ℝ) : ℝ := Y x*Real.cos x-Z x*Real.sin x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-Real.sin x/Y x
def value (x : ℝ) : ℝ := Real.pi/2-x+c 0+target 0 0+targetCost 0 (height x)
def first (x : ℝ) : ℝ := -1+targetSlope 0 (height x)*horizontal x*factor x

lemma radical_data {x : ℝ} (hx : x∈Icc 0 strip) :
    0<Y x ∧ (Y x)^2+(Z x)^2=Q0 := by
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have hz : 0<Z x ∧ Z x≤3/2 := by dsimp [Z]; constructor <;> linarith [ht.1,hf.2.1]
  have hr : 0<Q0-(Z x)^2 := by norm_num [Q0]; nlinarith
  exact ⟨Real.sqrt_pos.mpr hr,by dsimp [Y]; linarith [Real.sq_sqrt hr.le]⟩

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (-Real.sin x) x :=
  (Real.hasDerivAt_cos x).const_add (1/2)

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt Y (Z x*Real.sin x/Y x) x := by
  have hy := radical_data hx
  have hr : Q0-(Z x)^2≠0 := by nlinarith [hy.1,hy.2]
  have h := (((Z_hasDerivAt x).pow 2).const_sub Q0).sqrt hr
  convert h using 1
  · rfl
  change _=-(((2:ℕ):ℝ)*Z x^(2-1)*(-Real.sin x))/(2*Y x)
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
  field_simp

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt height (-horizontal x*factor x) x := by
  have hy := (radical_data hx).1
  have h := (((Y_hasDerivAt hx).mul (Real.hasDerivAt_cos x)).sub
    ((Z_hasDerivAt x).mul (Real.hasDerivAt_sin x))).sub_const (1/2)
  convert h using 1
  · funext y; simp only [height,vertical,Pi.sub_apply,Pi.mul_apply]
  · simp only [horizontal,factor]; field_simp; ring

lemma original_coordinates {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 strip)
    (he : 1/2+(1/2-A)*Real.cos x+(1/2+B)*Real.sin x=0) :
    horizontal x=A+1/2 ∧ vertical x=B+1/2 := by
  let T : ℝ := (A+1/2)*Real.sin x+(B+1/2)*Real.cos x
  have htr := strip_trig hx
  have hT : 0<T := by
    have hs := mul_nonneg (show 0≤A+1/2 by linarith [ht.1,ht.2.1]) htr.2.1
    have hc := mul_pos (show 0<B+1/2 by linarith [ht.1])
      (show 0<Real.cos x by linarith [htr.1])
    dsimp [T]
    linarith
  have hZ : Z x=(A+1/2)*Real.cos x-(B+1/2)*Real.sin x := by dsimp [Z]; linarith
  have hcircle : T^2+(Z x)^2=Q0 := by
    rw [hZ]
    dsimp [T]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=T := by
    have hr := radical_data hx
    nlinarith [hr.1,hr.2]
  constructor
  · dsimp [horizontal]
    rw [hY,hZ]
    dsimp [T]
    linear_combination (A+1/2)*(Real.sin_sq_add_cos_sq x)
  · dsimp [vertical]
    rw [hY,hZ]
    dsimp [T]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

lemma exists_target {x : ℝ} (hx : x∈Icc 0 strip) :
    ∃B,B∈Icc 0 outerDiagonal ∧ contact B x=0 := by
  have hB : (7/20:ℝ)∈Icc 0 outerDiagonal :=
    ⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hm := contact_angle_monotone hB (angle_full hx)
    (show strip∈Icc 0 (7/10) by norm_num [strip]) hx.2
  have hc : Continuous (fun B => contact B x) := by dsimp [contact,arc]; fun_prop
  obtain ⟨B,hB',he⟩ := intermediate_value_Icc hB.2 hc.continuousOn
    (show (0:ℝ)∈Icc (contact (7/20) x) (contact outerDiagonal x) from
      ⟨(hm.trans_lt fixed_contact_negative).le,(contact_target_diagonal hx).1.le⟩)
  exact ⟨B,⟨hB.1.trans hB'.1,hB'.2⟩,he⟩

lemma physical {x : ℝ} (hx : x∈Icc 0 strip) :
    height x∈Icc 0 outerDiagonal ∧ contact (height x) x=0 ∧ U (height x)=horizontal x := by
  obtain ⟨B,hB,he⟩ := exists_target hx
  have hh := original_coordinates (SameContact.arc_state hB) hx (by simpa [contact] using he)
  have hheight : height x=B := by dsimp [height]; linarith [hh.2]
  rw [hheight]
  exact ⟨hB,he,by dsimp [U]; linarith [hh.1]⟩

lemma actual_height {B x : ℝ} (hd : Domain B x) (he : contact B x=0) : height x=B := by
  have hh := original_coordinates (SameContact.arc_state hd.1) hd.2.1 (by simpa [contact] using he)
  dsimp [height]
  linarith [hh.2]

lemma actual_D {x : ℝ} (hx : x∈Icc 0 strip) : D (height x) x=Y x := by
  have hp := physical hx
  dsimp [D,W]
  rw [hp.2.2]
  dsimp [height,horizontal,vertical]
  linear_combination Y x*(Real.sin_sq_add_cos_sq x)

lemma value_cost {x : ℝ} (hx : x∈Icc 0 strip) : value x=Negative.cost 0 (height x) x := by
  dsimp [value,Negative.cost]
  rw [(physical hx).2.1]

lemma first_transport {x : ℝ} (hx : x∈Icc 0 strip) : first x=transport (height x) x := by
  have hp := physical hx
  have hH := H_identity hp.1
  rw [hp.2.2] at hH
  dsimp [first,factor,transport]
  rw [actual_D hx]
  nlinarith only [congrArg (fun z : ℝ => z*(1-Real.sin x/Y x)) hH]

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) : HasDerivAt value (first x) x := by
  have h := (((hasDerivAt_id x).neg).const_add (Real.pi/2+c 0+target 0 0)).add
    ((targetCost_hasDerivAt 0 (physical hx).1).comp x (height_hasDerivAt hx))
  convert h using 1
  · funext y; simp only [value,Pi.add_apply,Pi.neg_apply,Function.comp_apply,id_eq]; ring
  · simp only [first]; ring

theorem value_lower {x : ℝ} (hx : x∈Icc 0 strip) : (8981/10000:ℝ)<value x := by
  have hm : MonotoneOn value (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (value_hasDerivAt hy).continuousAt.continuousWithinAt)
    (fun y hy => value_hasDerivAt (Ioo_subset_Icc_self hy))
    (fun y hy => by
      have hys := Ioo_subset_Icc_self hy
      have hp := physical hys
      rw [first_transport hys]
      exact (transport_positive (show Domain (height y) y from ⟨hp.1,hys,hp.2.1.ge⟩)).le)
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  have hp := physical h0
  have hv := initial_lower (show Domain (height 0) 0 from ⟨hp.1,h0,hp.2.1.ge⟩)
  rw [←value_cost h0] at hv
  exact hv.trans_le (hm h0 hx hx.1)

theorem original_lower {B x : ℝ} (hd : Domain B x) (he : contact B x=0) :
    (8981/10000:ℝ)<Negative.cost 0 B x := by
  have hh := value_lower hd.2.1
  rw [value_cost hd.2.1,actual_height hd he] at hh
  exact hh

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.FirstStrip.Zero
