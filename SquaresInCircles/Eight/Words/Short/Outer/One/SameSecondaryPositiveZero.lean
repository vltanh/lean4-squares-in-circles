module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryPositiveGeometry

/-!
# Eight squares: the moving zero-source boundary of the secondary strip

The original target circle supplies an explicit rotating coordinate.
Its derivative is precisely the same positive transport derivative as
an interior stationary target.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive.Zero
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open SecondWord (U W)

def Z (x : ℝ) : ℝ := 1/2+Real.cos x+Real.sin x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Z x*Real.cos x-Y x*Real.sin x
def vertical (x : ℝ) : ℝ := Z x*Real.sin x+Y x*Real.cos x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-(Real.cos x-Real.sin x)/Y x
def value (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2+x+c r+target r 0+targetCost r (height x)
def first (r : Row) (x : ℝ) : ℝ :=
  1-targetSlope r (height x)*horizontal x*factor x

lemma radical_data {x : ℝ} (hx : x∈Icc 0 strip) :
    0<Y x ∧ (Y x)^2+(Z x)^2=Q0 := by
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have hz : (3/2:ℝ)≤Z x ∧ Z x≤201/125 := by
    dsimp [Z]
    constructor <;> linarith [hf.2.2.2.2.2,hf.2.1,ht.2.2.1]
  have hr : 0<Q0-(Z x)^2 := by norm_num [Q0]; nlinarith
  exact ⟨Real.sqrt_pos.mpr hr,by dsimp [Y]; linarith [Real.sq_sqrt hr.le]⟩

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (Real.cos x-Real.sin x) x := by
  have h := ((Real.hasDerivAt_cos x).const_add (1/2)).add (Real.hasDerivAt_sin x)
  convert h using 1
  · funext y; simp only [Z,Pi.add_apply]
  · ring

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt Y (-Z x*(Real.cos x-Real.sin x)/Y x) x := by
  have hy := radical_data hx
  have hr : Q0-(Z x)^2≠0 := by nlinarith [hy.1,hy.2]
  have h := (((Z_hasDerivAt x).pow 2).const_sub Q0).sqrt hr
  convert h using 1
  · rfl
  change _=-(((2:ℕ):ℝ)*Z x^(2-1)*(Real.cos x-Real.sin x))/(2*Y x)
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
  field_simp

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt height (horizontal x*factor x) x := by
  have hy := (radical_data hx).1
  have h := (((Z_hasDerivAt x).mul (Real.hasDerivAt_sin x)).add
    ((Y_hasDerivAt hx).mul (Real.hasDerivAt_cos x))).sub_const (1/2)
  convert h using 1
  · funext y; simp only [height,vertical,Pi.add_apply,Pi.mul_apply]
  · simp only [horizontal,factor]; field_simp; ring

lemma original_coordinates {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 strip)
    (he : 1/2+(1/2-A)*Real.cos x+(1/2-B)*Real.sin x=0) :
    horizontal x=A+1/2 ∧ vertical x=B+1/2 := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hD := (D_bounds hB hx).1
  have hD' : 0<(B+1/2)*Real.cos x-(A+1/2)*Real.sin x := by
    dsimp [D,U,W] at hD
    rw [(SameContact.actual_arc ht).1] at hD
    linarith
  have hZ : Z x=(A+1/2)*Real.cos x+(B+1/2)*Real.sin x := by
    dsimp [Z]
    linarith
  have hcircle : ((B+1/2)*Real.cos x-(A+1/2)*Real.sin x)^2+(Z x)^2=Q0 := by
    rw [hZ]
    linear_combination ht.2.2+
      ((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=(B+1/2)*Real.cos x-(A+1/2)*Real.sin x := by
    have hr := radical_data hx
    nlinarith [hr.1,hr.2]
  constructor
  · dsimp [horizontal]
    rw [hZ,hY]
    linear_combination (A+1/2)*(Real.sin_sq_add_cos_sq x)
  · dsimp [vertical]
    rw [hZ,hY]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

lemma exists_target {x : ℝ} (hx : x∈Icc 0 strip) :
    ∃B,B∈Icc 0 outerDiagonal ∧ contact B x=0 := by
  have hc : Continuous (fun B => contact B x) := by dsimp [contact,arc]; fun_prop
  exact intermediate_value_Icc (show (0:ℝ)≤outerDiagonal by linarith [outer_endpoint_bounds.2.2.1])
    hc.continuousOn (show (0:ℝ)∈Icc (contact 0 x) (contact outerDiagonal x) from
      ⟨(contact_zero_target hx).le,(contact_target_diagonal hx).1.le⟩)

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

lemma value_cost {x : ℝ} (hx : x∈Icc 0 strip) (r : Row) : value r x=cost r (height x) x := by
  dsimp [value,cost]
  rw [(physical hx).2.1]

lemma first_transport {x : ℝ} (hx : x∈Icc 0 strip) (r : Row) :
    first r x=transport r (height x) x := by
  have hp := physical hx
  have hH := H_identity hp.1 r
  rw [hp.2.2] at hH
  dsimp [first,factor,transport]
  rw [actual_D hx]
  nlinarith only [congrArg (fun z : ℝ => z*(1-(Real.cos x-Real.sin x)/Y x)) hH]

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) (r : Row) :
    HasDerivAt (value r) (first r x) x := by
  have h := ((hasDerivAt_id x).const_add (Real.pi/2+c r+target r 0)).add
    ((targetCost_hasDerivAt r (physical hx).1).comp x (height_hasDerivAt hx))
  convert h using 1
  · funext y; simp only [value,Pi.add_apply,Function.comp_apply,id_eq]; ring
  · simp only [first]; ring

theorem value_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 strip) : (8981/10000:ℝ)<value r x := by
  have hm : MonotoneOn (value r) (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (value_hasDerivAt hy r).continuousAt.continuousWithinAt)
    (fun y hy => value_hasDerivAt (Ioo_subset_Icc_self hy) r)
    (fun y hy => by
      rw [first_transport (Ioo_subset_Icc_self hy)]
      linarith [transport_lower r (physical (Ioo_subset_Icc_self hy)).1 (Ioo_subset_Icc_self hy)])
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  have hp := physical h0
  have hv := initial_lower r (show Domain (height 0) 0 from ⟨hp.1,h0,hp.2.1.ge⟩)
  rw [←value_cost h0 r] at hv
  exact hv.trans_le (hm h0 hx hx.1)

theorem original_lower (r : Row) {B x : ℝ} (hd : Domain B x) (he : contact B x=0) :
    (8981/10000:ℝ)<cost r B x := by
  have hh := value_lower r hd.2.1
  rw [value_cost hd.2.1 r,actual_height hd he] at hh
  exact hh

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive.Zero
