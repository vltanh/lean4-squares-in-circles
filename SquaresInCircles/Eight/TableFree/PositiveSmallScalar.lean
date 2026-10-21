module

public import SquaresInCircles.Eight.TableFree.SmallPositiveZeroEndpoint
public import SquaresInCircles.Eight.TableFree.PositiveNoncancelingOuter

/-!
# Strict convexity of the positive small-side scalar at the source circle

Uncompiled source draft.  The middle point need only be contained in q;
it is not raised to that circle.  Consequently T can slightly exceed one.
The bounds T≤1.08 and 1−2VT/W≥4999/47875 still give F''≥3/50
on the complete feasible interval.  This allows the eventual alignment
to decrease the original A primary and retain every original circle loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveSmallScalar

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
  convert ((Real.hasDerivAt_cos z).const_mul P).sub
    ((Real.hasDerivAt_sin z).const_mul Y) using 1 <;> dsimp [V,U] <;> ring

theorem U_hasDerivAt (P Y z : ℝ) : HasDerivAt (U P Y) (V P Y z) z := by
  convert ((Real.hasDerivAt_sin z).const_mul P).add
    ((Real.hasDerivAt_cos z).const_mul Y) using 1 <;> dsimp [V,U] <;> ring

theorem W_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(V P Y z)^2) :
    HasDerivAt (W q P Y) (V P Y z*U P Y z/W q P Y z) z := by
  have hw : W q P Y z≠0 := (Real.sqrt_pos.2 hr).ne'
  have hh := (((V_hasDerivAt P Y z).pow 2).const_sub q).sqrt hr.ne'
  convert hh using 1
  · rfl
  · dsimp [W]
    field_simp [show Real.sqrt (q-(V P Y z)^2)≠0 from hw]
    ring

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
  have ht := (T_hasDerivAt hr).comp h ((hasDerivAt_id h).const_add Θ)
  convert (((Real.hasDerivAt_sin h).mul (ht.sub_const 1)).add_const 1).sub
    (Real.hasDerivAt_cos h) using 1 <;> dsimp [F,F1] <;> ring

theorem F1_hasDerivAt {q P Y Θ h : ℝ} (hr : 0<q-(V P Y (Θ+h))^2) :
    HasDerivAt (F1 q P Y Θ) (F2 q P Y Θ h) h := by
  have ht := (T_hasDerivAt hr).comp h ((hasDerivAt_id h).const_add Θ)
  have ht1 := (T1_hasDerivAt hr).comp h ((hasDerivAt_id h).const_add Θ)
  convert ((Real.hasDerivAt_cos h).mul (ht.sub_const 1)).add
    ((Real.hasDerivAt_sin h).mul (ht1.add_const 1)) using 1 <;>
    dsimp [F1,F2] <;> ring

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
  have hcoef : 4999/47875≤1+2*T1 q P Y z := by dsimp [T1]; linarith
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
    nlinarith [Real.one_sub_sq_div_two_le_cos h,pow_le_pow_left₀ hh.1 hh.2 2]
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

end SquaresInCircles.Eight.TableFree.PositiveSmallScalar
