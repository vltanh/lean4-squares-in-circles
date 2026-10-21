module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroOuterOwners

/-!
# Actual core-source negative zero-edge contacts

The original separator forces the angle below `.32`. The endpoint at
the largest core coordinate is the explicitly rotated circle contact
`(U-1/2,V-1/2)`. Its first derivatives and its speed derivative are proved
on the entire interval. Whenever an original pair is feasible, this
continued contact is on the actual canonical outer arc and precedes the
original outer state. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero.CoreContact

open CommonQuarter CorePairGeometry Arithmetic

def cap : ℝ := 8/25
def Z (x : ℝ) : ℝ := Real.cos x+1/2-CoreAngleEndpoint.diagonal
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def U (x : ℝ) : ℝ := Real.cos x*Y x-Real.sin x*Z x
def V (x : ℝ) : ℝ := Real.sin x*Y x+Real.cos x*Z x
def speed (x : ℝ) : ℝ := 1-Real.sin x/Y x
def speedD (x : ℝ) : ℝ :=
  (Z x*(Real.sin x)^2-Real.cos x*(Y x)^2)/(Y x)^3
def cutMargin (x : ℝ) : ℝ := CoreAngleEndpoint.diagonal-1/2+
  (outerDiagonal-1/2)*Real.cos x-(outerDiagonal+1/2)*Real.sin x

lemma cap_trig : (3932/12500:ℝ)<Real.sin cap ∧ Real.sin cap<31457/100000 ∧
    (94923/100000:ℝ)<Real.cos cap ∧ Real.cos cap<23731/25000 := by
  have hs := sin_lower_seven (x := cap) (by norm_num [cap])
  have hsU := sin_upper_five (x := cap) (by norm_num [cap])
  have hc := cos_lower_six (x := cap) (by norm_num [cap])
  have hcU := cos_upper_four (x := cap) (by norm_num [cap])
  norm_num [cap] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bounds {x : ℝ} (hx : x∈Icc 0 cap) :
    0≤Real.sin x ∧ Real.sin x<63/200 ∧ (949/1000:ℝ)<Real.cos x ∧ Real.cos x≤1 := by
  have hcap : cap∈Icc 0 (7/10) := by norm_num [cap]
  have hx' : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans hcap.2⟩
  have hs := sin_mono hx' hcap hx.2
  have hc := cos_anti hx' hcap hx.2
  exact ⟨(positive_trig hx').2.2.1,by linarith [cap_trig.2.1],
    by linarith [cap_trig.2.2.1],Real.cos_le_one x⟩

lemma cutMargin_antitone : AntitoneOn cutMargin (Icc 0 (7/10)) := by
  let d : ℝ → ℝ := fun x => -(outerDiagonal-1/2)*Real.sin x-
    (outerDiagonal+1/2)*Real.cos x
  have hd (x : ℝ) : HasDerivAt cutMargin (d x) x := by
    convert (((Real.hasDerivAt_cos x).const_mul (outerDiagonal-1/2)).const_add
      (CoreAngleEndpoint.diagonal-1/2)).sub
        ((Real.hasDerivAt_sin x).const_mul (outerDiagonal+1/2)) using 1 <;>
      dsimp [cutMargin,d] <;> ring
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (hd x).continuousAt.continuousWithinAt
  · exact fun x _ => hd x
  · intro x hx
    have ht := positive_trig (Ioo_subset_Icc_self hx)
    have h₁ := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) ht.2.2.1
    have h₂ := mul_nonneg (show 0≤outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1])
      (show 0≤Real.cos x by linarith [ht.1])
    dsimp [d]
    linarith

lemma cutMargin_cap_neg : cutMargin cap<0 := by
  have ht := cap_trig
  have hd := fine_diagonal_bounds
  have hc := CoreAngleEndpoint.diagonal_bounds
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.le
    (show 0≤outerDiagonal-1/2 by linarith [hd.1])
  have hsin := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤outerDiagonal+1/2 by linarith [hd.1])
  dsimp [cutMargin]
  nlinarith [hd.1,hd.2,hc.2]

theorem original_angle_cut {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) : x<cap := by
  have htr := positive_trig hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have htar := outer_bounds ht
  have hA := mul_le_mul_of_nonneg_right htar.1 htr.2.2.1
  have hB := mul_le_mul_of_nonneg_right htar.2.2.2.1 (show 0≤Real.cos x by linarith [htr.1])
  have hh : 0≤cutMargin x := by dsimp [cutMargin]; linarith
  by_contra! hlarge
  have hcap : cap∈Icc 0 (7/10) := by norm_num [cap]
  have hbad := cutMargin_antitone hcap hx hlarge
  linarith [cutMargin_cap_neg]

lemma Z_bounds {x : ℝ} (hx : x∈Icc 0 cap) : (89/100:ℝ)<Z x ∧ Z x<471/500 := by
  have ht := trig_bounds hx
  have hd := CoreAngleEndpoint.diagonal_bounds
  dsimp [Z]
  exact ⟨by linarith [ht.2.2.1,hd.2],by linarith [ht.2.2.2,hd.1]⟩

lemma radicand_pos {x : ℝ} (hx : x∈Icc 0 cap) : 0<Q0-(Z x)^2 := by
  have hz := Z_bounds hx
  norm_num [Q0]
  nlinarith

lemma Y_pos {x : ℝ} (hx : x∈Icc 0 cap) : 0<Y x := Real.sqrt_pos.mpr (radicand_pos hx)
lemma Y_sq {x : ℝ} (hx : x∈Icc 0 cap) : (Y x)^2+(Z x)^2=Q0 := by
  have hs := Real.sq_sqrt (radicand_pos hx).le
  dsimp [Y]
  linarith

lemma Y_bounds {x : ℝ} (hx : x∈Icc 0 cap) : (87/50:ℝ)<Y x ∧ Y x<177/100 := by
  have hy := Y_pos hx
  have hs := Y_sq hx
  have hz := Z_bounds hx
  norm_num [Q0] at hs
  constructor <;> nlinarith [hz.1,hz.2]

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (-Real.sin x) x := by
  simpa [Z] using ((Real.hasDerivAt_cos x).add_const (1/2)).sub_const CoreAngleEndpoint.diagonal

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt Y (Z x*Real.sin x/Y x) x := by
  have hh := ((hasDerivAt_const x Q0).sub ((Z_hasDerivAt x).pow 2)).sqrt (radicand_pos hx).ne'
  convert hh using 1 <;> dsimp [Y] <;> ring

lemma U_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt U (-V x*speed x) x := by
  have hn := (Y_pos hx).ne'
  have hh := ((Real.hasDerivAt_cos x).mul (Y_hasDerivAt hx)).sub
    ((Real.hasDerivAt_sin x).mul (Z_hasDerivAt x))
  convert hh using 1
  · rfl
  · dsimp [U,V,speed]
    field_simp [hn]
    ring

lemma V_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt V (U x*speed x) x := by
  have hn := (Y_pos hx).ne'
  have hh := ((Real.hasDerivAt_sin x).mul (Y_hasDerivAt hx)).add
    ((Real.hasDerivAt_cos x).mul (Z_hasDerivAt x))
  convert hh using 1
  · rfl
  · dsimp [U,V,speed]
    field_simp [hn]
    ring

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 cap) :
    HasDerivAt speed (speedD x) x := by
  have hn := (Y_pos hx).ne'
  have hh := ((Real.hasDerivAt_sin x).div (Y_hasDerivAt hx) hn).const_sub 1
  convert hh using 1
  · rfl
  · dsimp [speed,speedD]
    field_simp [hn]
    ring

lemma speed_pos {x : ℝ} (hx : x∈Icc 0 cap) : 0<speed x := by
  have ht := trig_bounds hx
  have hy := Y_bounds hx
  have hh : Real.sin x/Y x<1 := (div_lt_one (Y_pos hx)).2 (by linarith [ht.2.1,hy.1])
  dsimp [speed]
  linarith

lemma speedD_neg {x : ℝ} (hx : x∈Icc 0 cap) : speedD x<0 := by
  have ht := trig_bounds hx
  have hz := Z_bounds hx
  have hy := Y_bounds hx
  have hs2 := pow_le_pow_left₀ ht.1 ht.2.1.le 2
  have hy2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤87/50) hy.1.le 2
  have h₁ := mul_le_mul hz.2.le hs2 (sq_nonneg (Real.sin x)) (by norm_num)
  have h₂ := mul_le_mul ht.2.2.1.le hy2 (by positivity) (show 0≤Real.cos x by linarith [ht.2.2.1])
  apply div_neg_of_neg_of_pos _ (pow_pos (Y_pos hx) 3)
  nlinarith

lemma coarse_coordinates {x : ℝ} (hx : x∈Icc 0 cap) : (27/20:ℝ)<U x ∧ (21/25:ℝ)<V x := by
  have ht := trig_bounds hx
  have hz := Z_bounds hx
  have hy := Y_bounds hx
  have hcy := mul_le_mul ht.2.2.1.le hy.1.le (by norm_num) (show 0≤Real.cos x by linarith [ht.2.2.1])
  have hsz := mul_le_mul ht.2.1.le hz.2.le (show 0≤Z x by linarith [hz.1]) (by norm_num)
  have hcz := mul_le_mul ht.2.2.1.le hz.1.le (by norm_num) (show 0≤Real.cos x by linarith [ht.2.2.1])
  have hsy := mul_nonneg ht.1 (Y_pos hx).le
  dsimp [U,V]
  exact ⟨by nlinarith,by nlinarith⟩

lemma U_antitone : AntitoneOn U (Icc 0 cap) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (U_hasDerivAt hx).continuousAt.continuousWithinAt
  · exact fun x hx => U_hasDerivAt (Ioo_subset_Icc_self hx)
  · intro x hx
    have hh := coarse_coordinates (Ioo_subset_Icc_self hx)
    have hs := speed_pos (Ioo_subset_Icc_self hx)
    nlinarith [hh.2]

lemma V_monotone : MonotoneOn V (Icc 0 cap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x hx => (V_hasDerivAt hx).continuousAt.continuousWithinAt
  · exact fun x hx => V_hasDerivAt (Ioo_subset_Icc_self hx)
  · intro x hx
    exact mul_nonneg (by linarith [(coarse_coordinates (Ioo_subset_Icc_self hx)).1])
      (speed_pos (Ioo_subset_Icc_self hx)).le

lemma endpoint_root : (17671/10000:ℝ)<Y cap ∧ Y cap<17673/10000 := by
  have hcap : cap∈Icc 0 cap := by norm_num [cap]
  have hs := Y_sq hcap
  have hp := Y_pos hcap
  have ht := cap_trig
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hz : (8903/10000:ℝ)<Z cap ∧ Z cap<11129/12500 := by
    dsimp [Z]
    exact ⟨by linarith [ht.2.2.1,hd.2],by linarith [ht.2.2.2,hd.1]⟩
  norm_num [Q0] at hs
  constructor <;> nlinarith [hz.1,hz.2]

lemma endpoint_coordinates : (139/100:ℝ)<U cap ∧ U cap<7/5 ∧
    (7/5:ℝ)<V cap ∧ V cap<141/100 := by
  have ht := cap_trig
  have hy := endpoint_root
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hz : (89/100:ℝ)<Z cap ∧ Z cap<891/1000 := by
    dsimp [Z]
    exact ⟨by linarith [ht.2.2.1,hd.2],by linarith [ht.2.2.2,hd.1]⟩
  have hcyL := mul_le_mul ht.2.2.1.le hy.1.le (by norm_num) (by linarith [ht.2.2.1])
  have hcyU := mul_le_mul ht.2.2.2.le hy.2.le (by linarith [hy.1]) (by norm_num)
  have hszL := mul_le_mul ht.1.le hz.1.le (by norm_num) (by linarith [ht.1])
  have hszU := mul_le_mul ht.2.1.le hz.2.le (by linarith [hz.1]) (by norm_num)
  have hsyL := mul_le_mul ht.1.le hy.1.le (by norm_num) (by linarith [ht.1])
  have hsyU := mul_le_mul ht.2.1.le hy.2.le (by linarith [hy.1]) (by norm_num)
  have hczL := mul_le_mul ht.2.2.1.le hz.1.le (by norm_num) (by linarith [ht.2.2.1])
  have hczU := mul_le_mul ht.2.2.2.le hz.2.le (by linarith [hz.1]) (by norm_num)
  dsimp [U,V]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

lemma initial_coordinates : (87/50:ℝ)<U 0 ∧ U 0<7/4 ∧
    V 0=3/2-CoreAngleEndpoint.diagonal := by
  have h0 : (0:ℝ)∈Icc 0 cap := by norm_num [cap]
  have hp := Y_pos h0
  have hs := Y_sq h0
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hy : Y 0<(7/4:ℝ) := by
    norm_num [Z,Q0] at hs
    nlinarith [hd.1,hd.2]
  simpa [U,V,Z] using And.intro (Y_bounds h0).1 (And.intro hy (by ring : (3/2-CoreAngleEndpoint.diagonal:ℝ)=3/2-CoreAngleEndpoint.diagonal))

lemma coordinates {x : ℝ} (hx : x∈Icc 0 cap) :
    (139/100:ℝ)<U x ∧ U x<7/4 ∧ (47/50:ℝ)<V x ∧ V x<141/100 := by
  have huL := U_antitone hx (by norm_num [cap]) hx.2
  have huU := U_antitone (by norm_num [cap]) hx hx.1
  have hvL := V_monotone (by norm_num [cap]) hx hx.1
  have hvU := V_monotone hx (by norm_num [cap]) hx.2
  have he := endpoint_coordinates
  have h0 := initial_coordinates
  have hd := CoreAngleEndpoint.diagonal_bounds
  exact ⟨he.1.trans_le huL,huU.trans_lt h0.2.1,
    by linarith [h0.2.2,hd.2],hvU.trans_lt he.2.2.2⟩

lemma circle {x : ℝ} (hx : x∈Icc 0 cap) : (U x)^2+(V x)^2=Q0 := by
  have hid : (U x)^2+(V x)^2=((Real.sin x)^2+(Real.cos x)^2)*((Y x)^2+(Z x)^2) := by
    dsimp [U,V]
    ring
  rw [hid,Real.sin_sq_add_cos_sq,one_mul,Y_sq hx]

lemma contact_equation (x : ℝ) :
    (V x-1/2)*Real.cos x-(U x-1/2)*Real.sin x=
      (1+Real.sin x+Real.cos x)/2-CoreAngleEndpoint.diagonal := by
  have hid : V x*Real.cos x-U x*Real.sin x=Z x := by
    dsimp [V,U]
    linear_combination (Z x)*(Real.sin_sq_add_cos_sq x)
  dsimp [Z] at hid
  linarith

/-- The exact contact belongs to the physical outer arc whenever the
original pair is feasible, and lies before the original outer point. -/
theorem original_contact {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 cap)
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    OuterState (U x-1/2) (V x-1/2) ∧ V x-1/2≤B := by
  have hc := coordinates hx
  have htr := trig_bounds hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have he := circle hx
  have hcontact := contact_equation x
  have hB : V x-1/2≤B := by
    by_contra! hbad
    have hA : U x-1/2<A := by
      by_contra! hnot
      have hp : 0≤A+1/2 := by linarith [ht.1,ht.2.1]
      have hsA := pow_le_pow_left₀ hp (show A+1/2≤U x by linarith) 2
      have hsB := mul_pos (show 0<V x-(B+1/2) by linarith)
        (show 0<V x+(B+1/2) by linarith [hc.2.2.1,ht.1])
      nlinarith [ht.2.2]
    have hprim := mul_le_mul_of_nonneg_right hA.le htr.1
    have hsec := mul_lt_mul_of_pos_right hbad (show 0<Real.cos x by linarith [htr.2.2.1])
    linarith
  have hBm : V x≤outerDiagonal+1/2 := by linarith [(outer_bounds ht).2.2.2.1]
  have hVsq := pow_le_pow_left₀ (show 0≤V x by linarith [hc.2.2.1]) hBm 2
  have hUV : V x≤U x := by
    nlinarith [diagonal_circle,hc.1,hc.2.2.1]
  exact ⟨⟨by linarith [hc.2.2.1],by linarith,by nlinarith⟩,hB⟩

end SquaresInCircles.Eight.TableFree.ShortMixedZero.CoreContact
