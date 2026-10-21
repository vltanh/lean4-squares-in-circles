module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroPositiveCore

/-!
# The actual zero-source contact for two negative mixed states

The original weak axis forces the angle above `.30243`. The continued
zero-source contact is written in rotated circle coordinates on the
entire interval up to `.7`. Its speed and speed derivative are positive,
so its first coordinate increases and its second decreases. Whenever
an original pair is feasible, the contact lies on the actual outer arc
before that target. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero.NegativeContact

open CommonQuarter CorePairGeometry Arithmetic

def start : ℝ := 30243/100000
def m (x : ℝ) : ℝ := Real.sin x+Real.cos x
def n (x : ℝ) : ℝ := Real.cos x-Real.sin x
def Z (x : ℝ) : ℝ := 1/2+m x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def U (x : ℝ) : ℝ := Z x*Real.sin x+Y x*Real.cos x
def V (x : ℝ) : ℝ := Z x*Real.cos x-Y x*Real.sin x
def speed (x : ℝ) : ℝ := 1-n x/Y x
def speedD (x : ℝ) : ℝ :=
  (m x*(Q0-9/4)-(m x)^2/2-1)/(Y x)^3
def cut (x : ℝ) : ℝ := (outerDiagonal-1/2)*m x-1/2

lemma start_trig : (2978407/10000000:ℝ)<Real.sin start ∧
    Real.sin start<2978409/10000000 ∧
    (1909231/2000000:ℝ)<Real.cos start ∧ Real.cos start<11932695/12500000 := by
  have hs := sin_lower_seven (x := start) (by norm_num [start])
  have hu := sin_upper_five (x := start) (by norm_num [start])
  have hc := cos_lower_six (x := start) (by norm_num [start])
  have hk := cos_le_cos8 (x := start) (by norm_num [start])
  norm_num [start,cos8] at hs hu hc hk
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma m_hasDerivAt (x : ℝ) : HasDerivAt m (n x) x := by
  simpa [m,n,sub_eq_add_neg] using (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
lemma n_hasDerivAt (x : ℝ) : HasDerivAt n (-m x) x := by
  convert (Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x) using 1 <;> dsimp [m,n] <;> ring

lemma n_pos {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<n x := by
  have ht := positive_trig hx
  dsimp [n]
  linarith [ht.1,ht.2.2.2.1]

lemma m_monotone : MonotoneOn m (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg (fun x _ => (m_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => m_hasDerivAt x) (fun x hx => (n_pos (Ioo_subset_Icc_self hx)).le)

lemma cut_start_neg : cut start<0 := by
  have hd := fine_diagonal_bounds
  have ht := start_trig
  have hm : m start<(2504913/2000000:ℝ) := by dsimp [m]; linarith [ht.2.1,ht.2.2.2]
  have hh := mul_le_mul_of_nonneg_left hm.le
    (show 0≤outerDiagonal-1/2 by linarith [hd.1])
  dsimp [cut]
  nlinarith [hd.2]

lemma original_angle {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) : start<φ := by
  have hp := negative_secondary_positive_angle (Or.inr hs) ht hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  have hproj := outer_diagonal_upper ht tr.2.2.1
    (show Real.sin φ≤Real.cos φ by linarith [n_pos hx])
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  have hcut : 0≤cut φ := by dsimp [cut,m]; nlinarith
  by_contra! hn
  have hstart : start∈Icc 0 (7/10) := by norm_num [start]
  have hmono := m_monotone hx hstart hn
  have hh := mul_le_mul_of_nonneg_left hmono
    (show 0≤outerDiagonal-1/2 by linarith [fine_diagonal_bounds.1])
  have hsneg := cut_start_neg
  dsimp [cut] at hcut hsneg
  linarith

lemma phase_bounds {x : ℝ} (hx : x∈Icc start (7/10)) :
    (313/250:ℝ)<m x ∧ m x<141/100 ∧ 0<n x := by
  have hx' : x∈Icc 0 (7/10) := ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩
  have hl := m_monotone (by norm_num [start]) hx' hx.1
  have hu := m_monotone hx' (by norm_num) hx.2
  have hs := start_trig
  have he := CommonQuarter.cap_trig
  refine ⟨?_,?_,n_pos hx'⟩
  · dsimp [m] at hl
    linarith [hs.1,hs.2.2.1]
  · dsimp [m] at hu
    linarith [he.2.1,he.2.2.2]

lemma Y_pos {x : ℝ} (hx : x∈Icc start (7/10)) : 0<Y x := by
  have hb := phase_bounds hx
  apply Real.sqrt_pos.mpr
  dsimp [Z]
  norm_num [Q0]
  nlinarith [hb.1,hb.2.1]

lemma circle_base {x : ℝ} (hx : x∈Icc start (7/10)) : (Y x)^2+(Z x)^2=Q0 := by
  have hp := (Real.sqrt_pos.mp (Y_pos hx)).le
  have hs := Real.sq_sqrt hp
  dsimp [Y]
  linarith

lemma Y_bounds {x : ℝ} (hx : x∈Icc start (7/10)) : (1/2:ℝ)<Y x ∧ Y x<921/1000 := by
  have he := circle_base hx
  have hy := Y_pos hx
  have hb := phase_bounds hx
  dsimp [Z] at he
  norm_num [Q0] at he
  constructor <;> nlinarith [hb.1,hb.2.1]

lemma phase_circle (x : ℝ) : (m x)^2+(n x)^2=2 := by
  dsimp [m,n]
  linear_combination 2*(Real.sin_sq_add_cos_sq x)

lemma speed_pos {x : ℝ} (hx : x∈Icc start (7/10)) : 0<speed x := by
  have he := circle_base hx
  have hc := phase_circle x
  have hp := phase_bounds hx
  have hy := Y_pos hx
  have hdiff : (n x)^2<(Y x)^2 := by
    dsimp [Z] at he
    norm_num [Q0] at he
    nlinarith [hp.2.1]
  have hny : n x<Y x := by nlinarith [hp.2.2]
  have hh := (div_lt_one hy).2 hny
  dsimp [speed]
  linarith

lemma speedD_pos {x : ℝ} (hx : x∈Icc start (7/10)) : 0<speedD x := by
  have hp := phase_bounds hx
  apply div_pos _ (pow_pos (Y_pos hx) 3)
  norm_num [Q0]
  have hs := mul_nonneg (show 0≤m x-313/250 by linarith [hp.1])
    (show 0≤141/100-m x by linarith [hp.2.1])
  nlinarith [hp.1,hp.2.1]

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt Y (-Z x*n x/Y x) x := by
  have hz := (m_hasDerivAt x).const_add (1/2)
  have hp : 0<Q0-(Z x)^2 := Real.sqrt_pos.mp (Y_pos hx)
  have hh := ((hasDerivAt_const x Q0).sub (hz.pow 2)).sqrt hp.ne'
  convert hh using 1 <;> dsimp [Y,Z] <;> ring

lemma U_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt U (V x*speed x) x := by
  have hz := (m_hasDerivAt x).const_add (1/2)
  have hh := (hz.mul (Real.hasDerivAt_sin x)).add ((Y_hasDerivAt hx).mul (Real.hasDerivAt_cos x))
  convert hh using 1
  · rfl
  · dsimp [U,V,speed,n]
    field_simp [(Y_pos hx).ne']
    ring

lemma V_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt V (-U x*speed x) x := by
  have hz := (m_hasDerivAt x).const_add (1/2)
  have hh := (hz.mul (Real.hasDerivAt_cos x)).sub ((Y_hasDerivAt hx).mul (Real.hasDerivAt_sin x))
  convert hh using 1
  · rfl
  · dsimp [U,V,speed,n]
    field_simp [(Y_pos hx).ne']
    ring

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt speed (speedD x) x := by
  have hh := ((n_hasDerivAt x).div (Y_hasDerivAt hx) (Y_pos hx).ne').const_sub 1
  have he := circle_base hx
  have hc := phase_circle x
  convert hh using 1
  · rfl
  · dsimp [speedD]
    field_simp [(Y_pos hx).ne']
    dsimp [Z] at he ⊢
    linear_combination (m x)*he-(1/2+m x)*hc

lemma coarse_coordinates {x : ℝ} (hx : x∈Icc start (7/10)) : 0<U x ∧ 0<V x := by
  have hp := phase_bounds hx
  have hy := Y_bounds hx
  have tr := positive_trig (show x∈Icc 0 (7/10) from
    ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩)
  have hz : (219/125:ℝ)<Z x := by dsimp [Z]; linarith [hp.1]
  have hzs := mul_nonneg (by linarith : 0≤Z x) tr.2.2.1
  have hyc := mul_pos (Y_pos hx) (show 0<Real.cos x by linarith [tr.1])
  have hzc := mul_le_mul hz.le (show (191/250:ℝ)≤Real.cos x by linarith [tr.1])
    (by norm_num) (by linarith)
  have hys := mul_le_mul hy.2.le tr.2.2.2.1.le tr.2.2.1 (by norm_num)
  dsimp [U,V]
  exact ⟨by linarith,by nlinarith⟩

lemma U_monotone : MonotoneOn U (Icc start (7/10)) :=
  monoOn_of_hasDeriv_nonneg (fun x hx => (U_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => U_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => mul_nonneg (coarse_coordinates (Ioo_subset_Icc_self hx)).2.le
      (speed_pos (Ioo_subset_Icc_self hx)).le)

lemma V_antitone : AntitoneOn V (Icc start (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (V_hasDerivAt hx).continuousAt.continuousWithinAt
  · exact fun x hx => V_hasDerivAt (Ioo_subset_Icc_self hx)
  · intro x hx
    have hh := mul_nonneg (coarse_coordinates (Ioo_subset_Icc_self hx)).1.le
      (speed_pos (Ioo_subset_Icc_self hx)).le
    linarith

lemma endpoint_coordinates :
    (1749/1250:ℝ)<U start ∧ U start<13993/10000 ∧
    (1749/1250:ℝ)<V start ∧ V start<13993/10000 ∧
    U (7/10)<1629/1000 ∧ (281/250:ℝ)<V (7/10) := by
  have hstart : start∈Icc start (7/10) := by norm_num [start]
  have hend : (7/10:ℝ)∈Icc start (7/10) := by norm_num [start]
  have ts := start_trig
  have te := CommonQuarter.cap_trig
  have zs : (8762281/5000000:ℝ)<Z start ∧ Z start<3504913/2000000 := by
    dsimp [Z,m]
    exact ⟨by linarith [ts.1,ts.2.2.1],by linarith [ts.2.1,ts.2.2.2]⟩
  have ze : (23863/12500:ℝ)<Z (7/10) ∧ Z (7/10)<477271/250000 := by
    dsimp [Z,m]
    exact ⟨by linarith [te.1,te.2.2.1],by linarith [te.2.1,te.2.2.2]⟩
  have ys : (11487/12500:ℝ)<Y start ∧ Y start<91897/100000 := by
    have he := circle_base hstart
    have hp := Y_pos hstart
    norm_num [Q0] at he
    constructor <;> nlinarith [zs.1,zs.2]
  have ye : (1041/2000:ℝ)<Y (7/10) ∧ Y (7/10)<651/1250 := by
    have he := circle_base hend
    have hp := Y_pos hend
    norm_num [Q0] at he
    constructor <;> nlinarith [ze.1,ze.2]
  have zsSL := mul_le_mul zs.1.le ts.1.le (by norm_num) (by linarith [zs.1])
  have zsSU := mul_le_mul zs.2.le ts.2.1.le (by linarith [ts.1]) (by norm_num)
  have ysCL := mul_le_mul ys.1.le ts.2.2.1.le (by norm_num) (by linarith [ys.1])
  have ysCU := mul_le_mul ys.2.le ts.2.2.2.le (by linarith [ts.2.2.1]) (by norm_num)
  have zsCL := mul_le_mul zs.1.le ts.2.2.1.le (by norm_num) (by linarith [zs.1])
  have zsCU := mul_le_mul zs.2.le ts.2.2.2.le (by linarith [ts.2.2.1]) (by norm_num)
  have ysSL := mul_le_mul ys.1.le ts.1.le (by norm_num) (by linarith [ys.1])
  have ysSU := mul_le_mul ys.2.le ts.2.1.le (by linarith [ts.1]) (by norm_num)
  have zeSU := mul_le_mul ze.2.le te.2.1.le (by linarith [te.1]) (by norm_num)
  have yeCU := mul_le_mul ye.2.le te.2.2.2.le (by linarith [te.2.2.1]) (by norm_num)
  have zeCL := mul_le_mul ze.1.le te.2.2.1.le (by norm_num) (by linarith [ze.1])
  have yeSU := mul_le_mul ye.2.le te.2.1.le (by linarith [te.1]) (by norm_num)
  dsimp [U,V]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

lemma coordinates {x : ℝ} (hx : x∈Icc start (7/10)) :
    (1399/1000:ℝ)<U x ∧ U x<1629/1000 ∧ (281/250:ℝ)<V x ∧ V x<7/5 := by
  have huL := U_monotone (by norm_num [start]) hx hx.1
  have huU := U_monotone hx (by norm_num [start]) hx.2
  have hvL := V_antitone hx (by norm_num [start]) hx.2
  have hvU := V_antitone (by norm_num [start]) hx hx.1
  have he := endpoint_coordinates
  exact ⟨by linarith [he.1],huU.trans_lt he.2.2.2.2.1,
    he.2.2.2.2.2.trans_le hvL,by linarith [he.2.2.2.1]⟩

lemma circle {x : ℝ} (hx : x∈Icc start (7/10)) : (U x)^2+(V x)^2=Q0 := by
  have hid : (U x)^2+(V x)^2=((Z x)^2+(Y x)^2)*((Real.sin x)^2+(Real.cos x)^2) := by
    dsimp [U,V]
    ring
  rw [hid,Real.sin_sq_add_cos_sq,mul_one]
  linarith [circle_base hx]

lemma contact_equation (x : ℝ) :
    (U x-1/2)*Real.sin x+(V x-1/2)*Real.cos x=(1+Real.sin x+Real.cos x)/2 := by
  have hh : U x*Real.sin x+V x*Real.cos x=Z x := by
    dsimp [U,V]
    linear_combination (Z x)*(Real.sin_sq_add_cos_sq x)
  dsimp [Z,m] at hh
  linarith

theorem original_contact {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc start (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤-b+A*Real.sin x+B*Real.cos x) :
    OuterState (U x-1/2) (V x-1/2) ∧ V x-1/2≤B := by
  have tr := positive_trig (show x∈Icc 0 (7/10) from
    ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩)
  let P := (A+1/2)*Real.sin x+(B+1/2)*Real.cos x
  let T := (A+1/2)*Real.cos x-(B+1/2)*Real.sin x
  have hP : Z x≤P := by
    dsimp [P,Z,m]
    linarith [(CoreAngleEndpoint.state_bounds hs).2.2.1]
  have hT : 0≤T := by
    have hp := mul_nonneg (show 0≤A-B by linarith [ht.2.1])
      (show 0≤Real.cos x by linarith [tr.1])
    have hq := mul_nonneg (show 0≤B+1/2 by linarith [ht.1])
      (show 0≤Real.cos x-Real.sin x by linarith [tr.1,tr.2.2.2.1])
    dsimp [T]
    nlinarith
  have hc : P^2+T^2=Q0 := by
    dsimp [P,T]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hZ : 0≤Z x := by dsimp [Z]; linarith [(phase_bounds hx).1]
  have hPsq := pow_le_pow_left₀ hZ hP 2
  have hTy : T≤Y x := by nlinarith [circle_base hx,Y_pos hx]
  have hpc := mul_le_mul_of_nonneg_right hP (show 0≤Real.cos x by linarith [tr.1])
  have hts := mul_le_mul_of_nonneg_right hTy tr.2.2.1
  have hid : P*Real.cos x-T*Real.sin x=B+1/2 := by
    dsimp [P,T]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)
  have hB : V x-1/2≤B := by dsimp [V]; linarith
  have hco := coordinates hx
  have he := circle hx
  have hVm : V x≤outerDiagonal+1/2 := by linarith [(outer_bounds ht).2.2.2.1]
  have hVsq := pow_le_pow_left₀ (show 0≤V x by linarith [hco.2.2.1]) hVm 2
  have hUV : V x≤U x := by nlinarith [diagonal_circle,hco.1,hco.2.2.1]
  exact ⟨⟨by linarith [hco.2.2.1],by linarith,by nlinarith⟩,hB⟩

end SquaresInCircles.Eight.TableFree.ShortMixedZero.NegativeContact
