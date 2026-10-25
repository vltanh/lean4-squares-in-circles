module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveCore

/-!
# Eight squares: original outer-source opposite-sign zero edges

All six nonnegative-angle families are treated on their complete half.
Four negative-angle families share an increasing secant/tangent support;
its derivative proof holds on the whole frame range and does not require
a numerical cutoff of the feasible contact.

The source outer coefficient is `-p r`, precisely the coefficient change
under reflection/reversal of the core-source families.
-/

section
/-!
## The actual zero-source contact for two negative mixed states

The original weak axis forces the angle above `.30243`. The continued
zero-source contact is written in rotated circle coordinates on the
entire interval up to `.7`. Its speed and speed derivative are positive,
so its first coordinate increases and its second decreases. Whenever
an original pair is feasible, the contact lies on the actual outer arc
before that target.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.NegativeContact

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
  have hst : start=30243/100000 := rfl
  have hs := sin_lower_seven (x := start) (by norm_num [start])
  have hu := sin_upper_five (x := start) (by norm_num [start])
  have hc := cos_lower_six (x := start) (by norm_num [start])
  have hk := cos_le_cos8 (x := start) (by norm_num [start])
  rw [hst] at hs hu hc hk ⊢
  norm_num [cos8] at hs hu hc hk
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma m_hasDerivAt (x : ℝ) : HasDerivAt m (n x) x := by
  have h : HasDerivAt (fun y => Real.sin y+Real.cos y) (Real.cos x+-Real.sin x) x :=
    (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  exact h.congr_deriv (by dsimp [n]; ring)
lemma n_hasDerivAt (x : ℝ) : HasDerivAt n (-m x) x := by
  have h : HasDerivAt (fun y => Real.cos y-Real.sin y) (-Real.sin x-Real.cos x) x :=
    (Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)
  exact h.congr_deriv (by dsimp [m]; ring)

lemma n_pos {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<n x := by
  have ht := positive_trig hx
  dsimp [n]
  linarith [ht.1,ht.2.2.2.1]

lemma m_monotone : MonotoneOn m (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg (fun x _ => (m_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => m_hasDerivAt x) (fun _ hx => (n_pos (Ioo_subset_Icc_self hx)).le)

lemma cut_start_neg : cut start<0 := by
  have hd := fine_diagonal_bounds
  have ht := start_trig
  have hm : m start<(2504913/2000000:ℝ) := by dsimp [m]; linarith [ht.2.1,ht.2.2.2]
  have hh := mul_le_mul_of_nonneg_left hm.le
    (show 0≤outerDiagonal-1/2 by linarith [hd.1])
  dsimp [cut]
  nlinarith [hd.2]

/-- The core case of `CommonQuarter.negative_secondary_positive_angle` (not imported here). -/
private lemma negative_secondary_positive_angle {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) : 0<φ := by
  have hb : 0≤b := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have hto := outer_bounds ht
  have hc := signed_cos hφ
  have hBc := mul_le_mul_of_nonneg_left hc.2 ht.1
  have hw : 1≤pairWidth φ := by
    have h := one_le_abs_cos_add_abs_sin φ
    dsimp [pairWidth]
    linarith
  by_contra! hbad
  have hsin : Real.sin φ≤0 := by
    have ht := positive_trig (x := -φ)
      ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using ht.2.2.1
  have hAs := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤A by linarith [ht.1,ht.2.1]) hsin
  norm_num [forwardMargin] at hm
  nlinarith [hto.2.2.2.1,outer_endpoint_bounds.2.2.2]

lemma original_angle {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) : start<φ := by
  have hp := negative_secondary_positive_angle hs ht hφ hm
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
    (313/250:ℝ)< m x ∧ m x<141/100 ∧ 0<n x := by
  have hx' : x∈Icc 0 (7/10) := ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩
  have hl := m_monotone (by norm_num [start]) hx' hx.1
  have hu := m_monotone hx' (by norm_num) hx.2
  have hs := start_trig
  have he := CommonQuarter.cap_trig
  refine ⟨?_,?_,n_pos hx'⟩
  · dsimp [m] at hl ⊢
    linarith [hs.1,hs.2.2.1]
  · dsimp [m] at hu ⊢
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
  have hs := mul_nonneg (show 0≤ m x-313/250 by linarith [hp.1])
    (show 0≤141/100-m x by linarith [hp.2.1])
  nlinarith [hp.1,hp.2.1]

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt Y (-Z x*n x/Y x) x := by
  have hp : 0<Q0-(Z x)^2 := Real.sqrt_pos.mp (Y_pos hx)
  have hz : HasDerivAt Z (n x) x := (m_hasDerivAt x).const_add (1/2)
  have hh : HasDerivAt (fun y => Real.sqrt (Q0-(Z y)^2))
      ((0-(2:ℕ)*Z x^(2-1)*n x)/(2*Real.sqrt (Q0-(Z x)^2))) x :=
    ((hasDerivAt_const x Q0).sub (hz.pow 2)).sqrt hp.ne'
  refine hh.congr_deriv ?_
  have hn := (Y_pos hx).ne'
  change (0-(2:ℕ)*Z x^(2-1)*n x)/(2*Y x)=-Z x*n x/Y x
  field_simp
  push_cast
  ring

lemma U_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt U (V x*speed x) x := by
  have hz : HasDerivAt Z (n x) x := (m_hasDerivAt x).const_add (1/2)
  have hh : HasDerivAt (fun y => Z y*Real.sin y+Y y*Real.cos y)
      (n x*Real.sin x+Z x*Real.cos x+((-Z x*n x/Y x)*Real.cos x+Y x*(-Real.sin x))) x :=
    (hz.mul (Real.hasDerivAt_sin x)).add ((Y_hasDerivAt hx).mul (Real.hasDerivAt_cos x))
  refine hh.congr_deriv ?_
  dsimp [V,speed]
  field_simp [(Y_pos hx).ne']
  ring

lemma V_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt V (-U x*speed x) x := by
  have hz : HasDerivAt Z (n x) x := (m_hasDerivAt x).const_add (1/2)
  have hh : HasDerivAt (fun y => Z y*Real.cos y-Y y*Real.sin y)
      (n x*Real.cos x+Z x*(-Real.sin x)-((-Z x*n x/Y x)*Real.sin x+Y x*Real.cos x)) x :=
    (hz.mul (Real.hasDerivAt_cos x)).sub ((Y_hasDerivAt hx).mul (Real.hasDerivAt_sin x))
  refine hh.congr_deriv ?_
  dsimp [U,speed]
  field_simp [(Y_pos hx).ne']
  ring

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt speed (speedD x) x := by
  have hh : HasDerivAt (fun y => 1-n y/Y y)
      (-((-m x*Y x-n x*(-Z x*n x/Y x))/(Y x)^2)) x :=
    ((n_hasDerivAt x).div (Y_hasDerivAt hx) (Y_pos hx).ne').const_sub 1
  have he := circle_base hx
  have hc := phase_circle x
  have hnum : m x*(Q0-9/4)-(m x)^2/2-1=m x*(Y x)^2-Z x*(n x)^2 := by
    dsimp only [Z] at he ⊢
    linear_combination (-m x)*he+(1/2+m x)*hc
  refine hh.congr_deriv ?_
  dsimp only [speedD]
  rw [hnum]
  field_simp [(Y_pos hx).ne']
  ring

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
  monoOn_of_hasDeriv_nonneg (fun _ hx => (U_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun _ hx => U_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun _ hx => mul_nonneg (coarse_coordinates (Ioo_subset_Icc_self hx)).2.le
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
  have zs : (8762281/5000000:ℝ)<Z start ∧ Z start<3504913/2000000 :=
    ⟨lt_of_eq_of_lt (by norm_num) ((add_lt_add_iff_left (1/2:ℝ)).mpr (add_lt_add ts.1 ts.2.2.1)),
      lt_of_lt_of_eq ((add_lt_add_iff_left (1/2:ℝ)).mpr (add_lt_add ts.2.1 ts.2.2.2)) (by norm_num)⟩
  have ze : (23863/12500:ℝ)<Z (7/10) ∧ Z (7/10)<477271/250000 :=
    ⟨lt_of_eq_of_lt (by norm_num) ((add_lt_add_iff_left (1/2:ℝ)).mpr (add_lt_add te.1 te.2.2.1)),
      lt_of_lt_of_eq ((add_lt_add_iff_left (1/2:ℝ)).mpr (add_lt_add te.2.1 te.2.2.2)) (by norm_num)⟩
  have hZs : 0≤Z start := (lt_trans (by norm_num) zs.1).le
  have hZe : 0≤Z (7/10) := (lt_trans (by norm_num) ze.1).le
  have hYs : 0≤Y start := (Y_pos hstart).le
  have hYe : 0≤Y (7/10) := (Y_pos hend).le
  have hss : 0≤Real.sin start := (lt_trans (by norm_num) ts.1).le
  have hcs : 0≤Real.cos start := (lt_trans (by norm_num) ts.2.2.1).le
  have hse : 0≤Real.sin (7/10) := (lt_trans (by norm_num) te.1).le
  have hce : 0≤Real.cos (7/10) := (lt_trans (by norm_num) te.2.2.1).le
  have hY (x : ℝ) : Y x=Real.sqrt (Q0-(Z x)^2) := rfl
  have ys : (11487/12500:ℝ)<Y start ∧ Y start<91897/100000 := by
    have h1 := pow_lt_pow_left₀ zs.2 hZs two_ne_zero
    have h2 := pow_lt_pow_left₀ zs.1 (by norm_num) two_ne_zero
    constructor
    · rw [hY,Real.lt_sqrt (by norm_num)]
      calc (11487/12500:ℝ)^2<Q0-(3504913/2000000)^2 := by norm_num [Q0]
        _<Q0-(Z start)^2 := sub_lt_sub_left h1 Q0
    · rw [hY,Real.sqrt_lt' (by norm_num)]
      calc Q0-(Z start)^2<Q0-(8762281/5000000)^2 := sub_lt_sub_left h2 Q0
        _<(91897/100000)^2 := by norm_num [Q0]
  have ye : (1041/2000:ℝ)<Y (7/10) ∧ Y (7/10)<651/1250 := by
    have h1 := pow_lt_pow_left₀ ze.2 hZe two_ne_zero
    have h2 := pow_lt_pow_left₀ ze.1 (by norm_num) two_ne_zero
    constructor
    · rw [hY,Real.lt_sqrt (by norm_num)]
      calc (1041/2000:ℝ)^2<Q0-(477271/250000)^2 := by norm_num [Q0]
        _<Q0-(Z (7/10))^2 := sub_lt_sub_left h1 Q0
    · rw [hY,Real.sqrt_lt' (by norm_num)]
      calc Q0-(Z (7/10))^2<Q0-(23863/12500)^2 := sub_lt_sub_left h2 Q0
        _<(651/1250)^2 := by norm_num [Q0]
  have zsSL := mul_le_mul zs.1.le ts.1.le (by norm_num) hZs
  have zsSU := mul_le_mul zs.2.le ts.2.1.le hss (by norm_num)
  have ysCL := mul_le_mul ys.1.le ts.2.2.1.le (by norm_num) hYs
  have ysCU := mul_le_mul ys.2.le ts.2.2.2.le hcs (by norm_num)
  have zsCL := mul_le_mul zs.1.le ts.2.2.1.le (by norm_num) hZs
  have zsCU := mul_le_mul zs.2.le ts.2.2.2.le hcs (by norm_num)
  have ysSL := mul_le_mul ys.1.le ts.1.le (by norm_num) hYs
  have ysSU := mul_le_mul ys.2.le ts.2.1.le hss (by norm_num)
  have zeSU := mul_le_mul ze.2.le te.2.1.le hse (by norm_num)
  have yeCU := mul_le_mul ye.2.le te.2.2.2.le hce (by norm_num)
  have zeCL := mul_le_mul ze.1.le te.2.2.1.le (by norm_num) hZe
  have yeSU := mul_le_mul ye.2.le te.2.1.le hse (by norm_num)
  dsimp only [U,V]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact lt_of_lt_of_le (by norm_num) (add_le_add zsSL ysCL)
  · exact lt_of_le_of_lt (add_le_add zsSU ysCU) (by norm_num)
  · exact lt_of_lt_of_le (by norm_num) (sub_le_sub zsCL ysSU)
  · exact lt_of_le_of_lt (sub_le_sub zsCU ysSL) (by norm_num)
  · exact lt_of_le_of_lt (add_le_add zeSU yeCU) (by norm_num)
  · exact lt_of_lt_of_le (by norm_num) (sub_le_sub zeCL yeSU)

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
    linarith
  have hc : P^2+T^2=Q0 := by
    dsimp [P,T]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hZ : 0≤Z x := by dsimp [Z]; linarith [(phase_bounds hx).1]
  have hPsq := pow_le_pow_left₀ hZ hP 2
  have hTy : T≤Y x := by
    by_contra! hlt
    have hp := mul_pos (sub_pos.mpr hlt) (show 0<T+Y x by linarith [Y_pos hx])
    linarith [circle_base hx]
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
  have hUV : V x≤U x := by
    by_contra! hlt
    have hp := mul_pos (sub_pos.mpr hlt) (show 0<V x+U x by linarith [hco.1,hco.2.2.1])
    linarith [diagonal_circle]
  have hcirc : (U x-1/2+1/2)^2+(V x-1/2+1/2)^2=Q0 := by
    rw [show U x-1/2+1/2=U x by ring,show V x-1/2+1/2=V x by ring]
    exact he
  exact ⟨⟨by linarith [hco.2.2.1],by linarith,hcirc⟩,hB⟩

end SquaresInCircles.Eight.ShortMixedZero.NegativeContact
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry WrongWordCircleSupport

lemma core_primary_lower {a b : ℝ} (hc : CoreState a b) :
    CoreAngleEndpoint.diagonal≤a := by
  rcases hc with ⟨rfl,_,_⟩ | ⟨hb,hab,he⟩
  · linarith [CoreAngleEndpoint.diagonal_bounds.2]
  · exact (CoreAngleEndpoint.corner_diagonal hb hab he).2

/-- The four smooth-multiplier families have their actual outer support
at the diagonal for every multiplier at least the original core slope. -/
lemma outer_diagonal_support (r : Row) (h0 : r≠0) (h3 : r≠3)
    {a b l : ℝ} (hc : OuterState a b) (hl : g r≤l) :
    (-p r+q r-l)*outerDiagonal≤-p r*a+(q r-l)*b := by
  have hd := outer_bounds hc
  have hd0 : 0≤outerDiagonal := by linarith [outer_endpoint_bounds.2.2.1]
  have hcompare : (-p r+q r-g r)*outerDiagonal≤-p r*outerAxial := by
    have ha := outer_endpoint_bounds
    have hf := fine_diagonal_bounds
    fin_cases r
    · exact absurd rfl h0
    · norm_num [p,q,g]; linarith [ha.1,ha.2.1,hf.1,hf.2]
    · norm_num [p,q,g]; linarith [ha.1,ha.2.1,hf.1,hf.2]
    · exact absurd rfl h3
    · norm_num [p,q,g]; linarith [ha.1,ha.2.1,hf.1,hf.2]
    · norm_num [p,q,g]; linarith [ha.1,ha.2.1,hf.1,hf.2]
  have hcompare' : (-p r+q r-l)*outerDiagonal≤-p r*outerAxial := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) hd0]
  by_cases hY : 0≤q r-l
  · exact outer_endpoints_lower hc hY hcompare' (le_of_eq (by ring))
  · by_cases hP : 0≤-p r
    · have hp := mul_le_mul_of_nonneg_left hd.1 hP
      have hq := mul_le_mul_of_nonpos_left hd.2.2.2.1 (le_of_not_ge hY)
      nlinarith
    · have hs : q r-g r+p r≤0 := by
        fin_cases r
        · exact absurd rfl h0
        · norm_num [p] at hP
        · norm_num [p] at hP
        · exact absurd rfl h3
        · norm_num [p] at hP
        · norm_num [p,q,g]
      have hh := outer_diagonal_lower (X := -p r) (Y := q r-l) hc (le_of_not_ge hP)
        (by linarith)
      linarith

def positiveSecant (r : Row) (x : ℝ) : ℝ :=
  x+c r+(-p r+q r)*outerDiagonal+g r/2+
    g r*(1/2-outerDiagonal)/Real.cos x-(g r/12)*Real.sin x/Real.cos x
def negativeSecant (r : Row) (x : ℝ) : ℝ :=
  -x+c r+(-p r+q r)*outerDiagonal+g r/2+
    g r*(1/2-outerDiagonal)/Real.cos x+
      g r*(1/2+CoreAngleEndpoint.diagonal)*Real.sin x/Real.cos x
def positiveSecantD (r : Row) (x : ℝ) : ℝ :=
  1-g r*((outerDiagonal-1/2)*Real.sin x+1/12)/(Real.cos x)^2
def negativeSecantD (r : Row) (x : ℝ) : ℝ :=
  -1+g r*((1/2+CoreAngleEndpoint.diagonal)-
    (outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2

lemma positiveSecant_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (positiveSecant r) (positiveSecantD r x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have hd := (((((hasDerivAt_id x).add_const (c r)).add_const
    ((-p r+q r)*outerDiagonal)).add_const (g r/2)).add
      ((hasDerivAt_const x (g r*(1/2-outerDiagonal))).div (Real.hasDerivAt_cos x) hc)).sub
        (((Real.hasDerivAt_sin x).const_mul (g r/12)).div (Real.hasDerivAt_cos x) hc)
  convert hd using 1
  · rfl
  · dsimp [positiveSecantD]
    field_simp [hc]
    have ht : g r*((Real.sin x)^2+(Real.cos x)^2)=g r := by
      rw [Real.sin_sq_add_cos_sq,mul_one]
    nlinarith only [ht]

lemma negativeSecant_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (negativeSecant r) (negativeSecantD r x) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have hd := ((((((hasDerivAt_id x).neg).add_const (c r)).add_const
    ((-p r+q r)*outerDiagonal)).add_const (g r/2)).add
      ((hasDerivAt_const x (g r*(1/2-outerDiagonal))).div (Real.hasDerivAt_cos x) hc)).add
        (((Real.hasDerivAt_sin x).const_mul (g r*(1/2+CoreAngleEndpoint.diagonal))).div
          (Real.hasDerivAt_cos x) hc)
  convert hd using 1
  · rfl
  · dsimp [negativeSecantD]
    field_simp [hc]
    have ht : g r*(1/2+CoreAngleEndpoint.diagonal)*
        ((Real.sin x)^2+(Real.cos x)^2)=g r*(1/2+CoreAngleEndpoint.diagonal) := by
      rw [Real.sin_sq_add_cos_sq,mul_one]
    nlinarith only [ht]

lemma positiveSecantD_pos (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<positiveSecantD r x := by
  have ht := positive_trig hx
  have hg := (coefficient_bounds r).1
  have hgU : g r≤1139/1000 :=
    (coefficient_bounds r).2.2.1.trans (coefficient_bounds r).2.2.2.1
  have hd := outer_endpoint_bounds
  have hcos : (29/50:ℝ)<(Real.cos x)^2 := by nlinarith [ht.1]
  have hnum : 0≤(outerDiagonal-1/2)*Real.sin x+1/12 := by
    have hm := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [hd.2.2.1]) ht.2.2.1
    linarith
  have hprod : (outerDiagonal-1/2)*Real.sin x<(2/5)*(129/200:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left ht.2.2.2.1.le
      (show 0≤outerDiagonal-1/2 by linarith [hd.2.2.1])
    have h2 := mul_lt_mul_of_pos_right
      (show outerDiagonal-1/2<(2/5:ℝ) by linarith [hd.2.2.2]) (by norm_num : (0:ℝ)<16106/25000)
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hgU hnum
  have hupper := mul_lt_mul_of_pos_left (show
    (outerDiagonal-1/2)*Real.sin x+1/12<(2/5)*(129/200:ℝ)+1/12 by linarith)
    (by norm_num : (0:ℝ)<1139/1000)
  have hratio : g r*((outerDiagonal-1/2)*Real.sin x+1/12)/(Real.cos x)^2<1 :=
    (div_lt_one (by linarith : 0<(Real.cos x)^2)).2 (by nlinarith)
  dsimp [positiveSecantD]
  linarith

lemma negativeSecantD_pos (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<negativeSecantD r x := by
  have hg : 1<g r := by
    fin_cases r
    · exact absurd rfl h0
    · norm_num [g]
    · norm_num [g]
    · exact absurd rfl h3
    · norm_num [g]
    · norm_num [g]
  have hd := outer_endpoint_bounds
  have hc := CoreAngleEndpoint.diagonal_bounds
  have ht := positive_trig hx
  have hden : 0<(Real.cos x)^2 := sq_pos_of_pos (by linarith [ht.1])
  have hdisc : (outerDiagonal-1/2)^2<4*(CoreAngleEndpoint.diagonal-1/2) := by
    nlinarith [hd.2.2.1,hd.2.2.2,hc.1]
  have hquadratic : 0<(Real.sin x)^2-(outerDiagonal-1/2)*Real.sin x+
      CoreAngleEndpoint.diagonal-1/2 := by
    linarith [sq_nonneg (2*Real.sin x-(outerDiagonal-1/2))]
  have hbracket : (Real.cos x)^2<(1/2+CoreAngleEndpoint.diagonal)-
      (outerDiagonal-1/2)*Real.sin x := by
    linarith [Real.sin_sq_add_cos_sq x]
  have hpositive : 0<(1/2+CoreAngleEndpoint.diagonal)-
      (outerDiagonal-1/2)*Real.sin x := hden.trans hbracket
  have hm := mul_lt_mul_of_pos_right hg hpositive
  have hratio : 1<g r*((1/2+CoreAngleEndpoint.diagonal)-
      (outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2 :=
    (one_lt_div hden).2 (by linarith)
  dsimp [negativeSecantD]
  linarith

lemma secant_initial (r : Row) (h0 : r≠0) (h3 : r≠3) :
    (449/500:ℝ)<positiveSecant r 0 ∧ (449/500:ℝ)<negativeSecant r 0 := by
  have hl : multiplier r=g r := by simp [multiplier,h0,h3]
  have hh := diagonal_initial r
  rw [hl] at hh
  norm_num [WrongWordCircleSupport.diagonal,base,X,Y,intercept,hl] at hh
  refine ⟨?_,?_⟩
  · norm_num [positiveSecant]
    linarith
  · norm_num [negativeSecant]
    linarith

lemma positiveSecant_lower (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<positiveSecant r x := by
  have hm : MonotoneOn (positiveSecant r) (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z hz => (positiveSecant_hasDerivAt r hz).continuousAt.continuousWithinAt
    · exact fun z hz => positiveSecant_hasDerivAt r (Ioo_subset_Icc_self hz)
    · exact fun z hz => (positiveSecantD_pos r (Ioo_subset_Icc_self hz)).le
  exact (secant_initial r h0 h3).1.trans_le (hm (by norm_num) hx hx.1)

lemma negativeSecant_lower (r : Row) (h0 : r≠0) (h3 : r≠3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<negativeSecant r x := by
  have hm : MonotoneOn (negativeSecant r) (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z hz => (negativeSecant_hasDerivAt r hz).continuousAt.continuousWithinAt
    · exact fun z hz => negativeSecant_hasDerivAt r (Ioo_subset_Icc_self hz)
    · exact fun z hz => (negativeSecantD_pos r h0 h3 (Ioo_subset_Icc_self hz)).le
  exact (secant_initial r h0 h3).2.trans_le (hm (by norm_num) hx hx.1)

lemma secant_multiplier (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<g r/Real.cos x ∧ g r≤g r/Real.cos x ∧
      (g r/Real.cos x)*Real.cos x=g r := by
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hg := (coefficient_bounds r).1
  exact ⟨div_pos hg hc,(le_div_iff₀ hc).2 (by nlinarith [Real.cos_le_one x]),
    div_mul_cancel₀ _ hc.ne'⟩

theorem opposite_outer_positive_secant (r : Row) (h0 : r≠0) (h3 : r≠3)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<x+c r-p r*a+q r*b+g r*B := by
  obtain ⟨l,hldef⟩ : ∃ l, l=g r/Real.cos x := ⟨_,rfl⟩
  have hl := secant_multiplier r hx
  rw [← hldef] at hl
  have hsource := outer_diagonal_support r h0 h3 hs hl.2.1
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hcore := mul_nonneg (mul_nonneg hl.1.le (positive_trig hx).2.2.1)
    (sub_nonneg.mpr hA)
  have hsep := mul_nonneg hl.1.le (sub_nonneg.mpr hm)
  have hh := positiveSecant_lower r h0 h3 hx
  have hid : positiveSecant r x=x+c r+(-p r+q r-l)*outerDiagonal+
      l*(1+Real.sin x+Real.cos x)/2-l*(7/12)*Real.sin x := by
    rw [hldef]
    dsimp [positiveSecant]
    field_simp [(ne_of_gt (show 0<Real.cos x by linarith [(positive_trig hx).1]))]
    ring
  rw [hid] at hh
  have hlcB : l*B*Real.cos x=g r*B := by rw [← hl.2.2]; ring
  linarith

/-- The four large-slope negative-angle families are controlled on the
whole frame interval, directly from their original weak separator. -/
theorem opposite_outer_negative_secant (r : Row) (h0 : r≠0) (h3 : r≠3)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c r-p r*a+q r*b+g r*B := by
  obtain ⟨l,hldef⟩ : ∃ l, l=g r/Real.cos x := ⟨_,rfl⟩
  have hl := secant_multiplier r hx
  rw [← hldef] at hl
  have hsource := outer_diagonal_support r h0 h3 hs hl.2.1
  have hA := core_primary_lower ht
  have hcore := mul_nonneg (mul_nonneg hl.1.le (positive_trig hx).2.2.1)
    (sub_nonneg.mpr hA)
  have hsep := mul_nonneg hl.1.le (sub_nonneg.mpr hm)
  have hh := negativeSecant_lower r h0 h3 hx
  have hid : negativeSecant r x=-x+c r+(-p r+q r-l)*outerDiagonal+
      l*(1+Real.sin x+Real.cos x)/2+l*CoreAngleEndpoint.diagonal*Real.sin x := by
    rw [hldef]
    dsimp [negativeSecant]
    field_simp [(ne_of_gt (show 0<Real.cos x by linarith [(positive_trig hx).1]))]
    ring
  rw [hid] at hh
  have hlcB : l*B*Real.cos x=g r*B := by rw [← hl.2.2]; ring
  linarith

def constantOuter (r : Row) (x : ℝ) : ℝ :=
  x+c r+(p r-q r+multiplier r)/2-CommonQuarter.radius*N (p r) (q r) (multiplier r) 0+
    multiplier r/2+g r*CoreAngleEndpoint.diagonal-(multiplier r/12)*Real.sin x+
      multiplier r*(1/2-CoreAngleEndpoint.diagonal)*Real.cos x
def constantOuterD (r : Row) (x : ℝ) : ℝ :=
  1-(multiplier r/12)*Real.cos x+
    multiplier r*(CoreAngleEndpoint.diagonal-1/2)*Real.sin x

lemma constantOuter_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (constantOuter r) (constantOuterD r x) x := by
  have hh : HasDerivAt (fun y => y+c r+(p r-q r+multiplier r)/2-
      CommonQuarter.radius*N (p r) (q r) (multiplier r) 0+multiplier r/2+g r*CoreAngleEndpoint.diagonal-
        (multiplier r/12)*Real.sin y+multiplier r*(1/2-CoreAngleEndpoint.diagonal)*Real.cos y)
      (1-(multiplier r/12)*Real.cos x+
        multiplier r*(1/2-CoreAngleEndpoint.diagonal)*(-Real.sin x)) x :=
    (((((((hasDerivAt_id' x).add_const (c r)).add_const
      ((p r-q r+multiplier r)/2)).sub_const
        (CommonQuarter.radius*N (p r) (q r) (multiplier r) 0)).add_const (multiplier r/2)).add_const
          (g r*CoreAngleEndpoint.diagonal)).sub
            ((Real.hasDerivAt_sin x).const_mul (multiplier r/12))).add
              ((Real.hasDerivAt_cos x).const_mul (multiplier r*(1/2-CoreAngleEndpoint.diagonal)))
  exact hh.congr_deriv (by dsimp [constantOuterD]; ring)

lemma constantOuter_lower (r : Row) (he : r=0 ∨ r=3)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : (449/500:ℝ)<constantOuter r x := by
  have hzero : constantOuter r 0=full (intercept r) (p r) (q r) (multiplier r) 0 := by
    rw [full_expression]
    simp only [constantOuter,intercept,Real.sin_zero,Real.cos_zero]
    ring
  have hinit : (449/500:ℝ)<constantOuter r 0 := by
    rw [hzero]
    rcases he with rfl | rfl
    · have hd := CoreAngleEndpoint.diagonal_bounds
      norm_num [full,base,X,Y,N,CircularNorm.norm,CircularNorm.energy,mass,
        intercept,c,p,q,g,multiplier]
      nlinarith [hd.1,hd.2]
    · exact third_full_initial
  have hm : MonotoneOn (constantOuter r) (Icc 0 (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (constantOuter_hasDerivAt r z).continuousAt.continuousWithinAt
    · exact fun z _ => constantOuter_hasDerivAt r z
    · intro z hz
      have ht := positive_trig (Ioo_subset_Icc_self hz)
      have hc := coefficient_bounds r
      have h₁ := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤ multiplier r/12 by linarith [hc.2.1])
      have h₂ := mul_nonneg (mul_nonneg hc.2.1.le
        (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [CoreAngleEndpoint.diagonal_bounds.1])) ht.2.2.1
      dsimp [constantOuterD]
      linarith [hc.2.2.2.1]
  exact hinit.trans_le (hm (by norm_num) hx hx.1)

theorem opposite_outer_positive_constant (r : Row) (he : r=0 ∨ r=3)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<x+c r-p r*a+q r*b+g r*B := by
  have hc := coefficient_bounds r
  have htr := positive_trig hx
  have hcoef : g r-multiplier r*Real.cos x≤0 := by
    have hp := mul_lt_mul_of_pos_left htr.1 hc.2.1
    rcases he with rfl | rfl <;> norm_num [g,multiplier,q] at hp ⊢ <;> linarith
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.2.2
  have hprimary := mul_nonneg (mul_nonneg hc.2.1.le htr.2.2.1) (sub_nonneg.mpr hA)
  have hsecondary := mul_nonneg_of_nonpos_of_nonpos hcoef (sub_nonpos.mpr hB)
  have hsource := outer_circle_lower (X := -p r) (Y := q r-multiplier r) hs
  have hN : N (p r) (q r) (multiplier r) 0=
      Real.sqrt ((-p r)^2+(q r-multiplier r)^2) := by
    rw [N,CircularNorm.norm,energy_eq]
    simp [X,Y]
  rw [← hN] at hsource
  have hsep := mul_nonneg hc.2.1.le (sub_nonneg.mpr hm)
  have hh := constantOuter_lower r he hx
  dsimp [constantOuter] at hh
  nlinarith

/-- All six original outer-source opposite-sign secondary families on
the nonnegative angle half. -/
theorem opposite_outer_positive (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)<x+c r-p r*a+q r*b+g r*B := by
  by_cases he : r=0 ∨ r=3
  · exact opposite_outer_positive_constant r he hs ht hx hm
  · exact opposite_outer_positive_secant r (fun h => he (Or.inl h))
      (fun h => he (Or.inr h)) hs ht hx hm

end SquaresInCircles.Eight.ShortMixedZero
end
end
end
