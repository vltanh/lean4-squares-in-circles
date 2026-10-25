module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperContact
public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFourScalars

/-!
# Eight squares: whole-domain geometry and the quartic contact-speed estimate

The speed bound is one polynomial monotonicity argument in sin x.
The radical inequality is written T ≤ R, retaining the possible equality
when z=0; the strict rational bounds used in the note are unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)
open SecondWord.SameZero.PJ.Diagonal (angle_mem)

theorem diagonal_circle {x : ℝ} (hx : DiagonalDomain x) : (U x)^2+(V x)^2=Q0 :=
  SecondWord.SameZero.PJ.Diagonal.circle hx.1

theorem diagonal_radical {x : ℝ} (hx : DiagonalDomain x) :
    (969/500:ℝ)<T x ∧ T x≤CommonQuarter.radius ∧ (T x)^2+(z x)^2=Q0 := by
  have hr := SecondWord.SameZero.PJ.Diagonal.radical_data hx.1
  have hR := ShortWord.MixedQuarter.Reference.radius_fine
  refine ⟨by linarith [hr.2.2.1],?_,hr.2.2.2.2⟩
  have hsq := radius_sq
  nlinarith [sq_nonneg (z x)]

theorem diagonal_z_bounds {x : ℝ} (hx : DiagonalDomain x) :
    -(123/500:ℝ)<z x ∧ z x<(79843/200000:ℝ) := by
  have hh := SecondWord.SameZero.PJ.Diagonal.radical_data hx.1
  exact ⟨hh.1,by linarith [hh.2.1]⟩

theorem diagonal_omega_bounds {x : ℝ} (hx : DiagonalDomain x) :
    (483/1000:ℝ)<omega x ∧ omega x<(307/500:ℝ) := by
  have hr := diagonal_radical hx
  have ht := positive_trig (angle_mem hx.1)
  have hT : 0<T x := by linarith [hr.1]
  have hR := ShortWord.MixedQuarter.Reference.radius_fine.2
  have hlo : Real.cos x/T x<(517/1000:ℝ) := by
    apply (div_lt_iff₀ hT).2
    nlinarith [ht.2.1,hr.1]
  have hhi : (193/500:ℝ)<Real.cos x/T x := by
    apply (lt_div_iff₀ hT).2
    nlinarith [ht.1,hr.2.1]
  dsimp [omega,SecondWord.SameZero.PJ.Diagonal.factor]
  constructor <;> linarith

theorem negative_z_data {x : ℝ} (hx : DiagonalDomain x) (hz : z x<0) :
    (499/1250:ℝ)<Real.sin x ∧ Real.cos x<(917/1000:ℝ) ∧
      (1963/1000:ℝ)<T x ∧ (133/250:ℝ)<omega x := by
  have ht := positive_trig (angle_mem hx.1)
  have hr := diagonal_radical hx
  have hzl := (diagonal_z_bounds hx).1
  have hs : (499/1250:ℝ)<Real.sin x := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀] at hz
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hc : Real.cos x<(917/1000:ℝ) := by nlinarith [Real.sin_sq_add_cos_sq x,ht.1]
  have hT : (1963/1000:ℝ)<T x := by
    norm_num [Q0] at hr
    nlinarith [mul_nonneg (by linarith : 0≤z x+123/500) (by linarith : 0≤123/500-z x)]
  have hd : Real.cos x/T x<(117/250:ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<T x)).2
    nlinarith
  exact ⟨hs,hc,hT,by dsimp [omega,SecondWord.SameZero.PJ.Diagonal.factor]; linarith⟩

theorem diagonal_V_cap : V (7/10)<(136/125:ℝ) := by
  have hx : DiagonalDomain (7/10) := by
    obtain ⟨e,he⟩ := exists_event
    exact after_diagonal_domain he ⟨(event_bounds he).2.2.2,le_rfl⟩
  have hs := RoleFour.fine_cap_trig
  have hr := diagonal_radical hx
  have hR := ShortWord.MixedQuarter.Reference.radius_fine.2
  have hz0 : z0<(79843/200000:ℝ) := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]
    linarith [ShortMixedZero.fine_diagonal_bounds.2]
  have hfirst := mul_le_mul hs.2.1.le
    (hr.2.1.trans hR.le) (by linarith [hr.1] : 0≤T (7/10)) (by norm_num)
  have hsecond := mul_le_mul
    (show (64421/100000:ℝ)-79843/200000≤Real.sin (7/10)-z0 by linarith [hs.1])
    (show (19121/25000:ℝ)≤Real.cos (7/10) by linarith [hs.2.2.1])
    (by norm_num) (by linarith [hs.1] : 0≤Real.sin (7/10)-z0)
  dsimp [V,SecondWord.SameZero.PJ.Diagonal.vertical,SecondWord.SameZero.PJ.Diagonal.Z]
  nlinarith

theorem diagonal_coordinate_bounds {x : ℝ} (hx : DiagonalDomain x) :
    (33/20:ℝ)<U x ∧ U x<(383/200:ℝ) ∧ (1/2:ℝ)≤V x ∧ V x<(136/125:ℝ) ∧
      0<V x/U x ∧ V x/U x<(33/50:ℝ) := by
  have hh := SecondWord.SameZero.PJ.Diagonal.whole_bounds hx.1
  have hv := SecondWord.SameZero.PJ.Diagonal.height_monotone hx.1
    (by norm_num [SecondWord.SameZero.PJ.Diagonal.start] :
      (7/10:ℝ)∈Icc SecondWord.SameZero.PJ.Diagonal.start (7/10)) hx.1.2
  have hVlo : (1/2:ℝ)≤V x := by
    have hz := hx.2
    dsimp [SecondWord.SameZero.PJ.Diagonal.height] at hz
    exact by linarith
  have hVhi : V x<(136/125:ℝ) := by
    dsimp [SecondWord.SameZero.PJ.Diagonal.height] at hv
    linarith [diagonal_V_cap]
  have hU : 0<U x := by linarith [hh.1]
  refine ⟨hh.1,hh.2.1,hVlo,hVhi,div_pos (by linarith) hU,?_⟩
  apply (div_lt_iff₀ hU).2
  linarith

theorem diagonal_ratio {x : ℝ} (hx : DiagonalDomain x) :
    ratio (diagonalB x)=V x/U x ∧ rho≤V x/U x := by
  have ha := diagonal_target_arc hx
  have hV : diagonalB x+1/2=V x := by
    dsimp [diagonalB,SecondWord.SameZero.PJ.Diagonal.height]; ring
  have hid : ratio (diagonalB x)=V x/U x := by
    rw [ratio,ha,hV]
    ring
  exact ⟨hid,by simpa only [hid] using (target_ratio
    (SecondWord.SameZero.PJ.Diagonal.target_mem hx)).1⟩

theorem diagonal_projection {x : ℝ} (_hx : DiagonalDomain x) :
    Real.cos x*U x+Real.sin x*V x=T x ∧
      Real.cos x*V x-Real.sin x*U x=z x := by
  have hc := Real.sin_sq_add_cos_sq x
  dsimp only [U,V,SecondWord.SameZero.PJ.Diagonal.horizontal,SecondWord.SameZero.PJ.Diagonal.vertical]
  constructor
  · linear_combination (SecondWord.SameZero.PJ.Diagonal.Y x)*hc
  · linear_combination (SecondWord.SameZero.PJ.Diagonal.Z x)*hc

theorem diagonal_U_le_T {x : ℝ} (hx : DiagonalDomain x) : U x≤T x := by
  have ht := positive_trig (angle_mem hx.1)
  have hr := diagonal_radical hx
  by_cases hz : 0≤z x
  · have hc := mul_le_mul_of_nonneg_left ht.2.1 (by linarith [hr.1] : 0≤T x)
    have hs := mul_nonneg hz ht.2.2.1
    dsimp [U,SecondWord.SameZero.PJ.Diagonal.horizontal]
    linarith
  · have hn := negative_z_data hx (lt_of_not_ge hz)
    have h1 := mul_le_mul_of_nonneg_left hn.2.1.le (by linarith [hr.1] : 0≤T x)
    have hz' : -z x≤(1229/5000:ℝ) := by
      dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
      linarith [ht.2.2.2.1,ShortMixedZero.fine_diagonal_bounds.1]
    have h2 := mul_le_mul hz' ht.2.2.2.1.le ht.2.2.1 (by norm_num)
    dsimp [U,SecondWord.SameZero.PJ.Diagonal.horizontal]
    nlinarith

theorem nonnegative_z_geometry {x : ℝ} (hx : DiagonalDomain x) (hz : 0≤z x) :
    V x<(4/5:ℝ) ∧ (9/5:ℝ)<U x ∧ Real.sin x≤V x/U x := by
  have ht := positive_trig (angle_mem hx.1)
  have hr := diagonal_radical hx
  have hc := diagonal_coordinate_bounds hx
  have hs : Real.sin x≤z0 := by
    dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z] at hz
    linarith
  have hz0 : z0<(2/5:ℝ) := by
    dsimp [z0,SecondWord.SameZero.PJ.Diagonal.z₀]; linarith [ShortMixedZero.fine_diagonal_bounds.2]
  have hV : V x≤z0*CommonQuarter.radius := by
    have h1 := mul_le_mul_of_nonneg_left hr.2.1 ht.2.2.1
    have h2 := mul_le_mul_of_nonneg_left
      (show Real.cos x≤CommonQuarter.radius by linarith [ht.2.1,ShortWord.MixedQuarter.Reference.radius_fine.1]) hz
    dsimp only [V,SecondWord.SameZero.PJ.Diagonal.vertical,z,SecondWord.SameZero.PJ.Diagonal.Z,
      T] at h1 h2 ⊢
    linarith
  have hprod := mul_lt_mul'' hz0 ShortWord.MixedQuarter.Reference.radius_fine.2
    (by linarith [hs,ht.2.2.1] : 0≤z0)
    (by linarith [ShortWord.MixedQuarter.Reference.radius_fine.1] : 0≤CommonQuarter.radius)
  have hv : V x<(4/5:ℝ) := by linarith
  have hu : (9/5:ℝ)<U x := by
    have hcircle := diagonal_circle hx
    norm_num [Q0] at hcircle
    have hV2 := mul_self_lt_mul_self (by linarith [hc.2.2.1] : 0≤V x) hv
    have hU2 : (9/5:ℝ)*(9/5)<U x*U x := by linarith
    exact lt_of_mul_self_lt_mul_self₀ (by linarith [hc.1]) hU2
  refine ⟨hv,hu,?_⟩
  apply (le_div_iff₀ (by linarith : 0<U x)).2
  have hT := mul_le_mul_of_nonneg_right (diagonal_U_le_T hx) ht.2.2.1
  have hnonneg := mul_nonneg hz (by linarith [ht.1] : 0≤Real.cos x)
  dsimp [V,SecondWord.SameZero.PJ.Diagonal.vertical]
  linarith

theorem cosine_upper_square {x : ℝ} (_hx : x∈Icc 0 (7/10)) :
    Real.cos x≤1-(Real.sin x)^2/2 := by
  nlinarith [Real.sin_sq_add_cos_sq x,sq_nonneg (1-Real.cos x)]

theorem cosine_lower_square {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    1-(Real.sin x)^2/(441/250:ℝ)≤Real.cos x := by
  have ht := positive_trig hx
  have hh := mul_nonneg (show 0≤Real.cos x-191/250 by linarith [ht.1])
    (sub_nonneg.mpr ht.2.1)
  nlinarith [Real.sin_sq_add_cos_sq x]

def speedPolynomial (s : ℝ) : ℝ :=
  9789/10000+(307/500)*s*(s-499/1250)-(s^2/2-107/10000)^2
def speedPolynomialD (s : ℝ) : ℝ := s*(6247/5000-s^2)-153193/625000

theorem speedPolynomial_hasDerivAt (s : ℝ) :
    HasDerivAt speedPolynomial (speedPolynomialD s) s := by
  have h := ((((hasDerivAt_id' s).const_mul (307/500:ℝ)).fun_mul
    ((hasDerivAt_id' s).sub_const (499/1250:ℝ))).const_add (9789/10000:ℝ)).fun_sub
      (((((hasDerivAt_id' s).fun_mul (hasDerivAt_id' s)).div_const (2:ℝ)).sub_const
        (107/10000:ℝ)).pow 2)
  convert h using 1
  · funext y
    simp only [speedPolynomial,Pi.pow_apply]
    ring
  · simp only [speedPolynomialD]
    ring

theorem speedPolynomial_increasing : MonotoneOn speedPolynomial (Icc (499/1250:ℝ) (129/200)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s _ => (speedPolynomial_hasDerivAt s).continuousAt.continuousWithinAt)
    (fun s _ => speedPolynomial_hasDerivAt s)
  intro s hs
  have hsquare : s^2≤(129/200:ℝ)^2 := pow_le_pow_left₀ (by linarith [hs.1]) hs.2.le 2
  have hprod := mul_le_mul hs.1.le
    (show (6247/5000:ℝ)-(129/200)^2≤6247/5000-s^2 by linarith)
    (by norm_num) (by linarith [hs.1] : 0 ≤ s)
  dsimp only [speedPolynomialD]
  linarith

theorem diagonal_speed_formula {x : ℝ} (hx : DiagonalDomain x) :
    diagonalSpeed x=Real.cos x*T x-(Real.cos x)^2-Real.sin x*z x*omega x := by
  have hT : T x≠0 := ne_of_gt (by linarith [(diagonal_radical hx).1])
  dsimp [diagonalSpeed,SecondWord.SameZero.PJ.Diagonal.speed,U,
    SecondWord.SameZero.PJ.Diagonal.horizontal,omega,SecondWord.SameZero.PJ.Diagonal.factor]
  field_simp [hT]

theorem diagonal_speed_bounds {x : ℝ} (hx : DiagonalDomain x) :
    0<diagonalSpeed x ∧ diagonalSpeed x<(26/25:ℝ) := by
  have hcoords := diagonal_coordinate_bounds hx
  have hr := diagonal_radical hx
  have ht := positive_trig (angle_mem hx.1)
  have hw := diagonal_omega_bounds hx
  have hp : 0<diagonalSpeed x := by
    exact mul_pos (by linarith [hcoords.1]) (by linarith [hw.1])
  refine ⟨hp,?_⟩
  rw [diagonal_speed_formula hx]
  by_cases hz : 0≤z x
  · have hcut := mul_nonneg (mul_nonneg ht.2.2.1 hz) (by linarith [hw.1] : 0≤omega x)
    have hsquare := sq_nonneg (Real.cos x-T x/2)
    have hrad := hr.2.2
    norm_num [Q0] at hrad
    linarith [sq_nonneg (z x)]
  · have hn := negative_z_data hx (lt_of_not_ge hz)
    have hcos := cosine_upper_square (angle_mem hx.1)
    have hR := ShortWord.MixedQuarter.Reference.radius_fine
    have hgap : 0≤(Real.sin x)^2/2-107/10000 := by
      have hs2 := mul_le_mul hn.1.le hn.1.le (by norm_num) (by linarith [hn.1])
      linarith
    have hgap' : (Real.sin x)^2/2-107/10000≤CommonQuarter.radius/2-Real.cos x := by
      linarith [hR.1]
    have hsq : ((Real.sin x)^2/2-107/10000)^2≤(CommonQuarter.radius/2-Real.cos x)^2 :=
      pow_le_pow_left₀ hgap hgap' 2
    have h1 := mul_le_mul_of_nonneg_left hr.2.1 (by linarith [ht.1] : 0≤Real.cos x)
    have hzbound : -z x≤Real.sin x-499/1250 := by
      dsimp [z,SecondWord.SameZero.PJ.Diagonal.Z,SecondWord.SameZero.PJ.Diagonal.z₀]
      linarith [ShortMixedZero.fine_diagonal_bounds.1]
    have h2 := mul_le_mul (mul_le_mul_of_nonneg_left hzbound ht.2.2.1) hw.2.le
      (by linarith [hw.1] : 0≤omega x)
      (mul_nonneg ht.2.2.1 (by linarith [hn.1] : 0≤Real.sin x-499/1250))
    have hbound : Real.cos x*T x-(Real.cos x)^2-Real.sin x*z x*omega x≤
        speedPolynomial (Real.sin x) := by
      have hrad := radius_sq
      dsimp only [speedPolynomial]
      norm_num [Q0] at hrad
      linarith
    have hs1 : Real.sin x≤129/200 := by linarith [ht.2.2.2.1]
    have hm := speedPolynomial_increasing
      (show Real.sin x∈Icc (499/1250:ℝ) (129/200) from ⟨hn.1.le,hs1⟩)
      (by norm_num : (129/200:ℝ)∈Icc (499/1250:ℝ) (129/200)) hs1
    have hnum : speedPolynomial (129/200)<(26/25:ℝ) := by norm_num [speedPolynomial]
    exact hbound.trans_lt (hm.trans_lt hnum)

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
