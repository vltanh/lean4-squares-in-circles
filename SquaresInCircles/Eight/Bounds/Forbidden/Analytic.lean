module

public import SquaresInCircles.Eight.Bounds.Forbidden.Geometry
public import SquaresInCircles.Eight.Arithmetic.Arctangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Supporting directions from rectangle geometry

The circle of radius `√(L²+c²)` supplies the curved supports. Sine addition shows
that their mean direction supports at least the mean height. For the wider
rectangle a linear angle already supports its corner, and its sum with the
opposite circle angle decreases up to a fixed endpoint. This proves the entire
band B estimate using elementary points and one analytic inequality.

Band A uses the same shallow-depth supports and the same circular-arc argument
at larger depth. In the middle range, a decreasing quartic locates the minimum
of its supporting-angle sum between two short decimal bounds.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.CentralForbidden.Analytic

/-- A point of the rectangle supporting the segment at the given angle. -/
structure Support (A h : ℝ) where
  x : ℝ
  y : ℝ
  angle : ℝ
  rectangle : Rectangle A h (x,y)
  radius : x^2+y^2 ≤ radiusSq
  angle_range : 0 ≤ angle ∧ angle ≤ 2
  projection : L ≤ x*Real.cos angle+y*Real.sin angle

def Support.mono_height {A h h' : ℝ} (S : Support A h) (hh : h ≤ h') : Support A h' :=
  { S with rectangle := ⟨S.rectangle.1,S.rectangle.2.1,S.rectangle.2.2.1,
      S.rectangle.2.2.2.trans hh⟩ }

def Support.mono_width {A A' h : ℝ} (S : Support A h) (hA : A ≤ A') : Support A' h :=
  { S with rectangle := ⟨S.rectangle.1,S.rectangle.2.1.trans hA,
      S.rectangle.2.2.1,S.rectangle.2.2.2⟩ }

lemma Support.interval {A h : ℝ} (S : Support A h) (hA : L ≤ A) :
    ∀ β, 0 ≤ β ∧ β ≤ S.angle →
      ∃ v, |v| ≤ c ∧ Rectangle A h (pointInDirection (0,0) (β : Direction) L v) :=
  rectangle_segment_interval hA S.rectangle S.radius S.angle_range S.projection

/-- Two supporting points give the whole forbidden interval, by radial projection. -/
theorem forbidden_of_supports {A W d : ℝ} (hA : L ≤ A)
    (hd : 0 ≤ d ∧ d ≤ 1) (S : Support A d) (T : Support A (1-d))
    (hW : W < S.angle+T.angle) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ W < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ A ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  refine ⟨-S.angle,T.angle,by linarith [S.angle_range.1],T.angle_range.1,
    by linarith,by linarith [S.angle_range.2,T.angle_range.2],?_⟩
  intro β hβ
  by_cases hβ₀ : 0 ≤ β
  · obtain ⟨v,hv,hp⟩ := T.interval hA β ⟨hβ₀,hβ.2⟩
    exact ⟨v,hv,hp.1,hp.2.1,by linarith only [hp.2.2.1,hd.1],hp.2.2.2⟩
  · obtain ⟨v,hv,hp⟩ := S.interval hA (-β) ⟨by linarith,by linarith [hβ.1]⟩
    refine ⟨-v,by simpa using hv,?_,?_,?_,?_⟩
    all_goals
      dsimp [Rectangle,pointInDirection] at hp ⊢
      simp only [Real.Angle.cos_neg,Real.Angle.sin_neg,Real.Angle.cos_coe,
        Real.Angle.sin_coe] at hp
      linarith only [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hd.1,hd.2]

private def axial : Support L 0 where
  x := L
  y := 0
  angle := 0
  rectangle := by norm_num [Rectangle,L]
  radius := by norm_num [L,radiusSq]
  angle_range := by norm_num
  projection := by simp

private def vertical : Support L L where
  x := 0
  y := L
  angle := Real.pi/2
  rectangle := by norm_num [Rectangle,L]
  radius := by norm_num [L,radiusSq]
  angle_range := ⟨by positivity,by linarith [Real.pi_lt_four]⟩
  projection := by simp

private def support13 : Support L (1/16) where
  x := L
  y := 1/16
  angle := 0.13
  rectangle := by norm_num [Rectangle,L]
  radius := by norm_num [L,radiusSq]
  angle_range := by norm_num
  projection := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := (0.13 : ℝ))
    have hs := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 0.13 by norm_num)
    norm_num [L] at *
    linarith

private def support17 : Support L (2/25) where
  x := L
  y := 2/25
  angle := 0.17
  rectangle := by norm_num [Rectangle,L]
  radius := by norm_num [L,radiusSq]
  angle_range := by norm_num
  projection := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := (0.17 : ℝ))
    have hs := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 0.17 by norm_num)
    norm_num [L] at *
    linarith

private def support175 : Support L (15/16) where
  x := 0
  y := 15/16
  angle := 1.75
  rectangle := by norm_num [Rectangle,L]
  radius := by norm_num [radiusSq]
  angle_range := by norm_num
  projection := by
    have hs := sin_lower_seven (x := (1.75 : ℝ)) (by norm_num)
    norm_num [L] at *
    linarith

private def support161 : Support L (23/25) where
  x := 0
  y := 23/25
  angle := 1.61
  rectangle := by norm_num [Rectangle,L]
  radius := by norm_num [radiusSq]
  angle_range := by norm_num
  projection := by
    have hs := sin_lower_seven (x := (1.61 : ℝ)) (by norm_num)
    norm_num [L] at *
    linarith

theorem bandA_small_depth {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/12) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (347/200) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ L ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  have hd' : 0 ≤ d ∧ d ≤ 1 := ⟨hd.1,by linarith⟩
  by_cases h : d ≤ 1/16
  · exact forbidden_of_supports le_rfl hd' (axial.mono_height hd.1)
      (support175.mono_height (by linarith)) (by norm_num [axial,support175,Support.mono_height])
  · by_cases h' : d ≤ 2/25
    · exact forbidden_of_supports le_rfl hd' (support13.mono_height (by linarith))
        (support161.mono_height (by linarith)) (by norm_num [support13,support161,Support.mono_height])
    · apply forbidden_of_supports le_rfl hd' (support17.mono_height (by linarith))
        (vertical.mono_height (by norm_num [L]; linarith))
      dsimp [support17,vertical,Support.mono_height]
      linarith [Real.pi_gt_d2]
private def supportQuarter : Support (19/20) 0 where
  x := 19/20
  y := 0
  angle := 1/4
  rectangle := by norm_num [Rectangle]
  radius := by norm_num [radiusSq]
  angle_range := by norm_num
  projection := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := (1/4 : ℝ))
    norm_num [L] at *
    linarith

theorem bandB_small_depth {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/12) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (899/500) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ (19/20) ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  apply forbidden_of_supports (by norm_num [L]) ⟨hd.1,by linarith⟩
    (supportQuarter.mono_height hd.1)
    ((vertical.mono_width (by norm_num [L])).mono_height (by norm_num [L]; linarith))
  dsimp [supportQuarter,vertical,Support.mono_width,Support.mono_height]
  linarith [Real.pi_gt_d2]

def capRadius : ℝ := Real.sqrt radiusSq
def capAngle : ℝ := Real.arctan (c/L)
def circleAngle (y : ℝ) : ℝ := Real.arcsin (y/capRadius)+capAngle

lemma capRadius_pos : 0 < capRadius := Real.sqrt_pos.mpr (by norm_num [radiusSq])
lemma capRadius_sq : capRadius^2 = radiusSq :=
  Real.sq_sqrt (by norm_num [radiusSq])
lemma capRadius_gt_L : L < capRadius := by
  have hr := capRadius_pos
  have hsq := capRadius_sq
  norm_num [L,radiusSq] at *
  nlinarith

lemma capAngle_range : 0 ≤ capAngle ∧ capAngle < Real.pi/2 :=
  ⟨Real.arctan_nonneg.mpr (by norm_num [c,L]), Real.arctan_lt_pi_div_two _⟩

lemma capAngle_frame : Real.cos capAngle = L/capRadius ∧ Real.sin capAngle = c/capRadius := by
  have hr := capRadius_pos
  have hL : 0 < L := by norm_num [L]
  have he : 1+(c/L)^2 = (capRadius/L)^2 := by
    simp only [div_pow,capRadius_sq]
    norm_num [L,c,radiusSq]
  have hroot : Real.sqrt (1+(c/L)^2) = capRadius/L := by
    rw [he,Real.sqrt_sq_eq_abs,abs_of_pos (div_pos hr hL)]
  constructor
  · rw [capAngle,Real.cos_arctan,hroot]
    field_simp
  · rw [capAngle,Real.sin_arctan,hroot]
    field_simp

lemma arcsin_L : Real.arcsin (L/capRadius) = Real.pi/2-capAngle := by
  rw [← capAngle_frame.1,← Real.sin_pi_div_two_sub]
  apply Real.arcsin_sin <;> linarith [capAngle_range.1,capAngle_range.2,Real.pi_pos]

lemma circleAngle_range {y : ℝ} (hy : 0 ≤ y ∧ y ≤ L) :
    0 ≤ circleAngle y ∧ circleAngle y ≤ Real.pi/2 := by
  have hr := capRadius_pos
  have h0 := Real.arcsin_nonneg.mpr (div_nonneg hy.1 hr.le)
  have h1 := Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hy.2 hr.le)
  rw [arcsin_L] at h1
  dsimp [circleAngle]
  constructor <;> linarith [capAngle_range.1]

/-- The circle clipped by the top of the rectangle supplies a supporting point. -/
def circleSupport {A y : ℝ} (hA : L ≤ A) (hy : 0 ≤ y ∧ y ≤ L)
    (hclip : radiusSq ≤ A^2+y^2) : Support A y := by
  have hr := capRadius_pos
  have hL : 0 < L := by norm_num [L]
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hrad : 0 < radiusSq-y^2 := by
    norm_num [L,radiusSq] at *
    linarith
  let x := Real.sqrt (radiusSq-y^2)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2 = radiusSq-y^2 := Real.sq_sqrt hrad.le
  have hxA : x ≤ A := by
    calc
      x ≤ Real.sqrt (A^2) := Real.sqrt_le_sqrt (by linarith [hclip])
      _ = A := by rw [Real.sqrt_sq_eq_abs,abs_of_pos (lt_of_lt_of_le hL hA)]
  have hyfrac : -1 ≤ y/capRadius ∧ y/capRadius ≤ 1 := by
    have hnonneg := div_nonneg hy.1 hr.le
    constructor
    · linarith
    · exact (div_le_one hr).mpr (hy.2.trans capRadius_gt_L.le)
  have hnorm : 1-(y/capRadius)^2 = (x/capRadius)^2 := by
    calc
      _ = (capRadius^2-y^2)/capRadius^2 := by field_simp [hr.ne']
      _ = (radiusSq-y^2)/capRadius^2 := by rw [capRadius_sq]
      _ = _ := by rw [div_pow,hx2]
  have hcos : Real.cos (Real.arcsin (y/capRadius)) = x/capRadius := by
    rw [Real.cos_arcsin,hnorm,Real.sqrt_sq_eq_abs,
      abs_of_nonneg (div_nonneg hx hr.le)]
  have hsin := Real.sin_arcsin hyfrac.1 hyfrac.2
  have hcircle : x^2+y^2 = capRadius^2 := by linarith [hx2,capRadius_sq]
  have hprojection : x*Real.cos (circleAngle y)+y*Real.sin (circleAngle y)=L := by
    dsimp [circleAngle]
    rw [Real.cos_add,Real.sin_add,hcos,hsin,capAngle_frame.1,capAngle_frame.2]
    field_simp
    linear_combination L*hcircle
  exact ⟨x,y,circleAngle y,⟨hx,hxA,hy.1,le_rfl⟩,by linarith [hx2],
    ⟨(circleAngle_range hy).1,by linarith [(circleAngle_range hy).2,Real.pi_lt_four]⟩,
    hprojection.ge⟩

def heightPhase (t : ℝ) : ℝ := L*Real.sin t-c*Real.cos t

lemma heightPhase_shift (t : ℝ) :
    heightPhase t = capRadius*Real.sin (t-capAngle) := by
  rw [Real.sin_sub,capAngle_frame.1,capAngle_frame.2]
  dsimp [heightPhase]
  field_simp [capRadius_pos.ne']

lemma heightPhase_mono : MonotoneOn heightPhase (Set.Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg (d := fun t => L*Real.cos t+c*Real.sin t)
  · unfold heightPhase
    fun_prop
  · intro t _
    unfold heightPhase
    convert (((hasDerivAt_id' t).sin.const_mul L).fun_sub
      ((hasDerivAt_id' t).cos.const_mul c)) using 1
    simp
  · intro t ht
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1,Real.pi_pos],ht.2.le⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2,Real.pi_pos])
    exact add_nonneg (mul_nonneg (by norm_num [L]) hc) (mul_nonneg (by norm_num [c]) hs)

lemma circleAngle_height {y : ℝ} (hy : 0 ≤ y ∧ y ≤ L) :
    heightPhase (circleAngle y) = y := by
  rw [heightPhase_shift]
  simp only [circleAngle,add_sub_cancel_right]
  have hr := capRadius_pos
  have hyfrac : -1 ≤ y/capRadius ∧ y/capRadius ≤ 1 := by
    constructor
    · linarith [div_nonneg hy.1 hr.le]
    · exact (div_le_one hr).mpr (hy.2.trans capRadius_gt_L.le)
  rw [Real.sin_arcsin hyfrac.1 hyfrac.2]
  field_simp

lemma circleAngle_ge_phase {y : ℝ} (hy : 0 ≤ y) : capAngle ≤ circleAngle y := by
  have ha := Real.arcsin_nonneg.mpr (div_nonneg hy capRadius_pos.le)
  dsimp [circleAngle]
  linarith

lemma circleAngle_lower {y t : ℝ} (hy : 0 ≤ y ∧ y ≤ L)
    (ht : 0 ≤ t ∧ t ≤ Real.pi/2) (hh : heightPhase t < y) : t < circleAngle y := by
  by_contra! h
  have hm := heightPhase_mono (circleAngle_range hy) ht h
  rw [circleAngle_height hy] at hm
  linarith

/-- The midpoint of two arc directions supports at least their mean height. -/
lemma circleAngle_pair_lower {y z t : ℝ} (hy : 0 ≤ y ∧ y ≤ L)
    (hz : 0 ≤ z ∧ z ≤ L) (hsum : y+z=1)
    (ht : 0 ≤ t ∧ t ≤ Real.pi/2) (hh : heightPhase t < 1/2) :
    2*t < circleAngle y+circleAngle z := by
  let a := circleAngle y
  let b := circleAngle z
  let mid := (a+b)/2
  have ha := circleAngle_range hy
  have hb := circleAngle_range hz
  have hmid : 0 ≤ mid ∧ mid ≤ Real.pi/2 := by
    dsimp [mid,a,b]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have hstart : capAngle ≤ mid := by
    dsimp [mid,a,b]
    linarith [circleAngle_ge_phase hy.1,circleAngle_ge_phase hz.1]
  have hzero : heightPhase capAngle = 0 := by rw [heightPhase_shift]; simp
  have hnonneg := heightPhase_mono ⟨capAngle_range.1,capAngle_range.2.le⟩ hmid hstart
  rw [hzero] at hnonneg
  have he : heightPhase a+heightPhase b = 2*Real.cos ((a-b)/2)*heightPhase mid := by
    dsimp [heightPhase,mid]
    linear_combination L*(Real.sin_add_sin a b)-c*(Real.cos_add_cos a b)
  have hmean : 1 ≤ 2*heightPhase mid := by
    have hprod := mul_le_mul_of_nonneg_right (Real.cos_le_one ((a-b)/2)) hnonneg
    have htotal : heightPhase a+heightPhase b = 1 := by
      dsimp [a,b]
      rw [circleAngle_height hy,circleAngle_height hz,hsum]
    nlinarith only [he,hprod,htotal]
  by_contra! h
  have hm : mid ≤ t := by dsimp [mid,a,b]; linarith
  have hmono := heightPhase_mono hmid ht hm
  linarith

lemma heightPhase_taylor {t : ℝ} (ht : 0 ≤ t) :
    heightPhase t ≤ L*S9 t-c*C10 t := by
  have hs := mul_le_mul_of_nonneg_left (sin_le_S9 ht) (by norm_num [L] : (0:ℝ) ≤ L)
  have hc := mul_le_mul_of_nonneg_left (C10_le_cos ht) (by norm_num [c] : (0:ℝ) ≤ c)
  dsimp [heightPhase]
  linarith

lemma heightPhase_0899 : heightPhase 0.899 < 1/2 := by
  have h := heightPhase_taylor (show (0:ℝ) ≤ 0.899 by norm_num)
  norm_num [L,c,S9,C10,C8] at h
  linarith

lemma heightPhase_1437 : heightPhase 1.437 < 0.862 := by
  have h := heightPhase_taylor (show (0:ℝ) ≤ 1.437 by norm_num)
  norm_num [L,c,S9,C10,C8] at h
  linarith

lemma heightPhase_123 : heightPhase 1.23 < 3/4 := by
  have h := heightPhase_taylor (show (0:ℝ) ≤ 1.23 by norm_num)
  norm_num [L,c,S9,C10,C8] at h
  linarith

lemma circleAngle_deriv {y : ℝ} (hy : 0 ≤ y ∧ y ≤ L) :
    HasDerivAt circleAngle (1/Real.sqrt (radiusSq-y^2)) y := by
  have hr := capRadius_pos
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hrad : 0 < radiusSq-y^2 := by norm_num [L,radiusSq] at *; linarith
  have hroot := Real.sqrt_pos.mpr hrad
  have hyfrac : -1 < y/capRadius ∧ y/capRadius < 1 := by
    constructor
    · linarith [div_nonneg hy.1 hr.le]
    · exact (div_lt_one hr).mpr (hy.2.trans_lt capRadius_gt_L)
  have hn : 1-(y/capRadius)^2 = (radiusSq-y^2)/capRadius^2 := by
    field_simp [hr.ne']
    rw [capRadius_sq]
  have hs : Real.sqrt (1-(y/capRadius)^2) = Real.sqrt (radiusSq-y^2)/capRadius := by
    rw [hn,Real.sqrt_div hrad.le,Real.sqrt_sq_eq_abs,abs_of_pos hr]
  have h := ((Real.hasDerivAt_arcsin (ne_of_gt hyfrac.1) (ne_of_lt hyfrac.2)).comp y
    ((hasDerivAt_id' y).div_const capRadius)).add_const capAngle
  unfold circleAngle
  convert h using 1
  · funext z
    rfl
  · rw [hs]
    field_simp

lemma circle_pair_width {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ 1/2) :
    (899/500) < circleAngle d+circleAngle (1-d) := by
  have hy : 0 ≤ d ∧ d ≤ L := by norm_num [L]; constructor <;> linarith
  have hz : 0 ≤ 1-d ∧ 1-d ≤ L := by norm_num [L]; constructor <;> linarith
  have h := circleAngle_pair_lower hy hz (by ring)
    (t := 0.899) (by constructor <;> linarith [Real.pi_gt_d2]) heightPhase_0899
  linarith

lemma bandA_large_depth {d : ℝ} (hd : c ≤ d ∧ d ≤ 1/2) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (347/200) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ L ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  have hy : 0 ≤ d ∧ d ≤ L := by norm_num [L,c] at *; constructor <;> linarith
  have hz : 0 ≤ 1-d ∧ 1-d ≤ L := by norm_num [L,c] at *; constructor <;> linarith
  have hd2 := pow_le_pow_left₀ (by norm_num [c] : (0:ℝ) ≤ c) hd.1 2
  have hz2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2)
    (by linarith : (1/2:ℝ) ≤ 1-d) 2
  have hclip : radiusSq ≤ L^2+d^2 := by norm_num [radiusSq,L,c] at *; linarith
  have hclip' : radiusSq ≤ L^2+(1-d)^2 := by norm_num [radiusSq,L] at *; linarith
  apply forbidden_of_supports le_rfl ⟨hy.1,by linarith⟩
    (circleSupport le_rfl hy hclip) (circleSupport le_rfl hz hclip')
  change (347/200:ℝ) < circleAngle d+circleAngle (1-d)
  have h := circle_pair_width (by norm_num [c] at hd; exact ⟨by linarith,hd.2⟩)
  linarith

/-! ## The narrower rectangle: the minimum of its supporting-angle sum -/

def cornerAngle (d : ℝ) : ℝ := 2*Real.arctan (d/L)

lemma cornerAngle_projection (d : ℝ) :
    L*Real.cos (cornerAngle d)+d*Real.sin (cornerAngle d)=L := by
  let a := Real.arctan (d/L)
  have hr : L*Real.sin a = d*Real.cos a := by
    dsimp [a]
    rw [Real.sin_arctan,Real.cos_arctan]
    field_simp [show L ≠ 0 by norm_num [L]]
  dsimp [cornerAngle]
  rw [Real.cos_two_mul,Real.sin_two_mul]
  have hs := Real.sin_sq_add_cos_sq a
  change L*(2*Real.cos a^2-1)+d*(2*Real.sin a*Real.cos a)=L
  linear_combination 2*L*hs-2*Real.sin a*hr

lemma cornerAngle_mono : Monotone cornerAngle := by
  intro x y hxy
  have h := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right hxy (by norm_num [L] : (0:ℝ) ≤ L))
  dsimp [cornerAngle]
  linarith

def cornerSupport {d : ℝ} (hd : 0 ≤ d ∧ d ≤ c) : Support L d where
  x := L
  y := d
  angle := cornerAngle d
  rectangle := ⟨by norm_num [L],le_rfl,hd.1,le_rfl⟩
  radius := by
    have h := pow_le_pow_left₀ hd.1 hd.2 2
    norm_num [L,c,radiusSq] at *
    linarith
  angle_range := by
    have h0 := Real.arctan_nonneg.mpr (div_nonneg hd.1 (by norm_num [L] : (0:ℝ) ≤ L))
    have h1 := Real.arctan_strictMono.monotone
      (show d/L ≤ 1 by norm_num [L,c] at *; linarith [hd.2])
    rw [Real.arctan_one] at h1
    dsimp [cornerAngle]
    constructor <;> linarith [Real.pi_lt_four]
  projection := (cornerAngle_projection d).ge

def bandAWidth (d : ℝ) : ℝ := cornerAngle d+circleAngle (1-d)
def widthSlope (d : ℝ) : ℝ := 2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2)
def widthPolynomial (d : ℝ) : ℝ :=
  d^4+6*L^2*d^2-8*L^2*d+4*L^2-3*L^4-4*L^2*c^2

lemma bandAWidth_deriv {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ c) :
    HasDerivAt bandAWidth (widthSlope d) d := by
  have hy : 0 ≤ 1-d ∧ 1-d ≤ L := by
    norm_num [L,c] at *
    constructor <;> linarith [hd.1,hd.2]
  have ha := (((hasDerivAt_id' d).div_const L).arctan).const_mul 2
  have he := (circleAngle_deriv hy).comp d ((hasDerivAt_id' d).const_sub 1)
  unfold bandAWidth cornerAngle widthSlope
  convert ha.fun_add he using 1
  · funext z
    rfl
  · norm_num [L]
    field_simp
    ring

lemma widthPolynomial_decreasing : AntitoneOn widthPolynomial (Set.Icc 0 c) := by
  apply antiOn_of_hasDeriv_nonpos (d := fun d => 4*d^3+12*L^2*d-8*L^2)
  · unfold widthPolynomial
    fun_prop
  · intro d _
    unfold widthPolynomial
    convert (((((hasDerivAt_id' d).pow 4).add
      (((hasDerivAt_id' d).pow 2).const_mul (6*L^2))).sub
      ((hasDerivAt_id' d).const_mul (8*L^2))).add_const
      (4*L^2-3*L^4-4*L^2*c^2)) using 1
    · funext x
      dsimp
      ring
    · dsimp
      ring
  · intro d hd
    have h3 := pow_le_pow_left₀ hd.1.le hd.2.le 3
    norm_num [L,c] at *
    linarith

/-- The polynomial and the width derivative have opposite signs. -/
lemma widthSlope_factor {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ c) :
    ∃ t : ℝ, 0 < t ∧ widthPolynomial d = -t*widthSlope d := by
  have hy : 0 ≤ 1-d ∧ 1-d ≤ L := by
    norm_num [L,c] at *
    constructor <;> linarith [hd.1,hd.2]
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hrad : 0 < radiusSq-(1-d)^2 := by norm_num [radiusSq,L] at *; linarith
  let r := Real.sqrt (radiusSq-(1-d)^2)
  let q := L^2+d^2
  have hr : 0 < r := Real.sqrt_pos.mpr hrad
  have hs : r^2 = radiusSq-(1-d)^2 := Real.sq_sqrt hrad.le
  have hq : 0 < q := by dsimp [q]; norm_num [L]; positivity
  have hL : 0 < L := by norm_num [L]
  refine ⟨q*r*(q+2*L*r),by positivity,?_⟩
  have hpoly : widthPolynomial d = q^2-(2*L*r)^2 := by
    rw [mul_pow,mul_pow,hs]
    norm_num [widthPolynomial,q,L,c,radiusSq]
    ring
  rw [hpoly]
  change q^2-(2*L*r)^2 = -(q*r*(q+2*L*r))*(2*L/q-1/r)
  field_simp
  ring

lemma widthSlope_nonpos {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ c)
    (hp : 0 ≤ widthPolynomial d) : widthSlope d ≤ 0 := by
  obtain ⟨t,ht,he⟩ := widthSlope_factor hd
  nlinarith

lemma widthSlope_nonneg {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ c)
    (hp : widthPolynomial d ≤ 0) : 0 ≤ widthSlope d := by
  obtain ⟨t,ht,he⟩ := widthSlope_factor hd
  nlinarith

lemma bandAWidth_continuous : Continuous bandAWidth := by
  exact ((Real.continuous_arctan.comp (continuous_id.div_const L)).const_mul 2).add
    ((Real.continuous_arcsin.comp ((continuous_const.sub continuous_id).div_const capRadius)).add_const capAngle)

lemma bandAWidth_decreasing : AntitoneOn bandAWidth (Set.Icc (1/12) 0.1379) := by
  apply antiOn_of_hasDeriv_nonpos bandAWidth_continuous.continuousOn
    (fun d hd => bandAWidth_deriv ⟨hd.1.le,by norm_num [c]; linarith [hd.2]⟩)
  intro d hd
  apply widthSlope_nonpos ⟨hd.1.le,by norm_num [c]; linarith [hd.2]⟩
  have h := widthPolynomial_decreasing
    (show d ∈ Set.Icc 0 c by norm_num [c]; constructor <;> linarith [hd.1,hd.2])
    (show (0.1379:ℝ) ∈ Set.Icc 0 c by norm_num [c]) hd.2.le
  have hp : 0 < widthPolynomial 0.1379 := by norm_num [widthPolynomial,L,c]
  linarith

lemma bandAWidth_increasing : MonotoneOn bandAWidth (Set.Icc 0.138 c) := by
  apply monoOn_of_hasDeriv_nonneg bandAWidth_continuous.continuousOn
    (fun d hd => bandAWidth_deriv ⟨by linarith [hd.1],hd.2.le⟩)
  intro d hd
  apply widthSlope_nonneg ⟨by linarith [hd.1],hd.2.le⟩
  have h := widthPolynomial_decreasing
    (show (0.138:ℝ) ∈ Set.Icc 0 c by norm_num [c])
    (show d ∈ Set.Icc 0 c by constructor; linarith [hd.1]; exact hd.2.le) hd.1.le
  have hp : widthPolynomial 0.138 < 0 := by norm_num [widthPolynomial,L,c]
  linarith

lemma circleAngle_mono : Monotone circleAngle := by
  intro x y hxy
  have h := Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hxy capRadius_pos.le)
  dsimp [circleAngle]
  linarith

lemma bandA_middle_width {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ c) :
    (347/200) < bandAWidth d := by
  have hcorner : (0.298:ℝ) < cornerAngle 0.1379 := by
    have h := Arithmetic.arctan_lower_cubic (x := 0.1379/L) (by norm_num [L])
    dsimp [cornerAngle]
    norm_num [L] at h ⊢
    linarith
  have hcircle : (1.437:ℝ) < circleAngle 0.862 :=
    circleAngle_lower (by norm_num [L])
      (by constructor <;> linarith [Real.pi_gt_d2]) heightPhase_1437
  have hbase : (347/200:ℝ) < cornerAngle 0.1379+circleAngle 0.862 := by linarith
  have hcompare : cornerAngle 0.1379+circleAngle 0.862 ≤ bandAWidth d := by
    by_cases hlo : d ≤ 0.1379
    · have h := bandAWidth_decreasing ⟨hd.1,hlo⟩
        (show (0.1379:ℝ) ∈ Set.Icc (1/12) 0.1379 by norm_num) hlo
      have he := circleAngle_mono (show (0.862:ℝ) ≤ 1-0.1379 by norm_num)
      dsimp [bandAWidth] at h ⊢
      linarith
    · by_cases hhi : 0.138 ≤ d
      · have h := bandAWidth_increasing
          (show (0.138:ℝ) ∈ Set.Icc 0.138 c by norm_num [c]) ⟨hhi,hd.2⟩ hhi
        have hc := cornerAngle_mono (show (0.1379:ℝ) ≤ 0.138 by norm_num)
        norm_num [bandAWidth] at h
        dsimp [bandAWidth]
        linarith
      · have hc := cornerAngle_mono (le_of_not_ge hlo)
        have he := circleAngle_mono (show (0.862:ℝ) ≤ 1-d by linarith)
        dsimp [bandAWidth]
        linarith
  exact hbase.trans_le hcompare

lemma bandA_middle_depth {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ c) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (347/200) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ L ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  have hy : 0 ≤ 1-d ∧ 1-d ≤ L := by
    norm_num [L,c] at *
    constructor <;> linarith [hd.1,hd.2]
  have hhalf : c ≤ 1-d := by norm_num [c] at *; linarith [hd.2]
  have hy2 := pow_le_pow_left₀ (by norm_num [c] : (0:ℝ) ≤ c) hhalf 2
  have hclip : radiusSq ≤ L^2+(1-d)^2 := by norm_num [radiusSq,L,c] at *; linarith
  apply forbidden_of_supports le_rfl ⟨by linarith [hd.1],by norm_num [c] at hd; linarith [hd.2]⟩
    (cornerSupport ⟨by linarith [hd.1],hd.2⟩) (circleSupport le_rfl hy hclip)
  exact bandA_middle_width hd

lemma bandB_large_depth {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) (hlarge : 217/3600 ≤ d^2) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (899/500) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ (19/20) ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  have hd0 : 1/12 ≤ d := by nlinarith [sq_nonneg (d-1/12)]
  have hy : 0 ≤ d ∧ d ≤ L := by norm_num [L]; exact ⟨hd.1,by linarith⟩
  have hz : 0 ≤ 1-d ∧ 1-d ≤ L := by norm_num [L]; constructor <;> linarith
  have hz2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2)
    (by linarith : (1/2:ℝ) ≤ 1-d) 2
  have hclip : radiusSq ≤ (19/20:ℝ)^2+d^2 := by norm_num [radiusSq]; linarith
  have hclip' : radiusSq ≤ (19/20:ℝ)^2+(1-d)^2 := by norm_num [radiusSq]; linarith
  apply forbidden_of_supports (by norm_num [L]) ⟨hd.1,by linarith⟩
    (circleSupport (by norm_num [L]) hy hclip)
    (circleSupport (by norm_num [L]) hz hclip')
  change (899/500:ℝ) < circleAngle d+circleAngle (1-d)
  exact circle_pair_width ⟨hd0,hd.2⟩

def bandBAngle (d : ℝ) : ℝ := 0.36+(5/4)*(d-1/12)

lemma bandBAngle_projection {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ 1/4) :
    L < (19/20)*Real.cos (bandBAngle d)+d*Real.sin (bandBAngle d) := by
  let t := d-1/12
  have ht : 0 ≤ t ∧ t ≤ 1/6 := by dsimp [t]; constructor <;> linarith [hd.1,hd.2]
  have ht2 : t^2 ≤ 1/36 := by
    have h := pow_le_pow_left₀ ht.1 ht.2 2
    norm_num at h
    exact h
  have ht3 : t^3 ≤ t^2/6 := by
    have h := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2)
    nlinarith only [h]
  have ht4 : t^4 ≤ t^2/36 := by
    have h := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)
    nlinarith only [h]
  have hdEq : d = t+1/12 := by dsimp [t]; ring
  have hpoly : L < (19/20)*(1-(bandBAngle d)^2/2)+
      d*(bandBAngle d-(bandBAngle d)^3/6) := by
    rw [hdEq]
    dsimp [bandBAngle]
    norm_num [L]
    nlinarith only [ht.1,ht3,ht4,sq_nonneg t]
  have hangle : 0 ≤ bandBAngle d := by dsimp [bandBAngle]; linarith [hd.1]
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := bandBAngle d))
    (by norm_num : (0:ℝ) ≤ 19/20)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hangle)
    (by linarith [hd.1] : 0 ≤ d)
  linarith only [hpoly,hc,hs]

/-- A linear choice of direction suffices before the corner reaches the cap circle. -/
def bandBCornerSupport {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ 1/4)
    (hr : d^2 ≤ 217/3600) : Support (19/20) d where
  x := 19/20
  y := d
  angle := bandBAngle d
  rectangle := by norm_num [Rectangle]; linarith [hd.1]
  radius := by norm_num [radiusSq]; linarith
  angle_range := by dsimp [bandBAngle]; constructor <;> linarith [hd.1,hd.2]
  projection := (bandBAngle_projection hd).le

lemma bandB_sum_decreasing :
    AntitoneOn (fun d => bandBAngle d+circleAngle (1-d)) (Set.Icc (1/12) (1/4)) := by
  apply antiOn_of_hasDeriv_nonpos
    (d := fun d => 5/4-1/Real.sqrt (radiusSq-(1-d)^2))
  · dsimp [bandBAngle,circleAngle]
    fun_prop
  · intro d hd
    have hy : 0 ≤ 1-d ∧ 1-d ≤ L := by norm_num [L]; constructor <;> linarith [hd.1,hd.2]
    have ha := (((hasDerivAt_id' d).sub_const (1/12)).const_mul (5/4)).const_add (0.36)
    have hc := (circleAngle_deriv hy).comp d ((hasDerivAt_id' d).const_sub 1)
    convert ha.fun_add hc using 1 <;> simp [bandBAngle,sub_eq_add_neg]
  · intro d hd
    have hy : 0 ≤ 1-d ∧ 1-d ≤ L := by norm_num [L]; constructor <;> linarith [hd.1,hd.2]
    have hu := pow_le_pow_left₀ hy.1 hy.2 2
    have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/4)
      (by linarith [hd.2] : (3/4:ℝ) ≤ 1-d) 2
    have hrad : 0 < radiusSq-(1-d)^2 := by norm_num [L,radiusSq] at *; linarith
    have hr := Real.sqrt_pos.mpr hrad
    have hs := Real.sq_sqrt hrad.le
    have hsmall : Real.sqrt (radiusSq-(1-d)^2) < 4/5 := by
      norm_num [radiusSq] at *
      nlinarith [sq_nonneg (Real.sqrt (radiusSq-(1-d)^2)-4/5)]
    have hh : (5/4:ℝ) ≤ 1/Real.sqrt (radiusSq-(1-d)^2) :=
      (le_div_iff₀ hr).mpr (by linarith)
    linarith

lemma bandB_middle_width {d : ℝ} (hd : 1/12 ≤ d ∧ d ≤ 1/4) :
    (899/500) < bandBAngle d+circleAngle (1-d) := by
  have h := bandB_sum_decreasing hd (by norm_num : (1/4:ℝ) ∈ Set.Icc (1/12) (1/4)) hd.2
  have he : (1.23:ℝ) < circleAngle (3/4) :=
    circleAngle_lower (by norm_num [L])
      (by constructor <;> linarith [Real.pi_gt_d2]) heightPhase_123
  norm_num [bandBAngle] at h ⊢
  linarith

/-- The wider rectangle needs only elementary supporting points and a circular arc. -/
theorem bandB_forbidden {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (899/500) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ (19/20) ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  by_cases hlow : d ≤ 1/12
  · exact bandB_small_depth ⟨hd.1,hlow⟩
  · by_cases hcircle : 217/3600 ≤ d^2
    · exact bandB_large_depth hd hcircle
    · have hd' : 1/12 ≤ d ∧ d ≤ 1/4 :=
        ⟨(lt_of_not_ge hlow).le,by nlinarith [sq_nonneg (d-1/4)]⟩
      have hy : 0 ≤ 1-d ∧ 1-d ≤ L := by norm_num [L]; constructor <;> linarith [hd'.1,hd'.2]
      have hy2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/4)
        (by linarith [hd'.2] : (3/4:ℝ) ≤ 1-d) 2
      have hclip : radiusSq ≤ (19/20:ℝ)^2+(1-d)^2 := by norm_num [radiusSq]; linarith
      apply forbidden_of_supports (by norm_num [L]) ⟨hd.1,by linarith⟩
        (bandBCornerSupport hd' (lt_of_not_ge hcircle).le)
        (circleSupport (by norm_num [L]) hy hclip)
      change (899/500:ℝ) < bandBAngle d+circleAngle (1-d)
      exact bandB_middle_width hd'

end SquaresInCircles.Eight.CentralForbidden.Analytic
