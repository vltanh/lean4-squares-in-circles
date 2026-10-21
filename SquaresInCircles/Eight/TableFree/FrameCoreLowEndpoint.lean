module

public import SquaresInCircles.Eight.TableFree.FrameCoreLowNorm
public import SquaresInCircles.Eight.TableFree.FrameCoreMidScalars
public import SquaresInCircles.Eight.TableFree.FrameCoreMidPrimaryContinuation

/-!
# Core/low endpoint supports on both physical quadrants

The axial negative-target support has an elementary initial bound and
one strong-convexity estimate.  The positive cut support uses one tangent
parabola on its whole interval.  Their actual second-quadrant continuations
are increasing, including all angle endpoints.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowEndpoint
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreMidScalars (ap cp trigAffine trigAffine_deriv trigAffine_monotone)

def axialB : ℝ := g*a0-cp
def cutB : ℝ := g*a1-cp
def axial (x : ℝ) : ℝ := x+ap+cp*Real.cos x-axialB*Real.sin x
def axialD (x : ℝ) : ℝ := 1-cp*Real.sin x-axialB*Real.cos x
def axialDD (x : ℝ) : ℝ := -cp*Real.cos x+axialB*Real.sin x
def negativeCut (x : ℝ) : ℝ :=
  x+ap+L1+(cp-g*b1)*Real.cos x-cutB*Real.sin x
def positiveCut (x : ℝ) : ℝ :=
  x+ap-L1+(cp+g*b1)*Real.cos x-cutB*Real.sin x
def axialSecond (x : ℝ) : ℝ := x+ap-cp*Real.cos x-axialB*Real.sin x
def negativeCutSecond (x : ℝ) : ℝ :=
  x+ap+L1+(-cp-g*b1)*Real.cos x-cutB*Real.sin x
def positiveCutSecond (x : ℝ) : ℝ :=
  x+ap-L1+(-cp+g*b1)*Real.cos x-cutB*Real.sin x

theorem coefficient_bounds :
    (107/100:ℝ)<axialB ∧ axialB<(269/250:ℝ) ∧
      0<cp-g*b1 ∧ cp-g*b1<1/10 ∧
        (19/20:ℝ)<cutB ∧ cutB<119/125 ∧ -cp+g*b1<0 := by
  have h0 := a0_bounds
  have h1 := a1_bounds
  have hb := b1_bounds
  dsimp [axialB,cutB,cp,g]
  repeat' constructor <;> linarith

theorem axial_deriv (x : ℝ) : HasDerivAt axial (axialD x) x := by
  convert (((hasDerivAt_id x).add_const ap).add
    ((Real.hasDerivAt_cos x).const_mul cp)).sub
    ((Real.hasDerivAt_sin x).const_mul axialB) using 1 <;> dsimp [axial,axialD] <;> ring

theorem axialD_deriv (x : ℝ) : HasDerivAt axialD (axialDD x) x := by
  convert (((Real.hasDerivAt_sin x).const_mul (-cp)).const_add 1).sub
    ((Real.hasDerivAt_cos x).const_mul axialB) using 1 <;> dsimp [axialD,axialDD] <;> ring

theorem axial_initial {x : ℝ} (hx : x∈Icc (0:ℝ) (1/2)) : (91/100:ℝ)<axial x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hs := Real.sin_le_self hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsin := mul_le_mul_of_nonneg_left hs (by linarith [coefficient_bounds.1] : 0≤axialB)
  have hB := mul_le_mul_of_nonneg_right coefficient_bounds.2.1.le hx.1
  have hcos := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤cp by norm_num [cp,g])
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  dsimp [axial,ap,cp,g] at *
  nlinarith

theorem axial_curvature {x : ℝ} (hx : x∈Icc (1/2:ℝ) (Real.pi/2)) :
    (1/20:ℝ)<axialDD x := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(1/2:ℝ)) hx.2 hx.1
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
  norm_num at hs0
  have hsin : (23/48:ℝ)≤Real.sin x := by linarith
  have hB := mul_le_mul_of_nonneg_right coefficient_bounds.1.le
    (show 0≤Real.sin x by linarith)
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
    (show (0:ℝ)≤cp by norm_num [cp,g])
  dsimp [axialDD,cp,g]
  nlinarith

theorem unit_trig :
    (4207/5000:ℝ)<Real.sin (1:ℝ) ∧ Real.sin (1:ℝ)<1683/2000 ∧
      (5403/10000:ℝ)<Real.cos (1:ℝ) ∧ Real.cos (1:ℝ)<1351/2500 := by
  have hsL := sin_lower_seven (show (0:ℝ)≤1 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤1 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤1 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤1 by norm_num)
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  repeat' constructor <;> linarith

theorem axial_contact : (24/25:ℝ)<axial 1 ∧ |axialD 1|<(1/20:ℝ) := by
  have ht := unit_trig
  have hb := coefficient_bounds
  have hsin := mul_le_mul_of_nonneg_right hb.2.1.le
    (show 0≤Real.sin (1:ℝ) by linarith [ht.1])
  have hcL := mul_le_mul_of_nonneg_right hb.1.le
    (show 0≤Real.cos (1:ℝ) by linarith [ht.2.2.1])
  have hcU := mul_le_mul_of_nonneg_right hb.2.1.le
    (show 0≤Real.cos (1:ℝ) by linarith [ht.2.2.1])
  dsimp [axial,axialD,ap,cp,g]
  refine ⟨by nlinarith,abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩

theorem axial_lower {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : (91/100:ℝ)<axial x := by
  by_cases hsmall : x≤1/2
  · exact axial_initial ⟨hx.1,hsmall⟩
  · have hx' : x∈Icc (1/2:ℝ) (Real.pi/2) := ⟨(lt_of_not_ge hsmall).le,hx.2⟩
    have ht : (1:ℝ)∈Icc (1/2:ℝ) (Real.pi/2) :=
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩
    have hd2 : (axialD 1)^2<(1/20:ℝ)^2 := by
      obtain ⟨hl,hu⟩ := abs_lt.mp axial_contact.2
      nlinarith
    have hh := positive_of_curvature (f := fun z => axial z-91/100)
      (d := axialD) (dd := axialDD) (κ := (1/20:ℝ)) (by norm_num) hx' ht
      (fun z _ => (axial_deriv z).sub_const (91/100))
      (fun z _ => axialD_deriv z) (fun z hz => (axial_curvature hz).le)
      (by nlinarith [axial_contact.1])
    linarith

theorem negativeCut_lower {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    (91/100:ℝ)<negativeCut x := by
  have hb := coefficient_bounds
  have hamp : (cp-g*b1)^2+(-cutB)^2<(1:ℝ)^2 := by
    nlinarith [sq_nonneg (1/10-(cp-g*b1)),sq_nonneg (119/125-cutB)]
  have hm := trigAffine_monotone (k := ap+L1) (l := (0:ℝ)) (u := Real.pi/2)
    (a := cp-g*b1) (b := -cutB) (by norm_num : (0:ℝ)<1) hamp
  have hh := hm ⟨le_rfl,by positivity⟩ hx hx.1
  have he : (103/100:ℝ)<negativeCut 0 := by
    dsimp [negativeCut,ap,cp,g]
    simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,zero_add]
    linarith [L1_bounds.1,b1_bounds.2]
  have hid (z : ℝ) : trigAffine 1 (ap+L1) (cp-g*b1) (-cutB) z=negativeCut z := by
    dsimp [trigAffine,negativeCut]
    ring
  rw [hid,hid] at hh
  linarith

def D : ℝ := cp+g*(12987/10000)/4
def B : ℝ := g*(3247/2500)-cp
def cutModel (x : ℝ) : ℝ := x+ap-307/1000+D*Real.cos x-B*Real.sin x
def cutModelD (x : ℝ) : ℝ := 1-D*Real.sin x-B*Real.cos x
def cutModelDD (x : ℝ) : ℝ := -D*Real.cos x+B*Real.sin x

theorem model_coefficients : 0<D ∧ D<4/5 ∧ (19/20:ℝ)<B ∧ B<1 := by
  norm_num [D,B,cp,g]

theorem cutModel_deriv (x : ℝ) : HasDerivAt cutModel (cutModelD x) x := by
  convert ((((hasDerivAt_id x).add_const ap).sub_const (307/1000)).add
    ((Real.hasDerivAt_cos x).const_mul D)).sub
    ((Real.hasDerivAt_sin x).const_mul B) using 1 <;> dsimp [cutModel,cutModelD] <;> ring

theorem cutModelD_deriv (x : ℝ) : HasDerivAt cutModelD (cutModelDD x) x := by
  convert (((Real.hasDerivAt_sin x).const_mul (-D)).const_add 1).sub
    ((Real.hasDerivAt_cos x).const_mul B) using 1 <;> dsimp [cutModelD,cutModelDD] <;> ring

theorem cutModel_curvature {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (1/2:ℝ)<cutModelDD x := by
  have ht := FrameCoreMidPrimaryContinuation.first_trig hx
  have hcos := mul_le_mul model_coefficients.2.1.le ht.2.2.le ht.2.1 (by norm_num)
  have hsin := mul_le_mul model_coefficients.2.2.1.le ht.1.le (by norm_num)
    (by linarith [model_coefficients.2.2.1] : 0≤B)
  dsimp [cutModelDD]
  nlinarith

theorem cut_contact_trig :
    (97193/100000:ℝ)<Real.sin (4/3:ℝ) ∧ Real.sin (4/3:ℝ)<19439/20000 ∧
      (23523/100000:ℝ)<Real.cos (4/3:ℝ) ∧ Real.cos (4/3:ℝ)<941/4000 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤4/3 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤4/3 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤4/3 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤4/3 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  repeat' constructor <;> linarith

theorem cut_contact : (459/500:ℝ)<cutModel (4/3:ℝ) ∧
    |cutModelD (4/3:ℝ)|<(1/1000:ℝ) := by
  have ht := cut_contact_trig
  dsimp [cutModel,cutModelD,D,B,ap,cp,g]
  refine ⟨by linarith,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

theorem cutModel_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (91/100:ℝ)<cutModel x := by
  have ht : (4/3:ℝ)∈Icc (6/5:ℝ) (Real.pi/2) :=
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩
  have hd2 : (cutModelD (4/3:ℝ))^2<(1/1000:ℝ)^2 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp cut_contact.2
    nlinarith
  have hh := positive_of_curvature (f := fun z => cutModel z-91/100)
    (d := cutModelD) (dd := cutModelDD) (κ := (1/2:ℝ)) (by norm_num) hx ht
    (fun z _ => (cutModel_deriv z).sub_const (91/100))
    (fun z _ => cutModelD_deriv z) (fun z hz => (cutModel_curvature hz).le)
    (by nlinarith [cut_contact.1])
  linarith

theorem positiveCut_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (91/100:ℝ)<positiveCut x := by
  have ht := FrameLowPair.quadrant
    (show x∈Icc 0 (Real.pi/2) from ⟨by linarith [hx.1],hx.2⟩)
  have hD : D≤cp+g*b1 := by dsimp [D,b1,g]; linarith [a1_bounds.1]
  have hB : cutB≤B := by dsimp [cutB,B,g]; linarith [a1_bounds.2]
  have hcos := mul_le_mul_of_nonneg_right hD ht.2.2.1
  have hsin := mul_le_mul_of_nonneg_right hB ht.1
  have hh := cutModel_lower hx
  dsimp [positiveCut,cutModel] at *
  linarith [L1_bounds.2]

theorem second_monotone {k a b : ℝ} (ha : a≤0) (hb : b≤0) :
    MonotoneOn (trigAffine 1 k a b) (Icc (Real.pi/2) Real.pi) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (trigAffine_deriv 1 k a b x).continuousAt.continuousWithinAt
  · exact fun x _ => trigAffine_deriv 1 k a b x
  · intro x hx
    have ht := second_signs (Ioo_subset_Icc_self hx)
    have h1 := mul_nonpos_of_nonpos_of_nonneg ha ht.1
    have h2 := mul_nonneg_of_nonpos_of_nonpos hb ht.2
    linarith

theorem axialSecond_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    (91/100:ℝ)<axialSecond x := by
  have hm := second_monotone (k := ap) (a := -cp) (b := -axialB)
    (by norm_num [cp,g]) (by linarith [coefficient_bounds.1])
  have hh := hm ⟨le_rfl,by linarith [Real.pi_pos]⟩ hx hx.1
  have he := axial_lower
    (show Real.pi/2∈Icc (0:ℝ) (Real.pi/2) from ⟨by positivity,le_rfl⟩)
  dsimp [trigAffine,axial,axialSecond] at *
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero] at *
  linarith

theorem negativeCutSecond_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    (91/100:ℝ)<negativeCutSecond x := by
  have hm := second_monotone (k := ap+L1) (a := -cp-g*b1) (b := -cutB)
    (by dsimp [cp,g]; linarith [b1_bounds.1])
    (by linarith [coefficient_bounds.2.2.2.2.1])
  have hh := hm ⟨le_rfl,by linarith [Real.pi_pos]⟩ hx hx.1
  have he := negativeCut_lower
    (show Real.pi/2∈Icc (0:ℝ) (Real.pi/2) from ⟨by positivity,le_rfl⟩)
  dsimp [trigAffine,negativeCut,negativeCutSecond] at *
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero] at *
  linarith

theorem positiveCutSecond_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    (91/100:ℝ)<positiveCutSecond x := by
  have hm := second_monotone (k := ap-L1) (a := -cp+g*b1) (b := -cutB)
    coefficient_bounds.2.2.2.2.2.2.le
    (by linarith [coefficient_bounds.2.2.2.2.1])
  have hh := hm ⟨le_rfl,by linarith [Real.pi_pos]⟩ hx hx.1
  have he := positiveCut_lower
    (show Real.pi/2∈Icc (6/5:ℝ) (Real.pi/2) from
      ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩)
  dsimp [trigAffine,positiveCut,positiveCutSecond] at *
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero] at *
  linarith

end SquaresInCircles.Eight.TableFree.FrameCoreLowEndpoint
