module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetPositive
public import SquaresInCircles.Eight.TableFree.SecondMixedCoreCorner
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra

/-!
# The original negative target-secondary contact

Uncompiled source draft.  The actual owner forces the negative angle
below `.44152` and the first target coordinate is an explicit harmonic
function of the unchanged core point.  Its value lies on the original
outer arc and precedes the original outer target.  The diagonal curve
is continued slightly past its last physical contact only for scalar
endpoint estimates; its radical remains positive there.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target
open CommonQuarter CorePairGeometry Arithmetic

def cap : ℝ := 5519/12500
def angles : Set ℝ := Icc 0 cap
def contact (a b x : ℝ) : ℝ :=
  1/2+(1/2-b)*Real.cos x+(a+1/2)*Real.sin x
def diagonal (x : ℝ) : ℝ := contact CoreAngleEndpoint.diagonal CoreAngleEndpoint.diagonal x
def speed (x : ℝ) : ℝ :=
  (CoreAngleEndpoint.diagonal-1/2)*Real.sin x+(CoreAngleEndpoint.diagonal+1/2)*Real.cos x
def cut (x : ℝ) : ℝ := outerDiagonal-diagonal x

lemma angle_subset {x : ℝ} (hx : x∈angles) : x∈Icc 0 (7/10) :=
  ⟨hx.1,by dsimp [cap] at hx; linarith [hx.2]⟩

lemma core_diagonal_bounds :
    (279462782549439/500000000000000:ℝ)<CoreAngleEndpoint.diagonal ∧
      CoreAngleEndpoint.diagonal<558925565098879/1000000000000000 := by
  have hh := CoreAngleEndpoint.diagonal_sq
  have hp := CoreAngleEndpoint.diagonal_bounds.1
  constructor <;> nlinarith

lemma cap_trig :
    (427314195019/1000000000000:ℝ)<Real.sin cap ∧
      Real.sin cap<21365709751/50000000000 ∧
    (904103190313/1000000000000:ℝ)<Real.cos cap ∧
      Real.cos cap<452051595157/500000000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := cap) (by norm_num [cap])
  have hsU := HighOrderTaylor.sin_le_S13 (x := cap) (by norm_num [cap])
  have hc := HighOrderTaylor.C14_le_cos (x := cap) (by norm_num [cap])
  have hcU := HighOrderTaylor.cos_le_C12 (x := cap) (by norm_num [cap])
  norm_num [cap,HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma diagonal_hasDerivAt (x : ℝ) : HasDerivAt diagonal (speed x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (1/2-CoreAngleEndpoint.diagonal)).const_add
    (1/2)).add ((Real.hasDerivAt_sin x).const_mul (CoreAngleEndpoint.diagonal+1/2)))
    using 1 <;> dsimp [diagonal,contact,speed] <;> ring

lemma speed_hasDerivAt (x : ℝ) : HasDerivAt speed (1/2-diagonal x) x := by
  convert ((Real.hasDerivAt_sin x).const_mul (CoreAngleEndpoint.diagonal-1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (CoreAngleEndpoint.diagonal+1/2))
    using 1 <;> dsimp [diagonal,contact,speed] <;> ring

lemma speed_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<speed x := by
  have tr := positive_trig hx
  have ha := CoreAngleEndpoint.diagonal_bounds.1
  have hp := mul_pos (show 0<CoreAngleEndpoint.diagonal+1/2 by linarith)
    (show 0<Real.cos x by linarith [tr.1])
  have hq := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith) tr.2.2.1
  dsimp [speed]
  linarith

lemma diagonal_monotone : MonotoneOn diagonal (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (diagonal_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => diagonal_hasDerivAt x)
    (fun x hx => (speed_positive (Ioo_subset_Icc_self hx)).le)

lemma diagonal_zero : diagonal 0=1-CoreAngleEndpoint.diagonal := by
  simp only [diagonal,contact,Real.sin_zero,Real.cos_zero]
  ring

lemma cap_coordinates : (89921913/100000000:ℝ)<diagonal cap ∧
    diagonal cap<89921914/100000000 ∧ (491/500:ℝ)<speed cap := by
  have hd := core_diagonal_bounds
  have ht := cap_trig
  have hcl := mul_le_mul
    (show (29462782549439/500000000000000:ℝ)≤CoreAngleEndpoint.diagonal-1/2 by linarith)
    ht.2.2.1.le (by norm_num : (0:ℝ)≤904103190313/1000000000000)
    (by linarith [hd.1] : 0≤CoreAngleEndpoint.diagonal-1/2)
  have hcu := mul_le_mul
    (show CoreAngleEndpoint.diagonal-1/2≤58925565098879/1000000000000000 by linarith)
    ht.2.2.2.le (by linarith [ht.2.2.1] : 0≤Real.cos cap)
    (by norm_num : (0:ℝ)≤58925565098879/1000000000000000)
  have hsl := mul_le_mul
    (show (529462782549439/500000000000000:ℝ)≤CoreAngleEndpoint.diagonal+1/2 by linarith)
    ht.1.le (by norm_num : (0:ℝ)≤427314195019/1000000000000)
    (by linarith [hd.1] : 0≤CoreAngleEndpoint.diagonal+1/2)
  have hsu := mul_le_mul
    (show CoreAngleEndpoint.diagonal+1/2≤1058925565098879/1000000000000000 by linarith)
    ht.2.1.le (by linarith [ht.1] : 0≤Real.sin cap)
    (by norm_num : (0:ℝ)≤1058925565098879/1000000000000000)
  have hwl := mul_le_mul
    (show (529462782549439/500000000000000:ℝ)≤CoreAngleEndpoint.diagonal+1/2 by linarith)
    ht.2.2.1.le (by norm_num : (0:ℝ)≤904103190313/1000000000000)
    (by linarith [hd.1] : 0≤CoreAngleEndpoint.diagonal+1/2)
  have hwr := mul_le_mul
    (show (29462782549439/500000000000000:ℝ)≤CoreAngleEndpoint.diagonal-1/2 by linarith)
    ht.1.le (by norm_num : (0:ℝ)≤427314195019/1000000000000)
    (by linarith [hd.1] : 0≤CoreAngleEndpoint.diagonal-1/2)
  dsimp [diagonal,contact,speed]
  exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

lemma original_angle {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤-a*Real.sin x+b*Real.cos x+B) : x<cap := by
  have tr := positive_trig hx
  have ha := ShortMixedZero.core_primary_lower hs
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have hAs := mul_le_mul_of_nonneg_right ha tr.2.2.1
  have hBc := mul_le_mul_of_nonneg_right hb (show 0≤Real.cos x by linarith [tr.1])
  have hd : diagonal x≤outerDiagonal := by
    dsimp [diagonal,contact]
    linarith [(outer_bounds ht).2.2.2.1]
  by_contra! hlarge
  have hcap : cap∈Icc 0 (7/10) := by norm_num [cap]
  have hmono := diagonal_monotone hcap hx hlarge
  linarith [cap_coordinates.1,ShortMixedZero.fine_diagonal_bounds.2]

lemma contact_lower {a b x : ℝ} (hs : CoreState a b) (hx : x∈angles) :
    1-b≤contact a b x := by
  have hc := CoreAngleEndpoint.state_bounds hs
  have tr := positive_trig (angle_subset hx)
  have hb := mul_nonneg hc.2.2.1 (sub_nonneg.mpr tr.2.1)
  have ha := mul_nonneg (show 0≤a by linarith [hc.1]) tr.2.2.1
  dsimp [contact]
  linarith [tr.2.2.2.2.2]

lemma original_contact {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈angles)
    (hm : (1+Real.sin x+Real.cos x)/2≤-a*Real.sin x+b*Real.cos x+B) :
    contact a b x∈Icc 0 outerDiagonal ∧ contact a b x≤B := by
  have hl := contact_lower hs hx
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.2.2
  have he : contact a b x≤B := by dsimp [contact]; linarith
  exact ⟨⟨by linarith [CoreAngleEndpoint.diagonal_bounds.2],
    he.trans (outer_bounds ht).2.2.2.1⟩,he⟩

lemma original_cost (r : Row) {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈angles)
    (hm : (1+Real.sin x+Real.cos x)/2≤-a*Real.sin x+b*Real.cos x+B) :
    -x+c r+g r*b+(F r).outer (contact a b x)≤-x+c r+g r*b+(F r).outer B := by
  have hh := original_contact hs ht hx hm
  exact add_le_add_left (outer_monotone r hh.1
    ⟨ht.1,(outer_bounds ht).2.2.2.1⟩ hh.2) _

lemma diagonal_bounds {x : ℝ} (hx : x∈angles) :
    (441/1000:ℝ)<diagonal x ∧ diagonal x<(9/10:ℝ) := by
  have hl := diagonal_monotone (by norm_num) (angle_subset hx) hx.1
  have hu := diagonal_monotone (angle_subset hx) (by norm_num [cap]) hx.2
  rw [diagonal_zero] at hl
  exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.2],by linarith [cap_coordinates.2.1]⟩

lemma speed_bounds {x : ℝ} (hx : x∈angles) :
    (491/500:ℝ)<speed x ∧ speed x<(1061/1000:ℝ) ∧
      (24/25:ℝ)<(speed x)^2 ∧ (speed x)^2<(563/500:ℝ) := by
  have hc : ConcaveOn ℝ angles speed :=
    concave_of_deriv2 (fun t _ => speed_hasDerivAt t)
      (fun t _ => (diagonal_hasDerivAt t).const_sub (1/2))
      (fun t ht => neg_nonpos.mpr (speed_positive (angle_subset ht)).le)
  have hl : (491/500:ℝ)<speed x := by
    apply concave_gt_of_endpoints hc hx
    · simp only [speed,Real.sin_zero,Real.cos_zero]
      linarith [CoreAngleEndpoint.diagonal_bounds.1]
    · exact cap_coordinates.2.2
  have he : (speed x)^2+(diagonal x-1/2)^2=2*CoreAngleEndpoint.diagonal^2+1/2 := by
    dsimp [speed,diagonal,contact]
    linear_combination (2*CoreAngleEndpoint.diagonal^2+1/2)*(Real.sin_sq_add_cos_sq x)
  have hd := core_diagonal_bounds
  have hs : CoreAngleEndpoint.diagonal^2<(55892557/100000000:ℝ)^2 := by
    nlinarith [hd.1,hd.2]
  exact ⟨hl,by nlinarith [sq_nonneg (diagonal x-1/2)],by nlinarith,
    by nlinarith [sq_nonneg (diagonal x-1/2)]⟩

lemma cosine_bounds {x : ℝ} (hx : x∈angles) :
    (9/10:ℝ)<Real.cos x ∧ (81/100:ℝ)<(Real.cos x)^2 := by
  have hs := pow_le_pow_left₀ hx.1 hx.2 2
  have hc := cos_lower_two hx.1
  have hcap : cap=(5519/12500:ℝ) := rfl
  constructor <;> nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target
