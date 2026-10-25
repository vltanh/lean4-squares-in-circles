module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreeLabels
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveNegativeThreeData

/-!
# Two increasing scalars for complete mixed quarter families

Both estimates hold on the entire lower half of the quarter window,
with a free label slope.  Their values are bounded only at its actual
left endpoint.  The elementary cotangent comparison retains the
aligned endpoint without division.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedAffine
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

def κ : ℝ := outerAxial-1/2
def first (g φ : ℝ) : ℝ := φ+g*(1/2+Real.cos φ/2-κ*Real.sin φ)
def firstD (g φ : ℝ) : ℝ := 1-g*(Real.sin φ/2+κ*Real.cos φ)
def second (g φ : ℝ) : ℝ := φ+g/2+g*(Real.cos φ-κ)/Real.sin φ
def secondD (g φ : ℝ) : ℝ := 1+g*(κ*Real.cos φ-1)/(Real.sin φ)^2

lemma κ_bounds : (457/500:ℝ)<κ ∧ κ<(183/200:ℝ) := by
  dsimp [κ]
  constructor <;> linarith [fine_outer_endpoint_bounds.1,outer_endpoint_bounds.2.1]

lemma left_mem : Lower lowerAngle := ⟨le_rfl,by dsimp [lowerAngle]; linarith⟩

lemma left_trig :
    (19121/25000:ℝ)<Real.sin lowerAngle ∧ Real.sin lowerAngle<15297/20000 ∧
    (64421/100000:ℝ)<Real.cos lowerAngle ∧ Real.cos lowerAngle<32211/50000 := by
  have hh := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at hh
  simp only [lowerAngle,Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,
    Real.cos_pi_div_two,one_mul,zero_mul,sub_zero,zero_add]
  exact ⟨by linarith [hh.2.1],by linarith [hh.2.2],
    by linarith [hh.1.1],by linarith [hh.1.2]⟩

lemma first_hasDerivAt (g φ : ℝ) : HasDerivAt (first g) (firstD g φ) φ := by
  exact ((hasDerivAt_id φ).add
    (((((Real.hasDerivAt_cos φ).div_const 2).const_add (1/2)).sub
      ((Real.hasDerivAt_sin φ).const_mul κ)).const_mul g)).congr_deriv
    (by dsimp only [firstD]; ring)

lemma firstD_hasDerivAt (g φ : ℝ) :
    HasDerivAt (firstD g) (g*(κ*Real.sin φ-Real.cos φ/2)) φ := by
  exact ((((Real.hasDerivAt_sin φ).div_const 2).add
    ((Real.hasDerivAt_cos φ).const_mul κ)).const_mul g).const_sub 1 |>.congr_deriv (by ring)

lemma firstD_monotone {g : ℝ} (hg : 0≤g) : MonotoneOn (firstD g) (Icc lowerAngle (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro φ hφ
    exact (firstD_hasDerivAt g φ).continuousAt.continuousWithinAt
  · intro φ hφ
    exact firstD_hasDerivAt g φ
  · intro φ hφ
    have ht := lower_trig (Ioo_subset_Icc_self hφ)
    have hm := mul_le_mul κ_bounds.1.le ht.1.le (by norm_num : (0:ℝ)≤19121/25000)
      (by linarith [κ_bounds.1] : 0≤κ)
    exact mul_nonneg hg (by nlinarith [ht.2.2.2.1])

lemma firstD_left {g : ℝ} (hg : g∈Icc (7/10) (197/200)) : 0<firstD g lowerAngle := by
  have ht := left_trig
  have hc := mul_le_mul κ_bounds.2.le ht.2.2.2.le
    (by linarith [ht.2.2.1] : 0≤Real.cos lowerAngle) (by norm_num : (0:ℝ)≤183/200)
  have hs : Real.sin lowerAngle/2+κ*Real.cos lowerAngle<(487/500:ℝ) := by
    nlinarith [ht.2.1]
  have hm := mul_le_mul hg.2 hs.le
    (by nlinarith [ht.1,ht.2.2.1,κ_bounds.1] : 0≤Real.sin lowerAngle/2+κ*Real.cos lowerAngle)
    (by norm_num : (0:ℝ)≤197/200)
  dsimp [firstD]
  nlinarith

lemma first_lower {g φ : ℝ} (hg : g∈Icc (7/10) (197/200)) (hφ : Lower φ) :
    87079/100000+(61/500)*g<first g φ := by
  have hmono : MonotoneOn (first g) (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (first_hasDerivAt g x).continuousAt.continuousWithinAt)
      (fun x _ => first_hasDerivAt g x)
      (fun x hx => ((firstD_left hg).trans_le
        (firstD_monotone (by linarith [hg.1]) left_mem (Ioo_subset_Icc_self hx) hx.1.le)).le)
  have ht := left_trig
  have hm := mul_le_mul κ_bounds.2.le ht.2.1.le
    (by linarith [ht.1] : 0≤Real.sin lowerAngle) (by norm_num : (0:ℝ)≤183/200)
  have hbase : (61/500:ℝ)<1/2+Real.cos lowerAngle/2-κ*Real.sin lowerAngle := by
    nlinarith [ht.2.2.1]
  have hp := mul_lt_mul_of_pos_left hbase (by linarith [hg.1] : 0<g)
  have ha : (87079/100000:ℝ)<lowerAngle := by dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hleft : 87079/100000+(61/500)*g<first g lowerAngle := by
    dsimp [first]
    nlinarith
  exact hleft.trans_le (hmono left_mem hφ hφ.1)

lemma second_hasDerivAt (g : ℝ) {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt (second g) (secondD g φ) φ := by
  have hs : Real.sin φ≠0 := ne_of_gt (by linarith [(lower_trig hφ).1])
  have hh := ((Real.hasDerivAt_cos φ).sub_const κ).div (Real.hasDerivAt_sin φ) hs
  have hn : -Real.sin φ*Real.sin φ-(Real.cos φ-κ)*Real.cos φ=κ*Real.cos φ-1 := by
    linear_combination (-1:ℝ)*Real.sin_sq_add_cos_sq φ
  rw [hn] at hh
  convert ((hasDerivAt_id φ).add_const (g/2)).add (hh.const_mul g) using 1
  · funext x
    simp only [second,id,Pi.add_apply,Pi.div_apply]
    ring
  · dsimp only [secondD]
    try ring

lemma secondD_positive {g φ : ℝ} (hg : g∈Icc (7/10) (197/200)) (hφ : Lower φ) :
    0<secondD g φ := by
  have ht := lower_trig hφ
  have hs : 0<Real.sin φ := by linarith [ht.1]
  have hgκ := mul_le_mul hg.1 κ_bounds.1.le (by norm_num : (0:ℝ)≤457/500)
    (by linarith [hg.1] : 0≤g)
  have hh : 0≤g*κ-Real.cos φ+3/500 := by nlinarith [ht.2.2.2.1]
  have hp := mul_nonneg hh ht.2.2.1
  have hnum : 0<(Real.sin φ)^2+g*(κ*Real.cos φ-1) := by
    nlinarith [Real.sin_sq_add_cos_sq φ,hg.2,Real.cos_le_one φ]
  have he : secondD g φ*(Real.sin φ)^2=(Real.sin φ)^2+g*(κ*Real.cos φ-1) := by
    dsimp [secondD]
    field_simp [hs.ne']
  by_contra hn
  have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (sq_nonneg (Real.sin φ))
  rw [he] at hp
  linarith

lemma second_lower {g φ : ℝ} (hg : g∈Icc (7/10) (197/200)) (hφ : Lower φ) :
    87079/100000+(29/200)*g<second g φ := by
  have hmono : MonotoneOn (second g) (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (second_hasDerivAt g hx).continuousAt.continuousWithinAt)
      (fun x hx => second_hasDerivAt g (Ioo_subset_Icc_self hx))
      (fun x hx => (secondD_positive hg (Ioo_subset_Icc_self hx)).le)
  have ht := left_trig
  have hs : 0<Real.sin lowerAngle := by linarith [ht.1]
  have hbase : (29/200:ℝ)<1/2+(Real.cos lowerAngle-κ)/Real.sin lowerAngle := by
    have he := div_mul_cancel₀ (Real.cos lowerAngle-κ) hs.ne'
    by_contra hn
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hs.le
    nlinarith [ht.1,ht.2.2.1,κ_bounds.2]
  have hp := mul_lt_mul_of_pos_left hbase (by linarith [hg.1] : 0<g)
  have ha : (87079/100000:ℝ)<lowerAngle := by dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hleft : 87079/100000+(29/200)*g<second g lowerAngle := by
    have he : second g lowerAngle=lowerAngle+g*(1/2+(Real.cos lowerAngle-κ)/Real.sin lowerAngle) := by
      dsimp only [second]
      ring
    rw [he]
    linarith
  exact hleft.trans_le (hmono left_mem hφ hφ.1)

lemma cotangent_linear {φ : ℝ} (hφ : Lower φ) :
    (Real.pi/2-φ)*Real.sin φ≤Real.cos φ := by
  have hx := lower_deviation hφ
  have hd (x : ℝ) : HasDerivAt (fun y => Real.sin y-y*Real.cos y) (x*Real.sin x) x :=
    ((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).congr_deriv
      (by simp only [id]; ring)
  have hm : MonotoneOn (fun y => Real.sin y-y*Real.cos y) (Icc (0:ℝ) (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => hd x)
      (fun x hx => mul_nonneg hx.1.le (positive_trig (Ioo_subset_Icc_self hx)).2.2.1)
  have hh := hm (by norm_num) hx hx.1
  simp only [Real.sin_zero,Real.cos_zero,zero_mul,sub_zero,Real.sin_sub,Real.cos_sub,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedAffine
