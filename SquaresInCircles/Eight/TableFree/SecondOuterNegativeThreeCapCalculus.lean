module

public import SquaresInCircles.Eight.TableFree.SecondOuterKReference
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeData
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoCapReferences

/-!
# Whole-curve derivatives at the physical endpoint angle

The existing physical target-secondary contact supplies the height,
its source speed and all derivatives at angle `.7`.  Replacing only
the literal edge labels gives the actual negative edge-three cost.
Its third derivative is less than `-.3` on the full feasible arc;
one fixed reference can therefore control its initial minimum.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD ratioDD)
open NegativeTwo.CapCurve (height k k1 k2 Domain target_mem before source_upper)

def cost (b : ℝ) : ℝ := value b (height b) (Real.pi/2-7/10)
def first (b : ℝ) : ℝ := -TLabel.d1 b+KLabel.d1 (height b)*k b
def second (b : ℝ) : ℝ :=
  -TLabel.d2 b+KLabel.d2 (height b)*(k b)^2+KLabel.d1 (height b)*k1 b
def third (b : ℝ) : ℝ :=
  -TLabel.d3 b+KLabel.d3 (height b)*(k b)^3+
    3*KLabel.d2 (height b)*k b*k1 b+KLabel.d1 (height b)*k2 b

lemma cost_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt cost (first b) b := by
  have hh := ((TLabel.outer_hasDerivAt (outer_domain hb.1)).neg).add
    ((KLabel.outer_hasDerivAt (outer_domain (target_mem hb))).comp b
      (NegativeTwo.CapCurve.height_hasDerivAt hb.1))
  have hfun : cost=fun x => (Real.pi/2-7/10)+(-TLabel.outer x+KLabel.outer (height x)) := by
    funext x
    simp only [cost,value,T,K]
    ring
  rw [hfun]
  exact hh.const_add (Real.pi/2-7/10)

lemma first_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt first (second b) b := by
  have hh := ((TLabel.d1_hasDerivAt (outer_domain hb.1)).neg).add
    (((KLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b
      (NegativeTwo.CapCurve.height_hasDerivAt hb.1)).mul
        (NegativeTwo.CapCurve.k_hasDerivAt hb.1))
  exact hh.congr_deriv (by simp only [second,Function.comp_apply]; ring)

lemma second_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt second (third b) b := by
  have ht := NegativeTwo.CapCurve.height_hasDerivAt hb.1
  have hk := NegativeTwo.CapCurve.k_hasDerivAt hb.1
  have hk2 : HasDerivAt (fun x => (k x)^2) (2*k b*k1 b) b :=
    (hk.pow 2).congr_deriv (by norm_num)
  have hh := (((TLabel.d2_hasDerivAt (outer_domain hb.1)).neg).add
    (((KLabel.d2_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul hk2)).add
      (((KLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
        (NegativeTwo.CapCurve.k1_hasDerivAt hb.1))
  exact hh.congr_deriv (by simp only [third,Function.comp_apply]; ring)

lemma source_radical_lower {b : ℝ} (hb : Domain b) : (61/40:ℝ)<U b := by
  have hu := U_positive (outer_domain hb.1)
  have hc := UW_circle (outer_domain hb.1)
  have hw : 0≤W b ∧ W b<(63/50:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hb.1.1,source_upper hb]
  have hw2 : (W b)^2<(63/50:ℝ)^2 := by nlinarith
  norm_num [Q0] at hc
  nlinarith

lemma last_term_upper {b : ℝ} (hb : Domain b) :
    KLabel.d1 (height b)*k2 b<(13/10:ℝ) := by
  have hu := U_positive (outer_domain hb.1)
  have hu0 : U b≠0 := hu.ne'
  have hU := source_radical_lower hb
  have hU5 := pow_lt_pow_left₀ hU (by norm_num : (0:ℝ)≤61/40) (by norm_num : (5:ℕ)≠0)
  have hK := K_first_bounds (target_mem hb)
  have hc := NegativeTwo.CapCurve.trig
  have hc0 : 0<NegativeTwo.CapCurve.c := by linarith [hc.1]
  have hcU : NegativeTwo.CapCurve.c<(153/200:ℝ) := by linarith [hc.2.1]
  have hw : 0<W b ∧ W b<(63/50:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hb.1.1,source_upper hb]
  have hp1 : KLabel.d1 (height b)*NegativeTwo.CapCurve.c<(116/125)*(153/200) :=
    mul_lt_mul hK.2 hcU.le hc0 (by norm_num)
  have hq : (0:ℝ)<3*Q0 := by norm_num [Q0]
  have hp2 := mul_lt_mul_of_pos_right hp1 hq
  have hp3 := mul_lt_mul hp2 hw.2.le hw.1 (by positivity)
  have he : KLabel.d1 (height b)*k2 b*(U b)^5=
      KLabel.d1 (height b)*NegativeTwo.CapCurve.c*(3*Q0)*W b := by
    rw [show k2 b=NegativeTwo.CapCurve.c*(3*Q0*W b/(U b)^5) from rfl]
    field_simp
  by_contra hh
  have hp := mul_le_mul_of_nonneg_right (not_lt.mp hh) (pow_nonneg hu.le 5)
  have hQ0 : Q0=9789/2500 := rfl
  norm_num at hU5
  linarith

theorem third_upper {b : ℝ} (hb : Domain b) : third b<(-3/10:ℝ) := by
  have hk := NegativeTwo.CapCurve.k_bounds hb.1
  have hk0 : 0<k b := by linarith [hk.1]
  have hneg1 := mul_neg_of_neg_of_pos (K_third_negative (target_mem hb)) (pow_pos hk0 3)
  have hneg2 := mul_neg_of_neg_of_pos
    (show KLabel.d2 (height b)<0 by linarith [K_second_upper (target_mem hb)])
    (mul_pos hk0 hk.2.1)
  dsimp [third]
  nlinarith [T_third_lower hb.1,last_term_upper hb]

lemma second_antitone {b : ℝ} (hb : Domain b) : AntitoneOn second (Icc 0 b) :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (second_hasDerivAt (before hb ht)).continuousAt.continuousWithinAt)
    (fun t ht => second_hasDerivAt (before hb (Ioo_subset_Icc_self ht)))
    (fun t ht => by linarith [third_upper (before hb (Ioo_subset_Icc_self ht))])

lemma first_concave {b : ℝ} (hb : Domain b) : ConcaveOn ℝ (Icc 0 b) first :=
  concave_of_deriv2
    (fun t ht => first_hasDerivAt (before hb ht))
    (fun t ht => second_hasDerivAt (before hb ht))
    (fun t ht => by linarith [third_upper (before hb ht)])

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Cap
