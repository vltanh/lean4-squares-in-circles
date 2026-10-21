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
  convert hh.const_add (Real.pi/2-7/10) using 1 <;>
    dsimp [cost,value,first,T,K] <;> ring

lemma first_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt first (second b) b := by
  have hh := ((TLabel.d1_hasDerivAt (outer_domain hb.1)).neg).add
    (((KLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b
      (NegativeTwo.CapCurve.height_hasDerivAt hb.1)).mul
        (NegativeTwo.CapCurve.k_hasDerivAt hb.1))
  convert hh using 1 <;> dsimp [first,second] <;> ring

lemma second_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt second (third b) b := by
  have hh := (((TLabel.d2_hasDerivAt (outer_domain hb.1)).neg).add
    (((KLabel.d2_hasDerivAt (outer_domain (target_mem hb))).comp b
      (NegativeTwo.CapCurve.height_hasDerivAt hb.1)).mul
        ((NegativeTwo.CapCurve.k_hasDerivAt hb.1).pow 2))).add
    (((KLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b
      (NegativeTwo.CapCurve.height_hasDerivAt hb.1)).mul
        (NegativeTwo.CapCurve.k1_hasDerivAt hb.1))
  convert hh using 1 <;> dsimp [second,third] <;> ring

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
  have hU := source_radical_lower hb
  have hU5 := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤61/40) hU
    (by norm_num : (5:ℕ)≠0)
  have hK := K_first_bounds (target_mem hb)
  have hc := NegativeTwo.CapCurve.trig
  have hc0 : 0<NegativeTwo.CapCurve.c := by linarith [hc.1]
  have hcU : NegativeTwo.CapCurve.c<(153/200:ℝ) := by linarith [hc.2.1]
  have hw : 0<W b ∧ W b<(63/50:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hb.1.1,source_upper hb]
  have hp1 := mul_lt_mul hK.2 hcU hc0 (by norm_num : (0:ℝ)≤116/125)
  have hp2 := mul_lt_mul_of_pos_right hp1 (show 0<3*Q0 by norm_num [Q0])
  have hp3 := mul_lt_mul hp2 hw.2 hw.1
    (by norm_num [Q0] : (0:ℝ)≤(116/125)*(153/200)*(3*Q0))
  have he : KLabel.d1 (height b)*k2 b*(U b)^5=
      KLabel.d1 (height b)*NegativeTwo.CapCurve.c*(3*Q0)*W b := by
    dsimp [k2,ratioDD,U,W]
    field_simp [show ShortOuterOne.SameContact.arc b+1/2≠0 from hu.ne']
    ring
  by_contra hh
  have hp := mul_nonneg (show 0≤KLabel.d1 (height b)*k2 b-13/10 by linarith)
    (pow_nonneg hu.le 5)
  norm_num [Q0] at hp3 hU5
  nlinarith

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
