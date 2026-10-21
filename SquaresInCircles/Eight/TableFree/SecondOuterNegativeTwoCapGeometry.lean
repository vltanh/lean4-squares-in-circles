module

public import SquaresInCircles.Eight.TableFree.SecondOuterFourthKernel
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactCap
public import SquaresInCircles.Eight.TableFree.SecondOuterFixedReference
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoData

/-!
# The physical contact at the endpoint angle

The original target-secondary contact at angle `π/2-.7` has an
increasing target coordinate.  Its feasible source interval ends before
`.76`, and the target coordinate strictly exceeds the source coordinate.
The four derivatives below are derivatives of this actual contact cost.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def c : ℝ := Real.cos (7/10)
def s : ℝ := Real.sin (7/10)
def height (b : ℝ) : ℝ := TargetContact.B b (7/10)
def k (b : ℝ) : ℝ := c*ratio b+s
def k1 (b : ℝ) : ℝ := c*ratioD b
def k2 (b : ℝ) : ℝ := c*ratioDD b
def k3 (b : ℝ) : ℝ := c*ratioDDD b
def cost (b : ℝ) : ℝ := value b (height b) (Real.pi/2-7/10)
def first (b : ℝ) : ℝ := -PLabel.d1 b+TLabel.d1 (height b)*k b
def second (b : ℝ) : ℝ :=
  -PLabel.d2 b+TLabel.d2 (height b)*(k b)^2+TLabel.d1 (height b)*k1 b
def third (b : ℝ) : ℝ :=
  -PLabel.d3 b+TLabel.d3 (height b)*(k b)^3+
    3*TLabel.d2 (height b)*k b*k1 b+TLabel.d1 (height b)*k2 b
def fourth (b : ℝ) : ℝ :=
  -PLabel.d4 b+TLabel.d4 (height b)*(k b)^4+
    6*TLabel.d3 (height b)*(k b)^2*k1 b+
      TLabel.d2 (height b)*(3*(k1 b)^2+4*k b*k2 b)+
        TLabel.d1 (height b)*k3 b
def Domain (b : ℝ) : Prop := b∈Icc 0 outerDiagonal ∧ height b≤outerDiagonal

lemma trig : (76484/100000:ℝ)<c ∧ c<764844/1000000 ∧
    (6442/10000:ℝ)<s ∧ s<64424/100000 := by
  have hh := CommonQuarter.cap_trig
  dsimp [c,s]
  exact ⟨by linarith [hh.2.2.1],by linarith [hh.2.2.2],
    by linarith [hh.1],by linarith [hh.2.1]⟩

lemma height_monotone : MonotoneOn height (Icc 0 outerDiagonal) :=
  TargetContact.B_source_monotone (by norm_num)

lemma height_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (61/500:ℝ)<height b := by
  have hm := height_monotone outer_zero_mem hb hb.1
  have hz := TargetContact.Cap.zero_target.1
  dsimp [height] at hm ⊢
  linarith

lemma target_mem {b : ℝ} (hb : Domain b) : height b∈Icc 0 outerDiagonal :=
  ⟨by linarith [height_positive hb.1],hb.2⟩

lemma before {b t : ℝ} (hb : Domain b) (ht : t∈Icc 0 b) : Domain t := by
  have htm : t∈Icc 0 outerDiagonal := ⟨ht.1,ht.2.trans hb.1.2⟩
  exact ⟨htm,(height_monotone htm hb.1 ht.2).trans hb.2⟩

lemma source_upper {b : ℝ} (hb : Domain b) : b<(19/25:ℝ) := by
  by_contra hh
  have hl : (19/25:ℝ)≤b := le_of_not_gt hh
  have hu := U_positive (outer_domain hb.1)
  have hc := UW_circle (outer_domain hb.1)
  have hU : U b<(763/500:ℝ) := by
    have hw : (63/50:ℝ)≤W b := by dsimp [W]; linarith
    have hw2 : (63/50:ℝ)^2≤(W b)^2 := by nlinarith
    norm_num [Q0] at hc
    nlinarith
  have hum : 0≤U b-1 := by linarith [(UW_bounds hb.1).1]
  have hcprod := mul_le_mul hU.le trig.2.1.le
    (by linarith [trig.1] : 0≤c) (by norm_num : (0:ℝ)≤763/500)
  have hcprod' := mul_le_mul (show U b-1≤263/500 by linarith) trig.2.1.le
    (by linarith [trig.1] : 0≤c) (by norm_num : (0:ℝ)≤263/500)
  have hsprod := mul_le_mul (show (63/50:ℝ)≤W b by dsimp [W]; linarith)
    trig.2.2.1.le (by norm_num : (0:ℝ)≤6442/10000)
    (by linarith [(UW_bounds hb.1).2.2.1] : 0≤W b)
  have he : height b=1/2-(U b-1)*c+W b*s := by
    dsimp [height,TargetContact.B,U,W,c,s]
    ring
  have hd := outer_endpoint_bounds.2.2.2
  nlinarith [hb.2]

lemma target_above_source {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : b<height b := by
  have hc := UW_circle (outer_domain hb)
  have htr : s^2+c^2=1 := Real.sin_sq_add_cos_sq (7/10)
  have hq : 0<Q0 := by norm_num [Q0]
  have he : (c*U b+(1-s)*W b)^2+(c*W b-(1-s)*U b)^2=
      Q0*(c^2+(1-s)^2) := by
    linear_combination (c^2+(1-s)^2)*hc
  have hgap : Q0*(c^2+(1-s)^2)<(1+c)^2 := by
    norm_num [Q0] at *
    nlinarith [trig.1,trig.2.1,trig.2.2.1,trig.2.2.2]
  have hproj : c*U b+(1-s)*W b<1+c := by
    have hcpos : 0<1+c := by linarith [trig.1]
    nlinarith [sq_nonneg (c*W b-(1-s)*U b)]
  have hheight : height b-b=1+c-(c*U b+(1-s)*W b) := by
    dsimp [height,TargetContact.B,U,W,c,s]
    ring
  linarith

lemma height_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt height (k b) b := by
  convert TargetContact.B_source_hasDerivAt hb (7/10) using 1 <;>
    dsimp [height,k,TargetContact.k,c,s] <;> ring

lemma k_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt k (k1 b) b := by
  convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    c).add_const s using 1

lemma k1_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt k1 (k2 b) b :=
  (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_mul c

lemma k2_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt k2 (k3 b) b := (ratioDD_hasDerivAt (outer_domain hb)).const_mul c

lemma k_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (21/25:ℝ)<k b ∧ 0<k1 b ∧ 0<k2 b ∧ 0<k3 b := by
  have hr := outer_ratio_bounds hb
  have hprod := mul_lt_mul trig.1 hr.1 (by norm_num : (0:ℝ)<261/1000)
    (by linarith [trig.1] : 0≤c)
  have hu := U_positive (outer_domain hb)
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hq : 0<Q0 := by norm_num [Q0]
  have hc : 0<c := by linarith [trig.1]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [k]
    nlinarith [trig.2.2.1]
  · exact mul_pos hc hr.2.2.1
  · dsimp [k2,ratioDD,U] at *
    positivity
  · dsimp [k3,ratioDDD]
    positivity

lemma cost_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt cost (first b) b := by
  have hd := ((PLabel.outer_hasDerivAt (outer_domain hb.1)).neg).add
    ((TLabel.outer_hasDerivAt (outer_domain (target_mem hb))).comp b
      (height_hasDerivAt hb.1))
  convert hd.const_add (Real.pi/2-7/10) using 1 <;>
    dsimp [cost,value,first,P,T] <;> ring

lemma first_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt first (second b) b := by
  have hd := ((PLabel.d1_hasDerivAt (outer_domain hb.1)).neg).add
    (((TLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b
      (height_hasDerivAt hb.1)).mul (k_hasDerivAt hb.1))
  convert hd using 1 <;> dsimp [first,second] <;> ring

lemma second_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt second (third b) b := by
  have ht := height_hasDerivAt hb.1
  have hk := k_hasDerivAt hb.1
  have hd := (((PLabel.d2_hasDerivAt (outer_domain hb.1)).neg).add
    (((TLabel.d2_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
      (hk.pow 2))).add
        (((TLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
          (k1_hasDerivAt hb.1))
  convert hd using 1 <;> dsimp [second,third] <;> ring

lemma third_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt third (fourth b) b := by
  have ht := height_hasDerivAt hb.1
  have hk := k_hasDerivAt hb.1
  have hd := ((((PLabel.d3_hasDerivAt (outer_domain hb.1)).neg).add
    (((TLabel.d3_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
      (hk.pow 3))).add
        (((((TLabel.d2_hasDerivAt (outer_domain (target_mem hb))).comp b ht).const_mul
          3).mul hk).mul (k1_hasDerivAt hb.1))).add
            (((TLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
              (k2_hasDerivAt hb.1))
  convert hd using 1 <;> dsimp [third,fourth] <;> ring

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve
