module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.FourthKernel
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoContactCap
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners

/-!
# Eight squares: the whole zero-target contact bound

A single strong-concavity reference bounds `T(b)-.72*b` on the first
half of the physical arc.  Convexity of the label derivative and its
actual endpoint values show that the same expression decreases on the
rest.  The affine angle bound then proves a reserve above `.9` for
every original zero-target contact.
-/

section
/-!
## The physical contact at the endpoint angle

The original target-secondary contact at angle `π/2-.7` has an
increasing target coordinate.  Its feasible source interval ends before
`.76`, and the target coordinate strictly exceeds the source coordinate.
The four derivatives below are derivatives of this actual contact cost.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve

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
  have h := TargetContact.B_source_hasDerivAt hb (7/10)
  exact h.congr_deriv (by simp only [TargetContact.k,k,c,s]; ring)

lemma k_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt k (k1 b) b := by
  exact ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    c).add_const s

lemma k1_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt k1 (k2 b) b :=
  (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_mul c

lemma k2_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt k2 (k3 b) b := (ratioDD_hasDerivAt (outer_domain hb)).const_mul c

lemma k_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (21/25:ℝ)<k b ∧ 0<k1 b ∧ 0<k2 b ∧ 0<k3 b := by
  have hr := outer_ratio_bounds hb
  have hprod := mul_lt_mul trig.1 hr.1.le (by norm_num : (0:ℝ)<261/1000)
    (by linarith [trig.1] : 0≤c)
  have hu := U_positive (outer_domain hb)
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hq : 0<Q0 := by norm_num [Q0]
  have hc : 0<c := by linarith [trig.1]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only [k]
    nlinarith [trig.2.2.1]
  · exact mul_pos hc hr.2.2.1
  · show 0<c*(3*Q0*(b+1/2)/(arc b+1/2)^5)
    exact mul_pos hc (div_pos (mul_pos (mul_pos (by norm_num) hq) hw) (pow_pos hu 5))
  · show 0<c*(3*Q0*((U b)^2+5*(W b)^2)/(U b)^7)
    exact mul_pos hc (div_pos (mul_pos (mul_pos (by norm_num) hq)
      (add_pos_of_pos_of_nonneg (pow_pos hu 2) (by positivity))) (pow_pos hu 7))

lemma cost_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt cost (first b) b := by
  have hd := ((PLabel.outer_hasDerivAt (outer_domain hb.1)).neg).add
    ((TLabel.outer_hasDerivAt (outer_domain (target_mem hb))).comp b
      (height_hasDerivAt hb.1))
  have hfun : cost=fun x => (Real.pi/2-7/10)+(-PLabel.outer x+TLabel.outer (height x)) := by
    funext x
    simp only [cost,value,P,T]
    ring
  rw [hfun]
  exact hd.const_add (Real.pi/2-7/10)

lemma first_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt first (second b) b := by
  have hd := ((PLabel.d1_hasDerivAt (outer_domain hb.1)).neg).add
    (((TLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b
      (height_hasDerivAt hb.1)).mul (k_hasDerivAt hb.1))
  exact hd.congr_deriv (by simp only [second,Function.comp_apply]; ring)

lemma second_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt second (third b) b := by
  have ht := height_hasDerivAt hb.1
  have hk := k_hasDerivAt hb.1
  have hk2 : HasDerivAt (fun x => (k x)^2) (2*k b*k1 b) b :=
    (hk.pow 2).congr_deriv (by norm_num)
  have hd := (((PLabel.d2_hasDerivAt (outer_domain hb.1)).neg).add
    (((TLabel.d2_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul hk2)).add
        (((TLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
          (k1_hasDerivAt hb.1))
  exact hd.congr_deriv (by simp only [third,Function.comp_apply]; ring)

lemma third_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt third (fourth b) b := by
  have ht := height_hasDerivAt hb.1
  have hk := k_hasDerivAt hb.1
  have hk3 : HasDerivAt (fun x => (k x)^3) (3*(k b)^2*k1 b) b :=
    (hk.pow 3).congr_deriv (by norm_num)
  have hd := ((((PLabel.d3_hasDerivAt (outer_domain hb.1)).neg).add
    (((TLabel.d3_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul hk3)).add
        (((((TLabel.d2_hasDerivAt (outer_domain (target_mem hb))).comp b ht).const_mul
          3).mul hk).mul (k1_hasDerivAt hb.1))).add
            (((TLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
              (k2_hasDerivAt hb.1))
  exact hd.congr_deriv (by simp only [fourth,Function.comp_apply,Pi.mul_apply]; ring)

end SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve
end
end
end

section
/-!
## Physical enclosures at the four endpoint-contact references

The angle is fixed at `.7`.  Adjacent Taylor polynomials enclose its
sine and cosine once; each source radical and target radical is then
enclosed by rational squaring at the prescribed physical reference.
These are fixed references for a whole-curve calculus proof.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open ShortOuterOne.SameContact (ratio ratioD ratioDD)

def sLo : ℝ := 64421768723613/100000000000000
def sHi : ℝ := 64421768773151/100000000000000
def cLo : ℝ := 76484218725566/100000000000000
def cHi : ℝ := 76484218728457/100000000000000

lemma fine_trig : s∈Icc sLo sHi ∧ c∈Icc cLo cHi := by
  have hs := sin11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hS := sin_le_sin9 (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤7/10 by norm_num)
  have hC := cos_le_cos12 (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hS hc hC
  dsimp [s,c,sLo,sHi,cLo,cHi]
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma reference_cage {b ul uh : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hU : U b∈Icc ul uh) (hul : 1<ul) :
    1/2-(uh-1)*cHi+(b+1/2)*sLo≤height b ∧
      height b≤1/2-(ul-1)*cLo+(b+1/2)*sHi ∧
      cLo*((b+1/2)/uh)+sLo≤k b ∧ k b≤cHi*((b+1/2)/ul)+sHi ∧
      cLo*(Q0/uh^3)≤k1 b ∧ k1 b≤cHi*(Q0/ul^3) ∧
      3*cLo*Q0*(b+1/2)/uh^5≤k2 b ∧
        k2 b≤3*cHi*Q0*(b+1/2)/ul^5 := by
  have ht := fine_trig
  have hu := U_positive (outer_domain hb)
  have hul0 : 0<ul := by linarith
  have hb0 : 0≤b+1/2 := by linarith [hb.1]
  have hc0 : 0≤c := by linarith [trig.1]
  have hq : 0≤Q0 := by norm_num [Q0]
  have hr := FixedReference.ratios hb ⟨le_rfl,le_rfl⟩ hU hb.1 (by linarith)
  have hU0 : 0≤U b-1 := by linarith [hU.1]
  have hUH : 0≤uh-1 := hU0.trans (by linarith [hU.2])
  have hlo := mul_le_mul (show ul-1≤U b-1 by linarith [hU.1]) ht.2.1
    (by norm_num [cLo]) hU0
  have hhi := mul_le_mul (show U b-1≤uh-1 by linarith [hU.2]) ht.2.2 hc0 hUH
  have hslo := mul_le_mul_of_nonneg_left ht.1.1 hb0
  have hshi := mul_le_mul_of_nonneg_left ht.1.2 hb0
  have hrlo := mul_le_mul ht.2.1 hr.1 (div_nonneg hb0 (hul0.le.trans (hU.1.trans hU.2))) hc0
  have hrhi := mul_le_mul ht.2.2 hr.2.1 (by linarith [(outer_ratio_bounds hb).1])
    (by norm_num [cHi])
  have hDlo := mul_le_mul ht.2.1 hr.2.2.1
    (div_nonneg hq (pow_nonneg (hul0.le.trans (hU.1.trans hU.2)) 3)) hc0
  have hDhi := mul_le_mul ht.2.2 hr.2.2.2 (outer_ratio_bounds hb).2.2.1.le
    (by norm_num [cHi])
  have hUlo5 := pow_le_pow_left₀ hul0.le hU.1 5
  have hUhi5 := pow_le_pow_left₀ hu.le hU.2 5
  have hnum : 0≤3*Q0*(b+1/2) := mul_nonneg (mul_nonneg (by norm_num) hq) hb0
  have hDDlo : 3*Q0*(b+1/2)/uh^5≤ratioDD b := by
    change 3*Q0*(b+1/2)/uh^5≤3*Q0*(b+1/2)/(U b)^5
    exact div_le_div_of_nonneg_left hnum (pow_pos hu 5) hUhi5
  have hDDhi : ratioDD b≤3*Q0*(b+1/2)/ul^5 := by
    change 3*Q0*(b+1/2)/(U b)^5≤3*Q0*(b+1/2)/ul^5
    exact div_le_div_of_nonneg_left hnum (pow_pos hul0 5) hUlo5
  have hDDpos : 0≤ratioDD b := by
    change 0≤3*Q0*(b+1/2)/(U b)^5
    exact div_nonneg hnum (pow_pos hu 5).le
  have hDDlow := mul_le_mul ht.2.1 hDDlo
    (div_nonneg hnum (pow_nonneg (hul0.le.trans (hU.1.trans hU.2)) 5)) hc0
  have hDDhigh := mul_le_mul ht.2.2 hDDhi hDDpos (by norm_num [cHi])
  have hlow5 : 3*cLo*Q0*(b+1/2)/uh^5=cLo*(3*Q0*(b+1/2)/uh^5) := by ring
  have hhigh5 : 3*cHi*Q0*(b+1/2)/ul^5=cHi*(3*Q0*(b+1/2)/ul^5) := by ring
  have he : height b=1/2-(U b-1)*c+(b+1/2)*s := by
    dsimp [height,TargetContact.B,U,c,s]
    ring
  rw [he]
  dsimp only [k,k1,k2]
  refine ⟨by linarith,by linarith,by linarith [ht.1.1],by linarith [ht.1.2],
    hDlo,hDhi,by linarith,by linarith⟩

lemma two_mem : (1/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)
lemma six_mem : (3/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)
lemma reference_mem : (14473/20000:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma zero_radical :
    U 0∈Icc (191457567100389/100000000000000) (191457567100390/100000000000000) :=
  ⟨TargetContact.Cap.zero_source_fine.1.le,TargetContact.Cap.zero_source_fine.2.le⟩

lemma two_radical :
    U (1/5)∈Icc (185083764820148/100000000000000) (185083764820149/100000000000000) := by
  have hh := shifted_chart_reference (outer_domain two_mem)
    (l := (185083764820148/100000000000000:ℝ))
    (u := (185083764820149/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma six_radical :
    U (3/5)∈Icc (164487081559616/100000000000000) (164487081559617/100000000000000) := by
  have hh := shifted_chart_reference (outer_domain six_mem)
    (l := (164487081559616/100000000000000:ℝ))
    (u := (164487081559617/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma reference_radical :
    U (14473/20000)∈Icc (155508220924168/100000000000000) (155508220924169/100000000000000) := by
  have hh := shifted_chart_reference (outer_domain reference_mem)
    (l := (155508220924168/100000000000000:ℝ))
    (u := (155508220924169/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma zero_cage :
    height 0∈Icc (1226027868/10000000000) (1226027874/10000000000) ∧
      (8439/10000:ℝ)<k 0 ∧ k1 0<(1067/2500:ℝ) := by
  have hh := reference_cage outer_zero_mem zero_radical (by norm_num)
  norm_num [sLo,sHi,cLo,cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩

lemma two_cage :
    height (1/5)∈Icc (3001958530/10000000000) (3001958537/10000000000) ∧
      (4667/5000:ℝ)<k (1/5) ∧ k (1/5)<1867/2000 ∧
      k1 (1/5)<1181/2500 ∧ (579/2000:ℝ)<k2 (1/5) := by
  have hh := reference_cage two_mem two_radical (by norm_num)
  norm_num [sLo,sHi,cLo,cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith,by linarith,by linarith⟩

lemma six_cage :
    height (3/5)∈Icc (7154150507/10000000000) (7154150516/10000000000) ∧
      (577851/500000:ℝ)<k (3/5) ∧ k (3/5)<115571/100000 ∧
      (672937/1000000:ℝ)<k1 (3/5) := by
  have hh := reference_cage six_mem six_radical (by norm_num)
  norm_num [sLo,sHi,cLo,cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith,by linarith⟩

lemma reference_cage_fine :
    height (14473/20000)∈Icc (86374668194/100000000000) (86374668258/100000000000) ∧
      k (14473/20000)∈Icc (124605027/100000000) (31151257/25000000) := by
  have hh := reference_cage reference_mem reference_radical (by norm_num)
  norm_num [sLo,sHi,cLo,cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma zero_domain : Domain 0 :=
  ⟨outer_zero_mem,by linarith [zero_cage.1.2,fine_outer_endpoint_bounds.2]⟩
lemma two_domain : Domain (1/5) :=
  ⟨two_mem,by linarith [two_cage.1.2,fine_outer_endpoint_bounds.2]⟩
lemma six_domain : Domain (3/5) :=
  ⟨six_mem,by linarith [six_cage.1.2,fine_outer_endpoint_bounds.2]⟩
lemma reference_domain : Domain (14473/20000) :=
  ⟨reference_mem,by linarith [reference_cage_fine.1.2,fine_outer_endpoint_bounds.2]⟩

lemma zero_target_radical :
    U (height 0)∈Icc (18782879888/10000000000) (18782879892/10000000000) := by
  have hc := UW_circle (outer_domain (target_mem zero_domain))
  have hp := U_positive (outer_domain (target_mem zero_domain))
  norm_num [W,Q0] at hc
  constructor <;> nlinarith [zero_cage.1.1,zero_cage.1.2]

lemma two_target_radical :
    U (height (1/5))∈Icc (18097752886/10000000000) (18097752891/10000000000) := by
  have hc := UW_circle (outer_domain (target_mem two_domain))
  have hp := U_positive (outer_domain (target_mem two_domain))
  norm_num [W,Q0] at hc
  constructor <;> nlinarith [two_cage.1.1,two_cage.1.2]

lemma six_target_radical :
    U (height (3/5))∈Icc (15615268977/10000000000) (15615268985/10000000000) := by
  have hc := UW_circle (outer_domain (target_mem six_domain))
  have hp := U_positive (outer_domain (target_mem six_domain))
  norm_num [W,Q0] at hc
  constructor <;> nlinarith [six_cage.1.1,six_cage.1.2]

lemma reference_target_radical :
    U (height (14473/20000))∈Icc (143380437499/100000000000) (143380437561/100000000000) := by
  have hc := UW_circle (outer_domain (target_mem reference_domain))
  have hp := U_positive (outer_domain (target_mem reference_domain))
  norm_num [W,Q0] at hc
  constructor <;> nlinarith [reference_cage_fine.1.1,reference_cage_fine.1.2]

end SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve
end
end
end

section
/-!
## The two named references and the true endpoint of the angle-cap arc

All cages are obtained from the original circle and the already proved
Taylor bounds at `.7`.  The two interior references are `.4` and
`.275034`; the final rational point lies strictly beyond the actual
diagonal-target endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.CapCurve (height k k1 Domain target_mem)

def reference : ℝ := 137517/500000
def endpointUpper : ℝ := 375927951/500000000

lemma four_mem : (2/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)
lemma reference_mem : reference∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [reference])
lemma endpointUpper_mem : endpointUpper∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [endpointUpper])

lemma four_radical :
    U (2/5)∈Icc (35245425235057/20000000000000) (88113563087643/50000000000000) := by
  have hh := shifted_chart_reference (outer_domain four_mem)
    (l := (35245425235057/20000000000000:ℝ))
    (u := (88113563087643/50000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma reference_radical :
    U reference∈Icc (36413856147593/20000000000000) (91034640368983/50000000000000) := by
  have hh := shifted_chart_reference (outer_domain reference_mem)
    (l := (36413856147593/20000000000000:ℝ))
    (u := (91034640368983/50000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma endpointUpper_radical :
    U endpointUpper∈Icc (76623377643963/50000000000000) (153246755287927/100000000000000) := by
  have hh := shifted_chart_reference (outer_domain endpointUpper_mem)
    (l := (76623377643963/50000000000000:ℝ))
    (u := (153246755287927/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [endpointUpper,W,Q0])
    (by norm_num [endpointUpper,W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma four_cage :
    height (2/5)∈Icc (4967786993/10000000000) (4967786999/10000000000) ∧
      (2587/2500:ℝ)<k (2/5) ∧ k (2/5)<207/200 ∧ (342/625:ℝ)<k1 (2/5) := by
  have hh := NegativeTwo.CapCurve.reference_cage four_mem four_radical (by norm_num)
  norm_num [NegativeTwo.CapCurve.sLo,NegativeTwo.CapCurve.sHi,
    NegativeTwo.CapCurve.cLo,NegativeTwo.CapCurve.cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith,by linarith⟩

lemma reference_cage :
    height reference∈Icc (3715901291/10000000000) (3715901296/10000000000) ∧
      k reference∈Icc (1212245417/1250000000) (4848981671/5000000000) := by
  have hh := NegativeTwo.CapCurve.reference_cage reference_mem reference_radical (by norm_num)
  rw [show reference=(137517/500000:ℝ) from rfl] at hh ⊢
  norm_num [NegativeTwo.CapCurve.sLo,NegativeTwo.CapCurve.sHi,
    NegativeTwo.CapCurve.cLo,NegativeTwo.CapCurve.cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma four_domain : Domain (2/5) :=
  ⟨four_mem,by linarith [four_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma reference_domain : Domain reference :=
  ⟨reference_mem,by linarith [reference_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma four_target_radical :
    U (height (2/5))∈Icc (42734882/25000000) (4273488201/2500000000) := by
  have hc := UW_circle (outer_domain (target_mem four_domain))
  have hp := U_positive (outer_domain (target_mem four_domain))
  norm_num [W,Q0] at hc
  constructor <;> nlinarith [four_cage.1.1,four_cage.1.2]

lemma reference_target_radical :
    U (height reference)∈Icc (3552987839/2000000000) (8882469599/5000000000) := by
  have hh := NegativeTwo.CapCurve.reference_cage reference_mem reference_radical (by norm_num)
  have hc := UW_circle (outer_domain (target_mem reference_domain))
  have hp := U_positive (outer_domain (target_mem reference_domain))
  rw [show reference=(137517/500000:ℝ) from rfl] at hh hc hp ⊢
  norm_num [NegativeTwo.CapCurve.sLo,NegativeTwo.CapCurve.sHi,
    NegativeTwo.CapCurve.cLo,NegativeTwo.CapCurve.cHi,Q0] at hh
  norm_num [W,Q0] at hc
  have hlo : (0:ℝ)≤height (137517/500000)+1/2 := by linarith [hh.1]
  have hsqlo := pow_le_pow_left₀ hlo
    (show height (137517/500000)+1/2≤371590129532063552910768681/1000000000000000000000000000+1/2
      by linarith [hh.2.1]) 2
  have hsqhi := pow_le_pow_left₀ (by norm_num)
    (show 1857950645621966662537750769/5000000000000000000000000000+1/2≤
      height (137517/500000)+1/2 by linarith [hh.1]) 2
  constructor
  · apply le_of_pow_le_pow_left₀ two_ne_zero hp.le
    norm_num at hsqlo ⊢
    linarith
  · apply le_of_pow_le_pow_left₀ two_ne_zero (by norm_num)
    norm_num at hsqhi ⊢
    linarith

lemma endpointUpper_outside : outerDiagonal<height endpointUpper := by
  have hh := NegativeTwo.CapCurve.reference_cage endpointUpper_mem endpointUpper_radical (by norm_num)
  rw [show endpointUpper=(375927951/500000000:ℝ) from rfl] at hh ⊢
  norm_num [NegativeTwo.CapCurve.sLo,NegativeTwo.CapCurve.sHi,
    NegativeTwo.CapCurve.cLo,NegativeTwo.CapCurve.cHi,Q0] at hh
  linarith [diagonal_fine.2]

lemma true_endpoint : ∃ e : ℝ, e∈Icc (2/5) endpointUpper ∧ height e=outerDiagonal := by
  have hcont : ContinuousOn height (Icc (2/5) endpointUpper) := fun x hx =>
    (NegativeTwo.CapCurve.height_hasDerivAt
      ⟨by linarith [hx.1],hx.2.trans endpointUpper_mem.2⟩).continuousAt.continuousWithinAt
  obtain ⟨e,he,hc⟩ := intermediate_value_Icc
    (show (2/5:ℝ)≤endpointUpper by norm_num [endpointUpper]) hcont
    (show outerDiagonal∈Icc (height (2/5)) (height endpointUpper) from
      ⟨four_domain.2,endpointUpper_outside.le⟩)
  exact ⟨e,he,hc⟩

lemma endpoint_domain {e : ℝ} (he : e∈Icc (2/5) endpointUpper)
    (hc : height e=outerDiagonal) : Domain e :=
  ⟨⟨by linarith [he.1],he.2.trans endpointUpper_mem.2⟩,by rw [hc]⟩

lemma source_bounded_by_end {b e : ℝ} (hb : Domain b)
    (he : e∈Icc (2/5) endpointUpper) (hc : height e=outerDiagonal) : b≤e := by
  have hed := endpoint_domain he hc
  have hmono : MonotoneOn (fun t => height t-(4/5)*t) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => ((NegativeTwo.CapCurve.height_hasDerivAt ht).sub
        ((hasDerivAt_id t).const_mul (4/5))).continuousAt.continuousWithinAt)
      (fun t ht => (NegativeTwo.CapCurve.height_hasDerivAt (Ioo_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).const_mul (4/5)))
      (fun t ht => by linarith [(NegativeTwo.CapCurve.k_bounds (Ioo_subset_Icc_self ht)).1])
  rcases le_total b e with h | h
  · exact h
  · have hh := hmono hed.1 hb.1 h
    simp only at hh
    rw [hc] at hh
    linarith [hb.2]

end SquaresInCircles.Eight.SecondWord.NegativeThree.Cap
end
end
end

section
/-!
## The first two original weak owners for negative edge three

A global chord for `K` and a global increment bound for `T` turn the
source-secondary projection directly into one positive quadratic.
The other three halves use the original geometric implication and
original angle order.  No auxiliary contact interval is needed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo (source_mem primary_mem)

theorem original_lower_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x)) :
    (93/100:ℝ)<value b B (Real.pi/2-x) := by
  have hb := source_mem hs
  have hB := source_mem ht
  have htr := positive_trig hx
  have hreserve := positive_taylor_reserves hx
  have hcut := lower_first_cut hx hm
  have hcos := mul_le_mul_of_nonneg_right
    (show A-1/2≤183/200 by linarith [(primary_mem ht).2,outer_endpoint_bounds.2.1])
    (show 0≤Real.cos x by linarith [htr.1])
  have hT := T_increment_upper outer_zero_mem hb hb.1
  rw [T_zero] at hT
  have hK := K_chord hB
  have hBs := mul_le_mul_of_nonneg_left htr.2.2.2.1.le hB.1
  have hquadratic : (93/100:ℝ)<Real.pi/2-x-167/10000-
      (1069/1000)*(183/200)*(1-(47/100)*x^2)+
        (1069/2000)*((9/10)*x)+1069/2000+K 0 := by
    nlinarith [pi_hand_enclosure.1,K_zero_bounds.1,sq_nonneg (x-113/200),hx.1]
  dsimp [value]
  nlinarith [hreserve.1,hreserve.2.1]

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  have hh := original_lower_source_secondary hs ht hx (upper_first_implies_lower ht hx hm)
  dsimp [value] at *
  linarith [hx.1]

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2-x)) :
    (93/100:ℝ)<value b B (Real.pi/2-x) := by
  have ht0 : OuterState outerAxial 0 := by
    simpa only [ShortOuterOne.SameContact.arc_zero] using
      ShortOuterOne.SameContact.arc_state outer_zero_mem
  have hh := original_lower_source_secondary hs ht0 hx
    (NegativeTwo.lower_second_implies_axial_first hs ht hx hm)
  have hK := K_lower (source_mem ht)
  dsimp [value] at *
  linarith

theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  have hK := K_lower (source_mem ht)
  by_cases hsmall : x≤11/100
  · have hb := NegativeTwo.upper_second_small_source hs ht ⟨hx.1,hsmall⟩ hm
    have hT := T_monotone (source_mem hs) T_six_mem hb.le
    dsimp [value]
    linarith [pi_hand_enclosure.1,T_six_value,K_zero_bounds.1,hx.1]
  · have hT := T_upper (source_mem hs)
    dsimp [value]
    linarith [pi_hand_enclosure.1,K_zero_bounds.1]

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
/-!
## A whole-arc affine bound for the zero-target contact angle

The comparison projection at angle `.571-.72*b` is strictly convex.
Its second derivative is positive by a circle-coordinate chord and the
elementary inequalities `cos C>5/6` and `sin C≤C`.  Both endpoint
projections are below one half, so every original zero-target contact
has smaller angle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.ZeroAngle

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def endpoint : ℝ := arc 1
def slope : ℝ := 18/25
def line (b : ℝ) : ℝ := 571/1000-slope*b
def projection (b : ℝ) : ℝ :=
  (U b-1)*Real.cos (line b)-W b*Real.sin (line b)
def first (b : ℝ) : ℝ :=
  (slope*W b-ratio b)*Real.cos (line b)+
    (slope*(U b-1)-1)*Real.sin (line b)
def core (b : ℝ) : ℝ := 2*slope-ratioD b-slope^2*(U b-1)
def coreFirst (b : ℝ) : ℝ := -ratioDD b+slope^2*ratio b
def coreSecond (b : ℝ) : ℝ := -ratioDDD b+slope^2*ratioD b
def loss (b : ℝ) : ℝ := 2*slope*ratio b-slope^2*W b
def lossFirst (b : ℝ) : ℝ := 2*slope*ratioD b-slope^2
def second (b : ℝ) : ℝ := core b*Real.cos (line b)-loss b*Real.sin (line b)

lemma endpoint_mem : endpoint∈Icc 0 outerDiagonal :=
  NegativeTwo.source_mem (ShortOuterOne.SameContact.primary_state primary_one_mem)

lemma endpoint_circle : U endpoint=3/2 := by
  have hh := (ShortOuterOne.SameContact.actual_arc
    (ShortOuterOne.SameContact.primary_state primary_one_mem)).1
  dsimp [endpoint,U]
  rw [hh]
  norm_num

lemma endpoint_bounds : (1581/2000:ℝ)<endpoint ∧ endpoint<791/1000 := by
  have hc := UW_circle (outer_domain endpoint_mem)
  rw [endpoint_circle] at hc
  norm_num [Q0] at hc
  have hb := endpoint_mem.1
  dsimp [W] at hc
  constructor <;> nlinarith

lemma source_mem {b : ℝ} (hb : b∈Icc 0 endpoint) : b∈Icc 0 outerDiagonal :=
  ⟨hb.1,hb.2.trans endpoint_mem.2⟩

lemma line_bounds {b : ℝ} (hb : b∈Icc 0 endpoint) :
    0<line b ∧ line b≤571/1000 := by
  dsimp [line,slope]
  constructor <;> linarith [hb.1,hb.2,endpoint_bounds.2]

lemma line_mem {b : ℝ} (hb : b∈Icc 0 endpoint) : line b∈Icc 0 (7/10) :=
  ⟨(line_bounds hb).1.le,by linarith [(line_bounds hb).2]⟩

lemma line_hasDerivAt (b : ℝ) : HasDerivAt line (-slope) b := by
  have h := ((hasDerivAt_id' b).const_mul slope).const_sub (571/1000:ℝ)
  rw [mul_one] at h
  exact h

lemma core_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt core (coreFirst b) b := by
  have hU : HasDerivAt U (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hh := ((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_sub
    (2*slope)).fun_sub ((hU.sub_const 1).const_mul (slope^2))
  exact hh.congr_deriv (by dsimp [coreFirst]; ring)

lemma coreFirst_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt coreFirst (coreSecond b) b :=
  (ratioDD_hasDerivAt (outer_domain hb)).fun_neg.fun_add
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul (slope^2))

lemma loss_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt loss (lossFirst b) b := by
  have hw : HasDerivAt W 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hh := ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    (2*slope)).fun_sub (hw.const_mul (slope^2))
  exact hh.congr_deriv (by dsimp [lossFirst]; ring)

lemma projection_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projection (first b) b := by
  have hc := (line_hasDerivAt b).cos
  have hs := (line_hasDerivAt b).sin
  have hu : HasDerivAt U (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hw : HasDerivAt W 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hh := ((hu.sub_const 1).fun_mul hc).fun_sub (hw.fun_mul hs)
  exact hh.congr_deriv (by dsimp [first]; ring)

lemma first_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt first (second b) b := by
  have hu : HasDerivAt U (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hw : HasDerivAt W 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hleft := (hw.const_mul slope).fun_sub
    (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb))
  have hright := ((hu.sub_const 1).const_mul slope).sub_const 1
  have hh := (hleft.fun_mul (line_hasDerivAt b).cos).fun_add
    (hright.fun_mul (line_hasDerivAt b).sin)
  exact hh.congr_deriv (by dsimp [second,core,loss]; ring)

lemma coreSecond_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : coreSecond b<0 := by
  have hu := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hU := (UW_bounds hb).2.1
  have hU4 := pow_lt_pow_left₀ hU hu.le (by norm_num : (4:ℕ)≠0)
  have he : coreSecond b*(U b)^7=
      Q0*(slope^2*(U b)^4-3*Q0-12*(W b)^2) := by
    have hD : ratioD b=Q0/(U b)^3 := rfl
    rw [coreSecond,ratioDDD,hD]
    field_simp
    linear_combination -3*Q0*hc
  have hp := pow_pos hu 7
  have hn : slope^2*(U b)^4-3*Q0-12*(W b)^2<0 := by
    norm_num [slope,Q0] at hU4 ⊢
    nlinarith [sq_nonneg (W b)]
  have hprod := mul_neg_of_pos_of_neg (show 0<Q0 by norm_num [Q0]) hn
  rw [← he] at hprod
  exact neg_of_mul_neg_left hprod hp.le

lemma core_zero : (407/1000:ℝ)<core 0 := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source_fine
  have hp := U_positive (outer_domain outer_zero_mem)
  have hlo : (957/500:ℝ)<U 0 := by linarith [hu.1]
  have hcube := pow_lt_pow_left₀ hlo (by norm_num : (0:ℝ)≤957/500)
    (by norm_num : (3:ℕ)≠0)
  have hD : ratioD 0<(2793/5000:ℝ) := by
    change Q0/(U 0)^3<(2793/5000:ℝ)
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at hcube ⊢
    linarith
  dsimp [core,slope]
  linarith [hu.2]

lemma core_endpoint : (103/5000:ℝ)<core endpoint := by
  have he : ratioD endpoint=Q0/(3/2)^3 := by
    change Q0/(U endpoint)^3=_
    rw [endpoint_circle]
  dsimp [core,slope]
  rw [he,endpoint_circle]
  norm_num [Q0]

lemma core_chord {b : ℝ} (hb : b∈Icc 0 endpoint) :
    (1/50:ℝ)+(12/25)*(endpoint-b)<core b := by
  have hconcave : ConcaveOn ℝ (Icc 0 endpoint)
      (fun t => core t-1/50-(12/25)*(endpoint-t)) := by
    apply concave_of_deriv2 (f' := fun t => coreFirst t+12/25)
      (fun t ht => (((core_hasDerivAt (source_mem ht)).sub_const (1/50)).fun_sub
        (((hasDerivAt_id' t).const_sub endpoint).const_mul (12/25))).congr_deriv (by ring))
      (fun t ht => (coreFirst_hasDerivAt (source_mem ht)).add_const (12/25))
    intro t ht
    exact (coreSecond_negative (source_mem ht)).le
  have hlo : 0<core 0-1/50-(12/25)*(endpoint-0) := by
    linarith [core_zero,endpoint_bounds.2]
  have hhi : 0<core endpoint-1/50-(12/25)*(endpoint-endpoint) := by
    linarith [core_endpoint]
  have hh := concave_gt_of_endpoints hconcave hb hlo hhi
  linarith

lemma ratioD_half {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (1/2:ℝ)<ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hU := (UW_bounds hb).2.1
  have hcube := pow_lt_pow_left₀ hU hu.le (by norm_num : (3:ℕ)≠0)
  change (1/2:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at hcube ⊢
  linarith

lemma loss_monotone : MonotoneOn loss (Icc 0 endpoint) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (loss_hasDerivAt (source_mem hb)).continuousAt.continuousWithinAt)
    (fun b hb => loss_hasDerivAt (source_mem (Ioo_subset_Icc_self hb)))
    (fun b hb => by
      have hh := ratioD_half (source_mem (Ioo_subset_Icc_self hb))
      dsimp [lossFirst,slope]
      linarith)

lemma loss_bounds {b : ℝ} (hb : b∈Icc 0 endpoint) : 0<loss b ∧ loss b<571/1000 := by
  have h0 := loss_monotone (show (0:ℝ)∈Icc 0 endpoint from ⟨le_rfl,endpoint_mem.1⟩) hb hb.1
  have h1 := loss_monotone hb (show endpoint∈Icc 0 endpoint from
    ⟨endpoint_mem.1,le_rfl⟩) hb.2
  have hz : 0<loss 0 := by
    have hr := (outer_ratio_bounds outer_zero_mem).1
    norm_num [loss,slope,W]
    linarith
  have he : loss endpoint<(571/1000:ℝ) := by
    have hr : ratio endpoint=W endpoint/(3/2) := by
      change W endpoint/U endpoint=_
      rw [endpoint_circle]
    dsimp [loss,slope]
    rw [hr]
    dsimp [W]
    linarith [endpoint_bounds.2]
  exact ⟨hz.trans_le h0,h1.trans_lt he⟩

lemma second_positive {b : ℝ} (hb : b∈Icc 0 endpoint) : 0<second b := by
  have hline := line_bounds hb
  have htr := positive_trig (line_mem hb)
  have ht := positive_taylor_reserves (line_mem hb)
  have hcos : (5/6:ℝ)<Real.cos (line b) := by
    have hs : (line b)^2≤(571/1000:ℝ)^2 := by nlinarith [hline.1,hline.2]
    nlinarith [ht.2.2]
  have hy : 0≤endpoint-b ∧ endpoint-b<(791/1000:ℝ) := by
    constructor <;> linarith [hb.1,hb.2,endpoint_bounds.2]
  have hc := core_chord hb
  have hl := loss_bounds hb
  have hfirst := mul_lt_mul'' hc hcos (by linarith [hy.1]) (by norm_num : (0:ℝ)≤5/6)
  have hlast := mul_le_mul hl.2.le htr.2.2.2.2.1 htr.2.2.1
    (by norm_num : (0:ℝ)≤571/1000)
  have hlin : line b<(23/12500:ℝ)+(18/25)*(endpoint-b) := by
    dsimp [line,slope]
    linarith [endpoint_bounds.1]
  dsimp [second]
  linarith [hy.1,hy.2]

lemma projection_zero : projection 0<(1/2:ℝ) := by
  have hc := cos_le_cos12 (show (0:ℝ)≤571/1000 by norm_num)
  have hs := sin11_le_sin (show (0:ℝ)≤571/1000 by norm_num)
  have hcos0 : 0≤Real.cos (571/1000) := by
    linarith [(positive_trig (show (571/1000:ℝ)∈Icc 0 (7/10) by norm_num)).1]
  have hu := NegativeTwo.TargetContact.Cap.zero_source_fine
  have hp := mul_le_mul
    (show U 0-1≤183/200 by linarith [hu.2]) hc hcos0
    (by norm_num : (0:ℝ)≤183/200)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hp hs
  dsimp [projection,line,slope,W]
  norm_num
  linarith

lemma projection_endpoint : projection endpoint<(1/2:ℝ) := by
  have hm : endpoint∈Icc 0 endpoint := ⟨endpoint_mem.1,le_rfl⟩
  have htr := positive_trig (line_mem hm)
  have ht := positive_taylor_reserves (line_mem hm)
  have hs : 0<Real.sin (line endpoint) := by
    nlinarith [(line_bounds hm).1,ht.1]
  have hw : 0<W endpoint := by dsimp [W]; linarith [endpoint_mem.1]
  have hp := mul_pos hw hs
  dsimp [projection]
  rw [endpoint_circle]
  linarith [htr.2.1]

lemma projection_upper {b : ℝ} (hb : b∈Icc 0 endpoint) : projection b<(1/2:ℝ) := by
  have hc : ConcaveOn ℝ (Icc 0 endpoint) (fun t => 1/2-projection t) :=
    concave_of_deriv2
      (fun t ht => (projection_hasDerivAt (source_mem ht)).const_sub (1/2))
      (fun t ht => (first_hasDerivAt (source_mem ht)).fun_neg)
      (fun t ht => by linarith [second_positive ht])
  have hh := concave_gt_of_endpoints (c := 0) hc hb
    (by linarith [projection_zero]) (by linarith [projection_endpoint])
  linarith

lemma original_source_range {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=0) :
    b∈Icc 0 endpoint := by
  have hm := NegativeTwo.TargetContact.B_angle_monotone hb (by norm_num) hx hx.1
  rw [NegativeTwo.TargetContact.B_zero,hc] at hm
  have hs := UW_circle (outer_domain hb)
  have he := UW_circle (outer_domain endpoint_mem)
  rw [endpoint_circle] at he
  have hu : (3/2:ℝ)≤U b := by dsimp [U]; linarith
  have hb0 := endpoint_mem.1
  dsimp [W] at hs he
  refine ⟨hb.1,?_⟩
  nlinarith

theorem original_angle {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=0) :
    x<571/1000-(18/25)*b := by
  have hrange := original_source_range hb hx hc
  have hp := projection_upper hrange
  have he : NegativeTwo.TargetContact.B b (line b)=1/2-projection b := by
    dsimp [NegativeTwo.TargetContact.B,projection,U,W]
    ring
  by_contra hn
  have hle : line b≤x := by dsimp [line,slope]; linarith
  have hm := NegativeTwo.TargetContact.B_angle_monotone hb (line_mem hrange) hx hle
  rw [he,hc] at hm
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeThree.ZeroAngle
end
end
end

section
/-!
## A whole-interval projection estimate for the endpoint contact

The product of the source radical and its rotated projection is concave
on the entire possible source interval.  Its two endpoint values give
one lower bound, with no interval rows.  This bounds the coefficient
ratio in the fourth derivative of the actual contact cost.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def projection (b : ℝ) : ℝ := c*W b+s*U b
def mass (b : ℝ) : ℝ := c*U b*W b+s*(U b)^2
def massD (b : ℝ) : ℝ := c*(U b-W b*ratio b)-2*s*W b
def massDD (b : ℝ) : ℝ := -c*(2*ratio b+W b*ratioD b)-2*s
def curvatureRatio (b : ℝ) : ℝ :=
  (3*(k1 b)^2+4*k b*k2 b)/(6*(k b)^2*k1 b)

lemma cap_source_mem : (19/25:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma cap_source_radical : (61/40:ℝ)<U (19/25) := by
  have hc := UW_circle (outer_domain cap_source_mem)
  have hp := U_positive (outer_domain cap_source_mem)
  norm_num [W,Q0] at hc
  nlinarith

lemma mass_identity (b : ℝ) : mass b=U b*projection b := by
  dsimp [mass,projection]
  ring

lemma projection_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projection (c-s*ratio b) b := by
  have h1 : HasDerivAt (fun t => t+1/2) 1 b := (hasDerivAt_id' b).add_const (1/2)
  have h2 := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  exact ((h1.const_mul c).add (h2.const_mul s)).congr_deriv (by ring)

lemma projection_monotone : MonotoneOn projection (Icc 0 outerDiagonal) := by
  refine monoOn_of_hasDeriv_nonneg
    (fun b hb => (projection_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun b hb => projection_hasDerivAt (Ioo_subset_Icc_self hb)) ?_
  intro b hb
  have hr := outer_ratio_bounds (Ioo_subset_Icc_self hb)
  have hh := mul_le_mul_of_nonneg_left hr.2.1
    (by linarith [trig.2.2.1] : 0≤ s)
  nlinarith [trig.1,trig.2.2.2]

lemma projection_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (323/200:ℝ)<projection b := by
  have hm := projection_monotone outer_zero_mem hb hb.1
  have hu := TargetContact.Cap.zero_source.1
  have hprod := mul_lt_mul trig.2.2.1 hu.le (by norm_num : (0:ℝ)<1914575671/1000000000)
    (by linarith [trig.2.2.1] : 0 ≤ s)
  dsimp only [projection,W] at hm ⊢
  linarith [trig.1]

lemma mass_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt mass (massD b) b := by
  have hu := U_positive (outer_domain hb)
  have hdU : HasDerivAt (fun t => arc t+1/2) (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hdW : HasDerivAt (fun t => t+1/2) 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hU2 : HasDerivAt (fun t => (arc t+1/2)^2) (2*(arc b+1/2)*(-ratio b)) b :=
    (hdU.pow 2).congr_deriv (by norm_num)
  have hd := ((hdU.const_mul c).mul hdW).add (hU2.const_mul s)
  have hr : (arc b+1/2)*ratio b=b+1/2 := by
    show (arc b+1/2)*((b+1/2)/(arc b+1/2))=b+1/2
    exact mul_div_cancel₀ _ hu.ne'
  exact hd.congr_deriv (by simp only [massD,U,W]; linear_combination (-2*s)*hr)

lemma massD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt massD (massDD b) b := by
  have hdU := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hdW : HasDerivAt (fun t => t+1/2) 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hd := ((hdU.sub (hdW.mul
    (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)))).const_mul c).sub
      (hdW.const_mul (2*s))
  exact hd.congr_deriv (by simp only [massDD,W]; ring)

lemma mass_second_nonpos {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : massDD b≤0 := by
  have hr := outer_ratio_bounds hb
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hh : 0<c*(2*ratio b+W b*ratioD b) :=
    mul_pos (by linarith [trig.1])
      (add_pos (by linarith [hr.1]) (mul_pos hw hr.2.2.1))
  dsimp [massDD]
  linarith [trig.2.2.1]

lemma mass_zero : (74/25:ℝ)< mass 0 := by
  have hu := TargetContact.Cap.zero_source.1
  have hc := UW_circle (outer_domain outer_zero_mem)
  have hfirst := mul_lt_mul trig.1 hu.le
    (by norm_num : (0:ℝ)<1914575671/1000000000) (by linarith [trig.1] : 0≤c)
  have hsecond := mul_lt_mul_of_pos_right trig.2.2.1
    (show (0:ℝ)<Q0-1/4 by norm_num [Q0])
  have hU2 : (U 0)^2=Q0-1/4 := by
    simp only [W] at hc
    linarith
  have he : mass 0=c*U 0*(1/2)+s*(Q0-1/4) := by
    simp only [mass,W]
    rw [hU2]
    ring
  rw [he]
  norm_num [Q0] at hsecond ⊢
  linarith

lemma mass_cap : (74/25:ℝ)< mass (19/25) := by
  have hc := UW_circle (outer_domain cap_source_mem)
  have hfirst := mul_lt_mul trig.1 cap_source_radical.le
    (by norm_num : (0:ℝ)<61/40) (by linarith [trig.1] : 0≤c)
  have hsecond := mul_lt_mul_of_pos_right trig.2.2.1
    (show (0:ℝ)<Q0-(63/50)^2 by norm_num [Q0])
  have hU2 : (U (19/25))^2=Q0-(63/50)^2 := by
    simp only [W] at hc
    linarith
  have he : mass (19/25)=c*U (19/25)*(63/50)+s*(Q0-(63/50)^2) := by
    simp only [mass,W]
    rw [hU2]
    ring
  rw [he]
  norm_num [Q0] at hsecond ⊢
  linarith

lemma mass_lower {b : ℝ} (hb : b∈Icc 0 (19/25)) :
    (74/25:ℝ)< mass b := by
  have hdom (t : ℝ) (ht : t∈Icc 0 (19/25)) : t∈Icc 0 outerDiagonal :=
    ⟨ht.1,ht.2.trans cap_source_mem.2⟩
  have hh := positive_of_second_nonpos (f := fun t => mass t-74/25)
    (d := massD) (dd := massDD) hb
      (fun t ht => (mass_hasDerivAt (hdom t ht)).sub_const (74/25))
      (fun t ht => massD_hasDerivAt (hdom t ht))
      (fun t ht => mass_second_nonpos (hdom t ht))
      (by linarith [mass_zero]) (by linarith [mass_cap])
  linarith

lemma curvatureRatio_identity {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    curvatureRatio b=c*Q0/(2*mass b*projection b)+2*W b/mass b := by
  have hu := U_positive (outer_domain hb)
  have hc : 0<c := by linarith [trig.1]
  have hp : 0<projection b := by linarith [projection_lower hb]
  have hm : 0 < mass b := by rw [mass_identity]; exact mul_pos hu hp
  have hk : k b=projection b/U b := by
    have hratio : ratio b=W b/U b := rfl
    rw [k,hratio,← mul_div_assoc,div_add' _ _ _ hu.ne']
    rfl
  have hk1 : k1 b=c*Q0/(U b)^3 := by dsimp [k1,ratioD,U]; ring
  have hk2 : k2 b=3*c*Q0*W b/(U b)^5 := by dsimp [k2,ratioDD,U,W]; ring
  rw [curvatureRatio,hk,hk1,hk2,mass_identity]
  field_simp [hu.ne',hc.ne',hp.ne',show Q0≠0 by norm_num [Q0]]
  ring

lemma curvatureRatio_upper {b : ℝ} (hb : Domain b) : curvatureRatio b<(6/5:ℝ) := by
  have hu := U_positive (outer_domain hb.1)
  have hm := mass_lower ⟨hb.1.1,(source_upper hb).le⟩
  have hp := projection_lower hb.1
  have hmass : 0 < mass b := by linarith
  have hproj : 0<projection b := by linarith
  have hmp := mul_lt_mul hm hp.le (by norm_num : (0:ℝ)<323/200) hmass.le
  have hq : 0<Q0 := by norm_num [Q0]
  have hfirst : c*Q0/(2*mass b*projection b)<
      ((153/200)*Q0)/(2*(74/25)*(323/200)) := by
    apply (div_lt_iff₀ (by positivity : 0<2*mass b*projection b)).2
    have hcq : c*Q0<(153/200)*Q0 :=
      mul_lt_mul_of_pos_right (by linarith [trig.2.1]) hq
    have hh := mul_lt_mul_of_pos_left hmp
      (show 0<2*((153/200)*Q0)/(2*(74/25)*(323/200)) by norm_num [Q0])
    norm_num [Q0] at hcq hh ⊢
    nlinarith
  have hsecond : 2*W b/mass b<(2*(63/50:ℝ))/(74/25) := by
    apply (div_lt_iff₀ hmass).2
    have hw : W b<(63/50:ℝ) := by dsimp [W]; linarith [source_upper hb]
    have hh := mul_lt_mul_of_pos_left hm (show (0:ℝ)<(2*(63/50))/(74/25) by norm_num)
    norm_num at hh ⊢
    linarith
  rw [curvatureRatio_identity hb.1]
  have hsum : ((153/200)*Q0)/(2*(74/25)*(323/200))+(2*(63/50:ℝ))/(74/25)<6/5 := by
    norm_num [Q0]
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve
end
end
end

section
/-!
## Positive fourth derivative on the full endpoint-angle contact

The target lies beyond the source on the same circle.  The increasing
fourth-derivative kernel pays the source fourth derivative.  A single
whole-domain projection bound pays the possibly negative target second
derivative.  The remaining term is positive.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic

lemma small_reference_mem : (61/500:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma small_reference_second : (-57/50:ℝ)<TLabel.d2 (61/500) := by
  have hh := TLabel.second_chart_reference (outer_domain small_reference_mem)
    (l := (2348/1250:ℝ)) (u := (3757/2000:ℝ))
    (dlo := (-57/50:ℝ)) (dhi := (-113/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.1

lemma small_reference_third : (173/100:ℝ)<TLabel.d3 (61/500) := by
  have hb := outer_domain small_reference_mem
  have hu := shifted_chart_reference hb
    (l := (2348/1250:ℝ)) (u := (3757/2000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hp := U_positive hb
  have he := TLabel.third_numerator hb
  have hpow := pow_le_pow_left₀ hp.le hu.2.le 5
  by_contra hneg
  have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hneg) (pow_pos hp 5).le
  rw [he] at hmul
  norm_num [TLabel,W,Q0] at hmul hpow
  linarith

lemma target_curvature_lower {b : ℝ} (hb : Domain b) :
    (-57/50:ℝ)<TLabel.d2 (height b) ∧ (173/100:ℝ)<TLabel.d3 (height b) := by
  have ht := target_mem hb
  have hh := (height_positive hb.1).le
  exact ⟨small_reference_second.trans_le
    (T_second_monotone small_reference_mem ht hh),
    small_reference_third.trans_le (T_third_monotone small_reference_mem ht hh)⟩

lemma leading_fourth_positive {b : ℝ} (hb : Domain b) :
    0< -PLabel.d4 b+TLabel.d4 (height b)*(k b)^4 := by
  have hp := P_fourth_positive hb.1
  have hdom := target_fourth_dominates hb.1 (target_mem hb)
    (target_above_source hb.1).le
  have hk := (k_bounds hb.1).1
  have hk0 : 0<k b := by linarith
  have hpow := pow_lt_pow_left₀ hk (by norm_num : (0:ℝ)≤21/25) (by norm_num : (4:ℕ)≠0)
  have hpaid : 1<8*(k b)^4 := by norm_num at hpow; linarith
  have hleft := mul_lt_mul_of_pos_left hpaid hp
  have hright := mul_lt_mul_of_pos_right hdom (pow_pos hk0 4)
  linarith

lemma middle_fourth_positive {b : ℝ} (hb : Domain b) :
    0<6*TLabel.d3 (height b)*(k b)^2*k1 b+
      TLabel.d2 (height b)*(3*(k1 b)^2+4*k b*k2 b) := by
  have hk := k_bounds hb.1
  have hk0 : 0<k b := by linarith [hk.1]
  have hden : 0<6*(k b)^2*k1 b := mul_pos (mul_pos (by norm_num) (pow_pos hk0 2)) hk.2.1
  have hnum : 0<3*(k1 b)^2+4*k b*k2 b :=
    add_pos (mul_pos (by norm_num) (pow_pos hk.2.1 2)) (mul_pos (mul_pos (by norm_num) hk0) hk.2.2.1)
  have hr0 : 0<curvatureRatio b := div_pos hnum hden
  have hr := curvatureRatio_upper hb
  have ht := target_curvature_lower hb
  have hproduct := mul_pos (show 0<TLabel.d2 (height b)+57/50 by linarith [ht.1]) hr0
  have hsum : 0<TLabel.d3 (height b)+TLabel.d2 (height b)*curvatureRatio b := by
    nlinarith [ht.2]
  have hfactor := mul_pos hden hsum
  have he : 6*(k b)^2*k1 b*curvatureRatio b=3*(k1 b)^2+4*k b*k2 b := by
    rw [curvatureRatio]
    exact mul_div_cancel₀ _ hden.ne'
  have hgoal : 6*TLabel.d3 (height b)*(k b)^2*k1 b+
      TLabel.d2 (height b)*(3*(k1 b)^2+4*k b*k2 b)=
        6*(k b)^2*k1 b*(TLabel.d3 (height b)+TLabel.d2 (height b)*curvatureRatio b) := by
    rw [← he]
    ring
  rw [hgoal]
  exact hfactor

theorem fourth_positive {b : ℝ} (hb : Domain b) : 0<fourth b := by
  have hlead := leading_fourth_positive hb
  have hmiddle := middle_fourth_positive hb
  have hlast := mul_pos (show 0<TLabel.d1 (height b) by
    linarith [T_first_lower (target_mem hb)]) (k_bounds hb.1).2.2.2
  dsimp [fourth]
  linarith

lemma third_monotone {b : ℝ} (hb : Domain b) : MonotoneOn third (Icc 0 b) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ht => (third_hasDerivAt (before hb ht)).continuousAt.continuousWithinAt)
    (fun _ ht => third_hasDerivAt (before hb (Ioo_subset_Icc_self ht)))
    (fun _ ht => (fourth_positive (before hb (Ioo_subset_Icc_self ht))).le)

lemma negative_second_concave {b : ℝ} (hb : Domain b) :
    ConcaveOn ℝ (Icc 0 b) (fun t => -second t) := by
  apply concave_of_deriv2
    (fun t ht => (second_hasDerivAt (before hb ht)).neg)
    (fun t ht => (third_hasDerivAt (before hb ht)).neg)
  intro t ht
  linarith [fourth_positive (before hb ht)]

end SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.ZeroTarget

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma half_mem : (1/2:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma half_second : TLabel.d2 (1/2)<(-42/125:ℝ) := by
  have hh := TLabel.second_chart_reference (outer_domain half_mem)
    (l := (683/400:ℝ)) (u := (4269/2500:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-42/125:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma half_first : TLabel.d1 (1/2)<(18/25:ℝ) := by
  have hh := TLabel.first_chart_reference (outer_domain half_mem)
    (l := (683/400:ℝ)) (u := (4269/2500:ℝ))
    (dlo := (0:ℝ)) (dhi := (18/25:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma third_references :
    T (1/3)-(18/25)*(1/3)<(69177/1000000:ℝ) ∧
      |TLabel.d1 (1/3)-18/25|<1/6250 := by
  have hm : (1/3:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hu := shifted_chart_reference (outer_domain hm)
    (l := (1794757798577723/1000000000000000:ℝ))
    (u := (448689449644431/250000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := FixedReference.target hm ⟨le_rfl,le_rfl⟩ ⟨hu.1.le,hu.2.le⟩
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hh
  constructor
  · linarith
  · rw [abs_lt]
    constructor <;> linarith

lemma early_label {b : ℝ} (hb : b∈Icc 0 (1/2)) :
    T b-(18/25)*b<(3459/50000:ℝ) := by
  have hdom (t : ℝ) (ht : t∈Icc 0 (1/2)) : t∈Icc 0 outerDiagonal :=
    ⟨ht.1,ht.2.trans half_mem.2⟩
  have hsec (t : ℝ) (ht : t∈Icc 0 (1/2)) : (42/125:ℝ)≤ -TLabel.d2 t := by
    have hm := T_second_monotone (hdom t ht) half_mem ht.2
    linarith [half_second]
  have hval : (18/25-TLabel.d1 (1/3))^2<
      2*(42/125)*(3459/50000-T (1/3)+(18/25)*(1/3)) := by
    have hd := (abs_lt.mp third_references.2)
    have hs : (18/25-TLabel.d1 (1/3))^2<(1/6250:ℝ)^2 := by nlinarith
    nlinarith [third_references.1]
  have hh := positive_of_curvature (f := fun t => 3459/50000-T t+(18/25)*t)
    (d := fun t => 18/25-TLabel.d1 t) (dd := fun t => -TLabel.d2 t)
    (κ := (42/125:ℝ)) (by norm_num) hb
    (show (1/3:ℝ)∈Icc 0 (1/2) by norm_num)
    (fun t ht => (((TLabel.outer_hasDerivAt (outer_domain (hdom t ht))).const_sub
        (3459/50000)).fun_add ((hasDerivAt_id' t).const_mul (18/25))).congr_deriv
        (by ring))
    (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom t ht))).const_sub (18/25))
    hsec hval
  linarith

lemma endpoint_first : TLabel.d1 ZeroAngle.endpoint<(18/25:ℝ) := by
  have hs := ShortOuterOne.SameContact.primary_state primary_one_mem
  have he := primary_first_exchange hs
  change TPrimaryLabel.d1 1*ratio ZeroAngle.endpoint=TLabel.d1 ZeroAngle.endpoint at he
  have hr : ratio ZeroAngle.endpoint<(1291/1500:ℝ) := by
    change W ZeroAngle.endpoint/U ZeroAngle.endpoint<_
    rw [ZeroAngle.endpoint_circle]
    dsimp [W]
    linarith [ZeroAngle.endpoint_bounds.2]
  have hr0 : 0≤ratio ZeroAngle.endpoint :=
    (ShortOuterOne.SameContact.ratio_pos (outer_domain ZeroAngle.endpoint_mem)).le
  have hm := primary_one_references
  have hp := mul_le_mul hm.2.1.le hr.le hr0 (by norm_num : (0:ℝ)≤38723/50000)
  rw [he] at hp
  norm_num at hp
  linarith

lemma late_first {b : ℝ} (hb : b∈Icc (1/2) ZeroAngle.endpoint) :
    TLabel.d1 b<(18/25:ℝ) := by
  have hdom (t : ℝ) (ht : t∈Icc (1/2) ZeroAngle.endpoint) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2.trans ZeroAngle.endpoint_mem.2⟩
  have hh := positive_of_second_nonpos
    (f := fun t => 18/25-TLabel.d1 t)
    (d := fun t => -TLabel.d2 t) (dd := fun t => -TLabel.d3 t) hb
    (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom t ht))).const_sub (18/25))
    (fun t ht => (TLabel.d2_hasDerivAt (outer_domain (hdom t ht))).neg)
    (fun t ht => by linarith [T_third_lower (hdom t ht)])
    (by linarith [half_first]) (by linarith [endpoint_first])
  linarith

theorem label_bound {b : ℝ} (hb : b∈Icc 0 ZeroAngle.endpoint) :
    T b-(18/25)*b<(3459/50000:ℝ) := by
  rcases le_total b (1/2) with h | h
  · exact early_label ⟨hb.1,h⟩
  · have hdom (t : ℝ) (ht : t∈Icc (1/2) ZeroAngle.endpoint) : t∈Icc 0 outerDiagonal :=
      ⟨by linarith [ht.1],ht.2.trans ZeroAngle.endpoint_mem.2⟩
    have hanti : AntitoneOn (fun t => T t-(18/25)*t) (Icc (1/2) ZeroAngle.endpoint) :=
      antiOn_of_hasDeriv_nonpos
        (fun t ht => ((TLabel.outer_hasDerivAt (outer_domain (hdom t ht))).sub
          ((hasDerivAt_id t).const_mul (18/25))).continuousAt.continuousWithinAt)
        (fun t ht => (TLabel.outer_hasDerivAt (outer_domain (hdom t (Ioo_subset_Icc_self ht)))).sub
          ((hasDerivAt_id t).const_mul (18/25)))
        (fun t ht => by linarith [late_first (Ioo_subset_Icc_self ht)])
    have hm := hanti (show (1/2:ℝ)∈Icc (1/2) ZeroAngle.endpoint from
      ⟨le_rfl,by linarith [ZeroAngle.endpoint_bounds.1]⟩) ⟨h,hb.2⟩ h
    exact hm.trans_lt (early_label (by norm_num))

theorem original_contact {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=0) :
    (9/10:ℝ)<value b 0 (Real.pi/2-x) := by
  have hr := ZeroAngle.original_source_range hb hx hc
  have ha := ZeroAngle.original_angle hb hx hc
  have hl := label_bound hr
  dsimp [value]
  linarith [pi_hand_enclosure.1,K_zero_bounds.1]

end SquaresInCircles.Eight.SecondWord.NegativeThree.ZeroTarget
end
end
end
