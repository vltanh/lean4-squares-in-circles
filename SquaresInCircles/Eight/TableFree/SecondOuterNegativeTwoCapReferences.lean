module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoCapFourth
public import SquaresInCircles.Eight.TableFree.SecondOuterSourceReference

/-!
# Physical enclosures at the four endpoint-contact references

The angle is fixed at `.7`.  Adjacent Taylor polynomials enclose its
sine and cosine once; each source radical and target radical is then
enclosed by rational squaring at the prescribed physical reference.
These are fixed references for a whole-curve calculus proof.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve

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

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve
