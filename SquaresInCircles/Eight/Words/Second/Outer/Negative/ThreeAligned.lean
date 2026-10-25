module

public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoTargetPrimaryLabel
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: the aligned negative edge-three minimum

The transformed source slope is below `.9` up to primary coordinate
one, while the necessary small target slope is above `.901`.  Beyond
one the source label increases.  Thus the actual aligned constraint
reduces to one physical circle point.
-/

section
/-!
## The complete aligned negative-quarter minimum

The third derivative of the aligned cost is positive throughout its
physical interval.  Its second derivative is therefore bounded above by
its negative right endpoint; its first derivative is bounded below by
its positive right endpoint.  The minimum is the original diagonal
source with target coordinate `1-d`.  No curvature partition is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma primary_fourth_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<PPrimaryLabel.d4 a := by
  have he := PPrimaryLabel.fourth_numerator (primary_domain ha)
  have hu := pow_pos (U_positive (primary_domain ha)) 7
  have hl : (1399/1000:ℝ)<W a := by
    dsimp [W]
    linarith [ha.1,fine_outer_endpoint_bounds.2]
  have hh : W a<(383/200:ℝ) := by
    dsimp [W]
    linarith [ha.2,outer_endpoint_bounds.2.1]
  have hpos : 0<PPrimaryLabel.d4 a*(U a)^7 := by
    rw [he]
    simp only [PPrimaryLabel,RoleLabel.primary,PLabel,Q0]
    nlinarith [sq_nonneg (W a-1/4)]
  by_contra hneg
  nlinarith [mul_le_mul_of_nonneg_right (not_lt.mp hneg) hu.le]

lemma primary_third_monotone :
    MonotoneOn PPrimaryLabel.d3 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (PPrimaryLabel.d3_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun _ ha => PPrimaryLabel.d3_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun _ ha => (primary_fourth_positive (Ioo_subset_Icc_self ha)).le)

lemma primary_third_diagonal : (1999/1000:ℝ)<PPrimaryLabel.d3 outerDiagonal := by
  have he := PPrimaryLabel.third_numerator
    (primary_domain OppositeTwo.primary_diagonal_mem)
  have hp := U_positive (primary_domain OppositeTwo.primary_diagonal_mem)
  have hUe : U outerDiagonal=outerDiagonal+1/2 := by
    rw [U,ShortOuterOne.SameContact.arc_diagonal]
  have hu : U outerDiagonal<(139922/100000:ℝ) := by
    rw [hUe]
    linarith [diagonal_fine.2]
  have hl : (139921/100000:ℝ)<W outerDiagonal := by
    dsimp only [W]
    linarith [diagonal_fine.1]
  have hpow := pow_le_pow_left₀ hp.le hu.le 5
  norm_num at hpow
  by_contra hneg
  have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hneg) (pow_pos hp 5).le
  rw [he] at hmul
  simp only [PPrimaryLabel,RoleLabel.primary,PLabel,Q0] at hmul
  linarith

lemma primary_one_second : PPrimaryLabel.d2 1<(6201/5000:ℝ) := by
  have hh := PPrimaryLabel.second_chart_reference (primary_domain primary_one_mem)
    (l := (129058126439213/100000000000000:ℝ))
    (u := (64529063219607/50000000000000:ℝ))
    (dlo := (31/25:ℝ)) (dhi := (6201/5000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
  exact hh.2

lemma target_zero_second : TLabel.d2 0< -(6673/5000:ℝ) := by
  have hh := TLabel.second_chart_reference (outer_domain outer_zero_mem)
    (l := (1914575671/1000000000:ℝ))
    (u := (239321959/125000000:ℝ))
    (dlo := -(267/200:ℝ)) (dhi := -(6673/5000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma primary_one_first_fine : (541709/500000:ℝ)<PPrimaryLabel.d1 1 := by
  have hh := PPrimaryLabel.first_chart_reference (primary_domain primary_one_mem)
    (l := (129058126439213/100000000000000:ℝ))
    (u := (64529063219607/50000000000000:ℝ))
    (dlo := (541709/500000:ℝ)) (dhi := (1083419/1000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
  exact hh.1

def aligned (a : ℝ) : ℝ := Real.pi/2+PPrimaryLabel.outer a+T (1-a)
def alignedD (a : ℝ) : ℝ := PPrimaryLabel.d1 a-TLabel.d1 (1-a)
def alignedDD (a : ℝ) : ℝ := PPrimaryLabel.d2 a+TLabel.d2 (1-a)
def alignedDDD (a : ℝ) : ℝ := PPrimaryLabel.d3 a-TLabel.d3 (1-a)

lemma aligned_domain {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    a∈Icc outerDiagonal outerAxial ∧ 1-a∈Icc 0 outerDiagonal ∧
      1-a∈Icc 0 (101/1000) := by
  refine ⟨⟨ha.1,ha.2.trans primary_one_mem.2⟩,?_,?_⟩
  · constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]
  · constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]

lemma aligned_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt aligned (alignedD a) a := by
  have ht := (TLabel.outer_hasDerivAt (outer_domain (aligned_domain ha).2.1)).comp a
    ((hasDerivAt_id' a).const_sub 1)
  have h := ((PPrimaryLabel.outer_hasDerivAt (primary_domain (aligned_domain ha).1)).const_add
    (Real.pi/2)).add ht
  exact h.congr_deriv (by simp only [alignedD]; ring)

lemma alignedD_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt alignedD (alignedDD a) a := by
  have ht := (TLabel.d1_hasDerivAt (outer_domain (aligned_domain ha).2.1)).comp a
    ((hasDerivAt_id' a).const_sub 1)
  have h := (PPrimaryLabel.d1_hasDerivAt (primary_domain (aligned_domain ha).1)).sub ht
  exact h.congr_deriv (by simp only [alignedDD]; ring)

lemma alignedDD_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt alignedDD (alignedDDD a) a := by
  have ht := (TLabel.d2_hasDerivAt (outer_domain (aligned_domain ha).2.1)).comp a
    ((hasDerivAt_id' a).const_sub 1)
  have h := (PPrimaryLabel.d2_hasDerivAt (primary_domain (aligned_domain ha).1)).add ht
  exact h.congr_deriv (by simp only [alignedDDD]; ring)

lemma aligned_third_positive {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    0<alignedDDD a := by
  have hm := primary_third_monotone OppositeTwo.primary_diagonal_mem
    (aligned_domain ha).1 ha.1
  have ht := T_third_small (aligned_domain ha).2.2
  dsimp [alignedDDD]
  linarith [primary_third_diagonal]

lemma aligned_second_monotone : MonotoneOn alignedDD (Icc outerDiagonal 1) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (alignedDD_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun _ ha => alignedDD_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun _ ha => (aligned_third_positive (Ioo_subset_Icc_self ha)).le)

lemma aligned_second_negative {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    alignedDD a< -(47/500:ℝ) := by
  have hm := aligned_second_monotone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2
  norm_num [alignedDD] at hm
  simp only [alignedDD]
  linarith [primary_one_second,target_zero_second]

lemma aligned_first_antitone : AntitoneOn alignedD (Icc outerDiagonal 1) :=
  antiOn_of_hasDeriv_nonpos
    (fun a ha => (alignedD_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun a ha => alignedD_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun a ha => by linarith [aligned_second_negative (Ioo_subset_Icc_self ha)])

lemma aligned_first_positive {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    (149/10000:ℝ)<alignedD a := by
  have hm := aligned_first_antitone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2
  norm_num [alignedD] at hm
  simp only [alignedD]
  linarith [primary_one_first_fine,T_first_zero_bounds.2]

lemma aligned_monotone : MonotoneOn aligned (Icc outerDiagonal 1) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (aligned_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun a ha => aligned_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun a ha => by linarith [aligned_first_positive (Ioo_subset_Icc_self ha)])

lemma aligned_target_reference :
    (47134490161383/25000000000000:ℝ)<U (1-outerDiagonal) ∧
      U (1-outerDiagonal)<188537960645533/100000000000000 := by
  have hd : outerDiagonal∈Icc outerDiagonal 1 :=
    ⟨le_rfl,primary_one_mem.1⟩
  have hb := (aligned_domain hd).2.1
  have hc := UW_circle (outer_domain hb)
  have hp := U_positive (outer_domain hb)
  have hw : (60078593489059/100000000000000:ℝ)<W (1-outerDiagonal) ∧
      W (1-outerDiagonal)<60078593489060/100000000000000 := by
    dsimp [W]
    constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
  norm_num [Q0] at hc
  constructor <;> nlinarith

lemma P_diagonal_fine : P outerDiagonal<(395450837/500000000:ℝ) := by
  have hc := UW_circle (outer_domain
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩))
  norm_num [U,W,ShortOuterOne.SameContact.arc_diagonal,Q0] at hc
  dsimp [P,RoleLabel.outer,RoleLabel.eval,PLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [diagonal_fine.2]

lemma aligned_diagonal : (8977827/10000000:ℝ)<aligned outerDiagonal := by
  have hb : (10078593489059/100000000000000:ℝ)<1-outerDiagonal ∧
      1-outerDiagonal<10078593489060/100000000000000 := by
    constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
  have ha : arc (1-outerDiagonal)<138537960645533/100000000000000 := by
    have hh := aligned_target_reference.2
    dsimp [U] at hh
    linarith
  have hapos : 0≤arc (1-outerDiagonal) :=
    (ShortOuterOne.SameContact.arc_state
      (aligned_domain ⟨le_rfl,primary_one_mem.1⟩).2.1).2.1.trans'
      (aligned_domain ⟨le_rfl,primary_one_mem.1⟩).2.1.1
  have hm := mul_le_mul ha.le hb.2.le (by linarith [hb.1])
    (by norm_num : (0:ℝ)≤138537960645533/100000000000000)
  have hsq := pow_le_pow_left₀ (by linarith [hb.1] : (0:ℝ)≤1-outerDiagonal) hb.2.le 2
  have he : PPrimaryLabel.outer outerDiagonal= -P outerDiagonal := by
    exact PLabel.primary_actual
      (by simpa only [ShortOuterOne.SameContact.arc_diagonal] using
        primary_state OppositeTwo.primary_diagonal_mem)
  dsimp [aligned]
  rw [he]
  dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  nlinarith [P_diagonal_fine,pi_hand_enclosure.1]

lemma aligned_lower {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    (8977827/10000000:ℝ)<aligned a :=
  aligned_diagonal.trans_le
    (aligned_monotone ⟨le_rfl,primary_one_mem.1⟩ ha ha.1)

theorem original_aligned {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (halign : 1≤a+B) : (8977827/10000000:ℝ)<value b B (Real.pi/2) := by
  have hmactual : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
  by_cases ha : a≤1
  · have hdom := aligned_domain ⟨(primary_mem hs).1,ha⟩
    have hT := T_monotone hdom.2.1 (source_mem ht) (by linarith)
    have hf := aligned_lower ⟨(primary_mem hs).1,ha⟩
    dsimp [aligned,value] at *
    rw [hmactual] at hf
    linarith
  · have hM := OppositeTwo.M_monotone primary_one_mem (primary_mem hs) (by linarith)
    have hT := T_lower (source_mem ht)
    have hf := aligned_lower ⟨primary_one_mem.1,le_rfl⟩
    dsimp [aligned,value] at *
    norm_num only [sub_self,T_zero] at hf
    rw [hmactual] at hM
    linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
/-!
## Three fixed references on the lower primary diagonal

The rational angles `.3`, `.4`, and `.556` give the transition bounds
for the physical curve.  Their enclosures follow from the exact
diagonal, adjacent Taylor polynomials, and circle square comparisons.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

lemma trig_reference {x sl sh cl ch : ℝ} (hx : 0≤x)
    (hsl : sl≤ sin11 x) (hsh : sin9 x≤ sh)
    (hcl : cl≤cos10 x) (hch : cos12 x≤ch) :
    Real.sin x∈Icc sl sh ∧ Real.cos x∈Icc cl ch :=
  ⟨⟨hsl.trans (sin11_le_sin hx),(sin_le_sin9 hx).trans hsh⟩,
    ⟨hcl.trans (cos10_le_cos hx),(cos_le_cos12 hx).trans hch⟩⟩

lemma three_trig :
    Real.sin (3/10:ℝ)∈Icc (295520206/1000000000) (295520207/1000000000) ∧
      Real.cos (3/10:ℝ)∈Icc (955336489/1000000000) (955336490/1000000000) :=
  trig_reference (by norm_num)
    (by norm_num [sin11,sin9,sin7]) (by norm_num [sin9,sin7])
    (by norm_num [cos10,cos8]) (by norm_num [cos12,cos10,cos8])

lemma four_trig :
    Real.sin (2/5:ℝ)∈Icc (389418342/1000000000) (389418343/1000000000) ∧
      Real.cos (2/5:ℝ)∈Icc (921060994/1000000000) (921060995/1000000000) :=
  trig_reference (by norm_num)
    (by norm_num [sin11,sin9,sin7]) (by norm_num [sin9,sin7])
    (by norm_num [cos10,cos8]) (by norm_num [cos12,cos10,cos8])

lemma end_trig :
    Real.sin (139/250:ℝ)∈Icc (527792937/1000000000) (527792938/1000000000) ∧
      Real.cos (139/250:ℝ)∈Icc (849373072/1000000000) (849373073/1000000000) :=
  trig_reference (by norm_num)
    (by norm_num [sin11,sin9,sin7]) (by norm_num [sin9,sin7])
    (by norm_num [cos10,cos8]) (by norm_num [cos12,cos10,cos8])

lemma three_Z : Z (3/10)∈Icc (556122423/1000000000) (556122426/1000000000) := by
  dsimp [Z,offset]
  exact ⟨by linarith [three_trig.2.1,diagonal_fine.2],
    by linarith [three_trig.2.2,diagonal_fine.1]⟩

lemma four_Z : Z (2/5)∈Icc (521846928/1000000000) (521846930/1000000000) := by
  dsimp [Z,offset]
  exact ⟨by linarith [four_trig.2.1,diagonal_fine.2],
    by linarith [four_trig.2.2,diagonal_fine.1]⟩

lemma end_Z : Z (139/250)∈Icc (450159006/1000000000) (450159008/1000000000) := by
  dsimp [Z,offset]
  exact ⟨by linarith [end_trig.2.1,diagonal_fine.2],
    by linarith [end_trig.2.2,diagonal_fine.1]⟩

lemma three_Y : Y (3/10)∈Icc (1899033397/1000000000) (1899033400/1000000000) := by
  have hh := radical_data (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hc := hh.2.2.2.2
  norm_num [Q0] at hc
  constructor <;> nlinarith [hh.2.2.1,three_Z.1,three_Z.2]

lemma four_Y : Y (2/5)∈Icc (1908736697/1000000000) (1908736700/1000000000) := by
  have hh := radical_data (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
  have hc := hh.2.2.2.2
  norm_num [Q0] at hc
  constructor <;> nlinarith [hh.2.2.1,four_Z.1,four_Z.2]

lemma end_Y : Y (139/250)∈Icc (1926903439/1000000000) (1926903443/1000000000) := by
  have hh := radical_data (show (139/250:ℝ)∈Icc 0 (7/10) by norm_num)
  have hc := hh.2.2.2.2
  norm_num [Q0] at hc
  constructor <;> nlinarith [hh.2.2.1,end_Z.1,end_Z.2]

lemma coordinate_cage {x sl sh cl ch zl zh yl yh : ℝ}
    (hx : x∈Icc 0 (7/10)) (hs : Real.sin x∈Icc sl sh)
    (hc : Real.cos x∈Icc cl ch) (hz : Z x∈Icc zl zh) (hy : Y x∈Icc yl yh)
    (hsl : 0≤ sl) (hcl : 0≤cl) (_hzl : 0≤zl) (hyl : 0<yl) :
    yl*cl-zh*sh≤horizontal x ∧ horizontal x≤yh*ch-zl*sl ∧
      yl*sl+zl*cl≤vertical x ∧ vertical x≤yh*sh+zh*ch ∧
      1-sh/yl≤factor x ∧ factor x≤1-sl/yh := by
  have hh := radical_data hx
  have ht := positive_trig hx
  have hyp : 0<Y x := by linarith [hh.2.2.1]
  have hyhp : 0<yh := hyp.trans_le hy.2
  have hYcL := mul_le_mul hy.1 hc.1 hcl hyp.le
  have hYcH := mul_le_mul hy.2 hc.2 (by linarith [ht.1]) hyhp.le
  have hZsL := mul_le_mul hz.1 hs.1 hsl hh.1.le
  have hZsH := mul_le_mul hz.2 hs.2 ht.2.2.1 (hh.1.le.trans hz.2)
  have hYsL := mul_le_mul hy.1 hs.1 hsl hyp.le
  have hYsH := mul_le_mul hy.2 hs.2 ht.2.2.1 hyhp.le
  have hZcL := mul_le_mul hz.1 hc.1 hcl hh.1.le
  have hZcH := mul_le_mul hz.2 hc.2 (by linarith [ht.1]) (hh.1.le.trans hz.2)
  have hdivL : sl/yh≤Real.sin x/Y x := by
    apply (le_div_iff₀ hyp).2
    have hm := mul_le_mul_of_nonneg_left hy.2 (div_nonneg hsl hyhp.le)
    have he : (sl/yh)*yh=sl := by field_simp [hyhp.ne']
    rw [he] at hm
    linarith [hs.1]
  have hdivH : Real.sin x/Y x≤ sh/yl := by
    apply (div_le_iff₀ hyp).2
    have hm := mul_le_mul_of_nonneg_left hy.1
      (div_nonneg (ht.2.2.1.trans hs.2) hyl.le)
    have he : (sh/yl)*yl=sh := by field_simp [hyl.ne']
    rw [he] at hm
    linarith [hs.2]
  dsimp [horizontal,vertical,factor]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma three_reference : height (3/10)<3/5 ∧ (273/250:ℝ)<vertical (3/10) ∧
    speed (3/10)<697/500 := by
  have hh := coordinate_cage (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num)
    three_trig.1 three_trig.2 three_Z three_Y
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hu : horizontal (3/10)<1649871/1000000 := by norm_num at hh; linarith
  have hf : factor (3/10)<105548/125000 := by norm_num at hh; linarith
  have hp := factor_bounds (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_lt_mul hu hf.le (by linarith [hp.1] : 0<factor (3/10))
    (by norm_num : (0:ℝ)≤1649871/1000000)
  norm_num at hh hprod
  dsimp [height,speed]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma four_reference :
    (3/5:ℝ)<height (2/5) ∧ height (2/5)<181/250 ∧
      (777/500:ℝ)<horizontal (2/5) ∧ (159/200:ℝ)<factor (2/5) ∧
      speed (2/5)<619/500 := by
  have hh := coordinate_cage (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
    four_trig.1 four_trig.2 four_Z four_Y
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hu : horizontal (2/5)<1554847/1000000 := by norm_num at hh; linarith
  have hf : factor (2/5)<397991/500000 := by norm_num at hh; linarith
  have hp := factor_bounds (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_lt_mul hu hf.le (by linarith [hp.1] : 0<factor (2/5))
    (by norm_num : (0:ℝ)≤1554847/1000000)
  norm_num at hh hprod
  dsimp [height,speed]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma end_reference : outerDiagonal<height (139/250) := by
  have hh := coordinate_cage (show (139/250:ℝ)∈Icc 0 (7/10) by norm_num)
    end_trig.1 end_trig.2 end_Z end_Y
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
  dsimp [height]
  linarith [diagonal_fine.2]

lemma four_domain : Domain (2/5) :=
  ⟨by norm_num,by linarith [four_reference.2.1,fine_outer_endpoint_bounds.2]⟩

lemma mid_factorD {x : ℝ} (hx : x∈Icc 0 (2/5)) : factorD x< -2/5 := by
  have hxfull : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hy := radical_data hxfull
  have ht := positive_trig hxfull
  have hc := cos_anti hxfull (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have hcos : (23/25:ℝ)<Real.cos x := by linarith [four_trig.2.1]
  have hnum := factorD_numerator hxfull
  have hk := offset_bounds
  have hcoef : (6889/2500:ℝ)<Q0-1-offset^2 := by norm_num [Q0]; nlinarith
  have hfirst := mul_lt_mul hcoef hcos.le (by norm_num : (0:ℝ)<23/25)
    (by linarith [hcoef] : 0≤Q0-1-offset^2)
  have hsq := pow_lt_pow_left₀ hcos (by norm_num : (0:ℝ)≤23/25) (by norm_num : (2:ℕ)≠0)
  have hsecond := mul_lt_mul
    (show (399/1000:ℝ)< -offset by linarith [hk.2])
    (show (1+(23/25)^2:ℝ)≤1+(Real.cos x)^2 by linarith)
    (by norm_num : (0:ℝ)<1+(23/25)^2) (by linarith [hk.2] : 0≤ -offset)
  have hycube := pow_lt_pow_left₀ hy.2.2.2.1 (show 0≤Y x by linarith [hy.2.2.1])
    (by norm_num : (3:ℕ)≠0)
  have hycube0 := pow_pos (show 0<Y x by linarith [hy.2.2.1]) 3
  norm_num at hfirst hsecond hycube
  by_contra hcon
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hcon) hycube0.le
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal
end
end
end

section
/-!
## The complete lower source-primary diagonal bound

The physical diagonal cost is concave through `.4` and decreases
afterward.  The increasing circle coordinate reaches its actual sorted
endpoint before `.556`.  Both true endpoints have strict reserves.
The final theorem identifies this curve from the original target circle
and original weak-axis contact equation.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal

open CommonQuarter CorePairGeometry Arithmetic

def cost (x : ℝ) : ℝ := value outerDiagonal (height x) (Real.pi/2-x)
def first (x : ℝ) : ℝ := -1+TLabel.d1 (height x)*speed x
def second (x : ℝ) : ℝ :=
  TLabel.d2 (height x)*(speed x)^2+TLabel.d1 (height x)*acceleration x

lemma before {x t : ℝ} (hx : Domain x) (ht : t∈Icc 0 x) : Domain t := by
  have htf : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hx.1.2⟩
  exact ⟨htf,(height_monotone htf hx.1 ht.2).trans hx.2⟩

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hT := (TLabel.outer_hasDerivAt (outer_domain (target_mem hx))).comp x
    (height_hasDerivAt hx.1)
  have hd := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const
    (P outerDiagonal)).fun_add hT
  show HasDerivAt (fun y => Real.pi/2-y-P outerDiagonal+(TLabel.outer ∘ height) y) _ x
  exact hd.congr_deriv (by dsimp [first])

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hd := (((TLabel.d1_hasDerivAt (outer_domain (target_mem hx))).comp x
    (height_hasDerivAt hx.1)).fun_mul (speed_hasDerivAt hx.1)).const_add (-1)
  show HasDerivAt (fun y => -1+(TLabel.d1 ∘ height) y*speed y) _ x
  refine hd.congr_deriv ?_
  simp only [Function.comp_apply,second]
  ring

lemma target_second_mid {b : ℝ} (hb : b∈Icc 0 (181/250)) :
    TLabel.d2 b<(99/250:ℝ) := by
  have href : (181/250:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hm := T_second_monotone ⟨hb.1,hb.2.trans href.2⟩ href hb.2
  have hh := TLabel.second_chart_reference (outer_domain href)
    (l := (3887/2500:ℝ)) (u := (15549/10000:ℝ))
    (dlo := (-2:ℝ)) (dhi := (99/250:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hm.trans_lt hh.2

lemma target_first_late {b : ℝ} (hb : b∈Icc (3/5) outerDiagonal) :
    TLabel.d1 b<(387/500:ℝ) := by
  have hdom (t : ℝ) (ht : t∈Icc (3/5) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hh := positive_of_second_nonpos
    (f := fun t => 387/500-TLabel.d1 t)
    (d := fun t => -TLabel.d2 t) (dd := fun t => -TLabel.d3 t) hb
    (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom t ht))).const_sub (387/500))
    (fun t ht => (TLabel.d2_hasDerivAt (outer_domain (hdom t ht))).neg)
    (fun t ht => by linarith [T_third_lower (hdom t ht)])
    (by linarith [T_six_first.2])
    (by rw [T_first_diagonal]; linarith [fine_outer_endpoint_bounds.2])
  linarith

lemma early_second {x : ℝ} (hx : x∈Icc 0 (3/10)) : second x<0 := by
  have hd := before four_domain (show x∈Icc 0 (2/5) from ⟨hx.1,by linarith [hx.2]⟩)
  have hB := target_mem hd
  have hm := height_monotone hd.1 (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have ht := T_second_early (show height x∈Icc 0 (3/5) from
    ⟨hB.1,by linarith [three_reference.1]⟩)
  have hleft := mul_neg_of_neg_of_pos (by linarith [ht] : TLabel.d2 (height x)<0)
    (pow_pos (show 0<speed x by linarith [speed_positive hd.1]) 2)
  have hright := mul_neg_of_pos_of_neg
    (by linarith [T_first_lower hB] : 0<TLabel.d1 (height x))
    (acceleration_negative hd.1)
  dsimp [second]
  linarith

lemma middle_second {x : ℝ} (hx : x∈Icc (3/10) (2/5)) : second x<0 := by
  have hd := before four_domain (show x∈Icc 0 (2/5) from ⟨by linarith [hx.1],hx.2⟩)
  have hB := target_mem hd
  have hheight := height_monotone hd.1 four_domain.1 hx.2
  have hT := target_second_mid ⟨hB.1,by linarith [four_reference.2.1]⟩
  have hspeed := speed_antitone (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hd.1 hx.1
  have hspeedupper : speed x<(697/500:ℝ) := hspeed.trans_lt three_reference.2.2
  have hspeed0 : 0<speed x := by linarith [speed_positive hd.1]
  have hsq := pow_lt_pow_left₀ hspeedupper hspeed0.le (by norm_num : (2:ℕ)≠0)
  have hpositive := mul_lt_mul_of_pos_right hT (pow_pos hspeed0 2)
  have hvertical := height_monotone (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hd.1 hx.1
  have hV : (273/250:ℝ)<vertical x := by
    dsimp [height] at hvertical
    linarith [three_reference.2.1]
  have hhorizontal := horizontal_antitone hd.1 four_domain.1 hx.2
  have hU : (777/500:ℝ)<horizontal x := four_reference.2.2.1.trans_le hhorizontal
  have hfactor := factor_antitone hd.1 four_domain.1 hx.2
  have hf : (159/200:ℝ)<factor x := four_reference.2.2.2.1.trans_le hfactor
  have hf2 := pow_lt_pow_left₀ hf (by norm_num : (0:ℝ)≤159/200) (by norm_num : (2:ℕ)≠0)
  have hleft := mul_lt_mul hV hf2.le (by norm_num : (0:ℝ)<(159/200)^2)
    (by linarith [hV] : 0≤vertical x)
  have hfd := mid_factorD (show x∈Icc 0 (2/5) from ⟨by linarith [hx.1],hx.2⟩)
  have hright := mul_lt_mul hU (show (2/5:ℝ)≤ -factorD x by linarith)
    (by norm_num : (0:ℝ)<2/5) (by linarith [hU] : 0≤horizontal x)
  have hacc : (273/250:ℝ)*(159/200)^2+(777/500)*(2/5)< -acceleration x := by
    dsimp [acceleration]
    linarith
  have hpaid := mul_lt_mul (T_first_lower hB) hacc.le
    (by norm_num : (0:ℝ)<(273/250)*(159/200)^2+(777/500)*(2/5))
    (by linarith [T_first_lower hB] : 0≤TLabel.d1 (height x))
  dsimp [second]
  norm_num at hsq hpaid
  linarith

lemma initial_concave : ConcaveOn ℝ (Icc 0 (2/5)) cost := by
  apply concave_of_deriv2
    (fun x hx => cost_hasDerivAt (before four_domain hx))
    (fun x hx => first_hasDerivAt (before four_domain hx))
  intro x hx
  rcases le_total x (3/10) with h | h
  · exact (early_second ⟨hx.1,h⟩).le
  · exact (middle_second ⟨h,hx.2⟩).le

lemma late_first {x : ℝ} (hx : Domain x) (hfour : (2/5:ℝ)≤x) : first x<0 := by
  have hm := height_monotone four_domain.1 hx.1 hfour
  have hT := target_first_late (show height x∈Icc (3/5) outerDiagonal from
    ⟨by linarith [four_reference.1],hx.2⟩)
  have hspeed := speed_antitone four_domain.1 hx.1 hfour
  have hspeedupper := hspeed.trans_lt four_reference.2.2.2.2
  have hh := mul_lt_mul hT hspeedupper.le
    (by linarith [speed_positive hx.1] : 0<speed x) (by norm_num : (0:ℝ)≤387/500)
  dsimp [first]
  norm_num at hh
  linarith

lemma end_contact : ∃ e : ℝ, e∈Icc (2/5) (139/250) ∧ height e=outerDiagonal := by
  have hcont : ContinuousOn height (Icc (2/5) (139/250)) := by
    intro x hx
    exact (height_hasDerivAt (show x∈Icc 0 (7/10) from
      ⟨by linarith [hx.1],by linarith [hx.2]⟩)).continuousAt.continuousWithinAt
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc (show (2/5:ℝ)≤139/250 by norm_num)
    hcont (show outerDiagonal∈Icc (height (2/5)) (height (139/250)) from
      ⟨four_domain.2,end_reference.le⟩)
  exact ⟨e,he,heq⟩

lemma target_diagonal_lower : (679/1000:ℝ)<T outerDiagonal := by
  have hd := diagonal_fine
  have hs := (ShortOuterOne.SameContact.arc_state
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)).2.2
  rw [ShortOuterOne.SameContact.arc_diagonal] at hs
  have he : T outerDiagonal=167/10000+(121161/50000)*outerDiagonal-
      (187513/100000)*outerDiagonal^2 := by
    dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel]
    rw [ShortOuterOne.SameContact.arc_diagonal]
    ring
  rw [he]
  norm_num [Q0] at hs
  linarith [hd.1]

lemma zero_value : (8977827/10000000:ℝ)<cost 0 := by
  have hb := target_mem (before four_domain (show (0:ℝ)∈Icc 0 (2/5) by norm_num))
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hh := original_aligned (ShortOuterOne.SameContact.arc_state hd)
    (ShortOuterOne.SameContact.arc_state hb)
    (show 1≤ShortOuterOne.SameContact.arc outerDiagonal+height 0 by
      rw [ShortOuterOne.SameContact.arc_diagonal,height_zero]
      linarith)
  simpa only [cost,sub_zero] using hh

lemma endpoint_value {e : ℝ} (he : e∈Icc (2/5) (139/250)) (hc : height e=outerDiagonal) :
    (9/10:ℝ)<cost e := by
  dsimp [cost,value]
  rw [hc]
  linarith [pi_hand_enclosure.1,P_diagonal_fine,target_diagonal_lower,he.2]

lemma bounded_by_end {x e : ℝ} (hx : Domain x) (he : e∈Icc (2/5) (139/250))
    (hc : height e=outerDiagonal) : x≤e := by
  rcases le_total x e with h | h
  · exact h
  · have hef : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
    have hm := height_half_monotone hef hx.1 h
    dsimp only at hm
    rw [hc] at hm
    linarith [hx.2]

theorem cost_lower {x : ℝ} (hx : Domain x) : (8977827/10000000:ℝ)<cost x := by
  obtain ⟨e,he,hc⟩ := end_contact
  have hefull : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
  have hed : Domain e := ⟨hefull,by rw [hc]⟩
  have hxe := bounded_by_end hx he hc
  have hanti : AntitoneOn cost (Icc (2/5) e) := by
    have hdom (t : ℝ) (ht : t∈Icc (2/5) e) : Domain t :=
      before hed ⟨by linarith [ht.1],ht.2⟩
    exact antiOn_of_hasDeriv_nonpos
      (fun t ht => (cost_hasDerivAt (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => cost_hasDerivAt (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (late_first (hdom t (Ioo_subset_Icc_self ht)) ht.1.le).le)
  have hend := endpoint_value he hc
  rcases le_total x (2/5) with h | h
  · have hfour := hanti (show (2/5:ℝ)∈Icc (2/5) e from ⟨le_rfl,he.1⟩)
      (show e∈Icc (2/5) e from ⟨he.1,le_rfl⟩) he.1
    exact concave_gt_of_endpoints initial_concave ⟨hx.1.1,h⟩ zero_value (by linarith)
  · have hm := hanti (show x∈Icc (2/5) e from ⟨h,hxe⟩)
      (show e∈Icc (2/5) e from ⟨he.1,le_rfl⟩) hxe
    linarith

lemma original_height {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hc : lowerSource A B x=outerDiagonal) : height x=B := by
  let r : ℝ := (A+1/2)*Real.cos x+(B+1/2)*Real.sin x
  have htr := positive_trig hx
  have hr : 0<r := by
    have hfirst := mul_pos (show 0<A+1/2 by linarith [ht.1,ht.2.1])
      (show 0<Real.cos x by linarith [htr.1])
    have hlast := mul_nonneg (show 0≤B+1/2 by linarith [ht.1]) htr.2.2.1
    dsimp [r]
    linarith
  have hz : Z x=(B+1/2)*Real.cos x-(A+1/2)*Real.sin x := by
    dsimp [lowerSource] at hc
    dsimp [Z,offset]
    linarith
  have hcircle : r^2+(Z x)^2=Q0 := by
    rw [hz]
    dsimp [r]
    linear_combination ht.2.2+
      ((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=r := by
    have hy := radical_data hx
    have h2 : (Y x)^2=r^2 := by linarith [hy.2.2.2.2]
    exact (pow_left_inj₀ (by linarith [hy.2.2.1]) hr.le two_ne_zero).1 h2
  dsimp [height,vertical]
  rw [hY,hz]
  dsimp [r]
  linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

theorem original_contact {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hc : lowerSource A B x=outerDiagonal) :
    (8977827/10000000:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have he := original_height ht hx hc
  have hd : Domain x := ⟨hx,by rw [he]; exact (source_mem ht).2⟩
  simpa only [cost,he] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal
end
end
end

section
/-!
## The transformed source label for negative edge three

On the primary-coordinate circle chart, the source label has positive
third derivative and its fourth derivative exceeds `9/2` times its
third derivative.  One fixed reference at primary coordinate one gives
the global slope floor `.76` by a tangent parabola.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def primaryMass : ℝ := 763901/200000
def primaryCross : ℝ := 95769/100000
def primaryNumerator (a : ℝ) : ℝ := primaryMass*W a-primaryCross*Q0

lemma primary_chart {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (1/2:ℝ)≤U a ∧ U a<7/5 ∧ (1399/1000:ℝ)<W a ∧ W a<383/200 ∧ U a≤W a := by
  have hs := ShortOuterOne.SameContact.primary_state ha
  have hb := NegativeTwo.source_mem hs
  have hp := ha
  dsimp [U,W]
  exact ⟨by linarith [hb.1],by linarith [hb.2,outer_endpoint_bounds.2.2.2],
    by linarith [ha.1,fine_outer_endpoint_bounds.2],
    by linarith [ha.2,outer_endpoint_bounds.2.1],by linarith [hs.2.1]⟩

lemma primaryNumerator_bounds {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<primaryNumerator a ∧ primaryNumerator a<primaryMass := by
  have hh := primary_chart ha
  dsimp [primaryNumerator,primaryMass,primaryCross]
  norm_num [Q0]
  constructor <;> nlinarith [hh.2.2.1,hh.2.2.2.1]

lemma primary_third_numerator {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    TPrimaryLabel.d3 a*(U a)^5=3*Q0*primaryNumerator a := by
  rw [TPrimaryLabel.third_numerator (primary_domain ha)]
  simp only [TPrimaryLabel,RoleLabel.primary,TLabel,primaryNumerator,primaryMass,primaryCross]
  ring

lemma primary_fourth_numerator {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    TPrimaryLabel.d4 a*(U a)^7=
      3*Q0*(primaryMass*(U a)^2+5*W a*primaryNumerator a) := by
  have hc := UW_circle (primary_domain ha)
  rw [TPrimaryLabel.fourth_numerator (primary_domain ha)]
  simp only [TPrimaryLabel,RoleLabel.primary,TLabel,primaryNumerator,primaryMass,primaryCross]
  linear_combination -3*Q0*(763901/200000)*hc

lemma primary_third_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<TPrimaryLabel.d3 a := by
  have he := primary_third_numerator ha
  have hu := pow_pos (U_positive (primary_domain ha)) 5
  have hn := (primaryNumerator_bounds ha).1
  have hq : 0<Q0 := by norm_num [Q0]
  nlinarith

lemma primary_fourth_growth {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (9/2)*TPrimaryLabel.d3 a<TPrimaryLabel.d4 a := by
  have hu := U_positive (primary_domain ha)
  have hc := primary_chart ha
  have hn := primaryNumerator_bounds ha
  have hfirst := mul_lt_mul_of_pos_right hn.2 (pow_pos hu 2)
  have hgeometry : (25/7)*(U a)^2<5*W a := by
    have hsquare : (U a)^2<(7/5)*U a := by nlinarith [hc.2.1]
    nlinarith [hc.2.2.2.2]
  have hsecond := mul_lt_mul_of_pos_right hgeometry hn.1
  have hpay : (9/2)*primaryNumerator a*(U a)^2<
      primaryMass*(U a)^2+5*W a*primaryNumerator a := by
    have hprod := mul_pos hn.1 (pow_pos hu 2)
    nlinarith
  have hq : 0<3*Q0 := by norm_num [Q0]
  have he3 : (9/2)*TPrimaryLabel.d3 a*(U a)^7=
      3*Q0*((9/2)*primaryNumerator a*(U a)^2) := by
    calc
      (9/2)*TPrimaryLabel.d3 a*(U a)^7=
          (9/2)*(TPrimaryLabel.d3 a*(U a)^5)*(U a)^2 := by ring
      _=3*Q0*((9/2)*primaryNumerator a*(U a)^2) := by
        rw [primary_third_numerator ha]
        ring
  have he4 := primary_fourth_numerator ha
  have hpaid : (9/2)*TPrimaryLabel.d3 a*(U a)^7<TPrimaryLabel.d4 a*(U a)^7 := by
    rw [he3,he4]
    exact mul_lt_mul_of_pos_left hpay hq
  exact lt_of_mul_lt_mul_right hpaid (pow_pos hu 7).le

lemma primary_third_monotone : MonotoneOn TPrimaryLabel.d3 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (TPrimaryLabel.d3_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun a ha => TPrimaryLabel.d3_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun a ha => by
      have h := Ioo_subset_Icc_self ha
      linarith [primary_third_positive h,primary_fourth_growth h])

lemma primary_diagonal_mem : outerDiagonal∈Icc outerDiagonal outerAxial :=
  ⟨le_rfl,by linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]⟩

lemma primary_diagonal_first : TPrimaryLabel.d1 outerDiagonal<(387/500:ℝ) := by
  have he : TPrimaryLabel.d1 outerDiagonal=121161/50000-(5734/3125)*outerDiagonal := by
    dsimp [RoleLabel.d1,TPrimaryLabel,RoleLabel.primary,TLabel]
    rw [ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
    ring
  rw [he]
  linarith [fine_outer_endpoint_bounds.2]

lemma primary_diagonal_second : TPrimaryLabel.d2 outerDiagonal<0 := by
  have hd := primary_diagonal_mem
  have hu := U_positive (primary_domain hd)
  have hc := UW_circle (primary_domain hd)
  have hU : U outerDiagonal=outerDiagonal+1/2 := by
    dsimp [U]
    rw [ShortOuterOne.SameContact.arc_diagonal]
  rw [hU] at hc hu
  have hQ : Q0=2*(outerDiagonal+1/2)^2 := by
    dsimp [W] at hc
    nlinarith
  have hD : ratioD outerDiagonal=2/(outerDiagonal+1/2) := by
    dsimp [ratioD]
    rw [ShortOuterOne.SameContact.arc_diagonal,hQ]
    field_simp [hu.ne']
  have hcoef : 480619/100000-(141641/25000)*outerDiagonal<0 := by
    linarith [fine_outer_endpoint_bounds.2]
  have hid : TPrimaryLabel.d2 outerDiagonal*(outerDiagonal+1/2)=
      480619/100000-(141641/25000)*outerDiagonal := by
    have h2 : 2/(outerDiagonal+1/2)*(outerDiagonal+1/2)=2 := div_mul_cancel₀ 2 hu.ne'
    simp only [RoleLabel.d2,TPrimaryLabel,RoleLabel.primary,TLabel]
    rw [ratio_diagonal,hD]
    linear_combination (-(-91744/100000-242322/100000+95769/100000*outerDiagonal):ℝ)*h2
  nlinarith

lemma primary_diagonal_third : (349/100:ℝ)<TPrimaryLabel.d3 outerDiagonal := by
  have he := primary_third_numerator primary_diagonal_mem
  have hU : U outerDiagonal=outerDiagonal+1/2 := by
    dsimp [U]
    rw [ShortOuterOne.SameContact.arc_diagonal]
  rw [hU] at he
  have hlo : (139921/100000:ℝ)<outerDiagonal+1/2 := by linarith [diagonal_fine.1]
  have hhi : outerDiagonal+1/2<(69961/50000:ℝ) := by linarith [diagonal_fine.2]
  have hp : 0<outerDiagonal+1/2 := by linarith
  have hpow := pow_le_pow_left₀ hp.le hhi.le 5
  dsimp [primaryNumerator,primaryMass,primaryCross,W] at he
  norm_num [Q0] at he hpow
  by_contra hneg
  have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hneg) (pow_pos hp 5).le
  nlinarith

lemma primary_third_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (349/100:ℝ)<TPrimaryLabel.d3 a :=
  primary_diagonal_third.trans_le (primary_third_monotone primary_diagonal_mem ha ha.1)

lemma primary_one_references :
    (15489/20000:ℝ)<TPrimaryLabel.d1 1 ∧ TPrimaryLabel.d1 1<38723/50000 ∧
      (6991/25000:ℝ)<TPrimaryLabel.d2 1 ∧ TPrimaryLabel.d2 1<5593/20000 := by
  have hf := TPrimaryLabel.first_chart_reference (primary_domain primary_one_mem)
    (l := (64529063/50000000:ℝ)) (u := (129058127/100000000:ℝ))
    (dlo := (15489/20000:ℝ)) (dhi := (38723/50000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  have hs := TPrimaryLabel.second_chart_reference (primary_domain primary_one_mem)
    (l := (64529063/50000000:ℝ)) (u := (129058127/100000000:ℝ))
    (dlo := (6991/25000:ℝ)) (dhi := (5593/20000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact ⟨hf.1,hf.2,hs.1,hs.2⟩

lemma primary_first_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (19/25:ℝ)<TPrimaryLabel.d1 a := by
  have ht := curvature_tangent (κ := (349/100:ℝ)) ha primary_one_mem
    (fun t ht => TPrimaryLabel.d1_hasDerivAt (primary_domain ht))
    (fun t ht => TPrimaryLabel.d2_hasDerivAt (primary_domain ht))
    (fun t ht => (primary_third_lower ht).le)
  have hd := primary_one_references
  have hs : (TPrimaryLabel.d2 1)^2<(9/100:ℝ) := by nlinarith [hd.2.2.1,hd.2.2.2]
  nlinarith [sq_nonneg ((349/100)*(a-1)+TPrimaryLabel.d2 1),hd.1]

lemma primary_monotone : MonotoneOn TPrimaryLabel.outer (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (TPrimaryLabel.outer_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun a ha => TPrimaryLabel.outer_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun a ha => by linarith [primary_first_lower (Ioo_subset_Icc_self ha)])

lemma primary_first_exchange {a b : ℝ} (hs : OuterState a b) :
    TPrimaryLabel.d1 a*ratio b=TLabel.d1 b := by
  have ha : 0<a+1/2 := by linarith [hs.1,hs.2.1]
  have hb : 0<b+1/2 := by linarith [hs.1]
  have harc := ShortOuterOne.SameContact.actual_arc hs
  have hx : (a+1/2)/(b+1/2)*((b+1/2)/(a+1/2))=1 := by
    rw [div_mul_div_comm,mul_comm (a+1/2),div_self (mul_ne_zero hb.ne' ha.ne')]
  have hy : (a+1/2)*((b+1/2)/(a+1/2))=b+1/2 := mul_div_cancel₀ _ ha.ne'
  simp only [TPrimaryLabel,RoleLabel.primary,RoleLabel.d1,TLabel,ratio]
  rw [harc.1,harc.2]
  linear_combination (-(-91744/100000-242322/100000+95769/100000*a))*hx+
    (2*(-91744/100000))*hy

lemma primary_first_small {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    TPrimaryLabel.d1 a<(9/10:ℝ) := by
  have hfull : a∈Icc outerDiagonal outerAxial := ⟨ha.1,ha.2.trans primary_one_mem.2⟩
  have hs := ShortOuterOne.SameContact.primary_state hfull
  have hb := NegativeTwo.source_mem hs
  have hcircle := hs.2.2
  have hbhigh : (79/100:ℝ)<arc a := by
    have ha0 : 0≤a+1/2 := by linarith [ha.1,fine_outer_endpoint_bounds.2]
    have ha2 : (a+1/2)^2≤(3/2:ℝ)^2 := by nlinarith [ha.2]
    norm_num [Q0] at hcircle
    nlinarith [hb.1]
  have hr : (43/50:ℝ)<ratio (arc a) := by
    have hrad : arc (arc a)=a := (ShortOuterOne.SameContact.actual_arc hs).1
    dsimp [ratio]
    rw [hrad]
    apply (lt_div_iff₀ (show 0<a+1/2 by linarith [ha.1,fine_outer_endpoint_bounds.2])).2
    nlinarith [ha.2]
  have hT := NegativeTwo.PrimaryDiagonal.target_first_late
    (show arc a∈Icc (3/5) outerDiagonal from ⟨by linarith,hb.2⟩)
  have he := primary_first_exchange hs
  have hm := primary_first_lower hfull
  nlinarith

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
/-!
## The original upper source-primary owner

The original target circle bounds the source-contact speed by a radical
depending only on its physical primary coordinate.  The product of that
radical and the source-label slope increases up to height one, where it
is strictly less than one.  An intermediate-value contact connects the
original weak separator to alignment while retaining the actual target.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def upperSpeed (A B x : ℝ) : ℝ :=
  (1/2-B)*Real.sin x+(A-1/2)*Real.cos x
def upperMass : ℝ := Q0-2*outerAxial
def primarySpeed (a : ℝ) : ℝ := Real.sqrt (upperMass-(a-1/2)^2)
def primaryProduct (a : ℝ) : ℝ := PPrimaryLabel.d1 a*primarySpeed a

lemma outer_sum_lower {A B : ℝ} (ht : OuterState A B) : outerAxial≤A+B := by
  have hz := (ShortOuterOne.SameContact.arc_state outer_zero_mem).2.2
  rw [ShortOuterOne.SameContact.arc_zero] at hz
  have hA0 : 0≤A := ht.1.trans ht.2.1
  have hAB := mul_nonneg hA0 ht.1
  have hs : 0≤A+B := by linarith [ht.1]
  have hax : 0≤outerAxial := by linarith [outer_endpoint_bounds.1]
  by_contra hh
  have hsum : A+B<outerAxial := lt_of_not_ge hh
  have hsq : (A+B)^2<outerAxial^2 := by nlinarith
  nlinarith [ht.2.2]

lemma upperSource_zero (A B : ℝ) : upperSource A B 0=1-B := by
  norm_num [upperSource]
  ring

lemma upperSource_hasDerivAt (A B x : ℝ) :
    HasDerivAt (upperSource A B) (-upperSpeed A B x) x := by
  have hd := (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (A-1/2))
  exact hd.congr_deriv (by dsimp [upperSpeed]; ring)

lemma upperSpeed_positive {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) : 0<upperSpeed A B x := by
  have hh := positive_trig hx
  have hcos0 : 0≤Real.cos x := by linarith [hh.1]
  have hfirst := mul_nonneg
    (show 0≤A-1/2-399/1000 by linarith [(primary_mem ht).1,fine_outer_endpoint_bounds.2]) hcos0
  have hsecond := mul_nonneg
    (show 0≤1/2-B+2/5 by linarith [(source_mem ht).2,outer_endpoint_bounds.2.2.2])
    hh.2.2.1
  dsimp [upperSpeed]
  nlinarith [hh.1,hh.2.2.2.1]

lemma upperSource_antitone {A B : ℝ} (ht : OuterState A B) :
    AntitoneOn (upperSource A B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (upperSource_hasDerivAt A B x).continuousAt.continuousWithinAt)
    (fun x _ => upperSource_hasDerivAt A B x)
    (fun _ hx => neg_nonpos.mpr (upperSpeed_positive ht (Ioo_subset_Icc_self hx)).le)

lemma upperSource_norm {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    (upperSource A B x-1/2)^2+(upperSpeed A B x)^2=Q0-2*(A+B) := by
  dsimp [upperSource,upperSpeed]
  linear_combination ht.2.2+
    ((1/2-B)^2+(A-1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma primarySpeed_data {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    0<primarySpeed a ∧ (primarySpeed a)^2=upperMass-(a-1/2)^2 ∧
      (2089/2500:ℝ)<(primarySpeed a)^2 := by
  have hcenter : 0≤a-1/2 ∧ a-1/2≤1/2 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]
  have hs : (a-1/2)^2≤(1/2:ℝ)^2 := by nlinarith
  have hm : (1357/1250:ℝ)<upperMass := by
    dsimp [upperMass]
    norm_num [Q0]
    linarith [outer_endpoint_bounds.2.1]
  have hpos : 0<upperMass-(a-1/2)^2 := by nlinarith
  have hp : 0<primarySpeed a := Real.sqrt_pos.2 hpos
  have he : (primarySpeed a)^2=upperMass-(a-1/2)^2 := Real.sq_sqrt hpos.le
  exact ⟨hp,he,by nlinarith⟩

lemma primarySpeed_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt primarySpeed (-(a-1/2)/primarySpeed a) a := by
  have hp := primarySpeed_data ha
  have hrad : upperMass-(a-1/2)^2≠0 := by rw [← hp.2.1]; exact (pow_pos hp.1 2).ne'
  have hd := ((((hasDerivAt_id' a).sub_const (1/2)).fun_pow 2).const_sub upperMass).sqrt hrad
  show HasDerivAt (fun y => Real.sqrt (upperMass-(y-1/2)^2)) _ a
  refine hd.congr_deriv ?_
  have hYx : Real.sqrt (upperMass-(a-1/2)^2)=primarySpeed a := rfl
  rw [hYx]
  field_simp
  norm_num
  ring

lemma primaryProduct_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt primaryProduct
      (PPrimaryLabel.d2 a*primarySpeed a-
        PPrimaryLabel.d1 a*(a-1/2)/primarySpeed a) a := by
  have hd := (PPrimaryLabel.d1_hasDerivAt (primary_domain (aligned_domain ha).1)).fun_mul
    (primarySpeed_hasDerivAt ha)
  exact hd.congr_deriv (by ring)

lemma primaryProduct_increases {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    0<PPrimaryLabel.d2 a*primarySpeed a-
      PPrimaryLabel.d1 a*(a-1/2)/primarySpeed a := by
  have hs := primarySpeed_data ha
  have hM := OppositeTwo.M_second_monotone OppositeTwo.primary_diagonal_mem
    (aligned_domain ha).1 ha.1
  have hMlower : (9/10:ℝ)<PPrimaryLabel.d2 a :=
    OppositeTwo.M_second_diagonal.trans_le hM
  have hfirst := OppositeTwo.M_first_monotone (aligned_domain ha).1 primary_one_mem ha.2
  have hfirstupper : PPrimaryLabel.d1 a<(271/250:ℝ) :=
    hfirst.trans_lt OppositeTwo.M_one_first.2
  have hfirstpos : 0<PPrimaryLabel.d1 a := by
    linarith [OppositeTwo.M_first_lower (aligned_domain ha).1]
  have hcenter : 0≤a-1/2 ∧ a-1/2≤1/2 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]
  have hbig := mul_lt_mul hMlower hs.2.2.le (by norm_num : (0:ℝ)<2089/2500)
    (by linarith : 0≤PPrimaryLabel.d2 a)
  have hsmall := mul_le_mul hfirstupper.le hcenter.2 hcenter.1 (by norm_num : (0:ℝ)≤271/250)
  have he : (PPrimaryLabel.d2 a*(primarySpeed a)^2-
      PPrimaryLabel.d1 a*(a-1/2))/primarySpeed a=
      PPrimaryLabel.d2 a*primarySpeed a-
        PPrimaryLabel.d1 a*(a-1/2)/primarySpeed a := by
    field_simp [hs.1.ne']
  rw [←he]
  exact div_pos (by linarith) hs.1

lemma primaryProduct_monotone : MonotoneOn primaryProduct (Icc outerDiagonal 1) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (primaryProduct_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun _ ha => primaryProduct_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun _ ha => (primaryProduct_increases (Ioo_subset_Icc_self ha)).le)

lemma primarySpeed_one : primarySpeed 1=outerAxial-1/2 := by
  have hs := primarySpeed_data (show (1:ℝ)∈Icc outerDiagonal 1 from ⟨primary_one_mem.1,le_rfl⟩)
  have hz := (ShortOuterOne.SameContact.arc_state outer_zero_mem).2.2
  rw [ShortOuterOne.SameContact.arc_zero] at hz
  norm_num [upperMass] at hs
  nlinarith [outer_endpoint_bounds.1]

lemma primaryProduct_one : primaryProduct 1<1 := by
  have hs : 0≤outerAxial-1/2 := by linarith [outer_endpoint_bounds.1]
  have hh := mul_le_mul OppositeTwo.M_one_first.2.le
    (show outerAxial-1/2≤(183/200:ℝ) by linarith [outer_endpoint_bounds.2.1])
    hs (by norm_num : (0:ℝ)≤271/250)
  dsimp [primaryProduct]
  rw [primarySpeed_one]
  norm_num at hh
  linarith

lemma upper_source_speed_paid {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (ha : upperSource A B x∈Icc outerDiagonal 1) :
    PPrimaryLabel.d1 (upperSource A B x)*upperSpeed A B x<1 := by
  have hv := upperSpeed_positive ht hx
  have hs := primarySpeed_data ha
  have hn := upperSource_norm ht x
  have hsum := outer_sum_lower ht
  have hspeed : upperSpeed A B x≤primarySpeed (upperSource A B x) := by
    dsimp [upperMass] at hs
    nlinarith
  have hM : 0≤PPrimaryLabel.d1 (upperSource A B x) := by
    linarith [OppositeTwo.M_first_lower (aligned_domain ha).1]
  have hprod := mul_le_mul_of_nonneg_left hspeed hM
  have hmono := primaryProduct_monotone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2
  have hend := primaryProduct_one
  dsimp [primaryProduct] at hmono hend
  linarith

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases halign : 1≤a+B
  · have hh := original_aligned hs ht halign
    dsimp [value] at *
    linarith [hx.1]
  · have hcut := upper_source_cut hx hm
    have hc : Continuous (fun t => -upperSource A B t) :=
      continuous_iff_continuousAt.2 fun t => (upperSource_hasDerivAt A B t).neg.continuousAt
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc hx.1 hc.continuousOn
      (show -a∈Icc (-upperSource A B 0) (-upperSource A B x) by
        rw [upperSource_zero]
        constructor <;> linarith)
    have he : upperSource A B y=a := by linarith
    have hycap : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hx.2⟩
    have hstart : 1-B∈Icc outerDiagonal 1 := by
      constructor <;> linarith [(primary_mem hs).1,ht.1]
    have hdom {t : ℝ} (htime : t∈Icc 0 y) :
        t∈Icc 0 (7/10) ∧ upperSource A B t∈Icc outerDiagonal 1 := by
      have htcap : t∈Icc 0 (7/10) := ⟨htime.1,htime.2.trans hycap.2⟩
      have hlo := upperSource_antitone ht htcap hycap htime.2
      have hhi := upperSource_antitone ht (by norm_num) htcap htime.1
      rw [he] at hlo
      rw [upperSource_zero] at hhi
      exact ⟨htcap,⟨(primary_mem hs).1.trans hlo,hhi.trans hstart.2⟩⟩
    have hd {t : ℝ} (htime : t∈Icc 0 y) :
        HasDerivAt (fun s => s+PPrimaryLabel.outer (upperSource A B s))
          (1-PPrimaryLabel.d1 (upperSource A B t)*upperSpeed A B t) t := by
      have hh := (PPrimaryLabel.outer_hasDerivAt
        (primary_domain (aligned_domain (hdom htime).2).1)).comp t
          (upperSource_hasDerivAt A B t)
      exact ((hasDerivAt_id' t).fun_add hh).congr_deriv (by ring)
    have hmono : MonotoneOn (fun s => s+PPrimaryLabel.outer (upperSource A B s))
        (Icc 0 y) := monoOn_of_hasDeriv_nonneg
      (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
      (fun t ht' => hd (Ioo_subset_Icc_self ht'))
      (fun t ht' => by
        have hh := hdom (Ioo_subset_Icc_self ht')
        linarith [upper_source_speed_paid ht hh.1 hh.2])
    have hstep := hmono ⟨le_rfl,hy.1⟩ ⟨hy.1,le_rfl⟩ hy.1
    dsimp only at hstep
    rw [upperSource_zero,he] at hstep
    have hbase := aligned_lower hstart
    have hactual : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
    dsimp [aligned,value] at *
    rw [hactual] at hstep
    have harg : 1-(1-B)=B := by ring
    rw [harg] at hbase
    linarith [hy.2]

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def aligned (a : ℝ) : ℝ := Real.pi/2+TPrimaryLabel.outer a+K (1-a)

lemma aligned_reference : (93/100:ℝ)<Real.pi/2+TPrimaryLabel.outer 1+K 0 := by
  have hs := ShortOuterOne.SameContact.primary_state primary_one_mem
  have hb := NegativeTwo.source_mem hs
  have hc := hs.2.2
  have hbox : arc 1∈Icc (1581/2000) (791/1000) := by
    norm_num [Q0] at hc
    constructor <;> nlinarith [hb.1]
  have hU : U (arc 1)∈Icc (3/2) (3/2) := by
    have he := (ShortOuterOne.SameContact.actual_arc hs).1
    dsimp [U]
    rw [he]
    norm_num
  have ht := FixedReference.target hb hbox hU (by norm_num) (by norm_num)
  have hT : T (arc 1)<(61/100:ℝ) := by
    norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
      FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at ht
    linarith
  have he := primary_actual hs
  rw [he]
  linarith [pi_hand_enclosure.1,K_zero_bounds.1]

lemma aligned_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt aligned (TPrimaryLabel.d1 a-KLabel.d1 (1-a)) a := by
  have hh := NegativeTwo.aligned_domain ha
  have ht := (KLabel.outer_hasDerivAt (outer_domain hh.2.1)).comp a
    ((hasDerivAt_id' a).const_sub 1)
  have hd := ((TPrimaryLabel.outer_hasDerivAt (primary_domain hh.1)).const_add
    (Real.pi/2)).add ht
  exact hd.congr_deriv (by ring)

lemma aligned_antitone : AntitoneOn aligned (Icc outerDiagonal 1) :=
  antiOn_of_hasDeriv_nonpos
    (fun a ha => (aligned_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun a ha => aligned_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun a ha => by
      have h := Ioo_subset_Icc_self ha
      linarith [primary_first_small h,K_first_small (NegativeTwo.aligned_domain h).2.2])

lemma aligned_lower {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    (93/100:ℝ)<aligned a := by
  have hmono := aligned_antitone ha (show (1:ℝ)∈Icc outerDiagonal 1 from
    ⟨primary_one_mem.1,le_rfl⟩) ha.2
  have hbase := aligned_reference
  unfold aligned at hmono ⊢
  rw [sub_self] at hmono
  linarith

theorem original_aligned {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (halign : 1≤a+B) :
    (93/100:ℝ)<value b B (Real.pi/2) := by
  have ha := NegativeTwo.primary_mem hs
  have hB := NegativeTwo.source_mem ht
  have hactual := primary_actual hs
  rcases le_total 1 a with h | h
  · have hM := primary_monotone primary_one_mem ha h
    have hK := K_lower hB
    rw [hactual] at hM
    dsimp [value]
    linarith [aligned_reference]
  · have hdom := NegativeTwo.aligned_domain (show a∈Icc outerDiagonal 1 from ⟨ha.1,h⟩)
    have hK := K_monotone hdom.2.1 hB (by linarith)
    have hbase := aligned_lower (show a∈Icc outerDiagonal 1 from ⟨ha.1,h⟩)
    dsimp [aligned] at hbase
    rw [hactual] at hbase
    dsimp [value]
    linarith

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end
