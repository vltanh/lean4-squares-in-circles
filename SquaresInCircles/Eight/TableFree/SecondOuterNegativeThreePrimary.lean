module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeData
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoPrimaryBound

/-!
# The transformed source label for negative edge three

On the primary-coordinate circle chart, the source label has positive
third derivative and its fourth derivative exceeds `9/2` times its
third derivative.  One fixed reference at primary coordinate one gives
the global slope floor `.76` by a tangent parabola.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

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
  have hh := TPrimaryLabel.third_numerator (primary_domain ha)
  norm_num [TPrimaryLabel,RoleLabel.primary,TLabel] at hh
  dsimp [primaryNumerator,primaryMass,primaryCross]
  nlinarith

lemma primary_fourth_numerator {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    TPrimaryLabel.d4 a*(U a)^7=
      3*Q0*(primaryMass*(U a)^2+5*W a*primaryNumerator a) := by
  have hh := TPrimaryLabel.fourth_numerator (primary_domain ha)
  have hc := UW_circle (primary_domain ha)
  norm_num [TPrimaryLabel,RoleLabel.primary,TLabel] at hh
  dsimp [primaryNumerator,primaryMass,primaryCross]
  linear_combination hh-3*Q0*(763901/200000)*hc

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
  exact (mul_lt_mul_right (pow_pos hu 7)).mp hpaid

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
    ring
  have hcoef : 480619/100000-(141641/25000)*outerDiagonal<0 := by
    linarith [fine_outer_endpoint_bounds.2]
  have hid : TPrimaryLabel.d2 outerDiagonal*(outerDiagonal+1/2)=
      480619/100000-(141641/25000)*outerDiagonal := by
    dsimp [RoleLabel.d2,TPrimaryLabel,RoleLabel.primary,TLabel]
    rw [ratio_diagonal,hD]
    field_simp [hu.ne']
    ring
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
  dsimp [TPrimaryLabel,RoleLabel.primary,RoleLabel.d1,TLabel,ratio]
  rw [harc.1,harc.2]
  field_simp [ha.ne',hb.ne']
  ring

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

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree
