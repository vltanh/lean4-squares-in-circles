module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoData
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoPrimaryLabels

/-!
# The complete aligned negative-quarter minimum

The third derivative of the aligned cost is positive throughout its
physical interval.  Its second derivative is therefore bounded above by
its negative right endpoint; its first derivative is bounded below by
its positive right endpoint.  The minimum is the original diagonal
source with target coordinate `1-d`.  No curvature partition is used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo

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
    (fun a ha => (PPrimaryLabel.d3_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun a ha => PPrimaryLabel.d3_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun a ha => (primary_fourth_positive (Ioo_subset_Icc_self ha)).le)

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
    (fun a ha => (alignedDD_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun a ha => alignedDD_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun a ha => (aligned_third_positive (Ioo_subset_Icc_self ha)).le)

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

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo
