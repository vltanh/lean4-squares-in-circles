module

public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeZeroSlope
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyCut
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeSourceSlope

/-!
# Eight squares: the original positive-to-negative quarter pair in a physical cycle

Reflected reversal preserves this sign pair and exchanges roles three and five
(`original_reflected`, `original_role`). The original selected weak owner and both original
circle coordinates are kept in the conclusion on the cycle (`actual`).
-/

section
/-!
## Two whole-arc chords for positive-to-negative outer edge three

The global source chord has slope `0.736` and the global target
chord has slope `0.7`.  Their common slope `0.7` already leaves a
strict reserve, so no short-coordinate derivative subdivisions are
needed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveNegativeThree

open CommonQuarter CorePairGeometry Arithmetic

def value (b B φ : ℝ) : ℝ := φ+V b+K B
def base : ℝ := V 0+K 0
def Early (φ : ℝ) : Prop := φ∈Icc PositiveThree.lowerAngle (943/1000)
def scalar (φ : ℝ) : ℝ :=
  φ+base+7/20+(7/20)*Real.cos φ-((7/10)*outerAxial-7/20)*Real.sin φ
def scalarFirst (φ : ℝ) : ℝ :=
  1-(7/20)*Real.sin φ-((7/10)*outerAxial-7/20)*Real.cos φ

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer true false a b A B φ=value b B φ := by
  unfold value
  rw [show V b=VLabel.eval a b from VLabel.outer_actual hs,
    show K B=KLabel.eval A B from KLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,VLabel,KLabel,RoleLabel.eval]
  ring

lemma base_lower : (-(4439/100000:ℝ))<base := by
  dsimp [base]
  linarith [V_zero_bounds.1,K_zero_bounds.1]

lemma chord {b B φ : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    φ+base+(7/10)*(b+B)≤value b B φ := by
  have hv := V_chord hb
  have hk := K_chord hB
  dsimp [value,base]
  linarith [hb.1]

lemma late_value {b B φ : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hφ : (943/1000:ℝ)≤φ) : (4493/5000:ℝ)<value b B φ := by
  have hh := chord (φ := φ) hb hB
  nlinarith [base_lower,hb.1,hB.1]

lemma large_sum {b B φ : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hφ : PositiveThree.lowerAngle≤φ) (hsum : (1/5:ℝ)≤b+B) :
    (483/500:ℝ)<value b B φ := by
  have hh := chord (φ := φ) hb hB
  dsimp [PositiveThree.lowerAngle] at hφ
  linarith [base_lower,pi_hand_enclosure.1]

lemma early_lower {φ : ℝ} (hφ : Early φ) : PositiveThree.Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma right_lower : PositiveThree.Lower (943/1000:ℝ) := by
  constructor
  · dsimp [PositiveThree.lowerAngle]
    linarith [pi_hand_enclosure.2]
  · linarith [pi_hand_enclosure.1]

lemma early_cos {φ : ℝ} (hφ : Early φ) : (587/1000:ℝ)<Real.cos φ := by
  have ht := PointProducts.trig (show (0:ℝ)≤943/1000 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  have href : (587/1000:ℝ)<Real.cos (943/1000) := by linarith [ht.2.1]
  exact href.trans_le (PositiveThree.lower_cos_antitone (early_lower hφ) right_lower hφ.2)

lemma small_primary {a b : ℝ} (hs : OuterState a b) (hb : b≤1/5) : (27/20:ℝ)<a := by
  have ha := NegativeTwo.primary_mem hs
  have hcircle := hs.2.2
  have hsquare : (b+1/2)^2≤(7/10:ℝ)^2 := by nlinarith [hs.1]
  norm_num [Q0] at hcircle
  nlinarith [ha.1,fine_outer_endpoint_bounds.2]

lemma scalar_hasDerivAt (φ : ℝ) : HasDerivAt scalar (scalarFirst φ) φ := by
  exact (((((hasDerivAt_id φ).add_const base).add_const (7/20)).add
    ((Real.hasDerivAt_cos φ).const_mul (7/20))).sub
      ((Real.hasDerivAt_sin φ).const_mul ((7/10)*outerAxial-7/20))).congr_deriv
    (by dsimp only [scalarFirst]; ring)

lemma scalarFirst_positive (φ : ℝ) : 0<scalarFirst φ := by
  have hcoef : 0≤(7/10)*outerAxial-7/20 := by linarith [outer_endpoint_bounds.1]
  have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one φ) (by norm_num : (0:ℝ)≤7/20)
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one φ) hcoef
  dsimp [scalarFirst]
  nlinarith [outer_endpoint_bounds.2.1]

lemma scalar_monotone : MonotoneOn scalar (Icc PositiveThree.lowerAngle (943/1000)) :=
  monoOn_of_hasDeriv_nonneg
    (fun φ _ => (scalar_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => scalar_hasDerivAt φ)
    (fun φ _ => (scalarFirst_positive φ).le)

lemma scalar_left : (9119/10000:ℝ)<scalar PositiveThree.lowerAngle := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  have hs : (64421/100000:ℝ)<Real.sin (7/10) := by linarith [ht.1.1]
  have hc : Real.cos (7/10)<(15297/20000:ℝ) := by linarith [ht.2.2]
  have hcoef : 0≤(7/10)*outerAxial-7/20 := by linarith [outer_endpoint_bounds.1]
  have hcap : (7/10)*outerAxial-7/20<(1281/2000:ℝ) := by
    linarith [outer_endpoint_bounds.2.1]
  have hcos0 : 0≤Real.cos (7/10) := by linarith [ht.2.1]
  have hp := mul_le_mul hcap.le hc.le hcos0 (by norm_num : (0:ℝ)≤1281/2000)
  simp only [scalar,PositiveThree.lowerAngle,Real.sin_sub,Real.cos_sub,
    Real.sin_pi_div_two,Real.cos_pi_div_two,zero_mul,one_mul,sub_zero,zero_add]
  nlinarith [base_lower,pi_hand_enclosure.1]

lemma scalar_lower {φ : ℝ} (hφ : Early φ) : (9119/10000:ℝ)<scalar φ :=
  scalar_left.trans_le
    (scalar_monotone ⟨le_rfl,right_lower.1⟩ hφ hφ.1)

end SquaresInCircles.Eight.SecondWord.PositiveNegativeThree
end
end
end

section
/-!
## Every original owner for positive-to-negative outer edge three

The two secondary owners give a lower bound for the sum of the
transverse coordinates.  If that sum is small, either primary owner
contradicts its original weak separator.  The two global circle
chords and one increasing scalar cover the entire quarter interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveNegativeThree

open CommonQuarter CorePairGeometry Arithmetic

lemma secondary_sum {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : Early φ) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    pairWidth φ-outerAxial*Real.sin φ≤b+B := by
  have htr := PositiveThree.lower_trig (early_lower hφ)
  have hs0 : 0≤Real.sin φ := by linarith [htr.1]
  have hc1 : Real.cos φ≤1 := by linarith [htr.2.2.2.1]
  have ha := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem hs).2 hs0
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).2 hs0
  have hb := mul_le_mul_of_nonneg_left hc1 hs.1
  have hB := mul_le_mul_of_nonneg_left hc1 ht.1
  rcases hj with rfl | rfl <;> norm_num [Eight.forwardMargin] at hm <;> linarith

lemma secondary_value {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : Early φ) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (9119/10000:ℝ)<value b B φ := by
  have hsum := secondary_sum hs ht hφ j hj hm
  rw [PositiveThree.lower_width (early_lower hφ)] at hsum
  have hh := chord (φ := φ) (NegativeTwo.source_mem hs) (NegativeTwo.source_mem ht)
  have hcost : scalar φ≤value b B φ := by
    dsimp [scalar]
    nlinarith
  exact (scalar_lower hφ).trans_le hcost

lemma primary_impossible {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : Early φ) (hsum : b+B≤1/5) (j : Fin 4) (hj : j=1 ∨ j=3)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) : False := by
  have htr := PositiveThree.lower_trig (early_lower hφ)
  have hw : 1≤pairWidth φ := by
    rw [PositiveThree.lower_width (early_lower hφ)]
    linarith [htr.2.2.2.2]
  have hb : b≤1/5 := by linarith [ht.1]
  have hB : B≤1/5 := by linarith [hs.1]
  have ha := small_primary hs hb
  have hA := small_primary ht hB
  have hc := early_cos hφ
  have hp := mul_lt_mul ha hc.le (by norm_num : (0:ℝ)<587/1000)
    (show 0≤a by linarith [ha])
  have hP := mul_lt_mul hA hc.le (by norm_num : (0:ℝ)<587/1000)
    (show 0≤A by linarith [hA])
  have hbSin := mul_le_mul_of_nonneg_left htr.2.1 hs.1
  have hBSin := mul_le_mul_of_nonneg_left htr.2.1 ht.1
  have hau : a<(283/200:ℝ) := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have hAu : A<(283/200:ℝ) := (NegativeTwo.primary_mem ht).2.trans_lt outer_endpoint_bounds.2.1
  rcases hj with rfl | rfl <;> norm_num [Eight.forwardMargin] at hm <;> linarith

theorem original_at_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (4493/5000:ℝ)<value b B φ := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  by_cases hlate : (943/1000:ℝ)≤φ
  · exact late_value hb hB hlate
  · have hangle : PositiveThree.lowerAngle≤φ := by
      have hh := (abs_le.mp hφ).1
      dsimp [PositiveThree.lowerAngle]
      linarith
    have hearly : Early φ := ⟨hangle,le_of_not_ge hlate⟩
    by_cases hsum : (1/5:ℝ)≤b+B
    · linarith [large_sum hb hB hangle hsum]
    · have hsmall : b+B≤1/5 := le_of_not_ge hsum
      fin_cases j
      · linarith [secondary_value hs ht hearly 0 (Or.inl rfl) hm]
      · exact (primary_impossible hs ht hearly hsmall 1 (Or.inl rfl) hm).elim
      · linarith [secondary_value hs ht hearly 2 (Or.inr rfl) hm]
      · exact (primary_impossible hs ht hearly hsmall 3 (Or.inr rfl) hm).elim

end SquaresInCircles.Eight.SecondWord.PositiveNegativeThree
end
end
end

section
/-!
## Order on the actual first-contact circle arc

The contact source coordinate increases by at least `0.19` times
the target-coordinate increase.  This quantitative order statement
retains equality and lets an original weak separator determine an
actual closed contact interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.FirstContact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

lemma sourceFirst_lower {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    (19/100:ℝ)<sourceFirst B φ := by
  have ht := lower_trig hφ
  have hr := (outer_ratio_bounds hB).1
  have hm := mul_lt_mul hr ht.1.le
    (by norm_num : (0:ℝ)<19121/25000)
    (by linarith [hr] : 0≤ratio B)
  dsimp [sourceFirst]
  nlinarith [ht.2.2.1]

lemma source_shift_monotone {φ : ℝ} (hφ : Lower φ) :
    MonotoneOn (fun B => source B φ-(19/100)*B) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => ((source_hasDerivAt hB φ).sub
      ((hasDerivAt_id B).const_mul (19/100))).continuousAt.continuousWithinAt)
    (fun B hB => (source_hasDerivAt (Ioo_subset_Icc_self hB) φ).sub
      ((hasDerivAt_id B).const_mul (19/100)))
    (fun B hB => by linarith [sourceFirst_lower (Ioo_subset_Icc_self hB) hφ])

theorem source_order {B C φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hC : C∈Icc 0 outerDiagonal) (hφ : Lower φ) (h : source B φ≤ source C φ) : B≤C := by
  rcases le_total B C with horder | horder
  · exact horder
  · have hh := source_shift_monotone hφ hC hB horder
    linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.FirstContact
end
end
end

section
/-!
## The full aligned positive edge-three minimum

Below target primary coordinate one, the first contact has a concave
first derivative which is positive at its zero-source endpoint.  Its
minimum is therefore one of the two actual physical endpoints.  Above
primary coordinate one, ordinary label monotonicity gives the zero
endpoint directly.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma quarter_lower : Lower (Real.pi/2) := by
  show lowerAngle≤Real.pi/2 ∧ Real.pi/2≤Real.pi/2
  exact ⟨by dsimp only [lowerAngle]; linarith,le_rfl⟩

lemma aligned_contact_domain {B : ℝ} (hB : B∈Icc zeroTarget outerDiagonal) :
    FirstContact.Domain B (Real.pi/2) := by
  have hBout : B∈Icc 0 outerDiagonal := ⟨zeroTarget_mem.1.trans hB.1,hB.2⟩
  have hu := ShortOuterOne.SameContact.arc_antitone (outer_domain zeroTarget_mem)
    (outer_domain hBout) hB.1
  rw [zeroTarget_arc] at hu
  have hl := (CommonQuarter.outer_bounds (ShortOuterOne.SameContact.arc_state hBout)).1
  refine ⟨hBout,?_,quarter_lower⟩
  rw [FirstContact.source_at_quarter]
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma aligned_contact_first : 0<FirstContact.first zeroTarget (Real.pi/2) := by
  have he : FirstContact.source zeroTarget (Real.pi/2)=0 := by
    rw [FirstContact.source_at_quarter,zeroTarget_arc]
    norm_num
  have hp := mul_lt_mul V_zero_first_lower zeroTarget_ratio.le
    (by norm_num : (0:ℝ)<43/50)
    (by linarith [V_zero_first_lower] : 0≤VLabel.d1 0)
  dsimp [FirstContact.first]
  rw [he]
  simp only [FirstContact.sourceFirst,Real.sin_pi_div_two,Real.cos_pi_div_two,
    mul_one,add_zero]
  norm_num at hp
  linarith [zeroTarget_labels.2.1]

theorem aligned_contact_lower {B : ℝ} (hB : B∈Icc zeroTarget outerDiagonal) :
    (44889/50000:ℝ)<FirstContact.cost B (Real.pi/2) := by
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos hB
    (fun t ht => FirstContact.cost_hasDerivAt (aligned_contact_domain ht))
    (fun t ht => FirstContact.first_hasDerivAt (aligned_contact_domain ht))
    (fun t ht => FirstContact.second_hasDerivAt (aligned_contact_domain ht))
    (fun t ht => (FirstContact.third_negative (aligned_contact_domain ht)).le)
    aligned_contact_first
  have hz : (44889/50000:ℝ)<FirstContact.cost zeroTarget (Real.pi/2) := by
    have he : FirstContact.source zeroTarget (Real.pi/2)=0 := by
      rw [FirstContact.source_at_quarter,zeroTarget_arc]
      norm_num
    dsimp [FirstContact.cost]
    rw [he]
    have hs := zero_aligned_value
    dsimp [value] at hs
    linarith
  have hd : (44889/50000:ℝ)<FirstContact.cost outerDiagonal (Real.pi/2) := by
    have he : FirstContact.source outerDiagonal (Real.pi/2)=alignedSource := by
      rw [FirstContact.source_at_quarter,ShortOuterOne.SameContact.arc_diagonal]
      rfl
    dsimp [FirstContact.cost]
    rw [he]
    exact diagonal_aligned_value
  exact (lt_min hz hd).trans_le hh

lemma aligned_inactive_target {A B : ℝ} (ht : OuterState A B) (hA : 1≤A) :
    B≤zeroTarget := by
  have hh := ShortOuterOne.SameContact.arc_antitone (primary_domain primary_one_mem)
    (primary_domain (NegativeTwo.primary_mem ht)) hA
  rw [(ShortOuterOne.SameContact.actual_arc ht).2] at hh
  exact hh

lemma aligned_active_target {A B : ℝ} (ht : OuterState A B) (hA : A≤1) :
    zeroTarget≤B := by
  have hh := ShortOuterOne.SameContact.arc_antitone
    (primary_domain (NegativeTwo.primary_mem ht)) (primary_domain primary_one_mem) hA
  rw [(ShortOuterOne.SameContact.actual_arc ht).2] at hh
  exact hh

theorem original_aligned {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (halign : 1≤b+A) :
    (44889/50000:ℝ)<value b B (Real.pi/2) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  by_cases hA : 1≤A
  · have htarget := L_monotone hB zeroTarget_mem (aligned_inactive_target ht hA)
    have hsource := V_monotone outer_zero_mem hb hb.1
    have hbase := zero_aligned_value
    dsimp [value] at *
    linarith
  · have hinterval : B∈Icc zeroTarget outerDiagonal :=
      ⟨aligned_active_target ht (by linarith),hB.2⟩
    have hdom := aligned_contact_domain hinterval
    have he : FirstContact.source B (Real.pi/2)=1-A := by
      rw [FirstContact.source_at_quarter,(ShortOuterOne.SameContact.actual_arc ht).1]
    have hsource := V_monotone hdom.2.1 hb
      (show FirstContact.source B (Real.pi/2)≤b by rw [he]; linarith)
    have hbase := aligned_contact_lower hinterval
    dsimp [FirstContact.cost,value] at *
    linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end

section
/-!
## The entire original target-diagonal boundary

After the actual diagonal crossing, the source coordinate decreases
to the aligned endpoint.  Its speed is bounded away from zero and
its acceleration is at most `0.4`.  The original source-label
curvature then makes the full cost concave.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalTarget

open CommonQuarter CorePairGeometry Arithmetic
open DiagonalContact (height heightFirst heightSecond)

def Domain (φ : ℝ) : Prop := Lower φ ∧ height φ≤outerDiagonal
def cost (φ : ℝ) : ℝ := value (height φ) outerDiagonal φ
def first (φ : ℝ) : ℝ := 1+VLabel.d1 (height φ)*heightFirst φ
def second (φ : ℝ) : ℝ :=
  VLabel.d2 (height φ)*(heightFirst φ)^2+VLabel.d1 (height φ)*heightSecond φ

lemma height_quarter : height (Real.pi/2)=alignedSource := by
  rw [height,FirstContact.source_at_quarter,ShortOuterOne.SameContact.arc_diagonal]
  rfl

lemma source_data {φ : ℝ} (hφ : Domain φ) : height φ∈Icc (1/10:ℝ) outerDiagonal := by
  have hh := DiagonalContact.height_antitone hφ.1 quarter_lower hφ.1.2
  rw [height_quarter] at hh
  dsimp [alignedSource] at hh
  exact ⟨by linarith [outer_endpoint_bounds.2.2.2],hφ.2⟩

lemma source_mem {φ : ℝ} (hφ : Domain φ) : height φ∈Icc 0 outerDiagonal :=
  ⟨by linarith [(source_data hφ).1],hφ.2⟩

lemma domain_after {φ e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200))
    (hc : height e=outerDiagonal) (hφ : φ∈Icc e (Real.pi/2)) : Domain φ := by
  have hl : Lower φ := ⟨(DiagonalContact.join_lower he).1.trans hφ.1,hφ.2⟩
  have hh := DiagonalContact.height_antitone (DiagonalContact.join_lower he) hl hφ.1
  rw [hc] at hh
  exact ⟨hl,hh⟩

lemma after_end {φ e : ℝ} (hφ : Domain φ)
    (he : e∈Icc (507/500:ℝ) (203/200)) (hc : height e=outerDiagonal) : e≤φ :=
  DiagonalContact.after_join hφ.1 he hc hφ.2

lemma angle_lower {φ : ℝ} (hφ : Domain φ) : (507/500:ℝ)≤φ := by
  obtain ⟨e,he,hc⟩ := DiagonalContact.exists_join
  exact he.1.trans (after_end hφ he hc)

lemma source_speed {φ : ℝ} (hφ : Domain φ) :
    heightFirst φ< -(1399/1000:ℝ)*(106/125) ∧ heightSecond φ≤2/5 := by
  have ht := lower_trig hφ.1
  have href : Lower (507/500:ℝ) := DiagonalContact.join_lower ⟨le_rfl,by norm_num⟩
  have hs := DiagonalContact.lower_join_sine.trans_le
    (lower_sin_monotone href hφ.1 (angle_lower hφ))
  have hleft := mul_nonpos_of_nonpos_of_nonneg
    (show 1/2-outerDiagonal≤0 by linarith [fine_outer_endpoint_bounds.2]) ht.2.2.1
  have hright := mul_lt_mul
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    hs.le (by norm_num : (0:ℝ)<106/125)
    (show 0≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
  constructor
  · dsimp [heightFirst]
    nlinarith
  · dsimp [heightSecond]
    linarith [(source_data hφ).1]

lemma cost_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt cost (first φ) φ := by
  have hd := ((hasDerivAt_id φ).add
    ((VLabel.outer_hasDerivAt (outer_domain (source_mem hφ))).comp φ
      (DiagonalContact.height_hasDerivAt φ))).sub_const (L outerDiagonal)
  convert hd using 1
  · funext t
    simp only [cost,value,V,Pi.add_apply,Function.comp_apply,id]
  · simp only [first]

lemma first_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt first (second φ) φ := by
  have hd := (((VLabel.d1_hasDerivAt (outer_domain (source_mem hφ))).comp φ
    (DiagonalContact.height_hasDerivAt φ)).mul
      (DiagonalContact.heightFirst_hasDerivAt φ)).const_add 1
  convert hd using 1
  · funext t
    simp only [first,Pi.mul_apply,Function.comp_apply]
  · simp only [second,Function.comp_apply]
    ring

lemma second_negative {φ : ℝ} (hφ : Domain φ) : second φ<0 := by
  have hs := source_speed hφ
  have hV := V_first_bounds (source_mem hφ)
  have hV0 : 0≤VLabel.d1 (height φ) := by linarith [hV.1]
  have hsq : ((1399/1000:ℝ)*(106/125))^2<(heightFirst φ)^2 := by
    nlinarith [hs.1]
  have hsqpos : 0<(heightFirst φ)^2 := by nlinarith
  have hfirst := mul_lt_mul_of_pos_right (V_second_late (source_data hφ)) hsqpos
  have hlast1 := mul_le_mul_of_nonneg_left hs.2 hV0
  have hlast2 := mul_lt_mul_of_pos_right hV.2 (by norm_num : (0:ℝ)<2/5)
  dsimp [second]
  nlinarith

theorem cost_lower {φ : ℝ} (hφ : Domain φ) : (44889/50000:ℝ)<cost φ := by
  obtain ⟨e,he,hc⟩ := DiagonalContact.exists_join
  have hleft : (44889/50000:ℝ)<cost e := by
    dsimp [cost]
    rw [hc]
    exact DiagonalContact.corner_value he
  have hright : (44889/50000:ℝ)<cost (Real.pi/2) := by
    rw [cost,height_quarter]
    exact diagonal_aligned_value
  have hconcave : ConcaveOn ℝ (Icc e (Real.pi/2)) cost :=
    concave_of_deriv2
      (fun t ht => cost_hasDerivAt (domain_after he hc ht))
      (fun t ht => first_hasDerivAt (domain_after he hc ht))
      (fun t ht => (second_negative (domain_after he hc ht)).le)
  exact concave_gt_of_endpoints hconcave ⟨after_end hφ he hc,hφ.1.2⟩ hleft hright

theorem original_contact {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : Lower φ) (hc : FirstContact.source outerDiagonal φ=b) :
    (44889/50000:ℝ)<value b outerDiagonal φ := by
  have hh : height φ=b := hc
  have hd : Domain φ := ⟨hφ,by rw [hh]; exact hb.2⟩
  simpa only [cost,hh] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalTarget
end
end
end

section
/-!
## Every original first owner on the early positive-quarter arc

The actual weak separator either reaches the short-source support,
or determines a closed physical contact interval.  Its left endpoint
is the actual `0.35` cut; its right endpoint is the target diagonal
or the first source-diagonal contact, constructed by IVT.  The
concave derivative reduces to these proved geometric endpoints.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic

lemma short_of_cut {b B φ : ℝ} (hb : b∈Icc (0:ℝ) (7/20))
    (hB : B∈Icc 0 outerDiagonal) (hφ : φ∈Icc lowerAngle (13/10))
    (hc : FirstContact.source B φ≤b) : (451/500:ℝ)<value b B φ := by
  have hminor := (minorant_lower hφ).trans_le (minorant_le_support hB hφ)
  have hV := V_chord_short hb
  have hz := V_zero_bounds.1
  have hcost : support B φ<value b B φ := by
    dsimp [FirstContact.source,support,value,g] at *
    linarith
  exact hminor.trans hcost

lemma cut_source {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    FirstContact.source (SourceCurve.target EarlyCut.parameter φ) φ=7/20 := by
  have hh := SourceCurve.contact (EarlyCut.domain hφ) (EarlyCut.target_mem hφ)
  norm_num [EarlyCut.parameter] at hh
  exact hh

lemma cut_value {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    (451/500:ℝ)<FirstContact.cost (SourceCurve.target EarlyCut.parameter φ) φ := by
  have hh := short_of_cut (show (7/20:ℝ)∈Icc 0 (7/20) by norm_num)
    (EarlyCut.target_mem hφ) hφ (cut_source hφ).le
  simpa only [FirstContact.cost,value,cut_source hφ] using hh

lemma physical_cap {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hc : FirstContact.source B φ≤outerDiagonal) :
    ∃ e : ℝ, e∈Icc B outerDiagonal ∧ FirstContact.source e φ≤outerDiagonal ∧
      (e=outerDiagonal ∨ FirstContact.source e φ=outerDiagonal) := by
  by_cases hd : FirstContact.source outerDiagonal φ≤outerDiagonal
  · exact ⟨outerDiagonal,⟨hB.2,le_rfl⟩,hd,Or.inl rfl⟩
  · have hcont : ContinuousOn (fun t => FirstContact.source t φ) (Icc B outerDiagonal) := by
      intro t ht
      exact (FirstContact.source_hasDerivAt ⟨hB.1.trans ht.1,ht.2⟩ φ).continuousAt.continuousWithinAt
    obtain ⟨e,he,heq⟩ := intermediate_value_Icc hB.2 hcont
      (show outerDiagonal∈Icc (FirstContact.source B φ)
        (FirstContact.source outerDiagonal φ) from ⟨hc,le_of_not_ge hd⟩)
    exact ⟨e,he,heq.le,Or.inr heq⟩

theorem active_contact {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hφ : φ∈Icc lowerAngle (13/10))
    (hsource : FirstContact.source B φ∈Icc (7/20:ℝ) outerDiagonal) :
    (44889/50000:ℝ)<FirstContact.cost B φ := by
  let b0 := SourceCurve.target EarlyCut.parameter φ
  have hb0 : b0∈Icc 0 outerDiagonal := EarlyCut.target_mem hφ
  have hcut : FirstContact.source b0 φ=7/20 := cut_source hφ
  have hB0 : b0≤B := FirstContact.source_order hb0 hB (early_lower hφ)
    (by rw [hcut]; exact hsource.1)
  obtain ⟨e,he,hecap,hend⟩ := physical_cap hB hsource.2
  have heout : e∈Icc 0 outerDiagonal := ⟨hB.1.trans he.1,he.2⟩
  have hdom : ∀ t∈Icc b0 e, FirstContact.Domain t φ := by
    intro t ht
    have htout : t∈Icc 0 outerDiagonal := ⟨hb0.1.trans ht.1,ht.2.trans he.2⟩
    have hlo := FirstContact.source_monotone (early_lower hφ) hb0 htout ht.1
    have hhi := FirstContact.source_monotone (early_lower hφ) htout heout ht.2
    dsimp only at hlo hhi
    rw [hcut] at hlo
    exact ⟨htout,⟨by linarith,hhi.trans hecap⟩,early_lower hφ⟩
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (show B∈Icc b0 e from ⟨hB0,he.1⟩)
    (fun t ht => FirstContact.cost_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.first_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.second_hasDerivAt (hdom t ht))
    (fun t ht => (FirstContact.third_negative (hdom t ht)).le)
    (EarlyCut.original_derivative hφ)
  have hleft : (44889/50000:ℝ)<FirstContact.cost b0 φ := by
    have h := cut_value hφ
    dsimp [b0]
    linarith
  have hright : (44889/50000:ℝ)<FirstContact.cost e φ := by
    have heDom := hdom e ⟨hB0.trans he.1,le_rfl⟩
    rcases hend with hend | hend
    · subst e
      exact DiagonalTarget.original_contact heDom.2.1 (early_lower hφ) rfl
    · have h := DiagonalSource.original_contact heout (early_lower hφ) hend
      simpa only [FirstContact.cost,value,hend] using h
  exact (lt_min hleft hright).trans_le hh

theorem original {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : φ∈Icc lowerAngle (13/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hc := FirstContact.original_cut ht (early_lower hφ) hm
  by_cases hshort : b≤7/20
  · have hh := original_short hs ht hφ hshort hm
    linarith
  · by_cases hcut : FirstContact.source B φ≤7/20
    · have hh := short_of_cut (show (7/20:ℝ)∈Icc 0 (7/20) by norm_num) hB hφ hcut
      have hV := V_monotone V_short_mem hb (le_of_not_ge hshort)
      dsimp [value] at *
      linarith
    · have hsrc : FirstContact.source B φ∈Icc (7/20:ℝ) outerDiagonal :=
        ⟨le_of_not_ge hcut,hc.trans hb.2⟩
      have hh := active_contact hB hφ hsrc
      have hV := V_monotone ⟨by linarith [hsrc.1],hsrc.2⟩ hb hc
      dsimp [FirstContact.cost,value] at *
      linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
end
end
end

section
/-!
## The full scalar reserve on the actual zero-source contact

The cost increases from `1.3` to `1.4`.  On the remaining arc it
is strictly concave.  Both arguments use actual angular velocities
and literal label derivatives; the two fixed physical endpoints
give a reserve above `0.902` throughout.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma initial_domain {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) : Domain φ :=
  ⟨hφ.1,hφ.2.trans middle_mem.2⟩

lemma initial_acceleration {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    0<bpp parameter φ := by
  have hp := domain (initial_domain hφ)
  have hu := u_antitone parameter_mem hp.2 (domain middle_mem).2 hφ.2
  have hw := target_monotone parameter_mem hp.2 (domain middle_mem).2 hφ.2
  dsimp [target] at hw
  have hf := f_monotone parameter_mem hp.2 (domain middle_mem).2 hφ.2
  have hfp := fp_monotone parameter_nonnegative (domain left_mem).2 hp.2 hφ.1
  have hmid := middle_curve
  have hul : (843/500:ℝ)≤u parameter φ := by linarith [hmid.2.1.1]
  have hwh : w parameter φ≤(259/250:ℝ) := by linarith [hmid.2.2.1.2]
  have hfh : SecondWord.PositiveThree.SourceCurve.f parameter φ≤(87/100:ℝ) := hf.trans hmid.2.2.2.1.2
  have hfpl : (679/1000:ℝ)≤fp parameter φ := left_curve.2.2.2.2.1.trans hfp
  have hf0 := (f_bounds hp).1.le
  have hf2 := pow_le_pow_left₀ hf0 hfh 2
  have hneg := mul_le_mul hwh hf2 (sq_nonneg _) (by norm_num : (0:ℝ)≤259/250)
  have hpos := mul_le_mul hul hfpl (by norm_num : (0:ℝ)≤679/1000) (u_positive hp).le
  dsimp [bpp]
  nlinarith

lemma initial_speed_monotone :
    MonotoneOn (bp parameter) (Icc (13/10:ℝ) (7/5)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hφ => (bp_hasDerivAt (domain (initial_domain hφ))).continuousAt.continuousWithinAt)
    (fun _ hφ => bp_hasDerivAt (domain (initial_domain (Ioo_subset_Icc_self hφ))))
    (fun _ hφ => (initial_acceleration (Ioo_subset_Icc_self hφ)).le)

lemma initial_speed {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    bp parameter φ<(1467/1000:ℝ) :=
  (initial_speed_monotone hφ ⟨by norm_num,le_rfl⟩ hφ.2).trans_lt middle_speed

lemma initial_label {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    LLabel.d1 (target parameter φ)<659/1000 := by
  have hlo := target_monotone parameter_mem (domain left_mem).2
    (domain (initial_domain hφ)).2 hφ.1
  have hhi := target_monotone parameter_mem (domain (initial_domain hφ)).2
    (domain middle_mem).2 hφ.2
  have hend := target_monotone parameter_mem (domain left_mem).2 (domain middle_mem).2
    (show (13/10:ℝ)≤7/5 by norm_num)
  have hdom : ∀ B∈Icc (target parameter (13/10)) (target parameter (7/5)),
      B∈Icc 0 outerDiagonal := by
    intro B hB
    exact ⟨left_target.1.trans hB.1,hB.2.trans middle_target.2⟩
  have hc : ConcaveOn ℝ (Icc (target parameter (13/10)) (target parameter (7/5)))
      (fun B => -LLabel.d1 B) :=
    concave_of_deriv2
      (fun B hB => (LLabel.d1_hasDerivAt (outer_domain (hdom B hB))).neg)
      (fun B hB => (LLabel.d2_hasDerivAt (outer_domain (hdom B hB))).neg)
      (fun B hB => by linarith [L_third_positive (hdom B hB)])
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hend⟩ ⟨hend,le_rfl⟩ ⟨hlo,hhi⟩
  have hlow : -(659/1000:ℝ)< -LLabel.d1 (target parameter φ) :=
    (lt_min (by linarith [left_labels.1]) (by linarith [middle_labels.1])).trans_le hh
  linarith

lemma initial_first {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) : 0<first φ := by
  have hbpp := bp_positive (domain (initial_domain hφ))
  have h1 := mul_lt_mul_of_pos_right (initial_label hφ) hbpp
  have h2 := mul_lt_mul_of_pos_left (initial_speed hφ)
    (by norm_num : (0:ℝ)<659/1000)
  dsimp [first]
  nlinarith

lemma initial_cost_monotone : MonotoneOn cost (Icc (13/10:ℝ) (7/5)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hφ => (cost_hasDerivAt (initial_domain hφ)).continuousAt.continuousWithinAt)
    (fun _ hφ => cost_hasDerivAt (initial_domain (Ioo_subset_Icc_self hφ)))
    (fun _ hφ => (initial_first (Ioo_subset_Icc_self hφ)).le)

lemma initial_value {φ : ℝ} (hφ : φ∈Icc (13/10:ℝ) (7/5)) :
    (451/500:ℝ)<cost φ :=
  left_labels.2.trans_le
    (initial_cost_monotone ⟨le_rfl,by norm_num⟩ hφ hφ.1)

lemma final_domain {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : Domain φ :=
  ⟨by linarith [hφ.1],hφ.2⟩

lemma final_velocities {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) :
    (13/10:ℝ)<bp parameter φ ∧ -(11/50:ℝ)<bpp parameter φ := by
  have hd := final_domain hφ
  have hh := geometry hd
  have hfl := f_monotone parameter_mem (domain middle_mem).2 (domain hd).2 hφ.1
  have hfpl := fp_monotone parameter_nonnegative (domain middle_mem).2 (domain hd).2 hφ.1
  have hf : (8699/10000:ℝ)≤SecondWord.PositiveThree.SourceCurve.f parameter φ := middle_curve.2.2.2.1.1.trans hfl
  have hfp : (73/100:ℝ)≤fp parameter φ := middle_curve.2.2.2.2.1.trans hfpl
  have hbp := mul_le_mul hh.1.1 hf (by norm_num : (0:ℝ)≤8699/10000)
    (u_positive (domain hd)).le
  have hup := mul_le_mul hh.1.1 hfp (by norm_num : (0:ℝ)≤73/100)
    (u_positive (domain hd)).le
  have hf2 : (SecondWord.PositiveThree.SourceCurve.f parameter φ)^2≤1 := by
    have hf0 := (f_bounds (domain hd)).1
    nlinarith [hh.2.2.2.1.2]
  have hneg := mul_le_mul hh.2.1.2 hf2 (sq_nonneg _)
    (by norm_num : (0:ℝ)≤1291/1000)
  dsimp [bp,bpp]
  exact ⟨by norm_num at hbp; linarith,by norm_num at hup hneg; linarith⟩

lemma final_second {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : second φ<0 := by
  have hd := final_domain hφ
  have ht := target_monotone parameter_mem (domain middle_mem).2 (domain hd).2 hφ.1
  have hL2 := middle_labels.2.trans_le
    (L_second_monotone middle_target (target_mem hd) ht)
  have hL1 := L_first_bounds (target_mem hd)
  have hLpos : 0<LLabel.d1 (target parameter φ) := by linarith [hL1.1]
  have hv := final_velocities hφ
  have hsq : (13/10:ℝ)^2<(bp parameter φ)^2 := by nlinarith [hv.1]
  have hneg := mul_lt_mul hL2 hsq.le (by norm_num : (0:ℝ)<(13/10)^2)
    (by linarith [hL2] : 0≤LLabel.d2 (target parameter φ))
  have hlast1 := mul_lt_mul_of_pos_left hv.2 hLpos
  have hlast2 := mul_lt_mul_of_pos_right hL1.2 (by norm_num : (0:ℝ)<11/50)
  dsimp [second]
  nlinarith

lemma final_value {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) :
    (451/500:ℝ)<cost φ := by
  have hc : ConcaveOn ℝ (Icc (7/5:ℝ) (Real.pi/2)) cost :=
    concave_of_deriv2
      (fun t ht => cost_hasDerivAt (final_domain ht))
      (fun t ht => first_hasDerivAt (final_domain ht))
      (fun t ht => (final_second ht).le)
  exact concave_gt_of_endpoints hc hφ
    (initial_value ⟨by norm_num,le_rfl⟩) (by linarith [quarter_value])

theorem cost_lower {φ : ℝ} (hφ : Domain φ) : (451/500:ℝ)<cost φ := by
  by_cases h : φ≤7/5
  · exact initial_value ⟨hφ.1,h⟩
  · exact final_value ⟨le_of_not_ge h,hφ.2⟩

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
end
end
end

section
/-!
## Every original first owner on the later positive-quarter arc

An inactive source is controlled by the zero-source contact (`zero_value`). An active source lies
on a closed physical contact interval beginning there; its concave first derivative reduces the
minimum to that zero endpoint or to one of the two diagonal boundaries (`active_contact`). Every
original weak tie is kept (`original`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Late

open CommonQuarter CorePairGeometry Arithmetic

lemma zero_source {φ : ℝ} (hφ : ZeroContact.Domain φ) :
    FirstContact.source (SourceCurve.target ZeroContact.parameter φ) φ=0 := by
  have hh := SourceCurve.contact (ZeroContact.domain hφ) (ZeroContact.target_mem hφ)
  norm_num [ZeroContact.parameter] at hh
  exact hh

lemma zero_value {φ : ℝ} (hφ : ZeroContact.Domain φ) :
    (451/500:ℝ)<FirstContact.cost (SourceCurve.target ZeroContact.parameter φ) φ := by
  have hh := ZeroContact.cost_lower hφ
  simpa only [FirstContact.cost,ZeroContact.cost,value,zero_source hφ] using hh

theorem active_contact {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hφ : ZeroContact.Domain φ)
    (hsource : FirstContact.source B φ∈Icc 0 outerDiagonal) :
    (44889/50000:ℝ)<FirstContact.cost B φ := by
  let b0 := SourceCurve.target ZeroContact.parameter φ
  have hb0 : b0∈Icc 0 outerDiagonal := ZeroContact.target_mem hφ
  have hcut : FirstContact.source b0 φ=0 := zero_source hφ
  have hLower := (ZeroContact.domain hφ).2
  have hB0 : b0≤B := FirstContact.source_order hb0 hB hLower
    (by rw [hcut]; exact hsource.1)
  obtain ⟨e,he,hecap,hend⟩ := Early.physical_cap hB hsource.2
  have heout : e∈Icc 0 outerDiagonal := ⟨hB.1.trans he.1,he.2⟩
  have hdom : ∀ t∈Icc b0 e, FirstContact.Domain t φ := by
    intro t ht
    have htout : t∈Icc 0 outerDiagonal := ⟨hb0.1.trans ht.1,ht.2.trans he.2⟩
    have hlo := FirstContact.source_monotone hLower hb0 htout ht.1
    have hhi := FirstContact.source_monotone hLower htout heout ht.2
    dsimp only at hlo hhi
    rw [hcut] at hlo
    exact ⟨htout,⟨hlo,hhi.trans hecap⟩,hLower⟩
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (show B∈Icc b0 e from ⟨hB0,he.1⟩)
    (fun t ht => FirstContact.cost_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.first_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.second_hasDerivAt (hdom t ht))
    (fun t ht => (FirstContact.third_negative (hdom t ht)).le)
    (ZeroContact.original_derivative hφ)
  have hleft : (44889/50000:ℝ)<FirstContact.cost b0 φ := by
    have h := zero_value hφ
    dsimp [b0]
    linarith
  have hright : (44889/50000:ℝ)<FirstContact.cost e φ := by
    have heDom := hdom e ⟨hB0.trans he.1,le_rfl⟩
    rcases hend with hend | hend
    · subst e
      exact DiagonalTarget.original_contact heDom.2.1 hLower rfl
    · have h := DiagonalSource.original_contact heout hLower hend
      simpa only [FirstContact.cost,value,hend] using h
  exact (lt_min hleft hright).trans_le hh

theorem original {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : ZeroContact.Domain φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hLower := (ZeroContact.domain hφ).2
  have hc := FirstContact.original_cut ht hLower hm
  by_cases hinactive : FirstContact.source B φ≤0
  · have hzero := ZeroContact.cost_lower hφ
    have horder := FirstContact.source_order hB (ZeroContact.target_mem hφ) hLower
      (by rw [zero_source hφ]; exact hinactive)
    have hL := L_monotone hB (ZeroContact.target_mem hφ) horder
    have hV := V_monotone outer_zero_mem hb hb.1
    dsimp [ZeroContact.cost,value] at *
    linarith
  · have hsrc : FirstContact.source B φ∈Icc 0 outerDiagonal :=
      ⟨le_of_not_ge hinactive,hc.trans hb.2⟩
    have hh := active_contact hB hφ hsrc
    have hV := V_monotone hsrc hb hc
    dsimp [FirstContact.cost,value] at *
    linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.Late
end
end
end

section
/-!
## Both upper first owners by finite displacement from alignment

The first upper owner loses at most `.4*x` in aligned source coordinate.
For the second upper owner on `x≤.11`, the loss is at most `.942076*x`.
The source slope is below `1.061`, and `1.061*.942076<1`, so the actual
angle increase pays the entire label loss.  No implicit contact
minimizer or contact-curve endpoint is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic

lemma V_increment_upper {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    V B-V b≤(1061/1000)*(B-b) := by
  have hm : AntitoneOn (fun t => V t-(1061/1000)*t) (Icc 0 outerDiagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => ((VLabel.outer_hasDerivAt (outer_domain ht)).sub
        ((hasDerivAt_id t).const_mul (1061/1000))).continuousAt.continuousWithinAt)
      (fun t ht => (VLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul (1061/1000)))
      (fun t ht => by linarith [V_first_upper (Ioo_subset_Icc_self ht)])
  have hh := hm hb hB h
  linarith

namespace PositiveThree

lemma upper_of_displacement {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : 0≤x)
    (hdisp : (1061/1000)*(1-A-b)≤x) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases halign : 1≤b+A
  · have hh := original_aligned hs ht halign
    dsimp [value] at *
    linarith
  · have hA : A≤1 := by linarith [hs.1]
    have hdom : 1-A∈Icc 0 outerDiagonal := by
      constructor <;> linarith [(NegativeTwo.primary_mem ht).1,fine_outer_endpoint_bounds.2]
    have hs0 := ShortOuterOne.SameContact.arc_state hdom
    have hbase := original_aligned hs0 ht (show 1≤(1-A)+A by linarith)
    have hinc := V_increment_upper (NegativeTwo.source_mem hs) hdom (by linarith)
    dsimp [value] at *
    linarith

lemma upper_first_displacement {a b A B x : ℝ}
    (_hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 (Real.pi/2+x)) :
    1-A-b≤(2/5)*x := by
  have hcut := upper_source_secondary_cut hx hm
  have htr := positive_trig hx
  have hcos := mul_nonneg
    (show 0≤A-1/2 by linarith [(NegativeTwo.primary_mem ht).1,fine_outer_endpoint_bounds.2])
    (sub_nonneg.mpr htr.2.1)
  have hsin := mul_le_mul_of_nonneg_right
    (show B-1/2≤2/5 by linarith [(NegativeTwo.source_mem ht).2,outer_endpoint_bounds.2.2.2])
    htr.2.2.1
  nlinarith [htr.2.2.2.2.1]

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  have hdisp := upper_first_displacement hs ht hx hm
  have hh := upper_of_displacement hs ht hx.1
    (show (1061/1000)*(1-A-b)≤x by nlinarith [hx.1])
  linarith

lemma upper_second_displacement {a b A B x : ℝ}
    (hs : OuterState a b) (_ht : OuterState A B) (hx : x∈Icc 0 (11/100))
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 (Real.pi/2+x)) :
    1-A-b≤(235519/250000)*x := by
  have hcap : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hcut := upper_target_primary_cut hcap hm
  have htr := positive_trig hcap
  have ha : a-1/2<(57161/62500:ℝ) := by
    linarith [(NegativeTwo.primary_mem hs).2,ShortOuterZero.fine_axial_bounds.2]
  have hsin := mul_le_mul ha.le htr.2.2.2.2.1
    htr.2.2.1 (by norm_num : (0:ℝ)≤57161/62500)
  have hb := mul_nonneg hs.1 (sub_nonneg.mpr htr.2.1)
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsquare := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  linarith

theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases he : x≤11/100
  · have hdisp := upper_second_displacement hs ht ⟨hx.1,he⟩ hm
    have hh := upper_of_displacement hs ht hx.1
      (show (1061/1000)*(1-A-b)≤x by nlinarith [hx.1])
    linarith
  · have hh := late_angle hs ht
      (show (419/250:ℝ)≤Real.pi/2+x by linarith [pi_hand_enclosure.1])
    linarith

end PositiveThree

end SquaresInCircles.Eight.SecondWord
end
end
end

section
/-!
## Every original weak owner for the positive second-word edge three

Both closed angle halves and all four original axes are included.
The lower first owner uses actual short-source and zero-source
contacts with the original physical diagonal endpoints.  No
contact reduction or endpoint bound is an input to this theorem.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_source_secondary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  by_cases h : φ≤13/10
  · exact Early.original hs ht ⟨hφ.1,h⟩ hm
  · exact Late.original hs ht ⟨le_of_not_ge h,hφ.2⟩ hm

theorem original_lower_target_primary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ :=
  original_lower_source_secondary hs ht hφ (lower_second_implies_first hs ht hφ hm)

theorem original_scalar {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hx0 : 0≤x
  · have hupper : x∈Icc 0 (7/10) := ⟨hx0,hx.2⟩
    fin_cases j
    · exact original_upper_source_secondary hs ht hupper hm
    · exact original_upper_target_primary hs ht hupper hm
    · linarith [original_upper_target_secondary hs ht hupper hm]
    · exact original_upper_source_primary hs ht hupper hm
  · have hlower : Lower (Real.pi/2+x) := by
      dsimp [Lower,lowerAngle]
      constructor <;> linarith [hx.1]
    fin_cases j
    · linarith [original_lower_source_secondary hs ht hlower hm]
    · linarith [original_lower_target_primary hs ht hlower hm]
    · linarith [original_lower_target_secondary hs ht hlower hm]
    · linarith [original_lower_source_primary hs ht hlower hm]

theorem original_scalar_abs {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) :=
  original_scalar hs ht (abs_le.mp hx) j hm

theorem original_at_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (89777/100000:ℝ)<value b B φ := by
  have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
  have hh := original_scalar_abs hs ht hφ j (by simpa only [he] using hm)
  simpa only [he] using hh

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end

section
/-!
## Original physical and cyclic positive edge-three inequalities

The role-three positive pair and its role-five negative reflection keep the original weak
separator (`original_role`). The cycle statement `actual` uses the common circle, the physical
signs and the quarter lift, including every tied original owner.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (89777/100000:ℝ)<SecondWord.cost 3 .outer .outer true true a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (89777/100000:ℝ)<SecondWord.cost 5 .outer .outer false false a b A B φ := by
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b 1 1 φ := by
    simpa only [neg_neg] using
      (show 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-(-1:ℝ)) (-(-1:ℝ)) φ from by
        rw [margin_reflection]
        exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (3:Vertex) .outer .outer true true A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (σ τ : Bool)
    (hrole : (i=3 ∧ σ=true ∧ τ=true) ∨ (i=5 ∧ σ=false ∧ τ=false))
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<SecondWord.cost i .outer .outer σ τ a b A B φ := by
  rw [threshold_value]
  rcases hrole with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 1 φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_cost hs ht hφ j hmargin]
  · have hmargin : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_reflected hs ht hφ j hmargin]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true) ∨
      (i=5 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,ite_true] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,ite_true] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original_role i (positiveOf C i) (positiveOf C (next i)) hrole
    hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true) ∨
      (i=5 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole hs ht j howner

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveNegativeThree

open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (4493/5000:ℝ)<SecondWord.cost 3 .outer .outer true false a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (4493/5000:ℝ)<SecondWord.cost 5 .outer .outer true false a b A B φ := by
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b 1 (-1) φ := by
    simpa only [neg_neg] using
      (show 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-(-1:ℝ)) (-(1:ℝ)) φ from by
        rw [margin_reflection]
        exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (3:Vertex) .outer .outer true false A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (σ τ : Bool)
    (hrole : (i=3 ∧ σ=true ∧ τ=false) ∨ (i=5 ∧ σ=true ∧ τ=false))
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<SecondWord.cost i .outer .outer σ τ a b A B φ := by
  rw [threshold_value]
  rcases hrole with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_cost hs ht hφ j hmargin]
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_reflected hs ht hφ j hmargin]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false) ∨
      (i=5 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original_role i (positiveOf C i) (positiveOf C (next i)) hrole
    hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false) ∨
      (i=5 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole hs ht j howner

end SquaresInCircles.Eight.SecondWord.PositiveNegativeThree
end
end
end
