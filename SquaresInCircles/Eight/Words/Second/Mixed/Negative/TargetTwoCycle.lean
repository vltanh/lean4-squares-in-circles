module

public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope
public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoLower
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoSide
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerStripContact
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: original-cycle role-two and reflected role-six negative-target rows

`actual_owner` keeps the exact weak owner supplied by the cycle. The reflected role-six row uses
the same points in reversed order, and its potential difference follows the exact reflection
identity (`original_role`).
-/

section
/-!
## Whole-angle affine scalars for the negative core role-two family

The primary costs share one harmonic scalar whose derivative loses
less than .02.  The secondary cost has a uniformly positive derivative.
Both are controlled on the entire lower quarter half from its left
endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

def value (b B φ : ℝ) : ℝ := φ-c-g*b+T B
def third (φ : ℝ) : ℝ :=
  φ+167/10000-c-g*(559/1000)+(609/1000)*
    (1/2+Real.cos φ/2-Real.sin φ/12+(559/1000)*Real.cos φ)
def thirdD (φ : ℝ) : ℝ :=
  1-(609/1000)*(1059/1000)*Real.sin φ-(609/12000)*Real.cos φ

lemma first_left : (997/1000:ℝ)<MixedAffine.first g lowerAngle ∧
    -(1/50:ℝ)<MixedAffine.firstD g lowerAngle := by
  have ht := MixedAffine.left_trig
  have hk := MixedAffine.κ_bounds
  have hs : MixedAffine.κ*Real.sin lowerAngle<(183/200)*(15297/20000) :=
    (mul_lt_mul_of_pos_right hk.2 (by linarith [ht.1] : 0<Real.sin lowerAngle)).trans
      (mul_lt_mul_of_pos_left ht.2.1 (by norm_num : (0:ℝ)<183/200))
  have hc : MixedAffine.κ*Real.cos lowerAngle<(183/200)*(32211/50000) :=
    (mul_lt_mul_of_pos_right hk.2 (by linarith [ht.2.2.1] : 0<Real.cos lowerAngle)).trans
      (mul_lt_mul_of_pos_left ht.2.2.2 (by norm_num : (0:ℝ)<183/200))
  have ha : (87079/100000:ℝ)<lowerAngle := by
    dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  dsimp [MixedAffine.first,MixedAffine.firstD,g]
  constructor <;> linarith [ht.2.2.1,ht.2.1]

lemma first_lower {φ : ℝ} (hφ : Lower φ) : (49/50:ℝ)<MixedAffine.first g φ := by
  have hleft : Lower lowerAngle := MixedAffine.left_mem
  have hder (x : ℝ) (hx : Lower x) : 0<MixedAffine.firstD g x+1/50 := by
    have hh := MixedAffine.firstD_monotone (show (0:ℝ)≤g by norm_num [g]) hleft hx hx.1
    linarith [first_left.2]
  have hm : MonotoneOn (fun x => MixedAffine.first g x+x/50) (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => ((MixedAffine.first_hasDerivAt g x).add ((hasDerivAt_id x).div_const 50)).continuousAt.continuousWithinAt)
      (fun x _ => (MixedAffine.first_hasDerivAt g x).add ((hasDerivAt_id x).div_const 50))
      (fun x hx => (hder x (Ioo_subset_Icc_self hx)).le)
  have hh := hm hleft hφ hφ.1
  have hgap : φ-lowerAngle≤7/10 := by dsimp [lowerAngle]; linarith [hφ.2]
  linarith [first_left.1]

lemma third_hasDerivAt (φ : ℝ) : HasDerivAt third (thirdD φ) φ := by
  have h : HasDerivAt third
      (1+(609/1000)*(-Real.sin φ/2-Real.cos φ/12+(559/1000)*(-Real.sin φ))) φ := by
    have h1 := (((hasDerivAt_id φ).add_const (167/10000)).sub_const c).sub_const (g*(559/1000))
    have h2 := ((((Real.hasDerivAt_cos φ).div_const 2).const_add (1/2)).sub
      ((Real.hasDerivAt_sin φ).div_const 12)).add ((Real.hasDerivAt_cos φ).const_mul (559/1000))
    unfold third
    exact h1.add (h2.const_mul (609/1000))
  convert h using 1
  dsimp [thirdD]
  ring

lemma thirdD_positive (φ : ℝ) : 0<thirdD φ := by
  dsimp [thirdD]
  linarith [Real.sin_le_one φ,Real.cos_le_one φ]

lemma third_left : (49/50:ℝ)<third lowerAngle := by
  have ht := MixedAffine.left_trig
  have ha : (87079/100000:ℝ)<lowerAngle := by
    dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  dsimp [third,g,c]
  linarith [ht.2.2.1,ht.2.1]

lemma third_lower {φ : ℝ} (hφ : Lower φ) : (49/50:ℝ)<third φ := by
  have hm : MonotoneOn third (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (third_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => third_hasDerivAt x)
      (fun x _ => (thirdD_positive x).le)
  exact third_left.trans_le (hm MixedAffine.left_mem hφ hφ.1)

lemma target_affine {A B : ℝ} (ht : OuterState A B) :
    167/10000+(609/1000)*B≤T B := by
  have hh := T_increment_lower outer_zero_mem (NegativeTwo.source_mem ht) ht.1
  rw [T_zero] at hh
  linarith

lemma target_axial_chord {A B : ℝ} (ht : OuterState A B) :
    A≤outerAxial-(261/1000)*B := by
  have hA := (NegativeTwo.primary_mem ht).2
  have hdelta : 0≤outerAxial-A := sub_nonneg.mpr hA
  have hcircle := ht.2.2
  have haxial := axial_circle
  have hraw : B≤(2*outerAxial+1)*(outerAxial-A) := by
    nlinarith [sq_nonneg (A-outerAxial),sq_nonneg B]
  have hfactor := mul_le_mul_of_nonneg_right
    (show 2*outerAxial+1≤383/100 by linarith [outer_endpoint_bounds.2.1]) hdelta
  nlinarith

lemma core_norm_reserve {a b φ : ℝ} (hs : CoreState a b) (hφ : Lower φ) :
    0<a+1/2-Real.sin φ/2-MixedAffine.κ*Real.cos φ := by
  have ht := lower_trig hφ
  have hk := MixedAffine.κ_bounds
  have hsq : (MixedAffine.κ)^2<(183/200:ℝ)^2 := by nlinarith [hk.1,hk.2]
  have he : (Real.sin φ/2+MixedAffine.κ*Real.cos φ)^2+
      (Real.cos φ/2-MixedAffine.κ*Real.sin φ)^2=1/4+(MixedAffine.κ)^2 := by
    linear_combination (1/4+(MixedAffine.κ)^2)*(Real.sin_sq_add_cos_sq φ)
  have hbound : Real.sin φ/2+MixedAffine.κ*Real.cos φ<(1043/1000:ℝ) := by
    nlinarith [sq_nonneg (Real.cos φ/2-MixedAffine.κ*Real.sin φ)]
  linarith [core_primary_lower hs,CoreAngleEndpoint.diagonal_bounds.1]

lemma fourth_early_trig {φ : ℝ} (hφ : Lower φ) (hcut : φ≤123/100) :
    Real.sin φ<(943/1000:ℝ) ∧ (167/500:ℝ)<Real.cos φ := by
  have href : Lower (123/100:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have hs := HighOrderTaylor.sin_le_S13 (x := (123/100:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (123/100:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,
    HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  have hsin := PositiveThree.lower_sin_monotone hφ href hcut
  have hcos := PositiveThree.lower_cos_antitone hφ href hcut
  constructor <;> linarith

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
end
end
end

section
/-!
## Every negative-core to negative-outer original role-two owner

One affine lower bound for T is enough for the whole family.  Each
original lower owner gives a direct comparison with the proved harmonic
scalars; the late estimate includes the complete upper quarter half.
The argument retains both core pieces and all weak axes.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

lemma core_transverse_upper {a b : ℝ} (hs : CoreState a b) : b<(559/1000:ℝ) :=
  (CoreAngleEndpoint.state_bounds hs).2.2.2.2.trans_lt
    (by linarith [CoreAngleEndpoint.diagonal_bounds.2])

lemma first_original {a b A B φ : ℝ} (_hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ+B*Real.cos φ) :
    (49/50:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hcircle := mul_le_mul_of_nonneg_right (target_axial_chord ht)
    (by linarith [htr.1] : 0≤Real.sin φ)
  have hcoef : 0≤609/1000-g*(Real.cos φ-(261/1000)*Real.sin φ) := by
    norm_num [g]
    linarith [htr.1,htr.2.2.2.1]
  have hpaid := mul_nonneg ht.1 hcoef
  have hT := target_affine ht
  have hh := first_lower hφ
  dsimp [value,MixedAffine.first,MixedAffine.κ,g,c] at *
  nlinarith

lemma second_original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -a*Real.cos φ-b*Real.sin φ+A) :
    (49/50:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have hreserve := mul_nonneg htr.2.2.1 (core_norm_reserve hs hφ).le
  have he :
      (outerAxial*Real.sin φ-(1+Real.sin φ+Real.cos φ)/2)*Real.sin φ-
        (outerAxial-a*Real.cos φ-(1+Real.sin φ+Real.cos φ)/2)=
      Real.cos φ*(a+1/2-Real.sin φ/2-MixedAffine.κ*Real.cos φ) := by
    dsimp [MixedAffine.κ]
    linear_combination (outerAxial-1/2)*(Real.sin_sq_add_cos_sq φ)
  have hcut : b≤outerAxial*Real.sin φ-(1+Real.sin φ+Real.cos φ)/2 := by
    apply (mul_le_mul_iff_left₀ hsine).mp
    nlinarith [(NegativeTwo.primary_mem ht).2]
  have hweighted := mul_le_mul_of_nonneg_left hcut (show (0:ℝ)≤g by norm_num [g])
  have hT := T_lower (NegativeTwo.source_mem ht)
  have hh := first_lower hφ
  dsimp [value,MixedAffine.first,MixedAffine.κ,g,c] at *
  nlinarith

lemma third_original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B) :
    (49/50:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hcore := CoreAngleEndpoint.state_bounds hs
  have ha := mul_le_mul_of_nonneg_right hcore.2.1 (by linarith [htr.1] : 0≤Real.sin φ)
  have hcut : 1/2+Real.cos φ/2-Real.sin φ/12+b*Real.cos φ≤B := by nlinarith
  have hcut' := mul_le_mul_of_nonneg_left hcut (by norm_num : (0:ℝ)≤609/1000)
  have hcoef : 0≤g-(609/1000)*Real.cos φ := by norm_num [g]; linarith [Real.cos_le_one φ]
  have hpaid := mul_nonneg (show 0≤559/1000-b by linarith [core_transverse_upper hs]) hcoef
  have hT := target_affine ht
  have hh := third_lower hφ
  dsimp [value,third] at *
  nlinarith

lemma fourth_original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    (9/10:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hBhi : B≤9/10 := (NegativeTwo.source_mem ht).2.trans outer_endpoint_bounds.2.2.2.le
  have hAB := mul_nonneg (sub_nonneg.mpr ht.2.1) htr.2.2.1
  have hsc : 0≤Real.sin φ-Real.cos φ := by linarith [htr.1,htr.2.2.2.1]
  have hdiag := mul_nonneg (sub_nonneg.mpr hBhi) hsc
  have hangle : (123/100:ℝ)<φ := by
    by_contra hn
    have hr := fourth_early_trig hφ (le_of_not_gt hn)
    nlinarith [hr.1,hr.2,hcore.2.1]
  have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
  have hBs := mul_le_mul_of_nonneg_left (Real.sin_le_one φ) ht.1
  have hB : (5/12:ℝ)≤B := by nlinarith [htr.2.2.2.2,hcore.2.1]
  have hT := target_affine ht
  have hb := core_transverse_upper hs
  dsimp [value,g,c]
  linarith

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (17953/20000:ℝ)<value b B φ := by
  by_cases hlate : (147/100:ℝ)≤φ
  · have hT := T_lower (NegativeTwo.source_mem ht)
    have hb := core_transverse_upper hs
    dsimp [value,g,c]
    linarith
  have hlow : Lower φ :=
    ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],
      by linarith [pi_hand_enclosure.1]⟩
  fin_cases j
  · have hh := first_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith
  · have hh := second_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith
  · have hh := third_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith
  · have hh := fourth_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    SecondWord.threshold 2<cost 2 kind .outer false false a b A B φ := by
  rw [threshold_value,core_outer_negative_negative hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
end
end
end

section
/-!
## Physical-cycle adapters for the complete negative-core role-two row

The exact original owner is preserved, including ties.  Reflection
carries the literal role-two cost to role six.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=2 ∧ source≠.outer ∧ target=.outer ∧ σ=false ∧ τ=false) ∨
  (i=6 ∧ source=.outer ∧ target≠.outer ∧ σ=true ∧ τ=true)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,hk,rfl,rfl,rfl⟩ | ⟨rfl,rfl,hk,rfl,rfl⟩
  · exact literal hk (by simpa [State,hk] using hs) (by simpa [State] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : OuterState a b := by simpa [State] using hs
    have ht' : CoreState A B := by simpa [State,hk] using ht
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) (-1) φ := by
      rw [show (-1:ℝ)= -(1:ℝ) by ring,margin_reflection]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (2:Vertex) target .outer false false A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
end
end
end

section
/-!
## All upper owners by an original-source aligned comparison

The core side coordinate max(0,1-a) is physical and aligned-feasible
at the unchanged outer source. The original upper separators allow
only .4x or .53x of coordinate loss. The target label slope bound pays
that finite loss on the entire upper half, including zero coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic

def base (a : ℝ) : ℝ := max 0 (1-a)
def side (B : ℝ) : ℝ := e+g*B-z*B^2

lemma side_label (B : ℝ) : MixedThree.negativeCore (7/12) B=side B := by
  dsimp [MixedThree.negativeCore,side,e,g,z]

lemma core_side_lower {A B : ℝ} (ht : CoreState A B) : side B≤MixedThree.negativeCore A B := by
  have hh := (CoreAngleEndpoint.state_bounds ht).2.1
  dsimp [side,e,g,z,MixedThree.negativeCore]
  linarith

lemma base_bounds {a b : ℝ} (hs : OuterState a b) : 0≤base a ∧ base a≤(101/1000:ℝ) := by
  have ha := (NegativeTwo.primary_mem hs).1
  exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith [fine_outer_endpoint_bounds.2])⟩

lemma aligned_base {a b : ℝ} (hs : OuterState a b) : γ<Real.pi/2-P b+side (base a) := by
  have hb := base_bounds hs
  have hc : 1≤a+base a := by have hh := le_max_right (0:ℝ) (1-a); dsimp [base]; linarith
  have hh := Side.original_primary hs
    (show base a∈Icc (0:ℝ) (1/2) from ⟨hb.1,by linarith [hb.2]⟩)
    (show PositiveThree.Lower (Real.pi/2) from ⟨by dsimp [PositiveThree.lowerAngle]; linarith,le_rfl⟩)
    (by norm_num; linarith)
  simpa [value,side_label] using hh

lemma upper_displacement_cost {a b A B x ρ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : 0≤x) (hρ : ρ∈Icc (0:ℝ) (53/100)) (hdisp : 1-a-ρ*x≤B) :
    γ<value b A B (Real.pi/2+x) := by
  have hb := base_bounds hs
  have hB := core_transverse ht
  have hρx := mul_nonneg hρ.1 hx
  have hbase : base a≤B+ρ*x := max_le (by linarith [hB.1]) (by linarith)
  have hcore := core_side_lower ht
  have hcost : side (base a)-g*ρ*x≤MixedThree.negativeCore A B := by
    by_cases he : base a≤B
    · have hprod := mul_nonneg (sub_nonneg.mpr he)
        (show 0≤g-z*(B+base a) by dsimp [g,z]; linarith [hB.2,hb.2])
      have hp := mul_nonneg (show 0≤g by norm_num [g]) hρx
      dsimp [side] at hcore ⊢
      nlinarith
    · have hsq : B^2≤(base a)^2 := pow_le_pow_left₀ hB.1 (le_of_not_ge he) 2
      have hp := mul_le_mul_of_nonneg_left hbase (show 0≤g by norm_num [g])
      dsimp [side,z] at hcore ⊢
      nlinarith
  have hpay := mul_nonneg (show 0≤1-g*ρ by dsimp [g]; linarith [hρ.1,hρ.2]) hx
  have hh := aligned_base hs
  dsimp [value]
  nlinarith

theorem upper_secondary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.cos x+b*Real.sin x+B) :
    γ<value b A B (Real.pi/2+x) := by
  have hcut : -B≤OppositeTwo.upperCut a b x := by dsimp [OppositeTwo.upperCut]; nlinarith
  have hh := OppositeTwo.upper_secondary_displacement hs hx
  exact upper_displacement_cost hs ht hx.1 (ρ := (2/5:ℝ)) (by norm_num) (by linarith)

theorem upper_primary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x+B*Real.cos x) :
    γ<value b A B (Real.pi/2+x) := by
  have htr := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [htr.1]
  have hA := mul_le_mul_of_nonneg_right (CoreAngleEndpoint.state_bounds ht).2.1 htr.2.2.1
  have hz : 0≤1-Real.cos x := by linarith [htr.2.1]
  have haxial := mul_le_mul_of_nonneg_right
    (show a-1/2≤183/200 by linarith [(NegativeTwo.primary_mem hs).2,outer_endpoint_bounds.2.1]) hz
  have hprod := mul_nonneg hx.1 (show 0≤7/10-x by linarith [hx.2])
  have hzbound : 1-Real.cos x≤(7/20)*x := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hzpaid := mul_le_mul_of_nonneg_left hzbound (by norm_num : (0:ℝ)≤183/200)
  have hspaid := mul_le_mul_of_nonneg_left htr.2.2.2.2.1 (by norm_num : (0:ℝ)≤1/12)
  have hcpay := mul_le_mul_of_nonneg_left htr.1.le (mul_nonneg (by norm_num : (0:ℝ)≤53/100) hx.1)
  have hdisp : -B≤a-1+(53/100)*x := by
    apply (mul_le_mul_iff_left₀ hcos).mp
    nlinarith
  exact upper_displacement_cost hs ht hx.1 (ρ := (53/100:ℝ)) (by norm_num) (by linarith)

theorem upper_second {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.sin x-b*Real.cos x+A) :
    γ<value b A B (Real.pi/2+x) := by
  by_cases he : (167/100:ℝ)≤Real.pi/2+x
  · exact tail hs ht he
  · have hxsmall : x<(1/10:ℝ) := by linarith [pi_hand_enclosure.1]
    have htφ := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htφ.2.2.2.2.2]
    have hsin := htφ.2.2.2.2.1.trans hxsmall.le
    have ha := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
    have has := mul_le_mul_of_nonneg_right ha.le htφ.2.2.1
    have hbc := mul_nonneg hs.1 (by linarith [htφ.1] : 0≤Real.cos x)
    have hA := (CoreAngleEndpoint.state_bounds ht).2.1
    nlinarith

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
end
end
end

section
/-!
## All original negative-outer to negative-core role-two owners

Both closed core pieces and all four weak physical separators are covered on the whole closed
quarter window (`original`, `literal`). The lower primary estimates and the finite upper
comparisons use the unchanged outer source and its original circle equation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) : γ<value b A B φ := by
  have hcore := CoreAngleEndpoint.state_bounds ht
  have hrad := core_radius_sq ht
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.sin φ+B*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [hs.1]
      have he : (A*Real.sin φ+B*Real.cos φ)^2+
          (A*Real.cos φ-B*Real.sin φ)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.cos φ-B*Real.sin φ)]
    · have hac := mul_nonneg (show 0≤a by linarith [hs.1,hs.2.1]) htr.2.2.1
      have hbs := mul_nonneg hs.1 (by linarith [htr.1] : 0≤Real.sin φ)
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1]
    · apply lower_secondary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply lower_primary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    have htr := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htr.2.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.cos x-B*Real.sin x := by
        norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
        linarith [hs.1]
      have he : (A*Real.cos x-B*Real.sin x)^2+
          (A*Real.sin x+B*Real.cos x)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq x)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.sin x+B*Real.cos x)]
    · apply upper_second hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_secondary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_primary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    SecondWord.threshold 2<cost 2 .outer kind false false a b A B φ := by
  rw [threshold_value,outer_core_negative_negative hk hs]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=2 ∧ source=.outer ∧ target≠.outer ∧ σ=false ∧ τ=false) ∨
  (i=6 ∧ source≠.outer ∧ target=.outer ∧ σ=true ∧ τ=true)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,rfl,hk,rfl,rfl⟩ | ⟨rfl,hk,rfl,rfl,rfl⟩
  · exact literal hk (by simpa [State] using hs) (by simpa [State,hk] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : CoreState a b := by simpa [State,hk] using hs
    have ht' : OuterState A B := by simpa [State] using ht
    have heq := margin_reflection j a b A B 1 1 φ
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) (-1) φ := by
      rw [heq]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (2:Vertex) .outer source false false A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
end
end
end
