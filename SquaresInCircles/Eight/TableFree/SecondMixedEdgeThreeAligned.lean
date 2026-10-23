module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreeAlignedScalars

/-!
# Actual aligned role-three mixed pairs

The positive core uses the original tangent coordinate. The negative
core uses the side polynomial forced by an aligned primary witness.
Every estimate is at the original outer circle point; no contact
replacement or enlarged radius is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.EdgeThreeAligned
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

def B1 : ℝ := HeightLabel.root (3/2)-1/2
def sideH (b : ℝ) : ℝ := en+gn*b-zn*b^2
def positiveCost (b B φ : ℝ) : ℝ := φ-ep+gp*b-L B
def negativeSideCost (b B φ : ℝ) : ℝ := φ-sideH b-L B
def negativeCost (a b B φ : ℝ) : ℝ := φ-MixedThree.negativeCore a b-L B

lemma B1_bounds : (79/100:ℝ)<B1 ∧ B1<(791/1000:ℝ) := by
  have hr := root_cage (u := (3/2:ℝ))
    (l := (1290581264392/1000000000000:ℝ))
    (r := (1290581264393/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  dsimp [B1]
  constructor <;> linarith

lemma unit_state : OuterState 1 B1 := by
  have hq := HeightLabel.root_sq
    (show 0<Q0-(3/2:ℝ)^2 by norm_num [Q0])
  refine ⟨by linarith [B1_bounds.1],by linarith [B1_bounds.2],?_⟩
  dsimp [B1]
  nlinarith

lemma B1_domain : B1∈Icc (0:ℝ) outerDiagonal :=
  ⟨(outer_bounds unit_state).2.2.1,(outer_bounds unit_state).2.2.2.1⟩

lemma unit_label : LHeight.eval (3/2) = -L B1 := by
  simpa using LHeight_actual unit_state

lemma height_bounds {A B : ℝ} (ht : OuterState A B) :
    A+1/2∈LHeightBounds.heights := by
  have hb := outer_bounds ht
  exact ⟨by linarith [hb.1,outer_endpoint_bounds.2.2.1],
    by linarith [hb.2.1,outer_endpoint_bounds.2.1]⟩

lemma unit_target_cut {A B : ℝ} (ht : OuterState A B) :
    (1≤A → B≤B1) ∧ (A≤1 → B1≤B) := by
  have hq := ht.2.2
  have hr := unit_state.2.2
  have hB := ht.1
  have hB1 : 0≤B1 := by linarith [B1_bounds.1]
  constructor
  · intro hA
    by_contra hh
    have hB' : B1<B := lt_of_not_ge hh
    have hp := mul_pos (sub_pos.mpr hB') (show 0<B+B1+1 by linarith)
    have ha := mul_nonneg (sub_nonneg.mpr hA) (show 0≤A+2 by linarith)
    nlinarith
  · intro hA
    by_contra hh
    have hB' : B<B1 := lt_of_not_ge hh
    have hp := mul_pos (sub_pos.mpr hB') (show 0<B+B1+1 by linarith)
    have ha := mul_nonneg (sub_nonneg.mpr hA)
      (show 0≤A+2 by linarith [(outer_bounds ht).1,outer_endpoint_bounds.2.2.1])
    nlinarith

lemma sideH_eq {b : ℝ} :
    MixedThree.negativeCore (7/12) b=sideH b := by
  norm_num [MixedThree.negativeCore,sideH,en,LPrimaryZero.e,gn,zn]
  ring

lemma sideH_mono {b c : ℝ} (hb : 0≤b) (hc : c≤1/2) (hbc : b≤c) :
    sideH b≤sideH c := by
  have hp := mul_nonneg (sub_nonneg.mpr hbc)
    (show 0≤gn-zn*(b+c) by norm_num [gn,zn]; nlinarith)
  dsimp [sideH]
  nlinarith

/-- A finite one-sided slope estimate, including the case in which the
original coordinate lies below the comparison coordinate. -/
lemma sideH_increment {b c x k : ℝ} (hb : 0≤b) (hc : c∈Icc (0:ℝ) (1/2))
    (hx : 0≤x) (hk : 0≤k) (hbc : b≤c+k*x) :
    sideH b≤sideH c+gn*k*x := by
  by_cases he : b≤c
  · have hh := sideH_mono hb hc.2 he
    have hp : 0≤gn*k*x := mul_nonneg (mul_nonneg (by norm_num [gn]) hk) hx
    linarith
  · have hp := mul_nonneg (show 0≤b-c by linarith) (show 0≤b+c by linarith [hc.1])
    have hmul := mul_nonneg (by norm_num : (0:ℝ)≤gn)
      (show 0≤c+k*x-b by linarith)
    dsimp [sideH,gn,zn] at *
    nlinarith

lemma positive_zero_cost : (361/400:ℝ)<positiveCost 0 B1 (Real.pi/2) := by
  have hh := positive_zero
  simpa [positiveCost,positiveHeight,unit_label] using hh

lemma negative_zero_cost : (4489/5000:ℝ)<negativeSideCost 0 B1 (Real.pi/2) := by
  have hh := negative_zero
  simpa [negativeSideCost,negativeHeight,sideH,unit_label] using hh

lemma positive_aligned {b A B : ℝ} (ht : OuterState A B)
    (hb : 0≤b) (hsep : 1≤b+A) :
    (89779/100000:ℝ)<positiveCost b B (Real.pi/2) := by
  have hdB : B∈Icc (0:ℝ) outerDiagonal :=
    ⟨(outer_bounds ht).2.2.1,(outer_bounds ht).2.2.2.1⟩
  by_cases hA : 1≤A
  · have hL := L_monotone hdB B1_domain ((unit_target_cut ht).1 hA)
    have hg := mul_nonneg (by norm_num : (0:ℝ)≤gp) hb
    have hz := positive_zero_cost
    dsimp [positiveCost] at *
    linarith
  · have hu : A+1/2∈Icc (outerDiagonal+1/2) (3/2) :=
      ⟨by linarith [(outer_bounds ht).1],by linarith⟩
    have hh := positive_height_lower hu
    have hM := LHeight_actual ht
    have hg := mul_nonneg (by norm_num : (0:ℝ)≤gp)
      (show 0≤b-(1-A) by linarith)
    dsimp [positiveHeight,positiveCost] at *
    rw [hM] at hh
    nlinarith

lemma negative_side_aligned {b A B : ℝ} (ht : OuterState A B)
    (hb : 0≤b) (hsep : 1≤A-b) :
    (44889/50000:ℝ)<negativeSideCost b B (Real.pi/2) := by
  have hA : 1≤A := by linarith
  have hAhi : A<(283/200:ℝ) := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hmono := sideH_mono hb (show A-1≤1/2 by linarith)
    (show b≤A-1 by linarith)
  have hh := negative_height_lower
    (show A+1/2∈Icc (3/2) (383/200) from ⟨by linarith,by linarith⟩)
  have hM := LHeight_actual ht
  dsimp [negativeHeight,negativeSideCost,sideH] at *
  rw [hM] at hh
  nlinarith

/-- The original side and target are retained; this is the form consumed
when a physical weak primary witness has forced the source onto its side. -/
theorem negative_aligned_of_side {a b A B : ℝ} (ht : OuterState A B)
    (hb : 0≤b) (ha : a=7/12) (hsep : 1≤A-b) :
    (44889/50000:ℝ)<negativeCost a b B (Real.pi/2) := by
  subst a
  simpa [negativeCost,negativeSideCost,sideH_eq] using negative_side_aligned ht hb hsep


theorem negative_aligned {a b A B : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hsep : 1≤A-b) :
    (44889/50000:ℝ)<negativeCost a b B (Real.pi/2) := by
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have hA := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hside : b<1/2 := by linarith
  exact negative_aligned_of_side ht hb (CommonQuarter.core_small_side hs hside).1 hsep

end SquaresInCircles.Eight.TableFree.SecondWord.EdgeThreeAligned
