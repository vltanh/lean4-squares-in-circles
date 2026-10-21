module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperTargetSource

/-!
# The complete initial target-diagonal curvature interval

The diagonal inverse uses the original fixed radius and literal target
diagonal.  The inverse-polynomial height bound and a positive bracket
give curvature greater than `.9` on the whole interval `[0,.1]`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

abbrev z := OppositeTwo.TargetRatio.z
abbrev speed := OppositeTwo.TargetRatio.speed
def value (b : ℝ) : ℝ :=
  Real.pi/2+UpperInverse.X z b-T b-L outerDiagonal
def first (b : ℝ) : ℝ := OppositeTwo.TargetRatio.F b-TLabel.d1 b
def second (b : ℝ) : ℝ := OppositeTwo.TargetRatio.first b-TLabel.d2 b

lemma z_mem : z∈UpperInverse.shifts := by
  have hh := OppositeTwo.TargetRatio.z_bounds
  constructor <;> linarith [hh.1,hh.2]

lemma inverse_first (b : ℝ) : UpperInverse.F z b=OppositeTwo.TargetRatio.F b := by
  rw [OppositeTwo.TargetRatio.F_formula]
  rfl

lemma value_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt value (first b) b := by
  have hd := (((OppositeTwo.PrimaryInverse.X_source_hasDerivAt hb z_mem).const_add
    (Real.pi/2)).sub (TLabel.outer_hasDerivAt (outer_domain hb))).sub_const (L outerDiagonal)
  convert hd using 1
  · rfl
  · dsimp [first]
    rw [inverse_first]

lemma first_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt first (second b) b := by
  convert (OppositeTwo.TargetRatio.F_hasDerivAt hb).sub
    (TLabel.d1_hasDerivAt (outer_domain hb)) using 1 <;> rfl

lemma early_domain {b : ℝ} (hb : b∈Icc 0 (1/10)) : b∈Icc 0 outerDiagonal :=
  ⟨hb.1,hb.2.trans UpperTarget.tenth_mem.2⟩

lemma tenth_U : (94281/50000:ℝ)<U (1/10) ∧ U (1/10)<47141/25000 :=
  shifted_chart_reference (outer_domain UpperTarget.tenth_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma early_ratio {b : ℝ} (hb : b∈Icc 0 (1/10)) : ratio b<(319/1000:ℝ) := by
  have hB := early_domain hb
  have hu := U_positive (outer_domain hB)
  have hmono := ShortOuterOne.SameContact.arc_antitone
    (outer_domain hB) (outer_domain UpperTarget.tenth_mem) hb.2
  have hU : (94281/50000:ℝ)<U b := by
    have hh := tenth_U.1
    dsimp [U] at hh ⊢
    linarith
  change (b+1/2)/U b<(319/1000:ℝ)
  apply (div_lt_iff₀ hu).2
  nlinarith [hb.2]

lemma ratioD_floor {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (557/1000:ℝ)<ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hp := pow_le_pow_left₀ hu.le (UW_bounds hb).2.1.le 3
  change (557/1000:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at *
  nlinarith

lemma early_brace {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    0<NegativeTwo.Inverse.brace (U b) (ratio b) (speed b) := by
  have hB := early_domain hb
  have hr := outer_ratio_bounds hB
  have hrhi := early_ratio hb
  have hr2 : (ratio b)^2<(319/1000:ℝ)^2 := by nlinarith [hr.1]
  have hq := NegativeTwo.Inverse.actual_q_positive hB
  have hq0 : 0<NegativeTwo.Inverse.q (U b) := by linarith
  have hv := OppositeTwo.TargetRatio.speed_lower hB
  have hv2 : (481/500:ℝ)^2<(speed b)^2 := by nlinarith
  have hfirst : 2*(ratio b)^2/NegativeTwo.Inverse.q (U b)<47/250 := by
    apply (div_lt_iff₀ hq0).2
    nlinarith
  have hsecond : (ratio b)^2/(speed b)^2<11/100 := by
    apply (div_lt_iff₀ (sq_pos_of_pos (show 0<speed b by linarith))).2
    nlinarith
  have hD := ratioD_floor hB
  change 0<ratioD b-2*(ratio b)^2/NegativeTwo.Inverse.q (U b)-
    (ratio b)^2/(speed b)^2
  linarith

lemma tenth_second : TLabel.d2 (1/10)<(-(1169/1000):ℝ) := by
  have hh := TLabel.second_chart_reference (outer_domain UpperTarget.tenth_mem)
    (l := (188562986/10^8:ℝ)) (u := (188562987/10^8:ℝ))
    (dlo := (-2:ℝ)) (dhi := (-(1169/1000):ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma early_curvature {b : ℝ} (hb : b∈Icc 0 (1/10)) : (9/10:ℝ)<second b := by
  have hB := early_domain hb
  have hheight := OppositeTwo.Inverse.actual_height_derivative hB
  have hweight := (OppositeTwo.TargetRatio.weight_bounds hB).1
  have hbrace := early_brace hb
  have hproduct := mul_pos hweight hbrace
  have hT := (T_second_monotone hB UpperTarget.tenth_mem hb.2).trans_lt tenth_second
  change (9/10:ℝ)< -ratio b*PJCritical.heightFactorD (U b)+
    z/(NegativeTwo.Inverse.q (U b)*speed b)*
      NegativeTwo.Inverse.brace (U b) (ratio b) (speed b)-TLabel.d2 b
  linarith

lemma late_monotone : MonotoneOn value (Icc (1/10) outerDiagonal) := by
  have hM := UpperTarget.source_cost_monotone z_mem (by rfl)
  intro b hb B hB h
  have hh := hM hb hB h
  dsimp [value]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperDiagonal
