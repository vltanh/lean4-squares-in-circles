module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameStationaryRatio

/-!
# The complete coupled stationary-point exclusion

Uncompiled transcription of equations (16)--(17). The first curved row
uses its full height interval. The last row retains the source-height
chord and the written increasing quadratic on [.5,.78]. Together with
the affine row, a stationary contact has either negative angular
curvature or a strictly negative target derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic

lemma height_mass (r : Row) (b : ℝ) : mass r b=Q0+1-2*height r b := by
  dsimp [height]
  ring

lemma fraction_upper {r : Row} {b Z L H : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hz : z b≤Z) (hZ : 0≤Z)
    (hl : l r b≤L) (hH : height r b≤H) (hT : 0<Q0+1-2*H) :
    z b*l r b/mass r b≤Z*L/(Q0+1-2*H) := by
  have hpos := l_positive r hb
  have hL : 0≤L := hpos.le.trans hl
  have hnum := mul_le_mul hz hl hpos.le hZ
  have hmass : Q0+1-2*H≤ mass r b := by rw [height_mass]; linarith
  have hfirst := div_le_div_of_nonneg_right hnum (mass_positive r hb).le
  have hsecond := div_le_div_of_nonneg_left (mul_nonneg hZ hL) hT hmass
  exact hfirst.trans hsecond

lemma row_one_target_negative {b : ℝ} (hb : b∈sourceDomain) (hG : G 1 b≤0) :
    stationaryTarget 1 b<0 := by
  have hcut := row_one_source hb hG
  have hH := row_one_height ⟨hb.1,hcut.le⟩
  have hdom : height 1 b∈Icc (1747/1000:ℝ) (951/500) :=
    ⟨by linarith [hH.1],by linarith [hH.2.1]⟩
  have hratio := targetRatio_upper hdom (by norm_num : (0:ℝ)≤923/500)
    hH.1.le (by norm_num : (0:ℝ)<387/1000) (by norm_num [Q0])
  have hratio0 := targetRatio_nonneg (show 0<height 1 b by linarith [hH.1])
  have hfrac := fraction_upper (source_outer hb)
    (show z b≤(1/10:ℝ) by dsimp [z]; linarith) (by norm_num)
    hH.2.2.le hH.2.1.le (by norm_num [Q0] : 0<Q0+1-2*(1891/1000))
  have hbracket : P 1+z b*l 1 b/mass 1 b≤
      P 1+(1/10)*(943/1000)/(Q0+1-2*(1891/1000)) := by linarith
  have hp := mul_le_mul_of_nonneg_left hbracket hratio0
  have hq := mul_le_mul_of_nonneg_right hratio.le
    (by norm_num [P,Q0] : (0:ℝ)≤P 1+(1/10)*(943/1000)/(Q0+1-2*(1891/1000)))
  have hf := f_monotone hdom (by norm_num) hH.2.1.le
  have href : f (1891/1000)+(387/1000)*
      (P 1+(1/10)*(943/1000)/(Q0+1-2*(1891/1000)))-t 1< -(6/625:ℝ) := by
    norm_num [f,P,t,Q0]
  dsimp [stationaryTarget]
  linarith

abbrev lastHeight : ℝ := 92117/50000
abbrev lastMass : ℝ := Q0+1-2*lastHeight
abbrev chordSlope : ℝ := (2367/25000)/(487/1000)
def ratioLine (b : ℝ) : ℝ := 82969/25000-(158863/100000)*chordHeight b
def finalBracket (b : ℝ) : ℝ := P 3+(233/250)*(b-1/2)/lastMass

def quadratic (b : ℝ) : ℝ := f lastHeight+ratioLine b*finalBracket b-t 3
def quadraticD (b : ℝ) : ℝ :=
  -(158863/100000)*chordSlope*finalBracket b+ratioLine b*(233/250)/lastMass

lemma quadratic_hasDerivAt (b : ℝ) : HasDerivAt quadratic (quadraticD b) b := by
  have hR : HasDerivAt ratioLine (-(158863/100000)*chordSlope) b := by
    have h : HasDerivAt (fun y => (82969/25000:ℝ)-(158863/100000)*
        ((4369/2500:ℝ)+(2367/25000)/(487/1000)*(y-293/1000)))
        (-((158863/100000)*((2367/25000)/(487/1000)*1))) b :=
      ((((hasDerivAt_id' b).sub_const (293/1000:ℝ)).const_mul
        ((2367/25000)/(487/1000):ℝ)).const_add (4369/2500:ℝ)).const_mul
          (158863/100000:ℝ) |>.const_sub (82969/25000:ℝ)
    exact h.congr_deriv (by simp only [chordSlope]; ring)
  have hB : HasDerivAt finalBracket ((233/250)/lastMass) b := by
    have h : HasDerivAt (fun y => P 3+(233/250)*(y-1/2)/lastMass)
        ((233/250)*1/lastMass) b :=
      ((((hasDerivAt_id' b).sub_const (1/2:ℝ)).const_mul (233/250:ℝ)).div_const
        lastMass).const_add (P 3)
    exact h.congr_deriv (by ring)
  have h : HasDerivAt (fun y => f lastHeight+ratioLine y*finalBracket y-t 3)
      (-(158863/100000)*chordSlope*finalBracket b+ratioLine b*((233/250)/lastMass)) b :=
    ((hR.mul hB).const_add (f lastHeight)).sub_const (t 3)
  exact h.congr_deriv (by simp only [quadraticD]; ring)

lemma quadratic_derivative_positive {b : ℝ} (hb : b∈Icc (1/2:ℝ) (39/50)) :
    (16/125:ℝ)<quadraticD b := by
  norm_num [quadraticD,finalBracket,ratioLine,chordHeight,chordSlope,lastMass,lastHeight,P,Q0]
  linarith [hb.1,hb.2]

lemma quadratic_negative {b : ℝ} (hb : b∈Icc (1/2:ℝ) (39/50)) : quadratic b<0 := by
  have hm : MonotoneOn quadratic (Icc (1/2:ℝ) (39/50)) :=
    monoOn_of_hasDeriv_nonneg
      (fun b _ => (quadratic_hasDerivAt b).continuousAt.continuousWithinAt)
      (fun b _ => quadratic_hasDerivAt b)
      (fun b hb => by linarith [quadratic_derivative_positive (Ioo_subset_Icc_self hb)])
  have hh := hm hb (by norm_num) hb.2
  have href : quadratic (39/50)< -(629/100000:ℝ) := by
    norm_num [quadratic,f,ratioLine,chordHeight,finalBracket,lastHeight,lastMass,P,t,Q0]
  linarith

lemma row_three_early_target_negative {b : ℝ} (hb : b∈sourceDomain)
    (hG : G 3 b≤0) (hsmall : b≤1/2) : stationaryTarget 3 b<0 := by
  have hcut := row_three_source hb hG
  have hH := row_three_height ⟨hb.1,hcut.le⟩
  have hdom : height 3 b∈Icc (1747/1000:ℝ) (951/500) :=
    ⟨by linarith [hH.1],by linarith [hH.2.1]⟩
  have hratio := targetRatio_upper hdom (by norm_num : (0:ℝ)≤4369/2500)
    hH.1.le (by norm_num : (0:ℝ)<533/1000) (by norm_num [Q0])
  have hratio0 := targetRatio_nonneg (show 0<height 3 b by linarith [hH.1])
  have hfrac : z b*l 3 b/mass 3 b≤0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by dsimp [z]; linarith) (l_positive 3 (source_outer hb)).le)
      (mass_positive 3 (source_outer hb)).le
  have hp := mul_le_mul_of_nonneg_left
    (show P 3+z b*l 3 b/mass 3 b≤P 3 by linarith) hratio0
  have hq := mul_le_mul_of_nonneg_right hratio.le (by norm_num [P] : (0:ℝ)≤P 3)
  have hf := f_monotone hdom (by norm_num [lastHeight]) hH.2.1.le
  have href : f lastHeight+(533/1000)*P 3-t 3< -(21/500:ℝ) := by
    norm_num [f,lastHeight,P,t,Q0]
  dsimp [stationaryTarget]
  linarith

lemma row_three_late_target_negative {b : ℝ} (hb : b∈sourceDomain)
    (hG : G 3 b≤0) (hlarge : 1/2≤b) : stationaryTarget 3 b<0 := by
  have hcut := row_three_source hb hG
  have hsrc : b∈Icc (293/1000:ℝ) (39/50) := ⟨hb.1,hcut.le⟩
  have hH := row_three_height hsrc
  have hdom : height 3 b∈ratioDomain := ⟨hH.1.le,hH.2.1.le⟩
  have hchord := row_three_chord hsrc
  have hratio := targetRatio_tangent hdom
  have hbound : targetRatio (height 3 b)<ratioLine b := by
    dsimp only [ratioLine]
    linarith
  have hratio0 := targetRatio_nonneg (show 0<height 3 b by linarith [hH.1])
  have hfrac := fraction_upper (source_outer hb) (le_refl (z b))
    (show 0≤z b by dsimp [z]; linarith) hH.2.2.le hH.2.1.le
    (by norm_num [Q0,lastHeight] : 0<Q0+1-2*lastHeight)
  have he : z b*(233/250)/(Q0+1-2*(92117/50000))=(233/250)*(b-1/2)/lastMass := by
    simp only [z,lastMass,lastHeight]
    ring
  have hbracket : P 3+z b*l 3 b/mass 3 b≤finalBracket b := by
    dsimp only [finalBracket]
    linarith
  have hm : 0<lastMass := by norm_num [lastMass,lastHeight,Q0]
  have hB0 : 0≤finalBracket b := by
    have hq := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤233/250) (sub_nonneg.mpr hlarge)) hm.le
    have hP : (0:ℝ)≤P 3 := by norm_num [P]
    dsimp only [finalBracket]
    linarith
  have hprod := mul_le_mul_of_nonneg_left hbracket hratio0
  have hprodU := mul_le_mul_of_nonneg_right hbound.le hB0
  have hf := f_monotone (ratio_domain_inclusion hdom) (by norm_num [lastHeight]) hH.2.1.le
  have hupper : stationaryTarget 3 b≤quadratic b := by
    dsimp only [stationaryTarget,quadratic]
    linarith
  exact hupper.trans_lt (quadratic_negative ⟨hlarge,hcut.le⟩)

lemma row_three_target_negative {b : ℝ} (hb : b∈sourceDomain) (hG : G 3 b≤0) :
    stationaryTarget 3 b<0 := by
  rcases le_total b (1/2) with hsmall | hlarge
  · exact row_three_early_target_negative hb hG hsmall
  · exact row_three_late_target_negative hb hG hlarge

lemma target_negative (r : Row) (hr : Coupled r) {b : ℝ}
    (hb : b∈sourceDomain) (hG : G r b≤0) : stationaryTarget r b<0 := by
  fin_cases r
  · exact row_zero_target_negative hb hG
  · exact row_one_target_negative hb hG
  · exact (hr rfl).elim
  · exact row_three_target_negative hb hG

/-- The two alternatives in equation (14), at the actual original contact. -/
theorem stationary_descent (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hstat : angleFirst r B x=0) :
    angleSecond r B x<0 ∨ targetFirst r B x<0 := by
  have hsource : contact B x∈sourceDomain :=
    ⟨(SecondWord.SameZero.b_lower hd.1 hd.2.1).le,hd.2.2.2⟩
  by_cases hG : G r (contact B x)≤0
  · right
    rw [actual_target r hd hstat]
    exact target_negative r hr hsource hG
  · left
    rw [actual_second r hd hstat]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (l_positive r hd.2.2)) (lt_of_not_ge hG)

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary
