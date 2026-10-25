module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryDiagonalReferences

/-!
# Eight squares: one speed estimate on the whole late secondary arc

Endpoint monotonicity gives the stated geometric bounds. The exact
second derivative of the circle speed is at most -1/2, and the single
reference 0.68 gives its global bound by completing a square.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open Diagonal (Z Y horizontal vertical factor factorD)
open StationaryPrimitives (Interval)

lemma late_angle {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) :
    x∈Icc 0 (7/10) := ⟨(Diagonal.event_angle he).1.trans hx.1,hx.2⟩

lemma late_geometry {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) :
    (1399/1000:ℝ)<vertical x ∧ vertical x<(1533/1000:ℝ) ∧
    (1251/1000:ℝ)<horizontal x ∧ horizontal x<(7/5:ℝ) ∧
    (167/250:ℝ)<factor x ∧ factor x<(727/1000:ℝ) ∧ factorD x< -(93/250:ℝ) ∧
    0<Z x ∧ Z x<(451/1000:ℝ) ∧ (77/40:ℝ)<Y x ∧ Real.cos x<(17/20:ℝ) := by
  have hx' := late_angle he hx
  have he' := Diagonal.event_angle he
  have hcap : (7/10:ℝ)∈Icc 0 (7/10) := by norm_num
  have hmV := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone he' hx' hx.1
  have hMV := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone hx' hcap hx.2
  have hmH := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_antitone he' hx' hx.1
  have hMH := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_antitone hx' hcap hx.2
  have hmF := SecondWord.NegativeTwo.PrimaryDiagonal.factor_antitone hx' hcap hx.2
  have hMF := SecondWord.NegativeTwo.PrimaryDiagonal.factor_antitone
    (show (2779/5000:ℝ)∈Icc 0 (7/10) by norm_num) hx'
    (he.1.1.le.trans hx.1)
  have hFD := factorD_monotone hx' hcap hx.2
  have hk := cos_anti (show (2779/5000:ℝ)∈Icc 0 (7/10) by norm_num) hx'
    (he.1.1.le.trans hx.1)
  have hk' : Real.cos x<(17/20:ℝ) := hk.trans_lt Reference.left_cos
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hc := event_coordinates he
  change vertical e-1/2≤vertical x-1/2 at hmV
  change vertical x-1/2≤vertical (7/10)-1/2 at hMV
  change horizontal x≤horizontal e at hmH
  rw [hc.2] at hmV
  rw [hc.1] at hmH
  have hrad := SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx'
  have hoff := SecondWord.NegativeTwo.PrimaryDiagonal.offset_bounds
  have hZ : Z x<(451/1000:ℝ) := by
    change Real.cos x+offset<(451/1000:ℝ)
    linarith only [hk',hoff.2]
  have hY : (77/40:ℝ)<Y x := by
    have hs := hrad.2.2.2.2
    have hZ2 := pow_lt_pow_left₀ hZ hrad.1.le two_ne_zero
    have hY2 : (77/40:ℝ)^2<(Y x)^2 := by norm_num [Q0] at hs ⊢; linarith only [hs,hZ2]
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith only [hrad.2.2.1]) hY2
  exact ⟨by linarith only [hmV,hd.1],by linarith only [hMV,Reference.cap_geometry.1],
    Reference.cap_geometry.2.1.trans_le hMH,by linarith only [hmH,hd.2],
    Reference.cap_geometry.2.2.1.trans_le hmF,hMF.trans_lt Reference.left_factor,
    hFD.trans_lt Reference.cap_geometry.2.2.2,hrad.1,hZ,hY,hk'⟩

lemma factorDD_upper {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) :
    factorDD x<(1/2:ℝ) := by
  have hx' := late_angle he hx
  have hg := late_geometry he hx
  have ht := positive_trig hx'
  have hyup := (SecondWord.NegativeTwo.PrimaryDiagonal.radical_data hx').2.2.2.1
  have hoff := SecondWord.NegativeTwo.PrimaryDiagonal.offset_bounds
  let K : Interval (Real.cos x) := Interval.of_bounds
    ⟨show (19121/25000:ℝ)≤Real.cos x from ht.1.le,hg.2.2.2.2.2.2.2.2.2.2.le⟩
  let S : Interval (Real.sin x) := Interval.of_bounds
    ⟨ht.2.2.1,show Real.sin x≤(129/200:ℝ) from by linarith [ht.2.2.2.1]⟩
  let O : Interval offset := Interval.of_bounds ⟨hoff.1.le,hoff.2.le⟩
  let Zb : Interval (Z x) := Interval.of_bounds
    ⟨hg.2.2.2.2.2.2.2.1.le,hg.2.2.2.2.2.2.2.2.1.le⟩
  let Yb : Interval (Y x) := Interval.of_bounds ⟨hg.2.2.2.2.2.2.2.2.2.1.le,hyup.le⟩
  have hY : 0<Yb.lo := by norm_num [Yb,Interval.of_bounds]
  let Nb : Interval (numerator x) :=
    ((((Interval.point (1-Q0)).add O.square).mul K)).add
      (O.mul ((Interval.point 1).add K.square))
  let NDb : Interval (numeratorD x) :=
    ((((Interval.point (Q0-1)).sub O.square).sub (((Interval.point 2).mul O).mul K))).mul S
  let Y5 := Yb.cube.mul Yb.square
  have hY5 : 0<Y5.lo := Interval.mul_lo_pos (Interval.cube_lo_pos hY)
    (Interval.square_lo_pos hY)
  let F := (NDb.div Yb.cube (Interval.cube_lo_pos hY)).sub
    (((((Interval.point 3).mul Nb).mul Zb).mul S).div Y5 hY5)
  have hhi : F.hi<(1/2:ℝ) := by
    norm_num [F,NDb,Nb,Y5,K,S,O,Zb,Yb,Interval.of_bounds,Interval.point,Interval.add,
      Interval.sub,Interval.neg,Interval.mul,Interval.square,Interval.cube,
      Interval.div,Interval.inv,Q0]
  have hb := F.mem.2.trans_lt hhi
  convert hb using 1
  dsimp [factorDD]
  congr 1
  congr 1
  ring

lemma speed_curvature {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) :
    speedDD x< -(1/2:ℝ) := by
  have hg := late_geometry he hx
  have hU := hg.1
  have hU' := hg.2.1
  have hV := hg.2.2.1
  have hf := hg.2.2.2.2.1
  have hfd := hg.2.2.2.2.2.2.1
  have hff := factorDD_upper he hx
  have h1 : (1399/1000:ℝ)*(167/250)^3<vertical x*(factor x)^3 := by
    gcongr
  have h2 : (3:ℝ)*(1251/1000)*(167/250)*(93/250)<
      3*horizontal x*factor x*(-factorD x) := by
    gcongr <;> linarith
  have h3a := mul_lt_mul_of_pos_left hff (show 0<vertical x by linarith)
  have h3b := mul_lt_mul_of_pos_right hU' (show (0:ℝ)<1/2 by norm_num)
  dsimp [speedDD]
  nlinarith

theorem speed_upper {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) :
    speed x<(513/500:ℝ) := by
  have hdom := fun y hy => late_angle he (show y∈Icc e (7/10) from hy)
  have href : (17/25:ℝ)∈Icc e (7/10) := ⟨by linarith [he.1.2],by norm_num⟩
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (f:=fun y => -speed y) (df:=fun y => -speedD y) (ddf:=fun y => -speedDD y)
    (κ:=1/2)
    (fun y hy => (speed_hasDerivAt (hdom y hy)).neg)
    (fun y hy => (speedD_hasDerivAt (hdom y hy)).neg)
    (fun y hy => by linarith [speed_curvature he hy]) href hx
  have hrefs := Reference.speed_reference
  have habs := abs_lt.1 hrefs.2
  have hs : (speedD (17/25))^2<(7/1000:ℝ)^2 := by nlinarith
  have hcomp := sq_nonneg (x-17/25-2*speedD (17/25))
  nlinarith

lemma first_negative (r : Row) (hr : r=1 ∨ r=2) {e x : ℝ}
    (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) : first r x<0 := by
  have hg := late_geometry he hx
  have hs := speed_upper he hx
  have hprod : horizontal x*factor x<(7/5:ℝ)*(727/1000) := by
    have hH := hg.2.2.2.1
    have hF := hg.2.2.2.2.2.1
    have hhp := hg.2.2.1
    have hfp := hg.2.2.2.2.1
    gcongr
  rcases hr with rfl | rfl <;> norm_num [first,p,q] <;> nlinarith

theorem cost_lower (r : Row) (hr : r=1 ∨ r=2) {e x : ℝ}
    (he : Diagonal.IsEvent e) (hx : x∈Icc e (7/10)) : (8981/10000:ℝ)<cost r x := by
  have ha : AntitoneOn (cost r) (Icc e (7/10)) := antiOn_of_hasDeriv_nonpos
    (fun y hy => (cost_hasDerivAt r (late_angle he hy)).continuousAt.continuousWithinAt)
    (fun y hy => cost_hasDerivAt r (late_angle he (Ioo_subset_Icc_self hy)))
    (fun y hy => (first_negative r hr he (Ioo_subset_Icc_self hy)).le)
  exact (Reference.final_cost r hr).trans_le
    (ha hx ⟨by linarith [he.1.2],le_rfl⟩ hx.2)

theorem original_contact (r : Row) (hr : r=1 ∨ r=2) {A B x : ℝ}
    (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hc : 1/2+(1/2-A)*Real.cos x+(1/2+B)*Real.sin x=outerDiagonal) :
    (8981/10000:ℝ)<Real.pi/2-x+c r+(t r-P r)*outerDiagonal+p r*A-q r*B := by
  obtain ⟨e,he⟩ := Diagonal.exists_event
  have hafter := original_after_event ht hx he hc
  have hcoords := original_coordinates ht hx hc
  have hh := cost_lower r hr he ⟨hafter,hx.2⟩
  dsimp [cost] at hh
  rw [hcoords.1,hcoords.2] at hh
  convert hh using 1 <;> ring

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal
