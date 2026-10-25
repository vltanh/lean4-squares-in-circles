module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoCapGeometry

/-!
# A whole-interval projection estimate for the endpoint contact

The product of the source radical and its rotated projection is concave
on the entire possible source interval.  Its two endpoint values give
one lower bound, with no interval rows.  This bounds the coefficient
ratio in the fourth derivative of the actual contact cost.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def projection (b : ℝ) : ℝ := c*W b+s*U b
def mass (b : ℝ) : ℝ := c*U b*W b+s*(U b)^2
def massD (b : ℝ) : ℝ := c*(U b-W b*ratio b)-2*s*W b
def massDD (b : ℝ) : ℝ := -c*(2*ratio b+W b*ratioD b)-2*s
def curvatureRatio (b : ℝ) : ℝ :=
  (3*(k1 b)^2+4*k b*k2 b)/(6*(k b)^2*k1 b)

lemma cap_source_mem : (19/25:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma cap_source_radical : (61/40:ℝ)<U (19/25) := by
  have hc := UW_circle (outer_domain cap_source_mem)
  have hp := U_positive (outer_domain cap_source_mem)
  norm_num [W,Q0] at hc
  nlinarith

lemma mass_identity (b : ℝ) : mass b=U b*projection b := by
  dsimp [mass,projection]
  ring

lemma projection_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projection (c-s*ratio b) b := by
  have h1 : HasDerivAt (fun t => t+1/2) 1 b := (hasDerivAt_id' b).add_const (1/2)
  have h2 := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  exact ((h1.const_mul c).add (h2.const_mul s)).congr_deriv (by ring)

lemma projection_monotone : MonotoneOn projection (Icc 0 outerDiagonal) := by
  refine monoOn_of_hasDeriv_nonneg
    (fun b hb => (projection_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun b hb => projection_hasDerivAt (Ioo_subset_Icc_self hb)) ?_
  intro b hb
  have hr := outer_ratio_bounds (Ioo_subset_Icc_self hb)
  have hh := mul_le_mul_of_nonneg_left hr.2.1
    (by linarith [trig.2.2.1] : 0≤ s)
  nlinarith [trig.1,trig.2.2.2]

lemma projection_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (323/200:ℝ)<projection b := by
  have hm := projection_monotone outer_zero_mem hb hb.1
  have hu := TargetContact.Cap.zero_source.1
  have hprod := mul_lt_mul trig.2.2.1 hu.le (by norm_num : (0:ℝ)<1914575671/1000000000)
    (by linarith [trig.2.2.1] : 0 ≤ s)
  dsimp only [projection,W] at hm ⊢
  linarith [trig.1]

lemma mass_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt mass (massD b) b := by
  have hu := U_positive (outer_domain hb)
  have hdU : HasDerivAt (fun t => arc t+1/2) (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hdW : HasDerivAt (fun t => t+1/2) 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hU2 : HasDerivAt (fun t => (arc t+1/2)^2) (2*(arc b+1/2)*(-ratio b)) b :=
    (hdU.pow 2).congr_deriv (by norm_num)
  have hd := ((hdU.const_mul c).mul hdW).add (hU2.const_mul s)
  have hr : (arc b+1/2)*ratio b=b+1/2 := by
    show (arc b+1/2)*((b+1/2)/(arc b+1/2))=b+1/2
    exact mul_div_cancel₀ _ hu.ne'
  exact hd.congr_deriv (by simp only [massD,U,W]; linear_combination (-2*s)*hr)

lemma massD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt massD (massDD b) b := by
  have hdU := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hdW : HasDerivAt (fun t => t+1/2) 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hd := ((hdU.sub (hdW.mul
    (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)))).const_mul c).sub
      (hdW.const_mul (2*s))
  exact hd.congr_deriv (by simp only [massDD,W]; ring)

lemma mass_second_nonpos {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : massDD b≤0 := by
  have hr := outer_ratio_bounds hb
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hh : 0<c*(2*ratio b+W b*ratioD b) :=
    mul_pos (by linarith [trig.1])
      (add_pos (by linarith [hr.1]) (mul_pos hw hr.2.2.1))
  dsimp [massDD]
  linarith [trig.2.2.1]

lemma mass_zero : (74/25:ℝ)< mass 0 := by
  have hu := TargetContact.Cap.zero_source.1
  have hc := UW_circle (outer_domain outer_zero_mem)
  have hfirst := mul_lt_mul trig.1 hu.le
    (by norm_num : (0:ℝ)<1914575671/1000000000) (by linarith [trig.1] : 0≤c)
  have hsecond := mul_lt_mul_of_pos_right trig.2.2.1
    (show (0:ℝ)<Q0-1/4 by norm_num [Q0])
  have hU2 : (U 0)^2=Q0-1/4 := by
    simp only [W] at hc
    linarith
  have he : mass 0=c*U 0*(1/2)+s*(Q0-1/4) := by
    simp only [mass,W]
    rw [hU2]
    ring
  rw [he]
  norm_num [Q0] at hsecond ⊢
  linarith

lemma mass_cap : (74/25:ℝ)< mass (19/25) := by
  have hc := UW_circle (outer_domain cap_source_mem)
  have hfirst := mul_lt_mul trig.1 cap_source_radical.le
    (by norm_num : (0:ℝ)<61/40) (by linarith [trig.1] : 0≤c)
  have hsecond := mul_lt_mul_of_pos_right trig.2.2.1
    (show (0:ℝ)<Q0-(63/50)^2 by norm_num [Q0])
  have hU2 : (U (19/25))^2=Q0-(63/50)^2 := by
    simp only [W] at hc
    linarith
  have he : mass (19/25)=c*U (19/25)*(63/50)+s*(Q0-(63/50)^2) := by
    simp only [mass,W]
    rw [hU2]
    ring
  rw [he]
  norm_num [Q0] at hsecond ⊢
  linarith

lemma mass_lower {b : ℝ} (hb : b∈Icc 0 (19/25)) :
    (74/25:ℝ)< mass b := by
  have hdom (t : ℝ) (ht : t∈Icc 0 (19/25)) : t∈Icc 0 outerDiagonal :=
    ⟨ht.1,ht.2.trans cap_source_mem.2⟩
  have hh := positive_of_second_nonpos (f := fun t => mass t-74/25)
    (d := massD) (dd := massDD) hb
      (fun t ht => (mass_hasDerivAt (hdom t ht)).sub_const (74/25))
      (fun t ht => massD_hasDerivAt (hdom t ht))
      (fun t ht => mass_second_nonpos (hdom t ht))
      (by linarith [mass_zero]) (by linarith [mass_cap])
  linarith

lemma curvatureRatio_identity {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    curvatureRatio b=c*Q0/(2*mass b*projection b)+2*W b/mass b := by
  have hu := U_positive (outer_domain hb)
  have hc : 0<c := by linarith [trig.1]
  have hp : 0<projection b := by linarith [projection_lower hb]
  have hm : 0 < mass b := by rw [mass_identity]; exact mul_pos hu hp
  have hk : k b=projection b/U b := by
    have hratio : ratio b=W b/U b := rfl
    rw [k,hratio,← mul_div_assoc,div_add' _ _ _ hu.ne']
    rfl
  have hk1 : k1 b=c*Q0/(U b)^3 := by dsimp [k1,ratioD,U]; ring
  have hk2 : k2 b=3*c*Q0*W b/(U b)^5 := by dsimp [k2,ratioDD,U,W]; ring
  rw [curvatureRatio,hk,hk1,hk2,mass_identity]
  field_simp [hu.ne',hc.ne',hp.ne',show Q0≠0 by norm_num [Q0]]
  ring

lemma curvatureRatio_upper {b : ℝ} (hb : Domain b) : curvatureRatio b<(6/5:ℝ) := by
  have hu := U_positive (outer_domain hb.1)
  have hm := mass_lower ⟨hb.1.1,(source_upper hb).le⟩
  have hp := projection_lower hb.1
  have hmass : 0 < mass b := by linarith
  have hproj : 0<projection b := by linarith
  have hmp := mul_lt_mul hm hp.le (by norm_num : (0:ℝ)<323/200) hmass.le
  have hq : 0<Q0 := by norm_num [Q0]
  have hfirst : c*Q0/(2*mass b*projection b)<
      ((153/200)*Q0)/(2*(74/25)*(323/200)) := by
    apply (div_lt_iff₀ (by positivity : 0<2*mass b*projection b)).2
    have hcq : c*Q0<(153/200)*Q0 :=
      mul_lt_mul_of_pos_right (by linarith [trig.2.1]) hq
    have hh := mul_lt_mul_of_pos_left hmp
      (show 0<2*((153/200)*Q0)/(2*(74/25)*(323/200)) by norm_num [Q0])
    norm_num [Q0] at hcq hh ⊢
    nlinarith
  have hsecond : 2*W b/mass b<(2*(63/50:ℝ))/(74/25) := by
    apply (div_lt_iff₀ hmass).2
    have hw : W b<(63/50:ℝ) := by dsimp [W]; linarith [source_upper hb]
    have hh := mul_lt_mul_of_pos_left hm (show (0:ℝ)<(2*(63/50))/(74/25) by norm_num)
    norm_num at hh ⊢
    linarith
  rw [curvatureRatio_identity hb.1]
  have hsum : ((153/200)*Q0)/(2*(74/25)*(323/200))+(2*(63/50:ℝ))/(74/25)<6/5 := by
    norm_num [Q0]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve
