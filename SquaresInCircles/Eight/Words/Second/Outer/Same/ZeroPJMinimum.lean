module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJDiagonalGeometry
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJZeroCap

/-!
# Eight squares: the complete original P/J same-sign contact

Compactness supplies a minimum on the entire
physical contact region.  Its only possible boundary types are the
three now proved boundaries; the explicit inverse curve excludes an
interior minimum.  The original weak separator then lowers to contact.
-/

section
/-!
## The whole-domain diagonal polynomial

The brace polynomial `bracePolynomial` and the height polynomial `heightPolynomial` are positive
on one interval (`brace_polynomial_positive`, `height_polynomial_positive`). The two signs of the
centered variable are used only to bound odd powers by their absolute values.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.Inverse (q N factorD)

def bracePolynomial (u : ℝ) : ℝ :=
  Q0*q u*(q u-4/25)-u*(Q0-u^2)*(3*q u-8/25)
def heightPolynomial (u : ℝ) : ℝ :=
  u^4*(q u)^2*(Q0-u)^2-16*(Q0-u^2)*(N u)^2
def heightMinorant (t : ℝ) : ℝ :=
  8-39*t+t^2*(2407-4605*t-975*t^2-371*t^3-9*t^5)

lemma brace_polynomial_positive {u : ℝ} (hu : u∈Icc (33/20:ℝ) (383/200)) :
    0<bracePolynomial u := by
  let y := u-33/20
  have hy : y∈Icc (0:ℝ) (53/200) := by dsimp [y]; constructor <;> linarith [hu.1,hu.2]
  have hident : bracePolynomial u=
      18541395801/62500000000+(175200237/25000000)*y+
        y^2*(627933/50000-(62933/2500)*y-6*y^2) := by
    dsimp [bracePolynomial,q,NegativeTwo.Inverse.q,Q0,y]
    ring
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hbracket : 0<627933/50000-(62933/2500)*y-6*y^2 := by nlinarith
  rw [hident]
  have hh := mul_nonneg (sq_nonneg y) hbracket.le
  linarith [hy.1]

lemma height_polynomial_minorant (x : ℝ) :
    heightMinorant |x|<heightPolynomial (37/20+x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h2 := pow_nonneg hx 2
    have h3 := pow_nonneg hx 3
    have h4 := pow_nonneg hx 4
    have h5 := pow_nonneg hx 5
    have h6 := pow_nonneg hx 6
    have h7 := pow_nonneg hx 7
    have h8 := pow_nonneg hx 8
    norm_num [heightMinorant,heightPolynomial,q,NegativeTwo.Inverse.q,N,NegativeTwo.Inverse.N,Q0]
    nlinarith
  · rw [abs_of_nonpos hx]
    have h1 : 0≤-x := neg_nonneg.mpr hx
    have h2 := pow_nonneg h1 2
    have h3 := pow_nonneg h1 3
    have h4 := pow_nonneg h1 4
    have h5 := pow_nonneg h1 5
    have h6 := pow_nonneg h1 6
    have h7 := pow_nonneg h1 7
    have h8 := pow_nonneg h1 8
    norm_num [heightMinorant,heightPolynomial,q,NegativeTwo.Inverse.q,N,NegativeTwo.Inverse.N,Q0]
    nlinarith

lemma height_minorant_positive {t : ℝ} (ht : t∈Icc (0:ℝ) (1/5)) :
    (7:ℝ)<heightMinorant t := by
  have h2 := pow_le_pow_left₀ ht.1 ht.2 2
  have h3 := pow_le_pow_left₀ ht.1 ht.2 3
  have h5 := pow_le_pow_left₀ ht.1 ht.2 5
  have hp : (1444:ℝ)<2407-4605*t-975*t^2-371*t^3-9*t^5 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hp.le (sq_nonneg t)
  have hs := sq_nonneg (t-39/2888)
  dsimp [heightMinorant]
  nlinarith

lemma height_polynomial_positive {u : ℝ} (hu : u∈Icc (33/20:ℝ) (383/200)) :
    (7:ℝ)<heightPolynomial u := by
  have hx : |u-37/20|∈Icc (0:ℝ) (1/5) := by
    refine ⟨abs_nonneg _,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith [hu.1,hu.2]
  have hh := height_polynomial_minorant (u-37/20)
  rw [show 37/20+(u-37/20)=u by ring] at hh
  exact (height_minorant_positive hx).trans hh

lemma inverse_brace_positive {u r z w : ℝ}
    (hu : u∈Icc (33/20:ℝ) (383/200)) (hr : r^2*u^2=Q0-u^2)
    (hz : z∈Icc (0:ℝ) (2/5)) (hw : 0<w) (hn : z^2+w^2=q u) :
    0<NegativeTwo.Inverse.brace u r w := by
  have hu0 : 0<u := by linarith [hu.1]
  have hq : 0<q u := by dsimp [q,NegativeTwo.Inverse.q]; norm_num [Q0]; linarith [hu.2]
  have hz2 : z^2≤(4/25:ℝ) := by nlinarith [hz.1,hz.2]
  have hcoef : 0<Q0*q u-2*u*(Q0-u^2) := by
    let y := u-33/20
    have hy : 0≤y := sub_nonneg.mpr hu.1
    have he : u=33/20+y := by dsimp [y]; ring
    rw [he]
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    nlinarith [sq_nonneg y,pow_nonneg hy 3]
  have hdiff := mul_nonneg (sub_nonneg.mpr hz2) hcoef.le
  have hp := brace_polynomial_positive hu
  have hden : 0<u^3*q u*w^2 := mul_pos (mul_pos (pow_pos hu0 3) hq) (sq_pos_of_pos hw)
  have he : NegativeTwo.Inverse.brace u r w*(u^3*q u*w^2)=
      bracePolynomial u+(4/25-z^2)*(Q0*q u-2*u*(Q0-u^2)) := by
    have e1 : NegativeTwo.Inverse.brace u r w*(u^3*q u*w^2)=
        Q0*q u*w^2-2*r^2*u^3*w^2-r^2*u^3*q u := by
      dsimp [NegativeTwo.Inverse.brace]
      field_simp
    rw [e1]
    dsimp [bracePolynomial]
    linear_combination (-(2*u*w^2+u*q u))*hr+(Q0*q u-2*u*(Q0-u^2))*hn
  have hpos : 0<NegativeTwo.Inverse.brace u r w*(u^3*q u*w^2) := by
    rw [he]
    linarith
  exact pos_of_mul_pos_left hpos hden.le

lemma logarithmic_height_bound {u r : ℝ}
    (hu : u∈Icc (33/20:ℝ) (383/200)) (hr : 0≤r)
    (hc : r^2*u^2=Q0-u^2) :
    r*NegativeTwo.Inverse.factorD u < NegativeTwo.Inverse.factor u/4 := by
  have hu0 : 0<u := by linarith [hu.1]
  have hq : 0<q u := by dsimp [q,NegativeTwo.Inverse.q]; norm_num [Q0]; linarith [hu.2]
  have hQu : 0<Q0-u := by norm_num [Q0]; linarith [hu.2]
  have hN : 0<N u := by
    have hprod := mul_nonneg (sub_nonneg.mpr hu.1)
      (show 0≤4*Q0-2*(u+33/20) by norm_num [Q0]; linarith [hu.2])
    norm_num [N,NegativeTwo.Inverse.N,Q0] at *
    nlinarith
  have hp := height_polynomial_positive hu
  have hleft : 0≤4*r*N u := by positivity
  have hright : 0<u*q u*(Q0-u) := by positivity
  have hsquare : (4*r*N u)^2<(u*q u*(Q0-u))^2 := by
    dsimp [heightPolynomial] at hp
    have hm := mul_nonneg (sq_nonneg (N u)) (show 0≤u^2 by positivity)
    nlinarith [hc,sq_pos_of_pos hu0]
  have hroot : 4*r*N u<u*q u*(Q0-u) := by nlinarith
  dsimp [NegativeTwo.Inverse.factorD,NegativeTwo.Inverse.factor]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).2
  field_simp [hu0.ne',hq.ne']
  nlinarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ.Diagonal
end
end
end

section
/-!
## The complete P/J source-diagonal boundary

The polynomial estimate bounds B''/(B')²
by 1/4 on the whole physical branch.  The original J bounds give
curvature greater than 1/30, so the one rational reference supplies
the asserted strict reserve everywhere on the branch.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

lemma acceleration_bound {x : ℝ} (hx : Domain x) :
    acceleration x<(speed x)^2/4 := by
  let u := U (height x)
  let r := ratio (height x)
  let w := v (height x) x
  have hd := contact_domain hx
  have hu : u∈Icc (33/20:ℝ) (383/200) := by
    dsimp [u]
    rw [(actual_coordinates hx).1]
    exact ⟨(whole_bounds hx.1).1.le,(whole_bounds hx.1).2.1.le⟩
  have hup : 0<u := U_positive (outer_domain hd.1)
  have hrp : 0<r := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hw : 0<w := v_positive hd.1 hd.2.1
  have hq : 0<NegativeTwo.Inverse.q u := by
    linarith [NegativeTwo.Inverse.actual_q_positive hd.1]
  have hz : z₀∈Icc (0:ℝ) (2/5) := by
    dsimp [z₀]
    constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
  have hrc : r^2*u^2=Q0-u^2 := by
    have hh := UW_circle (outer_domain hd.1)
    have hru : r*u=W (height x) := by
      have h0 : U (height x)≠0 := hup.ne'
      dsimp only [r,u]
      rw [show ratio (height x)=W (height x)/U (height x) from rfl]
      field_simp
    have hsq : r^2*u^2=(r*u)^2 := by ring
    rw [hsq,hru]
    dsimp only [u]
    linarith
  have hn : z₀^2+w^2=NegativeTwo.Inverse.q u := by
    have hh := norm_identity hd.1 x
    rw [contact hx] at hh
    exact hh
  have hbrace := inverse_brace_positive hu hrc hz hw hn
  have hlog := logarithmic_height_bound hu hrp.le hrc
  have hfac : 0<NegativeTwo.Inverse.factor u := by
    dsimp [NegativeTwo.Inverse.factor]
    apply div_pos _ (mul_pos hup hq)
    norm_num [Q0]
    linarith [hu.2]
  have hfirst : NegativeTwo.Inverse.factor u < inverseFirst x := by
    dsimp [inverseFirst]
    have hz0 : 0<z₀ := by dsimp [z₀]; linarith [diagonal_fine.1]
    have hp := div_pos (mul_pos hz0 hrp) (mul_pos hq hw)
    linarith
  have hsecond : -r*NegativeTwo.Inverse.factorD u < inverseSecond x := by
    have hz0 : 0<z₀ := by dsimp [z₀]; linarith [diagonal_fine.1]
    have hp := mul_pos (div_pos hz0 (mul_pos hq hw)) hbrace
    dsimp [inverseSecond,PJCritical.inverseTarget,PJCritical.heightFactorD]
    linarith
  have hif : 0 < inverseFirst x := hfac.trans hfirst
  have hratio : -inverseFirst x/4 < inverseSecond x := by linarith
  have hs : 0<speed x := by linarith [(whole_bounds hx.1).2.2.1]
  have hm := mul_lt_mul_of_pos_right hratio (sq_pos_of_pos hs)
  have hid := inverse_second_identity hx
  have hproduct : inverseFirst x*(acceleration x-(speed x)^2/4)<0 := by nlinarith
  exact lt_of_sub_neg (neg_of_mul_neg_right hproduct hif.le)

lemma curvature {x : ℝ} (hx : Domain x) : (1/30:ℝ)<second x := by
  have htarget := target_mem hx
  have hJ := J_first_bounds htarget
  have hJ2 := J_second_upper htarget
  have hspeed := (whole_bounds hx.1).2.2.1
  have hp : 0<JLabel.d1 (height x) := by linarith [hJ.1]
  have h1 := mul_lt_mul_of_pos_left (acceleration_bound hx) hp
  have h2 := mul_le_mul_of_nonneg_right hJ.2.le
    (div_nonneg (sq_nonneg (speed x)) (by norm_num : (0:ℝ)≤4))
  have h3 := mul_lt_mul_of_pos_right hJ2 (sq_pos_of_pos (by linarith : 0<speed x))
  dsimp [second]
  nlinarith

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hd : HasDerivAt (fun t => t+PLabel.outer outerDiagonal-JLabel.outer (height t))
      (1-JLabel.d1 (height x)*speed x) x :=
    (((hasDerivAt_id x).add_const (PLabel.outer outerDiagonal)).sub
      ((JLabel.outer_hasDerivAt (outer_domain (target_mem hx))).comp x
        (height_hasDerivAt hx.1))).congr_deriv (by simp)
  exact hd

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hd : HasDerivAt (fun t => 1-JLabel.d1 (height t)*speed t)
      (-(JLabel.d2 (height x)*speed x*speed x+JLabel.d1 (height x)*acceleration x)) x :=
    (((JLabel.d1_hasDerivAt (outer_domain (target_mem hx))).comp x
      (height_hasDerivAt hx.1)).fun_mul (speed_hasDerivAt hx.1)).const_sub 1
  exact hd.congr_deriv (by simp only [second]; ring)

theorem lower {x : ℝ} (hx : Domain x) : (89777/100000:ℝ)<cost x := by
  let r := Reference.diagonalReference
  let l := min x r
  let u := max x r
  have hr := Reference.diagonal_reference
  have hX : x∈Icc l u := ⟨min_le_left _ _,le_max_left _ _⟩
  have hR : r∈Icc l u := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom : ∀t∈Icc l u,Domain t := by
    intro t ht
    have hti : t∈Icc start (7/10) :=
      ⟨(le_min hx.1.1 hr.1.1.1).trans ht.1,ht.2.trans (max_le hx.1.2 hr.1.1.2)⟩
    refine ⟨hti,?_⟩
    rcases le_total x r with he | he
    · have hxt : x≤t := by simpa [l,min_eq_left he] using ht.1
      exact hx.2.trans (height_monotone hx.1 hti hxt)
    · have hrt : r≤t := by simpa [l,min_eq_right he] using ht.1
      exact hr.1.2.trans (height_monotone hr.1.1 hti hrt)
  have hh := curvature_tangent (f := cost) (d := first) (dd := second)
    (κ := (1/30:ℝ)) hX hR
    (fun t ht => cost_hasDerivAt (hdom t ht))
    (fun t ht => first_hasDerivAt (hdom t ht))
    (fun t ht => (curvature (hdom t ht)).le)
  have hs := abs_lt.mp hr.2.2
  have hsquare := sq_nonneg ((x-r)/30+first r)
  have hsmall : (first r)^2<(1/1000000:ℝ)^2 := by nlinarith
  nlinarith [hr.2.1]

theorem original_lower {B x : ℝ} (hd : SameZero.Domain B x)
    (he : b B x=outerDiagonal) : (89777/100000:ℝ)<value PLabel JLabel B x := by
  obtain ⟨hx,hB⟩ := original_coordinates hd he
  have hh := lower hx
  dsimp [cost] at hh
  rw [hB] at hh
  simpa [value,he] using hh

end SquaresInCircles.Eight.SecondWord.SameZero.PJ.Diagonal
end
end
end

section
/-!
## The P/J stationary point is not an interior contact minimum

The inverse angle gives an open interval of feasible contacts through the putative minimum. The
fixed direction `(1,-.7)` has uniformly negative second derivative on a neighborhood,
contradicting the one-variable minimum theorem (`interior_not_minimum`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma lineSecond_continuousAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    ContinuousAt (lineSecond s B) t := by
  have hz := inverse_data hs hB
  have hd := NegativeTwo.ContactInverse.data hB hz
  have hq0 : NegativeTwo.Inverse.q (U (B-(7/10)*t))≠0 := by
    linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have hu0 : U (B-(7/10)*t)≠0 := hd.1.ne'
  have hv0 : NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t)≠0 :=
    hd.2.2.2.2.1.ne'
  have hS : ContinuousAt (fun y : ℝ => s+y) t := by fun_prop
  have hT : ContinuousAt (fun y : ℝ => B-(7/10)*y) t := by fun_prop
  have hZ : ContinuousAt (fun y : ℝ => s+y-1/2) t := by fun_prop
  have hP0 := ContinuousAt.comp (x := t) (PLabel.d2_hasDerivAt (outer_domain hs)).continuousAt hS
  have hP : ContinuousAt (fun y => PLabel.d2 (s+y)) t := hP0
  have hJ0 := ContinuousAt.comp (x := t) (JLabel.d2_hasDerivAt (outer_domain hB)).continuousAt hT
  have hJ : ContinuousAt (fun y => JLabel.d2 (B-(7/10)*y)) t := hJ0
  have hU0 := ContinuousAt.comp (x := t) ((ShortOuterOne.SameContact.arc_hasDerivAt
    (outer_domain hB)).add_const (1/2)).continuousAt hT
  have hU : ContinuousAt (fun y => U (B-(7/10)*y)) t := hU0
  have hR0 := ContinuousAt.comp (x := t)
    (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).continuousAt hT
  have hR : ContinuousAt (fun y => ratio (B-(7/10)*y)) t := hR0
  have hQ : ContinuousAt (fun y => NegativeTwo.Inverse.q (U (B-(7/10)*y))) t :=
    continuousAt_const.sub (continuousAt_const.mul hU)
  have hV : ContinuousAt
      (fun y => NegativeTwo.ContactInverse.speed (s+y-1/2) (B-(7/10)*y)) t :=
    (hQ.sub (hZ.pow 2)).sqrt
  have hN : ContinuousAt (fun y => NegativeTwo.Inverse.N (U (B-(7/10)*y))) t :=
    ((continuousAt_const.mul hU).sub (continuousAt_const.mul (hU.pow 2))).sub
      continuousAt_const
  have hFD : ContinuousAt (fun y => NegativeTwo.Inverse.factorD (U (B-(7/10)*y))) t :=
    hN.div ((hU.pow 2).mul (hQ.pow 2)) (mul_ne_zero (pow_ne_zero 2 hu0) (pow_ne_zero 2 hq0))
  have hbrace : ContinuousAt (fun y => NegativeTwo.Inverse.brace (U (B-(7/10)*y))
      (ratio (B-(7/10)*y)) (NegativeTwo.ContactInverse.speed (s+y-1/2) (B-(7/10)*y))) t :=
    ((continuousAt_const.div (hU.pow 3) (pow_ne_zero 3 hu0)).sub
      ((continuousAt_const.mul (hR.pow 2)).div hQ hq0)).sub
        ((hR.pow 2).div (hV.pow 2) (pow_ne_zero 2 hv0))
  have hIT : ContinuousAt (fun y => PJCritical.inverseTarget (U (B-(7/10)*y))
      (ratio (B-(7/10)*y)) (s+y-1/2)
        (NegativeTwo.ContactInverse.speed (s+y-1/2) (B-(7/10)*y))) t :=
    (hR.neg.mul hFD).add ((hZ.div (hQ.mul hV) (mul_ne_zero hq0 hv0)).mul hbrace)
  have hIDS : ContinuousAt (fun y => inverseDirectionSecond (s+y) (B-(7/10)*y)) t :=
    ((hZ.add (continuousAt_const.mul hR)).neg.div (hV.pow 3) (pow_ne_zero 3 hv0)).add
      (continuousAt_const.mul hIT)
  exact (hIDS.add hP).sub (continuousAt_const.mul hJ)

theorem interior_not_minimum {B x : ℝ}
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hs : b B x∈Ioo 0 outerDiagonal)
    (hmin : ∀C y, Domain C y → value PLabel JLabel B x≤value PLabel JLabel C y) : False := by
  have hd : Domain B x :=
    ⟨Ioo_subset_Icc_self hB,Ioo_subset_Icc_self hx,Ioo_subset_Icc_self hs⟩
  have hbcont : Continuous (b B) :=
    continuous_iff_continuousAt.2 fun t => (b_angle_hasDerivAt B t).continuousAt
  let O : Set ℝ := Ioo 0 (7/10) ∩ (b B) ⁻¹' Ioo 0 outerDiagonal
  have hO : IsOpen O := isOpen_Ioo.inter (isOpen_Ioo.preimage hbcont)
  have hlocal : IsLocalMin (value PLabel JLabel B) x := by
    filter_upwards [hO.mem_nhds (show x∈O from ⟨hx,hs⟩)] with y hy
    exact hmin B y ⟨hd.1,Ioo_subset_Icc_self hy.1,Ioo_subset_Icc_self hy.2⟩
  have hstat : angleFirst PLabel B x=0 :=
    hlocal.hasDerivAt_eq_zero (value_angle_hasDerivAt PLabel JLabel hd)
  have hnegative := stationary_line_negative hd hstat
  let s := b B x
  let κ := -lineSecond s B 0/2
  have hk : 0<κ := by dsimp [κ,s]; linarith
  have hS : ContinuousAt (fun t : ℝ => s+t) 0 := by fun_prop
  have hT : ContinuousAt (fun t : ℝ => B-(7/10)*t) 0 := by fun_prop
  have hs0 : s+0∈Icc 0 outerDiagonal := by rw [add_zero]; exact hd.2.2
  have hB0 : B-(7/10)*0∈Icc 0 outerDiagonal := by rw [mul_zero,sub_zero]; exact hd.1
  have hI := (inverse_line_hasDerivAt (s := s) (B := B) (t := 0) hs0 hB0).continuousAt
  have hSecond := lineSecond_continuousAt (s := s) (B := B) (t := 0) hs0 hB0
  have hi0 : inverseAngle (s+0) (B-(7/10)*0)=x := by
    rw [add_zero,mul_zero,sub_zero]
    exact inverse_original hd
  have hSource : ∀ᶠ t in 𝓝 (0:ℝ), s+t∈Ioo 0 outerDiagonal :=
    hS.tendsto.eventually (isOpen_Ioo.mem_nhds (by rw [add_zero]; exact hs))
  have hTarget : ∀ᶠ t in 𝓝 (0:ℝ), B-(7/10)*t∈Ioo 0 outerDiagonal :=
    hT.tendsto.eventually (isOpen_Ioo.mem_nhds (by rw [mul_zero,sub_zero]; exact hB))
  have hAngle : ∀ᶠ t in 𝓝 (0:ℝ), inverseAngle (s+t) (B-(7/10)*t)∈Ioo 0 (7/10) :=
    hI.tendsto.eventually (isOpen_Ioo.mem_nhds (by rw [hi0]; exact hx))
  have hCurvature : ∀ᶠ t in 𝓝 (0:ℝ), lineSecond s B t< -κ :=
    hSecond.tendsto.eventually (eventually_lt_nhds (by dsimp [κ,s]; linarith))
  have hN : {t | s+t∈Ioo 0 outerDiagonal ∧ B-(7/10)*t∈Ioo 0 outerDiagonal ∧
      inverseAngle (s+t) (B-(7/10)*t)∈Ioo 0 (7/10) ∧ lineSecond s B t< -κ}∈𝓝 (0:ℝ) := by
    filter_upwards [hSource,hTarget,hAngle,hCurvature] with t ht hu hv hw
    exact ⟨ht,hu,hv,hw⟩
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hN
  apply not_minimum_on_strictly_concave_curve
    (s := {p : ℝ×ℝ | Domain p.1 p.2})
    (cost := fun p : ℝ×ℝ => value PLabel JLabel p.1 p.2)
    (p := (B,x)) (fun p hp => hmin p.1 p.2 hp)
    (curve := fun t : ℝ => (B-(7/10)*t,inverseAngle (s+t) (B-(7/10)*t)))
    (value := lineValue s B) (dvalue := lineFirst s B) (ddvalue := lineSecond s B)
    (O := Metric.ball 0 ε) Metric.isOpen_ball
    (show (0:ℝ)∈Metric.ball 0 ε by simpa using hε) hk
  · show (B-(7/10)*0,inverseAngle (s+0) (B-(7/10)*0))=(B,x)
    rw [hi0,mul_zero,sub_zero]
  · intro t ht
    have hh := hsub ht
    refine ⟨Ioo_subset_Icc_self hh.2.1,Ioo_subset_Icc_self hh.2.2.1,?_⟩
    show b (B-(7/10)*t) (inverseAngle (s+t) (B-(7/10)*t))∈Icc 0 outerDiagonal
    rw [inverse_contact (Ioo_subset_Icc_self hh.1) (Ioo_subset_Icc_self hh.2.1)]
    exact Ioo_subset_Icc_self hh.1
  · intro t ht
    have hh := hsub ht
    show value PLabel JLabel (B-(7/10)*t) (inverseAngle (s+t) (B-(7/10)*t))=_
    dsimp only [lineValue,inverseValue,value]
    rw [inverse_contact (Ioo_subset_Icc_self hh.1) (Ioo_subset_Icc_self hh.2.1)]
  · intro t ht
    exact lineValue_hasDerivAt (Ioo_subset_Icc_self (hsub ht).1)
      (Ioo_subset_Icc_self (hsub ht).2.1)
  · intro t ht
    exact lineFirst_hasDerivAt (Ioo_subset_Icc_self (hsub ht).1)
      (Ioo_subset_Icc_self (hsub ht).2.1)
  · intro t ht
    exact (hsub ht).2.2.2.le

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma target_strict {B x : ℝ} (hd : Domain B x) : B<outerDiagonal := by
  by_contra! hn
  have he : B=outerDiagonal := le_antisymm hd.1.2 hn
  have hh := b_angle_antitone hd.1 hd.2.1 (by norm_num : (7/10:ℝ)∈Icc 0 (7/10)) hd.2.1.2
  have ht := positive_trig (by norm_num : (7/10:ℝ)∈Icc 0 (7/10))
  have h1 := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    ht.1.le (by norm_num) (by linarith [fine_outer_endpoint_bounds.2] : 0≤outerDiagonal+1/2)
  have h2 := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith [outer_endpoint_bounds.2.2.2])
    ht.2.2.2.1.le ht.2.2.1 (by norm_num)
  have hb : b B x≤outerDiagonal := hd.2.2.2
  rw [he] at hh hb
  simp only [b,ShortOuterOne.SameContact.arc_diagonal] at hh hb
  linarith [outer_endpoint_bounds.2.2.2]

lemma angle_positive {B x : ℝ} (hd : Domain B x) : 0<x := by
  by_contra! hn
  have he : x=0 := le_antisymm hn hd.2.1.1
  have hh := hd.2.2.2
  rw [he] at hh
  norm_num [b] at hh
  linarith [hd.1.1,outer_endpoint_bounds.2.2.2]

theorem whole_contact_lower {B x : ℝ} (hd : Domain B x) :
    (89777/100000:ℝ)<value PLabel JLabel B x := by
  let guard : ℝ×ℝ→ℝ := fun p => outerDiagonal-b p.1 p.2
  let cost : ℝ×ℝ→ℝ := fun p => value PLabel JLabel p.1 p.2
  have hg : Continuous guard := by dsimp [guard,b,arc]; fun_prop
  have hc : Continuous cost := by dsimp [cost,value,RoleLabel.outer,RoleLabel.eval,b,arc]; fun_prop
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg hc
    (p₀ := (B,x)) ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2.2⟩
  have hpd : Domain p.1 p.2 := ⟨hp.1,hp.2.1,
    ⟨by linarith [b_lower hp.1 hp.2.1],sub_nonneg.mp hp.2.2⟩⟩
  have hboundary : p.1=0 ∨ b p.1 p.2=outerDiagonal ∨ p.2=7/10 := by
    by_contra hn
    simp only [not_or] at hn
    apply interior_not_minimum
      ⟨lt_of_le_of_ne hpd.1.1 (Ne.symm hn.1),target_strict hpd⟩
      ⟨angle_positive hpd,lt_of_le_of_ne hpd.2.1.2 hn.2.2⟩
      ⟨by linarith [b_lower hp.1 hp.2.1],lt_of_le_of_ne hpd.2.2.2 hn.2.1⟩
    intro C y hCy
    exact hmin (C,y) hCy.1 hCy.2.1 (sub_nonneg.mpr hCy.2.2.2)
  have hlower : (89777/100000:ℝ)<value PLabel JLabel p.1 p.2 := by
    rcases hboundary with hzero | hdiag | hcap
    · simpa [hzero] using zero_boundary_lower (by simpa [hzero] using hpd)
    · exact Diagonal.original_lower hpd hdiag
    · simpa [hcap] using cap_boundary_lower (by simpa [hcap] using hpd)
  exact hlower.trans_le hbetter

theorem original_primary {a b₀ A B x : ℝ} (hs : OuterState a b₀)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b₀ A B 1 1 x) :
    (89777/100000:ℝ)<x+PLabel.eval a b₀-JLabel.eval A B := by
  obtain ⟨hd,hcut⟩ := original_contact hs ht hx hm
  have hmono : MonotoneOn PLabel.outer (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (PLabel.outer_hasDerivAt (outer_domain ht)).continuousAt.continuousWithinAt)
      (fun t ht => PLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht)))
      (fun t ht => by linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1])
  have hsource := hmono hd.2.2 ⟨hs.1,(outer_bounds hs).2.2.2.1⟩ hcut
  rw [PLabel.outer_actual hs] at hsource
  have hh := whole_contact_lower hd
  dsimp [value] at hh
  rw [JLabel.outer_actual ht] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end
