module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroLKReference
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJZeroCap
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJMinimum
public import SquaresInCircles.Eight.Words.Wrong.ZeroOriginalOwners

/-!
# Eight squares: every original same-sign outer zero-quarter row

The P/J and L/K representatives and their reflected reversals are joined using the original
allowed role signs (`original_positive`, `original_negative`, `actual`). All weak owners are kept
through the separate G1 owner theorem.
-/

section
/-!
## The complete target-zero boundary of the L/K contact

The early part is uniformly strongly convex
at its single actual reference.  Once the source coordinate reaches
.755 the cost is increasing.  The transition point is obtained from
continuity when needed; no location or minimizer is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def zeroSecond (x : ℝ) : ℝ :=
  LLabel.d2 (b 0 x)*(v 0 x)^2-LLabel.d1 (b 0 x)*(b 0 x-1/2)

lemma zeroFirst_hasDerivAt {x : ℝ} (hd : Domain 0 x) :
    HasDerivAt (angleFirst LLabel 0) (zeroSecond x) x := by
  have hh := (((LLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp x
    (b_angle_hasDerivAt 0 x)).fun_mul (v_angle_hasDerivAt 0 x)).const_sub 1
  exact hh.congr_deriv (by simp only [Function.comp_apply,zeroSecond]; ring)

lemma zero_curvature {x : ℝ} (hd : Domain 0 x) (hb : 151/200≤b 0 x) :
    (1:ℝ)<zeroSecond x := by
  have href : (151/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hL2 := second_right.trans_le (L_second_monotone href hd.2.2 hb)
  have hL := (L_first_bounds hd.2.2).2
  have hz : (b 0 x-1/2)∈Icc 0 (2/5) := by
    constructor <;> linarith [hd.2.2.2,outer_endpoint_bounds.2.2.2]
  have hn := norm_identity outer_zero_mem x
  norm_num [NegativeTwo.Inverse.q,U,ShortOuterOne.SameContact.arc_zero,Q0] at hn
  have hv2 : (579/625:ℝ)<(v 0 x)^2 := by
    nlinarith [ShortOuterZero.fine_axial_bounds.2,
      pow_le_pow_left₀ hz.1 hz.2 2]
  have hp := mul_lt_mul'' hL2 hv2 (by norm_num : (0:ℝ)≤167/100)
    (by norm_num : (0:ℝ)≤579/625)
  have hq := mul_le_mul hL.le hz.2 hz.1 (by norm_num : (0:ℝ)≤147/125)
  dsimp [zeroSecond]
  linarith

lemma zero_first_late {x : ℝ} (hd : Domain 0 x) (hb : b 0 x≤151/200) :
    0<angleFirst LLabel 0 x := by
  have hL := first_middle ⟨(b_lower outer_zero_mem hd.2.1).le,hb⟩
  have hv := v_upper outer_zero_mem hd.2.1
  have hp := mul_lt_mul hL hv.le (v_positive outer_zero_mem hd.2.1)
    (by norm_num : (0:ℝ)≤817/1000)
  dsimp [angleFirst]
  norm_num at hp
  linarith

lemma zero_early_lower {x : ℝ} (hd : Domain 0 x) (hb : 151/200≤b 0 x) :
    (89777/100000:ℝ)<value LLabel KLabel 0 x := by
  let l := min x reference
  let u := max x reference
  have hx : x∈Icc l u := ⟨min_le_left _ _,le_max_left _ _⟩
  have hr : reference∈Icc l u := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom : ∀t∈Icc l u,Domain 0 t ∧ 151/200≤b 0 t := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := by
      dsimp [l,u] at ht
      constructor
      · exact (le_min hd.2.1.1 reference_domain.1.2.1.1).trans ht.1
      · exact ht.2.trans (max_le hd.2.1.2 reference_domain.1.2.1.2)
    have hblo : 151/200≤b 0 t := by
      rcases le_total x reference with he | he
      · have htt : t≤reference := by simpa [u,max_eq_right he] using ht.2
        exact reference_domain.2.le.trans
          (b_angle_antitone outer_zero_mem hti reference_domain.1.2.1 htt)
      · have htt : t≤x := by simpa [u,max_eq_left he] using ht.2
        exact hb.trans (b_angle_antitone outer_zero_mem hti hd.2.1 htt)
    have hbhi : b 0 t≤outerDiagonal := by
      rcases le_total x reference with he | he
      · have htt : x≤t := by simpa [l,min_eq_left he] using ht.1
        exact (b_angle_antitone outer_zero_mem hd.2.1 hti htt).trans hd.2.2.2
      · have htt : reference≤t := by simpa [l,min_eq_right he] using ht.1
        exact (b_angle_antitone outer_zero_mem reference_domain.1.2.1 hti htt).trans
          reference_domain.1.2.2.2
    exact ⟨⟨outer_zero_mem,hti,⟨by linarith,hbhi⟩⟩,hblo⟩
  have ht := curvature_tangent (f := value LLabel KLabel 0)
    (d := angleFirst LLabel 0) (dd := zeroSecond) (κ := (1:ℝ)) hx hr
    (fun t ht => value_angle_hasDerivAt LLabel KLabel (hdom t ht).1)
    (fun t ht => zeroFirst_hasDerivAt (hdom t ht).1)
    (fun t ht => (zero_curvature (hdom t ht).1 (hdom t ht).2).le)
  have hslope := abs_lt.mp reference_value.2
  have hs2 : (angleFirst LLabel 0 reference)^2<(3/1000000:ℝ)^2 := by
    nlinarith
  have hs := sq_nonneg (x-reference+angleFirst LLabel 0 reference)
  nlinarith [reference_value.1]

theorem zero_boundary_lower {x : ℝ} (hd : Domain 0 x) :
    (89777/100000:ℝ)<value LLabel KLabel 0 x := by
  by_cases hb : 151/200≤b 0 x
  · exact zero_early_lower hd hb
  have hlow : b 0 x<151/200 := lt_of_not_ge hb
  have horder : reference≤x := by
    by_contra! hn
    have hh := b_angle_antitone outer_zero_mem hd.2.1 reference_domain.1.2.1 hn.le
    linarith [reference_domain.2]
  have hc : Continuous (b 0) :=
    continuous_iff_continuousAt.2 fun t => (b_angle_hasDerivAt 0 t).continuousAt
  obtain ⟨y,hy,he⟩ := intermediate_value_Icc horder hc.neg.continuousOn
    (show -(151/200:ℝ)∈Icc (-b 0 reference) (-b 0 x) by
      constructor <;> linarith [reference_domain.2])
  rw [Pi.neg_apply] at he
  have hby : b 0 y=151/200 := by linarith
  have hyi : y∈Icc 0 (7/10) :=
    ⟨reference_domain.1.2.1.1.trans hy.1,hy.2.trans hd.2.1.2⟩
  have hyd : Domain 0 y := by
    refine ⟨outer_zero_mem,hyi,?_⟩
    rw [hby]
    exact Asymmetric.rational_outer_mem (by norm_num)
  have hdom : ∀t∈Icc y x,Domain 0 t ∧ b 0 t≤151/200 := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := ⟨hyi.1.trans ht.1,ht.2.trans hd.2.1.2⟩
    have hhi := b_angle_antitone outer_zero_mem hyi hti ht.1
    have hlo := b_lower outer_zero_mem hti
    rw [hby] at hhi
    exact ⟨⟨outer_zero_mem,hti,⟨by linarith,by
      linarith [fine_outer_endpoint_bounds.2]⟩⟩,hhi⟩
  have hmono : MonotoneOn (value LLabel KLabel 0) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (value_angle_hasDerivAt LLabel KLabel (hdom t ht).1).continuousAt.continuousWithinAt)
      (fun t ht => value_angle_hasDerivAt LLabel KLabel (hdom t (Ioo_subset_Icc_self ht)).1)
      (fun t ht => (zero_first_late (hdom t (Ioo_subset_Icc_self ht)).1
        (hdom t (Ioo_subset_Icc_self ht)).2).le)
  exact (zero_early_lower hyd hby.ge).trans_le
    (hmono ⟨le_rfl,hy.2⟩ ⟨hy.2,le_rfl⟩ hy.2)

end SquaresInCircles.Eight.SecondWord.SameZero.LK
end
end
end

section
/-!
## The L/K same-sign contact minimum

Compactness is applied to the whole physical contact rectangle. A minimum with positive target
coordinate would have nonpositive target derivative. The exact derivative implication then makes
its angular derivative positive; the source diagonal and the feasible left angular direction both
contradict this. Thus the minimum is on the target-zero boundary (`minimum_target_zero`), which
is bounded separately; this gives `whole_contact_lower`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma diagonal_angle_negative {B x : ℝ} (hd : Domain B x)
    (hb : b B x=outerDiagonal) : angleFirst LLabel B x<0 := by
  have hL : (23/20:ℝ)<LLabel.d1 outerDiagonal := by
    rw [L_first_diagonal]
    linarith [outer_endpoint_bounds.2.2.2]
  have hz : outerDiagonal-1/2∈Icc (0:ℝ) (2/5) := by
    constructor <;> linarith [fine_outer_endpoint_bounds.2,
      outer_endpoint_bounds.2.2.2]
  have hn := norm_identity hd.1 x
  rw [hb] at hn
  have hv := v_positive hd.1 hd.2.1
  have hvlo : (24/25:ℝ)<v B x := by
    have hsq := pow_le_pow_left₀ hz.1 hz.2 2
    have hq := NegativeTwo.Inverse.actual_q_positive hd.1
    nlinarith
  have hp := mul_lt_mul hL hvlo.le (by norm_num : (0:ℝ)<24/25)
    (show 0≤LLabel.d1 outerDiagonal by linarith)
  dsimp [angleFirst]
  rw [hb]
  norm_num at hp
  linarith

lemma domain_angle_positive {B x : ℝ} (hd : Domain B x) : 0<x := by
  by_contra! hn
  have he : x=0 := le_antisymm hn hd.2.1.1
  have hcut := hd.2.2.2
  rw [he] at hcut
  norm_num [b] at hcut
  linarith [hd.1.1,outer_endpoint_bounds.2.2.2]

theorem minimum_target_zero {B x : ℝ} (hd : Domain B x)
    (hmin : ∀C y,Domain C y →
      value LLabel KLabel B x≤value LLabel KLabel C y) : B=0 := by
  by_contra hne
  have hB : 0<B := lt_of_le_of_ne hd.1.1 (Ne.symm hne)
  have htarget : targetFirst LLabel KLabel B x≤0 := by
    have hmax : IsMaxOn (fun C => -value LLabel KLabel C x) (Icc 0 B) B := by
      intro C hC
      have hCi : C∈Icc 0 outerDiagonal := ⟨hC.1,hC.2.trans hd.1.2⟩
      have hbhi : b C x≤b B x := b_target_monotone hd.2.1 hCi hd.1 hC.2
      have hCd : Domain C x := ⟨hCi,hd.2.1,
        ⟨by linarith [b_lower hCi hd.2.1],hbhi.trans hd.2.2.2⟩⟩
      have hh := hmin C x hCd
      change -value LLabel KLabel C x≤ -value LLabel KLabel B x
      linarith
    have hh := not_negative_at_rightward_maximum
      (show B∈Icc 0 B from ⟨hd.1.1,le_rfl⟩) hB hmax
      (value_target_hasDerivAt LLabel KLabel hd).fun_neg
    linarith
  have hangle : 0<angleFirst LLabel B x := by
    by_contra! hn
    have hh := angular_nonpos_target_pos hd hn
    linarith
  have hbstrict : b B x<outerDiagonal := by
    rcases lt_or_eq_of_le hd.2.2.2 with hh | hh
    · exact hh
    · have hn := diagonal_angle_negative hd hh
      linarith
  have hx := domain_angle_positive hd
  let O : Set ℝ := {t | 0<t ∧ b B t<outerDiagonal}
  have hbcont : Continuous (b B) :=
    continuous_iff_continuousAt.2 fun t => (b_angle_hasDerivAt B t).continuousAt
  have hO : IsOpen O := by
    change IsOpen ({t : ℝ | 0<t} ∩ {t : ℝ | b B t<outerDiagonal})
    exact (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt hbcont continuous_const)
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO
    (show x∈O from ⟨hx,hbstrict⟩)
  have hmax : IsMaxOn (fun t => -value LLabel KLabel B t) (Icc (x-ε) x) x := by
    intro y hy
    have hyO := hsub (show y∈Icc (x-ε) (x+ε) from
      ⟨hy.1,by linarith [hy.2]⟩)
    have hyi : y∈Icc 0 (7/10) := ⟨hyO.1.le,hy.2.trans hd.2.1.2⟩
    have hyd : Domain B y := ⟨hd.1,hyi,
      ⟨by linarith [b_lower hd.1 hyi],hyO.2.le⟩⟩
    have hh := hmin B y hyd
    change -value LLabel KLabel B y≤ -value LLabel KLabel B x
    linarith
  have hh := not_negative_at_rightward_maximum
    (show x∈Icc (x-ε) x by constructor <;> linarith) (by linarith : x-ε<x)
    hmax (value_angle_hasDerivAt LLabel KLabel hd).fun_neg
  linarith

theorem whole_contact_lower {B x : ℝ} (hd : Domain B x) :
    (89777/100000:ℝ)<value LLabel KLabel B x := by
  let contact : ℝ×ℝ → ℝ := fun p => outerDiagonal-b p.1 p.2
  let cost : ℝ×ℝ → ℝ := fun p => value LLabel KLabel p.1 p.2
  have hc : Continuous contact := by
    dsimp [contact,b,arc]
    fun_prop
  have hf : Continuous cost := by
    dsimp [cost,value,RoleLabel.outer,RoleLabel.eval,b,arc]
    fun_prop
  obtain ⟨p,hp,hsmall,hmin⟩ := contact_region_minimum hc hf
    (p₀ := (B,x)) (show B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧
      0≤contact (B,x) from ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2.2⟩)
  have hpd : Domain p.1 p.2 := ⟨hp.1,hp.2.1,
    ⟨by linarith [b_lower hp.1 hp.2.1],sub_nonneg.mp hp.2.2⟩⟩
  have hzero := minimum_target_zero hpd (fun C y hCy =>
    hmin (C,y) hCy.1 hCy.2.1 (sub_nonneg.mpr hCy.2.2.2))
  have hl := zero_boundary_lower (show Domain 0 p.2 by simpa [hzero] using hpd)
  change value LLabel KLabel p.1 p.2≤value LLabel KLabel B x at hsmall
  rw [hzero] at hsmall
  exact hl.trans_le hsmall

/-- The original source-secondary weak separator pays the L/K row; the only move is to the
cost-lowering contact. -/
theorem original_primary {a b₀ A B x : ℝ} (hs : OuterState a b₀)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b₀ A B 1 1 x) :
    (89777/100000:ℝ)<x+LLabel.eval a b₀-KLabel.eval A B := by
  obtain ⟨hd,hcut⟩ := original_contact hs ht hx hm
  have hsource := L_monotone hd.2.2
    (show b₀∈Icc 0 outerDiagonal from ⟨hs.1,(outer_bounds hs).2.2.2.1⟩) hcut
  change LLabel.outer (b B x)≤LLabel.outer b₀ at hsource
  dsimp [RoleLabel.outer] at hsource
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hsource
  have hh := whole_contact_lower hd
  dsimp [value,RoleLabel.outer] at hh
  rw [(ShortOuterOne.SameContact.actual_arc ht).1] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.LK
end
end
end

section
/-!
## Both original same-sign L/K zero-quarter rows

The full contact bound is restored to the
literal role-four labels.  Reflected reversal gives the negative row.
The independent G1 zero-owner theorem excludes the other original
axes, including every weak tie, before either scalar estimate is used.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.SameZero.LK
open CommonQuarter Arithmetic QuarterWordGeometry

lemma positive_cost (a b A B x : ℝ) :
    SecondWord.cost 4 .outer .outer true true a b A B x=
      x+LLabel.eval a b-KLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
    next,RoleLabel.eval,LLabel,KLabel]

theorem original_positive {a b A B x : ℝ} (hs : OuterState a b)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (89777/100000:ℝ)<SecondWord.cost 4 .outer .outer true true a b A B x := by
  rw [positive_cost]
  exact original_primary hs ht hx hm

theorem original_negative {a b A B x : ℝ} (hs : OuterState a b)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) x) :
    (89777/100000:ℝ)<SecondWord.cost 4 .outer .outer false false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 1 x := by
    simp [Eight.forwardMargin] at hm ⊢
    linarith
  have hh := original_positive ht hs hx hrev
  have he := cost_reflection (4:Vertex) .outer .outer true true A B a b x
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hsg : positiveOf C 4=positiveOf C (next 4)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square 4) (C.square (next 4))) :
    threshold 4<phaseValue F hgap 4+wrongMarker C .second 4-
      wrongMarker C .second (next 4) := by
  have hz : F.word hgap pi_lt_22_over_7 4=0 := by
    rw [hw]
    norm_num [WordProblems.wrongWord]
  have hx : |phaseValue F hgap 4|≤7/10 := by
    simpa [phaseValue,hz] using (difference_small F 4).le
  have hsource : OuterState (C.a 4) (C.b 4) := by
    simpa only [State,hs,↓reduceIte] using actual_state C 4
  have htarget : OuterState (C.a (next 4)) (C.b (next 4)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next 4)
  have hm := original_margin C F hgap 4 j howner
  have hh : (89777/100000:ℝ)<SecondWord.cost 4 .outer .outer
      (positiveOf C 4) (positiveOf C (next 4))
      (C.a 4) (C.b 4) (C.a (next 4)) (C.b (next 4)) (phaseValue F hgap 4) := by
    rcases WrongZeroOriginalOwners.original C F hgap 4 hz j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htpos : positiveOf C (next 4)=true := hsg.symm.trans hpos
      rw [hpos,htpos]
      exact original_positive hsource htarget hx
        (by simpa [hpos,htpos,WordProblems.sign] using hm)
    · have hsneg : positiveOf C 4=false := hsg.trans hneg
      rw [hsneg,hneg]
      exact original_negative hsource htarget hx
        (by simpa [hsneg,hneg,WordProblems.sign] using hm)
  rw [threshold_value]
  have he : SecondWord.cost 4 .outer .outer (positiveOf C 4)
      (positiveOf C (next 4)) (C.a 4) (C.b 4) (C.a (next 4)) (C.b (next 4))
      (phaseValue F hgap 4)=phaseValue F hgap 4+wrongMarker C .second 4-
        wrongMarker C .second (next 4) := by
    simp only [SecondWord.cost,label,wrongMarker,hs,ht]
  rw [he] at hh
  linarith

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hsg : positiveOf C 4=positiveOf C (next 4)) :
    threshold 4<phaseValue F hgap 4+wrongMarker C .second 4-
      wrongMarker C .second (next 4) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl 4 (C.selected 4) (C.feasible 4)
  have howner : (forwardAxis j).Feasible (C.square 4) (C.square (next 4)) := by
    simpa only [←hj] using C.feasible 4
  exact actual_owner C F hgap hw hs ht hsg j howner

end SquaresInCircles.Eight.SecondWord.SameZero.LK
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.SameZero
open CommonQuarter Arithmetic QuarterWordGeometry

lemma PJ_positive_cost (a b A B x : ℝ) :
    SecondWord.cost 0 .outer .outer true true a b A B x=
      x+PLabel.eval a b-JLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
    next,RoleLabel.eval,PLabel,JLabel]

theorem original_positive {i : Vertex} (hi : i=0 ∨ i=4)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    threshold i<SecondWord.cost i .outer .outer true true a b A B x := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · rw [PJ_positive_cost]
    linarith [PJ.original_primary hs ht hx hm]
  · linarith [LK.original_positive hs ht hx hm]

theorem original_negative {i : Vertex} (hi : i=1 ∨ i=4)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) x) :
    threshold i<SecondWord.cost i .outer .outer false false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 1 x := by
    simp [Eight.forwardMargin] at hm ⊢
    linarith
  have hir : reverseEdge i=0 ∨ reverseEdge i=4 := by
    rcases hi with rfl | rfl <;> norm_num [reverseEdge]
  have hh := original_positive hir ht hs hx hrev
  have he := cost_reflection i .outer .outer false false a b A B x
  norm_num at he
  rw [he,threshold_value] at hh
  simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .second hw i
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh : threshold i<SecondWord.cost i .outer .outer
      (positiveOf C i) (positiveOf C (next i)) (C.a i) (C.b i)
      (C.a (next i)) (C.b (next i)) (phaseValue F hgap i) := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htpos : positiveOf C (next i)=true := hsg.symm.trans hpos
      rw [hpos,htpos] at ha ⊢
      have hir : i=0 ∨ i=4 := by
        revert hword ha
        fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next]
      exact original_positive hir hsource htarget hx
        (by simpa [hpos,htpos,WordProblems.sign] using hm)
    · have hsneg : positiveOf C i=false := hsg.trans hneg
      rw [hsneg,hneg] at ha ⊢
      have hir : i=1 ∨ i=4 := by
        revert hword ha
        fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next]
      exact original_negative hir hsource htarget hx
        (by simpa [hsneg,hneg,WordProblems.sign] using hm)
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht hsg j
    (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.SecondWord.SameZero
end
end
end
