module

public import SquaresInCircles.Eight.TableFree.DirectNegativeEAlignment

/-!
# Advancing the negative D/T contact while E is above D

Uncompiled source. Reflection is used only for the E-independent D/T/B
contact formulas. The retained mixed inequalities are the original DE2/3
projections with the original nonpositive E. A compact argument reaches
actual BT2 or actual DE alignment, and positive frame movement buys strict
slack in the original DE witness on D's own retained circle.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree
namespace DirectNegativeT
open AlignedNegative PrimaryCap

abbrev Source (q t : ℝ) (D T B : SignedPoint) : Prop :=
  AlignedNegative.Source q t D.reflect T.reflect B.reflect

def Dpath (qD P x : ℝ) : SignedPoint := (movingAnchor qD P x).reflect
def Tpath (P x : ℝ) : SignedPoint := (point P x).reflect

def positiveDESlack (qD P e : ℝ) (E : SignedPoint) (j : Fin 4) (x : ℝ) : ℝ :=
  if j=2 then lowMixedSlack qD P e E.reflect x else highMixedSlack qD P e E.reflect x

def positiveDEDerivative (qD P e : ℝ) (E : SignedPoint) (j : Fin 4) (x : ℝ) : ℝ :=
  if j=2 then lowMixedDerivative qD P e x else highMixedDerivative qD P e E.reflect x

theorem short_original_e_rate {a b d : ℝ}
    (ha : a<283/200) (hb : 0≤b) (hd : d∈Icc 0 (21/100 : ℝ)) :
    (a-1/2)*Real.cos d+(1/2-b)*Real.sin d<1249/1250 := by
  let f : ℝ → ℝ := fun x => (183/200)*Real.cos x+(1/2)*Real.sin x
  have hfder (x : ℝ) : HasDerivAt f (-(183/200)*Real.sin x+(1/2)*Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (183/200)).add
      ((Real.hasDerivAt_sin x).const_mul (1/2)) using 1 <;> simp [f] <;> ring
  have hmono : MonotoneOn f (Icc 0 (21/100 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg (by dsimp [f]; fun_prop)
      (fun x _ => hfder x)
    intro x hx
    have hs : Real.sin x≤21/100 :=
      ((le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_pos hx.1))).trans hx.2.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hx.1.le hx.2.le 2
    nlinarith
  have hendpoint : f (21/100)<1249/1250 := by
    have hc := cos_upper_four (show (0:ℝ)≤21/100 by norm_num)
    have hs := sin_upper_five (show (0:ℝ)≤21/100 by norm_num)
    dsimp [f]
    norm_num at hc hs
    linarith
  have hfd := hmono hd ⟨by norm_num,le_rfl⟩ hd.2
  have ht := transport_trig (show d∈Icc 0 (7/10 : ℝ) from ⟨hd.1,by linarith [hd.2]⟩)
  have hprim := mul_lt_mul_of_pos_right (show a-1/2<183/200 by linarith)
    (show 0<Real.cos d by linarith [ht.1])
  have htan := mul_le_mul_of_nonneg_right (show 1/2-b≤(1/2:ℝ) by linarith) ht.2.2.1
  dsimp [f] at hfd hendpoint
  linarith

theorem Source.primary_gain {q t x : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (hq : q≤qCap) (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0) :
    1<primaryGain D.circle (B.a-1/2) x := by
  let J := I.atAngle hq hx hnot
  have hcuts := J.cuts hq
  have hgeom := I.path_geometry hq ⟨hx.1.le,hx.2⟩
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  have hR : intrinsic (value (B.a-1/2) x) x<qCap := by
    simpa [point,SignedPoint.reflect] using hcuts.2.2.2.2.2.2.1.trans_le hq
  simpa [primaryGain] using circle_primary_gain
    ⟨hD.1,hD.2.1.le⟩ ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ hR
    (I.H_contained.trans hq) hgeom.2.2.2.2.2.2

theorem positiveDESlack_actual {qD P e x : ℝ} (E : SignedPoint)
    (j : Fin 4) (hj : j=2 ∨ j=3) (he : e+x∈Icc 0 (7/10 : ℝ)) :
    positiveDESlack qD P e E j x=
      quarterProjection (Dpath qD P x) E (e+x) j-edgeWidth (e+x) := by
  rcases hj with rfl | rfl
  · have hp := quarterProjection_reflect (Dpath qD P x) E (e+x) 2
    have heq : quarterProjection E.reflect (movingAnchor qD P x) (e+x) 0=
        quarterProjection (Dpath qD P x) E (e+x) 2 := by
      simpa [Dpath,reflectedOwner] using hp
    simpa [positiveDESlack,heq] using lowMixedSlack_actual (qH := qD) (P := P) E.reflect he
  · have hp := quarterProjection_reflect (Dpath qD P x) E (e+x) 3
    have heq : quarterProjection E.reflect (movingAnchor qD P x) (e+x) 1=
        quarterProjection (Dpath qD P x) E (e+x) 3 := by
      simpa [Dpath,reflectedOwner] using hp
    simpa [positiveDESlack,heq] using highMixedSlack_actual (qH := qD) (P := P) E.reflect he

theorem positiveDESlack_hasDerivAt {qD P e x : ℝ} (E : SignedPoint) (j : Fin 4)
    (hc : Real.cos x≠0) (hrad : 0<qD-(2-value P x)^2) :
    HasDerivAt (positiveDESlack qD P e E j) (positiveDEDerivative qD P e E j x) x := by
  by_cases hj : j=2
  · simpa [positiveDESlack,positiveDEDerivative,hj] using
      lowMixedSlack_hasDerivAt (e := e) E.reflect hc hrad
  · simpa [positiveDESlack,positiveDEDerivative,hj] using
      highMixedSlack_hasDerivAt (e := e) E.reflect hc hrad

theorem Source.positive_de_derivative {q t e x : ℝ} {D T B E : SignedPoint}
    (I : Source q t D T B) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore) (hEy : E.y≤0)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0)
    (he : e+x∈Icc 0 (21/100 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3) :
    positiveDEDerivative D.circle (B.a-1/2) e E j x< -(1/1250) := by
  rcases hj with rfl | rfl
  · have hh := I.lowMixedDerivative_negative hq hx hnot
      (show e+x∈Icc 0 (7/10 : ℝ) from ⟨he.1,by linarith [he.2]⟩)
    simpa [positiveDEDerivative] using hh.trans (by norm_num : -(3/50 : ℝ)< -(1/1250))
  · have hgain := I.primary_gain hq hx hnot
    have ha := (SignedPoint.coordinate_bounds hEs hEcore hEc hq).2.1
    have hrate := short_original_e_rate ha (neg_nonneg.mpr hEy) he
    simp only [positiveDEDerivative,show (3:Fin 4)≠2 by decide,ite_false,
      highMixedDerivative,SignedPoint.reflect]
    linarith

private theorem exists_left_improvement {f : ℝ → ℝ} {l m d : ℝ}
    (hd : HasDerivAt f d m) (hneg : d<0) (hlm : l<m) :
    ∃ x, x∈Ioo l m ∧ f m<f x := by
  have hf : HasDerivAt f d (-(-m)) := by simpa using hd
  have hg : HasDerivAt (fun z => f (-z)) (-d) (-m) := by
    simpa using hf.comp (-m) (hasDerivAt_id (-m)).neg
  have hbetter := NegativeContact.eventually_right_gt hg (neg_pos.mpr hneg)
  have hbound : ∀ᶠ z in 𝓝[>] (-m), z< -l :=
    (eventually_lt_nhds (show -m< -l by linarith)).filter_mono nhdsWithin_le_nhds
  obtain ⟨z,hz,hbound,hbetter⟩ :=
    (self_mem_nhdsWithin.and (hbound.and hbetter)).exists
  exact ⟨-z,⟨by linarith,by linarith⟩,by simpa using hbetter⟩

structure PositiveDEStop {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (E : SignedPoint) (e : ℝ) (j : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  error_mem : e+angle∈Icc 0 (7/10 : ℝ)
  mixed_strict : 0<positiveDESlack D.circle (B.a-1/2) e E j angle
  terminal : quarterFeasible (point (B.a-1/2) angle) B.reflect (-angle) 0 ∨ e+angle=0

/-- Positive movement stops only at an actually available BT2 axis or at
actual DE alignment, with strict original-DE slack in both alternatives. -/
theorem Source.positive_de_stop {q t e : ℝ} {D T B E : SignedPoint}
    (I : Source q t D T B) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore) (hEy : E.y≤0)
    (he : e+t∈Ioc 0 (21/100 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3)
    (hf : quarterFeasible D E (e+t) j) : Nonempty (PositiveDEStop I E e j) := by
  let P := B.a-1/2
  let L : ℝ → ℝ := positiveDESlack D.circle P e E j
  let l := max 0 (-e)
  let k : ℝ := 1/2500
  let F : ℝ → ℝ := fun x => L x-L t-k*(t-x)
  have hlt : l<t := max_lt_iff.mpr ⟨I.tilt_pos,by linarith [he.1]⟩
  have hl0 : 0≤l := le_max_left _ _
  have hlE : -e≤l := le_max_right _ _
  have hewide : |e+t|≤7/10 := by
    rw [abs_of_pos he.1]
    linarith [he.2]
  have hLstart : 0≤L t := by
    have hraw := (quarterFeasible_reflect D E (e+t) j).2 hf
    have hj' : reflectedOwner j=0 ∨ reflectedOwner j=1 := by
      rcases hj with rfl | rfl <;> norm_num [reflectedOwner]
    have hnormalized := (I.normalize hq).retains_mixed hq hewide hj' hraw
    rw [(I.normalize hq).H_eq] at hnormalized
    have hback : quarterFeasible (Dpath D.circle P t) E (e+t) j := by
      apply (quarterFeasible_reflect (Dpath D.circle P t) E (e+t) j).1
      simpa [Dpath,P] using hnormalized
    dsimp [L]
    rw [positiveDESlack_actual E j hj ⟨he.1.le,by linarith [he.2]⟩]
    exact sub_nonneg.mpr hback
  let clamp : ℝ → ℝ := fun x => max l (min t x)
  have hclamp (x : ℝ) : clamp x∈Icc l t :=
    ⟨le_max_left _ _,max_le hlt.le (min_le_left _ _)⟩
  have hclamp_eq {x : ℝ} (hx : x∈Icc l t) : clamp x=x := by
    simp [clamp,min_eq_right hx.2,max_eq_right hx.1]
  have hcclamp : Continuous clamp := by dsimp [clamp]; fun_prop
  have hcosclamp (x : ℝ) : Real.cos (clamp x)≠0 := by
    apply (transport_cos_pos (x := clamp x) ?_).ne'
    rw [abs_of_nonneg (hl0.trans (hclamp x).1)]
    exact (hclamp x).2.trans I.tilt_cap
  have hvalue : Continuous (fun x => value P (clamp x)) := by
    unfold value
    exact (continuous_const.sub (continuous_const.mul
      (Real.continuous_sin.comp hcclamp))).div
      (Real.continuous_cos.comp hcclamp) hcosclamp
  have hcF : Continuous (fun x => F (clamp x)) := by
    dsimp [F,L,positiveDESlack,lowMixedSlack,highMixedSlack,movingAnchor,anchorAt]
    split_ifs <;> fun_prop
  let S : Set ℝ := Icc l t ∩ {x | 0≤F (clamp x)}
  have hcompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hcF)
  have htS : t∈S := by
    refine ⟨⟨hlt.le,le_rfl⟩,?_⟩
    rw [hclamp_eq ⟨hlt.le,le_rfl⟩]
    simp [F]
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_isMinOn ⟨t,htS⟩ continuous_id.continuousOn
  have hmint : m∈Icc l t := hm.1
  have hm0 : 0≤m := hl0.trans hmint.1
  have hFm : 0≤F m := by simpa only [hclamp_eq hmint] using hm.2
  have hem : e+m∈Icc 0 (21/100 : ℝ) := by constructor <;> linarith [hmint.1,hmint.2,he.2]
  have hstop : quarterFeasible (point P m) B.reflect (-m) 0 ∨ e+m=0 := by
    by_cases hhard : quarterFeasible (point P m) B.reflect (-m) 0
    · exact Or.inl hhard
    right
    by_contra hne
    have hmpos : 0<m := by
      apply lt_of_le_of_ne hm0
      intro hzero
      have hprimary : quarterFeasible (point P 0) B.reflect 0 1 := by
        simpa using (actual_primary_contact
          (show B.reflect.a=P+1/2 by dsimp [P,SignedPoint.reflect]; ring)
          (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
      exact hhard (by simpa [← hzero] using (quarter_low_tie (point P 0) B.reflect).2 hprimary)
    have hlm : l<m := by
      apply max_lt_iff.mpr
      exact ⟨hmpos,by have hh := lt_of_le_of_ne hem.1 (Ne.symm hne); linarith⟩
    have hgeom := I.path_geometry hq ⟨hm0,hmint.2⟩
    have hc : Real.cos m≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hm0]; exact hmint.2.trans I.tilt_cap)).ne'
    have hdL := positiveDESlack_hasDerivAt (qD := D.circle) (P := P) (e := e) E j hc
      (by simpa using hgeom.2.2.2.2.2.2)
    have hdF : HasDerivAt F (positiveDEDerivative D.circle P e E j m+k) m := by
      convert (hdL.sub_const (L t)).sub
        (((hasDerivAt_id m).const_sub t).const_mul k) using 1 <;> simp [F,L] <;> ring
    have hneg : positiveDEDerivative D.circle P e E j m+k<0 := by
      have hh := I.positive_de_derivative hq hEs hEc hEcore hEy
        ⟨hmpos,hmint.2⟩ hhard hem j hj
      dsimp [P,k]
      linarith
    obtain ⟨x,hx,hbetter⟩ := exists_left_improvement hdF hneg hlm
    have hxt : x∈Icc l t := ⟨hx.1.le,hx.2.le.trans hmint.2⟩
    have hxS : x∈S := by
      refine ⟨hxt,?_⟩
      rw [hclamp_eq hxt]
      exact hFm.trans hbetter.le
    have hh : m≤x := hmin hxS
    linarith [hx.2]
  have hmt : m<t := by
    apply lt_of_le_of_ne hmint.2
    intro hmeq
    rcases hstop with hhard | hzero
    · have hn := (I.normalize hq).source.no_hard
      rw [(I.normalize hq).G_eq] at hn
      exact hn (by simpa [P,hmeq] using hhard)
    · linarith [he.1]
  have hstrict : 0<L m := by
    have hgrowth := mul_pos (show 0<k by norm_num [k]) (sub_pos.mpr hmt)
    dsimp [F] at hFm
    linarith
  exact ⟨⟨m,⟨hm0,hmt⟩,⟨hem.1,by linarith [hem.2]⟩,hstrict,hstop⟩⟩

end DirectNegativeT
end SquaresInCircles.Eight.TableFree
