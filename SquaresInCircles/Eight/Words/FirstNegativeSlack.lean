module

public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1Arc
public import SquaresInCircles.Eight.Words.Aligned.NegativeAssembly
public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1

/-!
# Eight squares: strict retained mixed slack at the first GA0 contact

The first contact is selected by the GA axis, independently of the mixed slack. The low mixed
derivative integrates up to that contact (`low_mixed_slack`). For the high mixed owner, a compact
minimum rules out passage through the small-slack derivative strip (`left_sublevel_barrier`,
`high_mixed_slack`). Thus the high-anchor cuts and a strictly positive physical mixed margin hold
at the same first contact.
-/

section
/-!
## The first actual hard-axis contact of a negative primary

The actual GA0 availability is a continuous trigonometric
polynomial after multiplication by its positive cosine. Its rightmost
available point precedes the original unconverted source. The one-sided
first-contact inequality, including angle zero, retains the intrinsic
opposite-anchor circle bound and hence the high-H cuts required by the
direct second negative-primary transport.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

def hardAvailability (A : SignedPoint) (x : ℝ) : ℝ :=
  Real.sin x*(K-(A.a-1/2)*Real.sin x-(A.y+1/2)*Real.cos x)

theorem hard_availability_identity (A : SignedPoint) {x : ℝ}
    (hx : x∈Icc 0 (7/10 : ℝ)) :
    (quarterProjection (point (A.a-1/2) x) A (-x) 0-edgeWidth (-x))*Real.cos x=
      hardAvailability A x := by
  have hc : Real.cos x≠0 := (transport_cos_pos (by rw [abs_of_nonneg hx.1]; exact hx.2)).ne'
  have hcontact := value_contact_identity (A.a-1/2) x hc
  have hmargin : quarterProjection (point (A.a-1/2) x) A (-x) 0-edgeWidth (-x)=
      (A.a-1/2)*Real.cos x-(A.y+1/2)*Real.sin x-value (A.a-1/2) x := by
    rw [edgeWidth_negative_formula hx]
    simp [quarterProjection,point,Real.sin_neg,Real.cos_neg]
    ring
  rw [hmargin]
  have hzero :
      ((A.a-1/2)*Real.cos x-(A.y+1/2)*Real.sin x-value (A.a-1/2) x)*Real.cos x-
        hardAvailability A x=0 := by
    calc
      _=(A.a-1/2)*(Real.sin x^2+Real.cos x^2)-
        value (A.a-1/2) x*Real.cos x-K*Real.sin x := by dsimp [hardAvailability]; ring
      _=0 := by rw [Real.sin_sq_add_cos_sq]; linarith
  linarith

theorem hard_availability_iff (A : SignedPoint) {x : ℝ}
    (hx : x∈Icc 0 (7/10 : ℝ)) :
    quarterFeasible (point (A.a-1/2) x) A (-x) 0 ↔ 0≤hardAvailability A x := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; exact hx.2)
  have hid := hard_availability_identity A hx
  constructor
  · intro hh
    rw [← hid]
    exact mul_nonneg (sub_nonneg.mpr hh) hc.le
  · intro hh
    apply sub_nonneg.mp
    apply (mul_nonneg_iff_of_pos_right hc).1
    rwa [hid]

structure FirstHard {q t : ℝ} {H G A : SignedPoint} (I : Source q t H G A) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  hard : quarterFeasible (point (A.a-1/2) angle) A (-angle) 0
  maximal : ∀ x∈Icc 0 t, quarterFeasible (point (A.a-1/2) x) A (-x) 0 → x≤angle

theorem Source.first_hard {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) : Nonempty (FirstHard I) := by
  let S : Set ℝ := Icc 0 t ∩ {x | 0≤hardAvailability A x}
  have hc : Continuous (fun x => hardAvailability A x) := by
    simp only [hardAvailability]
    fun_prop
  have hcompact : IsCompact S := isCompact_Icc.inter_right (isClosed_le continuous_const hc)
  have hzero : (0:ℝ)∈S := by exact ⟨⟨le_rfl,I.tilt_pos.le⟩,by simp [hardAvailability]⟩
  obtain ⟨r,hr,hmax⟩ := hcompact.exists_isMaxOn ⟨0,hzero⟩ continuous_id.continuousOn
  have hrange : r∈Icc 0 t := hr.1
  have hhard := (hard_availability_iff A ⟨hrange.1,hrange.2.trans I.tilt_cap⟩).2 hr.2
  have hrt : r<t := by
    apply lt_of_le_of_ne hrange.2
    intro heq
    have hn := (I.normalize hq).source.no_hard
    rw [(I.normalize hq).G_eq] at hn
    exact hn (by simpa [heq] using hhard)
  exact ⟨{
    angle := r
    angle_mem := ⟨hrange.1,hrt⟩
    hard := hhard
    maximal := by
      intro x hx hf
      exact hmax ⟨hx,(hard_availability_iff A ⟨hx.1,hx.2.trans I.tilt_cap⟩).1 hf⟩ }⟩

namespace FirstHard

variable {q t : ℝ} {H G A : SignedPoint} {I : Source q t H G A}

theorem later_unavailable (O : FirstHard I) {x : ℝ} (hx : x∈Ioc O.angle t) :
    ¬quarterFeasible (point (A.a-1/2) x) A (-x) 0 := by
  intro hh
  have hmax := O.maximal x ⟨O.angle_mem.1.trans hx.1.le,hx.2⟩ hh
  linarith [hx.1]

/-- The one-sided inequality remains meaningful when the first contact is
at zero, where the two quarter owners coincide automatically. -/
theorem contact_vector (O : FirstHard I) :
    K≤(A.a-1/2)*Real.sin O.angle+(A.y+1/2)*Real.cos O.angle := by
  by_contra! hbad
  let f : ℝ → ℝ := fun x => K-(A.a-1/2)*Real.sin x-(A.y+1/2)*Real.cos x
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hvalue : 0<f O.angle := by dsimp [f]; linarith
  have hpos : ∀ᶠ x in 𝓝[>] O.angle, 0<f x :=
    (hf.continuousAt.tendsto.eventually (eventually_gt_nhds hvalue)).filter_mono
      nhdsWithin_le_nhds
  have hbound : ∀ᶠ x in 𝓝[>] O.angle, x<t :=
    (eventually_lt_nhds O.angle_mem.2).filter_mono nhdsWithin_le_nhds
  obtain ⟨x,hx,hxt,hfx⟩ := (eventually_mem_nhdsWithin.and (hbound.and hpos)).exists
  have hx' : O.angle<x := hx
  have hx0 : 0<x := O.angle_mem.1.trans_lt hx'
  have hs : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0
    (by linarith [I.tilt_cap,Real.pi_gt_three])
  have havail : 0≤hardAvailability A x := by
    exact (mul_pos hs hfx).le
  have hhard := (hard_availability_iff A ⟨hx0.le,hxt.le.trans I.tilt_cap⟩).2 havail
  exact O.later_unavailable ⟨hx',hxt.le⟩ hhard

theorem intrinsic_bound (O : FirstHard I) (hq : q≤qCap) :
    intrinsic (value (A.a-1/2) O.angle) O.angle≤A.circle := by
  let x := O.angle
  let Z := value (A.a-1/2) x
  let V := K*Real.cos x-Z*Real.sin x
  have hx : x∈Icc 0 (7/10 : ℝ) := ⟨O.angle_mem.1,O.angle_mem.2.le.trans I.tilt_cap⟩
  have ht := transport_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hZ := I.path_cap hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  have hcontact : Z*Real.cos x=A.a-1/2-K*Real.sin x := by
    have h := value_contact_identity (A.a-1/2) x hc.ne'
    dsimp only [Z]
    linarith
  have hvpos : 0<V := by
    have hprod := mul_le_mul (show Z≤183/200 by exact hZ.2.1.le) ht.2.2.2.1.le
      ht.2.2.1 (by norm_num : (0:ℝ)≤183/200)
    dsimp [V,K]
    nlinarith [ht.1]
  have hvidentity : V*Real.cos x=K-(A.a-1/2)*Real.sin x := by
    have hh : V*Real.cos x-(K-(A.a-1/2)*Real.sin x)=
        K*(Real.sin x^2+Real.cos x^2-1)+
          (A.a-1/2-K*Real.sin x-Z*Real.cos x)*Real.sin x := by dsimp [V]; ring
    rw [Real.sin_sq_add_cos_sq] at hh
    nlinarith
  have hvupper : V≤A.y+1/2 := by
    apply le_of_mul_le_mul_right _ hc
    rw [hvidentity]
    linarith [O.contact_vector]
  have hv2 := pow_le_pow_left₀ hvpos.le hvupper 2
  have hAid : (A.a+1/2)^2+V^2=intrinsic Z x := by
    have hXa : A.a+1/2=1+Z*Real.cos x+K*Real.sin x := by linarith
    rw [hXa]
    calc
      _=1+(Z^2+K^2)*(Real.sin x^2+Real.cos x^2)+
          2*Z*Real.cos x+2*K*Real.sin x := by dsimp [V]; ring
      _=intrinsic Z x := by rw [Real.sin_sq_add_cos_sq]; dsimp [intrinsic]; ring
  rw [SignedPoint.circle,abs_of_nonneg I.A_nonneg,← hAid]
  linarith

theorem high_anchor (O : FirstHard I) (hq : q≤qCap) :
    value (A.a-1/2) O.angle<82/125 ∧
      211/250<(movingAnchor H.circle (A.a-1/2) O.angle).y ∧
      (movingAnchor H.circle (A.a-1/2) O.angle).a<1 := by
  let x := O.angle
  let Z := value (A.a-1/2) x
  have hx : x∈Icc 0 (7/10 : ℝ) := ⟨O.angle_mem.1,O.angle_mem.2.le.trans I.tilt_cap⟩
  have hZ := I.path_cap hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  have hi : intrinsic Z x≤qCap := (O.intrinsic_bound hq).trans (I.A_contained.trans hq)
  have ht := transport_trig hx
  have hsum : 1≤Real.sin x+Real.cos x := by
    have hh := one_le_abs_cos_add_abs_sin x
    rw [abs_of_pos (by linarith [ht.1] : 0<Real.cos x),abs_of_nonneg ht.2.2.1] at hh
    linarith
  have hsupport : Z≤Z*Real.cos x+K*Real.sin x := by
    have hp := mul_nonneg (show 0≤Z by linarith [hZ.1]) (sub_nonneg.mpr hsum)
    have hm := mul_nonneg (show 0≤K-Z by dsimp [K]; linarith [hZ.2.1]) ht.2.2.1
    nlinarith
  have hbase : K^2+(Z+1)^2≤qCap := by dsimp [intrinsic] at hi; nlinarith
  have hZcut : Z<82/125 := by
    by_contra! hbad
    dsimp [K,qCap] at hbase
    nlinarith
  have hhigh : 211/250<(movingAnchor H.circle (A.a-1/2) O.angle).y := by
    dsimp [movingAnchor,anchorAt]
    linarith
  have hg := I.path_geometry hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  have hcircle : (movingAnchor H.circle (A.a-1/2) O.angle).circle≤qCap :=
    hg.2.1.le.trans (I.H_contained.trans hq)
  have ha : (movingAnchor H.circle (A.a-1/2) O.angle).a<1 := by
    by_contra! hbad
    rw [SignedPoint.circle,abs_of_pos (by linarith :
      0<(movingAnchor H.circle (A.a-1/2) O.angle).y)] at hcircle
    dsimp [qCap] at hcircle
    nlinarith
  exact ⟨hZcut,hhigh,ha⟩

end FirstHard
end AlignedNegative
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight

/-- A negative derivative on the nonpositive sublevel cannot cross upwards
from a negative left endpoint to a nonnegative right endpoint. The derivative
is needed only in the open interval. -/
theorem left_sublevel_barrier {f df : ℝ → ℝ} {l u : ℝ}
    (hlu : l<u) (hc : ContinuousOn f (Icc l u))
    (hd : ∀x∈Ioo l u, HasDerivAt f (df x) x)
    (hneg : ∀x∈Ioo l u, f x≤0 → df x<0)
    (hu : 0≤f u) : 0≤f l := by
  by_contra! hl
  obtain ⟨z,hz,hzvalue⟩ := intermediate_value_Icc hlu.le hc
    (show f l/2∈Icc (f l) (f u) by constructor <;> linarith)
  have hlz : l<z := by
    apply lt_of_le_of_ne hz.1
    intro heq
    rw [← heq] at hzvalue
    linarith
  have hzt : z<u := by
    apply lt_of_le_of_ne hz.2
    intro heq
    rw [heq] at hzvalue
    linarith
  have hsub : Icc z u⊆Icc l u := Icc_subset_Icc hz.1 le_rfl
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc z u).Nonempty from ⟨z,⟨le_rfl,hzt.le⟩⟩) (hc.mono hsub)
  have hfm : f m<0 := by
    have hh : f m≤f z := hmin (show z∈Icc z u from ⟨le_rfl,hzt.le⟩)
    linarith
  have hmu : m<u := by
    apply lt_of_le_of_ne hm.2
    intro heq
    rw [heq] at hfm
    linarith
  have hlm : l<m := hlz.trans_le hm.1
  have hbetter := NegativeContact.eventually_right_lt (hd m ⟨hlm,hmu⟩)
    (hneg m ⟨hlm,hmu⟩ hfm.le)
  have hbound : ∀ᶠ x in 𝓝[>] m, x<u :=
    (eventually_lt_nhds hmu).filter_mono nhdsWithin_le_nhds
  obtain ⟨x,hmx,hxu,hfx⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and hbetter)).exists
  have hmx' : m<x := hmx
  have hh : f m≤f x := hmin (show x∈Icc z u from ⟨hm.1.trans hmx'.le,hxu.le⟩)
  linarith

namespace AlignedNegative
open PrimaryCap
namespace FirstHard

variable {q t : ℝ} {H G A : SignedPoint} {I : Source q t H G A}

theorem low_mixed_slack (O : FirstHard I) {E : SignedPoint} {e : ℝ}
    (hq : q≤qCap) (hEy : E.y≤0) (he : |e+t|≤7/10)
    (hf : quarterFeasible E H (e+t) 0) :
    e+O.angle∈Icc 0 (7/10 : ℝ) ∧
      0<lowMixedSlack H.circle (A.a-1/2) e E O.angle := by
  obtain ⟨m,hm,hem,hmhard,_⟩ := I.eh0_hard_point hq hEy he hf
  have hmr := O.maximal m ⟨hm.1,hm.2.le⟩ hmhard
  have heR : e+O.angle∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [hem.1,hem.2,O.angle_mem.2,(abs_le.mp he).2]
  have heX (x : ℝ) (hx : x∈Icc O.angle t) : e+x∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [heR.1,hx.1,hx.2,(abs_le.mp he).2]
  let L := lowMixedSlack H.circle (A.a-1/2) e E
  let dL := lowMixedDerivative H.circle (A.a-1/2) e
  have hderiv (x : ℝ) (hx : x∈Icc O.angle t) : HasDerivAt L (dL x) x := by
    have hx0 : 0≤x := O.angle_mem.1.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    exact lowMixedSlack_hasDerivAt E hc
      (I.path_geometry hq ⟨hx0,hx.2⟩).2.2.2.2.2.2
  have hcont : ContinuousOn L (Icc O.angle t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hLt : 0≤L t := by
    have hN := (I.normalize hq).retains_mixed hq he (Or.inl rfl) hf
    rw [(I.normalize hq).H_eq] at hN
    dsimp [L]
    rw [lowMixedSlack_actual E (heX t ⟨O.angle_mem.2.le,le_rfl⟩)]
    exact sub_nonneg.mpr hN
  have hreserve := derivative_reserve (f := fun x => -L x)
    (df := fun x => -dL x) (k := 3/50) hcont.neg
    (fun x hx => (hderiv x (Ioo_subset_Icc_self hx)).fun_neg)
    (fun x hx => by
      have hh := I.lowMixedDerivative_negative hq
        ⟨O.angle_mem.1.trans_lt hx.1,hx.2.le⟩
        (O.later_unavailable ⟨hx.1,hx.2.le⟩) (heX x (Ioo_subset_Icc_self hx))
      dsimp [dL]
      linarith)
    (show O.angle∈Icc O.angle t from ⟨le_rfl,O.angle_mem.2.le⟩)
    (show t∈Icc O.angle t from ⟨O.angle_mem.2.le,le_rfl⟩) O.angle_mem.2.le
  have hmovement : 0<(3/50 : ℝ)*(t-O.angle) := by
    exact mul_pos (by norm_num) (sub_pos.mpr O.angle_mem.2)
  exact ⟨heR,by dsimp [L] at hLt hreserve; linarith⟩

theorem high_mixed_slack (O : FirstHard I) {E : SignedPoint} {e : ℝ}
    (hq : q≤qCap) (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (he : |e+t|≤11/50) (hf : quarterFeasible E H (e+t) 1) :
    e+O.angle∈Icc 0 (11/50 : ℝ) ∧
      0<highMixedSlack H.circle (A.a-1/2) e E O.angle := by
  obtain ⟨m,hm,hem,hmhard,_⟩ := I.eh1_hard_point hq hEs hEc hEy he hf
  have hmr := O.maximal m ⟨hm.1,hm.2.le⟩ hmhard
  have heR : e+O.angle∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [hem.1,O.angle_mem.2,(abs_le.mp he).2]
  have heX (x : ℝ) (hx : x∈Icc O.angle t) : e+x∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [heR.1,hx.1,hx.2,(abs_le.mp he).2]
  let L := highMixedSlack H.circle (A.a-1/2) e E
  let dL := highMixedDerivative H.circle (A.a-1/2) e E
  let F : ℝ → ℝ := fun x => L x-(t-x)/4000
  let dF : ℝ → ℝ := fun x => dL x+1/4000
  have hderiv (x : ℝ) (hx : x∈Icc O.angle t) : HasDerivAt F (dF x) x := by
    have hx0 : 0≤x := O.angle_mem.1.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    have hL := highMixedSlack_hasDerivAt (e := e) E hc
      (I.path_geometry hq ⟨hx0,hx.2⟩).2.2.2.2.2.2
    have h := hL.fun_sub (((hasDerivAt_id' x).const_sub t).div_const 4000)
    convert h using 1
    show dL x+1/4000=_
    ring
  have hcont : ContinuousOn F (Icc O.angle t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hFt : 0≤F t := by
    have hN := (I.normalize hq).retains_mixed hq
      (show |e+t|≤7/10 by linarith) (Or.inr rfl) hf
    rw [(I.normalize hq).H_eq] at hN
    have hwide : e+t∈Icc 0 (7/10 : ℝ) := by
      have hh := heX t ⟨O.angle_mem.2.le,le_rfl⟩
      exact ⟨hh.1,by linarith [hh.2]⟩
    have h1 : L t=quarterProjection E (movingAnchor H.circle (A.a-1/2) t) (e+t) 1-
        edgeWidth (e+t) := highMixedSlack_actual E hwide
    have hN' : edgeWidth (e+t)≤quarterProjection E (movingAnchor H.circle (A.a-1/2) t) (e+t) 1 :=
      hN
    show 0≤L t-(t-t)/4000
    rw [h1]
    linarith
  have hbarrier : 0≤F O.angle := left_sublevel_barrier O.angle_mem.2 hcont
    (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
    (fun x hx hFx => by
      have hx0 : 0<x := O.angle_mem.1.trans_lt hx.1
      have hsmall : L x≤1/1000 := by
        dsimp [F] at hFx
        linarith [I.tilt_cap]
      have hh := I.highMixedDerivative_negative hq hEc hEy
        ⟨hx0,hx.2.le⟩ (O.later_unavailable ⟨hx.1,hx.2.le⟩)
        (heX x (Ioo_subset_Icc_self hx)) hsmall
      dsimp [dF,dL]
      linarith) hFt
  have hmovement : 0<(t-O.angle)/4000 :=
    div_pos (sub_pos.mpr O.angle_mem.2) (by norm_num)
  exact ⟨heR,by dsimp [F,L] at hbarrier; linarith⟩

end FirstHard
end AlignedNegative
end SquaresInCircles.Eight
end
end
end
