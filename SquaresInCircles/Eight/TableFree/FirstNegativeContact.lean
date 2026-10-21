module

public import SquaresInCircles.Eight.TableFree.AlignedNegativeEH1

/-!
# The first actual hard-axis contact of a negative primary

Uncompiled source. The actual GA0 availability is a continuous trigonometric
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
namespace SquaresInCircles.Eight.TableFree
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
  have hc : Continuous (hardAvailability A) := by dsimp [hardAvailability]; fun_prop
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
  obtain ⟨x,hx,hxt,hfx⟩ := (self_mem_nhdsWithin.and (hbound.and hpos)).exists
  have hx0 : 0<x := O.angle_mem.1.trans_lt hx
  have hs : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0
    (by linarith [I.tilt_cap,Real.pi_gt_three])
  have havail : 0≤hardAvailability A x := by
    exact (mul_pos hs hfx).le
  have hhard := (hard_availability_iff A ⟨hx0.le,hxt.le.trans I.tilt_cap⟩).2 havail
  exact O.later_unavailable ⟨hx,hxt.le⟩ hhard

theorem intrinsic_bound (O : FirstHard I) (hq : q≤qCap) :
    intrinsic (value (A.a-1/2) O.angle) O.angle≤A.circle := by
  let x := O.angle
  let Z := value (A.a-1/2) x
  let V := K*Real.cos x-Z*Real.sin x
  have hx : x∈Icc 0 (7/10 : ℝ) := ⟨O.angle_mem.1,O.angle_mem.2.le.trans I.tilt_cap⟩
  have ht := transport_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hZ := I.path_cap hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  have hcontact : Z*Real.cos x=A.a-1/2-K*Real.sin x := value_contact_identity _ _ hc.ne'
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
    apply (mul_le_mul_right hc).mp
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
end SquaresInCircles.Eight.TableFree
