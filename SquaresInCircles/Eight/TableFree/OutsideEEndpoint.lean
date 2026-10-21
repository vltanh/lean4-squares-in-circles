module

public import SquaresInCircles.Eight.TableFree.OutsideEZeroTangent

/-!
# Compact attainment of the actual negative-DE3 outside endpoint

Uncompiled source. A compact set contains the actual E radial states with
both original projections feasible. Its least positive-EH angle is attained.
The explicit strict improvement directions exclude every interior minimum
except an actual EH0 stop. Thus no feasible continuation path, first stopping
time, or omitted radial boundary is a hypothesis.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree
namespace OutsideE

theorem eventually_nonneg_of_value_or_rate {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hf : 0≤f 0) (h : 0<f 0 ∨ 0<d) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ), 0≤f τ := by
  rcases h with hp | hr
  · exact ((hd.continuousAt.tendsto.eventually (eventually_gt_nhds hp)).mono
      (fun _ hh => hh.le)).filter_mono nhdsWithin_le_nhds
  · exact (NegativeContact.eventually_right_gt hd hr).mono
      (fun _ hh => hf.trans hh.le)

/-- The small real movement is selected only after strict derivative or
strict source-margin certificates have been supplied for both functions. -/
theorem feasible_shift_left {f g : ℝ → ℝ → ℝ} {l u b₀ p b β df dg : ℝ}
    (hp : p∈Ioc l u) (hb : b∈Icc 0 b₀) (hβ : 0≤β)
    (hfloor : β=0 ∨ 0<b)
    (hdf : HasDerivAt (fun τ => f (p-τ) (b-β*τ)) df 0)
    (hdg : HasDerivAt (fun τ => g (p-τ) (b-β*τ)) dg 0)
    (hf : 0≤f p b) (hg : 0≤g p b)
    (hfstrict : 0<f p b ∨ 0<df) (hgstrict : 0<g p b ∨ 0<dg) :
    ∃ z : ℝ×ℝ, z.1∈Icc l u ∧ z.2∈Icc 0 b₀ ∧
      0≤f z.1 z.2 ∧ 0≤g z.1 z.2 ∧ z.1<p := by
  have hfe := eventually_nonneg_of_value_or_rate hdf
    (by simpa using hf) (by simpa using hfstrict)
  have hge := eventually_nonneg_of_value_or_rate hdg
    (by simpa using hg) (by simpa using hgstrict)
  have hangle : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ<p-l :=
    (eventually_lt_nhds (sub_pos.mpr hp.1)).filter_mono nhdsWithin_le_nhds
  have hradial : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0≤b-β*τ := by
    rcases hfloor with hzero | hbpos
    · exact Filter.Eventually.of_forall (by intro τ; simpa [hzero] using hb.1)
    · have hc : ContinuousAt (fun τ : ℝ => b-β*τ) 0 := by fun_prop
      have hval : 0<(fun τ : ℝ => b-β*τ) 0 := by simpa using hbpos
      exact ((hc.tendsto.eventually (eventually_gt_nhds hval)).mono
        (fun _ hh => hh.le)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ,hτ,hangle,hradial,hfe,hge⟩ :=
    (self_mem_nhdsWithin.and (hangle.and (hradial.and (hfe.and hge)))).exists
  refine ⟨⟨p-τ,b-β*τ⟩,⟨by linarith,by linarith [hp.2]⟩,
    ⟨hradial,?_⟩,hfe,hge,by linarith⟩
  have hprod := mul_nonneg hβ (show 0≤τ from le_of_lt hτ)
  linarith [hb.2]

structure DE3Endpoint (q : ℝ) (D E H : SignedPoint) (n p : ℝ) where
  point : SignedPoint
  movement : ℝ
  movement_nonneg : 0≤movement
  movement_le_n : movement≤n
  error_positive : 0<p-movement
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|E.y|
  circle_nonincrease : point.circle≤E.circle
  DE3 : quarterFeasible D point (-(n-movement)) 3
  EH1 : quarterFeasible point H (p-movement) 1
  terminal : quarterFeasible point H (p-movement) 0 ∨
    p-movement≤11/50 ∨ (n-movement=0 ∧ 11/50<p-movement)

theorem de3_endpoint {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y) (hHa : H.a<1) (hHo : H.Outer q)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc (11/50 : ℝ) (7/10 : ℝ))
    (hDE : quarterFeasible D E (-n) 3) (hEH : quarterFeasible E H p 1) :
    Nonempty (DE3Endpoint q D E H n p) := by
  obtain ⟨kind,I⟩ := arcSource_of_boundary hEs hEy hEr hHa
    ⟨by linarith [hp.1],hp.2⟩ hEH
  let α := p-n
  let l := max (11/50 : ℝ) α
  let f := ehSlack kind q H
  let g := de3Slack kind q α D
  have hlp : l<p := max_lt_iff.mpr ⟨hp.1,by dsimp [α]; linarith [hn.1]⟩
  have hlshort : 11/50≤l := le_max_left _ _
  have hlα : α≤l := le_max_right _ _
  have hparams {x : ℝ} (hx : x∈Icc l p) :
      x∈Icc (11/50 : ℝ) (7/10 : ℝ) ∧ x-α∈Icc 0 (7/10 : ℝ) := by
    constructor
    · exact ⟨hlshort.trans hx.1,hx.2.trans hp.2⟩
    · constructor
      · linarith [hx.1]
      · dsimp [α]; linarith [hx.2,hn.2]
  have hprim := kind.continuous_primary q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,ehSlack]
    fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,de3Slack]
    fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc l p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hlp.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
    · dsimp [f]
      rw [ehSlack_actual kind q H (-E.y) ⟨by linarith [hp.1],hp.2⟩,I.initial]
      exact sub_nonneg.mpr hEH
    · dsimp [g]
      rw [de3Slack_actual kind q α D (-E.y)
        (by dsimp [α]; simpa using ⟨hn.1.le,hn.2⟩),I.initial]
      simpa [α] using sub_nonneg.mpr hDE
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn ⟨(p,-E.y),hstart⟩
    continuous_fst.continuousOn
  let m := z.1
  let b := z.2
  have hm : m∈Icc l p := hz.1.1.1
  have hb : b∈Icc 0 (-E.y) := hz.1.1.2
  have hf : 0≤f m b := hz.1.2
  have hg : 0≤g m b := hz.2
  have hangles := hparams hm
  have hstop : quarterFeasible (kind.point q b) H m 0 ∨ m=l := by
    by_cases hEH0 : quarterFeasible (kind.point q b) H m 0
    · exact Or.inl hEH0
    right
    apply le_antisymm _ hm.1
    by_contra! hlm
    have hpm : m∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hangles.1.1],hangles.1.2⟩
    have hnear : ∃ z' : ℝ×ℝ, z'.1∈Icc l p ∧ z'.2∈Icc 0 (-E.y) ∧
        0≤f z'.1 z'.2 ∧ 0≤g z'.1 z'.2 ∧ z'.1<m := by
      by_cases hbzero : b=0
      · have hfpos : 0<f m b := by
          apply lt_of_le_of_ne hf
          intro heq
          have hcontact : ehSlack kind q H m 0=0 := by
            simpa [f,hbzero] using heq.symm
          exact hEH0 (by simpa [hbzero] using
            I.zero_contact_eh0 hqL hqU hHs hHy hHo hangles.1 hcontact)
        have hgpos := de3_fixed_tangent_rate_positive
          (I.geometry hqL hb).2.2.2.2.2.1 hb.1 hangles.2
        exact feasible_shift_left ⟨hlm,hm.2⟩ hb (le_rfl : (0:ℝ)≤0) (Or.inl rfl)
          (I.eh_direction_derivative (H := H) (p := m) (β := 0) hqL hb)
          (I.de3_direction_derivative (D := D) (α := α) (p := m) (β := 0) hqL hb)
          hf hg (Or.inl hfpos) (Or.inr (by simpa using hgpos))
      · have hbpos : 0<b := lt_of_le_of_ne hb.1 (Ne.symm hbzero)
        obtain ⟨β,hβ,hfpos,hgpos⟩ := I.de3_improving_speed hqL hb hpm hangles.2
        exact feasible_shift_left ⟨hlm,hm.2⟩ hb hβ.le (Or.inr hbpos)
          (I.eh_direction_derivative (H := H) (p := m) (β := β) hqL hb)
          (I.de3_direction_derivative (D := D) (α := α) (p := m) (β := β) hqL hb)
          hf hg (Or.inr hfpos) (Or.inr hgpos)
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := hnear
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  have hgeometry := I.geometry hqL hb
  have hEHfinal : quarterFeasible (kind.point q b) H m 1 := by
    have hh := hf
    dsimp [f] at hh
    rw [ehSlack_actual kind q H b ⟨by linarith [hangles.1.1],hangles.1.2⟩] at hh
    exact sub_nonneg.mp hh
  have hDEfinal : quarterFeasible D (kind.point q b) (-(n-(p-m))) 3 := by
    have hh := hg
    dsimp [g] at hh
    rw [de3Slack_actual kind q α D b hangles.2] at hh
    have heq : m-α=n-(p-m) := by dsimp [α]; ring
    simpa only [heq] using sub_nonneg.mp hh
  have hterminal : quarterFeasible (kind.point q b) H m 0 ∨
      m≤11/50 ∨ (n-(p-m)=0 ∧ 11/50<m) := by
    rcases hstop with hstop | hstop
    · exact Or.inl hstop
    · by_cases hmshort : m≤11/50
      · exact Or.inr (Or.inl hmshort)
      · have hmα : m=α := by
          have hlEq : l=α := by
            apply max_eq_right
            by_contra! hα
            have hlEq : l=11/50 := max_eq_left hα.le
            linarith
          exact hstop.trans hlEq
        exact Or.inr (Or.inr ⟨by dsimp [α] at hmα; linarith,lt_of_not_ge hmshort⟩)
  exact ⟨{
    point := kind.point q b
    movement := p-m
    movement_nonneg := sub_nonneg.mpr hm.2
    movement_le_n := by dsimp [α] at hlα; linarith [hm.1]
    error_positive := by linarith [hangles.1.1]
    sorted := hgeometry.1
    contained := hgeometry.2.1
    core := hgeometry.2.2.1
    radial := hgeometry.2.2.2.1
    nonpos := by dsimp [ArcKind.point]; linarith [hb.1]
    tangent_nonincrease := by
      simp only [ArcKind.point,abs_neg,abs_of_nonneg hb.1,abs_of_nonpos hEy]
      exact hb.2
    circle_nonincrease := hgeometry.2.2.2.2.1
    DE3 := hDEfinal
    EH1 := by simpa using hEHfinal
    terminal := by simpa using hterminal }⟩

end OutsideE
end SquaresInCircles.Eight.TableFree
