module

public import SquaresInCircles.Eight.Owners.Full.ERates
public import SquaresInCircles.Eight.Owners.Negative.TEntry
public import SquaresInCircles.Eight.Words.Outside.EEndpoint

/-!
# Eight squares: flat-core entry for a negative E-primary total

An EH0 witness puts a core E on its flat side, for either sign of the frame difference
(`secondary_flat`); a negative EH1 gives the stronger cuts of the contact vector
(`genuine_negative_flat`). For a negative DE3 and a positive EH1, minimizing over the compact set
of states on the whole core arc gives an EH0 endpoint at the same radius (`NegativeDEEndpoint`,
`negative_DE_endpoint`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace NegativeCoreE

theorem secondary_flat {q r : ℝ} {E H : SignedPoint}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hHs : H.Sorted) (hHc : H.Contained q) (hq : q≤qCap)
    (hEH : quarterFeasible E H r 0) :
    E.a=7/12 ∧ -E.y<83/200 := by
  have hn := NegativeTEntry.center_norm_lt hHs hHc hq
  have hp := NegativeTEntry.unshifted_projection_le_norm H.reflect r
  have hprojection : H.a*Real.cos r+H.y*Real.sin r≤
      Real.sqrt (H.a^2+H.y^2) := by
    simpa [SignedPoint.reflect] using hp
  have hf : edgeWidth r≤E.y+H.a*Real.cos r+H.y*Real.sin r := by
    simpa [quarterFeasible,quarterProjection] using hEH
  have hb : -E.y<83/200 := by linarith [edgeWidth_ge_one r]
  have hflat := (SignedPoint.flat_core_iff hEs (by
    rw [abs_of_nonpos hEy]
    linarith)).1 hEc
  exact ⟨hflat,hb⟩

theorem genuine_negative_flat {q n : ℝ} {E H : SignedPoint}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHc : H.Contained q) (hq : q≤qCap)
    (hn : n∈Ioc 0 frameCap)
    (hEH : quarterFeasible E H (-n) 1)
    (hnot : ¬quarterFeasible E H (-n) 0) :
    E.a=7/12 ∧ -E.y<39/250 ∧ n<1/4 := by
  have hc := exceptional_negative_primary_cuts hEs hHs
    (Or.inr hEc) hHc hq hEy hHy hn hEH hnot
  exact ⟨hc.1,by simpa [abs_of_nonpos hEy] using hc.2.1,hc.2.2.1⟩

structure NegativeDEEndpoint (q : ℝ) (D E H : SignedPoint) (n p : ℝ) where
  point : SignedPoint
  movement : ℝ
  movement_nonneg : 0≤ movement
  movement_le_p : movement≤p
  negative_remaining : 0<n-movement
  sorted : point.Sorted
  nonpos : point.y≤0
  core : point.Core
  contained : point.Contained q
  flat : point.a=7/12
  tangent_nonincrease : |point.y|≤|E.y|
  circle_nonincrease : point.circle≤E.circle
  DE3 : quarterFeasible D point (-(n-movement)) 3
  EH1 : quarterFeasible point H (p-movement) 1
  EH0 : quarterFeasible point H (p-movement) 0

/-- E may be on the curved part of the core. The endpoint comes from the compact set of feasible
states on the arc at the radius `q`; strict derivatives rule out every minimum without an EH0
separator. -/
theorem negative_DE_endpoint {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHo : H.Outer q)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hn : n∈Ioc 0 frameCap) (hp : 0<p ∧ p<n)
    (hDE : quarterFeasible D E (-n) 3) (hEH : quarterFeasible E H p 1) :
    Nonempty (NegativeDEEndpoint q D E H n p) := by
  let I : FullE.ArcSource q E .trueCore :=
    ⟨hEs,hEy,fun _ => hEc,by intro h; cases h⟩
  let J : TrueCoreE.Source E := ⟨hEs,hEy,hEc⟩
  let α := p-n
  let f := FullE.mixedSlack .trueCore q H 1
  let g := FullE.deSlack .trueCore q α D 3
  have hpU : p≤frameCap := hp.2.le.trans hn.2
  have hparams {x : ℝ} (hx : x∈Icc 0 p) :
      x∈Icc 0 frameCap ∧ x-α∈Icc 0 frameCap := by
    refine ⟨⟨hx.1,hx.2.trans hpU⟩,?_,?_⟩ <;>
      dsimp [α] <;> linarith [hx.1,hx.2,hp.2,hn.2]
  have hprim := FullE.ArcKind.continuous_primary .trueCore q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,FullE.mixedSlack,FullE.highSlack]
    fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,FullE.deSlack,FullE.de3Slack]
    fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc 0 p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hp.1.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
    · dsimp [f]
      rw [FullE.mixedSlack_actual .trueCore q H (-E.y)
        (Or.inr rfl) ⟨hp.1.le,hpU⟩,I.initial]
      exact sub_nonneg.mpr hEH
    · dsimp [g]
      rw [FullE.deSlack_actual .trueCore q α D (-E.y)
        (Or.inr rfl) (by dsimp [α]; simpa using ⟨hn.1.le,hn.2⟩),I.initial]
      simpa [α] using sub_nonneg.mpr hDE
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn ⟨(p,-E.y),hstart⟩
    continuous_fst.continuousOn
  let m := z.1
  let b := z.2
  have hm : m∈Icc 0 p := hz.1.1.1
  have hb : b∈Icc 0 (-E.y) := hz.1.1.2
  have hf : 0≤f m b := hz.1.2
  have hg : 0≤g m b := hz.2
  have hangles := hparams hm
  have hEHfinal : quarterFeasible (FullE.ArcKind.trueCore.point q b) H m 1 := by
    have hh := hf
    dsimp [f] at hh
    rw [FullE.mixedSlack_actual .trueCore q H b (Or.inr rfl) hangles.1] at hh
    exact sub_nonneg.mp hh
  have hEH0 : quarterFeasible (FullE.ArcKind.trueCore.point q b) H m 0 := by
    by_contra hnot
    have hmpos : 0<m := by
      by_contra! hmzero
      have hm0 : m=0 := le_antisymm hmzero hm.1
      apply hnot
      have hh := hEHfinal
      simp only [hm0,quarterFeasible,quarterProjection] at hh ⊢
      simp at hh ⊢
      linarith
    have hnear : ∃ z' : ℝ×ℝ, z'.1∈Icc 0 p ∧ z'.2∈Icc 0 (-E.y) ∧
        0≤f z'.1 z'.2 ∧ 0≤g z'.1 z'.2 ∧ z'.1<m := by
      by_cases hbzero : b=0
      · have hfpos : 0<f m b := by
          apply lt_of_le_of_ne hf
          intro heq
          have hcontact : OutsideE.ehSlack .flatCore q H m 0=0 := by
            have hh := heq.symm
            simpa [f,hbzero,FullE.mixedSlack,FullE.highSlack,
              FullE.ArcKind.primary,TrueCoreE.primary_flat (by norm_num : (0:ℝ)≤1/2),
              OutsideE.ehSlack,OutsideE.ArcKind.primary] using hh
          have hstop := OutsideE.flat_zero_contact_eh0 hqL hHs hHy hHo
            ⟨hmpos,hangles.1.2⟩ hcontact
          apply hnot
          simpa [hbzero,FullE.ArcKind.point,FullE.ArcKind.primary,
            TrueCoreE.primary_flat (by norm_num : (0:ℝ)≤1/2),
            OutsideE.ArcKind.point,OutsideE.ArcKind.primary] using hstop
        have hgpos := OutsideE.de3_fixed_tangent_rate_positive
          (I.geometry hqL hb).2.2.2.2.2.1 hb.1 hangles.2
        apply OutsideE.feasible_shift_left ⟨hmpos,hm.2⟩ hb (le_rfl : (0:ℝ)≤0)
          (Or.inl rfl)
          (by simpa [f,FullE.mixedSlack] using
            I.high_direction_derivative (H := H) (p := m) (β := 0) hqL hb)
          (by simpa [g,FullE.deSlack] using
            I.de3_direction_derivative (D := D) (α := α) (p := m) (β := 0) hqL hb)
          hf hg (Or.inl hfpos) (Or.inr (by simpa using hgpos))
      · have hbpos : 0<b := lt_of_le_of_ne hb.1 (Ne.symm hbzero)
        obtain ⟨β,hβ,hfpos,hgpos⟩ := I.de3_improving_speed hqL hb hangles.1 hangles.2
        exact OutsideE.feasible_shift_left ⟨hmpos,hm.2⟩ hb hβ.le (Or.inr hbpos)
          (by simpa [f,FullE.mixedSlack] using
            I.high_direction_derivative (H := H) (p := m) (β := β) hqL hb)
          (by simpa [g,FullE.deSlack] using
            I.de3_direction_derivative (D := D) (α := α) (p := m) (β := β) hqL hb)
          hf hg (Or.inr hfpos) (Or.inr hgpos)
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := hnear
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  have hgeometry := I.geometry hqL hb
  have hcore : (FullE.ArcKind.trueCore.point q b).Core := (J.geometry hb).2.1
  have hnonpos : (FullE.ArcKind.trueCore.point q b).y≤0 := by
    change -b≤0
    exact neg_nonpos.mpr hb.1
  have hflat := (secondary_flat hgeometry.1 hnonpos hcore hHs hHo.le hqU hEH0).1
  have hDEfinal : quarterFeasible D (FullE.ArcKind.trueCore.point q b)
      (-(n-(p-m))) 3 := by
    have hh := hg
    dsimp [g] at hh
    rw [FullE.deSlack_actual .trueCore q α D b (Or.inr rfl) hangles.2] at hh
    have heq : m-α=n-(p-m) := by dsimp [α]; ring
    have hh' := sub_nonneg.mp hh
    rw [heq] at hh'
    exact hh'
  exact ⟨{
    point := FullE.ArcKind.trueCore.point q b
    movement := p-m
    movement_nonneg := sub_nonneg.mpr hm.2
    movement_le_p := by linarith [hm.1]
    negative_remaining := by linarith [hm.1,hp.2]
    sorted := hgeometry.1
    nonpos := hnonpos
    core := hcore
    contained := hgeometry.2.1
    flat := hflat
    tangent_nonincrease := by
      simp only [FullE.ArcKind.point,abs_neg,abs_of_nonneg hb.1,abs_of_nonpos hEy]
      exact hb.2
    circle_nonincrease := hgeometry.2.2.2.2.1
    DE3 := hDEfinal
    EH1 := by simpa using hEHfinal
    EH0 := by simpa using hEH0 }⟩

end NegativeCoreE
end SquaresInCircles.Eight
