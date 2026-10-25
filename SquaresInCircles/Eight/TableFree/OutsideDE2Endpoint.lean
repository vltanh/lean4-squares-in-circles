module

public import SquaresInCircles.Eight.TableFree.OutsideDE2Comparison

/-!
# Compact same-q outside endpoint with the original DE2 witness

Uncompiled source. The two actual contact derivatives, including the outer
E comparison proved from the whole-interval polynomial, rule out an interior
compact minimum. The original DE2 axis is never replaced by DE3. H and D
are explicitly on the original q-circle, as required by those comparisons.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace OutsideE

structure DE2Endpoint (q : ℝ) (D E H : SignedPoint) (n p : ℝ) where
  point : SignedPoint
  movement : ℝ
  movement_nonneg : 0≤ movement
  movement_le_n : movement≤n
  error_positive : 0<p-movement
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|E.y|
  circle_nonincrease : point.circle≤E.circle
  DE2 : quarterFeasible D point (-(n-movement)) 2
  EH1 : quarterFeasible point H (p-movement) 1
  terminal : quarterFeasible point H (p-movement) 0 ∨
    p-movement≤11/50 ∨ (n-movement=0 ∧ 11/50<p-movement)

theorem de2_endpoint {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y) (hHa : H.a<1) (hHo : H.Outer q)
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc (11/50 : ℝ) (7/10 : ℝ))
    (hDE : quarterFeasible D E (-n) 2) (hEH : quarterFeasible E H p 1) :
    Nonempty (DE2Endpoint q D E H n p) := by
  obtain ⟨kind,I⟩ := arcSource_of_boundary hEs hEy hEr hHa
    ⟨by linarith [hp.1],hp.2⟩ hEH
  let α := p-n
  let l := max (11/50 : ℝ) α
  let f := ehSlack kind q H
  let g := de2Slack D α
  have hDa : 1/2<D.a := by
    have hd := (SignedPoint.outer_bounds hDs hDo).1
    have hlow := (uniform_circle_reserves hqL hqU).1
    linarith
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
    dsimp [g,de2Slack]
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
      rw [de2Slack_actual kind q α D (-E.y)
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
  have hpm : m∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hangles.1.1],hangles.1.2⟩
  have hstop : quarterFeasible (kind.point q b) H m 0 ∨ m=l := by
    by_cases hEH0 : quarterFeasible (kind.point q b) H m 0
    · exact Or.inl hEH0
    right
    apply le_antisymm _ hm.1
    by_contra! hlm
    have hnear : ∃ z' : ℝ×ℝ, z'.1∈Icc l p ∧ z'.2∈Icc 0 (-E.y) ∧
        0≤f z'.1 z'.2 ∧ 0≤g z'.1 z'.2 ∧ z'.1<m := by
      by_cases hfpos : 0<f m b
      · have hDpos := OutsideDContact.fixed_rate_positive hDa hDy hangles.2
        exact feasible_shift_left ⟨hlm,hm.2⟩ hb (le_rfl : (0:ℝ)≤0) (Or.inl rfl)
          (I.eh_direction_derivative (H := H) (p := m) (β := 0) hqL hb)
          (de2_direction_derivative D α b m 0)
          hf hg (Or.inl hfpos) (Or.inr (by simpa using hDpos))
      · have hfzero : f m b=0 := le_antisymm (le_of_not_gt hfpos) hf
        have hbpos : 0<b := by
          apply lt_of_le_of_ne hb.1
          intro hbzero
          have hcontact : ehSlack kind q H m 0=0 := by simpa [f,← hbzero] using hfzero
          exact hEH0 (by simpa [← hbzero] using
            I.zero_contact_eh0 hqL hqU hHs hHy hHo hangles.1 hcontact)
        let a := kind.primary q b
        let v := kind.slope q b
        let β₀ := contactSpeed a b v m
        let den := Real.cos m+v*Real.sin m
        let U := (a-1/2)*Real.cos m+(b+1/2)*Real.sin m
        let V := (D.a-1/2)*Real.sin (m-α)+(1/2-D.y)*Real.cos (m-α)
        have hgeom := I.geometry hqL hb
        have hder := I.derivative hqL hb
        have hβ := contactSpeed_positive hgeom.2.2.2.2.2.1 hb.1 hder.2.1 hpm
        have hidentity : β₀*den=U := by
          dsimp only [β₀,contactSpeed,den,U]
          exact div_mul_cancel₀ _ hβ.1.ne'
        by_cases hgpos : 0<g m b
        · have hEpos : 0<(β₀+1)*den-U := by nlinarith
          exact feasible_shift_left ⟨hlm,hm.2⟩ hb (by linarith [hβ.2]) (Or.inr hbpos)
            (I.eh_direction_derivative (H := H) (p := m) (β := β₀+1) hqL hb)
            (de2_direction_derivative D α b m (β₀+1))
            hf hg (Or.inr hEpos) (Or.inl hgpos)
        · have hgzero : g m b=0 := le_antisymm (le_of_not_gt hgpos) hg
          have hgap : β₀<V := I.de2_contact_speed_lt ⟨hqL,hqU⟩ hHs hHo hHa
            hDs hDy hDo hb hangles.1 hangles.2 hfzero hgzero
          let β := (β₀+V)/2
          have hβpos : 0<β := by dsimp [β]; linarith [hβ.2]
          have hβlower : β₀<β := by dsimp [β]; linarith
          have hEpos : 0<β*den-U := by
            have hh := mul_pos (sub_pos.mpr hβlower) hβ.1
            nlinarith
          have hDpos : 0<V-β := by dsimp [β]; linarith
          exact feasible_shift_left ⟨hlm,hm.2⟩ hb hβpos.le (Or.inr hbpos)
            (I.eh_direction_derivative (H := H) (p := m) (β := β) hqL hb)
            (de2_direction_derivative D α b m β)
            hf hg (Or.inr hEpos) (Or.inr hDpos)
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := hnear
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  have hgeometry := I.geometry hqL hb
  have hEHfinal : quarterFeasible (kind.point q b) H m 1 := by
    have hh := hf
    dsimp [f] at hh
    rw [ehSlack_actual kind q H b hpm] at hh
    exact sub_nonneg.mp hh
  have hDEfinal : quarterFeasible D (kind.point q b) (-(n-(p-m))) 2 := by
    have hh := hg
    dsimp [g] at hh
    rw [de2Slack_actual kind q α D b hangles.2] at hh
    have heq : m-α=n-(p-m) := by dsimp [α]; ring
    have hh2 := sub_nonneg.mp hh
    rw [heq] at hh2
    unfold quarterFeasible
    exact hh2
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
    DE2 := hDEfinal
    EH1 := by simpa using hEHfinal
    terminal := by simpa using hterminal }⟩

end OutsideE
end SquaresInCircles.Eight.TableFree
