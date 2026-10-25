module

public import SquaresInCircles.Eight.Owners.Direct.NegativeEContact
public import SquaresInCircles.Eight.Words.Outside.EEndpoint

/-!
# Eight squares: actual DE alignment with the original EH and DE normals

A compact minimum on E's actual radial arc attains DE
alignment. The four simultaneous rate estimates exclude every interior
minimum, while the original inequalities exclude both zero tangent and
zero EH error. In particular H>D is proved at the endpoint rather than
assumed at the beginning. No H or D outer equality is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeE
open OutsideE

theorem zero_tangent_impossible {q n : ℝ} {D : SignedPoint} {kind : ArcKind}
    (hDa : D.a<1) (hDs : D.Sorted) (hDy : D.y≤0)
    (ha : 0<kind.primary q 0) (hn : n∈Icc 0 (7/10 : ℝ))
    (j : Fin 4) (hj : j=2 ∨ j=3) :
    ¬quarterFeasible D (kind.point q 0) (-n) j := by
  intro hf
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have hw := edgeWidth_ge_one n
  rcases hj with rfl | rfl
  · have hcos := mul_le_mul_of_nonneg_left hc1 hDs.1.le
    have hsin := mul_nonpos_of_nonpos_of_nonneg hDy hs0
    simp [quarterFeasible,quarterProjection,ArcKind.point] at hf
    linarith
  · have hsin := mul_nonneg ha.le hs0
    simp [quarterFeasible,quarterProjection,ArcKind.point] at hf
    linarith

theorem zero_error_impossible {q b : ℝ} {H : SignedPoint} {kind : ArcKind}
    (hHa : H.a<1) (hb : 0≤b) (j : Fin 4) (hj : j=0 ∨ j=1) :
    ¬quarterFeasible (kind.point q b) H 0 j := by
  intro hf
  rcases hj with rfl | rfl <;>
    simp [quarterFeasible,quarterProjection,ArcKind.point,edgeWidth_zero] at hf <;>
    linarith

structure AlignmentEndpoint (q : ℝ) (D E H : SignedPoint) (n p : ℝ)
    (jDE jEH : Fin 4) where
  point : SignedPoint
  positive_span : 0<p-n
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|E.y|
  circle_nonincrease : point.circle≤E.circle
  DE : quarterFeasible D point 0 jDE
  EH : quarterFeasible point H (p-n) jEH

/-- Both original weak owners survive all the way to actual DE alignment.
The source's H--D span may have either sign; positivity is a conclusion. -/
theorem alignment_endpoint {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted) (hHa : H.a<1)
    (hDy : 211/250< -D.y) (hDs : D.Sorted) (hDa : D.a<1)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc 0 (7/10 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (-n) jDE) (hEH : quarterFeasible E H p jEH) :
    Nonempty (AlignmentEndpoint q D E H n p jDE jEH) := by
  obtain ⟨kind,I⟩ := arcSource_of_owner hEs hEy hEr hHy hHs hHa hjEH
    ⟨hp.1.le,hp.2⟩ hEH
  let α := p-n
  let l := max 0 α
  let f := mixedSlack kind q H jEH
  let g := deSlack kind q α D jDE
  have hlp : l<p := max_lt_iff.mpr ⟨hp.1,by dsimp [α]; linarith [hn.1]⟩
  have hlzero : 0≤l := le_max_left _ _
  have hlα : α≤l := le_max_right _ _
  have hparams {x : ℝ} (hx : x∈Icc l p) :
      x∈Icc 0 (7/10 : ℝ) ∧ x-α∈Icc 0 (7/10 : ℝ) := by
    constructor
    · exact ⟨hlzero.trans hx.1,hx.2.trans hp.2⟩
    · constructor
      · linarith [hx.1]
      · dsimp [α]; linarith [hx.2,hn.2]
  have hprim := kind.continuous_primary q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,mixedSlack,lowSlack,ehSlack]
    split_ifs <;> fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,deSlack,de2Slack,de3Slack]
    split_ifs <;> fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc l p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hlp.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
    · dsimp [f]
      rw [mixedSlack_actual kind q H (-E.y) hjEH ⟨hp.1.le,hp.2⟩,I.initial]
      exact sub_nonneg.mpr hEH
    · dsimp [g]
      rw [deSlack_actual kind q α D (-E.y) hjDE
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
  have hgeometry := I.geometry hqL hb
  have hEHfinal : quarterFeasible (kind.point q b) H m jEH := by
    have hh := hf
    dsimp [f] at hh
    rw [mixedSlack_actual kind q H b hjEH hangles.1] at hh
    exact sub_nonneg.mp hh
  have hDEfinal : quarterFeasible D (kind.point q b) (-(m-α)) jDE := by
    have hh := hg
    dsimp [g] at hh
    rw [deSlack_actual kind q α D b hjDE hangles.2] at hh
    exact sub_nonneg.mp hh
  have hbpos : 0<b := by
    apply lt_of_le_of_ne hb.1
    intro hzero
    have ha : 0<kind.primary q 0 := by
      have hh := hgeometry.2.2.2.2.2.1
      rw [← hzero] at hh
      linarith
    exact zero_tangent_impossible hDa hDs (by linarith) ha hangles.2 jDE hjDE
      (by simpa [← hzero] using hDEfinal)
  have hmleft : m=l := by
    apply le_antisymm _ hm.1
    by_contra! hlm
    obtain ⟨β,hβ,hfder,hgder⟩ := ArcSource.improving_below_speed I hqL hqU hHy hHs hDs hDy
      hb hangles.1 hangles.2 jDE jEH hjDE hjEH
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := feasible_shift_left
      (f := f) (g := g) ⟨hlm,hm.2⟩ hb hβ.le (Or.inr hbpos)
      (ArcSource.mixed_direction_derivative I (H := H) (p := m) (β := β) jEH hqL hb)
      (ArcSource.de_direction_derivative I (D := D) (α := α) (p := m) (β := β) jDE hqL hb)
      hf hg (Or.inr hfder) (Or.inr hgder)
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  have hmpos : 0<m := by
    apply lt_of_le_of_ne hangles.1.1
    intro hmzero
    exact zero_error_impossible hHa hb.1 jEH hjEH (by simpa [← hmzero] using hEHfinal)
  have hmα : m=α := by
    have hαpos : 0<α := by
      by_contra! hbad
      have hlEq : l=0 := max_eq_left hbad
      linarith
    exact hmleft.trans (max_eq_right hαpos.le)
  exact ⟨{
    point := kind.point q b
    positive_span := by dsimp [α] at hmα; linarith
    sorted := hgeometry.1
    contained := hgeometry.2.1
    core := hgeometry.2.2.1
    radial := hgeometry.2.2.2.1
    nonpos := by dsimp [ArcKind.point]; linarith [hb.1]
    tangent_nonincrease := by
      simp only [ArcKind.point,abs_neg,abs_of_nonneg hb.1,abs_of_nonpos hEy]
      exact hb.2
    circle_nonincrease := hgeometry.2.2.2.2.1
    DE := by simpa [hmα] using hDEfinal
    EH := by simpa [hmα,α] using hEHfinal }⟩

end DirectNegativeE
end SquaresInCircles.Eight
