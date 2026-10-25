module

public import SquaresInCircles.Eight.Owners.Direct.NegativeEAlignment
public import SquaresInCircles.Eight.Owners.Full.ERates

/-!
# Eight squares: actual E-to-D alignment with an arbitrary contained H

The original positive H--D order keeps EH positive
until DE aligns. A compact minimum on E's full actual radial arc attains
that alignment while retaining both original weak mixed owners. No
near-diagonal bound or outer equality is assumed for H.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace FullE

theorem zero_tangent_impossible {q n : ℝ} {D : SignedPoint} {kind : ArcKind}
    (hDa : D.a<1) (hDs : D.Sorted) (hDy : D.y≤0)
    (ha : 0<kind.primary q 0) (hn : n∈Icc 0 (7/10 : ℝ))
    (j : Fin 4) (hj : j=2 ∨ j=3) :
    ¬quarterFeasible D (kind.point q 0) (-n) j := by
  intro hf
  have ht := transport_trig hn
  have hw := edgeWidth_ge_one (-n)
  rcases hj with rfl | rfl
  · have hcos := mul_le_mul_of_nonneg_left ht.2.1 hDs.1.le
    have hsin := mul_nonpos_of_nonpos_of_nonneg hDy ht.2.2.1
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_two,ArcKind.point,
      Real.sin_neg,Real.cos_neg,neg_zero,sub_zero,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      Fin.succ_zero_eq_one,Matrix.cons_val_zero,Matrix.cons_val_one] at hf
    linarith
  · have hsin := mul_nonneg ha.le ht.2.2.1
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_three,ArcKind.point,
      Real.sin_neg,Real.cos_neg,neg_zero,zero_mul,sub_zero,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Matrix.cons_val_two,
      Matrix.cons_val_one,Matrix.cons_val_zero] at hf
    linarith


/-- The actual radial endpoint exists for either original EH owner and
either original negative DE owner, including curved-core E sources. -/
theorem alignment_endpoint_of_order {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q) (hHy : 0≤H.y)
    (hDy : 211/250< -D.y) (hDs : D.Sorted) (hDa : D.a<1)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc 0 (7/10 : ℝ)) (hnp : n<p)
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (-n) jDE) (hEH : quarterFeasible E H p jEH) :
    Nonempty (DirectNegativeE.AlignmentEndpoint q D E H n p jDE jEH) := by
  obtain ⟨kind,I⟩ := arcSource_of_boundary hEs hEy hEr
  let α := p-n
  let f := mixedSlack kind q H jEH
  let g := deSlack kind q α D jDE
  have hα : 0<α := by dsimp [α]; linarith
  have hαp : α<p := by dsimp [α]; linarith [hn.1]
  have hparams {x : ℝ} (hx : x∈Icc α p) :
      x∈Icc 0 (7/10 : ℝ) ∧ x-α∈Icc 0 (7/10 : ℝ) := by
    constructor
    · exact ⟨hα.le.trans hx.1,hx.2.trans hp.2⟩
    · constructor
      · linarith [hx.1]
      · dsimp [α]; linarith [hx.2,hn.2]
  have hprim := kind.continuous_primary q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,mixedSlack,DirectNegativeE.lowSlack,highSlack]
    split_ifs <;> fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,deSlack,OutsideE.de2Slack,de3Slack]
    split_ifs <;> fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc α p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hαp.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
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
  have hm : m∈Icc α p := hz.1.1.1
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
  have hmα : m=α := by
    apply le_antisymm _ hm.1
    by_contra! hαm
    obtain ⟨β,hβ,hfder,hgder⟩ := I.improving_below_speed hqL hqU
      hHs hHcore hHc hHy hDs hDy hb hangles.1 hangles.2
      jDE jEH hjDE hjEH hEHfinal
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := OutsideE.feasible_shift_left
      (f := f) (g := g) ⟨hαm,hm.2⟩ hb hβ.le (Or.inr hbpos)
      (I.mixed_direction_derivative (H := H) (p := m) (β := β) jEH hqL hb)
      (I.de_direction_derivative (D := D) (α := α) (p := m) (β := β) jDE hqL hb)
      hf hg (Or.inr hfder) (Or.inr hgder)
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  exact ⟨{
    point := kind.point q b
    positive_span := hα
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

end FullE
end SquaresInCircles.Eight
