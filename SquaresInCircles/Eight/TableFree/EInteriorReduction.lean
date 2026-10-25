module

public import SquaresInCircles.Eight.TableFree.EContactConcavity

/-!
# The E interior boundary reduction with an actual source-circle loss

Uncompiled draft.  Compact minimization is followed by explicit radial
descent or the exact two-contact curve.  A neighborhood is chosen only
for the strict sorting, sign and angle inequalities.  The circle bound
at the chosen endpoint follows from its proved strict energy decrease;
no feasible neighborhood of the circle boundary is assumed.  The full
.27 span of the retained negative composites is allowed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EInteriorGeometry

theorem contact_orientation_improves {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ioo 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) (hb : 0<P.2.1)
    (hangle : P.2.2∈Ioo 0 α)
    (hDE : deSlack d P=0) (hEH : ehSlack h α P=0) :
    ∃Q, Feasible h d α q Q ∧ corner Q<corner P := by
  let m := h+d-1
  let n := h-d
  let z := α/2-P.2.2
  have hwide : α∈Icc 0 (7/10 : ℝ) := ⟨hα.1.le,by linarith [hα.2]⟩
  have hsin := (transport_trig hwide).2.2.1
  have hsum2 : h+d<2 := by linarith
  have hm : m∈Icc (0:ℝ) 1 := by dsimp [m]; constructor <;> linarith
  have hn : |n|≤1 := by rw [abs_le]; dsimp [n]; constructor <;> linarith
  have hmD : (m-n+1)/2=d := by dsimp [m,n]; ring
  have hmH : (m+n+1)/2=h := by dsimp [m,n]; ring
  have hz : z∈Ioo (-α/2) (α/2) := by dsimp [z]; constructor <;> linarith [hangle.1,hangle.2]
  have hδ : α/2-z=P.2.2 := by dsimp [z]; ring
  have hε : α/2+z=α-P.2.2 := by dsimp [z]; ring
  have hdeeq : deValue d P=W P.2.2 := sub_eq_zero.mp hDE
  have heheq : ehValue h α P=W (α-P.2.2) := sub_eq_zero.mp hEH
  have hu := EContactCurve.contact_unique (m := m) (n := n) (a := P.1)
    (β := P.2.1) (z := z) hα
    (by rw [hmD,hδ]; exact hdeeq)
    (by rw [hmH,hε]; exact heheq)
  have hcurve : EContactCurve.curve m n α z=P := by
    apply Prod.ext
    · exact hu.1.symm
    · apply Prod.ext
      · exact hu.2.symm
      · exact hδ
  have hsort := strict_sorting_wide hq ⟨hα.1.le,hα.2.le⟩ hsum hp
  let S : Set ℝ := {r |
    0<EContactCurve.b m n α r ∧
    EContactCurve.b m n α r<EContactCurve.x m n α r+1/2 ∧
    -α/2<r ∧ r<α/2}
  have hSopen : IsOpen S := by
    have h1 : IsOpen {r : ℝ | 0<EContactCurve.b m n α r} :=
      isOpen_lt continuous_const (by
        unfold EContactCurve.b EContactCurve.U EContactCurve.V
        fun_prop)
    have h2 : IsOpen {r : ℝ | EContactCurve.b m n α r<EContactCurve.x m n α r+1/2} :=
      isOpen_lt (by unfold EContactCurve.b EContactCurve.U EContactCurve.V; fun_prop)
        (by unfold EContactCurve.x EContactCurve.U EContactCurve.V; fun_prop)
    have h3 : IsOpen {r : ℝ | -α/2<r} := isOpen_lt continuous_const continuous_id
    have h4 : IsOpen {r : ℝ | r<α/2} := isOpen_lt continuous_id continuous_const
    simpa only [S,setOf_and] using h1.inter (h2.inter (h3.inter h4))
  have hzS : z∈S := by
    change 0<EContactCurve.b m n α z ∧
      EContactCurve.b m n α z<EContactCurve.x m n α z+1/2 ∧ -α/2<z ∧ z<α/2
    exact ⟨by rw [←hu.2]; exact hb,by rw [←hu.2,←hu.1]; exact hsort,hz⟩
  obtain ⟨e,he,hball⟩ := Metric.isOpen_iff.mp hSopen z hzS
  have hnear {r : ℝ} (hr : |r-z|≤e/2) : r∈S := by
    apply hball
    change dist r z<e
    rw [Real.dist_eq]
    linarith
  have hlS : z-e/2∈S := by
    apply hnear
    rw [show z-e/2-z= -(e/2) by ring,abs_neg,abs_of_pos (by linarith : 0<e/2)]
  have huS : z+e/2∈S := by
    apply hnear
    rw [show z+e/2-z=e/2 by ring,abs_of_pos (by linarith : 0<e/2)]
  have himprove := EContactCurve.endpoint_improves hα hm hn
    hlS.2.2.1.le huS.2.2.2.le
    (show z∈Ioo (z-e/2) (z+e/2) by constructor <;> linarith)
  have hmake (r : ℝ) (hr : r∈S)
      (henergy : EContactCurve.energy m n α r<EContactCurve.energy m n α z) :
      Feasible h d α q (EContactCurve.curve m n α r) ∧
        corner (EContactCurve.curve m n α r)<corner P := by
    have hless : corner (EContactCurve.curve m n α r)<corner P := by
      rw [EContactCurve.corner_curve,←hcurve,EContactCurve.corner_curve]
      exact henergy
    have hcontacts := EContactCurve.curve_contacts hα m n r
    rw [hmD,hmH] at hcontacts
    refine ⟨{
      b_nonneg := hr.1.le
      sorted := hr.2.1.le
      angle := by
        dsimp [EContactCurve.curve]
        constructor <;> linarith [hr.2.2.1,hr.2.2.2]
      circle := hless.le.trans hp.circle
      DE := hcontacts.1.ge
      EH := ?_ },hless⟩
    change W (α-(α/2-r))≤ehValue h α (EContactCurve.curve m n α r)
    rw [show α-(α/2-r)=α/2+r by ring]
    exact hcontacts.2.ge
  rcases himprove with hl | hu'
  · exact ⟨_,hmake _ hlS hl⟩
  · exact ⟨_,hmake _ huS hu'⟩

/-- Every feasible interior state has an actual strict circle descendant.
Each contact case is settled by a concrete geometric move. -/
theorem interior_improves {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ioo 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) (hb : 0<P.2.1) (hangle : P.2.2∈Ioo 0 α) :
    ∃Q, Feasible h d α q Q ∧ corner Q<corner P := by
  have hde0 : 0≤deSlack d P := sub_nonneg.mpr hp.DE
  have heh0 : 0≤ehSlack h α P := sub_nonneg.mpr hp.EH
  rcases lt_or_eq_of_le hde0 with hde | hde
  · exact lower_tangent (by linarith [hα.2]) hp hb hde
  · rcases lt_or_eq_of_le heh0 with heh | heh
    · exact slide_DE (by linarith [hα.2]) hp
        (strict_sorting_wide hq ⟨hα.1.le,hα.2.le⟩ hsum hp) heh
    · exact contact_orientation_improves hq hα hh hd hsum hp hb hangle hde.symm heh.symm

theorem minimum_boundary {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ico 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P)
    (hmin : IsMinOn corner (feasibleSet h d α q) P) :
    P.2.1=0 ∨ P.2.2=0 ∨ P.2.2=α := by
  by_cases hb : P.2.1=0
  · exact Or.inl hb
  by_cases hδ : P.2.2=0
  · exact Or.inr (Or.inl hδ)
  by_cases hε : P.2.2=α
  · exact Or.inr (Or.inr hε)
  have hbpos : 0<P.2.1 := lt_of_le_of_ne hp.b_nonneg (Ne.symm hb)
  have hδpos : 0<P.2.2 := lt_of_le_of_ne hp.angle.1 (Ne.symm hδ)
  have hδlt : P.2.2<α := lt_of_le_of_ne hp.angle.2 hε
  obtain ⟨Q,hQ,hless⟩ := interior_improves hq
    ⟨span_pos hα.1 hsum hp,hα.2⟩ hh hd hsum hp hbpos ⟨hδpos,hδlt⟩
  exact False.elim (not_lt_of_ge (hmin hQ) hless)

/-- The source ceiling and source E corner stay separate.  In particular
an interior original E gives a strict decrease below its own circle. -/
theorem exists_boundary_minimum {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ico 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) :
    ∃Q, Feasible h d α q Q ∧ corner Q≤corner P ∧
      (Q.2.1=0 ∨ Q.2.2=0 ∨ Q.2.2=α) ∧
      ((0<P.2.1 ∧ P.2.2∈Ioo 0 α) → corner Q<corner P) := by
  obtain ⟨Q,hQ,hmin⟩ := exists_minimum hq ⟨P,hp⟩
  refine ⟨Q,hQ,hmin hp,minimum_boundary hq hα hh hd hsum hQ hmin,?_⟩
  rintro ⟨hb,hangle⟩
  obtain ⟨R,hR,hless⟩ := interior_improves hq
    ⟨span_pos hα.1 hsum hp,hα.2⟩ hh hd hsum hp hb hangle
  exact (hmin hR).trans_lt hless

end SquaresInCircles.Eight.TableFree.EInteriorGeometry
