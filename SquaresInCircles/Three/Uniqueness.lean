import SquaresInCircles.Three.Containing
import SquaresInCircles.Three.Construction
import SquaresInCircles.Common.ArcBudget
import SquaresInCircles.Common.Angles
import SquaresInCircles.Common.Optimum

/-!
# Three squares: uniqueness

In the closed disk of radius `5√17/16` no square contains the disk centre, so
every square holds a cap of the circle of radius `3/8` of at least 120 degrees.
The budget makes every cap exactly 120 degrees, so every square is of type A or
type B. Two squares of type A would hold too wide arcs of the circle of radius
`7/16`, and three of type B too wide arcs of the circle of radius `1/16`. For
one square of type A and two of type B, the angles between the caps rebuild the
T.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/
noncomputable section
open Set
namespace SquaresInCircles.Three

/-- A cap of half-width at most `π/3` belongs to a square of type A, centred on
its phase, or of type B, centred `π/6` from it. -/
lemma cap_types {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3 C.a C.b) {W : OpenArc o aux {p | openSquare S p}}
    (hw : W.halfWidth=(capA aux C.a+min (capA aux C.a) (capV aux C.b))/2)
    (hc : W.center=chartAngle C.phase C.reversed ((capA aux C.a-min (capA aux C.a) (capV aux C.b))/2))
    (h : W.halfWidth ≤ Real.pi/3) :
    (C.a=11/16 ∧ C.b=0 ∧ W.center=C.phase) ∨
      (C.a=1/2 ∧ C.b=5/16 ∧ W.center=chartAngle C.phase C.reversed (Real.pi/6)) := by
  obtain ⟨hA,-,hAV,htA,htB⟩ := cap_bounds ha C.nonneg.2 hp
  rcases le_or_gt (capA aux C.a) (capV aux C.b) with hfull | hclip
  · rw [min_eq_left hfull] at hw hc
    obtain ⟨h₁,h₂⟩ := htA (by linarith)
    exact Or.inl ⟨h₁,h₂,by rw [hc]; simp [chartAngle]⟩
  · rw [min_eq_right hclip.le] at hw hc
    obtain ⟨h₁,h₂⟩ := htB (by linarith)
    have hA2 : capA aux C.a=Real.pi/2 := by rw [capA,h₁,sub_self,zero_div,Real.arccos_zero]
    exact Or.inr ⟨h₁,h₂,by rw [hc]; congr 1; linarith⟩

/-- The phases of the T: if two squares of type B have antipodal phases `φ` and
`ψ`, and the centres of their caps and the phase `χ` of the square of type A
are pairwise `2π/3` apart, then the two orientations are opposite and `χ` is a
quarter turn from `φ`. -/
lemma apex_phase {φ ψ χ : Direction} (r s : Bool)
    (hanti : ψ=φ+(Real.pi:Direction))
    (h01 : (chartAngle ψ s (Real.pi/6)-chartAngle φ r (Real.pi/6)).cos= -(1/2))
    (h02 : (χ-chartAngle φ r (Real.pi/6)).cos= -(1/2))
    (h12 : (χ-chartAngle ψ s (Real.pi/6)).cos= -(1/2)) :
    s= !r ∧ (χ-φ).cos=0 ∧ (χ-φ).sin=(if r then 1 else -1) := by
  let δ := χ-φ
  let p : Direction := ((Real.pi/6:ℝ):Direction)
  have hcp : p.cos=Real.sqrt 3/2 := by simp [p,Real.cos_pi_div_six]
  have hsp : p.sin=(1/2:ℝ) := by simp [p,Real.sin_pi_div_six]
  cases r <;> cases s
  · have he : chartAngle ψ false (Real.pi/6)-chartAngle φ false (Real.pi/6)=(Real.pi:Direction) := by
      rw [hanti]; simp only [chartAngle,Bool.false_eq_true,ite_false]; abel
    rw [he,Real.Angle.cos_coe,Real.cos_pi] at h01
    norm_num at h01
  · have he₀ : χ-chartAngle φ false (Real.pi/6)=δ-p := by
      simp only [δ,p,chartAngle,Bool.false_eq_true,ite_false]; abel
    have he₁ : χ-chartAngle ψ true (Real.pi/6)=δ-(Real.pi:Direction)+p := by
      rw [hanti]; simp only [δ,p,chartAngle,ite_true,Real.Angle.coe_neg]; abel
    rw [he₀] at h02
    rw [he₁] at h12
    simp only [sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,Real.Angle.cos_neg,
      Real.Angle.sin_neg,Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi,Real.sin_pi,
      hcp,hsp] at h02 h12
    have hs : δ.sin= -1 := by linarith
    have hc : δ.cos=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq δ]
    exact ⟨rfl,hc,hs⟩
  · have he₀ : χ-chartAngle φ true (Real.pi/6)=δ+p := by
      simp only [δ,p,chartAngle,ite_true,Real.Angle.coe_neg]; abel
    have he₁ : χ-chartAngle ψ false (Real.pi/6)=δ-(Real.pi:Direction)-p := by
      rw [hanti]; simp only [δ,p,chartAngle,Bool.false_eq_true,ite_false]; abel
    rw [he₀] at h02
    rw [he₁] at h12
    simp only [sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,Real.Angle.cos_neg,
      Real.Angle.sin_neg,Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi,Real.sin_pi,
      hcp,hsp] at h02 h12
    have hs : δ.sin=1 := by linarith
    have hc : δ.cos=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq δ]
    exact ⟨rfl,hc,hs⟩
  · have he : chartAngle ψ true (Real.pi/6)-chartAngle φ true (Real.pi/6)=(Real.pi:Direction) := by
      rw [hanti]; simp only [chartAngle,ite_true]; abel
    rw [he,Real.Angle.cos_coe,Real.cos_pi] at h01
    norm_num at h01

/-- A square of type B whose phase is a quarter turn from `χ`, turned by its
orientation, sits at `c₁` or `c₂` in the frame `χ-π/2`. -/
lemma b_represents {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=5/16) {χ : Direction} (hc : (χ-C.phase).cos=0)
    (hs : (χ-C.phase).sin=if C.reversed then 1 else -1) :
    ∃ m, Represents S o (χ-((Real.pi/2:ℝ):Direction)) (centers m) := by
  have he : C.phase-(χ-((Real.pi/2:ℝ):Direction))=((Real.pi/2:ℝ):Direction)-(χ-C.phase) := by
    abel
  have h := represents_cardinal (ψ := χ-((Real.pi/2:ℝ):Direction)) (chart_represents C)
  cases hr : C.reversed
  · refine ⟨0,?_⟩
    have h2 := h 2 (by rw [he,Real.Angle.cos_pi_div_two_sub,hs,hr]; simp [quarterShift])
      (by rw [he,Real.Angle.sin_pi_div_two_sub,hc]; simp [quarterShift])
    simpa [turnPoint,centers,SquareChart.signedB,hr,ha,hb,neg_div] using h2
  · refine ⟨1,?_⟩
    have h0 := h 0 (by rw [he,Real.Angle.cos_pi_div_two_sub,hs,hr]; simp [quarterShift])
      (by rw [he,Real.Angle.sin_pi_div_two_sub,hc]; simp [quarterShift])
    simpa [turnPoint,centers,SquareChart.signedB,hr,ha,hb,neg_div] using h0

/-- A square of type A sits at `c₃` in the frame a quarter turn behind its
phase. -/
lemma a_represents {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=11/16) (hb : C.b=0) :
    Represents S o (C.phase-((Real.pi/2:ℝ):Direction)) (centers 2) := by
  have h := represents_cardinal (ψ := C.phase-((Real.pi/2:ℝ):Direction)) (chart_represents C) 1
    (by simp [quarterShift]) (by simp [quarterShift])
  simpa [turnPoint,centers,SquareChart.signedB,ha,hb] using h

/-- Every optimal three-square packing is one rigid image of the T. -/
theorem uniqueness (S : Fin 3 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : HasNormalForm S o centers := by
  have hφ (i : Fin 3) : phi (alpha (S i) o) (beta (S i) o) ≤ 425/256 := by
    simpa only [radius_sq] using hp.phi_le i
  have hd := hp.disjoint.pairwise
  choose C hsort using fun i => sorted_square_chart (S i) o
  have hP (i : Fin 3) : P3 (C i).a (C i).b := p3_of_phi (chart_phi (C i) (hφ i))
  have ha (i : Fin 3) : 1/2 ≤ (C i).a :=
    (C i).exterior (hsort i) (no_containing S o hp.disjoint hφ i)
  choose W hw hc hlo using fun i => exterior_cap (C i) (ha i) (hP i)
  -- every cap is exactly 120 degrees, of type A or type B
  have hup (i : Fin 3) : (W i).halfWidth ≤ Real.pi/3 :=
    not_lt.mp fun h => uniform_arc_excess W hd hlo ⟨i,h⟩
  have hty (i : Fin 3) := cap_types (C i) (ha i) (hP i) (hw i) (hc i) (hup i)
  have heq (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      dist (W j).center (W k).center=2*Real.pi/3 := by
    have h := (W i).third_distance_bounds (W j) (W k) (hd hij) (hd hik) (hd hjk)
    linarith [h.1,h.2,hlo i,hlo j,hlo k,hup i,hup j,hup k]
  -- not two squares of type A
  have hAA (i j : Fin 3) (hij : i ≠ j) (hi : (C i).a=11/16 ∧ (C i).b=0 ∧ (W i).center=(C i).phase)
      (hj : (C j).a=11/16 ∧ (C j).b=0 ∧ (W j).center=(C j).phase) : False := by
    obtain ⟨k,hik,hjk⟩ : ∃ k, i ≠ k ∧ j ≠ k := by
      revert hij; fin_cases i <;> fin_cases j <;> decide
    have h := heq k i j hik.symm hjk.symm hij
    rw [hi.2.2,hj.2.2] at h
    exact axial_pair_impossible (C i) (C j) ⟨by linarith [hi.1],by linarith [hi.1],by linarith [hi.2.1]⟩
      ⟨by linarith [hj.1],by linarith [hj.1],by linarith [hj.2.1]⟩ (hd hij) (by linarith)
  -- some square of type A
  obtain ⟨k,hk⟩ : ∃ k, (C k).a=11/16 ∧ (C k).b=0 ∧ (W k).center=(C k).phase := by
    by_contra hn
    have hB (i : Fin 3) : (C i).a=1/2 ∧ (C i).b=5/16 :=
      ((hty i).resolve_left fun h => hn ⟨i,h⟩).imp_right And.left
    choose X hX _ using fun i =>
      (C i).half_arc (r := 1/16) (by norm_num) (hB i).1 (by rw [(hB i).2]; norm_num)
    have h := triple_arc_budget (X 0) (X 1) (X 2) (hd (by decide)) (hd (by decide)) (hd (by decide))
    rw [hX,hX,hX] at h
    linarith [Real.pi_pos]
  obtain ⟨i,j,hij,hik,hjk,hcover⟩ :
      ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ∀ l, l=i ∨ l=j ∨ l=k := by
    fin_cases k <;> decide
  have hB (l : Fin 3) (hl : l ≠ k) := (hty l).resolve_left fun h => hAA l k hl h hk
  obtain ⟨hia,hib,hic⟩ := hB i hik
  obtain ⟨hja,hjb,hjc⟩ := hB j hjk
  -- the two squares of type B have antipodal phases
  obtain ⟨X,hX,hXc⟩ := (C i).half_arc (r := 1/16) (by norm_num) hia (by rw [hib]; norm_num)
  obtain ⟨Y,hY,hYc⟩ := (C j).half_arc (r := 1/16) (by norm_num) hja (by rw [hjb]; norm_num)
  have hanti : (C j).phase=(C i).phase+(Real.pi:Direction) := by
    rw [← hXc,← hYc]
    exact X.opposite Y (hd hij) hX hY
  -- the caps are centred pairwise `2π/3` apart
  have h01 := cos_sub_distance (W i).center (W j).center
  have h02 := cos_sub_distance (W i).center (W k).center
  have h12 := cos_sub_distance (W j).center (W k).center
  rw [heq k i j hik.symm hjk.symm hij,cos_two_pi_thirds] at h01
  rw [heq j i k hij.symm hjk hik,cos_two_pi_thirds] at h02
  rw [heq i j k hij hik hjk,cos_two_pi_thirds] at h12
  rw [hic,hjc] at h01
  rw [hic,hk.2.2] at h02
  rw [hjc,hk.2.2] at h12
  obtain ⟨hrev,hcos,hsin⟩ := apex_phase (C i).reversed (C j).reversed hanti h01 h02 h12
  have hj' : (C k).phase-(C j).phase=((C k).phase-(C i).phase)-(Real.pi:Direction) := by
    rw [hanti]; abel
  apply normal_form_of_slots (φ := (C k).phase-((Real.pi/2:ℝ):Direction)) hp.disjoint
  intro l
  rcases hcover l with rfl | rfl | rfl
  · exact b_represents (C l) hia hib hcos hsin
  · refine b_represents (C l) hja hjb (by rw [hj',Real.Angle.cos_sub_pi,hcos,neg_zero]) ?_
    rw [hj',Real.Angle.sin_sub_pi,hsin,hrev]
    cases (C i).reversed <;> simp
  · exact ⟨2,a_represents (C l) hk.1 hk.2.1⟩

/-- The optimum for three squares: `radius`, attained only by the normal forms
of `centers`. -/
def optimum : Optimum 3 :=
  .ofUnique centers model_packing
    ⟨0,-1,-13/16,by norm_num [centers,closedAxisSquare],by norm_num [radius_sq]⟩ uniqueness

end SquaresInCircles.Three
