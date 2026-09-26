import SquaresInCircles.Common.Angles
import SquaresInCircles.Four.Optimality
import SquaresInCircles.Common.Optimum

/-!
# Four squares: uniqueness

Equality rigidity for four squares uses the actual enclosing disk, not
uniqueness of the diamond relaxation (which is false).

The file ends with `optimum`: the case as an `Optimum`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Four

lemma contact_eq {a b : ℝ} (hφ : phi a b ≤ 2) (hs : 1 ≤ a+b) :
    a=1/2 ∧ b=1/2 := by
  have he : phi a b-2=2*(a+b-1)+(a-1/2)^2+(b-1/2)^2 := by dsimp [phi]; ring
  have hx := sq_nonneg (a-1/2)
  have hy := sq_nonneg (b-1/2)
  constructor <;> nlinarith

lemma some_vertex (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 2) :
    ∃ i, alpha (S i) o=1/2 ∧ beta (S i) o=1/2 := by
  by_contra hn
  apply diamond_impossible S o hd hφ
  intro i
  have hne : ¬ 1 ≤ alpha (S i) o+beta (S i) o := by
    intro h
    exact hn ⟨i,contact_eq (hφ i) h⟩
  exact lt_of_not_ge hne

lemma no_containing (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 2) :
    ∀ i, ¬ openSquare (S i) o := by
  obtain ⟨k,hka,hkb⟩ := some_vertex S o hd hφ
  have hclosed : closedSquare (S k) o := by
    change alpha (S k) o ≤ 1/2 ∧ beta (S k) o ≤ 1/2
    exact ⟨hka.le,hkb.le⟩
  intro i
  by_cases hi : i=k
  · subst i
    intro h
    change alpha (S k) o < 1/2 ∧ beta (S k) o < 1/2 at h
    linarith [h.1]
  · exact closed_open_disjoint (S k) (S i) (hd k i (Ne.symm hi)) hclosed

lemma all_vertices (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 2) :
    ∀ i, alpha (S i) o=1/2 ∧ beta (S i) o=1/2 := by
  have hout := no_containing S o hd hφ
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  choose A hA hstrict using (fun i => exterior_arc (C i) (hsort i) (hout i)
    (chart_phi (C i) (hφ i)))
  have htight (i : Fin 4) : 1 ≤ (C i).a+(C i).b := by
    by_contra hn
    exact uniform_arc_excess (n := 4) (by decide) A hd.pairwise hA
      ⟨i,hstrict i (lt_of_not_ge hn)⟩
  intro i
  have hc := contact_eq (chart_phi (C i) (hφ i)) (htight i)
  rcases (C i).coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> constructor <;> linarith [hc.1,hc.2]

def vertexMid {S : UnitSquare} {o : Point} (C : SquareChart S o) : Direction :=
  chartAngle C.phase C.reversed (Real.pi/4)

lemma vertex_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=1/2) :
    ∃ A : OpenArc o (1/2) {p | openSquare S p},
      A.halfWidth=Real.pi/4 ∧ A.center=vertexMid C := by
  obtain ⟨A,hA,hc⟩ := C.arc (1/2) 0 (Real.pi/2)
    (by positivity) (by linarith [Real.pi_pos]) (by
      intro t ht
      have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos])
      have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
      rw [ha,hb]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith,by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,by rw [hA]; ring,by rw [hc,vertexMid,show (0+Real.pi/2)/2=Real.pi/4 by ring]⟩

lemma vertex_represents {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=1/2) :
    Represents S o (vertexMid C-((Real.pi/4:ℝ):Direction)) (1/2,1/2) := by
  have h := chart_represents C
  cases hr : C.reversed
  · have he : vertexMid C-((Real.pi/4:ℝ):Direction)=C.phase := by
      simp [vertexMid,chartAngle,hr]
    simpa only [he,ha,SquareChart.signedB,hr,Bool.false_eq_true,ite_false,hb] using h
  · have hhalf : ((Real.pi/4:ℝ):Direction)+((Real.pi/4:ℝ):Direction)=((Real.pi/2:ℝ):Direction) := by
      rw [← Real.Angle.coe_add]; congr 1; ring
    have hq1 : quarterShift 1=((Real.pi/2:ℝ):Direction) := by simp [quarterShift]
    have he : C.phase=(vertexMid C-((Real.pi/4:ℝ):Direction))+quarterShift 1 := by
      rw [hq1,← hhalf]
      simp only [vertexMid,chartAngle,hr,ite_true,Real.Angle.coe_neg]
      abel
    have h' : Represents S o
        ((vertexMid C-((Real.pi/4:ℝ):Direction))+quarterShift 1) (1/2,-(1/2)) := by
      rw [← he]
      simpa only [ha,SquareChart.signedB,hr,ite_true,hb] using h
    have ht : turnPoint 1 (1/2,-(1/2))=((1:ℝ)/2,(1:ℝ)/2) := by simp [turnPoint]
    simpa only [ht] using represents_quarter 1 h'

/-- The only radius-sqrt(2) packing is the block, including the disk center. -/
theorem uniqueness (S : Fin 4 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : HasNormalForm S o centers := by
  have hφ (i : Fin 4) : phi (alpha (S i) o) (beta (S i) o) ≤ 2 := by
    have h := hp.phi_le i
    rwa [radius_sq] at h
  have hvertices := all_vertices S o hp.disjoint hφ
  have C (i : Fin 4) : SquareChart (S i) o := (square_chart (S i) o).some
  have hcoords (i : Fin 4) : (C i).a=1/2 ∧ (C i).b=1/2 :=
    (C i).transfer (fun a b => a=1/2 ∧ b=1/2) (fun h => ⟨h.2,h.1⟩) (hvertices i)
  choose A hA hmid using (fun i => vertex_arc (C i) (hcoords i).1 (hcoords i).2)
  have hsep (i j : Fin 4) (hij : i ≠ j) :
      Real.pi/2 ≤ dist (vertexMid (C i)) (vertexMid (C j)) := by
    have hd := (A i).centers_separated (A j) (hp.disjoint.pairwise hij)
    rw [hA i,hA j,hmid i,hmid j] at hd
    linarith
  obtain ⟨φ,σ,hgrid⟩ := regular_polygon _ (by push_cast; ring) hsep
  apply normal_form_of_slots (φ := φ-((Real.pi/4:ℝ):Direction)) hp.disjoint
  intro i
  obtain ⟨k,rfl⟩ := σ.surjective i
  refine ⟨k,?_⟩
  have hk : ((k.val*(Real.pi/2) : ℝ) : Direction)=quarterShift k := by
    fin_cases k <;> simp [quarterShift] <;> rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    exacts [⟨0,by ring⟩,⟨1,by push_cast; ring⟩]
  have hrep := vertex_represents (C (σ k)) (hcoords _).1 (hcoords _).2
  rw [hgrid,hk,add_sub_right_comm] at hrep
  have hc : turnPoint k (1/2,1/2)=centers k := by fin_cases k <;> norm_num [turnPoint,centers]
  simpa only [hc] using represents_quarter k hrep

/-- The optimum for four squares: `radius`, attained only by the normal forms
of `centers`. -/
def optimum : Optimum 4 :=
  .ofUnique centers optimality model_packing uniqueness

end SquaresInCircles.Four
