import SquaresInCircles.Four.Exterior
import SquaresInCircles.Four.Construction
import SquaresInCircles.Common.ArcBudget
import SquaresInCircles.Common.Angles
import SquaresInCircles.Common.Optimum

/-!
# Four squares: uniqueness

On the circle of radius `1/2` about the disk centre, a square whose closed
square contains the disk centre holds a quarter circle, and every other square
of a packing in the disk of radius `sqrt 2` holds at least a quarter circle,
more unless the disk centre is one of its vertices. The angular budget leaves
the disk centre a vertex of every square, and the four quarter circles form the
2×2 block.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/
noncomputable section
open Set
namespace SquaresInCircles.Four

/-- The middle of the quarter circle between the two edges of a square at its
vertex nearest the disk centre. -/
def vertexMid {S : UnitSquare} {o : Point} (C : SquareChart S o) : Direction :=
  chartAngle C.phase C.reversed (Real.pi/4)

/-- If the closed square contains the disk centre, the square holds the quarter
of the circle of radius `1/2` between the chart angles `0` and `π/2`. -/
lemma quarter_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a ≤ 1/2) (hb : C.b ≤ 1/2) :
    ∃ A : OpenArc o (1/2) {p | openSquare S p}, A.halfWidth=Real.pi/4 ∧ A.center=vertexMid C := by
  obtain ⟨A,hA,hc⟩ := C.arc (1/2) 0 (Real.pi/2) (by positivity) (by linarith [Real.pi_pos]) (by
    intro t ht
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
    have hu := Real.sin_sq_add_cos_sq t
    have hs1 : Real.sin t < 1 := by nlinarith
    have hc1 : Real.cos t < 1 := by nlinarith
    have := C.nonneg
    exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩)
  exact ⟨A,by rw [hA]; ring,by rw [hc,vertexMid]; congr 1; ring⟩

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

/-- The only radius-`sqrt 2` packing is the block: the disk centre is a vertex
of every square. -/
theorem uniqueness (S : Fin 4 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : HasNormalForm S o centers := by
  choose C hsort using fun i => sorted_square_chart (S i) o
  have hφ (i : Fin 4) : phi (C i).a (C i).b ≤ 2 :=
    chart_phi (C i) (by simpa only [radius_sq] using hp.phi_le i)
  have harc (i : Fin 4) : ∃ A : OpenArc o (1/2) {p | openSquare (S i) p},
      Real.pi/4 ≤ A.halfWidth ∧
        (¬ openSquare (S i) o → (C i).a+(C i).b < 1 → Real.pi/4 < A.halfWidth) := by
    by_cases hi : openSquare (S i) o
    · have h := (C i).origin.mp hi
      obtain ⟨A,hA,-⟩ := quarter_arc (C i) h.1.le h.2.le
      exact ⟨A,hA.ge,fun h => (h hi).elim⟩
    · obtain ⟨A,h₁,h₂⟩ := exterior_arc (C i) (hsort i) hi (hφ i)
      exact ⟨A,h₁,fun _ => h₂⟩
  choose A hA hstrict using harc
  have hvertex (i : Fin 4) (hi : ¬ openSquare (S i) o) : (C i).a=1/2 ∧ (C i).b=1/2 :=
    (diamond (hφ i)).2 (not_lt.mp fun h =>
      uniform_arc_excess A hp.disjoint.pairwise hA ⟨i,hstrict i hi h⟩)
  have hout (i : Fin 4) : ¬ openSquare (S i) o := by
    intro hi
    obtain ⟨k,hk⟩ := exists_exterior (by norm_num) hp.disjoint o
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    have hc := hvertex k hk
    refine closed_open_disjoint (S k) (S i) (hp.disjoint k i hki) ?_ hi
    change alpha (S k) o ≤ 1/2 ∧ beta (S k) o ≤ 1/2
    rcases (C k).coordinates with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> constructor <;> linarith
  have hcoords (i : Fin 4) := hvertex i (hout i)
  choose Q hQ hmid using fun i => quarter_arc (C i) (hcoords i).1.le (hcoords i).2.le
  have hsep (i j : Fin 4) (hij : i ≠ j) :
      Real.pi/2 ≤ dist (vertexMid (C i)) (vertexMid (C j)) := by
    have hd := (Q i).centers_separated (Q j) (hp.disjoint.pairwise hij)
    rw [hQ i,hQ j,hmid i,hmid j] at hd
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
  .ofUnique centers model_packing
    ⟨0,1,1,by norm_num [centers,closedAxisSquare],by norm_num [radius_sq]⟩ uniqueness

end SquaresInCircles.Four
