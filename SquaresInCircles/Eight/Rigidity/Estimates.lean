module

public import SquaresInCircles.Eight.ExactFamily.CenterCompletion
public import SquaresInCircles.Eight.ExactFamily.Perturbation
public import SquaresInCircles.Eight.Candidate.Geometry

/-!
# Eight squares: estimates for the sharp terminal

The inputs of the terminal inequality for a boundary cycle with the frames of the candidate word
(`Candidate.Frame`): the frames of the seven squares in terms of their real lifts, the five frame
errors (`errors`), whose sum is the mismatch (`error_sum`), and the centres (`positions`). The
anchored corners of `A`, `B`, `D`, `E` and `H` lie in their squares (`selected_vertex`) and so in
the disk (`vertex_containment`); on every edge a separating forward axis in the terminal owner set
gives a nonnegative gap (`owners_and_gaps`); and containment and the canonical bounds give the
coordinate bounds on the centres of `T` and `G` that the perturbation estimates need
(`automatic_projections`).

These are estimates, used in `Rigidity/Terminal.lean` together with the positivity argument; the optimal
configuration itself is defined in `ExactFamily/Stationary.lean`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open ExactFamily Coordinates
namespace Terminal
open Candidate Perturbation

/-- The frame of a candidate square is its real frame lift plus its quarter offset. -/
private theorem TerminalEstimates.frame_of {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (k : Vertex) :
    (C.square k).cosine = Real.cos (F.theta k + (offsets k : ℝ) * Real.pi / 2) ∧
    (C.square k).sine = Real.sin (F.theta k + (offsets k : ℝ) * Real.pi / 2) := by
  rw [← F.canonical_eq k]
  exact ⟨C.frame_cos k, C.frame_sin k⟩

/-- The seven frames, with the quarter offsets `(-1,-1,0,0,1,1,2)` evaluated. -/
private theorem TerminalEstimates.frames {q : ℝ} {C : BoundaryCycle q} (F : Frame C) :
    ((C.square 0).cosine = Real.sin (F.theta 0) ∧ (C.square 0).sine = -Real.cos (F.theta 0)) ∧
    ((C.square 1).cosine = Real.sin (F.theta 1) ∧ (C.square 1).sine = -Real.cos (F.theta 1)) ∧
    ((C.square 2).cosine = 1 ∧ (C.square 2).sine = 0) ∧
    ((C.square 3).cosine = Real.cos (F.theta 3) ∧ (C.square 3).sine = Real.sin (F.theta 3)) ∧
    ((C.square 4).cosine = -Real.sin (F.theta 4) ∧ (C.square 4).sine = Real.cos (F.theta 4)) ∧
    ((C.square 5).cosine = -Real.sin (F.theta 5) ∧ (C.square 5).sine = Real.cos (F.theta 5)) ∧
    ((C.square 6).cosine = -Real.cos (F.theta 6) ∧
      (C.square 6).sine = -Real.sin (F.theta 6)) := by
  have hA : F.theta 2 = 0 := F.theta_A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [offsets, hA, Real.cos_add, Real.sin_add, neg_div] using
      TerminalEstimates.frame_of F 0
  · simpa [offsets, hA, Real.cos_add, Real.sin_add, neg_div] using
      TerminalEstimates.frame_of F 1
  · simpa [offsets, hA, Real.cos_add, Real.sin_add, neg_div] using
      TerminalEstimates.frame_of F 2
  · simpa [offsets, hA, Real.cos_add, Real.sin_add, neg_div] using
      TerminalEstimates.frame_of F 3
  · simpa [offsets, hA, Real.cos_add, Real.sin_add, neg_div] using
      TerminalEstimates.frame_of F 4
  · simpa [offsets, hA, Real.cos_add, Real.sin_add, neg_div] using
      TerminalEstimates.frame_of F 5
  · simpa [offsets, hA, Real.cos_add, Real.sin_add, neg_div] using
      TerminalEstimates.frame_of F 6

def errors {q : ℝ} {C : BoundaryCycle q} (F : Frame C) : Errors :=
  ![F.theta B,F.theta T,F.theta D,F.theta E,F.theta H-tilt F.theta]
def positions {q : ℝ} (C : BoundaryCycle q) : Positions :=
  OriginalDual.ofCycle (fun i => (C.square i).center)

theorem error_sum {q : ℝ} {C : BoundaryCycle q} (F : Frame C) :
    errorSum (errors F)=mismatch F.theta := by
  have hA2 : F.theta 2 = 0 := F.theta_A
  simp [errorSum,errors,tree,mismatch,charged,delta,next,tilt,H,G,B,T,D,E,
    Fin.sum_univ_succ,hA2,abs_sub_comm]
  ring

theorem selected_vertex {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Fin 5) :
    closedSquare (C.square (OriginalDual.cycleIndex i.castSucc.castSucc))
      (add (positions C i.castSucc.castSucc) (offset (tilt F.theta) (errors F) i)) := by
  obtain ⟨⟨hHc,hHs⟩,-,⟨hAc,hAs⟩,⟨hBc,hBs⟩,-,⟨hDc,hDs⟩,⟨hEc,hEs⟩⟩ := TerminalEstimates.frames F
  let k := OriginalDual.cycleIndex i.castSucc.castSucc
  let v : ℝ := if i = 0 ∨ i = 4 then -1/2 else 1/2
  -- Each selected point is the corner with local coordinates (1/2, ±1/2).
  have hoffset : offset (tilt F.theta) (errors F) i = rotate (C.square k) (1/2,v) := by
    fin_cases i <;> apply Prod.ext <;>
      simp [k,v,offset,errors,tilt,H,B,D,E,OriginalDual.cycleIndex,rotate,R,
        hAc,hAs,hBc,hBs,hDc,hDs,hEc,hEs,hHc,hHs] <;> ring
  rw [hoffset]
  change closedSquare (C.square k) (add (C.square k).center (rotate (C.square k) (1/2,v)))
  simp only [closedSquare,localX_rotated,localY_rotated]
  dsimp [v]
  split_ifs <;> norm_num

theorem vertex_containment {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Fin 5) :
    normSq (add (positions C i.castSucc.castSucc) (offset (tilt F.theta) (errors F) i))≤q := by
  let j := OriginalDual.cycleIndex i.castSucc.castSucc
  have hK := C.contained j
  have hnonneg : 0 ≤ SquaresInCircles.phi (alpha (C.square j) (0,0))
      (beta (C.square j) (0,0)) := by
    unfold SquaresInCircles.phi
    positivity
  have hq : 0 ≤ q := hnonneg.trans hK
  exact ((SqContained.iff_points hq (C.square j)).mp hK) _ (selected_vertex F i)

theorem owners_and_gaps {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (ho : OwnerRestriction C terminalOwners) :
    ∃ o : Owners, ∀ i : Fin 7,
      0≤actualGap (tilt F.theta) (errors F) o (positions C) i := by
  have hj (i : Vertex) : ∃ j : Fin 4,
      j∈terminalOwners i ∧ (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨j,hj⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨j,ho i j (hj ▸ C.feasible i),hj ▸ C.feasible i⟩
  choose j hjmem hjsep using hj
  let o : Owners := ![decide (j A=2),decide (j B=3),decide (j T=0),
    decide (j D=2),decide (j H=0)]
  let edge : Fin 7 → Vertex := ![2,3,4,5,1,0,6]
  -- Quarter turns and reversing an edge preserve its support width.
  have hthreshold (k : Vertex) : SAT.threshold (C.square k) (C.square (next k)) =
      1 + Candidate.h (delta F.theta k) := by
    rw [SAT.threshold,(F.relative_trig k).1,(F.relative_trig k).2]
    have hh := h_phi F.theta k
    rw [h_abs] at hh
    rw [← hh]
    dsimp [Candidate.h]
    ring
  have hsupport (i : Fin 7) : support (tilt F.theta) (errors F) i =
      SAT.threshold (C.square (edge i)) (C.square (next (edge i))) := by
    rw [hthreshold]
    have hs : support (tilt F.theta) (errors F) i =
        1 + Candidate.h (phases (tilt F.theta) (errors F) (heads i) -
          phases (tilt F.theta) (errors F) (tails i)) := by
      dsimp [support,Candidate.h]
      ring
    rw [hs]
    have hA : F.theta 2 = 0 := F.theta_A
    have hflip (x y : ℝ) : Candidate.h (x-y) = Candidate.h (y-x) := by
      simpa only [neg_sub] using (h_neg (x-y)).symm
    fin_cases i <;> simp [edge,phases,errors,heads,tails,tilt,H,G,B,T,D,E,delta,next,hA,h_neg]
    all_goals exact hflip _ _
  -- The owner selects one of the two allowed normals on each aligned edge.
  have hprojection (i : Fin 7) :
      dot (normal (tilt F.theta) (errors F) o i)
          (sub (positions C (heads i)) (positions C (tails i))) =
        (forwardAxis (j (edge i))).projection (C.square (edge i)) (C.square (next (edge i))) := by
    obtain ⟨⟨hHc,hHs⟩,⟨hGc,hGs⟩,⟨hAc,hAs⟩,⟨hBc,hBs⟩,⟨hTc,hTs⟩,⟨hDc,hDs⟩,⟨hEc,hEs⟩⟩ :=
      TerminalEstimates.frames F
    have hmem := hjmem (edge i)
    generalize ha : j (edge i) = axis at hmem ⊢
    fin_cases i <;> fin_cases axis <;> norm_num [edge,terminalOwners] at hmem
    all_goals
      simp [edge] at ha
      simp [edge,normal,positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,heads,tails,
        o,ownerB,ownerU,ownerV,ownerD,ownerH,errors,tilt,A,B,T,D,E,H,G,ha,next,
        forwardAxis,SignedAxis.projection,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
        ex,ey,e,f,dot,sub,scale,hHc,hHs,hGc,hGs,hAc,hAs,hBc,hBs,hTc,hTs,hDc,hDs,hEc,hEs]
      <;> ring
  refine ⟨o,fun i => ?_⟩
  rw [actualGap,hprojection,hsupport]
  exact sub_nonneg.mpr (hjsep (edge i))


theorem contained_center_bound {q : ℝ} {K : UnitSquare} (hq : q≤Q0) (hK : SqContained q K) :
    normSq K.center≤9/4 := by
  have hradial := radial_sq_le_of_phi (alpha_nonneg K (0,0)) (beta_nonneg K (0,0))
    (hK.trans (hq.trans (by norm_num [Q0] : Q0 ≤ (3/2:ℝ)^2+3/2+1/2)))
  calc
    normSq K.center = (alpha K (0,0))^2+(beta K (0,0))^2 := by
      simpa [sub] using local_center_norm K (0,0)
    _ ≤ (3/2:ℝ)^2 := hradial
    _ = 9/4 := by norm_num

theorem automatic_projections {q z : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q≤Q0) (hz : z ∈ tiltBox) (hS : mismatch F.theta≤1/1000) :
    |(positions C 5).1|≤3/2 ∧ |(positions C 5).2|≤3/2 ∧
    |dot (ex (tilt F.theta)) (positions C 6)|≤3/2 ∧
    |dot (ey (tilt F.theta)) (positions C 6)|≤3/2 ∧
    (557/1000≤(positions C 5).2 ∧ (positions C 5).2≤1417/1000) ∧
    (-515/1000≤dot (ey (tilt F.theta)) (positions C 6)-(adaptiveData z hz).h₂-1/2 ∧
      dot (ey (tilt F.theta)) (positions C 6)-(adaptiveData z hz).h₂-1/2≤392/1000) := by
  have hTn := contained_center_bound hq (C.contained T)
  have hGn := contained_center_bound hq (C.contained G)
  have hGx := cauchy_sq (ex (tilt F.theta)) (positions C 6)
  have hGy := cauchy_sq (ey (tilt F.theta)) (positions C 6)
  rw [norm_ex] at hGx
  rw [norm_ey] at hGy
  obtain ⟨haT,haTu,hbT,hbTu⟩ := canonical_bounds C hq T
  obtain ⟨haG,haGu,hbG,hbGu⟩ := canonical_bounds C hq G
  obtain ⟨-,⟨hGc,hGs⟩,-,-,⟨hTc,hTs⟩,-,-⟩ := TerminalEstimates.frames F
  have heT : |F.theta T| ≤ mismatch F.theta := by
    have he := error_bound (errors F) 1
    have hh := errorSum_decompose (errors F)
    rw [error_sum F] at hh
    simpa [errors,T,B] using (he.trans
      (by linarith only [hh, abs_nonneg (errors F 4)] : chainSum (errors F) ≤ mismatch F.theta))
  have htc := (small_angle (heT.trans hS)).1
  have hts := (small_angle (heT.trans hS)).2
  have hpT : (positions C 5).2=C.a T*Real.cos (F.theta T)+
      C.sigma T*C.b T*Real.sin (F.theta T) := by
    show (C.square 4).center.2 =
      C.a 4*Real.cos (F.theta 4)+C.sigma 4*C.b 4*Real.sin (F.theta 4)
    rw [C.center_eq 4]
    simp only [rotate, hTc, hTs]
    ring
  have hpG : dot (ey (tilt F.theta)) (positions C 6)= -C.a G := by
    show dot (ey (F.theta 1)) (C.square 1).center = -C.a 1
    rw [C.center_eq 1]
    simp only [dot, ey, rotate, hGc, hGs]
    linear_combination -(C.a 1)*(Real.cos_sq_add_sin_sq (F.theta 1))
  have habsT : |C.sigma T*C.b T*Real.sin (F.theta T)|≤9/10000 := by
    rw [abs_mul,signed_b_abs]
    exact (mul_le_mul_of_nonneg_left hts hbT).trans
      (by linarith only [hbTu] : C.b T*(1/1000)≤9/10000)
  have hcosT : 0≤Real.cos (F.theta T) := by linarith only [htc]
  have hprod := mul_le_mul_of_nonneg_left htc (C.a_pos T).le
  have hprod1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (F.theta T)) (C.a_pos T).le
  have hTproj : 557/1000≤(positions C 5).2 ∧ (positions C 5).2≤1417/1000 := by
    rw [hpT]
    have hh := abs_le.mp habsT
    constructor <;> linarith only [hh.1, hh.2, hprod, hprod1, haT, haTu]
  have h₂ := adaptive_hTwo_bound hz
  have hT5 : (positions C 5).1^2+(positions C 5).2^2 ≤ 9/4 := hTn
  have hG6 : normSq (positions C 6) ≤ 9/4 := hGn
  refine ⟨?_,?_,?_,?_,hTproj,?_⟩
  · exact abs_le_of_sq_le_sq (by linarith only [hT5, sq_nonneg (positions C 5).2]) (by norm_num)
  · exact abs_le_of_sq_le_sq (by linarith only [hT5, sq_nonneg (positions C 5).1]) (by norm_num)
  · exact abs_le_of_sq_le_sq (hGx.trans (by rw [one_mul]; linarith only [hG6])) (by norm_num)
  · exact abs_le_of_sq_le_sq (hGy.trans (by rw [one_mul]; linarith only [hG6])) (by norm_num)
  · rw [hpG]
    obtain ⟨h₂l, h₂u⟩ := h₂
    generalize (adaptiveData z hz).h₂ = H at h₂l h₂u ⊢
    constructor <;> linarith only [h₂l, h₂u, haG, haGu]

end Terminal
end SquaresInCircles.Eight
