module

public import SquaresInCircles.Eight.ExactFamily.CenterCompletion
public import SquaresInCircles.Eight.ExactFamily.Perturbation
public import SquaresInCircles.Eight.Candidate.Geometry

/-!
# Boundary terminal and original-center pullback

Uncompiled draft.  The positive-error theorem is applied to the recovered
boundary cycle at its own containing radius.  After it forces zero errors,
the stationary dual is applied anew to the original centers.  The latter
step has no slider bounds or assumptions about displaced centers.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open ExactFamily Coordinates
namespace Terminal
open Candidate Perturbation

def errors {q : ℝ} {C : BoundaryCycle q} (F : Frame C) : Errors :=
  ![F.theta B,F.theta T,F.theta D,F.theta E,F.theta H-tilt F.theta]
def positions {q : ℝ} (C : BoundaryCycle q) : Positions :=
  OriginalDual.ofCycle (fun i => (C.square i).center)

theorem error_sum {q : ℝ} {C : BoundaryCycle q} (F : Frame C) :
    errorSum (errors F)=mismatch F.theta := by
  simp [errorSum,errors,tree,mismatch,charged,delta,next,tilt,H,G,A,B,T,D,E,
    Fin.sum_univ_succ,F.theta_A,abs_sub_comm]
  ring

theorem physical_phases {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Fin 7) :
    phases (tilt F.theta) (errors F) i=F.theta (OriginalDual.cycleIndex i) := by
  fin_cases i <;> simp [phases,errors,tilt,OriginalDual.cycleIndex,H,G,A,B,T,D,E,F.theta_A]

theorem selected_vertex {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Fin 5) :
    closedSquare (C.square (OriginalDual.cycleIndex i.castSucc.castSucc))
      (add (positions C i.castSucc.castSucc) (offset (tilt F.theta) (errors F) i)) := by
  have hc (j : Vertex) := C.frame_cos j
  have hs (j : Vertex) := C.frame_sin j
  have hf (j : Vertex) := F.canonical_eq j
  have hunit (x : ℝ) := Real.cos_sq_add_sin_sq x
  fin_cases i <;>
    simp [closedSquare,localX,localY,positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      offset,errors,R,add,tilt,H,G,A,B,T,D,E,hc,hs,hf,offsets,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,F.theta_A] <;>
    norm_num <;> nlinarith [hunit (F.theta 0),hunit (F.theta 3),
      hunit (F.theta 5),hunit (F.theta 6)]

theorem vertex_containment {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Fin 5) :
    normSq (add (positions C i.castSucc.castSucc) (offset (tilt F.theta) (errors F) i))≤q :=
  ((SqContained.iff_points _ _).mp (C.contained _)) _ (selected_vertex F i)

theorem owners_and_gaps {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (ho : OwnerRestriction C terminalOwners) :
    ∃ o : Owners, ∀ i : Fin 7,
      0≤actualGap (tilt F.theta) (errors F) o (positions C) i := by
  have hj (i : Vertex) : ∃ j : Fin 4,
      j∈terminalOwners i ∧ (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨j,hj⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    refine ⟨j,ho i j (hj ▸ C.feasible i),hj ▸ C.feasible i⟩
  choose j hjmem hjsep using hj
  let o : Owners := ![decide (j A=2),decide (j B=3),decide (j T=0),
    decide (j D=2),decide (j H=0)]
  refine ⟨o,?_⟩
  intro i
  have hmem0 := hjmem 0; have hmem1 := hjmem 1; have hmem2 := hjmem 2
  have hmem3 := hjmem 3; have hmem4 := hjmem 4; have hmem5 := hjmem 5; have hmem6 := hjmem 6
  have hsep0 := hjsep 0; have hsep1 := hjsep 1; have hsep2 := hjsep 2
  have hsep3 := hjsep 3; have hsep4 := hjsep 4; have hsep5 := hjsep 5; have hsep6 := hjsep 6
  simp only [terminalOwners,Finset.mem_insert,Finset.mem_singleton,
    Matrix.cons_val_zero,Matrix.cons_val_succ] at hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6
  have hc (k : Vertex) := C.frame_cos k
  have hs (k : Vertex) := C.frame_sin k
  have hf (k : Vertex) := F.canonical_eq k
  fin_cases i <;> rcases hmem0 with hmem0 | hmem0 <;>
    rcases hmem2 with hmem2 | hmem2 <;> rcases hmem3 with hmem3 | hmem3 <;>
    rcases hmem4 with hmem4 | hmem4 <;> rcases hmem5 with hmem5 | hmem5
  all_goals
    simp [actualGap,normal,support,phases,positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      tails,heads,errors,ownerB,ownerU,ownerV,ownerD,ownerH,o,
      hmem0,hmem1,hmem2,hmem3,hmem4,hmem5,hmem6,tilt,H,G,A,B,T,D,E,
      SignedAxis.Feasible,SignedAxis.projection,SignedAxis.normal,AxisOwner.normal,
      AxisSign.value,forwardAxis,SAT.threshold,relativeC,relativeS,
      dot,sub,scale,e,f,ex,ey,hc,hs,hf,offsets,F.theta_A,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,Real.cos_neg,Real.sin_neg,
      abs_neg,abs_sub_comm,add_comm,add_left_comm,add_assoc] at hsep0 hsep1 hsep2 hsep3 hsep4 hsep5 hsep6 ⊢
  all_goals first | linarith | nlinarith [Real.cos_sq_add_sin_sq (F.theta 0),
    Real.cos_sq_add_sin_sq (F.theta 1),Real.cos_sq_add_sin_sq (F.theta 3),
    Real.cos_sq_add_sin_sq (F.theta 4),Real.cos_sq_add_sin_sq (F.theta 5),
    Real.cos_sq_add_sin_sq (F.theta 6)]

theorem contained_center_bound {q : ℝ} {K : UnitSquare} (hq : q≤Q0) (hK : SqContained q K) :
    normSq K.center≤9/4 := by
  have ha := alpha_nonneg K (0,0)
  have hb := beta_nonneg K (0,0)
  have hc := local_center_norm K (0,0)
  have hp := hK.trans hq
  dsimp [SqContained,phi,Q0] at hp
  simp [sub] at hc
  by_contra! hn
  have hsum : alpha K (0,0)+beta K (0,0)>3/2 := by
    by_contra! hh
    nlinarith [mul_nonneg ha hb]
  nlinarith

theorem automatic_projections {q z : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q≤Q0) (hz : z ∈ tiltBox)
    (ht : tilt F.theta=2*Real.arctan z) (hS : mismatch F.theta≤1/1000) :
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
  have heT : |F.theta T|≤mismatch F.theta := by
    have he := error_bound (errors F) 1
    have hh := errorSum_decompose (errors F)
    rw [error_sum F] at hh
    simpa [errors,T,B] using (he.trans (by linarith : chainSum (errors F)≤mismatch F.theta))
  have htc := (small_angle (heT.trans hS)).1
  have hts := (small_angle (heT.trans hS)).2
  have hpT : (positions C 5).2=C.a T*Real.cos (F.theta T)+
      C.sigma T*C.b T*Real.sin (F.theta T) := by
    simp [positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,T,C.center_eq,
      rotate,C.frame_cos,C.frame_sin,F.canonical_eq,offsets,Real.cos_add,Real.sin_add]
  have hpG : dot (ey (tilt F.theta)) (positions C 6)= -C.a G := by
    simp [positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,G,tilt,C.center_eq,
      rotate,C.frame_cos,C.frame_sin,F.canonical_eq,offsets,Real.cos_sub,Real.sin_sub,
      dot,ey]
    linear_combination -(C.a G)*(Real.cos_sq_add_sin_sq (F.theta G))
  have habsT : |C.sigma T*C.b T*Real.sin (F.theta T)|≤9/10000 := by
    rw [abs_mul,signed_b_abs]
    exact (mul_le_mul_of_nonneg_left hts hbT).trans
      (by nlinarith : C.b T*(1/1000)≤9/10000)
  have hcosT : 0≤Real.cos (F.theta T) := by norm_num at htc; linarith
  have hprod := mul_le_mul_of_nonneg_left htc haT.le
  have hprod1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (F.theta T)) haT.le
  have hTproj : 557/1000≤(positions C 5).2 ∧ (positions C 5).2≤1417/1000 := by
    rw [hpT]
    have hh := abs_le.mp habsT
    constructor <;> norm_num at * <;> nlinarith
  have h₂ := adaptive_hTwo_bound hz
  refine ⟨?_,?_,?_,?_,hTproj,?_⟩
  · rw [abs_le]
    constructor <;> dsimp [positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,T,normSq] at * <;>
      nlinarith [sq_nonneg (positions C 5).2]
  · rw [abs_le]
    constructor <;> dsimp [positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,T,normSq] at * <;>
      nlinarith [sq_nonneg (positions C 5).1]
  · rw [abs_le]
    constructor <;> dsimp [positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,G] at * <;> nlinarith
  · rw [abs_le]
    constructor <;> dsimp [positions,OriginalDual.ofCycle,OriginalDual.cycleIndex,G] at * <;> nlinarith
  · rw [hpG]
    constructor <;> linarith

theorem boundary_quantitative {q z : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q≤Q0) (hz : z ∈ tiltBox) (ht : tilt F.theta=2*Real.arctan z)
    (htw : 1/10≤tilt F.theta ∧ tilt F.theta≤4/25)
    (hS : mismatch F.theta≤1/1000) (ho : OwnerRestriction C terminalOwners) :
    ∃ o : Owners,
      qStar+((adaptiveData z hz).mu 4/8)*(z-sharpData.z)^2+
        completed (adaptiveData z hz) (tilt F.theta) (errors F) o (positions C)+
        terminalReserve*mismatch F.theta≤q := by
  obtain ⟨o,hg⟩ := owners_and_gaps F ho
  obtain ⟨hX,hZabs,hU,hV,hZ,hη⟩ := automatic_projections F hq hz ht hS
  refine ⟨o,?_⟩
  simpa [error_sum F] using quantitative hz ht htw (errors F) o (positions C)
    (by simpa [error_sum F] using hS) (vertex_containment F) hg hX hZabs hU hV hZ hη

theorem boundary_rigid {q z : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q≤qStar) (hz : z ∈ tiltBox) (ht : tilt F.theta=2*Real.arctan z)
    (htw : 1/10≤tilt F.theta ∧ tilt F.theta≤4/25)
    (hS : mismatch F.theta≤1/1000) (ho : OwnerRestriction C terminalOwners) :
    q=qStar ∧ z=sharpData.z ∧ mismatch F.theta=0 := by
  obtain ⟨o,hineq⟩ := boundary_quantitative F
    (hq.trans qStar_limits.2.2.le) hz ht htw hS ho
  have hμ := (adaptive_weightDomain hz).mu_pos 4
  have hcomp := completed_nonneg (adaptive_weightDomain hz) (tilt F.theta) (errors F) o (positions C)
  have hs := mismatch_nonneg F.theta
  have hρ : 0<terminalReserve := terminal_constants.2.2.2.2.1
  have hsq := sq_nonneg (z-sharpData.z)
  have hcurv : 0≤((adaptiveData z hz).mu 4/8)*(z-sharpData.z)^2 := by positivity
  have hprod := mul_nonneg hρ.le hs
  refine ⟨by linarith,?_,?_⟩ <;> nlinarith

/-- The second use of the dual, on untouched original centers.  This theorem
deliberately has neither displacement nor projected-slider assumptions. -/
theorem original_pullback {p : Positions}
    (hv : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (sharpData.anchorOffsets i))≤qStar)
    (hg : ∀ e : Fin 7, 0≤OriginalDual.gap sharpData p e) :
    (∀ i : Fin 5, p i.castSucc.castSucc=sharpData.anchorCenters i) ∧
    (∀ e : Fin 7, OriginalDual.gap sharpData p e=0) ∧
      ∃ Z η : ℝ, p 5=sharpData.pT Z ∧ p 6=sharpData.pG η := by
  have h := OriginalDual.original_centers_rigid sharpData_stationary.toIsChain
    sharpData_stationary.weightDomain sharpData_stationary.zero_defect
    sharpData_stationary.position_stationary hv hg
  exact ⟨h.1,h.2,OriginalDual.slider_coordinates (h.1 1) (h.1 4) (h.2 1) (h.2 5)⟩

end Terminal
end SquaresInCircles.Eight
