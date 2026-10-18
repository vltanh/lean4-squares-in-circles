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

These are estimates, used in `Terminal.lean` together with the positivity argument; the optimal
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
  have h0 := TerminalEstimates.frame_of F 0
  have h1 := TerminalEstimates.frame_of F 1
  have h2 := TerminalEstimates.frame_of F 2
  have h3 := TerminalEstimates.frame_of F 3
  have h4 := TerminalEstimates.frame_of F 4
  have h5 := TerminalEstimates.frame_of F 5
  have h6 := TerminalEstimates.frame_of F 6
  have e0 : ((offsets 0 : ℤ) : ℝ) = -1 := by simp [offsets]
  have e1 : ((offsets 1 : ℤ) : ℝ) = -1 := by simp [offsets]
  have e2 : ((offsets 2 : ℤ) : ℝ) = 0 := by simp [offsets]
  have e3 : ((offsets 3 : ℤ) : ℝ) = 0 := by simp [offsets]
  have e4 : ((offsets 4 : ℤ) : ℝ) = 1 := by simp [offsets]
  have e5 : ((offsets 5 : ℤ) : ℝ) = 1 := by simp [offsets]
  have e6 : ((offsets 6 : ℤ) : ℝ) = 2 := by simp [offsets]
  have o0 : F.theta 0 + ((offsets 0 : ℤ) : ℝ) * Real.pi / 2 = F.theta 0 - Real.pi / 2 := by
    rw [e0]; ring
  have o1 : F.theta 1 + ((offsets 1 : ℤ) : ℝ) * Real.pi / 2 = F.theta 1 - Real.pi / 2 := by
    rw [e1]; ring
  have o2 : F.theta 2 + ((offsets 2 : ℤ) : ℝ) * Real.pi / 2 = 0 := by
    rw [e2, hA]; ring
  have o3 : F.theta 3 + ((offsets 3 : ℤ) : ℝ) * Real.pi / 2 = F.theta 3 := by
    rw [e3]; ring
  have o4 : F.theta 4 + ((offsets 4 : ℤ) : ℝ) * Real.pi / 2 = F.theta 4 + Real.pi / 2 := by
    rw [e4]; ring
  have o5 : F.theta 5 + ((offsets 5 : ℤ) : ℝ) * Real.pi / 2 = F.theta 5 + Real.pi / 2 := by
    rw [e5]; ring
  have o6 : F.theta 6 + ((offsets 6 : ℤ) : ℝ) * Real.pi / 2 = F.theta 6 + Real.pi := by
    rw [e6]; ring
  rw [o0, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two] at h0
  rw [o1, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two] at h1
  rw [o2, Real.cos_zero, Real.sin_zero] at h2
  rw [o3] at h3
  rw [o4, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at h4
  rw [o5, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at h5
  rw [o6, Real.cos_add_pi, Real.sin_add_pi] at h6
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

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

theorem physical_phases {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Fin 7) :
    phases (tilt F.theta) (errors F) i=F.theta (OriginalDual.cycleIndex i) := by
  have hA2 : F.theta 2 = 0 := F.theta_A
  fin_cases i <;> simp [phases,errors,tilt,OriginalDual.cycleIndex,H,G,B,T,D,E,hA2]

theorem selected_vertex {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Fin 5) :
    closedSquare (C.square (OriginalDual.cycleIndex i.castSucc.castSucc))
      (add (positions C i.castSucc.castSucc) (offset (tilt F.theta) (errors F) i)) := by
  obtain ⟨⟨hHc,hHs⟩,-,⟨hAc,hAs⟩,⟨hBc,hBs⟩,-,⟨hDc,hDs⟩,⟨hEc,hEs⟩⟩ := TerminalEstimates.frames F
  have hunit (x : ℝ) := Real.cos_sq_add_sin_sq x
  fin_cases i
  · -- the selected corner of A
    show closedSquare (C.square 2) (add (C.square 2).center (1/2, -1/2))
    have hx : localX (C.square 2) (add (C.square 2).center (1/2, -1/2)) = 1/2 := by
      simp only [localX, add, hAc, hAs]; ring
    have hy : localY (C.square 2) (add (C.square 2).center (1/2, -1/2)) = -1/2 := by
      simp only [localY, add, hAc, hAs]; ring
    exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
  · -- the selected corner of B
    show closedSquare (C.square 3) (add (C.square 3).center (R (F.theta 3) (1/2, 1/2)))
    have hx : localX (C.square 3) (add (C.square 3).center (R (F.theta 3) (1/2, 1/2))) = 1/2 := by
      simp only [localX, add, R, hBc, hBs]
      linear_combination (1/2 : ℝ) * hunit (F.theta 3)
    have hy : localY (C.square 3) (add (C.square 3).center (R (F.theta 3) (1/2, 1/2))) = 1/2 := by
      simp only [localY, add, R, hBc, hBs]
      linear_combination (1/2 : ℝ) * hunit (F.theta 3)
    exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
  · -- the selected corner of D
    show closedSquare (C.square 5) (add (C.square 5).center (R (F.theta 5) (-1/2, 1/2)))
    have hx : localX (C.square 5) (add (C.square 5).center (R (F.theta 5) (-1/2, 1/2))) =
        1/2 := by
      simp only [localX, add, R, hDc, hDs]
      linear_combination (1/2 : ℝ) * hunit (F.theta 5)
    have hy : localY (C.square 5) (add (C.square 5).center (R (F.theta 5) (-1/2, 1/2))) =
        1/2 := by
      simp only [localY, add, R, hDc, hDs]
      linear_combination (1/2 : ℝ) * hunit (F.theta 5)
    exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
  · -- the selected corner of E
    show closedSquare (C.square 6) (add (C.square 6).center (R (F.theta 6) (-1/2, -1/2)))
    have hx : localX (C.square 6) (add (C.square 6).center (R (F.theta 6) (-1/2, -1/2))) =
        1/2 := by
      simp only [localX, add, R, hEc, hEs]
      linear_combination (1/2 : ℝ) * hunit (F.theta 6)
    have hy : localY (C.square 6) (add (C.square 6).center (R (F.theta 6) (-1/2, -1/2))) =
        1/2 := by
      simp only [localY, add, R, hEc, hEs]
      linear_combination (1/2 : ℝ) * hunit (F.theta 6)
    exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
  · -- the selected corner of H
    show closedSquare (C.square 0) (add (C.square 0).center
      (R (tilt F.theta + (F.theta H - tilt F.theta)) (-1/2, -1/2)))
    have hψ : tilt F.theta + (F.theta H - tilt F.theta) = F.theta 0 := by
      simp only [H]; ring
    rw [hψ]
    have hx : localX (C.square 0) (add (C.square 0).center (R (F.theta 0) (-1/2, -1/2))) =
        1/2 := by
      simp only [localX, add, R, hHc, hHs]
      linear_combination (1/2 : ℝ) * hunit (F.theta 0)
    have hy : localY (C.square 0) (add (C.square 0).center (R (F.theta 0) (-1/2, -1/2))) =
        -1/2 := by
      simp only [localY, add, R, hHc, hHs]
      linear_combination (-1/2 : ℝ) * hunit (F.theta 0)
    exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩

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
  refine ⟨o,?_⟩
  obtain ⟨⟨hHc,hHs⟩,⟨hGc,hGs⟩,⟨hAc,hAs⟩,⟨hBc,hBs⟩,⟨hTc,hTs⟩,⟨hDc,hDs⟩,⟨hEc,hEs⟩⟩ :=
    TerminalEstimates.frames F
  -- the owners allowed by the terminal owner sets
  have hown (k : Vertex) (x y : Fin 4) (hk : terminalOwners k = {x, y}) :
      j k = x ∨ j k = y := by
    have hm := hjmem k
    rw [hk] at hm
    simpa using hm
  have j0 : j 0 = 0 ∨ j 0 = 2 := hown 0 0 2 rfl
  have j2 : j 2 = 0 ∨ j 2 = 2 := hown 2 0 2 rfl
  have j3 : j 3 = 2 ∨ j 3 = 3 := hown 3 2 3 rfl
  have j4 : j 4 = 0 ∨ j 4 = 2 := hown 4 0 2 rfl
  have j5 : j 5 = 2 ∨ j 5 = 3 := hown 5 2 3 rfl
  have j1 : j 1 = 0 := by simpa [terminalOwners] using hjmem 1
  have j6 : j 6 = 1 := by simpa [terminalOwners] using hjmem 6
  -- edge A → B, cycle edge 2
  have g0 : 0 ≤ actualGap (tilt F.theta) (errors F) o (positions C) 0 := by
    have hsep : SAT.threshold (C.square 2) (C.square 3) ≤
        (forwardAxis (j 2)).projection (C.square 2) (C.square 3) := hjsep 2
    have hthr : SAT.threshold (C.square 2) (C.square 3) =
        (1 + |Real.cos (F.theta 3)| + |Real.sin (F.theta 3)|) / 2 := by
      have hc : relativeC (C.square 2) (C.square 3) = Real.cos (F.theta 3) := by
        rw [relativeC, hAc, hAs, hBc, hBs]; ring
      have hs : relativeS (C.square 2) (C.square 3) = Real.sin (F.theta 3) := by
        rw [relativeS, hAc, hAs, hBc, hBs]; ring
      rw [SAT.threshold, hc, hs]
    have hΔ : phases (tilt F.theta) (errors F) (heads 0) -
        phases (tilt F.theta) (errors F) (tails 0) = F.theta 3 := by
      simp [phases, heads, tails, errors, B]
    have hgap : actualGap (tilt F.theta) (errors F) o (positions C) 0 =
        dot (ey (ownerB (errors F) o)) (sub (C.square 3).center (C.square 2).center) -
          (1 + |Real.cos (F.theta 3)| + |Real.sin (F.theta 3)|) / 2 := by
      rw [actualGap, support, hΔ]
      rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j2 with h | h
    · rw [h] at hsep
      have hb : ownerB (errors F) o = 0 := by simp [ownerB, o, h, A]
      rw [hb]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ey, dot, sub, scale, hAc, hAs] at hsep ⊢
      linarith
    · rw [h] at hsep
      have hb : ownerB (errors F) o = F.theta 3 := by simp [ownerB, o, h, A, errors, B]
      rw [hb]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ey, dot, sub, scale, hBc, hBs] at hsep ⊢
      linarith
  -- edge B → T, cycle edge 3, read from T to B
  have g1 : 0 ≤ actualGap (tilt F.theta) (errors F) o (positions C) 1 := by
    have hsep : SAT.threshold (C.square 3) (C.square 4) ≤
        (forwardAxis (j 3)).projection (C.square 3) (C.square 4) := hjsep 3
    have hthr : SAT.threshold (C.square 3) (C.square 4) =
        (1 + |Real.cos (F.theta 3 - F.theta 4)| + |Real.sin (F.theta 3 - F.theta 4)|) / 2 := by
      have hc : relativeC (C.square 3) (C.square 4) = Real.sin (F.theta 3 - F.theta 4) := by
        rw [relativeC, hBc, hBs, hTc, hTs, Real.sin_sub]; ring
      have hs : relativeS (C.square 3) (C.square 4) = Real.cos (F.theta 3 - F.theta 4) := by
        rw [relativeS, hBc, hBs, hTc, hTs, Real.cos_sub]; ring
      rw [SAT.threshold, hc, hs]; ring
    have hΔ : phases (tilt F.theta) (errors F) (heads 1) -
        phases (tilt F.theta) (errors F) (tails 1) = F.theta 3 - F.theta 4 := by
      simp [phases, heads, tails, errors, B, T]
    have hgap : actualGap (tilt F.theta) (errors F) o (positions C) 1 =
        dot (ex (ownerU (errors F) o)) (sub (C.square 3).center (C.square 4).center) -
          (1 + |Real.cos (F.theta 3 - F.theta 4)| + |Real.sin (F.theta 3 - F.theta 4)|) / 2 := by
      rw [actualGap, support, hΔ]
      rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j3 with h | h
    · rw [h] at hsep
      have hu : ownerU (errors F) o = F.theta 4 := by simp [ownerU, o, h, B, errors, T]
      rw [hu]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ex, dot, sub, scale, hTc, hTs] at hsep ⊢
      linarith
    · rw [h] at hsep
      have hu : ownerU (errors F) o = F.theta 3 := by simp [ownerU, o, h, B, errors]
      rw [hu]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, e, ex, dot, sub, scale, hBc, hBs] at hsep ⊢
      linarith
  -- edge T → D, cycle edge 4, read from D to T
  have g2 : 0 ≤ actualGap (tilt F.theta) (errors F) o (positions C) 2 := by
    have hsep : SAT.threshold (C.square 4) (C.square 5) ≤
        (forwardAxis (j 4)).projection (C.square 4) (C.square 5) := hjsep 4
    have hthr : SAT.threshold (C.square 4) (C.square 5) =
        (1 + |Real.cos (F.theta 4 - F.theta 5)| + |Real.sin (F.theta 4 - F.theta 5)|) / 2 := by
      have hc : relativeC (C.square 4) (C.square 5) = Real.cos (F.theta 4 - F.theta 5) := by
        rw [relativeC, hTc, hTs, hDc, hDs, Real.cos_sub]; ring
      have hs : relativeS (C.square 4) (C.square 5) = -Real.sin (F.theta 4 - F.theta 5) := by
        rw [relativeS, hTc, hTs, hDc, hDs, Real.sin_sub]; ring
      rw [SAT.threshold, hc, hs, abs_neg]
    have hΔ : phases (tilt F.theta) (errors F) (heads 2) -
        phases (tilt F.theta) (errors F) (tails 2) = F.theta 4 - F.theta 5 := by
      simp [phases, heads, tails, errors, T, D]
    have hgap : actualGap (tilt F.theta) (errors F) o (positions C) 2 =
        dot (ex (ownerV (errors F) o)) (sub (C.square 4).center (C.square 5).center) -
          (1 + |Real.cos (F.theta 4 - F.theta 5)| + |Real.sin (F.theta 4 - F.theta 5)|) / 2 := by
      rw [actualGap, support, hΔ]
      rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j4 with h | h
    · rw [h] at hsep
      have hv : ownerV (errors F) o = F.theta 4 := by simp [ownerV, o, h, T, errors]
      rw [hv]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ex, dot, sub, scale, hTc, hTs] at hsep ⊢
      linarith
    · rw [h] at hsep
      have hv : ownerV (errors F) o = F.theta 5 := by simp [ownerV, o, h, T, errors, D]
      rw [hv]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ex, dot, sub, scale, hDc, hDs] at hsep ⊢
      linarith
  -- edge D → E, cycle edge 5, read from E to D
  have g3 : 0 ≤ actualGap (tilt F.theta) (errors F) o (positions C) 3 := by
    have hsep : SAT.threshold (C.square 5) (C.square 6) ≤
        (forwardAxis (j 5)).projection (C.square 5) (C.square 6) := hjsep 5
    have hthr : SAT.threshold (C.square 5) (C.square 6) =
        (1 + |Real.cos (F.theta 5 - F.theta 6)| + |Real.sin (F.theta 5 - F.theta 6)|) / 2 := by
      have hc : relativeC (C.square 5) (C.square 6) = Real.sin (F.theta 5 - F.theta 6) := by
        rw [relativeC, hDc, hDs, hEc, hEs, Real.sin_sub]; ring
      have hs : relativeS (C.square 5) (C.square 6) = Real.cos (F.theta 5 - F.theta 6) := by
        rw [relativeS, hDc, hDs, hEc, hEs, Real.cos_sub]; ring
      rw [SAT.threshold, hc, hs]; ring
    have hΔ : phases (tilt F.theta) (errors F) (heads 3) -
        phases (tilt F.theta) (errors F) (tails 3) = F.theta 5 - F.theta 6 := by
      simp [phases, heads, tails, errors, D, E]
    have hgap : actualGap (tilt F.theta) (errors F) o (positions C) 3 =
        dot (ey (ownerD (errors F) o)) (sub (C.square 5).center (C.square 6).center) -
          (1 + |Real.cos (F.theta 5 - F.theta 6)| + |Real.sin (F.theta 5 - F.theta 6)|) / 2 := by
      rw [actualGap, support, hΔ]
      rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j5 with h | h
    · rw [h] at hsep
      have hd : ownerD (errors F) o = F.theta 6 := by simp [ownerD, o, h, D, errors, E]
      rw [hd]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ey, dot, sub, scale, hEc, hEs] at hsep ⊢
      linarith
    · rw [h] at hsep
      have hd : ownerD (errors F) o = F.theta 5 := by simp [ownerD, o, h, D, errors]
      rw [hd]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, e, ey, dot, sub, scale, hDc, hDs] at hsep ⊢
      linarith
  -- edge G → A, cycle edge 1
  have g4 : 0 ≤ actualGap (tilt F.theta) (errors F) o (positions C) 4 := by
    have hsep : SAT.threshold (C.square 1) (C.square 2) ≤
        (forwardAxis (j 1)).projection (C.square 1) (C.square 2) := hjsep 1
    have hthr : SAT.threshold (C.square 1) (C.square 2) =
        (1 + |Real.cos (F.theta 1)| + |Real.sin (F.theta 1)|) / 2 := by
      have hc : relativeC (C.square 1) (C.square 2) = Real.sin (F.theta 1) := by
        rw [relativeC, hGc, hGs, hAc, hAs]; ring
      have hs : relativeS (C.square 1) (C.square 2) = Real.cos (F.theta 1) := by
        rw [relativeS, hGc, hGs, hAc, hAs]; ring
      rw [SAT.threshold, hc, hs]; ring
    have hΔ : phases (tilt F.theta) (errors F) (heads 4) -
        phases (tilt F.theta) (errors F) (tails 4) = -F.theta 1 := by
      simp [phases, heads, tails, tilt, G]
    have hgap : actualGap (tilt F.theta) (errors F) o (positions C) 4 =
        dot (ex (tilt F.theta)) (sub (C.square 2).center (C.square 1).center) -
          (1 + |Real.cos (F.theta 1)| + |Real.sin (F.theta 1)|) / 2 := by
      rw [actualGap, support, hΔ, Real.cos_neg, Real.sin_neg, abs_neg]
      rfl
    rw [hthr, j1] at hsep
    rw [hgap]
    simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
      AxisSign.value, f, ex, dot, sub, scale, hGc, hGs, tilt, G] at hsep ⊢
    linarith
  -- edge H → G, cycle edge 0
  have g5 : 0 ≤ actualGap (tilt F.theta) (errors F) o (positions C) 5 := by
    have hsep : SAT.threshold (C.square 0) (C.square 1) ≤
        (forwardAxis (j 0)).projection (C.square 0) (C.square 1) := hjsep 0
    have hthr : SAT.threshold (C.square 0) (C.square 1) =
        (1 + |Real.cos (F.theta 0 - F.theta 1)| + |Real.sin (F.theta 0 - F.theta 1)|) / 2 := by
      have hc : relativeC (C.square 0) (C.square 1) = Real.cos (F.theta 0 - F.theta 1) := by
        rw [relativeC, hHc, hHs, hGc, hGs, Real.cos_sub]; ring
      have hs : relativeS (C.square 0) (C.square 1) = -Real.sin (F.theta 0 - F.theta 1) := by
        rw [relativeS, hHc, hHs, hGc, hGs, Real.sin_sub]; ring
      rw [SAT.threshold, hc, hs, abs_neg]
    have hΔ : phases (tilt F.theta) (errors F) (heads 5) -
        phases (tilt F.theta) (errors F) (tails 5) = -(F.theta 0 - F.theta 1) := by
      simp [phases, heads, tails, errors, tilt, H, G]
    have hgap : actualGap (tilt F.theta) (errors F) o (positions C) 5 =
        dot (ex (tilt F.theta + ownerH (errors F) o)) (sub (C.square 1).center (C.square 0).center) -
          (1 + |Real.cos (F.theta 0 - F.theta 1)| + |Real.sin (F.theta 0 - F.theta 1)|) / 2 := by
      rw [actualGap, support, hΔ, Real.cos_neg, Real.sin_neg, abs_neg]
      rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j0 with h | h
    · rw [h] at hsep
      have hh : tilt F.theta + ownerH (errors F) o = F.theta 0 := by
        simp [ownerH, o, h, H, errors]
      rw [hh]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ex, dot, sub, scale, hHc, hHs] at hsep ⊢
      linarith
    · rw [h] at hsep
      have hh : tilt F.theta + ownerH (errors F) o = F.theta 1 := by
        simp [ownerH, o, h, H, tilt, G]
      rw [hh]
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, f, ex, dot, sub, scale, hGc, hGs] at hsep ⊢
      linarith
  -- edge E → H, cycle edge 6, read from H to E
  have g6 : 0 ≤ actualGap (tilt F.theta) (errors F) o (positions C) 6 := by
    have hsep : SAT.threshold (C.square 6) (C.square 0) ≤
        (forwardAxis (j 6)).projection (C.square 6) (C.square 0) := hjsep 6
    have hthr : SAT.threshold (C.square 6) (C.square 0) =
        (1 + |Real.cos (F.theta 6 - F.theta 0)| + |Real.sin (F.theta 6 - F.theta 0)|) / 2 := by
      have hc : relativeC (C.square 6) (C.square 0) = Real.sin (F.theta 6 - F.theta 0) := by
        rw [relativeC, hEc, hEs, hHc, hHs, Real.sin_sub]; ring
      have hs : relativeS (C.square 6) (C.square 0) = Real.cos (F.theta 6 - F.theta 0) := by
        rw [relativeS, hEc, hEs, hHc, hHs, Real.cos_sub]; ring
      rw [SAT.threshold, hc, hs]; ring
    have hΔ : phases (tilt F.theta) (errors F) (heads 6) -
        phases (tilt F.theta) (errors F) (tails 6) = F.theta 6 - F.theta 0 := by
      simp [phases, heads, tails, errors, tilt, H, E]
    have hn : tilt F.theta + errors F 4 = F.theta 0 := by
      simp [errors, H]
    have hgap : actualGap (tilt F.theta) (errors F) o (positions C) 6 =
        dot (ey (tilt F.theta + errors F 4)) (sub (C.square 6).center (C.square 0).center) -
          (1 + |Real.cos (F.theta 6 - F.theta 0)| + |Real.sin (F.theta 6 - F.theta 0)|) / 2 := by
      rw [actualGap, support, hΔ]
      rfl
    rw [hthr, j6] at hsep
    rw [hgap, hn]
    simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
      AxisSign.value, e, ey, dot, sub, scale, hHc, hHs] at hsep ⊢
    linarith
  intro i
  fin_cases i
  exacts [g0, g1, g2, g3, g4, g5, g6]

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
