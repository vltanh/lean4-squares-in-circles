module

public import SquaresInCircles.Eight.TableFree.GlobalBTDE2Support
public import SquaresInCircles.Eight.TableFree.GlobalBTReturn

/-!
# The complete ordinary BT0 tail on actual source states

The four actual weak separating inequalities pay the explicit dual
multipliers.  All signed AB errors and both TD owners are included.
The sole remaining tail is core E with a strictly negative DE3 error.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Candidate FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem zeroDual_le_error (s t : State) (primary : Bool) {v lambda : ℝ}
    (hl : 0≤lambda) (hp : GlobalOuterAnchor.width v≤projection false s t v (leftOwner primary)) :
    zeroDual primary s t v lambda≤v := by
  have hm := mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos.mpr hp)
  dsimp [zeroDual]
  linarith

theorem quarterDual_le_error (s t : State) (j : Fin 4) {v lambda : ℝ}
    (hl : 0≤lambda) (hp : GlobalOuterAnchor.width v≤projection true s t v j) :
    quarterDual s t j v lambda≤v := by
  have hm := mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos.mpr hp)
  dsimp [quarterDual]
  linarith

theorem ordinary_path (a b t d e : State) (ab td : Bool) (jD : Fin 4)
    {v x w y : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hv : |v|≤frameCap) (hx : |x|≤frameCap) (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-x) 0+max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v (leftOwner ab))
    (hBT : GlobalOuterAnchor.width x≤projection true b t x 0)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+v+x+w+y+kappa*a.b+ZeroPrimary.unsigned e := by
  let i := tailChart e.branch.type
  let z := max (-x) 0+max (-w) 0+max (-y) 0
  let c := strengthenedWeight i z
  let eWeight : ℝ := (TailPolynomial.e i:ℝ)
  have hz : z∈Icc 0 frameCap := ⟨by dsimp [z]; positivity,hcap⟩
  have hcBounds := strengthened_bounds i hz
  have hc : 0≤c := by dsimp [c]; linarith [hcBounds.1]
  have hcu : c≤kappa := hcBounds.2.1
  have heBounds := tailChart_weight_bounds i
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := (retain_BT0 b t (lambda := kappa) hx (by norm_num [kappa]) le_rfl).trans
    (quarterDual_le_error b t 0 (lambda := kappa) (by norm_num [kappa]) hBT)
  have hTDdual := (retain_zero t d td hw hc hcu).trans
    (zeroDual_le_error t d td hc hTD)
  have hDEdual := (retain_DE d e jD hd he hjD hy heBounds.1.le heBounds.2 hordinary).trans
    (quarterDual_le_error d e jD heBounds.1.le hDE)
  have hstrict := reduced_de2_strict b t d e td ht hd he
    (le_max_right (-x) 0) (le_max_right (-w) 0) (le_max_right (-y) 0) hcap
  have hay := transverse_of_nonneg a ha
  rw [hay] at hABdual
  dsimp [reducedDE2Tail] at hstrict
  dsimp [retainedNegative] at hBTdual hTDdual hDEdual
  dsimp [c,z,i,eWeight] at hTDdual hDEdual
  linarith

theorem frame_tail_negative_budget {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) :
    max (-delta F.theta B) 0+max (-delta F.theta T) 0+
      max (-delta F.theta D) 0<frameCap := by
  have hv := (FramePhysicalTransport.candidate_variations F hq).2
  change negativeVariation F.theta<frameCap at hv
  simp only [negativeVariation,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hv
  have h0 := negativePart_nonneg (delta F.theta H)
  have h1 := negativePart_nonneg (delta F.theta G)
  have h2 := negativePart_nonneg (delta F.theta Candidate.A)
  have h6 := negativePart_nonneg (delta F.theta E)
  dsimp [negativePart,H,G,Candidate.A,B,T,D,E] at hv h0 h1 h2 h6 ⊢
  linarith

theorem ceiling_BT0_ordinary_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T))
    (jD : Fin 4) (hDE : (forwardAxis jD).Feasible (C.square D) (C.square E))
    (hordinary : jD=2 ∨ 0≤delta F.theta D ∨ C.kind E=.outer) : False := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hA := GlobalZeroLow.frame_BT_low_A_positive F hq 0 (Or.inl rfl) hBT
  have hT : 0<C.tangent T := by
    rcases GlobalQuarterSign.of_frame F hq B (by norm_num [word,B]) 0
      (by simpa [B,T,next] using hBT) with ⟨_,hh⟩ | ⟨hh,_⟩
    · simpa [B,T,next] using hh
    · rcases hh with hh | hh <;> norm_num at hh
  have hD := GlobalQuarterSign.frame_DE F hq hE
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose owner hf using hex
  have hABowner : owner Candidate.A=0 ∨ owner Candidate.A=2 := by
    rcases GlobalZeroSign.of_frame F hq Candidate.A (by norm_num [word,Candidate.A])
      (owner Candidate.A) (hf Candidate.A) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hTDowner : owner T=0 ∨ owner T=2 := by
    rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) (owner T) (hf T) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨ab,hab⟩ : ∃ab : Bool,leftOwner ab=owner Candidate.A := by
    rcases hABowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  obtain ⟨td,htd⟩ : ∃td : Bool,leftOwner td=owner T := by
    rcases hTDowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hABstate : (stateOf C Candidate.A).Feasible (stateOf C B) (leftOwner ab)
      (0+delta F.theta Candidate.A) := by
    simpa [Candidate.phi,word,Candidate.A,B,next,hab] using
      GlobalAllHigh.frame_state_feasible F Candidate.A (owner Candidate.A) (hf Candidate.A)
  have hBTstate : (stateOf C B).Feasible (stateOf C T) 0
      (Real.pi/2+delta F.theta B) := by
    simpa [Candidate.phi,word,B,T,next] using GlobalAllHigh.frame_state_feasible F B 0
      (by simpa [B,T,next] using hBT)
  have hTDstate : (stateOf C T).Feasible (stateOf C D) (leftOwner td)
      (0+delta F.theta T) := by
    simpa [Candidate.phi,word,T,D,next,htd] using
      GlobalAllHigh.frame_state_feasible F T (owner T) (hf T)
  have hDEstate : (stateOf C D).Feasible (stateOf C E) jD
      (Real.pi/2+delta F.theta D) := by
    simpa [Candidate.phi,word,D,E,next] using GlobalAllHigh.frame_state_feasible F D jD
      (by simpa [D,E,next] using hDE)
  have hey : transverse (stateOf C E)≤0 := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  have ho : jD=2 ∨ 0≤delta F.theta D ∨ (stateOf C E).branch.type≠0 := by
    rcases hordinary with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr (GlobalAllHigh.state_outer_of_kind C E hh))
  have hpath := ordinary_path (stateOf C Candidate.A) (stateOf C B) (stateOf C T)
    (stateOf C D) (stateOf C E) ab td jD
    (GlobalAllHigh.state_positive_of_tangent C Candidate.A hA).le
    (GlobalAllHigh.state_positive_of_tangent C T hT).le
    (GlobalAllHigh.state_negative_of_tangent C D hD.1).le hey
    (hdelta Candidate.A) (hdelta B) (hdelta T) (hdelta D)
    (frame_tail_negative_budget F hq).le (hD.2 jD hDE) ho
    ((projection_feasible false _ _ _ (hdelta Candidate.A)).1 hABstate)
    ((projection_feasible true _ _ _ (hdelta B)).1 hBTstate)
    ((projection_feasible false _ _ _ (hdelta T)).1 hTDstate)
    ((projection_feasible true _ _ _ (hdelta D)).1 hDEstate)
  have hreturn := frame_tail_cap F hE hA.le
  dsimp [tailCharge] at hreturn
  linarith

/-- The same original weak BT0 and DE witnesses are preserved by the
fixed-ray expansion; this excludes the source at every admissible q. -/
theorem frame_BT0_ordinary_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T))
    (jD : Fin 4) (hDE : (forwardAxis jD).Feasible (C.square D) (C.square E))
    (hordinary : jD=2 ∨ 0≤delta F.theta D ∨ C.kind E=.outer) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  have hBT' : (forwardAxis 0).Feasible (K.square B) (K.square T) := by
    simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 0)
      (by simpa [B,T,next] using hBT)
  have hDE' : (forwardAxis jD).Feasible (K.square D) (K.square E) := by
    simpa [D,E,next] using hR.preserves_all_axes D (forwardAxis jD)
      (by simpa [D,E,next] using hDE)
  apply ceiling_BT0_ordinary_false F' (by simpa only [hR.same_tangents] using hE) hBT' jD hDE'
  simpa only [F',FramePhysicalTransport.candidatePushforward,hR.same_kind] using hordinary

end SquaresInCircles.Eight.TableFree.GlobalBT
