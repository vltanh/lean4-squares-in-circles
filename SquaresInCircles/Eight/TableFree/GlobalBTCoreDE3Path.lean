module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Monotone
public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Support
public import SquaresInCircles.Eight.TableFree.GlobalBTDE2Path

/-!
# The complete core-E negative-DE3 path on original states

The actual weak AB, BT0, TD and DE3 inequalities pay their explicit
positive weights.  Only the positive prefix errors are removed inside
the dual; the original negative DE3 error and core marker are retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open Candidate FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem path (a b t d e : State) (ab td : Bool) {v x w u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0) (hcore : e.branch.type=0)
    (hv : |v|≤frameCap) (hx : |x|≤frameCap) (hw : |w|≤frameCap)
    (hu : u∈Icc 0 frameCap)
    (hcap : max (-x) 0+max (-w) 0+u≤frameCap)
    (hAB : width v≤projection false a b v (leftOwner ab))
    (hBT : width x≤projection true b t x 0)
    (hTD : width w≤projection false t d w (leftOwner td))
    (hDE : width (-u)≤projection true d e (-u) 3) :
    pathThreshold<Real.pi+v+x+w-u+kappa*a.b+ZeroPrimary.unsigned e := by
  let p := max (-x) 0+max (-w) 0
  have hp : p∈Icc 0 frameCap :=
    ⟨by dsimp [p]; positivity,by dsimp [p]; linarith [hu.1]⟩
  have hc := weight_pos hp
  have hcu := (weight_bounds hp).2.2
  have heWeight : 0≤endpointWeight u :=
    (show 0≤kappa by norm_num [kappa]).trans (endpointWeight_bounds hu).1
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := (retain_BT0 b t (lambda := kappa) hx (by norm_num [kappa]) le_rfl).trans
    (quarterDual_le_error b t 0 (lambda := kappa) (by norm_num [kappa]) hBT)
  have hTDdual := (retain_zero t d td hw hc.le hcu).trans
    (zeroDual_le_error t d td hc.le hTD)
  have hDEdual := quarterDual_le_error d e 3 heWeight hDE
  have hscalar := tail_strict td (le_max_right (-x) 0) (le_max_right (-w) 0) hu.1 hcap
  have hsupport := support b t d e td (c := weight p) ht hd he hcore
    (negative_part_range hx) (negative_part_range hw) hu
  have hstrict := hscalar.trans_le hsupport
  have hay := transverse_of_nonneg a ha
  rw [hay] at hABdual
  dsimp [reduced] at hstrict
  dsimp [retainedNegative,p] at hBTdual hTDdual hstrict
  linarith

theorem ceiling_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T))
    (hDE : (forwardAxis 3).Feasible (C.square D) (C.square E))
    (hcore : C.kind E≠.outer) (hnegative : delta F.theta D≤0) : False := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hA := GlobalZeroLow.frame_BT_low_A_positive F hq 0 (Or.inl rfl) hBT
  have hT : 0<C.tangent T := by
    rcases GlobalQuarterSign.of_frame F hq B (by norm_num [word,B]) 0
      (by simpa [B,T,next] using hBT) with ⟨_,hh⟩ | ⟨hh,_⟩
    · simpa [B,T,next] using hh
    · rcases hh with hh | hh <;> norm_num at hh
  have hD := (GlobalQuarterSign.frame_DE F hq hE).1
  let owner : Vertex→Fin 4 := fun i =>
    Classical.choose (F.forward_complete i (C.selected i) (C.feasible i))
  have hf (i : Vertex) :
      (forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)) := by
    have hh := Classical.choose_spec (F.forward_complete i (C.selected i) (C.feasible i))
    simpa only [hh] using C.feasible i
  have hABowner : owner A=0 ∨ owner A=2 := by
    rcases GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) (owner A) (hf A) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hTDowner : owner T=0 ∨ owner T=2 := by
    rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) (owner T) (hf T) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨ab,hab⟩ : ∃ab : Bool,leftOwner ab=owner A := by
    rcases hABowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  obtain ⟨td,htd⟩ : ∃td : Bool,leftOwner td=owner T := by
    rcases hTDowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hABstate : (stateOf C A).Feasible (stateOf C B) (leftOwner ab)
      (0+delta F.theta A) := by
    simpa [phi,word,A,B,next,hab] using GlobalAllHigh.frame_state_feasible F A (owner A) (hf A)
  have hBTstate : (stateOf C B).Feasible (stateOf C T) 0
      (Real.pi/2+delta F.theta B) := by
    simpa [phi,word,B,T,next] using GlobalAllHigh.frame_state_feasible F B 0
      (by simpa [B,T,next] using hBT)
  have hTDstate : (stateOf C T).Feasible (stateOf C D) (leftOwner td)
      (0+delta F.theta T) := by
    simpa [phi,word,T,D,next,htd] using GlobalAllHigh.frame_state_feasible F T (owner T) (hf T)
  have hDEstate : (stateOf C D).Feasible (stateOf C E) 3
      (Real.pi/2+delta F.theta D) := by
    simpa [phi,word,D,E,next] using GlobalAllHigh.frame_state_feasible F D 3
      (by simpa [D,E,next] using hDE)
  have hey : transverse (stateOf C E)≤0 := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  have hcoreState : (stateOf C E).branch.type=0 := (branchOf_core_iff C E).2 hcore
  have hu : -delta F.theta D∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta D)).trans (hdelta D)⟩
  have hcap : max (-delta F.theta B) 0+max (-delta F.theta T) 0+
      (-delta F.theta D)≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    rw [max_eq_left (show 0≤-delta F.theta D by linarith)] at hh
    exact hh
  have hpath := path (stateOf C A) (stateOf C B) (stateOf C T) (stateOf C D) (stateOf C E)
    ab td (GlobalAllHigh.state_positive_of_tangent C A hA).le
    (GlobalAllHigh.state_positive_of_tangent C T hT).le
    (GlobalAllHigh.state_negative_of_tangent C D hD).le hey hcoreState
    (hdelta A) (hdelta B) (hdelta T) hu hcap
    ((projection_feasible false _ _ _ (hdelta A)).1 hABstate)
    ((projection_feasible true _ _ _ (hdelta B)).1 hBTstate)
    ((projection_feasible false _ _ _ (hdelta T)).1 hTDstate)
    (by simpa only [neg_neg] using (projection_feasible true _ _ _ (hdelta D)).1 hDEstate)
  have hreturn := frame_tail_cap F hE hA.le
  dsimp [tailCharge] at hreturn
  linarith

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
