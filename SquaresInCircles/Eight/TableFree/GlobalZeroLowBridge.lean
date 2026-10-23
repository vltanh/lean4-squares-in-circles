module

public import SquaresInCircles.Eight.TableFree.GlobalZeroLowCycle

/-!
# Original-frame sign consequences for the global owner rows

These adapters retain the requested weak axis individually.  In
particular the four signs on the putative high-EH/low-GA path follow
without a restriction on any of the other quarter owners.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalZeroLow

open Candidate

theorem frame_zero_low_source_positive {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    0<C.tangent i := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact zero_low_source_positive C hq G i hinc hinc' j howner haxis

theorem frame_high_zero_target_negative {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=1) (hj : word (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.tangent (next (next i))<0 := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact high_zero_target_negative C hq G i hinc hinc' j howner haxis

theorem frame_GA_low_H_positive {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (j : Fin 4) (hj : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square G) (C.square A)) : 0<C.tangent H := by
  simpa [H,G,A,next] using frame_zero_low_source_positive F hq H
    (by norm_num [word,H]) (by norm_num [word,H,next]) j hj
    (by simpa [H,G,A,next] using haxis)

theorem frame_BT_low_A_positive {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (j : Fin 4) (hj : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square B) (C.square T)) : 0<C.tangent A := by
  simpa [A,B,T,next] using frame_zero_low_source_positive F hq A
    (by norm_num [word,A]) (by norm_num [word,A,next]) j hj
    (by simpa [A,B,T,next] using haxis)

theorem frame_GA_high_B_negative {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square G) (C.square A)) : C.tangent B<0 := by
  simpa [G,A,B,next] using frame_high_zero_target_negative F hq G
    (by norm_num [word,G]) (by norm_num [word,G,next]) j hj
    (by simpa [G,A,next] using haxis)

theorem frame_BT_high_D_negative {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square B) (C.square T)) : C.tangent D<0 := by
  simpa [B,T,D,next] using frame_high_zero_target_negative F hq B
    (by norm_num [word,B]) (by norm_num [word,B,next]) j hj
    (by simpa [B,T,next] using haxis)

theorem frame_EH_high_G_negative {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square E) (C.square H)) : C.tangent G<0 := by
  simpa [E,H,G,next] using frame_high_zero_target_negative F hq E
    (by norm_num [word,E]) (by norm_num [word,E,next]) j hj
    (by simpa [E,H,next] using haxis)

theorem frame_high_EH_low_GA_signs {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0)
    (jE jG : Fin 4) (hE : jE=2 ∨ jE=3) (hG : jG=0 ∨ jG=1)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A)) :
    C.tangent E<0 ∧ 0<C.tangent H ∧ C.tangent G<0 ∧ 0<C.tangent A := by
  have hEsign : C.tangent E<0 := by
    rcases GlobalQuarterSign.of_frame F hq E (by norm_num [word,E]) jE
      (by simpa [E,H,next] using hEH) with ⟨hj,_⟩ | ⟨_,hy⟩
    · rcases hE with rfl | rfl <;> rcases hj with hj | hj <;> norm_num at hj
    · exact hy
  have hAsign : 0<C.tangent A := by
    rcases GlobalQuarterSign.of_frame F hq G (by norm_num [word,G]) jG
      (by simpa [G,A,next] using hGA) with ⟨_,hy⟩ | ⟨hj,_⟩
    · simpa [G,A,next] using hy
    · rcases hG with rfl | rfl <;> rcases hj with hj | hj <;> norm_num at hj
  exact ⟨hEsign,frame_GA_low_H_positive F hq jG hG hGA,
    frame_EH_high_G_negative F hq jE hE hEH,hAsign⟩

end SquaresInCircles.Eight.TableFree.GlobalZeroLow
