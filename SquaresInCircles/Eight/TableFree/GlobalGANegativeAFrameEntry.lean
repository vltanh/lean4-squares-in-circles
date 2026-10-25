module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAEntry

/-!
# Negative-A entry at the original boundary frame

Uncompiled source. The nonpositive GA target uses its already established
original outer radial kind. In the single AB-primary row the retained GA2
axis itself gives the required target cut, before the flat-core alternative
is applied. No global GA owner conclusion is used in either adapter.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA
open Candidate Secondary

theorem contained_center_norm {q : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap) :
    P.a^2+P.y^2<(283/200:ℝ)^2 := by
  let r := Real.sqrt (P.a^2+P.y^2)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=P.a^2+P.y^2 := Real.sq_sqrt (by positivity)
  have hsum : r≤P.a+|P.y| := by
    by_contra! hh
    nlinarith [hs.1,abs_nonneg P.y,mul_nonneg hs.1.le (abs_nonneg P.y),sq_abs P.y]
  have hcircle : (P.a+1/2)^2+(|P.y|+1/2)^2≤qCap := hc.trans hq
  have hu : r<(283/200:ℝ) := by
    by_contra! hh
    norm_num [qCap] at hcircle
    nlinarith [sq_abs P.y]
  nlinarith

theorem secondary_GA_target_cut {q d : ℝ} {G A : SignedPoint}
    (hs : G.Sorted) (hc : G.Contained q) (hq : q≤qCap)
    (hGA : quarterFeasible G A d 2) : A.y<1/2 := by
  have hn := contained_center_norm hs hc hq
  have hp := FrameCoreArc.projection_lt (a:=-G.y) (b:=G.a)
    (by norm_num : (0:ℝ)<283/200) (by nlinarith) d
  have hw := edgeWidth_ge_one d
  have hGA' : edgeWidth d≤G.a*Real.cos d-G.y*Real.sin d-A.y := hGA
  linarith

theorem frame_GA_entry {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (hGA : (forwardAxis 3).Feasible (C.square G) (C.square A))
    (hnegative : delta F.theta G<0) :
    (forwardAxis 2).Feasible (C.square G) (C.square A) ∨
      (((SignedCycle.atFrame F).point A).a=7/12 ∧
        0<((SignedCycle.atFrame F).point A).y ∧
        ((SignedCycle.atFrame F).point A).y<39/250 ∧ -(1/4:ℝ)<delta F.theta G) := by
  let S := SignedCycle.atFrame F
  let s := -delta F.theta G
  have hn := SignedCycle.atFrame_necessary F
  have hv := FramePhysicalTransport.candidate_variations F hq
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (original_error_bound hv.1.le hv.2.le G)⟩
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    3 (Or.inr rfl) (by simpa [G,A,next] using hGA)
  have hGy : (S.point G).y≤0 := ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
  have hAouter : (S.point A).y≤0 → (S.point A).Outer q := by
    intro hh
    have hsign := (SignedCycle.atFrame_y_nonpos_iff F A).1 hh
    exact SignedCycle.atFrame_outer_of_kind F A
      (GlobalZeroSourceOuter.frame_nonpositive_source_outer F hq A
        (by norm_num [word,A]) hsign)
  have hprimary : quarterFeasible (S.point G) (S.point A) (-s) 3 := by
    have hh := (SignedCycle.atFrame_feasible F G 3).2 (by simpa [G,A,next] using hGA)
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      S,s,SignedCycle.atFrame,word,G,A,next,quarterFeasible,sub_nonneg] using hh
  rcases GA_entry (hn.sorted G) (hn.contained G) (hn.sorted A)
    (SignedCycle.atFrame_boundary F A) hq.2 hGy hAouter hs hprimary with hsecondary | hflat
  · left
    apply (SignedCycle.atFrame_feasible F G 2).1
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      S,s,SignedCycle.atFrame,word,G,A,next,quarterFeasible,sub_nonneg] using hsecondary
  · right
    exact ⟨hflat.1,hflat.2.1,hflat.2.2.1,by dsimp [s] at hflat; linarith [hflat.2.2.2]⟩

theorem frame_AB_entry {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hGA : (forwardAxis 2).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis 2).Feasible (C.square A) (C.square B))
    (hnegative : delta F.theta A<0) :
    (forwardAxis 0).Feasible (C.square A) (C.square B) ∨
      (((SignedCycle.atFrame F).point A).a=7/12 ∧
        0<((SignedCycle.atFrame F).point A).y ∧
        ((SignedCycle.atFrame F).point A).y<1/2 ∧ -(19/50:ℝ)<delta F.theta A) := by
  let S := SignedCycle.atFrame F
  let s := -delta F.theta A
  have hn := SignedCycle.atFrame_necessary F
  have hv := FramePhysicalTransport.candidate_variations F hq
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (original_error_bound hv.1.le hv.2.le A)⟩
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hGA' : quarterFeasible (S.point G) (S.point A) (delta F.theta G) 2 := by
    have hh := (SignedCycle.atFrame_feasible F G 2).2 (by simpa [G,A,next] using hGA)
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      S,SignedCycle.atFrame,word,G,A,next,quarterFeasible,sub_nonneg] using hh
  have hcut := secondary_GA_target_cut (hn.sorted G) (hn.contained G) hq.2 hGA'
  have hprimary : zeroFeasible (S.point A) (S.point B) (-s) 2 := by
    have hh := (SignedCycle.atFrame_feasible F A 2).2 (by simpa [A,B,next] using hAB)
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      S,s,SignedCycle.atFrame,word,A,B,next,zeroFeasible,sub_nonneg] using hh
  rcases AB_entry (hn.sorted A) (SignedCycle.atFrame_boundary F A) (hn.sorted B)
    hanchors.2.2.1 hq.2 hcut hanchors.2.2.2.1.le hs hprimary with hsecondary | hflat
  · left
    apply (SignedCycle.atFrame_feasible F A 0).1
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      S,s,SignedCycle.atFrame,word,A,B,next,zeroFeasible,sub_nonneg] using hsecondary
  · right
    exact ⟨hflat.1,hflat.2.1,hflat.2.2.1,by dsimp [s] at hflat; linarith [hflat.2.2.2]⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA
