module

public import SquaresInCircles.Eight.TableFree.PositiveGAAllTExclusion
public import SquaresInCircles.Eight.TableFree.UniversalNegativeTerminal
public import SquaresInCircles.Eight.TableFree.SourceAwareBoundaryPreprocessing

/-!
# The actual non-diagonal G/T terminal matrix

Uncompiled source. The two three-way terminal descriptions refer to the
current actual points, frames, and weak owners. A negative aligned TD
tie may be reselected on those same points for the positive-G stress.
Reflection retains the actual E state. The remaining negative cells
pay on the original rigid H or D anchor.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PairTerminalMatrix
open Candidate SignedCycle ExactFamily PositiveGAOuterSoleReduction

def GState (C : SignedCycle) (w : C.Witnesses) : Prop :=
  w.owner G=0 ∨
    (w.owner G=1 ∧ w.owner H=2 ∧ 0<delta C.theta G) ∨
    (w.owner G=1 ∧ C.theta G=C.theta H ∧ delta C.theta G<0 ∧ (C.point G).y<0)

def TState (C : SignedCycle) (w : C.Witnesses) : Prop :=
  w.owner B=2 ∨
    (w.owner B=3 ∧ w.owner T=0 ∧ 0<delta C.theta B) ∨
    (w.owner B=3 ∧ C.theta T=C.theta D ∧ delta C.theta B<0 ∧ 0<(C.point T).y)

def td0Witnesses {q : ℝ} (I : BoundaryInput q) (hf : I.cycle.Feasible T 0) : I.cycle.Witnesses where
  owner := Function.update I.witnesses.owner T 0
  feasible i := by
    by_cases hi : i=T
    · subst i; simpa using hf
    · simpa [hi] using I.witnesses.feasible i
  allowed i := by
    by_cases hi : i=T
    · subst i; simp [normalOwners,T]
    · simpa [hi] using I.witnesses.allowed i

def td0Input {q : ℝ} (I : BoundaryInput q) (hf : I.cycle.Feasible T 0)
    (hy : 0<(I.cycle.point T).y) : BoundaryInput q :=
  { I with
    witnesses := td0Witnesses I hf
    zero_signs := {
      HG_canceling := by
        intro hh
        exact I.zero_signs.HG_canceling (by simpa [td0Witnesses,H,T] using hh)
      TD_canceling := fun _ => hy } }

theorem aligned_TD0 {q : ℝ} (I : BoundaryInput q)
    (ha : I.cycle.theta T=I.cycle.theta D) : I.cycle.Feasible T 0 := by
  have hdelta : delta I.cycle.theta T=0 := by
    simp only [delta,show next T=D by decide,ha,sub_self]
  have hf := (NegativeSecondaryEExclusion.TD_contact I.cycle (I.witnesses.owner T)).1
    (I.witnesses.feasible T)
  rw [hdelta] at hf
  have ho : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  have hz : zeroFeasible (I.cycle.point T) (I.cycle.point D) 0 0 := by
    rcases ho with ho | ho
    · simpa [ho] using hf
    · exact (zero_owner_tie _ _).2 (by simpa [ho] using hf)
  apply (NegativeSecondaryEExclusion.TD_contact I.cycle 0).2
  simpa [hdelta] using hz

theorem positive_G_false {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar) (hH : I.witnesses.owner H=2)
    (hG : I.witnesses.owner G=1) (hx : 0<delta I.cycle.theta G)
    (ht : TState I.cycle I.witnesses) : False := by
  have hsharp : q ≤ sharpData.q := hq
  rcases ht with hB | ⟨hB,hT,hpos⟩ | ⟨hB,ha,hneg,hy⟩
  · have hT : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
      simpa [normalOwners,T] using I.witnesses.allowed T
    have hregime : TRegime I := by
      rcases hT with hT | hT
      · exact Or.inl ⟨hB,hT⟩
      · exact Or.inr (Or.inl ⟨hB,hT⟩)
    exact PositiveGAAllTExclusion.original_boundary_false sharpData_stationary I hQL hsharp hH hG hx hregime
  · have hregime : TRegime I := Or.inr (Or.inr ⟨hB,hT,by intro h; linarith⟩)
    exact PositiveGAAllTExclusion.original_boundary_false sharpData_stationary I hQL hsharp hH hG hx hregime
  · let J := td0Input I (aligned_TD0 I ha) hy
    have hH' : J.witnesses.owner H=2 := by simpa [J,td0Input,td0Witnesses,H,T] using hH
    have hG' : J.witnesses.owner G=1 := by simpa [J,td0Input,td0Witnesses,G,T] using hG
    have hB' : J.witnesses.owner B=3 := by simpa [J,td0Input,td0Witnesses,B,T] using hB
    have hT' : J.witnesses.owner T=0 := by simp [J,td0Input,td0Witnesses]
    have halign : delta J.cycle.theta T=0 := by
      change delta I.cycle.theta T=0
      simp only [delta,show next T=D by decide,ha,sub_self]
    exact PositiveGAAllTExclusion.original_boundary_false sharpData_stationary J hQL hsharp
      hH' hG' hx (Or.inr (Or.inr ⟨hB',hT',fun _ => halign⟩))

theorem GState.reflected {q : ℝ} {I : BoundaryInput q}
    (h : GState I.cycle I.witnesses) : TState I.reflected.cycle I.reflected.witnesses := by
  rcases h with hG | ⟨hG,hH,hpos⟩ | ⟨hG,ha,hneg,hy⟩
  · left
    simp [BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,reflectedOwner,B,show I.witnesses.owner 1=_ from hG]
  · right; left
    refine ⟨?_,?_,?_⟩
    · simp [BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,reflectedOwner,B,show I.witnesses.owner 1=_ from hG]
    · simp [BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,reflectedOwner,T,show I.witnesses.owner 0=_ from hH]
    · simpa [BoundaryInput.reflected,reflected_delta,reflectedIndex,next,B,G] using hpos
  · right; right
    refine ⟨?_,?_,?_,?_⟩
    · simp [BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,reflectedOwner,B,show I.witnesses.owner 1=_ from hG]
    · change I.cycle.reflected.theta T=I.cycle.reflected.theta D
      simpa [SignedCycle.reflected,reflectedIndex,T,D,G,H] using congrArg (fun a => I.cycle.theta B-a) ha
    · simpa [BoundaryInput.reflected,reflected_delta,reflectedIndex,next,B,G] using hneg
    · simpa [BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,T,G,SignedPoint.reflect]
        using neg_pos.mpr hy

theorem positive_T_false {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar) (hB : I.witnesses.owner B=3)
    (hT : I.witnesses.owner T=0) (hz : 0<delta I.cycle.theta B)
    (hg : GState I.cycle I.witnesses) : False := by
  have hH' : I.reflected.witnesses.owner H=2 := by
    simp [BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,reflectedOwner,H,show I.witnesses.owner 4=_ from hT]
  have hG' : I.reflected.witnesses.owner G=1 := by
    simp [BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,reflectedOwner,G,show I.witnesses.owner 3=_ from hB]
  have hx' : 0<delta I.reflected.cycle.theta G := by
    simpa [BoundaryInput.reflected,reflected_delta,reflectedIndex,next,G,B] using hz
  exact positive_G_false I.reflected hQL hq hH' hG' hx' hg.reflected

/-- The complete 3 by 3 non-diagonal terminal matrix. A hard axis may
be feasible even if the source retained the other weak owner. -/
theorem hard {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar)
    (hg : GState I.cycle I.witnesses) (ht : TState I.cycle I.witnesses) : I.cycle.HardOwners := by
  have hGn : ¬(I.witnesses.owner G=1 ∧ I.witnesses.owner H=2 ∧ 0<delta I.cycle.theta G) := by
    rintro ⟨hG,hH,hx⟩
    exact positive_G_false I.toBoundaryInput hQL hq hH hG hx ht
  have hTn : ¬(I.witnesses.owner B=3 ∧ I.witnesses.owner T=0 ∧ 0<delta I.cycle.theta B) := by
    rintro ⟨hB,hT,hz⟩
    exact positive_T_false I.toBoundaryInput hQL hq hB hT hz hg
  have hGcase : I.cycle.Feasible G 0 ∨
      (I.cycle.Feasible G 1 ∧ I.cycle.theta G=I.cycle.theta H ∧
        I.cycle.theta A<I.cycle.theta H ∧ (I.cycle.point G).y≤0) := by
    rcases hg with h | h | ⟨h,ha,hn,hy⟩
    · exact Or.inl (by simpa [h] using I.witnesses.feasible G)
    · exact (hGn h).elim
    · right
      refine ⟨by simpa [h] using I.witnesses.feasible G,ha,?_,hy.le⟩
      have hh : delta I.cycle.theta G=I.cycle.theta A-I.cycle.theta G := by simp [delta,next,G,A]
      rw [hh,ha] at hn
      linarith
  have hTcase : I.cycle.Feasible B 2 ∨
      (I.cycle.Feasible B 3 ∧ I.cycle.theta T=I.cycle.theta D ∧
        I.cycle.theta D<I.cycle.theta B ∧ 0≤(I.cycle.point T).y) := by
    rcases ht with h | h | ⟨h,ha,hn,hy⟩
    · exact Or.inl (by simpa [h] using I.witnesses.feasible B)
    · exact (hTn h).elim
    · right
      refine ⟨by simpa [h] using I.witnesses.feasible B,ha,?_,hy.le⟩
      have hh : delta I.cycle.theta B=I.cycle.theta T-I.cycle.theta B := by simp [delta,next,B,T]
      rw [hh,ha] at hn
      linarith
  by_cases hGA : I.cycle.Feasible G 0
  · refine ⟨hGA,?_⟩
    by_contra hBT
    rcases hTcase with hh | ⟨hB,ha,hn,hy⟩
    · exact hBT hh
    · exact DirectNegativeT.negative_t_impossible I hQL hq ha hn hy hB hBT hGA
  · rcases hGcase with hh | ⟨hG,haG,hnG,hyG⟩
    · exact (hGA hh).elim
    · by_cases hBT : I.cycle.Feasible B 2
      · exact (AlignedNegative.negative_g_impossible I hQL hq haG hnG hyG hG hGA hBT).elim
      · rcases hTcase with hh | ⟨hB,haT,hnT,hyT⟩
        · exact (hBT hh).elim
        · exact (AlignedNegative.both_negative_impossible I hQL hq haG hnG hG hGA haT hnT hB hBT).elim

end SquaresInCircles.Eight.TableFree.PairTerminalMatrix
