module

public import SquaresInCircles.Eight.Boundary.SourceRecovery
public import SquaresInCircles.Eight.Boundary.UniversalSourceRecovery
public import SquaresInCircles.Eight.Owners.OriginalOwners
public import SquaresInCircles.Eight.Owners.Negative.TerminalSharp
public import SquaresInCircles.Eight.Owners.Positive.GAAllTExclusion

/-!
# Eight squares: the hard owners after the two pair moves, and the source

The exclusion of the binary words rules out the two diagonal cases on the cycle after the two
pair moves, at the same level (`G_negative_not_diagonal`, `T_positive_not_diagonal`), so the
terminal matrix gives hard owners on that cycle (`hard`). With pair moves that keep track of their
source, the contacts that they keep recover the hard axes on the input itself, which the moves
leave unchanged and which is sharp (`source_recovery`).
-/

section
/-!
## The terminal matrix of G and T

The terminal state of G (`GState`) is one of three: G–A separated along the axis zero; along the
axis one, with H–G along the axis two and a positive frame step `delta C.theta G`; or along the
axis one, with G on the frame of H, a negative step and `yG < 0`. The terminal state of T
(`TState`) is its reflection (`GState.reflected`). For a normalized boundary input at a level in
`[qLow, qStar]`, the cells with a positive step are impossible (`positive_G_false`,
`positive_T_false`): when T lies on the frame of D, the witness of T–D may be taken along the
axis zero on the same points (`aligned_TD0`, `td0Input`), and the reflection keeps the state of
E. The negative cells cost the anchor H or D a strict loss (`negative_g_impossible`,
`negative_t_impossible`, `both_negative_impossible`). So both hard axes are feasible (`hard`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PairTerminalMatrix
open Candidate SignedCycle Stationary PositiveGAOuterSoleReduction

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

/-- The terminal matrix of the three states of G and the three states of T, away from the
diagonals: GA0 and BT2 are feasible, also when the witness of the edge is the other owner. -/
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

end SquaresInCircles.Eight.PairTerminalMatrix
end
end
end

section
/-!
## The terminal matrix after the two pair moves

On the cycle after the two pair moves (`BoundaryInput.pairDescendant`), the terminal alternatives
of the two outputs give the terminal states of G and of T (`states`), except when a moved point
lies on a diagonal of the nearest axes, `yG = -aG` or `yT = aT`; these two cases stay as
hypotheses. Without them, the terminal matrix gives hard owners on the cycle after the moves
(`hard_of_no_diagonal`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.PairTerminalDescendant
open Candidate SignedCycle Stationary GeometricModel PairTerminalMatrix

theorem states {q : ℝ} (I : BoundaryInput q) (hcap : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGdiag : ((I.pairDescendant hcap OG OT).cycle.point G).y ≠
      -((I.pairDescendant hcap OG OT).cycle.point G).a)
    (hTdiag : ((I.pairDescendant hcap OG OT).cycle.point T).y ≠
      ((I.pairDescendant hcap OG OT).cycle.point T).a) :
    GState (I.pairDescendant hcap OG OT).cycle (I.pairDescendant hcap OG OT).witnesses ∧
    TState (I.pairDescendant hcap OG OT).cycle (I.pairDescendant hcap OG OT).witnesses := by
  let J := I.pairDescendant hcap OG OT
  obtain ⟨hH,hG,hA,hB,hT,hD,hE⟩ := I.pairDescendant_owners hcap OG OT
  have hGp : J.cycle.point G=OG.point := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,G,T]
  have hTp : J.cycle.point T=OT.point := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint]
  have hGt : J.cycle.theta G=OG.theta := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,G,T]
  have hHt : J.cycle.theta H=I.cycle.theta H := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,H,G,T]
  have hTt : J.cycle.theta T=OT.theta := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint]
  have hDt : J.cycle.theta D=I.cycle.theta D := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,D,G,T]
  have hdeltaG : delta J.cycle.theta G=I.cycle.theta A-OG.theta := by
    simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,delta,next,G,A,T]
  have hdeltaB : delta J.cycle.theta B=OT.theta-I.cycle.theta B := by
    simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,delta,next,B,G,T]
  change GState J.cycle J.witnesses ∧ TState J.cycle J.witnesses
  constructor
  · rcases OG.terminal with hg | ⟨hg,hh,hpos⟩ | ⟨hg,ha,hneg,hy⟩ | hdiag
    · exact Or.inl (hG.trans hg)
    · exact Or.inr (Or.inl ⟨hG.trans hg,hH.trans hh,by rwa [hdeltaG]⟩)
    · exact Or.inr (Or.inr ⟨hG.trans hg,by rw [hGt,hHt,ha],
        by rwa [hdeltaG],by rwa [hGp]⟩)
    · exact (hGdiag (by change (J.cycle.point G).y= -(J.cycle.point G).a; rwa [hGp])).elim
  · rcases OT.terminal with hb | ⟨hb,ht,hpos⟩ | ⟨hb,ha,hneg,hy⟩ | hdiag
    · exact Or.inl (hB.trans hb)
    · exact Or.inr (Or.inl ⟨hB.trans hb,hT.trans ht,by rwa [hdeltaB]⟩)
    · exact Or.inr (Or.inr ⟨hB.trans hb,by rw [hTt,hDt,ha],
        by rwa [hdeltaB],by rwa [hTp]⟩)
    · exact (hTdiag (by change (J.cycle.point T).y=(J.cycle.point T).a; rwa [hTp])).elim

theorem hard_of_no_diagonal {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar) (hcap : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGdiag : ((I.pairDescendant hcap OG OT).cycle.point G).y ≠
      -((I.pairDescendant hcap OG OT).cycle.point G).a)
    (hTdiag : ((I.pairDescendant hcap OG OT).cycle.point T).y ≠
      ((I.pairDescendant hcap OG OT).cycle.point T).a) :
    (I.pairDescendant hcap OG OT).cycle.HardOwners := by
  have hs := states I.toBoundaryInput hcap OG OT hGdiag hTdiag
  exact PairTerminalMatrix.hard (I.pairDescendant hcap OG OT) hQL hq hs.1 hs.2

end SquaresInCircles.Eight.PairTerminalDescendant
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.PairTerminalDescendant
open Set Candidate SignedCycle Stationary GeometricModel

theorem hard {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar) (hcap : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    (I.pairDescendant hcap OG OT).cycle.HardOwners := by
  have hmem : q∈Icc (5/2:ℝ) qCap :=
    ⟨le_trans (by norm_num [qLow]) hQL,hcap⟩
  let J := I.pairDescendant hcap OG OT
  exact hard_of_no_diagonal I hQL hq hcap OG OT
    (J.toBoundaryInput.G_negative_not_diagonal hmem)
    (J.toBoundaryInput.T_positive_not_diagonal hmem)

/-- A normalized boundary input at a level in `[qLow, qStar]`, with pair moves that keep track of
their source, has hard owners, is left unchanged by the moves, and is sharp; the diagonal cases
are excluded inside the proof. -/
theorem source_recovery {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hcap : q≤qCap) :
    I.cycle.HardOwners ∧ (I.pairDescendant hcap SG.output ST.output).cycle=I.cycle ∧
      I.cycle.theta A=I.cycle.theta B ∧ (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hh := hard I hQL hq hcap SG.output ST.output
  exact I.pair_source_recovery hQL hq SG ST hcap hh.1 hh.2

end SquaresInCircles.Eight.PairTerminalDescendant
end
end
end
