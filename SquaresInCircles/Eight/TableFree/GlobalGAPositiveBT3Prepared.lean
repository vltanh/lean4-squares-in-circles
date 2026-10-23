module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTSource

/-!
# All prepared A/E source sectors with sole nonnegative BT3

Uncompiled finite source join. Prepared E means either a nonnegative
selected signed total, one negative DE3 with EH0, or one negative EH1
with DE2 and its actual geometric cuts. These are exactly the outputs
of the original E normalization. The two negative-A alternatives retain
their actual flat coordinate, angle bound and neighboring separators.
No remaining scalar inequality is assumed as an input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Complete
open Candidate Secondary SignedCycle PairedE

/-- The nonnegative-total escape is retained explicitly, including
escapes caused by selecting an already actual secondary witness. -/
def ERegime (C : SignedCycle) (de eh : Bool) : Prop :=
  0≤cycleTotal C de eh ∨
    ((C.point E).a=7/12 ∧
      ((de=true ∧ eh=false ∧ delta C.theta D<0) ∨
       (de=false ∧ eh=true ∧ delta C.theta E<0 ∧
         -delta C.theta E≤1/4 ∧ -(C.point E).y∈Icc (0:ℝ) (39/250))))

theorem nonnegative_A_false {Q : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hn : C.Necessary Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤Source.aTotal C ga ab) (hz : 0≤delta C.theta B) (hreg : ERegime C de eh)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have hHG' : C.Feasible H 0∨C.Feasible H 2 := by
    rcases hhg with rfl|rfl
    · exact Or.inl hHG
    · exact Or.inr hHG
  rcases hreg with he|⟨hflat,hnegative⟩
  · exact Source.actual_false ga ab de eh hn.sorted hn.contained hQ hHy hGy hBy hDy
      hvar ha hz he hHG' hGA hAB hBT hTD hDE hEH
  · rcases hnegative with ⟨rfl,rfl,hs⟩|⟨rfl,rfl,hs,hcap,hb⟩
    · obtain ⟨hgb,hgval⟩ : ∃hgb : Bool,hg=(if hgb then 2 else 0) := by
        rcases hhg with hh|hh
        · exact ⟨false,hh⟩
        · exact ⟨true,hh⟩
      apply NegativeDEPositiveBT.Source.original_flat_false hgb ga ab hn.sorted hn.contained
        hQ hHy hGy hBy hDy hvar ha hz hs.le hflat
      intro i
      fin_cases i
      · simpa [NegativeDEPositiveBT.Source.owners,H,hgval] using hHG
      · simpa [NegativeDEPositiveBT.Source.owners,G] using hGA
      · simpa [NegativeDEPositiveBT.Source.owners,A] using hAB
      · simpa [NegativeDEPositiveBT.Source.owners,B] using hBT
      · simpa [NegativeDEPositiveBT.Source.owners,T] using hTD
      · simpa [NegativeDEPositiveBT.Source.owners,D] using hDE
      · simpa [NegativeDEPositiveBT.Source.owners,E] using hEH
    · apply NegativeEHBT3.Source.original_flat_false ga ab hn.sorted hn.contained
        hQ hHy hGy hBy hDy hvar ha hz hs.le hflat hb hcap hhg
      intro i
      fin_cases i
      · simpa [NegativeEHBT3.Source.owners,Source.owners,H] using hHG
      · simpa [NegativeEHBT3.Source.owners,Source.owners,G] using hGA
      · simpa [NegativeEHBT3.Source.owners,Source.owners,A] using hAB
      · simpa [NegativeEHBT3.Source.owners,Source.owners,B] using hBT
      · simpa [NegativeEHBT3.Source.owners,Source.owners,T] using hTD
      · simpa [NegativeEHBT3.Source.owners,Source.owners,D] using hDE
      · simpa [NegativeEHBT3.Source.owners,Source.owners,E] using hEH

/-- A genuine negative A terminal, for every prepared E alternative.
The radius and all arguments are those of this necessary system. -/
theorem negative_A_false {Q r : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hn : C.Necessary Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc 0 (NegativeABT3.Explicit.angleCut atG))
    (ha : NegativeABT3.Source.aError C atG= -r)
    (hAflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤if atG then 39/250 else 1/2)
    (hz : 0≤delta C.theta B) (hreg : ERegime C de eh)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  rcases hreg with he|⟨hEflat,hnegative⟩
  · exact NegativeABT3.original atG de eh hn.sorted hn.contained hQ hHy hGy hBy hDy hvar
      hr ha hAflat hAy hcut he hz hhg hHG hGA hAB hBT hTD hDE hEH
  · have hr' : r∈Icc (0:ℝ) (19/50) := by
      cases atG <;> norm_num [NegativeABT3.Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut] at hr ⊢ <;>
        exact ⟨hr.1,by linarith [hr.2]⟩
    have ha' : JointNegativeAEBT3.Source.aError C atG= -r := ha
    have hnvar : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    rcases hnegative with ⟨rfl,rfl,hs⟩|⟨rfl,rfl,hs,hcap,hb⟩
    · have hd : -delta C.theta D∈Icc 0 frameCap :=
        ⟨(neg_pos.mpr hs).le,(neg_le_abs _).trans (original_error_bound hvar hnvar D)⟩
      exact JointNegativeAEBT3.original atG false hn.sorted hn.contained hQ hHy hGy hBy hDy
        hvar hr' hd (by intro h; cases h) ha' (by simp [JointNegativeAEBT3.Source.eError,
          JointNegativeAETD2.Source.eError]) hAflat hEflat hz hhg hHG hGA hAB hBT hTD hDE hEH
    · have hd : -delta C.theta E∈Icc 0 frameCap :=
        ⟨(neg_pos.mpr hs).le,(neg_le_abs _).trans (original_error_bound hvar hnvar E)⟩
      exact JointNegativeAEBT3.original atG true hn.sorted hn.contained hQ hHy hGy hBy hDy
        hvar hr' hd (fun _ => hcap) ha' (by simp [JointNegativeAEBT3.Source.eError,
          JointNegativeAETD2.Source.eError]) hAflat hEflat hz hhg hHG hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Complete
