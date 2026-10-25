module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Source
public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTSource

/-!
# The finite prepared A/E regimes for positive BT3

Uncompiled source dispatch. Every selected E total is either nonnegative,
or one negative flat DE3, or one genuine negative flat EH1 with the
original short-angle and tangent cuts. The latter cuts are established
before A is moved. Both negative-A normal forms are handled at their
actual endpoints, with no assumption on the unrelated TD0 error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveT.Source
open Candidate Secondary SignedCycle PairedE

def ERegime (C : SignedCycle) (de eh : Bool) : Prop :=
  0≤cycleTotal C de eh ∨
    ((C.point E).a=7/12 ∧
      ((de=true ∧ eh=false ∧ delta C.theta D≤0) ∨
       (de=false ∧ eh=true ∧ -delta C.theta E∈Icc (0:ℝ) (1/4) ∧
         -(C.point E).y∈Icc (0:ℝ) (39/250))))

theorem nonnegative_A_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤PositiveBT3.Source.aTotal C ga ab) (hz : 0≤delta C.theta B)
    (hreg : ERegime C de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  rcases hreg with he|⟨hflat,hnegative⟩
  · exact PositiveBT3.Source.actual_false ga ab de eh hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha hz he hHG hGA hAB hBT hTD hDE hEH
  · obtain ⟨hg,hhg⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
      rcases hHG with hh|hh
      · exact ⟨false,hh⟩
      · exact ⟨true,hh⟩
    rcases hnegative with ⟨rfl,rfl,hd⟩|⟨rfl,rfl,he,hEy⟩
    · apply NegativeDEPositiveBT.Source.original_flat_false hg ga ab hsorted hcontained hQ
        hHy hGy hBy hDy hvar ha hz hd hflat
      intro i
      fin_cases i
      · simpa [NegativeDEPositiveBT.Source.owners,H] using hhg
      · simpa [NegativeDEPositiveBT.Source.owners,G] using hGA
      · simpa [NegativeDEPositiveBT.Source.owners,A] using hAB
      · simpa [NegativeDEPositiveBT.Source.owners,B] using hBT
      · simpa [NegativeDEPositiveBT.Source.owners,T] using hTD
      · simpa [NegativeDEPositiveBT.Source.owners,D] using hDE
      · simpa [NegativeDEPositiveBT.Source.owners,E] using hEH
    · apply NegativeEHBT3.Source.original_flat_false (if hg then 2 else 0) ga ab hsorted hcontained hQ
        hHy hGy hBy hDy hvar ha hz (by linarith [he.1]) hflat hEy he.2
        (by cases hg <;> simp)
      intro i
      fin_cases i
      · simpa [NegativeEHBT3.Source.owners,PositiveBT3.Source.owners,H] using hhg
      · simpa [NegativeEHBT3.Source.owners,PositiveBT3.Source.owners,G] using hGA
      · simpa [NegativeEHBT3.Source.owners,PositiveBT3.Source.owners,A] using hAB
      · simpa [NegativeEHBT3.Source.owners,PositiveBT3.Source.owners,B] using hBT
      · simpa [NegativeEHBT3.Source.owners,PositiveBT3.Source.owners,T] using hTD
      · simpa [NegativeEHBT3.Source.owners,PositiveBT3.Source.owners,D] using hDE
      · simpa [NegativeEHBT3.Source.owners,PositiveBT3.Source.owners,E] using hEH

theorem negative_A_false {Q r : ℝ} {C : SignedCycle} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc 0 (NegativeABT3.Explicit.angleCut atG))
    (ha : NegativeABT3.Source.aError C atG= -r)
    (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤ if atG then 39/250 else 1/2)
    (hz : 0≤delta C.theta B) (hreg : ERegime C de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  rcases hreg with he|⟨hEflat,hnegative⟩
  · exact NegativeABT3.original atG de eh hsorted hcontained hQ hHy hGy hBy hDy
      hvar hr ha hflat hAy hcut he hz hhg hHG hGA hAB hBT hTD hDE hEH
  · have hr' : r∈Icc (0:ℝ) (19/50) := by
      cases atG <;> simp only [NegativeABT3.Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,
        Bool.false_eq_true,↓reduceIte] at hr <;>
        exact ⟨hr.1,by linarith [hr.2]⟩
    have ha' : JointNegativeAEBT3.Source.aError C atG= -r := by
      rw [←ha]
      cases atG <;> rfl
    have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    rcases hnegative with ⟨rfl,rfl,hd⟩|⟨rfl,rfl,he,hEy⟩
    · have hs : -delta C.theta D∈Icc 0 frameCap :=
        ⟨neg_nonneg.mpr hd,(neg_le_abs _).trans (original_error_bound hvar hn D)⟩
      exact JointNegativeAEBT3.original atG false hsorted hcontained hQ hHy hGy hBy hDy
        hvar hr' hs (by intro h; cases h) ha'
        (by simp [JointNegativeAEBT3.Source.eError,JointNegativeAETD2.Source.eError]) hflat hEflat hz hhg hHG
        hGA hAB hBT hTD hDE hEH
    · have hs : -delta C.theta E∈Icc 0 frameCap :=
        ⟨he.1,by norm_num [frameCap]; linarith [he.2]⟩
      exact JointNegativeAEBT3.original atG true hsorted hcontained hQ hHy hGy hBy hDy
        hvar hr' hs (fun _ => he.2) ha'
        (by simp [JointNegativeAEBT3.Source.eError,JointNegativeAETD2.Source.eError]) hflat hEflat hz hhg hHG
        hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveT.Source
