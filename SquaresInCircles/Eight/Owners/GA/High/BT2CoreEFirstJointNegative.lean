module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirst
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Source
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Source
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Source

/-!
# Eight squares: normalizing E first and A second, with A and E negative and positive TD2

`negative_A_negative_E_positive_TD2_false` is the branch of the high-GA BT2 theorem with two
negative primaries. E moves on a source domain before A moves; the move of A gives a signed cycle
that satisfies the necessary conditions, not a second packing. All seven signed witnesses are
taken on that cycle, at the same squared radius.

For E with a negative DE3 the joint-negative stress `JointNegativeAETD2.original` needs no bound
on the angle of E. For a negative EH1, a feasible secondary EH0 is excluded by the negative-A TD2
stress `NegativeAPositiveTD.Source.original` without moving E; otherwise the geometric entry of
EH1 gives the short angle `s ≤ 1/4` that the joint-negative stress requires. A zero angle or a
tie enters the corresponding secondary.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

private theorem frame_signs :
    0≤(R.A.cycle.point H).y ∧
    (R.A.cycle.point G).y≤0 ∧
    (R.A.cycle.point B).y≤0 ∧
    (R.A.cycle.point D).y≤0 := by
  constructor
  · rw [ATransport.H_point R.A]
    exact R.E.source.H_positive.le
  constructor
  · rw [ATransport.G_point R.A]
    exact R.E.source.G_negative.le
  constructor
  · rw [ATransport.B_point R.A]
    exact R.E.source.B_negative.le
  · rw [ATransport.D_point R.A]
    exact R.E.source.D_negative.le

private theorem source_HG :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp
    (ATransport.HG R.A 0) (ATransport.HG R.A 2)

private theorem source_budget :
    positiveVariation R.A.cycle.theta≤frameCap :=
  R.A.variation.trans R.E.source.positive_variation.le

private theorem negative_error_in_frame (i : Vertex)
    (hneg : delta R.A.cycle.theta i<0) :
    -(delta R.A.cycle.theta i)∈Icc 0 frameCap := by
  have hv := source_budget R
  have hn : negativeVariation R.A.cycle.theta≤frameCap := by
    rw [←variations_equal]
    exact hv
  have habs := GlobalGA.Secondary.original_error_bound hv hn i
  exact ⟨by linarith, (neg_le_abs _).trans habs⟩

private theorem angle_A_joint (atG : Bool) {r : ℝ}
    (hr : r∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG)) :
    r∈Icc (0:ℝ) (19/50) := by
  refine ⟨hr.1,?_⟩
  have h2 := hr.2
  cases atG <;>
    simp only [GlobalGA.NegativeAPositiveTD.Explicit.angleCut,
      Bool.false_eq_true,↓reduceIte] at h2 <;>
    linarith

private theorem raw_joint_negative_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (atG atH : Bool) (r s : ℝ)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hshort : atH=true→s≤1/4)
    (ha : GlobalGA.JointNegativeAETD2.Source.aError R.A.cycle atG= -r)
    (he : GlobalGA.JointNegativeAETD2.Source.eError R.A.cycle atH= -s)
    (hAflat : (R.A.cycle.point A).a=7/12)
    (hEflat : (R.A.cycle.point E).a=7/12)
    (hGA : R.A.cycle.Feasible G (if atG then 3 else 2))
    (hAB : R.A.cycle.Feasible A (if atG then 0 else 2))
    (hDE : R.A.cycle.Feasible D (if atH then 2 else 3))
    (hEH : R.A.cycle.Feasible E (if atH then 1 else 0)) :
    False := by
  obtain ⟨hH,hG,hB,hD⟩ := frame_signs R
  have hfinish (hg : Fin 4) (hhg : hg=0∨hg=2)
      (hHG : R.A.cycle.Feasible H hg) : False :=
    GlobalGA.JointNegativeAETD2.original atG atH
      R.A.necessary.sorted R.A.necessary.contained hqU
      hH hG hB hD (source_budget R) hr hs hshort
      ha he hAflat hEflat hz hhg hHG hGA hAB
      (R.BT2 hBT) (R.TD 2 hTD) hDE hEH
  rcases source_HG R with hh|hh
  · exact hfinish 0 (Or.inl rfl) hh
  · exact hfinish 2 (Or.inr rfl) hh

/-- If EH0 is feasible as well as EH1 on the same cycle, the pair DE2, EH0 has zero selected E
charge, and the negative-A stress excludes it without moving E. -/
private theorem EH_secondary_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (atG : Bool) (r : ℝ)
    (hr : r∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.JointNegativeAETD2.Source.aError R.A.cycle atG= -r)
    (hAflat : (R.A.cycle.point A).a=7/12)
    (hGA : R.A.cycle.Feasible G (if atG then 3 else 2))
    (hAB : R.A.cycle.Feasible A (if atG then 0 else 2))
    (hDE : R.A.cycle.Feasible D 2)
    (hEH0 : R.A.cycle.Feasible E 0) : False := by
  obtain ⟨hH,hG,hB,hD⟩ := frame_signs R
  have hfinish (hg : Fin 4) (hhg : hg=0∨hg=2)
      (hHG : R.A.cycle.Feasible H hg) : False := by
    exact GlobalGA.NegativeAPositiveTD.Source.original atG
      R.A.necessary.sorted R.A.necessary.contained hqU
      hH hG hB hD (source_budget R) hr
      (by simpa [GlobalGA.JointNegativeAETD2.Source.aError,
        GlobalGA.NegativeAPositiveTD.Source.aError] using ha)
      hAflat hz hhg hHG hGA hAB
      (R.BT2 hBT) (R.TD 2 hTD) hDE hEH0
  rcases source_HG R with hh|hh
  · exact hfinish 0 (Or.inl rfl) hh
  · exact hfinish 2 (Or.inr rfl) hh

/-- The two negative E alternatives on the cycle with E then A moved. DE3 needs no short E cut;
EH1 either has its secondary EH0 or satisfies the quarter entry bound given by the geometry. -/
private theorem negative_E_cases_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (atG : Bool) (r : ℝ)
    (hr : r∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.JointNegativeAETD2.Source.aError R.A.cycle atG= -r)
    (hAflat : (R.A.cycle.point A).a=7/12)
    (hGA : R.A.cycle.Feasible G (if atG then 3 else 2))
    (hAB : R.A.cycle.Feasible A (if atG then 0 else 2))
    (hEflat : (R.A.cycle.point E).a=7/12)
    (hcase :
      ((R.E.source.owner D=3 ∧ R.E.source.owner E=0 ∧
          delta R.A.cycle.theta D<0) ∨
       (R.E.source.owner D=2 ∧ R.E.source.owner E=1 ∧
          delta R.A.cycle.theta E<0))) : False := by
  rcases hcase with ⟨hd,he,hdneg⟩|⟨hd,he,heneg⟩
  · let s := -(delta R.A.cycle.theta D)
    have hs : s∈Icc 0 frameCap := negative_error_in_frame R D hdneg
    have hDE : R.A.cycle.Feasible D 3 := by simpa [hd] using R.DE
    have hEH : R.A.cycle.Feasible E 0 := by simpa [he] using R.EH
    exact raw_joint_negative_false R hqU hBT hTD hz
      atG false r s (angle_A_joint atG hr) hs
      (by intro h; cases h) ha
      (by simp [GlobalGA.JointNegativeAETD2.Source.eError,s])
      hAflat hEflat hGA hAB hDE hEH
  · have hDE : R.A.cycle.Feasible D 2 := by simpa [hd] using R.DE
    have hEH : R.A.cycle.Feasible E 1 := by simpa [he] using R.EH
    by_cases hsecondary : R.A.cycle.Feasible E 0
    · exact EH_secondary_false R hqU hBT hTD hz atG r hr ha
        hAflat hGA hAB hDE hsecondary
    have hEy : (R.A.cycle.point E).y≤0 := by
      rw [R.E_point]; exact R.E.source.E_nonpos
    have hHy : 0≤(R.A.cycle.point H).y := (frame_signs R).1
    obtain ⟨_,_,hshort⟩ :=
      GlobalGA.NegativeEHPositiveTD.Source.genuine_domain
        R.A.necessary.sorted R.A.necessary.contained hqU
        hHy hEy R.E_core (source_budget R)
        heneg hEH hsecondary
    let s := -(delta R.A.cycle.theta E)
    have hs : s∈Icc 0 frameCap := negative_error_in_frame R E heneg
    exact raw_joint_negative_false R hqU hBT hTD hz
      atG true r s (angle_A_joint atG hr) hs
      (by intro _; simpa [s,GlobalGA.NegativeEHPositiveTD.Source.magnitude]
        using hshort) ha
      (by simp [GlobalGA.JointNegativeAETD2.Source.eError,s])
      hAflat hEflat hGA hAB hDE hEH

/-- On the cycle with a core E normalized and then A moved, negative normal forms of both A and E
are impossible with positive TD2. -/
theorem negative_A_negative_E_positive_TD2_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (hnegative : ¬0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab (delta R.A.cycle.theta G)
        (delta R.A.cycle.theta A))
    (hEflat : (R.A.cycle.point E).a=7/12)
    (hcase :
      ((R.E.source.owner D=3 ∧ R.E.source.owner E=0 ∧
          delta R.A.cycle.theta D<0) ∨
       (R.E.source.owner D=2 ∧ R.E.source.owner E=1 ∧
          delta R.A.cycle.theta E<0))) : False := by
  rcases R.A.reduced with hnonneg|⟨hg,hab,hAflat,hy,hu⟩|
      ⟨hg,hab,hAflat,hy,hv⟩
  · exact hnegative hnonneg
  · let r := -(delta R.A.cycle.theta G)
    have hr : r∈Icc 0
        (GlobalGA.NegativeAPositiveTD.Explicit.angleCut true) := by
      simpa [r,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
        using (show -(delta R.A.cycle.theta G)∈Icc 0 (1/4:ℝ) by
          constructor <;> linarith [hu.1,hu.2])
    exact negative_E_cases_false R hqU hBT hTD hz true r hr
      (by simp [GlobalGA.JointNegativeAETD2.Source.aError,r])
      hAflat (by simpa [hg] using R.A.GA)
      (by simpa [hab] using R.A.AB) hEflat hcase
  · let r := -(delta R.A.cycle.theta A)
    have hr : r∈Icc 0
        (GlobalGA.NegativeAPositiveTD.Explicit.angleCut false) := by
      simpa [r,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
        using (show -(delta R.A.cycle.theta A)∈Icc 0 (19/50:ℝ) by
          constructor <;> linarith [hv.1,hv.2])
    exact negative_E_cases_false R hqU hBT hTD hz false r hr
      (by simp [GlobalGA.JointNegativeAETD2.Source.aError,r])
      hAflat (by simpa [hg] using R.A.GA)
      (by simpa [hab] using R.A.AB) hEflat hcase

end SquaresInCircles.Eight.HighGABT2
