module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstNonnegative
public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstSecondaryE
public import SquaresInCircles.Eight.Owners.GA.High.BT2NonpositivePrimaries
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD0Source
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD0Source
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAStress

/-!
# Eight squares: a core E, E first and A second, with nonnegative A and nonpositive T

E is normalized while the cycle is an ordered boundary cycle. The move of A that follows gives a
signed cycle that is used only through the seven circle inequalities of the necessary conditions,
not as a packing. The cases are: a nonnegative selected E total, or a single negative DE3 or EH1
on the flat core; a selected A total in `[0, 1/6]` or in `[1/6, frameCap]`; and TD0, or TD2 with
nonpositive error (`nonnegative_A_nonpositive_T_all_E_false`). The scalar stresses for the low and
the high A totals, with TD0 or TD2, apply with the weak witnesses of the cycle. For EH1, a feasible
EH0 is reselected on the same cycle; otherwise the geometry of E and H gives the short cut of the
angle of E.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- After A moves, the total of the selected A primaries, not the sum of both A angles, stays in
the signed-variation window `[0, frameCap]` of the source domain. -/
private theorem a_total_domain
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab) :
    GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab∈
      Icc 0 frameCap := by
  have hp : positiveVariation R.A.cycle.theta≤frameCap :=
    R.A.variation.trans R.E.source.positive_variation.le
  have hn : negativeVariation R.A.cycle.theta≤frameCap := by
    rw [←variations_equal]
    exact hp
  have hpair := GlobalGA.Secondary.original_pair_budgets (i:=G) (j:=A)
    hp hn (by norm_num [G,A])
  exact GlobalGA.PairedE.total_bounds R.A.ga R.A.ab hpair.1 hpair.2
    (by simpa [GlobalGA.PairedE.LowA.aTotal,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total] using ha)

/-- The signs of H, G, B and D used by the A, E and T stresses, after the move of A. -/
private theorem anchor_signs :
    0≤(R.A.cycle.point H).y ∧
      (R.A.cycle.point G).y≤0 ∧
      (R.A.cycle.point B).y≤0 ∧
      (R.A.cycle.point D).y≤0 := by
  constructor
  · rw [ATransport.H_point R.A]; exact R.E.source.H_positive.le
  constructor
  · rw [ATransport.G_point R.A]; exact R.E.source.G_negative.le
  constructor
  · rw [ATransport.B_point R.A]; exact R.E.source.B_negative.le
  · rw [ATransport.D_point R.A]; exact R.E.source.D_negative.le

private theorem H_witness :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp (ATransport.HG R.A 0) (ATransport.HG R.A 2)

/-- A nonnegative selected A total, a nonpositive selected T primary and a negative DE3 with the
secondary EH0 are impossible. -/
theorem nonnegative_A_negative_DE_nonpositive_T_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hTD : R.A.cycle.Feasible T (if tdFlag R.E.source then 2 else 0))
    (ht : tdFlag R.E.source=true→delta R.A.cycle.theta T≤0)
    (hflat : (R.A.cycle.point E).a=7/12)
    (hd : delta R.A.cycle.theta D<0)
    (hDE : R.A.cycle.Feasible D 3)
    (hEH : R.A.cycle.Feasible E 0) : False := by
  obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
  have hEy : (R.A.cycle.point E).y≤0 := by
    rw [R.E_point]; exact R.E.source.E_nonpos
  have ha := a_total_domain R hA
  have hv : positiveVariation R.A.cycle.theta≤frameCap :=
    R.A.variation.trans R.E.source.positive_variation.le
  by_cases hsmall : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab ≤ 1/6
  · exact GlobalGA.NegativeELowA.actual_false
      R.A.ga R.A.ab (tdFlag R.E.source) true false
      R.A.necessary.sorted R.A.necessary.contained
      (R.A.necessary.core T) hqU hH hG hB hD hflat hv
      (H_witness R) R.A.GA R.A.AB (R.BT2 hBT)
      hTD hDE hEH ⟨ha.1,hsmall⟩ ht
      (fun _=>hd.le) (by intro h; cases h)
  · have hhigh : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab∈
        Icc (1/6:ℝ) frameCap := ⟨(lt_of_not_ge hsmall).le,ha.2⟩
    cases htflag : tdFlag R.E.source
    · have hTD0 : R.A.cycle.Feasible T 0 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeDETD0.original_high_false
        R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
        hqU hH hG hB hD hEy R.E_core hv hhigh hd.le
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD0
        hDE hEH
    · have hTD2 : R.A.cycle.Feasible T 2 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeELargeA.Source.actual_false
        R.A.ga R.A.ab true false
        R.A.necessary.sorted R.A.necessary.contained
        (R.A.necessary.core T) hqU hH hG hB hD hflat hv
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD2 hDE hEH
        hhigh (ht htflag) (fun _=>hd.le) (by intro h; cases h)

/-- A single negative EH1 has a quarter entry, so the flat tangent and angle cut of E hold on this
cycle. The cyclic order of the moved A is not used. -/
theorem nonnegative_A_negative_EH_nonpositive_T_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hTD : R.A.cycle.Feasible T (if tdFlag R.E.source then 2 else 0))
    (ht : tdFlag R.E.source=true→delta R.A.cycle.theta T≤0)
    (hEneg : delta R.A.cycle.theta E<0)
    (hDE : R.A.cycle.Feasible D 2)
    (hEH : R.A.cycle.Feasible E 1) : False := by
  by_cases hEH0 : R.A.cycle.Feasible E 0
  · exact nonnegative_A_secondary_E_all_T_false R hqU hBT hA hDE hEH0
  have hv : positiveVariation R.A.cycle.theta≤frameCap :=
    R.A.variation.trans R.E.source.positive_variation.le
  have hEy : (R.A.cycle.point E).y≤0 := by
    rw [R.E_point]; exact R.E.source.E_nonpos
  have hHy : 0≤(R.A.cycle.point H).y := by
    rw [ATransport.H_point R.A]
    exact R.E.source.H_positive.le
  obtain ⟨hflat,hb,hmag⟩ :=
    GlobalGA.NegativeEHPositiveTD.Source.genuine_domain
      R.A.necessary.sorted R.A.necessary.contained hqU hHy hEy
      R.E_core hv hEneg hEH hEH0
  have hang : -delta R.A.cycle.theta E∈Icc (0:ℝ) (1/4) := by
    constructor
    · linarith
    · simpa [GlobalGA.NegativeEHPositiveTD.Source.magnitude] using hmag
  obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
  have ha := a_total_domain R hA
  by_cases hsmall : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab ≤ 1/6
  · exact GlobalGA.NegativeELowA.actual_false
      R.A.ga R.A.ab (tdFlag R.E.source) false true
      R.A.necessary.sorted R.A.necessary.contained
      (R.A.necessary.core T) hqU hH hG hB hD hflat hv
      (H_witness R) R.A.GA R.A.AB (R.BT2 hBT)
      hTD hDE hEH ⟨ha.1,hsmall⟩ ht
      (by intro h; cases h) (fun _=>hang)
  · have hhigh : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab∈
        Icc (1/6:ℝ) frameCap := ⟨(lt_of_not_ge hsmall).le,ha.2⟩
    cases htflag : tdFlag R.E.source
    · have hTD0 : R.A.cycle.Feasible T 0 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeEHTD0.original_high_false
        R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
        hqU hH hG hB hD hEy R.E_core hv hhigh hEneg hEH0
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD0
        hDE hEH
    · have hTD2 : R.A.cycle.Feasible T 2 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeELargeA.Source.actual_false
        R.A.ga R.A.ab false true
        R.A.necessary.sorted R.A.necessary.contained
        (R.A.necessary.core T) hqU hH hG hB hD hflat hv
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD2 hDE hEH
        hhigh (ht htflag)
        (by intro h; cases h) (fun _=>⟨hang,hb.2⟩)

/-- Every E normal form with a nonnegative selected A total and a nonpositive selected T primary
is impossible, including a TD0 error of either sign, a zero TD2 error and simultaneous weak
owners. -/
theorem nonnegative_A_nonpositive_T_all_E_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (ha : 0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab (delta R.A.cycle.theta G)
        (delta R.A.cycle.theta A))
    (ht : tdFlag R.E.source=true→delta R.A.cycle.theta T≤0) : False := by
  have ha' : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected] using ha
  have hTD : R.A.cycle.Feasible T (if tdFlag R.E.source then 2 else 0) := by
    apply R.TD
    rw [←td_owner R.E.source]
    exact R.E.source.feasible T
  rcases R.E_reduced with he|⟨hflat,hcase⟩
  · have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle
        (deFlag R.E.source) (ehFlag R.E.source) := by
      simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
        GlobalGA.PairedE.total,GlobalGA.CoreENegativeTotal.selected_total,
        GlobalGA.PairedE.cycleTotal,de_owner R.E.source,eh_owner R.E.source]
        using he
    exact reduced_nonnegative_AE_false R hqU hBT ha he'
  · rcases hcase with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · exact nonnegative_A_negative_DE_nonpositive_T_false
        R hqU hBT ha' hTD ht hflat hd
        (by simpa [hde] using R.DE)
        (by simpa [heh] using R.EH)
    · exact nonnegative_A_negative_EH_nonpositive_T_false
        R hqU hBT ha' hTD ht he
        (by simpa [hde] using R.DE)
        (by simpa [heh] using R.EH)

end SquaresInCircles.Eight.HighGABT2
