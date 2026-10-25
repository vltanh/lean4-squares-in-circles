module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstNonpositiveT
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3Source
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESource
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3HighScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Source
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Source
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Source
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDSource
public import SquaresInCircles.Eight.Owners.GA.OuterESelection

/-!
# Eight squares: complete outer-E terminal for negative A normalization

A is a necessary-system motion, not an original packing. The sole
negative primary either has its *actual same-state* secondary projection
feasible (hence its selected primary total becomes zero), or the exact
local entry estimate supplies the positive flat-core and angle/tangent
cut used by the already proved short/long-E stress. This handles
arbitrary signs of the unchanged TD error and weak owner ties.

The new sources retain all unchanged original E and T witnesses.
-/

section
/-!
## Normalizing E first and A second, with A and E negative and positive TD2

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
end
end
end

section
/-!
## Negative A and nonnegative E, for every radial kind of E

`negative_A_nonnegative_E_positive_TD2_raw_false` splits the signed E total against the angle `s`
of the negative A primary: a short total `≤ s` is excluded by `NegativeA.ShortE.original`, a long
one by `NegativeA.LongE.original`. It is stated on a signed cycle at the squared radius `q` that
satisfies the necessary inequalities, so it applies when E was on the core curve and was
normalized before A moved; the moved A and E need not form a packing.

The inputs are the chosen DE and EH axes and the nonnegative sum of their selected signed primary
errors. The flat and tangent cuts of the negative A primary are hypotheses, given by the entry
theorems. Weak ties with zero slack are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

/-- A single negative A primary, with a nonnegative selected E total, positive TD2 and either weak
HG owner, is impossible. The selected E owners may be D2/E0, D3/E0, D2/E1 or D3/E1, and their
signed errors need not be nonnegative one by one. -/
theorem negative_A_nonnegative_E_positive_TD2_raw_false
    {q s : ℝ} {C : SignedCycle}
    (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q)
    (hqU : q≤qCap)
    (hH : 0≤(C.point H).y) (hG : (C.point G).y≤0)
    (hB : (C.point B).y≤0) (hD : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.NegativeAPositiveTD.Source.aError C atG= -s)
    (hflat : (C.point A).a=7/12)
    (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤ if atG then 39/250 else 1/2)
    (he : 0≤GlobalGA.PairedE.cycleTotal C de eh)
    (hz : 0≤delta C.theta T)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have hfinish (hg : Fin 4) (hhg : hg=0∨hg=2)
      (hHG' : C.Feasible H hg) : False := by
    by_cases hsmall : GlobalGA.PairedE.cycleTotal C de eh≤ s
    · exact GlobalGA.NegativeA.ShortE.original atG de eh
        hsorted hcontained hqU hH hG hB hD hvar hs ha hflat
        hAy hcut ⟨he,hsmall⟩ hz hhg hHG'
        hGA hAB hBT hTD hDE hEH
    · exact GlobalGA.NegativeA.LongE.original atG de eh
        hsorted hcontained hqU hH hG hB hD hvar hs ha hflat
        hAy (le_of_lt (lt_of_not_ge hsmall)) hz hhg hHG'
        hGA hAB hBT hTD hDE hEH
  rcases hHG with hh|hh
  · exact hfinish 0 (Or.inl rfl) hh
  · exact hfinish 2 (Or.inr rfl) hh

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## A core E, negative A and nonnegative E, with positive TD2

E, on the core curve, is normalized on a source domain before A moves. On the cycle with A moved,
the selected DE and EH axes of E, its selected total and the signed T error are those before the
move of A.

A negative flat GA3 or AB2 normal form of A either has the secondary GA2 or AB0 feasible at the
same state, and then the reselection gives the stress of nonnegative totals
`reduced_nonnegative_AE_false`, or satisfies the entry cut of A (`NegativeA.GA_entry`). In the
second case the short/long-E contradiction `negative_A_nonnegative_E_positive_TD2_raw_false`
applies to every radial kind and owner flag of E (`negative_A_nonnegative_E_positive_TD2_false`).
The cycle with A moved is used only as a signed cycle, not as a packing, and weak ties are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

private theorem core_E_nonnegative_as_charge
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E)) :
    0≤GlobalGA.PairedE.cycleTotal R.A.cycle
      (deFlag R.E.source) (ehFlag R.E.source) := by
  simpa [GlobalGA.PairedE.cycleTotal, GlobalGA.NonnegativeTotals.Source.eTotal,
    GlobalGA.PairedE.total, GlobalGA.PairedE.selected,
    ActualCoreEBlocks.eTotal,
    ActualCoreEBlocks.primaryDE,
    ActualCoreEBlocks.primaryEH,
    de_owner R.E.source,eh_owner R.E.source] using he

/-- The stress `negative_A_nonnegative_E_positive_TD2_raw_false` makes no assumption on the radial
kind of E. -/
private theorem core_negative_A_positive_TD2_with_entry_false
    (hqU : q≤qCap)
    (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (atG : Bool)
    (hGA : R.A.cycle.Feasible G (if atG then 3 else 2))
    (hAB : R.A.cycle.Feasible A (if atG then 0 else 2))
    (hflat : (R.A.cycle.point A).a=7/12)
    (hy : 0≤(R.A.cycle.point A).y)
    (hcut : (R.A.cycle.point A).y≤ if atG then 39/250 else 1/2)
    (s : ℝ)
    (hs : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.NegativeAPositiveTD.Source.aError R.A.cycle atG= -s) :
    False := by
  have hH : 0≤(R.A.cycle.point H).y := by
    rw [ATransport.H_point R.A]; exact R.E.source.H_positive.le
  have hG : (R.A.cycle.point G).y≤0 := by
    rw [ATransport.G_point R.A]; exact R.E.source.G_negative.le
  have hB : (R.A.cycle.point B).y≤0 := by
    rw [ATransport.B_point R.A]; exact R.E.source.B_negative.le
  have hD : (R.A.cycle.point D).y≤0 := by
    rw [ATransport.D_point R.A]; exact R.E.source.D_negative.le
  have hDE : R.A.cycle.Feasible D
      (if deFlag R.E.source then 3 else 2) := by
    rw [←de_owner R.E.source]; exact R.DE
  have hEH : R.A.cycle.Feasible E
      (if ehFlag R.E.source then 1 else 0) := by
    rw [←eh_owner R.E.source]; exact R.EH
  have hHG : R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
    (original_HG R.E.source).imp
      (ATransport.HG R.A 0) (ATransport.HG R.A 2)
  exact negative_A_nonnegative_E_positive_TD2_raw_false
    atG (deFlag R.E.source) (ehFlag R.E.source)
    R.A.necessary.sorted R.A.necessary.contained hqU
    hH hG hB hD
    (R.A.variation.trans R.E.source.positive_variation.le)
    hs ha hflat hy hcut (core_E_nonnegative_as_charge R he)
    hz hHG hGA hAB (R.BT2 hBT) (R.TD 2 hTD)
    hDE hEH

/-- A weak secondary GA2 witness at the same state reduces to nonnegative A and E totals, with
neither E nor T moved or reselected. -/
private theorem secondary_GA_core_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (hab : R.A.ab=false)
    (hsecondary : R.A.cycle.Feasible G 2) : False := by
  let P : CycleResult q R.E.cycle :=
    { R.A with
      ga := false
      GA := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,
          GlobalGA.PairedE.selected,hab] }
  let S : CoreEFirstResult I := ⟨R.E,P⟩
  have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal
      P.cycle (deFlag R.E.source) (ehFlag R.E.source) := by
    simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected,
      ActualCoreEBlocks.eTotal,
      ActualCoreEBlocks.primaryDE,
      ActualCoreEBlocks.primaryEH,
      de_owner R.E.source,eh_owner R.E.source] using he
  exact reduced_nonnegative_AE_false S hqU hBT
    (by simp [GlobalGA.NegativeANormalForm.total,
      GlobalGA.PairedE.selected,hab,P,S])
    he'

/-- Likewise a weak secondary AB0 witness at the same state gives a zero A primary total, without
moving A, E, T or any anchor on the circle. -/
private theorem secondary_AB_core_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (hga : R.A.ga=false)
    (hsecondary : R.A.cycle.Feasible A 0) : False := by
  let P : CycleResult q R.E.cycle :=
    { R.A with
      ab := false
      AB := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,
          GlobalGA.PairedE.selected,hga] }
  let S : CoreEFirstResult I := ⟨R.E,P⟩
  have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal
      P.cycle (deFlag R.E.source) (ehFlag R.E.source) := by
    simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected,
      ActualCoreEBlocks.eTotal,
      ActualCoreEBlocks.primaryDE,
      ActualCoreEBlocks.primaryEH,
      de_owner R.E.source,eh_owner R.E.source] using he
  exact reduced_nonnegative_AE_false S hqU hBT
    (by simp [GlobalGA.NegativeANormalForm.total,
      GlobalGA.PairedE.selected,hga,P,S])
    he'

/-- A negative normal form of A with a nonnegative selected E total is impossible on the cycle
with E then A moved, for positive TD2; both negative branches of the flat-A normal form are
covered. -/
theorem negative_A_nonnegative_E_positive_TD2_false
    (hqU : q≤qCap)
    (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (he : 0≤ActualCoreEBlocks.eTotal R.A.cycle
      (R.E.source.owner D) (R.E.source.owner E))
    (hnegative : ¬0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab
      (delta R.A.cycle.theta G) (delta R.A.cycle.theta A)) :
    False := by
  rcases R.A.reduced with hnonneg|⟨hg,ha,hflat,hy,hu⟩|⟨hg,ha,hflat,hy,hv⟩
  · exact hnegative hnonneg
  · by_cases hsec : R.A.cycle.Feasible G 2
    · exact secondary_GA_core_false R hqU hBT he ha hsec
    have hG : (R.A.cycle.point G).y≤0 := by
      rw [ATransport.G_point R.A]; exact R.E.source.G_negative.le
    have hquarter : quarterFeasible (R.A.cycle.point G) (R.A.cycle.point A)
        (delta R.A.cycle.theta G) 3 := by
      have hh : R.A.cycle.Feasible G 3 := by simpa [hg] using R.A.GA
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,G,A,quarterFeasible,sub_nonneg] using hh
    let s := -(delta R.A.cycle.theta G)
    have hs : s∈Ioc 0 frameCap := by
      dsimp [s]
      constructor
      · linarith [hu.2]
      · simp only [frameCap]
        linarith [hu.1]
    have houterA : (R.A.cycle.point A).y≤0→
        (R.A.cycle.point A).Outer q := by
      intro hh
      linarith [hy.1]
    rcases GlobalGA.NegativeA.GA_entry (R.A.necessary.sorted G)
        (R.A.necessary.contained G) (R.A.necessary.sorted A)
        (R.A.radial A) hqU hG houterA hs
        (by simpa [s,neg_neg] using hquarter) with hsecondary|⟨_,_,hcut,_⟩
    · apply hsec
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,G,A,quarterFeasible,sub_nonneg,s] using hsecondary
    have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut true) := by
      simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
        using (show -(delta R.A.cycle.theta G)∈Icc 0 (1/4:ℝ) by
          constructor <;> linarith [hu.1,hu.2])
    exact core_negative_A_positive_TD2_with_entry_false R hqU
      hBT hTD hz he true (by simpa [hg] using R.A.GA)
      (by simpa [ha] using R.A.AB) hflat hy.1.le hcut.le
      s hs' (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])
  · by_cases hsec : R.A.cycle.Feasible A 0
    · exact secondary_AB_core_false R hqU hBT he hg hsec
    let s := -(delta R.A.cycle.theta A)
    have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut false) := by
      simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
        using (show -(delta R.A.cycle.theta A)∈Icc 0 (19/50:ℝ) by
          constructor <;> linarith [hv.1,hv.2])
    exact core_negative_A_positive_TD2_with_entry_false R hqU
      hBT hTD hz he false (by simpa [hg] using R.A.GA)
      (by simpa [ha] using R.A.AB) hflat hy.1.le hy.2.le
      s hs' (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## Normalizing E first and A second, with nonnegative A and positive TD2

The normal form of a core E has three alternatives at the same radius: a nonnegative E total, a
negative DE3 with EH0, or a negative EH1 with DE2. The last one first checks EH0 on the cycle with
A moved: if it is feasible, E takes the secondary EH0 without moving
(`positive_TD2_secondary_E_false`); otherwise the EH1 stress uses the short-angle entry
inequality. Both keep the H and D anchors, BT2 and TD2 with the same signed T error
(`nonnegative_A_positive_TD2_all_E_false`). Neither an order nor a source domain is assumed after
A moves.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm
variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- The move of A keeps the anchors H, G, B and D with their signs, and the variation budget
(`budget`). -/
private theorem anchor_signs :
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

private theorem hg :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp (ATransport.HG R.A 0) (ATransport.HG R.A 2)

private theorem budget :
    positiveVariation R.A.cycle.theta≤frameCap :=
  R.A.variation.trans R.E.source.positive_variation.le

/-- The signed-circle stress excludes any feasible pair DE2, EH0, whether or not it is the selected
E pair. -/
theorem positive_TD2_secondary_E_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hDE : R.A.cycle.Feasible D 2)
    (hEH : R.A.cycle.Feasible E 0) : False := by
  obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
  have he : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle false false := by
    simp [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected]
  exact GlobalGA.NonnegativeTotals.Source.actual_false
    R.A.ga R.A.ab false false
    R.A.necessary.sorted R.A.necessary.contained hqU
    hH hG hB hD (budget R) ha hz he
    (hg R) R.A.GA R.A.AB (R.BT2 hBT) (R.TD 2 hTD) hDE hEH

/-- For a core E normalized first, a nonnegative selected A total with TD2 and a nonnegative T
error is impossible, for every selected sign on D and E. -/
theorem nonnegative_A_positive_TD2_all_E_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (ha : 0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab (delta R.A.cycle.theta G)
        (delta R.A.cycle.theta A)) : False := by
  have ha' : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected] using ha
  rcases R.E_reduced with he|⟨hflat,hcase⟩
  · have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle
        (deFlag R.E.source) (ehFlag R.E.source) := by
      simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
        GlobalGA.PairedE.total,GlobalGA.CoreENegativeTotal.selected_total,
        GlobalGA.PairedE.cycleTotal,de_owner R.E.source,eh_owner R.E.source]
        using he
    exact reduced_nonnegative_AE_false R hqU hBT ha he'
  · obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
    rcases hcase with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : R.A.cycle.Feasible D 3 := by
        simpa [hde] using R.DE
      have hEH : R.A.cycle.Feasible E 0 := by
        simpa [heh] using R.EH
      exact GlobalGA.NegativeDEPositiveTD.Source.actual_false
        R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
        hqU hH hG hB hD (budget R) ha' hz hd.le hflat
        (hg R) R.A.GA R.A.AB (R.BT2 hBT) (R.TD 2 hTD) hDE hEH
    · have hDE : R.A.cycle.Feasible D 2 := by
        simpa [hde] using R.DE
      have hEH : R.A.cycle.Feasible E 1 := by
        simpa [heh] using R.EH
      by_cases hE0 : R.A.cycle.Feasible E 0
      · exact positive_TD2_secondary_E_false R hqU hBT hTD hz ha' hDE hE0
      · have hEy : (R.A.cycle.point E).y≤0 := by
          rw [R.E_point]
          exact R.E.source.E_nonpos
        exact GlobalGA.NegativeEHPositiveTD.Source.actual_false
          R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
          hqU hH hG hB hD hEy R.E_core (budget R)
          ha' hz he hE0 (hg R) R.A.GA R.A.AB
          (R.BT2 hBT) (R.TD 2 hTD) hDE hEH

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## A single negative flat A primary, positive TD2 and an outer E

`reduced_negative_A_outer_E_positive_TD2_false` splits the selected E total against the angle `s`
of the negative A primary, short (`NegativeA.ShortE.original`) or long
(`NegativeA.LongE.original`), on the cycle with A moved. E does not move. Its DE and EH witnesses
are reselected on the source domain (`OuterE.select`) and stay feasible on the cycle with A moved;
neither the gap order of that cycle nor its selected normals are used.

The angle and the tangent cut of the negative A primary are hypotheses here; they come from the
entry lemmas or from a reselection of a secondary at the same state.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C) (O : CycleResult q C)

include I in
/-- Both sizes of the nonnegative selected total of an outer E, against the negative error of a
flat A, are excluded, for either weak HG owner and either negative primary of A. -/
theorem reduced_negative_A_outer_E_positive_TD2_false
    (hqU : q≤qCap)
    (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hz : 0≤delta C.theta T)
    (atG : Bool)
    (hGA : O.cycle.Feasible G (if atG then 3 else 2))
    (hAB : O.cycle.Feasible A (if atG then 0 else 2))
    (hflat : (O.cycle.point A).a=7/12)
    (hy : 0≤(O.cycle.point A).y)
    (hcut : (O.cycle.point A).y≤ if atG then 39/250 else 1/2)
    (s : ℝ)
    (hs : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.NegativeAPositiveTD.Source.aError O.cycle atG= -s) :
    False := by
  let S := GlobalGA.OuterE.select I hqU houter
  have hBT' := ATransport.BT2 O hBT
  have hTD' := ATransport.TD O 2 hTD
  have hHG' : O.cycle.Feasible H 0∨O.cycle.Feasible H 2 :=
    (original_HG I).imp (ATransport.HG O 0) (ATransport.HG O 2)
  have hDE' := ATransport.DE O _ S.DE
  have hEH' := ATransport.EH O _ S.EH
  have hH : 0≤(O.cycle.point H).y := by
    rw [ATransport.H_point O]; exact I.H_positive.le
  have hG : (O.cycle.point G).y≤0 := by
    rw [ATransport.G_point O]; exact I.G_negative.le
  have hB : (O.cycle.point B).y≤0 := by
    rw [ATransport.B_point O]; exact I.B_negative.le
  have hD : (O.cycle.point D).y≤0 := by
    rw [ATransport.D_point O]; exact I.D_negative.le
  have hvar : positiveVariation O.cycle.theta≤frameCap :=
    O.variation.trans I.positive_variation.le
  have hz' : 0≤delta O.cycle.theta T := by
    rw [ATransport.original_T_error O]
    exact hz
  have he : 0≤GlobalGA.PairedE.cycleTotal O.cycle S.de S.eh := by
    simpa [GlobalGA.PairedE.cycleTotal,GlobalGA.PairedE.total,
      GlobalGA.PairedE.selected,ATransport.original_D_error O,
      ATransport.original_E_error O] using S.total_nonneg
  have hfinish (hg : Fin 4) (hhg : hg=0∨hg=2)
      (hHG : O.cycle.Feasible H hg) : False := by
    by_cases hsmall : GlobalGA.PairedE.cycleTotal O.cycle S.de S.eh ≤ s
    · exact GlobalGA.NegativeA.ShortE.original atG S.de S.eh
        O.necessary.sorted O.necessary.contained hqU
        hH hG hB hD hvar hs ha hflat hy hcut
        ⟨he,hsmall⟩ hz' hhg hHG hGA hAB hBT' hTD' hDE' hEH'
    · exact GlobalGA.NegativeA.LongE.original atG S.de S.eh
        O.necessary.sorted O.necessary.contained hqU
        hH hG hB hD hvar hs ha hflat hy
        (le_of_lt (lt_of_not_ge hsmall)) hz' hhg hHG hGA hAB
        hBT' hTD' hDE' hEH'
  rcases hHG' with hh|hh
  · exact hfinish 0 (Or.inl rfl) hh
  · exact hfinish 2 (Or.inr rfl) hh

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## Transported-A nonnegative selected total, actual outer E

After moving A, the result is a necessary seven-circle cycle, not
necessarily an ordered original packing. This exclusion deliberately
uses the raw nonnegative-A/E signed-stress lemma rather than building a
fictitious SourceDomain on the moved A cycle. E remains literally the
original outer E; its weak owner reselection occurs on original I, at
the unchanged q, and its true projections carry over to the new cycle.

Both actual T owners and every signed TD2 error are included.
No kernel compilation or CI was run.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C) (O : CycleResult q C)

include I in
/-- Moving A cannot invalidate the outer-E selection, signed E total,
the original BT2 witness, or either actual TD owner. -/
theorem reduced_nonnegative_A_outer_E_false
    (hqU : q≤qCap) (hBT : C.Feasible B 2)
    (houter : (C.point E).Outer q)
    (ha : 0≤GlobalGA.NegativeANormalForm.total O.ga O.ab
      (delta O.cycle.theta G) (delta O.cycle.theta A)) : False := by
  let S := GlobalGA.OuterE.select I hqU houter
  have hBT' := ATransport.BT2 O hBT
  have hHG' : O.cycle.Feasible H 0∨O.cycle.Feasible H 2 :=
    (original_HG I).imp (ATransport.HG O 0) (ATransport.HG O 2)
  have hTD' : O.cycle.Feasible T 0∨O.cycle.Feasible T 2 :=
    (original_TD I).imp (ATransport.TD O 0) (ATransport.TD O 2)
  have hDE' := ATransport.DE O _ S.DE
  have hEH' := ATransport.EH O _ S.EH
  have hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal O.cycle O.ga O.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected] using ha
  have hE : 0≤GlobalGA.NonnegativeTotals.Source.eTotal O.cycle S.de S.eh := by
    simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.cycleTotal,
      ATransport.original_D_error O,ATransport.original_E_error O]
      using S.total_nonneg
  have hH : 0≤(O.cycle.point H).y := by
    rw [ATransport.H_point O]
    exact I.H_positive.le
  have hG : (O.cycle.point G).y≤0 := by
    rw [ATransport.G_point O]
    exact I.G_negative.le
  have hB : (O.cycle.point B).y≤0 := by
    rw [ATransport.B_point O]
    exact I.B_negative.le
  have hD : (O.cycle.point D).y≤0 := by
    rw [ATransport.D_point O]
    exact I.D_negative.le
  exact GlobalGA.NonnegativeTotals.all_TD_false
    O.ga O.ab S.de S.eh O.necessary.sorted O.necessary.contained
    (O.necessary.core T) hqU hH hG hB hD
    (O.variation.trans I.positive_variation.le) hA hE hHG'
    O.GA O.AB hBT' hTD' hDE' hEH'

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C) (O : CycleResult q C)

include I in
/-- Negative reduced GA3 with actual GA2 as a weak secondary: selecting
GA2 on the same moved state gives the nonnegative-A terminal. -/
theorem reduced_GA_secondary_outer_E_false
    (hqU : q≤qCap) (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2)
    (hab : O.ab=false) (hsecondary : O.cycle.Feasible G 2) : False := by
  let P : CycleResult q C :=
    { O with
      ga := false
      GA := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hab] }
  exact reduced_nonnegative_A_outer_E_false I P hqU hBT houter
    (by simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hab,P])

include I in
/-- Negative reduced AB2 with actual AB0 as a weak secondary: likewise
no change of the moved A state, its radius or any non-A witness. -/
theorem reduced_AB_secondary_outer_E_false
    (hqU : q≤qCap) (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2)
    (hga : O.ga=false) (hsecondary : O.cycle.Feasible A 0) : False := by
  let P : CycleResult q C :=
    { O with
      ab := false
      AB := hsecondary
      reduced := by
        apply Or.inl
        simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hga] }
  exact reduced_nonnegative_A_outer_E_false I P hqU hBT houter
    (by simp [GlobalGA.NegativeANormalForm.total,GlobalGA.PairedE.selected,hga,P])

include I in
/-- All negative-A transported normal forms with the *unchanged original
outer E* are impossible under BT2, for either physical TD owner and
every signed T error. Only the necessary cycle O is used after A moves. -/
theorem negative_A_outer_E_all_T_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2)
    (hnegative : ¬0≤GlobalGA.NegativeANormalForm.total O.ga O.ab
      (delta O.cycle.theta G) (delta O.cycle.theta A)) : False := by
  by_cases hpositive : tdFlag I=true ∧ 0<delta C.theta T
  · have hTD : C.Feasible T 2 := by
      have ho : I.owner T=2 := tdFlag_true I hpositive.1
      simpa [ho] using I.feasible T
    rcases O.reduced with hnonneg|⟨hg,ha,hflat,hy,hu⟩|⟨hg,ha,hflat,hy,hv⟩
    · exact hnegative hnonneg
    · by_cases hsec : O.cycle.Feasible G 2
      · exact reduced_GA_secondary_outer_E_false I O hqU houter hBT ha hsec
      have hG : (O.cycle.point G).y≤0 := by
        rw [ATransport.G_point O]; exact I.G_negative.le
      have hquarter : quarterFeasible (O.cycle.point G) (O.cycle.point A)
          (delta O.cycle.theta G) 3 := by
        have hh : O.cycle.Feasible G 3 := by simpa [hg] using O.GA
        simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
          word,delta,next,G,A,quarterFeasible,sub_nonneg] using hh
      let s := -(delta O.cycle.theta G)
      have hs : s∈Ioc 0 frameCap := by
        dsimp [s]
        constructor
        · linarith [hu.2]
        · simp only [frameCap]
          linarith [hu.1]
      have houterA : (O.cycle.point A).y≤0→(O.cycle.point A).Outer q := by
        intro hh
        linarith [hy.1]
      rcases GlobalGA.NegativeA.GA_entry (O.necessary.sorted G)
          (O.necessary.contained G) (O.necessary.sorted A) (O.radial A)
          hqU hG houterA hs
          (by simpa [s,neg_neg] using hquarter) with hsecondary|⟨_,_,hcut,_⟩
      · apply hsec
        simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
          word,delta,next,G,A,quarterFeasible,sub_nonneg,s] using hsecondary
      have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut true) := by
        simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
          using (show -(delta O.cycle.theta G)∈Icc 0 (1/4:ℝ) by
            constructor <;> linarith [hu.1,hu.2])
      exact reduced_negative_A_outer_E_positive_TD2_false I O hqU houter
        hBT hTD hpositive.2.le true
        (by simpa [hg] using O.GA) (by simpa [ha] using O.AB)
        hflat hy.1.le hcut.le s hs'
        (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])
    · by_cases hsec : O.cycle.Feasible A 0
      · exact reduced_AB_secondary_outer_E_false I O hqU houter hBT hg hsec
      let s := -(delta O.cycle.theta A)
      have hs' : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut false) := by
        simpa [s,GlobalGA.NegativeAPositiveTD.Explicit.angleCut]
          using (show -(delta O.cycle.theta A)∈Icc 0 (19/50:ℝ) by
            constructor <;> linarith [hv.1,hv.2])
      exact reduced_negative_A_outer_E_positive_TD2_false I O hqU houter
        hBT hTD hpositive.2.le false
        (by simpa [hg] using O.GA) (by simpa [ha] using O.AB)
        hflat hy.1.le (by simpa using hy.2.le) s hs'
        (by simp [GlobalGA.NegativeAPositiveTD.Source.aError,s])
  · have htd : tdFlag I=true→delta C.theta T≤0 := by
      intro ht
      by_contra hn
      exact hpositive ⟨ht,lt_of_not_ge hn⟩
    exact negative_reduced_A_nonpositive_T_false I O hqL hqU hBT htd hnegative

end SquaresInCircles.Eight.HighGABT2
end
end
end
