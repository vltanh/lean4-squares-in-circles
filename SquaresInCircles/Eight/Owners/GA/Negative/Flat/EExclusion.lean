module

public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EGainReserve
public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EStress

/-!
# Eight squares: simultaneous nonpositive A, T, and flat-core-E primary owners

The two E gains are added before the decreasing ratio comparison is applied (`gains_reserve`).
Every multiplier is positive, whereas the necessary inequalities make the collected stress
nonpositive (`actual_false`). The statement is about signed cycles with the necessary conditions,
so it applies after the moves of the cycle; no marker theorem is applied after a move.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
open Candidate Secondary

def magnitude (primary : Bool) (d : ℝ) : ℝ := if primary then -d else 0

theorem magnitude_nonneg (p : Bool) {d : ℝ} (hd : p=true → d≤0) : 0≤ magnitude p d := by
  cases hp : p
  · simp [magnitude]
  · simpa [magnitude,hp] using neg_nonneg.mpr (hd hp)

theorem magnitude_le_negativePart (p : Bool) (d : ℝ) : magnitude p d≤negativePart d := by
  cases p
  · exact negativePart_nonneg d
  · exact le_max_left _ _

theorem primary_charged_nonneg {d A B : ℝ} (hd : d≤0) (hsmall : |d|≤frameCap)
    (hA : (447/800:ℝ)≤A) (hB : B≤283/200) :
    0≤primaryGain d A B+charge*d := by
  have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr hd,(neg_le_abs d).trans hsmall⟩
  have hh := primaryGain_lower hs hA hB
  simp only [neg_neg,charge] at hh ⊢
  linarith

theorem td_charged_nonneg {d : ℝ} {T : SignedPoint} (hd : d≤0) (hsmall : |d|≤frameCap)
    (hT : T.Sorted) (hcore : T.AvoidsCore) : 0≤tdGain d T+charge*d := by
  have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr hd,(neg_le_abs d).trans hsmall⟩
  have hh := tdGain_lower hs hT hcore
  simp only [neg_neg,charge] at hh ⊢
  linarith

theorem e_charged_lower (p : Bool) {d A : ℝ} (hd : p=true → d≤0)
    (hsmall : |d|≤frameCap) (hA : A≤283/200) :
    g (magnitude p d)-charge*magnitude p d≤ if p then eGain d A+charge*d else 0 := by
  cases hp : p
  · simp [magnitude]
  · have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr (hd hp),(neg_le_abs d).trans hsmall⟩
    have hh := eGain_lower hs hA
    simp only [neg_neg] at hh
    simpa [magnitude,sub_eq_add_neg,mul_neg] using add_le_add_right hh (charge*d)

theorem gains_reserve {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hga : ga=true → delta C.theta G≤0) (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) (hde : de=true → delta C.theta D≤0)
    (heh : eh=true → delta C.theta E≤0) : -baseline<gains ga ab td de eh C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hA := SignedPoint.coordinate_bounds (hs A) (hcore A) (hc A) hq
  have hG := SignedPoint.coordinate_bounds (hs G) (hcore G) (hc G) hq
  have hB := SignedPoint.coordinate_bounds (hs B) (hcore B) (hc B) hq
  have hD := SignedPoint.coordinate_bounds (hs D) (hcore D) (hc D) hq
  have hH := SignedPoint.coordinate_bounds (hs H) (hcore H) (hc H) hq
  have hBy : -(C.point B).y≤283/200 := by linarith [neg_le_abs (C.point B).y,hB.2.2]
  have hgainG : 0≤ if ga then primaryGain (delta C.theta G) (C.point A).a (C.point G).a+
      charge*delta C.theta G else 0 := by
    cases hp : ga
    · simp
    · exact primary_charged_nonneg (hga hp) (hsmall G) hA.1.le hG.2.1.le
  have hgainA : 0≤ if ab then primaryGain (delta C.theta A) (C.point A).a (-(C.point B).y)+
      charge*delta C.theta A else 0 := by
    cases hp : ab
    · simp
    · exact primary_charged_nonneg (hab hp) (hsmall A) hA.1.le hBy
  have hgainT : 0≤ if td then tdGain (delta C.theta T) (C.point T)+charge*delta C.theta T else 0 := by
    cases hp : td
    · simp
    · exact td_charged_nonneg (htd hp) (hsmall T) (hs T) (hcore T)
  have hgainD := e_charged_lower de hde (hsmall D) hD.2.1.le
  have hgainH := e_charged_lower eh heh (hsmall E) hH.2.1.le
  have hnD := magnitude_nonneg de hde
  have hnH := magnitude_nonneg eh heh
  have hsum : magnitude de (delta C.theta D)+magnitude eh (delta C.theta E)≤frameCap := by
    have hh := (original_pair_budgets (i:=D) (j:=E) hvar hn (by norm_num [D,E])).2
    exact (add_le_add (magnitude_le_negativePart de _) (magnitude_le_negativePart eh _)).trans hh
  have hcombine := gain_pair hnD hnH hsum
  have hfinal := baseline_gain_positive ⟨add_nonneg hnD hnH,hsum⟩
  dsimp [gains]
  linarith

theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (_hEy : (C.point E).y∈Icc (-(1/2:ℝ)) 0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2)) (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2)) (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true → delta C.theta G≤0) (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) (hde : de=true → delta C.theta D≤0)
    (heh : eh=true → delta C.theta E≤0) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab td de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hupper := stress_nonpos hsmall hf
  have hbase := reference_reserve hg ga ab td de eh hs hc hq hHy hGy hBy hDy hvar
  have hgain := gains_reserve ga ab td de eh hs hc hcore hq hvar hga hab htd hde heh
  have hid := decomposition hg ga ab td de eh C hflat
    (NegativePrimary.cos_pos (hsmall G)).ne' (NegativePrimary.cos_pos (hsmall A)).ne'
    (NegativePrimary.cos_pos (hsmall D)).ne' (NegativePrimary.cos_pos (hsmall E)).ne'
  rw [hid] at hupper
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
