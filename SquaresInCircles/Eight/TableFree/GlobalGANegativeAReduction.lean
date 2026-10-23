module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABothMotion

/-!
# Every selected A total reduces by the written original-neighbor moves

Uncompiled transcription of Section 7 of
`HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md`.
Original same-state secondary witnesses are tried first. If both
primaries remain, the two mixed motions or the both-negative G5 motion
apply. The new A frame is an old endpoint; every other vertex is fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeANormalForm
open Candidate Secondary MixedNegativeA

theorem reduce {Q θG θA θB : ℝ} {G A B : SignedPoint} (ga ab : Bool)
    (hQlo : (5/2:ℝ)≤Q) (hQ : Q≤qCap)
    (hGs : G.Sorted) (hGc : G.Contained Q) (hGcore : G.AvoidsCore) (hGy : G.y≤0)
    (hAs : A.Sorted) (hAc : A.Contained Q) (hAcore : A.AvoidsCore)
    (hAr : A.Boundary Q) (hAy : A.y<1/2) (hAouter : A.y≤0 → A.Outer Q)
    (hBs : B.Sorted) (hBc : B.Contained Q) (hBcore : B.AvoidsCore)
    (hBo : B.Outer Q) (hBy : B.y≤0)
    (hu : |θA-θG|≤frameCap) (hv : |θB-θA|≤frameCap) (hspan : |θG-θB|≤frameCap)
    (hGA : quarterFeasible G A (θA-θG) (if ga then 3 else 2))
    (hAB : zeroFeasible A B (θB-θA) (if ab then 2 else 0)) :
    Nonempty (Result Q G A B θG θA θB) := by
  by_cases hnonneg : 0≤total ga ab (θA-θG) (θB-θA)
  · exact ⟨unchanged ga ab hAs hAc hAcore hAr hAy hGA hAB (Or.inl hnonneg)⟩
  by_cases hsingle : ga=false ∨ ab=false
  · exact single ga ab hsingle hGs hGc hGy hAs hAc hAcore hAr hAy hAouter
      hBs hBo hBy hQ hu hv hGA hAB
  have hga : ga=true := by cases ga <;> simp_all
  have hab : ab=true := by cases ab <;> simp_all
  subst ga
  subst ab
  have hsum : (θA-θG)+(θB-θA)<0 := by
    simpa only [total,PairedE.selected,if_true] using lt_of_not_ge hnonneg
  by_cases hsecondaryGA : quarterFeasible G A (θA-θG) 2
  · exact single false true (Or.inl rfl) hGs hGc hGy hAs hAc hAcore hAr hAy hAouter
      hBs hBo hBy hQ hu hv hsecondaryGA hAB
  by_cases hsecondaryAB : zeroFeasible A B (θB-θA) 0
  · exact single true false (Or.inr rfl) hGs hGc hGy hAs hAc hAcore hAr hAy hAouter
      hBs hBo hBy hQ hu hv hGA hsecondaryAB
  have hGb := SignedPoint.coordinate_bounds hGs hGcore hGc hQ
  have hGparameter : G.a-1/2∈Ioo 0 (183/200:ℝ) :=
    ⟨by linarith [hGb.1],by linarith [hGb.2.1]⟩
  have hGupper : G.a<283/200 := hGb.2.1
  have hBb := actual_coordinate_bounds (P:=B.reflect)
    (by simpa using hBs) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hBc) hQ
  have hBtangent : -B.y<9/10 := by
    have hh := hBb.2.1
    dsimp [SignedPoint.reflect] at hh
    linarith [diagonal_bounds.2]
  by_cases huneg : θA<θG
  · have hn : θG-θA∈Ioc 0 frameCap :=
      ⟨by linarith,by rw [sub_eq_neg_sub,←abs_of_neg (sub_neg.mpr huneg)]; exact hu⟩
    have hGAneg : quarterFeasible G A (-(θG-θA)) 3 := by simpa only [neg_sub] using hGA
    have hflat := NegativeA.GA_entry hGs hGc hAs hAr hQ hGy hAouter hn hGAneg
    rcases hflat with hsec|⟨hAa,hApos,hAtiny,hncut⟩
    · exact (hsecondaryGA (by simpa only [neg_sub] using hsec)).elim
    by_cases hvpos : θA≤θB
    · have hAeq : A=flat A.y := by
        cases A
        simp only [flat,SignedPoint.mk.injEq] at ⊢
        exact ⟨hAa,rfl⟩
      have hn' : θG-θA∈Ioo 0 (1/4:ℝ) := ⟨hn.1,hncut⟩
      have hp : θB-θA∈Icc 0 (θG-θA) := ⟨by linarith,by linarith⟩
      obtain ⟨A',hAs',hAr',hAcore',hAc',hAa',hAy',hGA',hAB'⟩ :=
        GA_terminal hQlo hGparameter hBtangent ⟨hApos,hAtiny⟩ hn' hp
          (by simpa only [hAeq,neg_sub] using hGA)
          (by simpa only [hAeq] using hAB)
      have hGA'' : quarterFeasible G A' (θB-θG) 3 := by
        convert hGA' using 1
        congr 1
        ring
      exact ⟨{
        point := A'
        theta := θB
        ga := true
        ab := false
        sorted := hAs'
        contained := hAc'
        core := hAcore'
        radial := Or.inr hAr'
        tangent_upper := by linarith [hAy'.2]
        frame := Or.inr (Or.inr rfl)
        GA := hGA''
        AB := by simpa only [sub_self] using hAB'
        reduced := Or.inr (Or.inl ⟨rfl,rfl,hAa',
          ⟨hAy'.1,by linarith [hAy'.2]⟩,
          ⟨by linarith [hncut,hvpos],by linarith⟩⟩) }⟩
    · exact both_negative hQ hGs hGc hGcore hGy hGupper
        hAs hAc hAcore hAa hApos hBs hBc hBcore hBo hBy huneg
        (lt_of_not_ge hvpos) hspan hGA hAB
  · have hupos : θG≤θA := le_of_not_gt huneg
    have hvneg : θB<θA := by linarith
    have hn : θA-θB∈Ioc 0 frameCap :=
      ⟨by linarith,by rw [sub_eq_neg_sub,←abs_of_neg (sub_neg.mpr hvneg)]; exact hv⟩
    have hABneg : zeroFeasible A B (-(θA-θB)) 2 := by simpa only [neg_sub] using hAB
    rcases NegativeA.AB_entry hAs hAr hBs hBo hQ hAy hBy hn hABneg with hsec|⟨hAa,hApos,hAupper,hncut⟩
    · exact (hsecondaryAB (by simpa only [neg_sub] using hsec)).elim
    have hAeq : A=flat A.y := by
      cases A
      simp only [flat,SignedPoint.mk.injEq] at ⊢
      exact ⟨hAa,rfl⟩
    have hn' : θA-θB∈Icc 0 cut := ⟨hn.1.le,hncut.le⟩
    have hp : θA-θG∈Icc 0 (θA-θB) := ⟨by linarith,by linarith⟩
    obtain ⟨A',hAs',hAr',hAcore',hAc',hAa',hAy',hGA',hAB'⟩ :=
      AB_terminal hQlo hGparameter hBtangent ⟨hApos,hAupper⟩ hn' hp
        (by simpa only [hAeq] using hGA)
        (by simpa only [hAeq,neg_sub] using hAB)
    have hAB'' : zeroFeasible A' B (θB-θG) 2 := by
      convert hAB' using 1
      congr 1
      ring
    exact ⟨{
      point := A'
      theta := θG
      ga := false
      ab := true
      sorted := hAs'
      contained := hAc'
      core := hAcore'
      radial := Or.inr hAr'
      tangent_upper := hAy'.2
      frame := Or.inr (Or.inl rfl)
      GA := by simpa only [sub_self] using hGA'
      AB := hAB''
      reduced := Or.inr (Or.inr ⟨rfl,rfl,hAa',
        ⟨by linarith [hAy'.1],hAy'.2⟩,
        ⟨by linarith [hncut,hupos],by linarith⟩⟩) }⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeANormalForm
