module

public import SquaresInCircles.Eight.Owners.GA.Mixed.NegativeAMotion
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3FarLowScalar

/-!
# Eight squares: the normalization of A on a signed cycle

`cycle_reduce` changes only the point and the frame of A (`replace`). The five edge inequalities
away from A, all other points and all other frames are unchanged (`CycleResult`). The positive and
the negative variation do not increase when A takes the frame of G or of B
(`variation_nonincreasing`). The moved cycle satisfies the necessary conditions but need not be a
packing; no marker or order theorem is applied to it.
-/

section
/-!
## Every selected A total reduces by moves of A to a neighboring frame

`reduce` first tries the secondary witnesses at the same state. If both primaries remain, the two
mixed motions or the both-negative motion G5 apply. The new frame of A is one of the frames of A,
G and B before the move; every other square is fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
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
  change quarterFeasible G A (θA-θG) 3 at hGA
  change zeroFeasible A B (θB-θA) 2 at hAB
  have hsum : (θA-θG)+(θB-θA)<0 := by
    simpa only [total,PairedE.selected,ite_true] using lt_of_not_ge hnonneg
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
      ⟨by linarith,by linarith [neg_abs_le (θA-θG)]⟩
    have hGAneg : quarterFeasible G A (-(θG-θA)) 3 := by rw [neg_sub]; exact hGA
    have hflat := NegativeA.GA_entry hGs hGc hAs hAr hQ hGy hAouter hn hGAneg
    rcases hflat with hsec|⟨hAa,hApos,hAtiny,hncut⟩
    · exact (hsecondaryGA (by simpa only [neg_sub] using hsec)).elim
    by_cases hvpos : θA≤θB
    · have hAeq : A=flat A.y := SignedPoint.ext hAa rfl
      have hn' : θG-θA∈Ioo 0 (1/4:ℝ) := ⟨hn.1,hncut⟩
      have hp : θB-θA∈Icc 0 (θG-θA) := ⟨by linarith,by linarith⟩
      obtain ⟨A',hAs',hAr',hAcore',hAc',hAa',hAy',hGA',hAB'⟩ :=
        GA_terminal hQlo hGparameter hBtangent ⟨hApos,hAtiny⟩ hn' hp
          (by rw [← hAeq,neg_sub]; exact hGA)
          (by rw [← hAeq]; exact hAB)
      have hGA'' : quarterFeasible G A' (θB-θG) 3 := by
        rw [show θB-θG=-(θG-θA-(θB-θA)) by ring]
        exact hGA'
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
        AB := by rw [sub_self]; exact hAB'
        reduced := Or.inr (Or.inl ⟨rfl,rfl,hAa',
          ⟨hAy'.1,by linarith [hAy'.2]⟩,
          ⟨by linarith [hncut,hvpos],by linarith⟩⟩) }⟩
    · exact both_negative hQ hGs hGc hGcore hGy hGupper
        hAs hAc hAcore hAa hApos hBs hBc hBcore hBo hBy huneg
        (lt_of_not_ge hvpos) hspan hGA hAB
  · have hupos : θG≤θA := le_of_not_gt huneg
    have hvneg : θB<θA := by linarith
    have hn : θA-θB∈Ioc 0 frameCap :=
      ⟨by linarith,by linarith [neg_abs_le (θB-θA)]⟩
    have hABneg : zeroFeasible A B (-(θA-θB)) 2 := by rw [neg_sub]; exact hAB
    rcases NegativeA.AB_entry hAs hAr hBs hBo hQ hAy hBy hn hABneg with hsec|⟨hAa,hApos,hAupper,hncut⟩
    · exact (hsecondaryAB (by simpa only [neg_sub] using hsec)).elim
    have hAeq : A=flat A.y := SignedPoint.ext hAa rfl
    have hn' : θA-θB∈Icc 0 cut := ⟨hn.1.le,hncut.le⟩
    have hp : θA-θG∈Icc 0 (θA-θB) := ⟨by linarith,by linarith⟩
    obtain ⟨A',hAs',hAr',hAcore',hAc',hAa',hAy',hGA',hAB'⟩ :=
      AB_terminal hQlo hGparameter hBtangent ⟨hApos,hAupper⟩ hn' hp
        (by rw [← hAeq]; exact hGA)
        (by rw [← hAeq,neg_sub]; exact hAB)
    have hAB'' : zeroFeasible A' B (θB-θG) 2 := by
      rw [show θB-θG=-(θA-θB-(θA-θG)) by ring]
      exact hAB'
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
      GA := by rw [sub_self]; exact hGA'
      AB := hAB''
      reduced := Or.inr (Or.inr ⟨rfl,rfl,hAa',
        ⟨by linarith [hAy'.1],hAy'.2⟩,
        ⟨by linarith [hncut,hupos],by linarith⟩⟩) }⟩


end SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
open Candidate Secondary

def replace (C : SignedCycle) (P : SignedPoint) (t : ℝ) : SignedCycle :=
  { C with point := Function.update C.point A P, theta := Function.update C.theta A t }

@[simp] theorem replace_point_A (C : SignedCycle) (P : SignedPoint) (t : ℝ) :
    (replace C P t).point A=P := by simp [replace]

@[simp] theorem replace_theta_A (C : SignedCycle) (P : SignedPoint) (t : ℝ) :
    (replace C P t).theta A=t := by simp [replace]

theorem replace_point_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠A) : (replace C P t).point i=C.point i := by simp [replace,hi]

theorem replace_theta_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠A) : (replace C P t).theta i=C.theta i := by simp [replace,hi]

theorem replace_delta_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠G ∧ i≠A) : delta (replace C P t).theta i=delta C.theta i := by
  fin_cases i <;> simp [replace,delta,next,G,A] at hi ⊢

theorem replace_edge_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠G ∧ i≠A) (j : Fin 4) :
    (replace C P t).edge i j=C.edge i j := by
  fin_cases i <;> simp [SignedCycle.edge,replace,delta,next,G,A] at hi ⊢

theorem replace_feasible_other (C : SignedCycle) (P : SignedPoint) (t : ℝ)
    {i : Vertex} (hi : i≠G ∧ i≠A) (j : Fin 4) :
    (replace C P t).Feasible i j ↔ C.Feasible i j := by
  simp only [SignedCycle.Feasible,SignedCycle.slack,replace_edge_other C P t hi j,
    replace_delta_other C P t hi]

theorem replace_GA (C : SignedCycle) (P : SignedPoint) (t : ℝ) (j : Fin 4) :
    (replace C P t).Feasible G j ↔ quarterFeasible (C.point G) P (t-C.theta G) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,replace,
    quarterFeasible,word,delta,next,G,A,sub_nonneg]

theorem replace_AB (C : SignedCycle) (P : SignedPoint) (t : ℝ) (j : Fin 4) :
    (replace C P t).Feasible A j ↔ zeroFeasible P (C.point B) (C.theta B-t) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,replace,
    zeroFeasible,word,delta,next,A,B,sub_nonneg]

theorem positivePart_add (u v : ℝ) : positivePart (u+v)≤positivePart u+positivePart v := by
  unfold positivePart
  apply max_le
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem variation_identity (C : SignedCycle) (P : SignedPoint) (t : ℝ) :
    positiveVariation (replace C P t).theta+positivePart (delta C.theta G)+positivePart (delta C.theta A)=
      positiveVariation C.theta+positivePart (t-C.theta G)+positivePart (C.theta B-t) := by
  have h0 : (replace C P t).theta 0=C.theta 0 := replace_theta_other C P t (by decide)
  have h1 : (replace C P t).theta 1=C.theta 1 := replace_theta_other C P t (by decide)
  have h2 : (replace C P t).theta 2=t := replace_theta_A C P t
  have h3 : (replace C P t).theta 3=C.theta 3 := replace_theta_other C P t (by decide)
  have h4 : (replace C P t).theta 4=C.theta 4 := replace_theta_other C P t (by decide)
  have h5 : (replace C P t).theta 5=C.theta 5 := replace_theta_other C P t (by decide)
  have h6 : (replace C P t).theta 6=C.theta 6 := replace_theta_other C P t (by decide)
  simp only [positiveVariation,Fin.sum_univ_seven,delta,next,G,A,B,Fin.reduceAdd,
    h0,h1,h2,h3,h4,h5,h6]
  ring

theorem variation_nonincreasing (C : SignedCycle) (P : SignedPoint) {t : ℝ}
    (ht : t=C.theta A ∨ t=C.theta G ∨ t=C.theta B) :
    positiveVariation (replace C P t).theta≤positiveVariation C.theta := by
  have hid := variation_identity C P t
  have hδG : delta C.theta G=C.theta A-C.theta G := rfl
  have hδA : delta C.theta A=C.theta B-C.theta A := rfl
  rw [hδG,hδA] at hid
  have htriangle := positivePart_add (C.theta A-C.theta G) (C.theta B-C.theta A)
  have he : (C.theta A-C.theta G)+(C.theta B-C.theta A)=C.theta B-C.theta G := by ring
  rw [he] at htriangle
  rcases ht with rfl|rfl|rfl
  · linarith
  · simp only [sub_self,positivePart_zero,add_zero] at hid
    linarith
  · simp only [sub_self,positivePart_zero,add_zero] at hid
    linarith

theorem spread_preserved {C : SignedCycle} (P : SignedPoint) {t : ℝ}
    (hs : C.Spread) (ht : t=C.theta A ∨ t=C.theta G ∨ t=C.theta B) :
    (replace C P t).Spread := by
  intro i j
  rcases ht with ht|ht|ht
  · by_cases hi : i=A <;> by_cases hj : j=A <;>
      simpa [replace,ht,hi,hj] using
        hs (if i=A then A else i) (if j=A then A else j)
  · by_cases hi : i=A <;> by_cases hj : j=A <;>
      simpa [replace,ht,hi,hj] using
        hs (if i=A then G else i) (if j=A then G else j)
  · by_cases hi : i=A <;> by_cases hj : j=A <;>
      simpa [replace,ht,hi,hj] using
        hs (if i=A then B else i) (if j=A then B else j)

structure CycleResult (Q : ℝ) (C : SignedCycle) where
  cycle : SignedCycle
  ga : Bool
  ab : Bool
  necessary : cycle.Necessary Q
  radial : ∀i,(cycle.point i).Boundary Q
  tangent_upper : (cycle.point A).y<1/2
  point_other : ∀i,i≠A → cycle.point i=C.point i
  theta_other : ∀i,i≠A → cycle.theta i=C.theta i
  theta_A : cycle.theta A=C.theta A ∨ cycle.theta A=C.theta G ∨ cycle.theta A=C.theta B
  other_edges : ∀i,i≠G ∧ i≠A → ∀j,cycle.Feasible i j ↔ C.Feasible i j
  variation : positiveVariation cycle.theta≤positiveVariation C.theta
  GA : cycle.Feasible G (if ga then 3 else 2)
  AB : cycle.Feasible A (if ab then 2 else 0)
  reduced : Reduced (cycle.point A) ga ab (delta cycle.theta G) (delta cycle.theta A)

def Result.toCycle {Q : ℝ} {C : SignedCycle}
    (R : Result Q (C.point G) (C.point A) (C.point B) (C.theta G) (C.theta A) (C.theta B))
    (hn : C.Necessary Q) (hr : ∀i,(C.point i).Boundary Q) : CycleResult Q C where
  cycle := replace C R.point R.theta
  ga := R.ga
  ab := R.ab
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=A
      · subst i
        simpa using R.sorted
      · simpa [replace,hi] using hn.sorted i
    contained := by
      intro i
      by_cases hi : i=A
      · subst i
        simpa using R.contained
      · simpa [replace,hi] using hn.contained i
    core := by
      intro i
      by_cases hi : i=A
      · subst i
        simpa using R.core
      · simpa [replace,hi] using hn.core i
    spread := spread_preserved R.point hn.spread R.frame }
  radial := by
    intro i
    by_cases hi : i=A
    · subst i
      simpa using R.radial
    · simpa [replace,hi] using hr i
  tangent_upper := by simpa using R.tangent_upper
  point_other := fun i hi => replace_point_other C R.point R.theta hi
  theta_other := fun i hi => replace_theta_other C R.point R.theta hi
  theta_A := by simpa using R.frame
  other_edges := fun i hi j => replace_feasible_other C R.point R.theta hi j
  variation := variation_nonincreasing C R.point R.frame
  GA := (replace_GA C R.point R.theta _).2 R.GA
  AB := (replace_AB C R.point R.theta _).2 R.AB
  reduced := by
    simpa [replace,delta,next,G,A,B] using R.reduced

theorem cycle_reduce {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hQlo : (5/2:ℝ)≤Q) (hQ : Q≤qCap)
    (hn : C.Necessary Q) (hr : ∀i,(C.point i).Boundary Q)
    (hGy : (C.point G).y≤0) (hBo : (C.point B).Outer Q) (hBy : (C.point B).y≤0)
    (hAy : (C.point A).y<1/2) (hAouter : (C.point A).y≤0 → (C.point A).Outer Q)
    (hs : C.StrictSpread)
    (hGA : C.Feasible G (if ga then 3 else 2)) (hAB : C.Feasible A (if ab then 2 else 0)) :
    Nonempty (CycleResult Q C) := by
  have hGA' : quarterFeasible (C.point G) (C.point A) (C.theta A-C.theta G) (if ga then 3 else 2) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,G,A,sub_nonneg,quarterFeasible] using hGA
  have hAB' : zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) (if ab then 2 else 0) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,A,B,sub_nonneg,zeroFeasible] using hAB
  obtain ⟨R⟩ := reduce ga ab hQlo hQ (hn.sorted G) (hn.contained G) (hn.core G) hGy
    (hn.sorted A) (hn.contained A) (hn.core A) (hr A) hAy hAouter
    (hn.sorted B) (hn.contained B) (hn.core B) hBo hBy (hs A G).le (hs B A).le (hs G B).le hGA' hAB'
  exact ⟨R.toCycle hn hr⟩

end SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
end
end
end
