module

public import SquaresInCircles.Eight.Owners.GA.Mixed.NegativeAMotion
public import SquaresInCircles.Eight.Owners.GA.Negative.AEntry
public import SquaresInCircles.Eight.Owners.GA.Paired.ECharge

/-!
# Eight squares: the three terminal A regimes on the original neighbors

The first regime is a nonnegative selected A total. The other two are
the original single negative flat-core primary with its original angle
cut. Same-state secondary re-selection is included before any motion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
open Candidate Secondary MixedNegativeA

def total (ga ab : Bool) (u v : ℝ) : ℝ :=
  PairedE.selected ga u+PairedE.selected ab v

def Reduced (P : SignedPoint) (ga ab : Bool) (u v : ℝ) : Prop :=
  0≤total ga ab u v ∨
  (ga=true ∧ ab=false ∧ P.a=7/12 ∧ P.y∈Ioo 0 (1/2:ℝ) ∧ u∈Ioo (-(1/4:ℝ)) 0) ∨
  (ga=false ∧ ab=true ∧ P.a=7/12 ∧ P.y∈Ioo 0 (1/2:ℝ) ∧ v∈Ioo (-(19/50:ℝ)) 0)

structure Result (Q : ℝ) (G A B : SignedPoint) (θG θA θB : ℝ) where
  point : SignedPoint
  theta : ℝ
  ga : Bool
  ab : Bool
  sorted : point.Sorted
  contained : point.Contained Q
  core : point.AvoidsCore
  radial : point.Boundary Q
  tangent_upper : point.y<1/2
  frame : theta=θA ∨ theta=θG ∨ theta=θB
  GA : quarterFeasible G point (theta-θG) (if ga then 3 else 2)
  AB : zeroFeasible point B (θB-theta) (if ab then 2 else 0)
  reduced : Reduced point ga ab (theta-θG) (θB-theta)

def unchanged {Q θG θA θB : ℝ} {G A B : SignedPoint} (ga ab : Bool)
    (hAs : A.Sorted) (hAc : A.Contained Q) (hAcore : A.AvoidsCore)
    (hAr : A.Boundary Q) (hAy : A.y<1/2)
    (hGA : quarterFeasible G A (θA-θG) (if ga then 3 else 2))
    (hAB : zeroFeasible A B (θB-θA) (if ab then 2 else 0))
    (hred : Reduced A ga ab (θA-θG) (θB-θA)) : Result Q G A B θG θA θB where
  point := A
  theta := θA
  ga := ga
  ab := ab
  sorted := hAs
  contained := hAc
  core := hAcore
  radial := hAr
  tangent_upper := hAy
  frame := Or.inl rfl
  GA := hGA
  AB := hAB
  reduced := hred

theorem single {Q θG θA θB : ℝ} {G A B : SignedPoint} (ga ab : Bool)
    (hsingle : ga=false ∨ ab=false)
    (hGs : G.Sorted) (hGc : G.Contained Q) (hGy : G.y≤0)
    (hAs : A.Sorted) (hAc : A.Contained Q) (hAcore : A.AvoidsCore)
    (hAr : A.Boundary Q) (hAy : A.y<1/2) (hAouter : A.y≤0 → A.Outer Q)
    (hBs : B.Sorted) (hBo : B.Outer Q) (hBy : B.y≤0) (hQ : Q≤qCap)
    (hu : |θA-θG|≤frameCap) (hv : |θB-θA|≤frameCap)
    (hGA : quarterFeasible G A (θA-θG) (if ga then 3 else 2))
    (hAB : zeroFeasible A B (θB-θA) (if ab then 2 else 0)) :
    Nonempty (Result Q G A B θG θA θB) := by
  by_cases hnonneg : 0≤total ga ab (θA-θG) (θB-θA)
  · exact ⟨unchanged ga ab hAs hAc hAcore hAr hAy hGA hAB (Or.inl hnonneg)⟩
  have hneg : total ga ab (θA-θG) (θB-θA)<0 := lt_of_not_ge hnonneg
  cases ga <;> cases ab
  · simp [total,PairedE.selected] at hneg
  · have hvneg : θB-θA<0 := by simpa [total,PairedE.selected] using hneg
    have hs : -(θB-θA)∈Ioc 0 frameCap :=
      ⟨by linarith,(neg_le_abs _).trans hv⟩
    have hprimary : zeroFeasible A B (-(-(θB-θA))) 2 := by simpa using hAB
    rcases NegativeA.AB_entry hAs hAr hBs hBo hQ hAy hBy hs hprimary with hsecondary|hflat
    · exact ⟨unchanged false false hAs hAc hAcore hAr hAy hGA
        (by simpa using hsecondary) (Or.inl (by simp [total,PairedE.selected]))⟩
    · refine ⟨unchanged false true hAs hAc hAcore hAr hAy hGA hAB ?_⟩
      exact Or.inr (Or.inr ⟨rfl,rfl,hflat.1,⟨hflat.2.1,hflat.2.2.1⟩,
        ⟨by linarith [hflat.2.2.2],hvneg⟩⟩)
  · have huneg : θA-θG<0 := by simpa [total,PairedE.selected] using hneg
    have hs : -(θA-θG)∈Ioc 0 frameCap :=
      ⟨by linarith,(neg_le_abs _).trans hu⟩
    have hprimary : quarterFeasible G A (-(-(θA-θG))) 3 := by simpa using hGA
    rcases NegativeA.GA_entry hGs hGc hAs hAr hQ hGy hAouter hs hprimary with hsecondary|hflat
    · exact ⟨unchanged false false hAs hAc hAcore hAr hAy
        (by simpa using hsecondary) hAB (Or.inl (by simp [total,PairedE.selected]))⟩
    · refine ⟨unchanged true false hAs hAc hAcore hAr hAy hGA hAB ?_⟩
      exact Or.inr (Or.inl ⟨rfl,rfl,hflat.1,⟨hflat.2.1,by linarith [hflat.2.2.1]⟩,
        ⟨by linarith [hflat.2.2.2],huneg⟩⟩)
  · simp at hsingle

end SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
