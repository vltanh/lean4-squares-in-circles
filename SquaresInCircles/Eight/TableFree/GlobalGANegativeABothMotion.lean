module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeANormalForm
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedECharge

/-!
# Both negative A primaries use the written G5 reflection

Uncompiled transcription of Section 6 of the mixed-negative-A note.
The reflected triple is (B*,A*,G*). Original AB2 becomes HG0 and
original GA3 becomes GA1, so the existing flat-core transport applies
literally. Its strict core and containment facts are pulled back before
the aligned secondary owner is selected.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeANormalForm
open Candidate Secondary MixedNegativeA

def Result.rebase {Q θG θA θA' θB : ℝ} {G A A' B : SignedPoint}
    (R : Result Q G A' B θG θA' θB)
    (hframe : θA'=θA ∨ θA'=θG ∨ θA'=θB) : Result Q G A B θG θA θB where
  point := R.point
  theta := R.theta
  ga := R.ga
  ab := R.ab
  sorted := R.sorted
  contained := R.contained
  core := R.core
  radial := R.radial
  tangent_upper := R.tangent_upper
  frame := by
    rcases R.frame with hh|hh|hh
    · rw [hh]
      exact hframe
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  GA := R.GA
  AB := R.AB
  reduced := R.reduced

theorem flat_high_tangent_upper {G A : SignedPoint} {s : ℝ}
    (hG : G.a<283/200) (hflat : A.a=7/12)
    (hs : s∈Icc 0 frameCap) (hGA : quarterFeasible G A (-s) 3) : A.y<1/2 := by
  have ht := transport_trig hs
  have hc : 0≤Real.cos s := by linarith [ht.1]
  have hsum := one_le_abs_cos_add_abs_sin s
  rw [abs_of_nonneg hc,abs_of_nonneg ht.2.2.1] at hsum
  by_contra! hbad
  have hy := mul_le_mul_of_nonneg_right hbad hc
  dsimp [quarterFeasible,quarterProjection] at hGA
  simp only [Matrix.cons_val_succ,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hflat] at hGA
  rw [edgeWidth_negative_formula hs] at hGA
  nlinarith only [hGA,hy,hsum,hG,ht.2.2.1]

theorem both_negative {Q θG θA θB : ℝ} {G A B : SignedPoint}
    (hQ : Q≤qCap)
    (hGs : G.Sorted) (hGc : G.Contained Q) (hGcore : G.AvoidsCore)
    (hGy : G.y≤0) (hGupper : G.a<283/200)
    (hAs : A.Sorted) (hAc : A.Contained Q) (hAcore : A.AvoidsCore)
    (hflat : A.a=7/12) (hAy : 0<A.y)
    (hBs : B.Sorted) (hBc : B.Contained Q) (hBcore : B.AvoidsCore)
    (hBo : B.Outer Q) (hBy : B.y≤0)
    (hu : θA<θG) (hv : θB<θA)
    (hspan : |θG-θB|≤frameCap)
    (hGA : quarterFeasible G A (θA-θG) 3)
    (hAB : zeroFeasible A B (θB-θA) 2) :
    Nonempty (Result Q G A B θG θA θB) := by
  let z : ℝ := θG-θA
  let Θ : ℝ := θG-θB
  have hz : 0<z ∧ z≤7/10 := by
    dsimp [z]
    dsimp [frameCap] at hspan
    exact ⟨by linarith,by linarith [(le_abs_self (θG-θB)).trans hspan]⟩
  have hΘ : |Θ|≤(7/10:ℝ) := by simpa [Θ,frameCap] using hspan
  have hgap : |z-Θ|≤(7/10:ℝ) := by
    apply abs_le.mpr
    have hb := abs_le.mp hΘ
    dsimp [z,Θ] at *
    constructor <;> linarith
  have hHG : zeroFeasible B.reflect A.reflect (z-Θ) 0 := by
    have hh := (zeroFeasible_reflect A B (θB-θA) 2).2 hAB
    convert hh using 1 <;> try rfl
    dsimp [z,Θ]
    ring
  have hGA' : quarterFeasible A.reflect G.reflect (-z) 1 := by
    have hh := (quarterFeasible_reflect G A (θA-θG) 3).2 hGA
    convert hh using 1 <;> try rfl
    dsimp [z]
    ring
  obtain ⟨P,x,hPa,hendpoint,hx,hPs,hPcore,hPavoid,hPcircle,hzero,hquarter,hhard,hstrict,hPy⟩ :=
    flat_core_negative_ga1_hg0_transport hQ
      (by simpa using hBs) (by simpa using hAs) (by simpa using hGs)
      (by simpa using hBc) (by simpa using hAc) (by simpa using hGc)
      (by simpa using hBcore) (by simpa using hAcore) (by simpa using hGcore)
      hflat (by simpa [SignedPoint.reflect] using hAy.le) hz hΘ hgap hHG hGA'
  let A' := P.reflect
  let θ' := θG-x
  have hAs' : A'.Sorted := by simpa [A'] using hPs
  have hAc' : A'.Contained Q := by simpa [A',SignedPoint.Contained] using hPcircle.le
  have hAcore' : A'.AvoidsCore := by simpa [A'] using hPavoid
  have hAr' : A'.Boundary Q := Or.inr (by simpa [A'] using hPcore)
  have hflat' : A'.a=7/12 := by simpa [A',SignedPoint.reflect,hflat] using hPa
  have hAy' : 0<A'.y := by simpa [A',SignedPoint.reflect] using neg_pos.mpr hPy
  have hxdom : x∈Icc 0 frameCap := by
    rcases hendpoint with hh|hh
    · rw [hh]
      norm_num [frameCap]
    · rw [hh]
      dsimp [Θ]
      exact ⟨by linarith,(le_abs_self _).trans hspan⟩
  have hnewGA : quarterFeasible G A' (θ'-θG) 3 := by
    have hh := (quarterFeasible_reflect P G.reflect (-x) 1).2 hquarter
    simpa [θ',A',reflectedOwner] using hh
  have hnewAB : zeroFeasible A' B (θB-θ') 2 := by
    have hh := (zeroFeasible_reflect B.reflect P (x-Θ) 0).2 hzero
    convert hh using 1 <;> try simp [A',reflectedOwner]
    dsimp [θ',Θ]
    ring
  have hAyupper : A'.y<1/2 := by
    apply flat_high_tangent_upper hGupper hflat' hxdom
    simpa [θ'] using hnewGA
  have hframe : θ'=θG ∨ θ'=θB := by
    rcases hendpoint with hh|hh
    · exact Or.inl (by simp [θ',hh])
    · exact Or.inr (by dsimp [θ',Θ] at *; linarith)
  have hu' : |θ'-θG|≤frameCap := by
    rw [show θ'-θG= -x by dsimp [θ']; ring,abs_neg,abs_of_nonneg hxdom.1]
    exact hxdom.2
  have hv' : |θB-θ'|≤frameCap := by
    rcases hframe with hh|hh
    · rw [hh,abs_sub_comm]
      exact hspan
    · rw [hh,sub_self,abs_zero]
      norm_num [frameCap]
  have hAouter' : A'.y≤0 → A'.Outer Q := by intro hh; linarith
  rcases hframe with hleft|hright
  · have hGA2 : quarterFeasible G A' (θ'-θG) 2 := by
      rw [hleft,sub_self] at hnewGA ⊢
      exact (quarter_high_tie G A').2 hnewGA
    obtain ⟨R⟩ := single false true (Or.inl rfl) hGs hGc hGy
      hAs' hAc' hAcore' hAr' hAyupper hAouter' hBs hBo hBy hQ hu' hv' hGA2 hnewAB
    exact ⟨R.rebase (Or.inr (Or.inl hleft))⟩
  · have hAB0 : zeroFeasible A' B (θB-θ') 0 := by
      rw [hright,sub_self] at hnewAB ⊢
      exact (zero_owner_tie A' B).2 hnewAB
    obtain ⟨R⟩ := single true false (Or.inr rfl) hGs hGc hGy
      hAs' hAc' hAcore' hAr' hAyupper hAouter' hBs hBo hBy hQ hu' hv' hnewGA hAB0
    exact ⟨R.rebase (Or.inr (Or.inr hright))⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeANormalForm
