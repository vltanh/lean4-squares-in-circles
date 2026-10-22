module

public import SquaresInCircles.Eight.TableFree.GlobalGAMixedNegativeACapSlopes

/-!
# The two unchanged-neighbor mixed A transports

Uncompiled transcription of Sections 4--5. Negative GA uses precisely
max(b,Lplus), while negative AB uses precisely min(b,Uplus). The whole
motion stays on the true flat core and inside the original containing
circle. At the terminal aligned edge the secondary owner is an exact
projection identity, not a selected virtual inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.MixedNegativeA
open Candidate Secondary

def tangentGA (B b p τ : ℝ) : ℝ := max b (Lplus B (p-τ))
def tangentAB (P b p τ : ℝ) : ℝ := min b (Uplus P (p-τ))

theorem positive_AB_large_neighbor {B b p : ℝ}
    (hb : b∈Ioo 0 (39/250:ℝ)) (hp : p∈Icc 0 (1/4:ℝ))
    (hAB : Lplus B p≤b) : (4/5:ℝ)<B := by
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans (by norm_num [cut])⟩
  have hc := cosine_positive hp'
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=p)
  have hp2 := pow_le_pow_left₀ hp.1 hp.2 2
  have hcoslo : (31/32:ℝ)≤Real.cos p := by nlinarith
  have hs : Real.sin p≤(1/4:ℝ) := (Real.sin_le_self hp.1).trans hp.2
  have hprod := mul_le_mul
    (show (43/125:ℝ)≤1/2-b by linarith [hb.2]) hcoslo
    (by norm_num : (0:ℝ)≤31/32) (by linarith [hb.2] : 0≤1/2-b)
  have hcap := hAB
  unfold Lplus cap at hcap
  rw [add_le_iff_le_sub,div_le_iff₀ hc] at hcap
  dsimp [k0] at hcap
  nlinarith only [hcap,hprod,hs]

theorem GA_motion {P B b n p τ : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hb : b∈Ioo 0 (39/250:ℝ)) (hn : n∈Ioo 0 (1/4:ℝ))
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : b≤Uminus P n) (hAB : Lplus B p≤b) :
    tangentGA B b p τ∈Ioo 0 (1/5:ℝ) ∧
    tangentGA B b p τ≤Uminus P (n-τ) ∧
    Lplus B (p-τ)≤tangentGA B b p τ := by
  have hn' : n∈Icc 0 cut := ⟨hn.1.le,hn.2.le.trans (by norm_num [cut])⟩
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans hn'.2⟩
  have hangles := motion_angles hn' hp hτ
  have hlarge := positive_AB_large_neighbor hb ⟨hp.1,hp.2.trans hn.2.le⟩ hAB
  have hU := Uminus_antitone hP hangles.1 hn' (by linarith [hτ.1])
  have hgap := gap_growth true hP hB hn' hp hτ
  have hgap0 : 0≤gap true P B n p 0 := by
    simp only [gap,if_true,sub_zero]
    linarith
  have hroom : Lplus B (p-τ)≤Uminus P (n-τ) := by
    dsimp [gap] at hgap hgap0
    linarith [hτ.1]
  have hL := Lplus_antitone (B:=B) (by linarith)
    (show (0:ℝ)∈Icc 0 cut by norm_num [cut]) hangles.2 hangles.2.1
  rw [Lplus_zero] at hL
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · exact hb.1.trans_le (le_max_left _ _)
  · exact max_lt (by linarith [hb.2]) (by linarith)
  · exact max_le (hGA.trans hU) hroom
  · exact le_max_right _ _

theorem AB_motion {P B b n p τ : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hb : b∈Ioo 0 (1/2:ℝ)) (hn : n∈Icc 0 cut)
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : b≤Uplus P p) (hAB : Lminus B n≤b) :
    tangentAB P b p τ∈Ioo (1/10:ℝ) (1/2:ℝ) ∧
    tangentAB P b p τ≤Uplus P (p-τ) ∧
    Lminus B (n-τ)≤tangentAB P b p τ := by
  have hangles := motion_angles hn hp hτ
  have hL := Lminus_monotone hB hangles.1 hn (by linarith [hτ.1])
  have hgap := gap_growth false hP hB hn hp hτ
  have hgap0 : 0≤gap false P B n p 0 := by
    simp only [gap,if_false,sub_zero]
    linarith
  have hroom : Lminus B (n-τ)≤Uplus P (p-τ) := by
    dsimp [gap] at hgap hgap0
    linarith [hτ.1]
  have hlow' : Lminus B (n-τ)≤tangentAB P b p τ :=
    le_min (hL.trans hAB) hroom
  exact ⟨⟨(Lminus_lower hB hangles.1).trans_le hlow',
    (min_le_left _ _).trans_lt hb.2⟩,min_le_right _ _,hlow'⟩

theorem GA_initial {B b p : ℝ} (hAB : Lplus B p≤b) : tangentGA B b p 0=b := by
  simp only [tangentGA,sub_zero,max_eq_left hAB]

theorem AB_initial {P b p : ℝ} (hGA : b≤Uplus P p) : tangentAB P b p 0=b := by
  simp only [tangentAB,sub_zero,min_eq_left hGA]

theorem GA_original_motion {Q b n p τ : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (39/250:ℝ)) (hn : n∈Ioo 0 (1/4:ℝ))
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : quarterFeasible G (flat b) (-n) 3)
    (hAB : zeroFeasible (flat b) B p 2) :
    let b' := tangentGA (-B.y) b p τ
    (flat b').Sorted ∧ (flat b').Core ∧ (flat b').AvoidsCore ∧
      (flat b').Contained Q ∧ b'∈Ioo 0 (1/5:ℝ) ∧
      quarterFeasible G (flat b') (-(n-τ)) 3 ∧ zeroFeasible (flat b') B (p-τ) 2 := by
  have hn' : n∈Icc 0 cut := ⟨hn.1.le,hn.2.le.trans (by norm_num [cut])⟩
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans hn'.2⟩
  have hh := GA_motion hG hB hb hn hp hτ
    ((GA_negative_iff G b hn').1 hGA) ((AB_positive_iff B b hp').1 hAB)
  have hgeom := flat_geometry (show tangentGA (-B.y) b p τ∈Ioo 0 (1/2:ℝ) from
    ⟨hh.1.1,by linarith [hh.1.2]⟩)
  have hang := motion_angles hn' hp hτ
  exact ⟨hgeom.1,hgeom.2.1,hgeom.2.2.1,
    (flat_small_circle hh.1).le.trans (by linarith),hh.1,
    (GA_negative_iff G _ hang.1).2 hh.2.1,(AB_positive_iff B _ hang.2).2 hh.2.2⟩

theorem AB_original_motion {Q b n p τ : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (1/2:ℝ)) (hn : n∈Icc 0 cut)
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : quarterFeasible G (flat b) p 3)
    (hAB : zeroFeasible (flat b) B (-n) 2) :
    let b' := tangentAB (G.a-1/2) b p τ
    (flat b').Sorted ∧ (flat b').Core ∧ (flat b').AvoidsCore ∧
      (flat b').Contained Q ∧ b'∈Ioo (1/10:ℝ) (1/2:ℝ) ∧
      quarterFeasible G (flat b') (p-τ) 3 ∧ zeroFeasible (flat b') B (-(n-τ)) 2 := by
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans hn.2⟩
  have hh := AB_motion hG hB hb hn hp hτ
    ((GA_positive_iff G b hp').1 hGA) ((AB_negative_iff B b hn).1 hAB)
  have hgeom := flat_geometry (show tangentAB (G.a-1/2) b p τ∈Ioo 0 (1/2:ℝ) from
    ⟨by linarith [hh.1.1],hh.1.2⟩)
  have hang := motion_angles hn hp hτ
  exact ⟨hgeom.1,hgeom.2.1,hgeom.2.2.1,hgeom.2.2.2.le.trans (by linarith),hh.1,
    (GA_positive_iff G _ hang.2).2 hh.2.1,(AB_negative_iff B _ hang.1).2 hh.2.2⟩

theorem GA_terminal {Q b n p : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (39/250:ℝ)) (hn : n∈Ioo 0 (1/4:ℝ)) (hp : p∈Icc 0 n)
    (hGA : quarterFeasible G (flat b) (-n) 3) (hAB : zeroFeasible (flat b) B p 2) :
    ∃A' : SignedPoint,A'.Sorted ∧ A'.Core ∧ A'.AvoidsCore ∧ A'.Contained Q ∧
      A'.a=7/12 ∧ A'.y∈Ioo 0 (1/5:ℝ) ∧
      quarterFeasible G A' (-(n-p)) 3 ∧ zeroFeasible A' B 0 0 := by
  have hh := GA_original_motion hQ hG hB hb hn hp ⟨hp.1,le_rfl⟩ hGA hAB
  refine ⟨flat (tangentGA (-B.y) b p p),hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,rfl,
    hh.2.2.2.2.1,hh.2.2.2.2.2.1,?_⟩
  have hzero : zeroFeasible (flat (tangentGA (-B.y) b p p)) B 0 2 := by
    simpa only [sub_self] using hh.2.2.2.2.2.2
  simpa [zeroFeasible,zeroProjection] using hzero

theorem AB_terminal {Q b n p : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (1/2:ℝ)) (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n)
    (hGA : quarterFeasible G (flat b) p 3) (hAB : zeroFeasible (flat b) B (-n) 2) :
    ∃A' : SignedPoint,A'.Sorted ∧ A'.Core ∧ A'.AvoidsCore ∧ A'.Contained Q ∧
      A'.a=7/12 ∧ A'.y∈Ioo (1/10:ℝ) (1/2:ℝ) ∧
      quarterFeasible G A' 0 2 ∧ zeroFeasible A' B (-(n-p)) 2 := by
  have hh := AB_original_motion hQ hG hB hb hn hp ⟨hp.1,le_rfl⟩ hGA hAB
  refine ⟨flat (tangentAB (G.a-1/2) b p p),hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,rfl,
    hh.2.2.2.2.1,?_,hh.2.2.2.2.2.2⟩
  have hzero : quarterFeasible G (flat (tangentAB (G.a-1/2) b p p)) 0 3 := by
    simpa only [sub_self] using hh.2.2.2.2.2.1
  simpa [quarterFeasible,quarterProjection] using hzero

end SquaresInCircles.Eight.TableFree.GlobalGA.MixedNegativeA
