module

public import SquaresInCircles.Eight.TableFree.SoleOriginalBlocks
public import SquaresInCircles.Eight.TableFree.SoleResiduals
public import SquaresInCircles.Eight.TableFree.SoleFixedSplit

/-!
# A fixed-coordinate primary split for the original sole-E stress

Uncompiled source. The four anchor coordinates and all ordinary signed
angles are fixed. Only the positive primary parameters x and t-x vary
in this scalar expression. The high sole-EH expression uses |E.y|, so
its concavity does not require E to have a prescribed sign. Sole-DE
uses the actual axis upper bound M in place of E's work.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleSplitModel
open Candidate SoleECoefficients SoleResiduals SoleOriginalBlocks
open PositiveAngularEnvelope SecondaryEStress

def transverse (C : SignedCycle) : ℝ :=
  edgeWidth (delta C.theta H)-(C.point H).a*Real.sin (delta C.theta H)-
    |(C.point H).y|*Real.cos (delta C.theta H)

def radial (C : SignedCycle) (de : Bool) : ℝ :=
  if de then edgeWidth (delta C.theta E)-(C.point H).a*Real.cos (delta C.theta E)-
    |(C.point H).y|*Real.sin (delta C.theta E)
  else edgeWidth (delta C.theta D)-(C.point D).a*Real.cos (delta C.theta D)-
    |(C.point D).y|*Real.sin (delta C.theta D)

def constant (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t : ℝ) : ℝ :=
  ell b t*(edgeWidth (delta C.theta A)-C.edge A ab)+
    c b t*(edgeWidth (delta C.theta B)-C.edge B 2)+
    c b t*(edgeWidth (delta C.theta T)-C.edge T 0)-k b t*(C.point A).a-
    (if de then (C.point D).a else (C.point H).a)

def eBound (C : SignedCycle) (b : Band) (de : Bool) (R M t e : ℝ) : ℝ :=
  if b=.high then
    if de then M*Real.sin e
    else (C.point E).a*Real.sin e+|(C.point E).y|*(1-Real.cos e)
  else (if de then M else sigma R (eta b t))*Real.sin e

def value (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (R M t x : ℝ) : ℝ :=
  if b=.high then
    SoleFixedSplit.high (constant C ab b de t+radial C de) (transverse C)
      (k b t) (g b t) (sigma R (g b t))
      (if de then M else (C.point E).a) (if de then 0 else |(C.point E).y|) t x
  else
    SoleFixedSplit.tilted (constant C ab b de t) (transverse C) (radial C de)
      (k b t) (g b t) (if de then 7/10 else eta b t)
      (sigma R (g b t)) (if de then M else sigma R (eta b t)) t x

theorem formula {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool)
    (R M : ℝ) {t x : ℝ} (ht : t∈domain b) (hx : x∈Icc 0 t) :
    value C ab b de R M t x=
      constant C ab b de t+n b t x*transverse C+k b t*edgeWidth x-
        k b t*sigma R (g b t)*Real.sin x+
        (if de then r b (t-x) else p b t (t-x))*radial C de+
        edgeWidth (t-x)-eBound C b de R M t (t-x) := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans (angle ht).2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,(angle ht).2]⟩
  cases b <;> cases de <;>
    simp [value,eBound,SoleFixedSplit.tilted_formula,SoleFixedSplit.high_formula,
      n,p,r,tiltedWeight,edgeWidth_positive_formula hx',edgeWidth_positive_formula he] <;> ring

theorem coefficient_ranges {b : Band} {t : ℝ} (ht : t∈domain b) :
    (431/500 : ℝ)≤k b t ∧ g b t∈Icc (1/4 : ℝ) (7/20) ∧
      eta b t∈Icc (1/4 : ℝ) (7/20) := by
  cases b
  · rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    dsimp [g]
    repeat' constructor <;> linarith
  · rcases middle_bounds ht with ⟨hk0,hk1,hc0,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    dsimp [g]
    repeat' constructor <;> linarith
  · rcases high_bounds ht with ⟨hk0,hk1,hc,hl0,hl1,hlk,hcl,hg0,hg1⟩
    dsimp [eta]
    repeat' constructor <;> linarith

theorem residual_bounds {C : SignedCycle} (de : Bool)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    -(13/200 : ℝ)≤transverse C ∧ -(83/200 : ℝ)≤radial C de := by
  refine ⟨(transverse_residual (hs H) (hc H) (ha H)).le,?_⟩
  cases de
  · exact (radial_residual (hs D) (hc D) (ha D)).le
  · exact (radial_residual (hs H) (hc H) (ha E)).le

/-- Concavity is proved before any replacement of the four original
anchor works by independent norm supports. -/
theorem concave {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool) {R M t : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hM : M≤283/200) (ht : t∈domain b)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    ConcaveOn ℝ (Icc 0 t) (value C ab b de R M t) := by
  obtain ⟨hMH,hMX⟩ := residual_bounds de hs hc ha
  obtain ⟨hk,hg,heta⟩ := coefficient_ranges ht
  have hG := (tilt_reserve hR hQU hg).le
  have hEta := (tilt_reserve hR hQU heta).le
  cases b
  · apply SoleFixedSplit.tilted_concave hMH hMX hk
      (by norm_num [g]) (by cases de <;> simp [eta]; nlinarith [heta.1]) hG
    · cases de <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
        linarith [heta.2]
    · exact ⟨ht.1,by linarith [ht.2]⟩
  · apply SoleFixedSplit.tilted_concave hMH hMX hk
      (by norm_num [g]) (by cases de <;> simp; linarith [heta.1]) hG
    · cases de <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
        linarith [heta.2]
    · exact ⟨(angle ht).1,ht.2⟩
  · have hb := high_bounds ht
    apply SoleFixedSplit.high_concave hMH ⟨hb.1,hb.2.1⟩
      ⟨by linarith [hg.1],hb.2.2.2.2.2.2.2.2⟩ hG
    · cases de
      · exact (contained_bounds (hs E) (hc E)).1.le
      · exact hM
    · cases de <;> simp
    · exact angle ht

theorem positive_of_endpoints {C : SignedCycle} {ab : Fin 4} {b : Band} {de : Bool}
    {R M t x : ℝ} (hconc : ConcaveOn ℝ (Icc 0 t) (value C ab b de R M t))
    (hx : x∈Icc 0 t) (h0 : 0<value C ab b de R M t 0)
    (h1 : 0<value C ab b de R M t t) : 0<value C ab b de R M t x := by
  exact (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

end SquaresInCircles.Eight.TableFree.SoleSplitModel
