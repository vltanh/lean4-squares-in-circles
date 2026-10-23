module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveQuarterSplit

/-!
# Far-low intrinsic reserves at every original A/TD split

Uncompiled endpoint join for the far-low companion. The coefficients
are fixed at theta, and the actual split ranges over [0,theta]. Full D
support differs from the existing split model by a constant only. The
positive B alternative retains its moving m coefficient in the concave
function; the remaining four alternatives have fixed increments.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def base (θ a : ℝ) : ℝ := Explicit.baseline .far .low a (θ-a)
def correction (θ : ℝ) : ℝ :=
  clippedSupport 1 (Explicit.c .far .low θ)-fullSupport 1 (Explicit.c .far .low θ)

theorem base_identity (θ a : ℝ) :
    base θ a=TwoPositive.splitBase (Explicit.k .far .low θ) (Explicit.l .far .low θ)
      (Explicit.c .far .low θ) θ a+correction θ := by
  simp only [base,Explicit.baseline,show a+(θ-a)=θ by ring,
    Explicit.sortedD,Bool.false_eq_true,if_false,TwoPositive.splitBase,PositiveTD.baseline,correction]
  dsimp [Explicit.m,Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.eta,
    NegativeDEPositiveTD.Explicit.sigma,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

theorem coefficients {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) :
    0<Explicit.c .far .low θ ∧ 0<Explicit.l .far .low θ ∧
    Explicit.c .far .low θ≤(3/2)*Explicit.l .far .low θ ∧
    (∀a∈Icc 0 θ,PositiveTD.tilted (Explicit.c .far .low θ) (θ-a)≤
      (3/2)*Explicit.l .far .low θ) := by
  have hr := Explicit.far_low_ranges hθ
  refine ⟨by linarith [hr.2.2.1.1],by linarith [hr.2.1.1],
    by linarith [hr.2.2.1.2,hr.2.1.1],?_⟩
  intro a ha
  have hm := Explicit.far_low_tilted hθ
    (show θ-a∈Icc 0 θ from ⟨by linarith [ha.2],by linarith [ha.1]⟩)
  change Explicit.m .far .low θ (θ-a)≤(3/2)*Explicit.l .far .low θ
  linarith [hm.2.2.2,hr.2.1.1]

theorem base_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) :
    ConcaveOn ℝ (Icc 0 θ) (base θ) := by
  obtain ⟨hc,hl,hcl,hm⟩ := coefficients hθ
  have hh := TwoPositive.QuarterSplit.increment_concave
    (k:=Explicit.k .far .low θ) (s:=0) (g:=0) (e:=0)
    hc hl hcl hθ (by norm_num [frameCap]) (by norm_num) (by norm_num)
    (by linarith [Real.cos_le_one frameCap]) (by simp) hm
  have hb : ConcaveOn ℝ (Icc 0 θ)
      (TwoPositive.splitBase (Explicit.k .far .low θ) (Explicit.l .far .low θ)
        (Explicit.c .far .low θ) θ) := by
    simpa only [TwoPositive.Split.increment_zero,add_zero] using hh
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hb (correction θ))
  intro a _
  exact (base_identity θ a).symm

theorem B_positive_concave {θ d : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hd : d∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => base θ a+
      U R (Explicit.l .far .low θ) (Explicit.m .far .low θ (θ-a)) d) := by
  obtain ⟨hc,hl,hcl,hm⟩ := coefficients hθ
  have hh := TwoPositive.QuarterSplit.increment_concave
    (k:=Explicit.k .far .low θ) (s:=d) (g:=phi d-1) (e:=0)
    hc hl hcl hθ (by rw [abs_of_nonneg hd.1]; exact hd.2)
    (sub_nonneg.mpr (TwoPositive.Split.phi_ge_one hd)) le_rfl
    (by linarith [Real.cos_le_one frameCap]) (by simp) hm
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hh (correction θ))
  intro a ha
  have horder := (Explicit.far_low_tilted hθ
    (show θ-a∈Icc 0 θ from ⟨by linarith [ha.2],by linarith [ha.1]⟩)).2.2.1.le
  rw [TwoPositive.Split.increment_U,base_identity]
  change TwoPositive.splitBase _ _ _ θ a+
      U R (min (Explicit.l .far .low θ) (Explicit.m .far .low θ (θ-a)))
        (max (Explicit.l .far .low θ) (Explicit.m .far .low θ (θ-a))) d+correction θ=_
  rw [min_eq_left horder,max_eq_right horder]
  ring

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (a+z) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht) (NegativeEH.G θ)
  have h0 := Certificate.far_low_equal_positive .atT hθ
  have h1 := Certificate.far_low_equal_positive .atA hθ
  have hh := concave_gt_of_endpoints hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ] using h0)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ] using h1)
  simpa only [base,θ,show a+z-a=z by ring] using hh

theorem positive_H {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      U R (Explicit.k .far .low (a+z)) 1 (1/10-(a+z))-
        NegativeEH.epsilon*(1/10-(a+z)) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (NegativeEH.G (1/10)+U R (Explicit.k .far .low θ) 1 (1/10-θ)-NegativeEH.epsilon*(1/10-θ))
  have hh := concave_gt_of_endpoints hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ,add_assoc,sub_eq_add_neg]
      using Certificate.far_low_positive_H .atT hθ)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ,add_assoc,sub_eq_add_neg]
      using Certificate.far_low_positive_H .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc,sub_eq_add_neg] using hh

theorem positive_B {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      U R (Explicit.l .far .low (a+z)) (Explicit.m .far .low (a+z) z) (1/10-(a+z))-
        NegativeEH.epsilon*(1/10-(a+z)) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hd : 1/10-θ∈Icc 0 frameCap :=
    ⟨by linarith [hθ.2],by norm_num [frameCap]; linarith [hθ.1]⟩
  have hc := TwoPositive.Split.add_constant (B_positive_concave ht hd)
    (NegativeEH.G (1/10)-NegativeEH.epsilon*(1/10-θ))
  have hh := concave_gt_of_endpoints hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitM,Explicit.splitA,Explicit.splitT,θ,
        add_assoc,add_comm,add_left_comm,sub_eq_add_neg]
      using Certificate.far_low_positive_B .atT hθ)
    (by simpa [base,Explicit.splitM,Explicit.splitA,Explicit.splitT,θ,
        add_assoc,add_comm,add_left_comm,sub_eq_add_neg]
      using Certificate.far_low_positive_B .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc,add_comm,add_left_comm,sub_eq_add_neg] using hh

theorem negative_H {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low (a+z)) 1 (a+z-1/10) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (NegativeEH.G (1/10)+V R (Explicit.k .far .low θ) 1 (θ-1/10))
  have hh := concave_gt_of_endpoints hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_H .atT hθ)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_H .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc] using hh

theorem negative_G {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low (a+z)) (Explicit.l .far .low (a+z)) (a+z-1/10) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (NegativeEH.G (1/10)+V R (Explicit.k .far .low θ) (Explicit.l .far .low θ) (θ-1/10))
  have hh := concave_gt_of_endpoints hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_G .atT hθ)
    (by simpa [base,Explicit.splitA,Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_G .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowSplit
