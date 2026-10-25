module

public import SquaresInCircles.Eight.Words.Crossed.WrongEndpointCalculus

/-!
# Eight squares: the crossed wrong-sign endpoint bound

The zero-tangent contact divides the two intrinsic cap alternatives. In the positive cap,
monotonicity of the zero demand gives the lower bound (`positive_cap_reserve`). In the wrong cap,
the two HG-angle endpoints give the same bound after the loss `27/6400`
(`wrong_cap_reserve`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedWrongEndpointBound
open PositiveSmallScalar CrossedSmallWrongScalar CrossedWrongEndpointCalculus
open EndpointRotationPenalty

theorem contact_mem {Z : ℝ} (hZ : Z∈Ioo (39/200 : ℝ) (2/5)) :
    Z∈Icc 0 frameCap := by
  dsimp [frameCap]
  constructor <;> linarith [hZ.1,hZ.2]

theorem positive_cap_reserve {q P Y Z z r : ℝ}
    (S : CrossedSmallWrongScalar.CapData q P Y)
    (hZ : Z∈Ioo (39/200 : ℝ) (2/5)) (hcontact : V P Y Z=1/2)
    (hz : z∈Icc 0 frameCap) (hcap : 1/2≤V P Y z)
    (hr : 0≤r) (hh : r+z≤frameCap) :
    1+7/1000-27/6400≤zeroDemand q (r+z)+charge*r+charge*Z := by
  have hZi := contact_mem hZ
  have hzZ : z≤Z := by
    by_contra! hbad
    have hs := CrossedSmallWrongScalar.V_strictAnti S hZi hz hbad
    rw [hcontact] at hs
    linarith
  have hrmax : r≤7/10 := by dsimp [frameCap] at hh; linarith [hz.1]
  have hlarge : r+Z∈Icc (39/200 : ℝ) (11/10) := by
    constructor <;> linarith [hZ.1,hZ.2]
  have hsmall : r+z∈Icc (0:ℝ) (11/10) := by
    dsimp [frameCap] at hh
    exact ⟨add_nonneg hr hz.1,by linarith⟩
  have hm := zeroDemand_antitone S.floor hsmall
    (show r+Z∈Icc (0:ℝ) (11/10) from ⟨by linarith [hlarge.1],hlarge.2⟩)
    (by linarith : r+z≤r+Z)
  have hf := zeroDemand_reserve S.floor S.ceiling hlarge
  linarith

theorem wrong_cap_reserve {q P Y Z z h : ℝ}
    (S : CrossedSmallWrongScalar.CapData q P Y)
    (hZ : Z∈Ioo (39/200 : ℝ) (2/5)) (hcontact : V P Y Z=1/2)
    (hz : z∈Icc 0 frameCap) (hcap : V P Y z∈Icc (2/5 : ℝ) (1/2))
    (hh : h∈Icc z frameCap) :
    1+7/1000-27/6400≤chargedDemand q P Y z h+charge*Z := by
  have hZi := contact_mem hZ
  have hZz : Z≤z := by
    by_contra! hbad
    have hs := CrossedSmallWrongScalar.V_strictAnti S hz hZi hbad
    rw [hcontact] at hs
    linarith [hcap.2]
  have hmono := CrossedSmallWrongScalar.demand_monotone S (Θ := 0) (l := Z) (r := z)
    le_rfl (by
      intro t ht
      have hi : t∈Icc 0 frameCap := ⟨hZi.1.trans ht.1,ht.2.trans hz.2⟩
      have hlo := CrossedSmallWrongScalar.V_antitone S hi hz ht.2
      have hhi := CrossedSmallWrongScalar.V_antitone S hZi hi ht.1
      simpa only [zero_add] using
        (show 0≤t ∧ t∈Icc 0 frameCap ∧ V P Y t∈Icc (2/5 : ℝ) (1/2) from
          ⟨hi.1,hi,⟨hcap.1.trans hlo,by linarith⟩⟩))
  have hordered := hmono (show Z∈Icc Z z from ⟨le_rfl,hZz⟩)
    (show z∈Icc Z z from ⟨hZz,le_rfl⟩) hZz
  have hzero : SmallWrongScalar.demand q P Y 0 Z=zeroDemand q Z := by
    norm_num [SmallWrongScalar.demand,SmallWrongScalar.W,zeroDemand,hcontact] <;> ring
  have hzeroReserve := zeroDemand_reserve S.floor S.ceiling
    (show Z∈Icc (39/200 : ℝ) (11/10) from ⟨hZ.1.le,by linarith [hZ.2]⟩)
  have hleft : 1+7/1000-27/6400-charge*Z≤SmallWrongScalar.demand q P Y 0 z := by
    rw [hzero] at hordered
    linarith
  have hKloss := K_contact_loss S hZi hz hZz hcontact hcap
  have hKzero : K q P Y Z+charge*Z=zeroDemand q frameCap+charge*frameCap := by
    norm_num [K,chargedDemand,SmallWrongScalar.W,zeroDemand,hcontact] <;> ring
  have hfarReserve := zeroDemand_reserve S.floor S.ceiling
    (show frameCap∈Icc (39/200 : ℝ) (11/10) by norm_num [frameCap])
  have hright : 1+7/1000-27/6400-charge*Z≤K q P Y z := by
    simp only [frameCap] at hKzero hfarReserve
    linarith
  have hfinal := chargedDemand_endpoint_lower S hz hcap hh hleft hright
  linarith

end SquaresInCircles.Eight.CrossedWrongEndpointBound
