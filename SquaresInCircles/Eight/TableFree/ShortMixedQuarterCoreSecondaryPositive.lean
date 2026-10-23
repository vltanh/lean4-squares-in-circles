module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterCoreSecondaryReferences

/-!
# Every positive outer target on a mixed source-secondary quarter edge

The original weak separator supplies the source sign's precise lower
angle domain. Whole-half concavity and its proved geometric endpoints
then give the corrected original role-label inequality. Uncompiled.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryPositive
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    F r upper x≤coreOuterCost r a b A B (angle upper x) := by
  have hh := fixed_coefficients r hr
  have hb := CoreAngleEndpoint.state_bounds hs
  have hrem := mul_nonneg hh.2.1 hb.2.2.1
  have hsup := outer_circle_lower (X:= -coP r-lambda r*Real.cos x)
    (Y:= -direction upper*lambda r*Real.sin x-coQ r) ht
  have he : Real.sqrt ((-coP r-lambda r*Real.cos x)^2+
      (-direction upper*lambda r*Real.sin x-coQ r)^2)=N r upper x := by
    rw [N,CircularNorm.norm,energy_identity]
    congr 1
    ring
  rw [he] at hsup
  dsimp [sourceSecondary] at hm
  have hmult := mul_le_mul_of_nonneg_left hm hh.1.le
  rw [angle_width upper hx,angle_sin,angle_cos,targetSign_positive hr] at hmult
  dsimp [F,coreOuterCost]
  rw [targetSign_positive hr]
  cases upper <;> dsimp [direction] at * <;> nlinarith

theorem scalar_lower (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10))
    (hcut : upper=false → sourcePositive r=false → x≤cut) : (449/500:ℝ)<F r upper x := by
  have hzero : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  have hcap : (7/10:ℝ)∈Icc 0 (7/10) := by norm_num
  cases upper
  · cases hs : sourcePositive r
    · have hx' : x∈Icc 0 cut := ⟨hx.1,hcut rfl hs⟩
      have h := (concave r hr false).min_le_of_mem_Icc hzero cut_mem hx'
      have hm : (449/500:ℝ)<min (F r false 0) (F r false cut) :=
        lt_min (by linarith [aligned r hr]) (by linarith [lower_cut r hr hs])
      exact hm.trans_le h
    · have h := (concave r hr false).min_le_of_mem_Icc hzero hcap hx
      have hm : (449/500:ℝ)<min (F r false 0) (F r false (7/10)) :=
        lt_min (by linarith [aligned r hr]) (by linarith [lower_cap r hr hs])
      exact hm.trans_le h
  · have he : F r true 0=F r false 0 := by
      simp [F,angle,N,CircularNorm.norm,CircularNorm.energy]
    have h := (concave r hr true).min_le_of_mem_Icc hzero hcap hx
    have hm : (449/500:ℝ)<min (F r true 0) (F r true (7/10)) :=
      lt_min (by linarith [aligned r hr]) (by linarith [upper_cap r hr])
    exact hm.trans_le h

theorem original (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  have hcut : upper=false → sourcePositive r=false → x≤cut := by
    rintro rfl hσ
    exact (original_lower_cut r hr hσ hs ht hx hm).le
  exact (scalar_lower r hr upper hx hcut).trans_le (original_lower r hr upper hs ht hx hm)

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryPositive
