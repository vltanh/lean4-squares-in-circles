module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeGeometry

/-!
# The twelve continued endpoint curves

Uncompiled source. Each curve is the original source circle at one of
the two intrinsic core endpoints. The shared polynomial curvature
reserve is applied on the entire early angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Endpoint
open CommonQuarter CorePairGeometry Arithmetic
open SecondWord (MixedCorner)

def AA (diagonal : Bool) : ℝ := if diagonal then CoreAngleEndpoint.diagonal+1/2 else 13/12
def BB (diagonal : Bool) : ℝ := if diagonal then CoreAngleEndpoint.diagonal-1/2 else 0
def bC (diagonal : Bool) : ℝ := if diagonal then CoreAngleEndpoint.diagonal else 1/2
def K (diagonal : Bool) : ℝ := AA diagonal^2+BB diagonal^2
def height (diagonal : Bool) (φ : ℝ) : ℝ := 1+AA diagonal*Real.cos φ-BB diagonal*Real.sin φ
def speed (diagonal : Bool) (φ : ℝ) : ℝ := AA diagonal*Real.sin φ+BB diagonal*Real.cos φ
def H (r : Row) (diagonal : Bool) (φ : ℝ) : ℝ :=
  φ+ocC r+M r (height diagonal φ-1/2)+ocG r*bC diagonal
def Hd (r : Row) (diagonal : Bool) (φ : ℝ) : ℝ :=
  1-M1 r (height diagonal φ-1/2)*speed diagonal φ
def Hdd (r : Row) (diagonal : Bool) (φ : ℝ) : ℝ :=
  M2 r (height diagonal φ-1/2)*(speed diagonal φ)^2-
    M1 r (height diagonal φ-1/2)*(height diagonal φ-1)

theorem endpoint_mem (diagonal : Bool) : bC diagonal∈MixedCorner.domain := by
  cases diagonal <;> dsimp [bC,MixedCorner.domain] <;>
    constructor <;> linarith [CoreAngleEndpoint.diagonal_bounds.1]
theorem height_contact (diagonal : Bool) (φ : ℝ) :
    height diagonal φ=contactPrimary (bC diagonal) φ+1/2 := by
  cases diagonal
  · dsimp [height,AA,BB,bC,contactPrimary]
    rw [MixedCorner.join]
    ring
  · dsimp [height,AA,BB,bC,contactPrimary]
    rw [MixedCorner.diagonal]
    ring
theorem height_range (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    HeightRange (height diagonal φ) := by
  rw [height_contact]
  exact contact_height_range (endpoint_mem diagonal) hφ
theorem height_domain (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    SourceDomain (height diagonal φ-1/2) := height_source_domain (height_range diagonal hφ)
theorem mass_lower (diagonal : Bool) : Curvature.K0<K diagonal := by
  cases diagonal
  · norm_num [Curvature.K0,K,AA,BB]
  · have hs := CoreAngleEndpoint.diagonal_sq
    have hd := CoreAngleEndpoint.diagonal_bounds.1
    dsimp [Curvature.K0,K,AA,BB]
    nlinarith

theorem height_hasDerivAt (diagonal : Bool) (φ : ℝ) :
    HasDerivAt (height diagonal) (-speed diagonal φ) φ := by
  convert (((Real.hasDerivAt_cos φ).const_mul (AA diagonal)).const_add 1).sub
    ((Real.hasDerivAt_sin φ).const_mul (BB diagonal)) using 1 <;>
    dsimp [height,speed] <;> ring
theorem speed_hasDerivAt (diagonal : Bool) (φ : ℝ) :
    HasDerivAt (speed diagonal) (height diagonal φ-1) φ := by
  convert ((Real.hasDerivAt_sin φ).const_mul (AA diagonal)).add
    ((Real.hasDerivAt_cos φ).const_mul (BB diagonal)) using 1 <;>
    dsimp [height,speed] <;> ring
theorem speed_circle (diagonal : Bool) (φ : ℝ) :
    (speed diagonal φ)^2+(height diagonal φ-1)^2=K diagonal := by
  dsimp [speed,height,K]
  linear_combination (AA diagonal^2+BB diagonal^2)*(Real.sin_sq_add_cos_sq φ)
theorem H_hasDerivAt (r : Row) (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    HasDerivAt (H r diagonal) (Hd r diagonal φ) φ := by
  convert (((hasDerivAt_id φ).add_const (ocC r)).add
    ((M_hasDerivAt r (height_domain diagonal hφ)).comp φ
      ((height_hasDerivAt diagonal φ).sub_const (1/2)))).add_const (ocG r*bC diagonal)
    using 1 <;> dsimp [H,Hd] <;> ring
theorem Hd_hasDerivAt (r : Row) (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    HasDerivAt (Hd r diagonal) (Hdd r diagonal φ) φ := by
  convert ((((M1_hasDerivAt r (height_domain diagonal hφ)).comp φ
    ((height_hasDerivAt diagonal φ).sub_const (1/2))).mul
      (speed_hasDerivAt diagonal φ)).const_sub 1) using 1 <;> dsimp [Hd,Hdd] <;> ring

theorem second_identity (r : Row) (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    Hdd r diagonal φ*(v (height diagonal φ))^3=
      ocQ r*(Q0*(K diagonal-(height diagonal φ-1)^2)-
        height diagonal φ*(height diagonal φ-1)*(Q0-(height diagonal φ)^2))-
          ocP r*(height diagonal φ-1)*(v (height diagonal φ))^3 := by
  have hp := source_v_positive (height_domain diagonal hφ)
  have he := source_v_square (height_domain diagonal hφ)
  simp only [sub_add_cancel] at hp he
  have hs : (speed diagonal φ)^2=K diagonal-(height diagonal φ-1)^2 := by
    linarith [speed_circle diagonal φ]
  calc
    _ = ocQ r*Q0*(speed diagonal φ)^2-
        ocP r*(height diagonal φ-1)*(v (height diagonal φ))^3-
          ocQ r*height diagonal φ*(height diagonal φ-1)*(v (height diagonal φ))^2 := by
      dsimp [Hdd,M1,M2]
      simp only [sub_add_cancel]
      field_simp [hp.ne']
      ring
    _ = _ := by rw [hs,he]; ring

theorem curvature (r : Row) (hr : Remaining r) (diagonal : Bool) {φ : ℝ}
    (hφ : φ∈earlyAngles) : (13/20:ℝ)<Hdd r diagonal φ :=
  Curvature.endpoint_second_lower (coefficients r hr).1 (coefficients r hr).2.2.2.2
    (mass_lower diagonal) (height_range diagonal hφ) (second_identity r diagonal hφ)

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Endpoint
