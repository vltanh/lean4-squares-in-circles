module

public import SquaresInCircles.Eight.TableFree.OneNegativeAnchorPenalty
public import SquaresInCircles.Eight.TableFree.DirectNegativeTCycle

/-!
# The original negative BT contact as a scalar middle reference

Uncompiled source draft.  The unchanged negative-primary contact implies
the exact radial reference and its signed correction.  The existing
whole-domain affine cut `t+.63u<.156` suffices for both chosen stresses;
the `.94` stress retains a strict reserve greater than `.0019u`.
No additional T point, circle hypothesis, or geometric replacement is
introduced by the reference.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace OneNegativeBTReference
open PrimaryCap PositiveAngularEnvelope

def effective (t u : ℝ) : ℝ := (t+1/2)*Real.cos u+K*Real.sin u-1/2
def increment (t u : ℝ) : ℝ := effective t u-t

theorem increment_lower {t u : ℝ}
    (ht : t∈Icc 0 (39/250 : ℝ)) (hu : u∈Icc 0 (9/100 : ℝ)) :
    (10523/10000 : ℝ)*u≤increment t u := by
  have hc := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := u)) (show 0≤t+1/2 by linarith [ht.1])
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu.1)
    (show 0≤K by norm_num [K])
  have hcoeff := mul_nonneg (show 0≤82/125-(t+1/2) by linarith [ht.2]) (sq_nonneg u)
  have h2 : u^2≤(9/100)*u := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have h3 : u^3≤(81/10000)*u := by
    have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.1 hu.2 2) hu.1
    nlinarith
  dsimp [increment,effective,K]
  nlinarith

theorem increment_positive {t u : ℝ}
    (ht : t∈Icc 0 (39/250 : ℝ)) (hu : u∈Ioc 0 (9/100 : ℝ)) :
    (21/20 : ℝ)*u<increment t u := by
  have h := increment_lower ht ⟨hu.1.le,hu.2⟩
  nlinarith [hu.1]

theorem correction {t u mu : ℝ}
    (ht : t∈Icc 0 (39/250 : ℝ)) (hu : u∈Ioc 0 (9/100 : ℝ))
    (hline : t+(63/100)*u<39/250) (hmu : mu=47/50 ∨ mu=1) :
    (1-mu)*t+(41/40)*u-mu*increment t u≤(1-mu)*(39/250) := by
  have hs := increment_lower ht ⟨hu.1.le,hu.2⟩
  rcases hmu with rfl | rfl <;> nlinarith [hu.1]

end OneNegativeBTReference

namespace AlignedNegative
open PrimaryCap OneNegativeBTReference

/-- All three reference facts follow from the actual aligned source at
its own original circle ceiling. -/
theorem Source.scalar_reference {q u : ℝ} {H G A : SignedPoint}
    (I : Source q u H G A) (hq : q≤qCap) :
    1+effective (-G.y) u≤A.a ∧
      (21/20 : ℝ)*u<increment (-G.y) u ∧
      -G.y+(63/100)*u<39/250 := by
  obtain ⟨hGa,hg0,hg1,hH,hHa,hu,hR,hq0⟩ := I.cuts hq
  obtain ⟨hAlo,hAhi,hvalue,hvaluele⟩ := I.cap_data hq
  have hc : 0<Real.cos u := transport_cos_pos
    (show |u|≤(7/10 : ℝ) by rw [abs_of_pos I.tilt_pos]; exact I.tilt_cap)
  have hcontact := value_contact_identity (A.a-1/2) u hc.ne'
  have hm := mul_le_mul_of_nonneg_right hvalue hc.le
  have hfirst : 1+effective (-G.y) u≤A.a := by
    dsimp [effective]
    linarith
  have hinc := increment_positive
    (show -G.y∈Icc 0 (39/250 : ℝ) by exact ⟨by linarith,hg1.le⟩)
    ⟨I.tilt_pos,hu.le⟩
  have hline := intrinsic_affine_cut
    (show 3/5< -G.y+1/2 ∧ -G.y+1/2≤183/200 by constructor <;> linarith)
    ⟨I.tilt_pos.le,I.tilt_cap⟩ (hR.trans_le hq)
  exact ⟨hfirst,hinc,by linarith⟩

theorem Source.reference_correction {q u l mu L : ℝ} {H G A : SignedPoint}
    (I : Source q u H G A) (hq : q≤qCap)
    (hw : OneNegativeAnchorConcentration.Weights l mu L) :
    (1-mu)*(-G.y)+(41/40)*u-mu*OneNegativeBTReference.increment (-G.y) u≤
      (1-mu)*(39/250) := by
  obtain ⟨_,hg0,hg1,_,_,hu,_,_⟩ := I.cuts hq
  apply OneNegativeBTReference.correction
    ⟨by linarith,hg1.le⟩ ⟨I.tilt_pos,hu.le⟩ (I.scalar_reference hq).2.2
  rcases hw with ⟨_,_,hmu⟩ | ⟨_,_,hmu⟩
  · exact Or.inl hmu
  · exact Or.inr hmu

end AlignedNegative
end SquaresInCircles.Eight.TableFree
