module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJBoundaryReferences

/-!
# The target-zero and upper-angle P/J boundaries

Uncompiled source draft.  The first boundary uses the single circle
estimate from Section 5, and the second uses the exact positive
curvature identity and its one named reference.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma zero_angle_positive {x : ℝ} (hd : Domain 0 x) : 0<angleFirst PLabel 0 x := by
  let z := b 0 x-1/2
  let q₀ := NegativeTwo.Inverse.q (U 0)
  let R := Real.sqrt q₀
  have hv := v_positive hd.1 hd.2.1
  have hp := (P_first_bounds hd.2.2).1
  have hq0 : 0<q₀ := by linarith [NegativeTwo.Inverse.actual_q_positive outer_zero_mem]
  have hq : q₀<(1087/1000:ℝ) := by
    dsimp [q₀,NegativeTwo.Inverse.q,U]
    rw [ShortOuterOne.SameContact.arc_zero]
    norm_num [Q0]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hR : 0<R := Real.sqrt_pos.mpr hq0
  have hR2 : R^2=q₀ := Real.sq_sqrt hq0.le
  have hRu : R<(1043/1000:ℝ) := by nlinarith
  have hn : z^2+(v 0 x)^2=q₀ := norm_identity outer_zero_mem x
  have hP : PLabel.d1 (b 0 x)<443/500+(223/1000)*z := by
    have hh := OppositeTwo.P_first_affine hd.2.2
    dsimp [z]
    linarith
  have hvR : v 0 x≤R := by nlinarith [sq_nonneg z]
  have hprod : PLabel.d1 (b 0 x)*v 0 x<1 := by
    rcases le_total z 0 with hz | hz
    · have hsmall : PLabel.d1 (b 0 x)<443/500 := by linarith
      have hh := mul_lt_mul'' hsmall (hvR.trans_lt hRu) (by linarith) hv.le
      norm_num at hh
      linarith
    · have htangent : v 0 x≤R-z^2/(2*R) := by
        have h2R : 0<2*R := by linarith
        have hh : z^2/(2*R)≤R-v 0 x := by
          rw [div_le_iff₀ h2R]
          nlinarith [sq_nonneg (R-v 0 x)]
        linarith
      have hcoef : 0<443/500+(223/1000)*z := by linarith
      have h1 := mul_lt_mul_of_pos_right hP hv
      have h2 := mul_le_mul_of_nonneg_left htangent hcoef.le
      have hcomplete : (443/500+(223/1000)*z)*(R-z^2/(2*R))≤
          (443/500)*R+(223/1000)^2*R^3/(2*(443/500)) := by
        have hkey : (443/500)*R+(223/1000)^2*R^3/(2*(443/500))-
            (443/500+(223/1000)*z)*(R-z^2/(2*R))=
            ((443/500)*z-(223/1000)*R^2)^2/(2*(443/500)*R)+(223/1000)*z^3/(2*R) := by
          field_simp
          ring
        have hnn : 0≤((443/500)*z-(223/1000)*R^2)^2/(2*(443/500)*R)+(223/1000)*z^3/(2*R) :=
          add_nonneg (by positivity)
            (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hz 3)) (by positivity))
        linarith
      have hcube : R^3<(1087/1000)*(1043/1000:ℝ) := by
        have hh := mul_lt_mul'' hq hRu hq0.le hR.le
        have he : R^3=q₀*R := by rw [←hR2]; ring
        rw [he]
        exact hh
      have hend : (443/500)*(1043/1000)+
          (223/1000)^2*((1087/1000)*(1043/1000))/(2*(443/500))<(1:ℝ) := by norm_num
      nlinarith
  dsimp [angleFirst]
  linarith

theorem zero_boundary_lower {x : ℝ} (hd : Domain 0 x) :
    (89777/100000:ℝ)<value PLabel JLabel 0 x := by
  have hstart : Diagonal.start<x := by
    by_contra! hn
    have hh := b_angle_antitone outer_zero_mem hd.2.1
      (by norm_num [Diagonal.start] : Diagonal.start∈Icc 0 (7/10)) hn
    linarith [Reference.zero_start,hd.2.2.2]
  have hc : Continuous (b 0) := by
    have hb : b 0=fun t => 1/2+(0+1/2)*Real.cos t-(arc 0-1/2)*Real.sin t := rfl
    rw [hb]
    fun_prop
  obtain ⟨y,hy,he⟩ := intermediate_value_Icc hstart.le hc.neg.continuousOn
    (show -outerDiagonal∈Icc (-b 0 Diagonal.start) (-b 0 x) by
      constructor <;> linarith [Reference.zero_start,hd.2.2.2])
  simp only [Pi.neg_apply] at he
  have hcontact : b 0 y=outerDiagonal := by linarith
  have hyi : y∈Icc 0 (7/10) :=
    ⟨by linarith [hy.1,show (0:ℝ)<Diagonal.start by norm_num [Diagonal.start]],hy.2.trans hd.2.1.2⟩
  have hdom : ∀t∈Icc y x,Domain 0 t := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := ⟨hyi.1.trans ht.1,ht.2.trans hd.2.1.2⟩
    have hb := b_angle_antitone outer_zero_mem hyi hti ht.1
    rw [hcontact] at hb
    exact ⟨outer_zero_mem,hti,⟨by linarith [b_lower outer_zero_mem hti],hb⟩⟩
  have hm : MonotoneOn (value PLabel JLabel 0) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (value_angle_hasDerivAt PLabel JLabel (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => value_angle_hasDerivAt PLabel JLabel (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (zero_angle_positive (hdom t (Ioo_subset_Icc_self ht))).le)
  have hh := hm ⟨le_rfl,hy.2⟩ ⟨hy.2,le_rfl⟩ hy.2
  dsimp [value] at hh ⊢
  rw [hcontact] at hh
  linarith [Reference.zero_start_cost,hy.1]

def capSecond (B : ℝ) : ℝ :=
  PLabel.d2 (b B (7/10))*(k B (7/10))^2+
    PLabel.d1 (b B (7/10))*ratioD B*Real.sin (7/10)-JLabel.d2 B

lemma capFirst_hasDerivAt {B : ℝ} (hd : Domain B (7/10)) :
    HasDerivAt (fun t => targetFirst PLabel JLabel t (7/10)) (capSecond B) B := by
  have hk : HasDerivAt (fun t => k t (7/10)) (ratioD B*Real.sin (7/10)) B :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
      (Real.sin (7/10))).const_add (Real.cos (7/10))
  have h := (((PLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp B
    (b_target_hasDerivAt hd.1 (7/10))).mul hk).sub
      (JLabel.d1_hasDerivAt (outer_domain hd.1))
  convert h using 1
  · funext t
    rfl
  · dsimp [capSecond]
    ring

lemma cap_curvature {B : ℝ} (hd : Domain B (7/10)) : (329/1000:ℝ)<capSecond B := by
  have hP2 := P_second_positive hd.2.2
  have hp := (P_first_bounds hd.2.2).1
  have hD := (outer_ratio_bounds hd.1).2.2.1
  have hs := (positive_trig hd.2.1).2.2.1
  have h1 := mul_nonneg hP2.le (sq_nonneg (k B (7/10)))
  have h2 := mul_nonneg (mul_nonneg (by linarith : 0≤PLabel.d1 (b B (7/10))) hD.le) hs
  have hJ := J_second_upper hd.1
  dsimp [capSecond]
  linarith

theorem cap_boundary_lower {B : ℝ} (hd : Domain B (7/10)) :
    (89777/100000:ℝ)<value PLabel JLabel B (7/10) := by
  let r := Reference.capReference
  let l := min B r
  let u := max B r
  have hr := Reference.cap_reference
  have hB : B∈Icc l u := ⟨min_le_left _ _,le_max_left _ _⟩
  have hR : r∈Icc l u := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom : ∀t∈Icc l u,Domain t (7/10) := by
    intro t ht
    have hti : t∈Icc 0 outerDiagonal :=
      ⟨(le_min hd.1.1 hr.1.1.1).trans ht.1,ht.2.trans (max_le hd.1.2 hr.1.1.2)⟩
    have hcut : b t (7/10)≤outerDiagonal := by
      rcases le_total B r with he | he
      · have htr : t≤r := by simpa [u,max_eq_right he] using ht.2
        exact (b_target_monotone hd.2.1 hti hr.1.1 htr).trans hr.1.2.2.2
      · have htB : t≤B := by simpa [u,max_eq_left he] using ht.2
        exact (b_target_monotone hd.2.1 hti hd.1 htB).trans hd.2.2.2
    exact ⟨hti,hd.2.1,⟨by linarith [b_lower hti hd.2.1],hcut⟩⟩
  have hh := curvature_tangent
    (f := fun t => value PLabel JLabel t (7/10))
    (d := fun t => targetFirst PLabel JLabel t (7/10)) (dd := capSecond)
    (κ := (329/1000:ℝ)) hB hR
    (fun t ht => value_target_hasDerivAt PLabel JLabel (hdom t ht))
    (fun t ht => capFirst_hasDerivAt (hdom t ht))
    (fun t ht => (cap_curvature (hdom t ht)).le)
  have hs := abs_lt.mp hr.2.2
  have hsquare := sq_nonneg ((329/1000)*(B-r)+targetFirst PLabel JLabel r (7/10))
  have hsmall : (targetFirst PLabel JLabel r (7/10))^2<(1/100000:ℝ)^2 := by nlinarith
  nlinarith [hr.2.1]

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
