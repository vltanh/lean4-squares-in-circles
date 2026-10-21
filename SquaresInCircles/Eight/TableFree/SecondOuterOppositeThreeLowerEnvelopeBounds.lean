module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerEnvelopeReferences

/-!
# Whole-interval shape of the target envelope

Monotonicity and concavity propagate the two endpoint substitutions
over the entire continued target interval.  The derivative estimates
retain the dependence between the target slope and its curvature.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)

lemma mem_short {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : B∈Icc 0 (83/200) :=
  ⟨by linarith [hB.1],by linarith [hB.2]⟩
lemma mem_outer {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : B∈Icc 0 outerDiagonal :=
  LowerFirst.short_domain (mem_short hB)

lemma label_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (911/1000:ℝ)<p B ∧ p B<1117/1000 ∧
    -(191/100:ℝ)<ell B ∧ ell B< -(753/500:ℝ) ∧
    (129/40:ℝ)<LLabel.d3 B ∧ LLabel.d3 B<438/125 := by
  rcases endpoint_label_bounds with ⟨hp₀,hp₁,he₀,he₁,ht₀,ht₁⟩
  have hpL := p_antitone (by norm_num : (3/100:ℝ)∈Icc 0 (83/200)) (mem_short hB) hB.1
  have hpR := p_antitone (mem_short hB) (by norm_num : (3/20:ℝ)∈Icc 0 (83/200)) hB.2
  have heL := L_second_monotone (mem_outer (by norm_num : (3/100:ℝ)∈Icc (3/100) (3/20)))
    (mem_outer hB) hB.1
  have heR := L_second_monotone (mem_outer hB)
    (mem_outer (by norm_num : (3/20:ℝ)∈Icc (3/100) (3/20))) hB.2
  have htL := L_third_monotone (mem_outer (by norm_num : (3/100:ℝ)∈Icc (3/100) (3/20)))
    (mem_outer hB) hB.1
  have htR := L_third_monotone (mem_outer hB)
    (mem_outer (by norm_num : (3/20:ℝ)∈Icc (3/100) (3/20))) hB.2
  exact ⟨hp₁.trans_le hpR,hpL.trans_lt hp₀,he₀.trans_le heL,heR.trans_lt he₁,
    ht₀.trans_le htL,htR.trans_lt ht₁⟩

lemma product_second_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    -(264/125:ℝ)<h₂ B ∧ h₂ B< -(367/500:ℝ) := by
  rcases label_bounds hB with ⟨hp0,hp1,he0,he1,ht0,ht1⟩
  have hz : z B∈Icc (53/100:ℝ) (13/20) := by
    dsimp [z]
    constructor <;> linarith [hB.1,hB.2]
  let Z : Interval (z B) := Interval.of_bounds hz
  let E : Interval (ell B) := Interval.of_bounds ⟨he0.le,he1.le⟩
  let T : Interval (LLabel.d3 B) := Interval.of_bounds ⟨ht0.le,ht1.le⟩
  let H := ((Interval.point 2).mul E).add (Z.mul T)
  have hl : -(264/125:ℝ)<H.lo := by
    norm_num [H,E,Z,T,Interval.point,Interval.of_bounds,Interval.mul,Interval.add]
  have hh : H.hi< -(367/500:ℝ) := by
    norm_num [H,E,Z,T,Interval.point,Interval.of_bounds,Interval.mul,Interval.add]
  exact ⟨hl.trans_le H.mem.1,H.mem.2.trans_lt hh⟩

lemma product_first_antitone : AntitoneOn h₁ (Icc (3/100) (3/20)) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (h₁_hasDerivAt (mem_outer hB)).continuousAt.continuousWithinAt)
    (fun B hB => h₁_hasDerivAt (mem_outer (Ioo_subset_Icc_self hB)))
    (fun B hB => by linarith [(product_second_bounds (Ioo_subset_Icc_self hB)).2])

lemma product_first_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    -(69/1000:ℝ)<h₁ B ∧ h₁ B<21/200 := by
  have hl := product_first_antitone hB (by norm_num) hB.2
  have hh := product_first_antitone (by norm_num) hB hB.1
  rcases endpoint_product_bounds with ⟨_,_,_,hleft,hright,_,_⟩
  exact ⟨hright.trans_le hl,hh.trans_lt hleft⟩

lemma product_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (591/1000:ℝ)<h B ∧ h B<121/200 := by
  have hconc : ConcaveOn ℝ (Icc (3/100) (3/20)) h :=
    concave_of_deriv2 (fun t ht => h_hasDerivAt (mem_outer ht))
      (fun t ht => h₁_hasDerivAt (mem_outer ht))
      (fun t ht => by linarith [(product_second_bounds ht).2])
  rcases endpoint_product_bounds with ⟨hl,hh,hr,_,_,_,_⟩
  have hlo := concave_gt_of_endpoints hconc hB hl hr
  have hd {t : ℝ} (ht : t∈Icc (3/100) (3/20)) :
      HasDerivAt (fun y => (21/200)*y-h y) (21/200-h₁ t) t :=
    ((hasDerivAt_id t).const_mul (21/200)).sub (h_hasDerivAt (mem_outer ht))
  have hm : MonotoneOn (fun y => (21/200)*y-h y) (Icc (3/100) (3/20)) :=
    monoOn_of_hasDeriv_nonneg (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [(product_first_bounds (Ioo_subset_Icc_self ht)).2])
  have hmB := hm (by norm_num) hB hB.1
  exact ⟨hlo,by nlinarith [hB.2]⟩

lemma marker_positive {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : 0<marker B := by
  have hm : AntitoneOn marker (Icc (3/100) (3/20)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro t ht
      exact (marker_hasDerivAt (mem_outer ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact marker_hasDerivAt (mem_outer (Ioo_subset_Icc_self ht))
    · intro t ht
      rcases label_bounds (Ioo_subset_Icc_self ht) with ⟨_,_,he,_,hthird,_⟩
      linarith
  have hh := hm hB (by norm_num) hB.2
  rcases endpoint_product_bounds with ⟨_,_,_,_,_,hp,_⟩
  exact hp.trans_le hh

lemma S_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (27/25:ℝ)<S B ∧ S B<163/100 := by
  have hp := label_bounds hB
  let P : Interval (p B) := Interval.of_bounds ⟨hp.1.le,hp.2.1.le⟩
  let Y : Interval B := Interval.of_bounds hB
  have hP : 0<P.lo := by norm_num [P,Interval.of_bounds]
  let Q := SBox Y P hP
  have hl : (27/25:ℝ)<Q.lo := by
    norm_num [Q,Y,P,SBox,zBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.square,Interval.mul,Interval.div,Interval.inv]
  have hh : Q.hi<(163/100:ℝ) := by
    norm_num [Q,Y,P,SBox,zBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.square,Interval.mul,Interval.div,Interval.inv]
  exact ⟨hl.trans_le Q.mem.1,Q.mem.2.trans_lt hh⟩

lemma D_large {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : (3/2)*S B<D B := by
  have hp := p_positive (mem_outer hB)
  have hm := marker_positive hB
  have hz : 0<z B ∧ z B<2/3 := by dsimp [z]; constructor <;> linarith [hB.1,hB.2]
  have he : D B-(3/2)*S B=z B*(1-(3/2)*z B)+marker B/(p B)^3 := by
    dsimp [D,S,marker]
    field_simp [hp.ne']
    ring
  have hfirst := mul_pos hz.1 (show 0<1-(3/2)*z B by linarith [hz.2])
  have hlast := div_pos hm (pow_pos hp 3)
  linarith

lemma curvature_square_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    p B*LLabel.d3 B<2*(ell B)^2 := by
  rcases label_bounds hB with ⟨hp0,hp1,he0,he1,ht0,ht1⟩
  have hp := mul_lt_mul hp1 ht1 (by linarith) (by norm_num)
  have he : (753/500:ℝ)^2<(ell B)^2 := by nlinarith
  nlinarith

lemma slopeRatio_bound {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    0<slopeRatio B ∧ slopeRatio B<227/125 := by
  have hp := p_positive (mem_outer hB)
  have he := ell_negative (mem_short hB)
  have hlo : 0<slopeRatio B := by dsimp [slopeRatio]; positivity
  have hm : MonotoneOn slopeRatio (Icc (3/100) (3/20)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (slopeRatio_hasDerivAt (mem_outer ht)).continuousAt.continuousWithinAt)
      (fun t ht => slopeRatio_hasDerivAt (mem_outer (Ioo_subset_Icc_self ht)))
      (fun t ht => div_nonneg (by linarith [curvature_square_bounds (Ioo_subset_Icc_self ht)])
        (pow_nonneg (p_positive (mem_outer (Ioo_subset_Icc_self ht))).le 3))
  have hh := hm hB (by norm_num) hB.2
  rcases endpoint_product_bounds with ⟨_,_,_,_,_,_,hhi⟩
  exact ⟨hlo,hh.trans_lt hhi⟩

lemma D_first_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : 0<D₁ B ∧ D₁ B<43/5 := by
  have hp := p_positive (mem_outer hB)
  have heq : D₁ B=1+(3*(ell B)^2-p B*LLabel.d3 B)/(p B)^4 := by
    dsimp [D₁]
    field_simp [hp.ne']
    ring
  have hnum : 0<3*(ell B)^2-p B*LLabel.d3 B := by
    nlinarith [curvature_square_bounds hB,sq_nonneg (ell B)]
  have hlo : 0<D₁ B := by rw [heq]; positivity
  have hd := label_bounds hB
  have hk := slopeRatio_bound hB
  let P : Interval (p B) := Interval.of_bounds ⟨hd.1.le,hd.2.1.le⟩
  let T : Interval (LLabel.d3 B) := Interval.of_bounds ⟨hd.2.2.2.2.1.le,hd.2.2.2.2.2.le⟩
  let K : Interval (slopeRatio B) := Interval.of_bounds ⟨hk.1.le,hk.2.le⟩
  have hP : 0<P.lo := by norm_num [P,Interval.of_bounds]
  let V := ((Interval.point 1).sub (T.div P.cube (Interval.cube_lo_pos hP))).add
    ((Interval.point 3).mul K.square)
  have hhi : V.hi<(43/5:ℝ) := by
    norm_num [V,T,P,K,Interval.of_bounds,Interval.point,Interval.sub,Interval.add,
      Interval.square,Interval.cube,Interval.mul,Interval.div,Interval.inv]
  have he : D₁ B=1-LLabel.d3 B/(p B)^3+3*(slopeRatio B)^2 := by
    dsimp [D₁,slopeRatio]
    field_simp [hp.ne']
    ring
  exact ⟨hlo,by rw [he]; exact V.mem.2.trans_lt hhi⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
