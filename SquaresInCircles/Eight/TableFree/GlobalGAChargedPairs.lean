module

public import SquaresInCircles.Eight.TableFree.GlobalGARadicals
public import SquaresInCircles.Eight.TableFree.ActualOrdinaryBlocks

/-!
# Full signed-angle bounds for the high-GA four-circle pairs

Uncompiled translation.  The original two signed angles are first
bounded by their exact positive and negative totals.  Separate
concavity then reduces the entire square of totals to its four
intrinsic corners.  No original angle is assumed concentrated.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity ActualOrdinaryBlocks

def chargedMixed (p q P N : ℝ) : ℝ :=
  mixedBlock R p q P N+charge*(P-N)

def chargedPair (p q a b : ℝ) : ℝ :=
  p*psi a+q*psi b-R*(pairNorm p q (a+b)-pairNorm p q 0)+charge*(a+b)

@[simp] theorem chargedMixed_zero (p q : ℝ) : chargedMixed p q 0 0=0 := by
  simp [chargedMixed,mixedBlock]

theorem chargedMixed_concave_P {p q N : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => chargedMixed p q P N) := by
  apply concave_of_deriv2
    (f' := fun P => mixedPDerivative R p q P N+charge)
    (f'' := fun P => curvature R p q (P-N)-p*PositiveAngularEnvelope.phi P)
  · intro P hP
    have h := (mixedP_hasDerivAt (R := R) hp (hp.trans_le hpq) hP hN).fun_add
      (((hasDerivAt_id P).sub_const N).const_mul charge)
    convert h using 1
    · funext x
      simp only [chargedMixed,id]
    · ring
  · intro P hP
    exact (mixedPDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN).add_const charge
  · intro P hP
    exact (mixedP_second_lt (Real.sqrt_nonneg _) (by rw [radius_sq])
      hp hpq hqp hP hN).le.trans (by nlinarith)

theorem chargedMixed_concave_N {p q P : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (chargedMixed p q P) := by
  apply concave_of_deriv2
    (f' := fun N => mixedNDerivative R p q P N-charge)
    (f'' := fun N => curvature R p q (P-N)-q*Real.cos N)
  · intro N hN
    have h := (mixedN_hasDerivAt (R := R) hp (hp.trans_le hpq) hP hN).fun_add
      (((hasDerivAt_const N P).sub (hasDerivAt_id N)).const_mul charge)
    convert h using 1
    · funext x
      simp only [chargedMixed,id,Pi.sub_apply]
    · ring
  · intro N hN
    exact (mixedNDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN).sub_const charge
  · intro N hN
    exact (mixedN_second_lt (Real.sqrt_nonneg _) (by rw [radius_sq])
      hp hpq hqp hP hN).le.trans (by nlinarith [hp.trans_le hpq])

/-- Four intrinsic corners control every allocation of both signed totals. -/
theorem charged_rectangle_lower {p q P N b : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap)
    (h00 : b<chargedMixed p q 0 0)
    (h10 : b<chargedMixed p q frameCap 0)
    (h01 : b<chargedMixed p q 0 frameCap)
    (h11 : b<chargedMixed p q frameCap frameCap) :
    b<chargedMixed p q P N := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have h0 := concave_gt_of_endpoints (chargedMixed_concave_N hp hpq hqp hz) hN h00 h01
  have h1 := concave_gt_of_endpoints (chargedMixed_concave_N hp hpq hqp hh) hN h10 h11
  exact concave_gt_of_endpoints (f := fun P => chargedMixed p q P N)
    (chargedMixed_concave_P hp hpq hqp hN) hP h0 h1

theorem charged_pair_minorant {p q a b : ℝ} (hp : 0≤p) (hpq : p≤q)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    chargedMixed p q (positivePart a+positivePart b) (negativePart a+negativePart b)≤
      chargedPair p q a b := by
  let B : Block := ⟨p,q,a,b⟩
  have hm := B.minorant R
    (by simpa [B,Block.p,min_eq_left hpq] using hp) hP hN
  have he : positivePart a+positivePart b-(negativePart a+negativePart b)=a+b := by
    linarith [positive_sub_negative a,positive_sub_negative b]
  simp only [B,Block.p,Block.q,Block.P,Block.N,Block.increment,
    min_eq_left hpq,max_eq_right hpq] at hm
  dsimp [chargedMixed,chargedPair]
  rw [he]
  linarith

theorem G_corners :
    (259/1000:ℝ)<chargedMixed k l frameCap 0 ∧
    -(576/10000:ℝ)<chargedMixed k l 0 frameCap ∧
    -(475/10000:ℝ)<chargedMixed k l frameCap frameCap := by
  have hn0 := radius_norm_lower (by norm_num : (0:ℝ)<17329526/10000000) G_zero_norm.1
  have hnp := radius_norm_upper (by norm_num : (0:ℝ)<21332741/10000000) G_positive_norm
  have hnn := radius_norm_upper (by norm_num : (0:ℝ)<12063965/10000000) G_negative_norm
  have hs := cap_trig.1
  have hc := cap_trig.2.2.1
  norm_num [Arithmetic.sin7,frameCap,k,l] at hn0 hnp hnn hs hc
  refine ⟨?_,?_,?_⟩ <;>
    norm_num [chargedMixed,mixedBlock,PositiveAngularEnvelope.phi,charge,k,l,frameCap] <;> nlinarith

theorem H_corners :
    (365/1000:ℝ)<chargedMixed k 1 frameCap 0 ∧
    -(22/10000:ℝ)<chargedMixed k 1 0 frameCap ∧
    (81/1000:ℝ)<chargedMixed k 1 frameCap frameCap := by
  have hn0 := radius_norm_lower (by norm_num : (0:ℝ)<12651580/10000000) H_zero_norm.1
  have hnp := radius_norm_upper (by norm_num : (0:ℝ)<16121920/10000000) H_positive_norm
  have hnn := radius_norm_upper (by norm_num : (0:ℝ)<7759432/10000000) H_negative_norm
  have hs := cap_trig.1
  have hc := cap_trig.2.2.1
  norm_num [Arithmetic.sin7,frameCap,k] at hn0 hnp hnn hs hc
  refine ⟨?_,?_,?_⟩ <;>
    norm_num [chargedMixed,mixedBlock,PositiveAngularEnvelope.phi,charge,k,frameCap] <;> nlinarith

theorem B_corners :
    -(44/10000:ℝ)<chargedMixed l 2 frameCap 0 ∧
    (730/1000:ℝ)<chargedMixed l 2 0 frameCap ∧
    (163/1000:ℝ)<chargedMixed l 2 frameCap frameCap := by
  have hn0 := radius_norm_lower (by norm_num : (0:ℝ)<12651580/10000000) H_zero_norm.1
  have hnp := radius_norm_upper (by norm_num : (0:ℝ)<16121920/10000000) H_positive_norm
  have hnn := radius_norm_upper (by norm_num : (0:ℝ)<7759432/10000000) H_negative_norm
  have hs := cap_trig.1
  have hc := cap_trig.2.2.1
  norm_num [Arithmetic.sin7,frameCap,k] at hn0 hnp hnn hs hc
  refine ⟨?_,?_,?_⟩ <;>
    simp only [chargedMixed,mixedBlock,B_norm_scale] <;>
    norm_num [PositiveAngularEnvelope.phi,charge,k,l,frameCap] <;> nlinarith

/-- The G pair estimate is valid on the complete intrinsic signed hexagon. -/
theorem G_pair_lower {a b : ℝ}
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(576/10000:ℝ)<chargedPair k l a b := by
  have h := charged_rectangle_lower (p:=k) (q:=l)
    (by norm_num [k]) (by norm_num [k,l]) (by norm_num [k,l])
    ⟨add_nonneg (positivePart_nonneg _) (positivePart_nonneg _),hP⟩
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hN⟩
    (by norm_num) (by linarith [G_corners.1]) G_corners.2.1 (by linarith [G_corners.2.2])
  exact h.trans_le (charged_pair_minorant (by norm_num [k]) (by norm_num [k,l]) hP hN)

/-- The H pair retains the smaller reserve needed for the other HG owner. -/
theorem H_pair_lower {a b : ℝ}
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(22/10000:ℝ)<chargedPair k 1 a b := by
  have h := charged_rectangle_lower (p:=k) (q:=1)
    (by norm_num [k]) (by norm_num [k]) (by norm_num [k])
    ⟨add_nonneg (positivePart_nonneg _) (positivePart_nonneg _),hP⟩
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hN⟩
    (by norm_num) (by linarith [H_corners.1]) H_corners.2.1 (by linarith [H_corners.2.2])
  exact h.trans_le (charged_pair_minorant (by norm_num [k]) (by norm_num [k]) hP hN)

theorem B_pair_lower {a b : ℝ}
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(44/10000:ℝ)<chargedPair l 2 a b := by
  have h := charged_rectangle_lower (p:=l) (q:=2)
    (by norm_num [l]) (by norm_num [l]) (by norm_num [l])
    ⟨add_nonneg (positivePart_nonneg _) (positivePart_nonneg _),hP⟩
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hN⟩
    (by norm_num) B_corners.1 (by linarith [B_corners.2.1]) (by linarith [B_corners.2.2])
  exact h.trans_le (charged_pair_minorant (by norm_num [l]) (by norm_num [l]) hP hN)

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
