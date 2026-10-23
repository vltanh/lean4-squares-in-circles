module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDScalars

/-!
# Concentration with the actual excess a-s

Uncompiled transcription of Sections 4--5 of the positive-A/negative-TD2
hand proof. Both sign totals are concentrated with their original
budgets. The common positive total has the intrinsic endpoints
`max 0 (s-a)` and `h-a`; the remaining s-dependence has endpoints 0, a, h.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.Fixed
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope
open PositiveTD.Hybrid

abbrev block (i : Fin 4) (P N : ℝ) : ℝ := PositiveTD.Hybrid.block R aD p q 3 i P N

def line (i j : Fin 4) (P N : ℝ) : ℝ :=
  if i=j then block i P N else positive i P+V R (p j) (q j) N

@[simp] theorem line_zero_left (i j : Fin 4) (N : ℝ) : line i j 0 N=V R (p j) (q j) N := by
  by_cases hij : i=j
  · subst j; simp [line,block]
  · simp [line,hij,positive]

@[simp] theorem line_zero_right (i j : Fin 4) (P : ℝ) : line i j P 0=positive i P := by
  by_cases hij : i=j <;> simp [line,hij,block,positive]

theorem affine_add_concave {f : ℝ→ℝ} {L U : ℝ}
    (hf : ConcaveOn ℝ (Icc L U) f) (A B : ℝ) :
    ConcaveOn ℝ (Icc L U) (fun x => A+B*x+f x) := by
  convert (affine_concave B A L U).add hf using 1
  funext x
  ring

theorem positive_lower (i : Fin 4) {b : ℝ} (hb : b∈Icc 0 frameCap) :
    -(109/200)*c*b≤positive i b := by
  by_cases hi : i=3
  · subst i
    simp only [positive,PositiveTD.Hybrid.positive,if_pos rfl]
    have hh := mul_le_mul_of_nonneg_right
      (show aD≤(109/200)*c by dsimp [aD,c]; linarith [diagonal_bounds.2]) hb.1
    linarith
  · have hc := coefficients i
    have hh := U_lower (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1
      (by linarith [hc.2.2.1]) hb
    have hcoef := mul_le_mul_of_nonneg_right hc.2.2.2.2.2 hb.1
    simp only [positive,PositiveTD.Hybrid.positive,if_neg hi]
    dsimp [c] at *
    linarith

/-- For nonnegative negative-variation excess, the whole line lies above
its pure negative endpoint. The 257/4000 reserve is kept in the proof. -/
theorem line_excess_lower (i j : Fin 4) {a P : ℝ}
    (ha : a∈Icc 0 frameCap) (hP : P∈Icc 0 (frameCap-a)) :
    V R (p j) (q j) a≤line i j P (a+P) := by
  have hPf : P∈Icc 0 frameCap := ⟨hP.1,by linarith [hP.2,ha.1]⟩
  have hN : a+P∈Icc 0 frameCap := ⟨by linarith [ha.1,hP.1],by linarith [hP.2]⟩
  have hseparated : V R (p j) (q j) a≤positive i P+V R (p j) (q j) (a+P) := by
    have hu := positive_lower i hPf
    have hv := negative_growth j ha hN (by linarith [hP.1])
    have hreserve : 0≤(257/4000:ℝ)*P := by positivity
    dsimp [c] at hu
    nlinarith
  by_cases hij : i=j
  · subst j
    simp only [line,if_pos rfl]
    by_cases hi : i=3
    · subst i
      simpa [block,PositiveTD.Hybrid.block,positive,PositiveTD.Hybrid.positive] using hseparated
    · have hc := coefficients i
      have hconc := sameBlockLine_concave (R:=R) hc.1.le (hc.1.trans_le hc.2.1).le ha
      have hmin := hconc.min_le_of_mem_Icc
        (show (0:ℝ)∈Icc 0 (frameCap-a) from ⟨le_rfl,by linarith [ha.2]⟩)
        (show frameCap-a∈Icc 0 (frameCap-a) from ⟨by linarith [ha.2],le_rfl⟩) hP
      simp only [add_zero,mixedBlock_zero_left,mixedBlock_saturated] at hmin
      have hm := M_ge_V hc.1.le (hc.1.trans_le hc.2.1).le
        (by linarith [hc.2.2.1]) ha
      rw [min_eq_left hm] at hmin
      simpa only [block,PositiveTD.Hybrid.block,if_neg hi] using hmin
  · simpa only [line,if_neg hij] using hseparated

theorem shifted_maps {a s P : ℝ} (ha : a∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hP : P∈Icc (max 0 (s-a)) (frameCap-a)) :
    P∈Icc 0 frameCap ∧ a-s+P∈Icc 0 frameCap := by
  have hP0 : 0≤P := (le_max_left 0 (s-a)).trans hP.1
  have hPa : s-a≤P := (le_max_right 0 (s-a)).trans hP.1
  exact ⟨⟨hP0,by linarith [hP.2,ha.1]⟩,
    ⟨by linarith,by linarith [hP.2,hs.1]⟩⟩

/-- The same-block norm retains the fixed original signed sum s-a. -/
theorem shifted_same_concave (i : Fin 4) {a s : ℝ}
    (ha : a∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max 0 (s-a)) (frameCap-a))
      (fun P => block i P (a-s+P)) := by
  have hc := coefficients i
  by_cases hi : i=3
  · have hlin : ConcaveOn ℝ (Icc (max 0 (s-a)) (frameCap-a)) (fun P : ℝ => -aD*P) := by
      simpa using affine_concave (-aD) 0 (max 0 (s-a)) (frameCap-a)
    have hV := concave_affine_argument
      (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1
        (by linarith [hc.2.2.1]))
      (a:=1) (b:=a-s) (l:=max 0 (s-a)) (u:=frameCap-a)
      (fun P hP => by simpa only [one_mul,add_comm P] using (shifted_maps ha hs hP).2)
    simpa only [block,PositiveTD.Hybrid.block,if_pos hi,one_mul,add_comm _ (a-s)] using hlin.add hV
  · have he (P : ℝ) : block i P (a-s+P)=
        p i*(phi P-1)+q i*(Real.cos (a-s+P)-1)-
          R*(pairNorm (p i) (q i) (s-a)-pairNorm (p i) (q i) 0) := by
      simp only [block,PositiveTD.Hybrid.block,if_neg hi,mixedBlock]
      rw [show P-(a-s+P)=s-a by ring]
    simp_rw [he]
    apply concave_of_deriv2
      (f':=fun P => p i*(Real.cos P-Real.sin P)-q i*Real.sin (a-s+P))
      (f'':=fun P => -p i*phi P-q i*Real.cos (a-s+P))
    · intro P hP
      have hrot := (Real.hasDerivAt_cos (a-s+P)).comp P
        ((hasDerivAt_id P).const_add (a-s))
      convert ((((((Real.hasDerivAt_cos P).add (Real.hasDerivAt_sin P)).sub_const 1).const_mul (p i)).add
        ((hrot.sub_const 1).const_mul (q i))).sub_const
          (R*(pairNorm (p i) (q i) (s-a)-pairNorm (p i) (q i) 0)) using 1 <;> ring
    · intro P hP
      have hrot := (Real.hasDerivAt_sin (a-s+P)).comp P
        ((hasDerivAt_id P).const_add (a-s))
      convert (((Real.hasDerivAt_cos P).sub (Real.hasDerivAt_sin P)).const_mul (p i)).sub
        (hrot.const_mul (q i)) using 1 <;> dsimp [phi] <;> ring
    · intro P hP
      have hm := shifted_maps ha hs hP
      have hφ : 0≤phi P := by
        dsimp [phi]
        linarith [(transport_trig hm.1).1,(transport_trig hm.1).2.2.1]
      have hcos : 0≤Real.cos (a-s+P) := by linarith [(transport_trig hm.2).1]
      have h₁ := mul_nonneg hc.1.le hφ
      have h₂ := mul_nonneg (hc.1.trans_le hc.2.1).le hcos
      linarith

theorem shifted_line_concave (i j : Fin 4) {a s : ℝ}
    (ha : a∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max 0 (s-a)) (frameCap-a))
      (fun P => line i j P (a-s+P)) := by
  by_cases hij : i=j
  · subst j
    simpa only [line,if_pos rfl] using shifted_same_concave i ha hs
  · have hi := coefficients i
    have hj := coefficients j
    have hU := (PositiveTD.Hybrid.positive_concave (a:=aD) (d:=3)
      (Real.sqrt_nonneg qCap) radius_sq.le hi.1 hi.2.1
      (by linarith [hi.2.2.1])).subset
      (show Icc (max 0 (s-a)) (frameCap-a)⊆Icc 0 frameCap from
        fun P hP => (shifted_maps ha hs hP).1) (convex_Icc _ _)
    have hV := concave_affine_argument
      (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hj.1 hj.2.1
        (by linarith [hj.2.2.1]))
      (a:=1) (b:=a-s) (l:=max 0 (s-a)) (u:=frameCap-a)
      (fun P hP => by simpa only [one_mul,add_comm P] using (shifted_maps ha hs hP).2)
    simpa only [line,if_neg hij,positive,one_mul,add_comm _ (a-s)] using hU.add hV

theorem lower_negative_positive (j : Fin 4) {a s : ℝ}
    (ha : a∈Icc L frameCap) (hs : s∈Icc 0 a) :
    0<base+l*TwoPositive.ASupport.charge a+speed*s+V R (p j) (q j) (a-s) := by
  have hc := coefficients j
  have haf : a∈Icc 0 frameCap := ⟨by dsimp [L] at ha; linarith [ha.1],ha.2⟩
  have hV := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1
      (by linarith [hc.2.2.1]))
    (a:= -1) (b:=a) (l:=0) (u:=a)
    (fun s hs => ⟨by linarith [hs.2],by linarith [hs.1,ha.2]⟩)
  have hconc := affine_add_concave hV (base+l*TwoPositive.ASupport.charge a) speed
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+speed*0+V R (p j) (q j) ((-1)*0+a) := by
    simpa [pureScalar] using pure_positive j ha
  have h1 : 0<base+l*TwoPositive.ASupport.charge a+speed*a+V R (p j) (q j) ((-1)*a+a) := by
    simpa [middleScalar] using middle_positive ha
  have hh := concave_gt_of_endpoints hconc hs h0 h1
  simpa only [neg_mul,one_mul,neg_add_eq_sub] using hh

theorem lower_positive_positive (i : Fin 4) {a s : ℝ}
    (ha : a∈Icc L frameCap) (hs : s∈Icc a frameCap) :
    0<base+l*TwoPositive.ASupport.charge a+speed*s+positive i (s-a) := by
  have hc := coefficients i
  have haf : a∈Icc 0 frameCap := ⟨by dsimp [L] at ha; linarith [ha.1],ha.2⟩
  have hU := concave_affine_argument
    (PositiveTD.Hybrid.positive_concave (a:=aD) (p:=p) (q:=q) (d:=3) (i:=i)
      (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:=1) (b:= -a) (l:=a) (u:=frameCap)
    (fun s hs => ⟨by linarith [hs.1],by linarith [hs.2,haf.1]⟩)
  have hconc := affine_add_concave hU (base+l*TwoPositive.ASupport.charge a) speed
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+speed*a+
      PositiveTD.Hybrid.positive R aD p q 3 i (1*a+-a) := by
    simpa [middleScalar] using middle_positive ha
  have h1 : 0<base+l*TwoPositive.ASupport.charge a+speed*frameCap+
      PositiveTD.Hybrid.positive R aD p q 3 i (1*frameCap+-a) := by
    simpa [positiveScalar,positive,sub_eq_add_neg] using positive_positive i ha
  simpa only [one_mul,← sub_eq_add_neg,positive] using
    concave_gt_of_endpoints hconc hs h0 h1

theorem upper_line_concave (i j : Fin 4) {a : ℝ} (ha : a∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun s => line i j (frameCap-a) (frameCap-s)) := by
  have hi := coefficients i
  have hj := coefficients j
  have hP : frameCap-a∈Icc 0 frameCap := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  by_cases hij : i=j
  · subst j
    have hh := concave_affine_argument
      (PositiveTD.Hybrid.block_concave_negative (a:=aD) (p:=p) (q:=q) (d:=3) (i:=i)
        (Real.sqrt_nonneg qCap) radius_sq.le hi.1 hi.2.1
        (by linarith [hi.2.2.1]) hP)
      (a:= -1) (b:=frameCap) (l:=0) (u:=frameCap)
      (fun s hs => ⟨by linarith [hs.2],by linarith [hs.1]⟩)
    convert hh using 1
    funext s
    simp only [line,if_pos rfl,block]
    congr 1
    ring
  · have hh := concave_affine_argument
      (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hj.1 hj.2.1
        (by linarith [hj.2.2.1]))
      (a:= -1) (b:=frameCap) (l:=0) (u:=frameCap)
      (fun s hs => ⟨by linarith [hs.2],by linarith [hs.1]⟩)
    have hc := affine_add_concave hh (positive i (frameCap-a)) 0
    convert hc using 1
    funext s
    simp only [line,if_neg hij,zero_mul,add_zero]
    congr 1
    ring

theorem upper_positive (i j : Fin 4) {a s : ℝ}
    (ha : a∈Icc L frameCap) (hs : s∈Icc 0 frameCap) :
    0<base+l*TwoPositive.ASupport.charge a+speed*s+line i j (frameCap-a) (frameCap-s) := by
  have haf : a∈Icc 0 frameCap := ⟨by dsimp [L] at ha; linarith [ha.1],ha.2⟩
  have hconc := affine_add_concave (upper_line_concave i j haf)
    (base+l*TwoPositive.ASupport.charge a) speed
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+speed*0+
      line i j (frameCap-a) (frameCap-0) := by
    have hb := line_excess_lower i j haf
      (show frameCap-a∈Icc 0 (frameCap-a) from ⟨by linarith [ha.2],le_rfl⟩)
    rw [show a+(frameCap-a)=frameCap by ring] at hb
    have hp := pure_positive j ha
    dsimp [pureScalar] at hp
    simp only [mul_zero,add_zero,sub_zero]
    linarith
  have h1 : 0<base+l*TwoPositive.ASupport.charge a+speed*frameCap+
      line i j (frameCap-a) (frameCap-frameCap) := by
    simpa only [sub_self,line_zero_right,positiveScalar] using positive_positive i ha
  exact concave_gt_of_endpoints hconc hs h0 h1

/-- Every original positive total between its two intrinsic endpoints
has positive scalar stress, for the full signed excess a-s. -/
theorem line_scalar_positive (i j : Fin 4) {a s P : ℝ}
    (ha : a∈Icc L frameCap) (hs : s∈Icc 0 frameCap)
    (hP : P∈Icc (max 0 (s-a)) (frameCap-a)) :
    0<base+l*TwoPositive.ASupport.charge a+speed*s+line i j P (a-s+P) := by
  have haf : a∈Icc 0 frameCap := ⟨by dsimp [L] at ha; linarith [ha.1],ha.2⟩
  have hconc := affine_add_concave (shifted_line_concave i j haf hs)
    (base+l*TwoPositive.ASupport.charge a+speed*s) 0
  have hlo : 0<base+l*TwoPositive.ASupport.charge a+speed*s+
      line i j (max 0 (s-a)) (a-s+max 0 (s-a)) := by
    by_cases hsa : s≤a
    · rw [max_eq_left (by linarith : s-a≤0)]
      simp only [add_zero,line_zero_left]
      exact lower_negative_positive j ha ⟨hs.1,hsa⟩
    · have has : a≤s := (lt_of_not_ge hsa).le
      rw [max_eq_right (by linarith : 0≤s-a),show a-s+(s-a)=0 by ring,line_zero_right]
      exact lower_positive_positive i ha ⟨has,hs.2⟩
  have hhi : 0<base+l*TwoPositive.ASupport.charge a+speed*s+
      line i j (frameCap-a) (a-s+(frameCap-a)) := by
    rw [show a-s+(frameCap-a)=frameCap-s by ring]
    exact upper_positive i j ha hs
  simpa only [zero_mul,add_zero] using concave_gt_of_endpoints hconc hP
    (by simpa only [zero_mul,add_zero] using hlo)
    (by simpa only [zero_mul,add_zero] using hhi)

/-- Both concentration steps preserve the actual two sign totals. -/
theorem sum_scalar_positive {a s : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)=a-s+∑i,P i) :
    0<base+l*TwoPositive.ASupport.charge a+speed*s+∑i,block i (P i) (N i) := by
  have ha0 : 0≤a := by dsimp [L] at ha; linarith [ha.1]
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hP i)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hN i)
  obtain ⟨i,j,hij⟩ := PositiveTD.Hybrid.both_signs_concentrate R aD p q P N 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (coefficients i).1) (fun i => (coefficients i).2.1)
    (fun i => by linarith [(coefficients i).2.2.1]) hP hN
    (by linarith) (by linarith [hs.1])
  change line i j (∑i,P i) (∑i,N i)≤∑i,block i (P i) (N i) at hij
  have hpdom : (∑i,P i)∈Icc (max 0 (s-a)) (frameCap-a) :=
    ⟨max_le hP0 (by linarith),hPt⟩
  have hp := line_scalar_positive i j ha hs hpdom
  rw [hbalance] at hij
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.Fixed
