module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDSlopes
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDConcentration

/-!
# The original signed excess delta-s in the E-dependent family

Uncompiled transcription of equations (22)--(24). The same-block norm
retains its fixed signed total; the separated case keeps both original
variation masses. The gain 257/4000 is obtained from the actual largest
coefficient c=27/20 and the proved absolute negative derivative 4/5.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Concentration
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope

abbrev positive (E : ℝ) (i : Fin 4) (P : ℝ) : ℝ :=
  PositiveTD.Hybrid.positive R aD (p E) (q E) 3 i P
abbrev block (E : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  PositiveTD.Hybrid.block R aD (p E) (q E) 3 i P N

def line (E : ℝ) (i j : Fin 4) (P N : ℝ) : ℝ :=
  if i=j then block E i P N else positive E i P+V R (p E j) (q E j) N

@[simp] theorem line_zero_left (E : ℝ) (i j : Fin 4) (N : ℝ) :
    line E i j 0 N=V R (p E j) (q E j) N := by
  by_cases hij : i=j
  · subst j; simp [line,block]
  · simp [line,hij,positive]

@[simp] theorem line_zero_right (E : ℝ) (i j : Fin 4) (P : ℝ) :
    line E i j P 0=positive E i P := by
  by_cases hij : i=j <;> simp [line,hij,block,positive]

theorem positive_lower {E P : ℝ} (hE : E∈Icc 0 frameCap)
    (i : Fin 4) (hP : P∈Icc 0 frameCap) : -(109/200)*c*P≤positive E i P := by
  by_cases hi : i=3
  · subst i
    rw [positive,PositiveTD.Hybrid.positive,ite_eq_left rfl]
    have hh := mul_le_mul_of_nonneg_right
      (show aD≤(109/200)*c by dsimp [aD,c]; linarith [diagonal_bounds.2]) hP.1
    linarith
  · have hc := coefficients hE i
    have hh := U_lower (R:=R) (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1
      (by linarith [hc.2.2.1]) hP
    have hq := mul_le_mul_of_nonneg_right hc.2.2.2.2 hP.1
    rw [positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
    simp only [c] at hq ⊢
    linarith

theorem line_excess_lower {E t P : ℝ} (hE : E∈Icc 0 frameCap) (i j : Fin 4)
    (ht : t∈Icc 0 frameCap) (hP : P∈Icc 0 (frameCap-t)) :
    V R (p E j) (q E j) t≤line E i j P (t+P) := by
  have hPf : P∈Icc 0 frameCap := ⟨hP.1,by linarith [hP.2,ht.1]⟩
  have hN : t+P∈Icc 0 frameCap := ⟨by linarith [ht.1,hP.1],by linarith [hP.2]⟩
  have hseparated : V R (p E j) (q E j) t≤positive E i P+V R (p E j) (q E j) (t+P) := by
    have hu := positive_lower hE i hPf
    have hv := negative_growth hE j ht hN (by linarith [hP.1])
    have hreserve := mul_nonneg (by norm_num : (0:ℝ)≤257/4000) hP.1
    dsimp [c] at hu
    linarith
  by_cases hij : i=j
  · subst j
    simp only [line,↓reduceIte]
    by_cases hi : i=3
    · subst i
      simpa [block,PositiveTD.Hybrid.block,positive,PositiveTD.Hybrid.positive] using hseparated
    · have hc := coefficients hE i
      have hconc := sameBlockLine_concave (R:=R) hc.1.le (hc.1.trans_le hc.2.1).le ht
      have hmin := hconc.min_le_of_mem_Icc
        (show (0:ℝ)∈Icc 0 (frameCap-t) from ⟨le_rfl,by linarith [ht.2]⟩)
        (show frameCap-t∈Icc 0 (frameCap-t) from ⟨by linarith [ht.2],le_rfl⟩) hP
      simp only [add_zero,mixedBlock_zero_left,mixedBlock_saturated] at hmin
      have hm := M_ge_V (R:=R) hc.1.le (hc.1.trans_le hc.2.1).le (by linarith [hc.2.2.1]) ht
      rw [min_eq_left hm] at hmin
      simpa only [block,PositiveTD.Hybrid.block,hi,↓reduceIte] using hmin
  · simpa only [line,hij,↓reduceIte] using hseparated

theorem shifted_maps {t s P : ℝ} (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hP : P∈Icc (max 0 (s-t)) (frameCap-t)) :
    P∈Icc 0 frameCap ∧ t-s+P∈Icc 0 frameCap :=
  PositiveANegativeTD.Fixed.shifted_maps ht hs hP

theorem shifted_same_concave {E t s : ℝ} (hE : E∈Icc 0 frameCap) (i : Fin 4)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t)) (fun P => block E i P (t-s+P)) := by
  have hc := coefficients hE i
  by_cases hi : i=3
  · have hlin : ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t)) (fun P : ℝ => -aD*P) := by
      simpa using affine_concave (-aD) 0 (max 0 (s-t)) (frameCap-t)
    have hV := concave_affine_argument
      (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
      (a:=1) (b:=t-s) (l:=max 0 (s-t)) (u:=frameCap-t)
      (fun P hP => by simpa only [one_mul,add_comm P] using (shifted_maps ht hs hP).2)
    refine (hlin.add hV).congr fun P _ => ?_
    simp only [Pi.add_apply,block,PositiveTD.Hybrid.block,hi,↓reduceIte,one_mul]
    rw [add_comm P (t-s)]
  · have he (P : ℝ) : block E i P (t-s+P)=
        p E i*(PositiveAngularEnvelope.phi P-1)+q E i*(Real.cos (t-s+P)-1)-
        R*(pairNorm (p E i) (q E i) (s-t)-pairNorm (p E i) (q E i) 0) := by
      simp only [block,PositiveTD.Hybrid.block,ite_eq_right hi,mixedBlock]
      rw [show P-(t-s+P)=s-t by ring]
    simp_rw [he]
    apply concave_of_deriv2
      (f':=fun P => p E i*(Real.cos P-Real.sin P)-q E i*Real.sin (t-s+P))
      (f'':=fun P => -p E i*PositiveAngularEnvelope.phi P-q E i*Real.cos (t-s+P))
    · intro P hP
      have hrot := (Real.hasDerivAt_cos (t-s+P)).comp P ((hasDerivAt_id P).const_add (t-s))
      have hraw := (((((Real.hasDerivAt_cos P).add (Real.hasDerivAt_sin P)).sub_const 1).const_mul
        (p E i)).add ((hrot.sub_const 1).const_mul (q E i))).sub_const
          (R*(pairNorm (p E i) (q E i) (s-t)-pairNorm (p E i) (q E i) 0))
      convert hraw using 1
      · rfl
      · ring
    · intro P hP
      have hrot := (Real.hasDerivAt_sin (t-s+P)).comp P ((hasDerivAt_id P).const_add (t-s))
      convert (((Real.hasDerivAt_cos P).sub (Real.hasDerivAt_sin P)).const_mul (p E i)).sub
        (hrot.const_mul (q E i)) using 1
      · rfl
      · dsimp [PositiveAngularEnvelope.phi]
        ring
    · intro P hP
      have hm := shifted_maps ht hs hP
      have hφ : 0≤PositiveAngularEnvelope.phi P := by
        dsimp [PositiveAngularEnvelope.phi]
        linarith [(transport_trig hm.1).1,(transport_trig hm.1).2.2.1]
      have hcos : 0≤Real.cos (t-s+P) := by linarith [(transport_trig hm.2).1]
      have h₁ := mul_nonneg hc.1.le hφ
      have h₂ := mul_nonneg (hc.1.trans_le hc.2.1).le hcos
      linarith

theorem shifted_line_concave {E t s : ℝ} (hE : E∈Icc 0 frameCap) (i j : Fin 4)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t)) (fun P => line E i j P (t-s+P)) := by
  by_cases hij : i=j
  · subst j
    simpa only [line,↓reduceIte] using shifted_same_concave hE i ht hs
  · have hi := coefficients hE i
    have hj := coefficients hE j
    have hU := (PositiveTD.Hybrid.positive_concave (a:=aD) (d:=3) (p:=p E) (q:=q E) (i:=i)
      (Real.sqrt_nonneg qCap) radius_sq.le hi.1 hi.2.1 (by linarith [hi.2.2.1])).subset
      (show Icc (max 0 (s-t)) (frameCap-t)⊆Icc 0 frameCap from fun P hP => (shifted_maps ht hs hP).1)
      (convex_Icc _ _)
    have hV := concave_affine_argument
      (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hj.1 hj.2.1 (by linarith [hj.2.2.1]))
      (a:=1) (b:=t-s) (l:=max 0 (s-t)) (u:=frameCap-t)
      (fun P hP => by simpa only [one_mul,add_comm P] using (shifted_maps ht hs hP).2)
    refine (hU.add hV).congr fun P _ => ?_
    simp only [Pi.add_apply,line,hij,↓reduceIte,positive,one_mul]
    rw [add_comm P (t-s)]

theorem upper_line_concave {E t : ℝ} (hE : E∈Icc 0 frameCap) (i j : Fin 4)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun s => line E i j (frameCap-t) (frameCap-s)) := by
  have hi := coefficients hE i
  have hj := coefficients hE j
  have hP : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  by_cases hij : i=j
  · subst j
    have hh := concave_affine_argument
      (PositiveTD.Hybrid.block_concave_negative (a:=aD) (p:=p E) (q:=q E) (d:=3) (i:=i)
        (Real.sqrt_nonneg qCap) radius_sq.le hi.1 hi.2.1 (by linarith [hi.2.2.1]) hP)
      (a:=-1) (b:=frameCap) (l:=0) (u:=frameCap)
      (fun s hs => ⟨by linarith [hs.2],by linarith [hs.1]⟩)
    convert hh using 1
    funext s
    simp only [line,↓reduceIte,block]
    congr 1
    ring_nf
  · have hh := concave_affine_argument
      (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hj.1 hj.2.1 (by linarith [hj.2.2.1]))
      (a:=-1) (b:=frameCap) (l:=0) (u:=frameCap)
      (fun s hs => ⟨by linarith [hs.2],by linarith [hs.1]⟩)
    have hc := PositiveANegativeTD.Fixed.affine_add_concave hh (positive E i (frameCap-t)) 0
    convert hc using 1
    funext s
    simp only [line,hij,↓reduceIte,zero_mul,add_zero]
    congr 1
    ring_nf

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Concentration
