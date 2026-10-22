module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Nonradical

/-!
# Squared-norm bounds at all reference endpoints

Uncompiled Section 7. The affected zero-angle norm cancels its secant
exactly. At an unaffected negative-angle norm the lower cosine square
is used only after comparison with the actual nonnegative sine. The
only coefficient replaced by a Taylor upper bound is D's zero-angle
rotating coefficient.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Analytic
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate (Curve)

theorem unscaled_angle (e : Curve) (z : ℝ) (he : Certificate.scaled e≠true) : angle e z=0 := by
  cases e <;> simp [Certificate.scaled,angle] at he ⊢

theorem coefficient_positive (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    0<p e z j ∧ 0<q e z j := by
  have hd := domains e hz
  have hb := Explicit.positive (Certificate.family e) hd.1
  have hl : 0<Explicit.l (Certificate.family e) z := by linarith [hb.2.1]
  have hcos : 0<Real.cos (angle e z) := by linarith [(transport_trig hd.2.1).1]
  have hsec : 0<secant (Explicit.l (Certificate.family e) z) (angle e z) := div_pos hl hcos
  have hc : 0<Explicit.c (Certificate.family e) z :=
    PositiveTD.tilted_pos hb.2.2 (Explicit.frame_domain (Certificate.family e) hd.1)
  fin_cases j
  · simpa [p,q] using And.intro hb.1 (show (0:ℝ)<1 by norm_num)
  · dsimp [p,q,lambdaG,NegativeAPositiveTD.lambdaG]
    split_ifs <;> exact ⟨hb.1,by assumption⟩
  · dsimp [p,q,lambdaB,NegativeAPositiveTD.lambdaB]
    split_ifs <;> exact ⟨hb.2.2,by assumption⟩
  · simpa [p,q] using And.intro (show (0:ℝ)<1 by norm_num) hc

theorem native_rotation (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.rotation e)=
      aeval z (Certificate.rotationHi (Certificate.family e)) := by
  simp [Certificate.rotation,Certificate.rotationHi,aeval_comp,PositiveTD.Certificate.etaQ]

theorem base_square_bounds (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    (scale e z*pairNorm (p e z j) (q e z j) 0)^2≤
      aeval (z-(Certificate.start e:ℝ))
        (if Certificate.scaled e then Certificate.scaledP e j else Certificate.baseP e j) := by
  have hd := domains e hz
  have hcos := NegativeAPositiveTD.Certificate.cosine_square_upper hd.2.1
  have hc : 0<Real.cos (angle e z) := by linarith [(transport_trig hd.2.1).1]
  have hrot := (Explicit.rotation_bounds (Certificate.family e) hd.1).2
  have hrot0 : 0≤Explicit.c (Certificate.family e) z := (coefficient_positive e hz 3).2.le
  have hD := NonnegativeTotals.Analytic.norm_zero_coefficient_upper (p:=1) hrot0 hrot
  by_cases he : Certificate.scaled e=true
  · simp only [if_pos he]
    fin_cases j
    · have hh := mul_le_mul_of_nonneg_right hcos
        (add_nonneg (sq_nonneg (Explicit.k (Certificate.family e) z)) (sq_nonneg (1:ℝ)))
      simpa [scale,he,p,q,Certificate.scaledP,Certificate.baseP,aeval_comp,mul_pow,
        NonnegativeTotals.Analytic.norm_zero_square] using hh
    · by_cases hg : Certificate.atG e=true
      · have hh := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Explicit.k (Certificate.family e) z))
        have hs := NegativeAPositiveTD.Certificate.scaled_secant_norm_sq
          (a:=Explicit.k (Certificate.family e) z) (l:=Explicit.l (Certificate.family e) z) hc
        simp only [scale,if_pos he,p,q,lambdaG,NegativeAPositiveTD.lambdaG,if_pos hg,
          Matrix.cons_val_succ,Matrix.cons_val_zero,hs]
        simpa [Certificate.scaledP,hg,aeval_comp,add_comm] using
          add_le_add_right hh ((Explicit.l (Certificate.family e) z)^2)
      · have hh := mul_le_mul_of_nonneg_right hcos
          (add_nonneg (sq_nonneg (Explicit.k (Certificate.family e) z)) (sq_nonneg (Explicit.l (Certificate.family e) z)))
        simpa [scale,he,p,q,lambdaG,NegativeAPositiveTD.lambdaG,hg,Certificate.scaledP,
          Certificate.baseP,aeval_comp,mul_pow,NonnegativeTotals.Analytic.norm_zero_square] using hh
    · by_cases hg : Certificate.atG e=true
      · have hh := mul_le_mul_of_nonneg_right hcos
          (add_nonneg (sq_nonneg (Explicit.m (Certificate.family e) z)) (sq_nonneg (Explicit.l (Certificate.family e) z)))
        simpa [scale,he,p,q,lambdaB,NegativeAPositiveTD.lambdaB,hg,Certificate.scaledP,
          Certificate.baseP,aeval_comp,mul_pow,NonnegativeTotals.Analytic.norm_zero_square,add_comm] using hh
      · have hg' : Certificate.atG e=false := by cases Certificate.atG e <;> simp_all
        have hh := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Explicit.m (Certificate.family e) z))
        have hs := NegativeAPositiveTD.Certificate.scaled_secant_norm_sq
          (a:=Explicit.m (Certificate.family e) z) (l:=Explicit.l (Certificate.family e) z) hc
        simp only [scale,if_pos he,p,q,lambdaB,NegativeAPositiveTD.lambdaB,if_neg hg,
          Matrix.cons_val_succ,Matrix.cons_val_zero,hs]
        simpa [Certificate.scaledP,hg',aeval_comp,add_comm] using
          add_le_add_right hh ((Explicit.l (Certificate.family e) z)^2)
    · have hh := mul_le_mul hcos hD (sq_nonneg _) (sq_nonneg _)
      simpa [scale,he,p,q,Certificate.scaledP,Certificate.baseP,aeval_comp,mul_pow,
        native_rotation] using hh
  · have hs := unscaled_angle e z he
    simp only [if_neg he]
    fin_cases j
    · simp [scale,he,p,q,Certificate.baseP,NonnegativeTotals.Analytic.norm_zero_square,add_comm]
    · simp [scale,he,p,q,lambdaG,NegativeAPositiveTD.lambdaG,secant,NegativeAPositiveTD.secant,
        hs,Certificate.baseP,NonnegativeTotals.Analytic.norm_zero_square]
    · simp [scale,he,p,q,lambdaB,NegativeAPositiveTD.lambdaB,secant,NegativeAPositiveTD.secant,
        hs,Certificate.baseP,NonnegativeTotals.Analytic.norm_zero_square,add_comm]
    · simpa [scale,he,p,q,Certificate.baseP,native_rotation] using hD

theorem selected_fixed (e : Curve) (z : ℝ) (j : Fin 4) (hj : Certificate.selected e=some j) :
    j≠3 ∧ q e z j=(![1,Explicit.l (Certificate.family e) z,Explicit.l (Certificate.family e) z,
      Explicit.c (Certificate.family e) z] j) ∧
    Certificate.scaledP e j=(PositiveTD.Certificate.C12.comp (Certificate.angle e))^2*Certificate.baseP e j := by
  cases e <;> fin_cases j <;>
    simp [Certificate.selected] at hj <;>
    simp [q,angle,lambdaG,lambdaB,secant,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,
      NegativeAPositiveTD.secant,Certificate.atG,Certificate.scaledP]

theorem selected_base (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4)
    (hj : Certificate.selected e=some j) :
    (p e z j)^2+(q e z j)^2=aeval (z-(Certificate.start e:ℝ)) (Certificate.baseP e j) ∧
    p e z j*q e z j=aeval (z-(Certificate.start e:ℝ)) (Certificate.pairProduct e j) := by
  have hf := selected_fixed e z j hj
  rw [hf.2.1]
  fin_cases j
  · simp [p,Certificate.baseP,Certificate.pairProduct,add_comm]
  · simp [p,Certificate.baseP,Certificate.pairProduct]
  · simp [p,Certificate.baseP,Certificate.pairProduct,add_comm,mul_comm]
  · exact False.elim (hf.1 rfl)

theorem norm_square_upper (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    (scaledNorm e z j)^2≤aeval (z-(Certificate.start e:ℝ)) (Certificate.P e j) := by
  have hbase := base_square_bounds e hz j
  by_cases hj : Certificate.selected e=some j
  · have hfixed := selected_fixed e z j hj
    have hpair := selected_base e hz j hj
    have hp := coefficient_positive e hz j
    have hd := domains e hz
    have hs := PositiveTD.Certificate.taylor_bounds hd.2.1
    have hn := PositiveTD.Certificate.taylor_bounds hd.2.2.1
    by_cases he : Certificate.scaled e=true
    · have hClo : (aeval (angle e z) PositiveTD.Certificate.C10)^2≤(Real.cos (angle e z))^2 :=
        pow_le_pow_left₀ (by linarith [hs.2.2.2.1]) hs.2.2.2.2.1 2
      have hChi := NegativeAPositiveTD.Certificate.cosine_square_upper hd.2.1
      have hh := NegativeAPositiveTD.Certificate.scaled_negative_norm_bound hp.1 hp.2 hd.2.2.1
        hClo hChi hpair.1.le (mul_nonneg hp.1.le hp.2.le) (le_refl (p e z j*q e z j)) hn.2.1
      rw [hpair.2] at hh
      simpa [scaledNorm,scale,he,norm,hj,Certificate.P,hfixed.2.2,aeval_comp] using hh
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hp.1 hp.2 hd.2.2.1
      rw [hpair.1,hpair.2] at hh
      simpa [scaledNorm,scale,he,norm,hj,Certificate.P,aeval_comp] using hh
  · simpa [scaledNorm,norm,hj,Certificate.P] using hbase

theorem scaledNorm_nonnegative (e : Curve) {z : ℝ} (hz : Domain e z) (j : Fin 4) :
    0≤scaledNorm e z j := mul_nonneg (scale_positive e hz).le (Real.sqrt_nonneg _)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Analytic
