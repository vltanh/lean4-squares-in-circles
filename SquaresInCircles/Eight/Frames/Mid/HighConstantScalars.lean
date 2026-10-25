module

public import SquaresInCircles.Eight.Frames.Diagonal.Labels
public import SquaresInCircles.Eight.Frames.Mid.HighNormMonotonicity
public import SquaresInCircles.Eight.Words.Second.Outer.ReferenceTrig

/-!
# Eight squares: the three constant middle/high supports

The common derivative theorem applies to all three doubled multipliers.
Each remaining comparison is at its first geometric endpoint, using
Taylor bounds and positive square comparisons for the actual norm.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighConstantScalars
open FramePair FrameDiagonalArc FrameDiagonalLabels

def P (x : ℝ) : ℝ :=
  9/100+43/100+cM-(43/100)*FrameDiagonalArc.a0+k+FrameMidHighNormMonotonicity.F (43/50) x
def sourceNorm (l : ℝ) : ℝ := Real.sqrt ((l+u)^2+(l-v)^2)
def negativeK (l : ℝ) : ℝ :=
  9/100+2*l+u*R+cM+k-R*sourceNorm l
def N (l x : ℝ) : ℝ := negativeK l+FrameMidHighNormMonotonicity.F (2*l) x

theorem trigonometric_reference {x : ℝ} (hx : 0≤x) :
    HighOrderTaylor.S11 x≤Real.sin x ∧ Real.sin x≤Arithmetic.sin9 x ∧
      Arithmetic.cos10 x≤Real.cos x ∧ Real.cos x≤SecondWord.ReferenceTrig.cos12 x :=
  ⟨HighOrderTaylor.S11_le_sin hx,Arithmetic.sin_le_sin9 hx,
    Arithmetic.cos10_le_cos hx,SecondWord.ReferenceTrig.cos_le_cos12 hx⟩

/-- The two radii are related by their exact squares. This comparison
retains the positive actual norm before eliminating the radical. -/
theorem target_force_upper {L x z : ℝ} (hL : 0≤L)
    (hx : x∈Icc 0 (Real.pi/2)) (hz : 0<z)
    (he : FrameMidArc.p^2+FrameMidArc.q^2+L^2+
      2*L*(FrameMidArc.p*Real.sin x-FrameMidArc.q*Real.cos x)<2*z^2) :
    FrameCircleArc.R*FrameMidHighNormMonotonicity.NF L x<
      (139921407/50000000:ℝ)*z := by
  have hn := FrameMidHighNormMonotonicity.NF_pos hL hx
  have hN2 := FrameMidHighNormMonotonicity.NF_sq hL hx
  have hN : (FrameMidHighNormMonotonicity.NF L x)^2<2*z^2 := by rwa [hN2]
  have hp := mul_lt_mul_of_pos_left hN (show 0<Q0 by norm_num [Q0])
  have hleft : (FrameCircleArc.R*FrameMidHighNormMonotonicity.NF L x)^2=
      Q0*(FrameMidHighNormMonotonicity.NF L x)^2 := by
    rw [mul_pow,FrameCircleArc.R_sq]
  have hright : (R*z)^2=2*Q0*z^2 := by rw [mul_pow,R_sq]
  have hlt : FrameCircleArc.R*FrameMidHighNormMonotonicity.NF L x<R*z := by
    nlinarith [mul_pos FrameCircleArc.R_pos hn,mul_pos R_pos hz]
  exact hlt.trans (mul_lt_mul_of_pos_right R_precise.2 hz)

theorem positive_reference : (8951/10000:ℝ)<P (21/50) := by
  have ht := trigonometric_reference (show (0:ℝ)≤21/50 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have he : FrameMidArc.p^2+FrameMidArc.q^2+(43/50:ℝ)^2+
      2*(43/50)*(FrameMidArc.p*Real.sin (21/50)-FrameMidArc.q*Real.cos (21/50))<
        2*(28349773/20000000:ℝ)^2 := by
    dsimp [FrameMidArc.p,FrameMidArc.q]
    nlinarith
  have hforce := target_force_upper (by norm_num : (0:ℝ)≤43/50)
    (show (21/50:ℝ)∈Icc 0 (Real.pi/2) from
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩)
    (by norm_num : (0:ℝ)<28349773/20000000) he
  dsimp [P,FrameMidHighNormMonotonicity.F,cM,k]
  linarith [Arithmetic.pi_hand_enclosure.1,a0_precise.2]

theorem source_norm_positive {l : ℝ} (hl : 0≤l) : 0<sourceNorm l := by
  apply Real.sqrt_pos.mpr
  have hp : 0<l+u := by dsimp [u]; linarith
  nlinarith [sq_pos_of_pos hp,sq_nonneg (l-v)]

theorem source_norm_sq (l : ℝ) : (sourceNorm l)^2=(l+u)^2+(l-v)^2 :=
  Real.sq_sqrt (by positivity)

theorem source_force_upper {l z : ℝ} (hl : 0≤l) (hz : 0<z)
    (he : (l+u)^2+(l-v)^2<z^2) :
    R*sourceNorm l<(139921407/50000000:ℝ)*z := by
  have hn := source_norm_positive hl
  have hs := source_norm_sq l
  have hnorm : sourceNorm l<z := by nlinarith
  exact (mul_lt_mul_of_pos_left hnorm R_pos).trans
    (mul_lt_mul_of_pos_right R_precise.2 hz)

theorem negative_middle_reference : (2233/2500:ℝ)<N (21/50) (3/5) := by
  have ht := trigonometric_reference (show (0:ℝ)≤3/5 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have he : FrameMidArc.p^2+FrameMidArc.q^2+(21/25:ℝ)^2+
      2*(21/25)*(FrameMidArc.p*Real.sin (3/5)-FrameMidArc.q*Real.cos (3/5))<
        2*(152373423/100000000:ℝ)^2 := by
    dsimp [FrameMidArc.p,FrameMidArc.q]
    nlinarith
  have htarget := target_force_upper (by norm_num : (0:ℝ)≤21/25)
    (show (3/5:ℝ)∈Icc 0 (Real.pi/2) from
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩)
    (by norm_num : (0:ℝ)<152373423/100000000) he
  have hsource := source_force_upper (l := (21/50:ℝ)) (z := (51283613/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [u,v])
  dsimp [N,negativeK,FrameMidHighNormMonotonicity.F,cM,k,u]
  norm_num only at htarget ⊢
  linarith [Arithmetic.pi_hand_enclosure.1,R_precise.1]

theorem negative_last_reference : (1123/1250:ℝ)<N (2/5) (7/10) := by
  have ht := trigonometric_reference (show (0:ℝ)≤7/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have he : FrameMidArc.p^2+FrameMidArc.q^2+(4/5:ℝ)^2+
      2*(4/5)*(FrameMidArc.p*Real.sin (7/10)-FrameMidArc.q*Real.cos (7/10))<
        2*(15744183/10000000:ℝ)^2 := by
    dsimp [FrameMidArc.p,FrameMidArc.q]
    nlinarith
  have htarget := target_force_upper (by norm_num : (0:ℝ)≤4/5)
    (show (7/10:ℝ)∈Icc 0 (Real.pi/2) from
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩)
    (by norm_num : (0:ℝ)<15744183/10000000) he
  have hsource := source_force_upper (l := (2/5:ℝ)) (z := (9916377/20000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [u,v])
  dsimp [N,negativeK,FrameMidHighNormMonotonicity.F,cM,k,u]
  norm_num only at htarget ⊢
  linarith [Arithmetic.pi_hand_enclosure.1,R_precise.1]

theorem positive_lower {x : ℝ} (hx : x∈Icc (21/50:ℝ) (61/100)) :
    (4463/5000:ℝ)<P x := by
  have hh := FrameMidHighNormMonotonicity.F_monotone
    (L := (43/50:ℝ)) (by constructor <;> norm_num)
    (show (21/50:ℝ)∈Icc (21/50:ℝ) (93/100) by constructor <;> norm_num)
    (show x∈Icc (21/50:ℝ) (93/100) from ⟨hx.1,by linarith [hx.2]⟩) hx.1
  have hP : P (21/50)≤P x := by dsimp [P]; linarith
  linarith [positive_reference]

theorem negative_middle_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (7/10)) :
    (4463/5000:ℝ)<N (21/50) x := by
  have hh := FrameMidHighNormMonotonicity.F_monotone
    (L := (21/25:ℝ)) (by constructor <;> norm_num)
    (show (3/5:ℝ)∈Icc (21/50:ℝ) (93/100) by constructor <;> norm_num)
    (show x∈Icc (21/50:ℝ) (93/100) from ⟨by linarith [hx.1],by linarith [hx.2]⟩) hx.1
  have hN : N (21/50) (3/5)≤N (21/50) x := by dsimp [N]; norm_num only; linarith
  linarith [negative_middle_reference]

theorem negative_last_lower {x : ℝ} (hx : x∈Icc (7/10:ℝ) (93/100)) :
    (4463/5000:ℝ)<N (2/5) x := by
  have hh := FrameMidHighNormMonotonicity.F_monotone
    (L := (4/5:ℝ)) (by constructor <;> norm_num)
    (show (7/10:ℝ)∈Icc (21/50:ℝ) (93/100) by constructor <;> norm_num)
    (show x∈Icc (21/50:ℝ) (93/100) from ⟨by linarith [hx.1],hx.2⟩) hx.1
  have hN : N (2/5) (7/10)≤N (2/5) x := by dsimp [N]; norm_num only; linarith
  linarith [negative_last_reference]

end SquaresInCircles.Eight.FrameMidHighConstantScalars
