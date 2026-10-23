module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerEnvelope

/-!
# One rational source polynomial on the complete continued arc

The bound on the third derivative of the inverse base angle is one
expanded degree-eight polynomial on `0 ≤ b ≤ .6`.  Its positive
coefficients and one endpoint power estimate prove the sign without
subdividing the source interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerSource
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open LowerInverse LowerGeometry

def polynomial (u : ℝ) : ℝ :=
  (11/20)*u^5*(q u)^3+Q0*NegativeTwo.Inverse.N u*q u-
    (Q0-u^2)*(2*Q0*(q u)^3+8*(Q0-1)*u^3)/(Q0+1)

lemma polynomial_shift (s : ℝ) : polynomial (411/250+s)=
    476159311146441826602549/305175781250000000000000+
    (26101615378177364354307/244140625000000000000)*s-
    (79955973126184850181/488281250000000000)*s^2+
    (454962014464731219/1953125000000000)*s^3+
    (2000561895379869/15625000000000)*s^4+
    (5418602309299/312500000000)*s^5-
    (2460112413/62500000)*s^6-(317823/12500)*s^7-(22/5)*s^8 := by
  dsimp [polynomial,q,NegativeTwo.Inverse.q,NegativeTwo.Inverse.N,Q0]
  ring

lemma polynomial_positive {u : ℝ} (hu : u∈Icc (411/250) (383/200)) : 0<polynomial u := by
  let s : ℝ := u-411/250
  have hs : s∈Icc (0:ℝ) (271/1000) := by
    dsimp [s]
    constructor <;> linarith [hu.1,hu.2]
  have h5 := pow_le_pow_left₀ hs.1 hs.2 5
  have h6 := pow_le_pow_left₀ hs.1 hs.2 6
  have h7 := pow_le_pow_left₀ hs.1 hs.2 7
  let tail : ℝ := 10691/100-(655/4)*s-(19681/500)*s^5-(12713/500)*s^6-(22/5)*s^7
  have htail : (62:ℝ)<tail := by
    dsimp [tail]
    norm_num at h5 h6 h7
    nlinarith [hs.2]
  have hpay : 0≤s*tail := mul_nonneg hs.1 (by linarith)
  have he := polynomial_shift s
  have heq : 411/250+s=u := by dsimp [s]; ring
  rw [heq] at he
  have hlo : (39/25:ℝ)+s*tail≤polynomial u := by
    dsimp [tail]
    nlinarith [pow_nonneg hs.1 3,pow_nonneg hs.1 4,pow_nonneg hs.1 5,
      pow_nonneg hs.1 6,pow_nonneg hs.1 7,sq_nonneg s]
  linarith

lemma source_U {b : ℝ} (hb : b∈Icc 0 (3/5)) :
    (411/250:ℝ)<U b ∧ U b<383/200 :=
  shifted_range (full_domain ⟨hb.1,by linarith [hb.2]⟩) hb.1 hb.2
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Q0]) (by norm_num [Q0])

lemma polynomial_identity {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (11/20-X b)*(U b)^5*(q (U b))^3=polynomial (U b) := by
  have hu := U_positive (outer_domain hb)
  have hq : 0<q (U b) := by linarith [NegativeTwo.Inverse.actual_q_positive hb]
  have hc := UW_circle (outer_domain hb)
  have hr : (ratio b)^2=(Q0-(U b)^2)/(U b)^2 := by
    change (W b/U b)^2=(Q0-(U b)^2)/(U b)^2
    field_simp [hu.ne']
    nlinarith
  change (11/20-(-(Q0/(U b)^3)*factorD (U b)+(ratio b)^2*factorDD (U b)))*
    (U b)^5*(q (U b))^3=polynomial (U b)
  rw [hr]
  dsimp [factorD,NegativeTwo.Inverse.factorD,factorDD,polynomial]
  field_simp [hu.ne',hq.ne',show Q0+1≠0 by norm_num [Q0]]
  ring

theorem X_upper {b : ℝ} (hb : b∈Icc 0 (3/5)) : X b<(11/20:ℝ) := by
  have hf := full_domain ⟨hb.1,by linarith [hb.2]⟩
  have he := polynomial_identity hf
  have hp := polynomial_positive ⟨(source_U hb).1.le,(source_U hb).2.le⟩
  have hu := U_positive (outer_domain hf)
  have hq : 0<q (U b) := by linarith [NegativeTwo.Inverse.actual_q_positive hf]
  have hden : 0<(U b)^5*(q (U b))^3 := by positivity
  have hpos : 0<(11/20-X b)*((U b)^5*(q (U b))^3) := by nlinarith
  have hh := (mul_pos_iff_of_pos_right hden).mp hpos
  linarith

lemma product_floor {u : ℝ} (hu : u∈Icc (411/250:ℝ) (383/200)) : (199/50:ℝ)<u^2*q u := by
  have hd (v : ℝ) : HasDerivAt (fun w => w^2*q w) (2*v*(Q0+1-3*v)) v := by
    convert ((hasDerivAt_id v).pow 2).mul (NegativeTwo.Inverse.q_hasDerivAt v)
      using 1 <;> dsimp [q,NegativeTwo.Inverse.q] <;> ring
  have hm : AntitoneOn (fun w => w^2*q w) (Icc (411/250:ℝ) (383/200)) :=
    antiOn_of_hasDeriv_nonpos
      (fun v _ => (hd v).continuousAt.continuousWithinAt)
      (fun v _ => hd v)
      (fun v hv => by
        have hv0 : 0≤v := by linarith [hv.1]
        have hc : Q0+1-3*v≤0 := by norm_num [Q0]; linarith [hv.1]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hc)
  have he : (199/50:ℝ)<(383/200)^2*q (383/200) := by norm_num [q,NegativeTwo.Inverse.q,Q0]
  exact he.trans_le (hm hu (by norm_num) hu.2)

theorem ratio_product_upper {b : ℝ} (hb : b∈Icc 0 (3/5)) :
    ratio b*ratioD b/(q (U b))^2<(273/1000:ℝ) := by
  have hf := full_domain ⟨hb.1,by linarith [hb.2]⟩
  have hu := U_positive (outer_domain hf)
  have hq : 0<q (U b) := by linarith [NegativeTwo.Inverse.actual_q_positive hf]
  have hp := product_floor ⟨(source_U hb).1.le,(source_U hb).2.le⟩
  have hw : W b≤(11/10:ℝ) := by dsimp [W]; linarith [hb.2]
  have he : ratio b*ratioD b/(q (U b))^2=Q0*W b/((U b)^2*q (U b))^2 := by
    dsimp [ratio,ratioD,U,W]
    field_simp [show arc b+1/2≠0 from hu.ne',hq.ne']
    ring
  rw [he]
  apply (div_lt_iff₀ (pow_pos (by linarith : 0<(U b)^2*q (U b)) 2)).2
  have hs := mul_self_le_mul_self (by norm_num : (0:ℝ)≤199/50) hp.le
  norm_num [Q0] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerSource
