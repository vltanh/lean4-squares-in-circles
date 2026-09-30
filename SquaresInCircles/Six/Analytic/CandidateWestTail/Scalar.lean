module
public import SquaresInCircles.Six.Analytic.LowDWestSource.Scalar

@[expose] public section

/-!
# A whole-domain scalar obstruction for the candidate west tail

The stress has central weights 109/200 and 47/250 and wing weights 169/1000
and 49/500. A global affine majorant of the diagonal resultant, rather than a
support-branch partition, leaves a sum of first harmonics. Three kinds encode
OWN S, nonnegative cardinal S, and negative cardinal S. The latter uses x=-s.

Each coordinate slice is a constant plus A cos x+B sin x with A,B>=0 on the
entire physical rectangle. Thus its minimum is at a corner. The 24 corners
below are exactly two endpoints in each of three coordinates and three
geometric central/sign choices; they are not a searched subdivision or a
stress-row table. Each endpoint uses the displayed Taylor polynomials.

The rational diagonal bound d<=11/14 only enlarges d<=pi/4. The OWN S bound
s<=3/5 will be supplied by the shared-center OWN/OWN budget in Geometry.lean.
Compilation and kernel acceptance remain deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CandidateWestTail

/-- 0: OWN S; 1: cardinal S>=0; 2: cardinal S<=0, with x=-s. -/
def side (k : Fin 3) : ℝ := ![1,1,-1] k
def xMax (k : Fin 3) : ℝ := ![3/5,3/5,2/5] k
def gCoeff (k : Fin 3) : ℝ := ![47/500,47/250,47/250] k
def hCoeff (k : Fin 3) : ℝ := ![18001/156250,7336967/50000000,2063033/50000000] k
def offset (k : Fin 3) : ℝ := ![0,-47/500,-47/500] k

def minorant (k : Fin 3) (v x d : ℝ) : ℝ :=
  -27197287317/50000000000+offset k+
    (2110131/10000000)*Real.cos v+(109/400)*Real.sin v+
    gCoeff k*Real.cos x+hCoeff k*Real.sin x+
    (169/2000)*(Real.cos (v+d)+Real.sin (v+d))+
    (49/1000)*(Real.cos (d-side k*x)+Real.sin (d-side k*x))-
    (9514611/125000000)*Real.sin (v+side k*x)

private lemma trig_small {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 2/3) :
    7/9 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ 2/3 := by
  have hs := mul_nonneg (sub_nonneg.mpr hx.2)
    (show 0 ≤ (2:ℝ)/3+x by linarith [hx.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  exact ⟨by nlinarith,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2]),
    (Real.sin_le hx.1).trans hx.2⟩

private lemma trig_x {k : Fin 3} {x : ℝ} (hx : 0 ≤ x ∧ x ≤ xMax k) :
    41/50 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ 3/5 := by
  have hmax : xMax k ≤ 3/5 := by fin_cases k <;> norm_num [xMax]
  have hx1 : x ≤ 3/5 := hx.2.trans hmax
  have hsq := mul_nonneg (sub_nonneg.mpr hx1)
    (show 0 ≤ (3:ℝ)/5+x by linarith [hx.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  exact ⟨by nlinarith,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx1,Real.pi_gt_d2]),
    (Real.sin_le hx.1).trans hx1⟩

private lemma trig_d {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ Real.cos d ∧ 23/48 ≤ Real.sin d := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hs := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos])
    (show d ≤ Real.pi/2 by linarith [hd.2,Real.pi_gt_d2]) hd.1
  exact ⟨hc,by nlinarith⟩

private def vA (k : Fin 3) (x d : ℝ) : ℝ :=
  2110131/10000000+(169/2000)*(Real.cos d+Real.sin d)-
    (9514611/125000000)*side k*Real.sin x
private def vB (x d : ℝ) : ℝ :=
  109/400+(169/2000)*(Real.cos d-Real.sin d)-(9514611/125000000)*Real.cos x
private def vK (k : Fin 3) (x d : ℝ) : ℝ :=
  -27197287317/50000000000+offset k+gCoeff k*Real.cos x+hCoeff k*Real.sin x+
    (49/1000)*(Real.cos (d-side k*x)+Real.sin (d-side k*x))

private def xA (k : Fin 3) (v d : ℝ) : ℝ :=
  gCoeff k+(49/1000)*(Real.cos d+Real.sin d)-(9514611/125000000)*Real.sin v
private def xB (k : Fin 3) (v d : ℝ) : ℝ :=
  hCoeff k+side k*((49/1000)*(Real.sin d-Real.cos d)-(9514611/125000000)*Real.cos v)
private def xK (k : Fin 3) (v d : ℝ) : ℝ :=
  -27197287317/50000000000+offset k+
    (2110131/10000000)*Real.cos v+(109/400)*Real.sin v+
    (169/2000)*(Real.cos (v+d)+Real.sin (v+d))

private def dA (k : Fin 3) (v x : ℝ) : ℝ :=
  (169/2000)*(Real.cos v+Real.sin v)+(49/1000)*(Real.cos x-side k*Real.sin x)
private def dB (k : Fin 3) (v x : ℝ) : ℝ :=
  (169/2000)*(Real.cos v-Real.sin v)+(49/1000)*(Real.cos x+side k*Real.sin x)
private def dK (k : Fin 3) (v x : ℝ) : ℝ :=
  -27197287317/50000000000+offset k+
    (2110131/10000000)*Real.cos v+(109/400)*Real.sin v+
    gCoeff k*Real.cos x+hCoeff k*Real.sin x-
    (9514611/125000000)*Real.sin (v+side k*x)

private lemma v_identity (k : Fin 3) (v x d : ℝ) :
    minorant k v x d=vK k x d+vA k x d*Real.cos v+vB x d*Real.sin v := by
  fin_cases k <;>
    simp [minorant,vK,vA,vB,side,Real.cos_add,Real.sin_add,Real.sin_neg,Real.cos_neg] <;> ring

private lemma x_identity (k : Fin 3) (v x d : ℝ) :
    minorant k v x d=xK k v d+xA k v d*Real.cos x+xB k v d*Real.sin x := by
  fin_cases k <;>
    simp [minorant,xK,xA,xB,side,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
      Real.sin_neg,Real.cos_neg] <;> ring

private lemma d_identity (k : Fin 3) (v x d : ℝ) :
    minorant k v x d=dK k v x+dA k v x*Real.cos d+dB k v x*Real.sin d := by
  fin_cases k <;>
    simp [minorant,dK,dA,dB,side,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
      Real.sin_neg,Real.cos_neg] <;> ring

private lemma v_coefficients (k : Fin 3) {x d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ xMax k) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ vA k x d ∧ 0 ≤ vB x d := by
  have tx := trig_x hx
  have td := trig_d hd
  fin_cases k <;> dsimp [vA,vB,side] <;> constructor <;>
    nlinarith [Real.sin_le_one x,Real.cos_le_one x,Real.sin_le_one d]

private lemma x_coefficients (k : Fin 3) {v d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ xA k v d ∧ 0 ≤ xB k v d := by
  have tv := trig_small ⟨by linarith [hv.1],hv.2⟩
  have td := trig_d hd
  fin_cases k <;> dsimp [xA,xB,gCoeff,hCoeff,side] <;> constructor <;>
    nlinarith [Real.cos_le_one v,Real.cos_le_one d,Real.sin_le_one d]

private lemma d_coefficients (k : Fin 3) {v x : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k) :
    0 ≤ dA k v x ∧ 0 ≤ dB k v x := by
  have tv := trig_small ⟨by linarith [hv.1],hv.2⟩
  have tx := trig_x hx
  fin_cases k <;> dsimp [dA,dB,side] <;> constructor <;> nlinarith

private lemma extend_trig {A B K l u x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 ≤ l) (hu : u ≤ Real.pi/2)
    (hx : l ≤ x ∧ x ≤ u)
    (hleft : 0 < K+A*Real.cos l+B*Real.sin l)
    (hright : 0 < K+A*Real.cos u+B*Real.sin u) :
    0 < K+A*Real.cos x+B*Real.sin x := by
  have h := trig_lower_of_endpoints hA hB hl hu hx (C := -K)
    (by linarith) (by linarith)
  linarith

private lemma extend_v (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hleft : 0 < minorant k (11/25) x d) (hright : 0 < minorant k (2/3) x d) :
    0 < minorant k v x d := by
  rw [v_identity] at hleft hright ⊢
  have h := v_coefficients k hx hd
  exact extend_trig h.1 h.2 (by norm_num) (by linarith [Real.pi_gt_d2]) hv hleft hright

private lemma extend_x (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hleft : 0 < minorant k v 0 d) (hright : 0 < minorant k v (xMax k) d) :
    0 < minorant k v x d := by
  rw [x_identity] at hleft hright ⊢
  have h := x_coefficients k hv hd
  have hup : xMax k ≤ Real.pi/2 := by fin_cases k <;> norm_num [xMax] <;> linarith [Real.pi_gt_d2]
  exact extend_trig h.1 h.2 (by norm_num) hup hx hleft hright

private lemma extend_d (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hleft : 0 < minorant k v x (1/2)) (hright : 0 < minorant k v x (11/14)) :
    0 < minorant k v x d := by
  rw [d_identity] at hleft hright ⊢
  have h := d_coefficients k hv hx
  exact extend_trig h.1 h.2 (by norm_num) (by linarith [Real.pi_gt_d2]) hd hleft hright

private def cosLower (x : ℝ) := 1-x^2/2+x^4/24-x^6/720
private def sinLower (x : ℝ) :=
  if 0 ≤ x then x-x^3/6+x^5/120-x^7/5040 else x-x^3/6+x^5/120
private def sinUpper (x : ℝ) :=
  if 0 ≤ x then x-x^3/6+x^5/120 else x-x^3/6+x^5/120-x^7/5040

private lemma cos_lower (x : ℝ) : cosLower x ≤ Real.cos x := by
  by_cases hx : 0 ≤ x
  · exact Seven.cos_lower_six hx
  · have h := Seven.cos_lower_six (x := -x) (by linarith)
    simpa [cosLower,Real.cos_neg] using h

private lemma sin_bracket (x : ℝ) : sinLower x ≤ Real.sin x ∧ Real.sin x ≤ sinUpper x := by
  by_cases hx : 0 ≤ x
  · simp only [sinLower,sinUpper,if_pos hx]
    exact ⟨Seven.sin_lower_seven hx,Seven.sin_upper_five hx⟩
  · have hl := Seven.sin_lower_seven (x := -x) (by linarith)
    have hu := Seven.sin_upper_five (x := -x) (by linarith)
    simp only [Real.sin_neg] at hl hu
    simp only [sinLower,sinUpper,if_neg hx]
    constructor <;> nlinarith only [hl,hu]

private def polynomialLower (k : Fin 3) (v x d : ℝ) : ℝ :=
  -27197287317/50000000000+offset k+
    (2110131/10000000)*cosLower v+(109/400)*sinLower v+
    gCoeff k*cosLower x+hCoeff k*sinLower x+
    (169/2000)*(cosLower (v+d)+sinLower (v+d))+
    (49/1000)*(cosLower (d-side k*x)+sinLower (d-side k*x))-
    (9514611/125000000)*sinUpper (v+side k*x)

private lemma polynomial_le (k : Fin 3) (v x d : ℝ) :
    polynomialLower k v x d ≤ minorant k v x d := by
  have cv := cos_lower v
  have sv := (sin_bracket v).1
  have cx := cos_lower x
  have sx := (sin_bracket x).1
  have cq := cos_lower (v+d)
  have sq := (sin_bracket (v+d)).1
  have cr := cos_lower (d-side k*x)
  have sr := (sin_bracket (d-side k*x)).1
  have sz := (sin_bracket (v+side k*x)).2
  fin_cases k <;> dsimp [polynomialLower,minorant,gCoeff,hCoeff] <;>
    nlinarith only [cv,sv,cx,sx,cq,sq,cr,sr,sz]

private def vEnd (i : Fin 2) : ℝ := ![11/25,2/3] i
private def xEnd (k : Fin 3) (i : Fin 2) : ℝ := ![0,xMax k] i
private def dEnd (i : Fin 2) : ℝ := ![1/2,11/14] i

/-- Explicit rational endpoint arithmetic after the concavity reduction. -/
private lemma corners (k : Fin 3) (i j l : Fin 2) :
    0 < minorant k (vEnd i) (xEnd k j) (dEnd l) := by
  have h := polynomial_le k (vEnd i) (xEnd k j) (dEnd l)
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals norm_num [polynomialLower,cosLower,sinLower,sinUpper,gCoeff,hCoeff,
    offset,side,vEnd,xEnd,xMax,dEnd] at h ⊢
  all_goals linarith

/-- The full rectangle follows from concavity in each of its three coordinates. -/
theorem positive (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : 0 < minorant k v x d := by
  have hvEnd (i : Fin 2) : 11/25 ≤ vEnd i ∧ vEnd i ≤ 2/3 := by
    fin_cases i <;> norm_num [vEnd]
  have hxEnd (j : Fin 2) : 0 ≤ xEnd k j ∧ xEnd k j ≤ xMax k := by
    fin_cases k <;> fin_cases j <;> norm_num [xEnd,xMax]
  have alongD (i j : Fin 2) : 0 < minorant k (vEnd i) (xEnd k j) d :=
    extend_d k (hvEnd i) (hxEnd j) hd (corners k i j 0) (corners k i j 1)
  have alongX (i : Fin 2) : 0 < minorant k (vEnd i) x d :=
    extend_x k (hvEnd i) hx hd (alongD i 0) (alongD i 1)
  exact extend_v k hv hx hd (alongX 0) (alongX 1)

end SquaresInCircles.Six.Analytic.CandidateWestTail
