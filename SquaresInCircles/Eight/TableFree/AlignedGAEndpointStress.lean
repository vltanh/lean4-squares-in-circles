module

public import SquaresInCircles.Eight.TableFree.AlignedGAEndpointPolynomial
public import SquaresInCircles.Eight.TableFree.AlignedCycleBounds

/-!
# Actual five-anchor exclusion of the wrong GA/DE endpoint

Uncompiled draft.  The unchanged G/T coordinates are canceled first.
The five actual circle inequalities are then used once each, with the
explicit positive masses.  The polynomial theorem proves positivity of
the same stress defect for every positive sine in the complete domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace AlignedGAEndpointStress
open Polynomial AlignedGAEndpointPolynomial

def a (s : ℝ) : ℝ := aeval s aP
def beta (s : ℝ) : ℝ := aeval s betaP
def delta (s : ℝ) : ℝ := aeval s deltaP
def epsilon (s : ℝ) : ℝ := aeval s epsilonP
def massA (s : ℝ) : ℝ := aeval s massAP
def massB (s : ℝ) : ℝ := aeval s massBP
def massD (s : ℝ) : ℝ := aeval s massDP
def massH (s : ℝ) : ℝ := aeval s massHP
def massE (s : ℝ) : ℝ := aeval s massEP
def den (s : ℝ) : ℝ := 4*massA s*massB s*massD s*massH s*massE s

structure Positive (s : ℝ) : Prop where
  a_pos : 0<a s
  beta_pos : 0<beta s
  delta_pos : 0<delta s
  epsilon_pos : 0<epsilon s
  A_pos : 0< massA s
  B_pos : 0< massB s
  D_pos : 0< massD s
  H_pos : 0< massH s
  E_pos : 0< massE s

theorem positive {s : ℝ} (hs : s∈Ioc 0 (11/50 : ℝ)) : Positive s := by
  have h2 := pow_le_pow_left₀ hs.1.le hs.2 2
  have h3 := pow_le_pow_left₀ hs.1.le hs.2 3
  have h2n := pow_nonneg hs.1.le 2
  have h3n := pow_nonneg hs.1.le 3
  have hEbase : 0<38/125-(47/250)*s+(11/100)*s^2-(11/250)*s^3 := by
    nlinarith [hs.2]
  have hE : 0< massE s := by
    have hp := mul_pos hs.1 hEbase
    norm_num [massE,massEP] at hp ⊢
    nlinarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hE⟩ <;>
    norm_num [a,beta,delta,epsilon,massA,massB,massD,massH,
      aP,betaP,deltaP,epsilonP,massAP,massBP,massDP,massHP] <;>
    nlinarith [hs.1,hs.2]

theorem den_pos {s : ℝ} (hp : Positive s) : 0<den s := by
  exact mul_pos (mul_pos (mul_pos (mul_pos
    (mul_pos (by norm_num : (0:ℝ)<4) hp.A_pos) hp.B_pos) hp.D_pos) hp.H_pos) hp.E_pos

def defect (s c : ℝ) : ℝ :=
  3+2*a s+2*beta s+2*delta s+epsilon s+beta s*c+epsilon s*s-
    qCap*(massA s+massB s+massD s+massH s+massE s)-
    (1+a s^2)/(4*massA s)-
    (beta s^2+a s^2-2*a s*beta s*s)/(4*massB s)-
    (delta s^2+beta s^2)/(4*massD s)-
    (epsilon s^2+1)/(4*massH s)-
    (delta s^2+epsilon s^2-2*delta s*epsilon s*c)/(4*massE s)

theorem cleared_defect {s : ℝ} (hp : Positive s) (c : ℝ) :
    den s*defect s c=aeval s constantNumerator+aeval s cosineNumerator*c := by
  have hA := hp.A_pos.ne'
  have hB := hp.B_pos.ne'
  have hD := hp.D_pos.ne'
  have hH := hp.H_pos.ne'
  have hE := hp.E_pos.ne'
  simp only [defect,den,a,beta,delta,epsilon,massA,massB,massD,massH,massE] at hA hB hD hH hE ⊢
  simp only [constantNumerator,cosineNumerator,denominator,map_add,map_sub,map_mul,map_pow,
    map_one,aeval_C,aeval_X,eq_ratCast,qCap]
  push_cast
  field_simp
  ring

theorem cosineNumerator_pos {s : ℝ} (hp : Positive s) : 0<aeval s cosineNumerator := by
  simp only [cosineNumerator,denominator,map_add,map_mul,aeval_C]
  change 0<den s*beta s+2*delta s*epsilon s*massA s*massB s*massD s*massH s
  have hfirst := mul_pos (den_pos hp) hp.beta_pos
  have hsecond := mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
    (mul_pos (by norm_num : (0:ℝ)<2) hp.delta_pos) hp.epsilon_pos) hp.A_pos)
    hp.B_pos) hp.D_pos) hp.H_pos
  exact add_pos hfirst hsecond

theorem defect_positive {s c : ℝ} (hs : s∈Ioc 0 (11/50 : ℝ))
    (hc : 0≤c) (hunit : c^2+s^2=1) : 0<defect s c := by
  have hp := positive hs
  have hP := P_positive hs
  have hC := cosine_lower ⟨hs.1.le,hs.2⟩ hc hunit
  have hcoef := cosineNumerator_pos hp
  have hprod := mul_le_mul_of_nonneg_left hC hcoef.le
  have hPeq : aeval s P=aeval s constantNumerator+
      aeval s cosineNumerator*(1-s^2/2-(13/100)*s^4) := by
    simp only [P,cosineLower,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
      eq_ratCast]
    push_cast
    ring
  have hden : 0<den s*defect s c := by
    rw [cleared_defect hp c]
    rw [hPeq] at hP
    linarith
  exact (mul_pos_iff_of_pos_left (den_pos hp)).mp hden

def support (m X Y : ℝ) : ℝ := m*qCap+(X^2+Y^2)/(4*m)-(X+Y)/2

theorem quadratic_support {P : SignedPoint} {m : ℝ}
    (hm : 0< m) (hy : 0≤P.y) (hc : P.circle≤qCap) (X Y : ℝ) :
    X*P.a+Y*P.y≤ support m X Y := by
  have hcircle : (P.a+1/2)^2+(P.y+1/2)^2≤qCap := by
    simpa [SignedPoint.circle,abs_of_nonneg hy] using hc
  have hmul := mul_le_mul_of_nonneg_left hcircle (show 0≤4*m^2 by positivity)
  have hsqX := sq_nonneg (2*m*(P.a+1/2)-X)
  have hsqY := sq_nonneg (2*m*(P.y+1/2)-Y)
  have hid : 4*m*support m X Y=4*m^2*qCap+X^2+Y^2-2*m*(X+Y) := by
    dsimp [support]
    field_simp
    ring
  apply le_of_mul_le_mul_left _ (show (0:ℝ)<4*m by linarith)
  rw [hid]
  generalize qCap=Q at hmul ⊢
  linarith

theorem defect_support_identity {s c : ℝ} (hunit : c^2+s^2=1) :
    defect s c=
      2+a s+beta s+delta s+(beta s+epsilon s)*(1+c+s)/2-
        (support (massA s) 1 (a s)+
        support (massB s) (beta s*c) (a s-beta s*s)+
        support (massD s) (delta s) (beta s)+
        support (massH s) (epsilon s) 1+
        support (massE s) (epsilon s*s) (delta s-epsilon s*c)) := by
  have hB : (beta s*c)^2+(a s-beta s*s)^2=beta s^2+a s^2-2*a s*beta s*s := by
    linear_combination beta s^2*hunit
  have hE : (epsilon s*s)^2+(delta s-epsilon s*c)^2=
      delta s^2+epsilon s^2-2*delta s*epsilon s*c := by
    linear_combination epsilon s^2*hunit
  dsimp [support]
  rw [hB,hE]
  dsimp [defect]
  ring

/-- The actual five shared circles imply the nonpositive stress.  The
free G/T points have already canceled in the displayed composites. -/
theorem five_anchor_defect {H A B D E : SignedPoint} {s c : ℝ}
    (hs : s∈Ioc 0 (11/50 : ℝ)) (hunit : c^2+s^2=1)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hcH : H.circle≤qCap) (hcA : A.circle≤qCap) (hcB : B.circle≤qCap)
    (hcD : D.circle≤qCap) (hcE : E.circle≤qCap)
    (hHA : 2≤H.y+A.a) (hAB : 1≤A.y+B.y)
    (hBD : 1+(1+c+s)/2≤c*B.a-s*B.y+D.y)
    (hDE : 1≤D.a+E.y) (hEH : (1+c+s)/2≤H.a+s*E.a-c*E.y) :
    defect s c≤0 := by
  have hp := positive hs
  have hABw := mul_le_mul_of_nonneg_left hAB hp.a_pos.le
  have hBDw := mul_le_mul_of_nonneg_left hBD hp.beta_pos.le
  have hDEw := mul_le_mul_of_nonneg_left hDE hp.delta_pos.le
  have hEHw := mul_le_mul_of_nonneg_left hEH hp.epsilon_pos.le
  have hA := quadratic_support hp.A_pos hyA hcA 1 (a s)
  have hB := quadratic_support hp.B_pos hyB hcB (beta s*c) (a s-beta s*s)
  have hD := quadratic_support hp.D_pos hyD hcD (delta s) (beta s)
  have hH := quadratic_support hp.H_pos hyH hcH (epsilon s) 1
  have hE := quadratic_support hp.E_pos hyE hcE (epsilon s*s) (delta s-epsilon s*c)
  rw [defect_support_identity hunit]
  nlinarith

theorem five_anchor_impossible {H A B D E : SignedPoint} {s c : ℝ}
    (hs : s∈Ioc 0 (11/50 : ℝ)) (hc : 0≤c) (hunit : c^2+s^2=1)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hcH : H.circle≤qCap) (hcA : A.circle≤qCap) (hcB : B.circle≤qCap)
    (hcD : D.circle≤qCap) (hcE : E.circle≤qCap)
    (hHA : 2≤H.y+A.a) (hAB : 1≤A.y+B.y)
    (hBD : 1+(1+c+s)/2≤c*B.a-s*B.y+D.y)
    (hDE : 1≤D.a+E.y) (hEH : (1+c+s)/2≤H.a+s*E.a-c*E.y) : False := by
  have hn := five_anchor_defect hs hunit hyH hyA hyB hyD hyE hcH hcA hcB hcD hcE
    hHA hAB hBD hDE hEH
  exact not_lt_of_ge hn (defect_positive hs hc hunit)

end AlignedGAEndpointStress

namespace SignedCycle
open Candidate

/-- The wrong endpoint is excluded for actual original mixed axes and
all radial slack.  The zero-angle endpoint is included separately. -/
theorem HardInput.aligned_GA_DE_impossible {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hAH : I.cycle.theta A=I.cycle.theta H)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (horder : I.cycle.theta D≤I.cycle.theta A)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  have hb := I.aligned_bounds hq hHG hAB hTD hAH.le horder
  have hcomp := I.aligned_composites hHG hAB hTD
  have hnD : next D=E := rfl
  have hnE : next E=H := rfl
  set α := I.cycle.theta H-I.cycle.theta D with hαdef
  have hα : α∈Ico 0 (11/50 : ℝ) := ⟨hb.span_nonneg,hb.span_lt⟩
  have hHA : 2≤(I.cycle.point H).y+(I.cycle.point A).a := by
    have h := hcomp.1
    rw [hAH,sub_self,edgeWidth_zero,Real.cos_zero,Real.sin_zero] at h
    linarith
  have hAB' : 1≤(I.cycle.point A).y-(I.cycle.point B).y := hcomp.2.2
  have hBD : 1+edgeWidth α≤
      (I.cycle.point B).a*Real.cos α+(I.cycle.point B).y*Real.sin α-(I.cycle.point D).y := by
    have h := hcomp.2.1
    rw [hAH,← hαdef] at h
    linarith
  have hDE' : 1≤(I.cycle.point D).a-(I.cycle.point E).y := by
    have hf := hDE
    rw [Feasible,slack,edge,ite_eq_right (show ¬Candidate.word D=0 by decide),delta,hnD,hED,
      sub_self,edgeWidth_zero] at hf
    simp [quarterProjection] at hf
    linarith
  have hEH' : edgeWidth α≤(I.cycle.point H).a+
      (I.cycle.point E).a*Real.sin α+(I.cycle.point E).y*Real.cos α := by
    have hf := hEH
    rw [Feasible,slack,edge,ite_eq_right (show ¬Candidate.word E=0 by decide),delta,hnE,hED,
      ← hαdef] at hf
    simp [quarterProjection] at hf
    linarith
  rcases lt_or_eq_of_le hα.1 with hpos | hzero
  · have hwide : α∈Icc 0 (7/10 : ℝ) := ⟨hα.1,by linarith [hα.2]⟩
    have hs : Real.sin α∈Ioc 0 (11/50 : ℝ) :=
      ⟨Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [hα.2,Real.pi_gt_three]),
        (Real.sin_le hα.1).trans hα.2.le⟩
    have hc : 0≤Real.cos α := by linarith [(transport_trig hwide).1]
    rw [edgeWidth_positive_formula hwide] at hBD hEH'
    exact AlignedGAEndpointStress.five_anchor_impossible
      (H := I.cycle.point H) (A := I.cycle.point A)
      (B := (I.cycle.point B).reflect) (D := (I.cycle.point D).reflect)
      (E := (I.cycle.point E).reflect) hs hc (Real.cos_sq_add_sin_sq α)
      I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg
      (by simp only [SignedPoint.reflect]; linarith [I.anchors_normal.B_nonpos])
      (by simp only [SignedPoint.reflect]; linarith [I.anchors_normal.D_nonpos])
      (by simp only [SignedPoint.reflect]; linarith [I.E_nonpos])
      (le_trans (I.necessary.contained H) hq) (le_trans (I.necessary.contained A) hq)
      (by rw [SignedPoint.reflect_circle]; exact le_trans (I.necessary.contained B) hq)
      (by rw [SignedPoint.reflect_circle]; exact le_trans (I.necessary.contained D) hq)
      (by rw [SignedPoint.reflect_circle]; exact le_trans (I.necessary.contained E) hq) hHA
      (by simp only [SignedPoint.reflect]; linarith)
      (by simp only [SignedPoint.reflect]; linarith)
      (by simp only [SignedPoint.reflect]; linarith)
      (by simp only [SignedPoint.reflect]; linarith)
  · have hz : α=0 := hzero.symm
    rw [hz,edgeWidth_zero,Real.sin_zero,Real.cos_zero] at hEH'
    have hsum := hb.primary_sum
    rw [← hαdef,hz,Real.sin_zero] at hsum
    linarith

end SignedCycle
end SquaresInCircles.Eight.TableFree
