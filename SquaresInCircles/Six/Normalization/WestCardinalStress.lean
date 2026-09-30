import SquaresInCircles.Six.Normalization.CardinalGeometry
import SquaresInCircles.Six.Stress.Reverse

/-!
# Appendix A: eight directed three-square stresses

These are precisely the rational weights of the retained Appendix A. The
full far-vertex support is used on both exterior squares; it is at least as
strong as the appendix's occasional weakened primary support. Every directed
axis is included. The eight compact two-angle inequalities are proved by the
sound finite-cover checker, with concrete kernel `decide` proof bodies.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SquaresInCircles.Six.Normalization.WestCardinal
open Certificates ProofTools

/-- Weights on C--D, C--W, W--D. -/
def alphaQ : Fin 8 → ℚ := ![1/10,3/5,3/10,3/10,3/10,1/2,3/10,3/10]
def betaQ : Fin 8 → ℚ := ![3/5,1/10,9/20,9/20,9/20,1/5,9/20,9/20]
def muQ : Fin 8 → ℚ := ![3/10,3/10,1/4,1/4,1/4,3/10,1/4,1/4]

noncomputable def normal (i : Fin 8) (t u : ℝ) : Point :=
  ![(-Real.cos t,-Real.sin t),(Real.cos t,Real.sin t),
    (Real.sin t,-Real.cos t),(-Real.sin t,Real.cos t),
    (-Real.cos u,-Real.sin u),(Real.cos u,Real.sin u),
    (Real.sin u,-Real.cos u),(-Real.sin u,Real.cos u)] i

noncomputable def forceC (i : Fin 8) (t : ℝ) : Point :=
  ((alphaQ i:ℝ)+(betaQ i:ℝ)*Real.cos t,(betaQ i:ℝ)*Real.sin t)
noncomputable def forceW (i : Fin 8) (t u : ℝ) : Point :=
  (-(betaQ i:ℝ)*Real.cos t-(muQ i:ℝ)*(normal i t u).1,
   -(betaQ i:ℝ)*Real.sin t-(muQ i:ℝ)*(normal i t u).2)
noncomputable def forceD (i : Fin 8) (t u : ℝ) : Point :=
  (-(alphaQ i:ℝ)+(muQ i:ℝ)*(normal i t u).1,(muQ i:ℝ)*(normal i t u).2)

noncomputable def vertexValue (t : ℝ) (g : Point) : ℝ :=
  R0*Real.sqrt (g.1^2+g.2^2)-
    (|g.1*Real.cos t+g.2*Real.sin t|+|-g.1*Real.sin t+g.2*Real.cos t|)/2

noncomputable def threshold (i : Fin 8) (t u : ℝ) : ℝ :=
  (alphaQ i:ℝ)*(1/2+angularWidth u)+(betaQ i:ℝ)*(1/2+angularWidth t)+
    (muQ i:ℝ)*(1/2+angularWidth (u-t))

noncomputable def gap (i : Fin 8) (t u : ℝ) : ℝ :=
  threshold i t u-Stress.boxSupport c0 (forceC i t)-
    vertexValue t (forceW i t u)-vertexValue u (forceD i t u)

def normalE {n : ℕ} (i : Fin 8) (t u : Expr n) : Expr n × Expr n :=
  ![(-.cos t,-.sin t),(.cos t,.sin t),(.sin t,-.cos t),(-.sin t,.cos t),
    (-.cos u,-.sin u),(.cos u,.sin u),(.sin u,-.cos u),(-.sin u,.cos u)] i

def vertexE {n : ℕ} (t gx gy : Expr n) : Expr n :=
  .sqrt q0E * .sqrt (.sq gx+.sq gy)-
    (.abs (gx * .cos t+gy * .sin t)+.abs (-gx * .sin t+gy * .cos t))/2

def gapE (i : Fin 8) : Expr 2 :=
  let t := Expr.var 0
  let u := Expr.var 1
  let al := r (alphaQ i)
  let be := r (betaQ i)
  let mu := r (muQ i)
  let nx := (normalE i t u).1
  let ny := (normalE i t u).2
  let gcx := al+be * .cos t
  let gcy := be * .sin t
  let gwx := -be * .cos t-mu*nx
  let gwy := -be * .sin t-mu*ny
  let gdx := -al+mu*nx
  let gdy := mu*ny
  al*(r (1/2)+widthE u)+be*(r (1/2)+widthE t)+mu*(r (1/2)+widthE (u-t))-
    c0E*(.max gcx 0+.max gcy 0)-vertexE t gwx gwy-vertexE u gdx gdy

def root : RBox 2 := ![⟨-2/3,2/5⟩,⟨-2/5,2/5⟩]
def claim (i : Fin 8) : Formula 2 := .imp (.le (.var 0) (.var 1)) (.lt 0 (gapE i))

theorem checked (i : Fin 8) : certify (claim i) (fun _ => 1) 0 64 root = true := by
  fin_cases i <;> decide

noncomputable section

@[simp] lemma denote_gapE (i : Fin 8) (t u : ℝ) : Expr.denote (gapE i) ![t,u] = gap i t u := by
  fin_cases i <;> simp [gapE,gap,threshold,forceC,forceW,forceD,normalE,normal,
    alphaQ,betaQ,muQ,vertexE,vertexValue,Stress.boxSupport,Expr.denote,R0,
    widthE,angularWidth,sub_eq_add_neg,div_eq_mul_inv,mul_assoc]

lemma gap_positive (i : Fin 8) {t u : ℝ}
    (ht : -2/3 ≤ t) (hu0 : -2/5 ≤ u) (hu1 : u ≤ 2/5) (htu : t ≤ u) : 0 < gap i t u := by
  have hb : root.Mem ![t,u] := by
    intro j
    fin_cases j <;> norm_num [root,RInterval.Mem] <;> constructor <;> linarith
  have hh := certify_sound (claim i) (fun _ => 1) 0 64 (checked i) hb
  have hr := hh htu
  simpa [claim,Formula.Holds,Expr.denote] using hr

/-- The incidence system uses the actual three directed separations. -/
def system (i : Fin 8) (t u : ℝ) : Stress.System 3 3 where
  source := ![0,0,1]
  target := ![2,1,2]
  normal := ![(-1,0),(-Real.cos t,-Real.sin t),normal i t u]
  weight := ![(alphaQ i:ℝ),(betaQ i:ℝ),(muQ i:ℝ)]
  threshold := ![1/2+angularWidth u,1/2+angularWidth t,1/2+angularWidth (u-t)]

lemma system_nonnegative (i : Fin 8) (t u : ℝ) : (system i t u).Nonnegative := by
  intro e
  fin_cases i <;> fin_cases e <;> norm_num [system,alphaQ,betaQ,muQ]

lemma system_force (i : Fin 8) (t u : ℝ) (j : Fin 3) :
    (system i t u).force j = ![forceC i t,forceW i t u,forceD i t u] j := by
  fin_cases j <;> apply Prod.ext <;>
    simp [Stress.System.force,system,forceC,forceW,forceD,Fin.sum_univ_succ] <;> ring

lemma system_threshold (i : Fin 8) (t u : ℝ) : (system i t u).thresholdSum=threshold i t u := by
  simp [Stress.System.thresholdSum,system,threshold,Fin.sum_univ_succ]
  ring

lemma normal_eq_pairNormal (i : Fin 8) (t u a b A B : ℝ) :
    normal i t u = Stress.pairNormal i (orientedSquare (Real.pi+t) a b)
      (orientedSquare (Real.pi+u) A B) := by
  fin_cases i <;> apply Prod.ext <;>
    simp [normal,Stress.pairNormal,normalX,normalY,orientedSquare,scale,
      Real.cos_pi_add,Real.sin_pi_add]

lemma vertexValue_eq_support (t a b : ℝ) (g : Point) :
    vertexValue t g = Stress.vertexSupport R0 (orientedSquare (Real.pi+t) a b) g := by
  have hx : frameX (orientedSquare (Real.pi+t) a b) g =
      -(g.1*Real.cos t+g.2*Real.sin t) := by
    simp only [frameX,orientedSquare,Real.cos_pi_add,Real.sin_pi_add]
    ring
  have hy : frameY (orientedSquare (Real.pi+t) a b) g =
      -(-g.1*Real.sin t+g.2*Real.cos t) := by
    simp only [frameY,orientedSquare,Real.cos_pi_add,Real.sin_pi_add]
    ring
  simp only [Stress.vertexSupport,Stress.vectorLength,width,hx,hy,abs_neg,normSq,vertexValue]

/-- Appendix A's actual geometric exclusion on its full compact triangle. -/
theorem impossible {c : Point} {t u a b A B : ℝ}
    (hc : (0 ≤ c.1 ∧ c.1 ≤ c0) ∧ (0 ≤ c.2 ∧ c.2 ≤ c0))
    (hW : ContainedChart a |b|) (hD : ContainedChart A |B|)
    (ht : -2/3 ≤ t) (hu0 : -2/5 ≤ u) (hu1 : u ≤ 2/5) (htu : t ≤ u)
    (hCW : 0 ≤ centralMargin .own (Real.pi+t) a b c.1 c.2)
    (hCD : 0 ≤ centralMargin .west (Real.pi+u) A B c.1 c.2)
    (hWD : ∀ p, ¬ (openSquare (orientedSquare (Real.pi+t) a b) p ∧
      openSquare (orientedSquare (Real.pi+u) A B) p)) : False := by
  obtain ⟨i,hi⟩ := Stress.directed_pair_separator
    (orientedSquare (Real.pi+t) a b) (orientedSquare (Real.pi+u) A B) hWD
  rw [← normal_eq_pairNormal i t u a b A B,oriented_pair_threshold] at hi
  have hdelta : (Real.pi+u)-(Real.pi+t)=u-t := by ring
  rw [hdelta] at hi
  let S : Fin 3 → UnitSquare :=
    ![axisSquare c,orientedSquare (Real.pi+t) a b,orientedSquare (Real.pi+u) A B]
  let U : Fin 3 → ℝ := ![Stress.boxSupport c0 (forceC i t),
    vertexValue t (forceW i t u),vertexValue u (forceD i t u)]
  have hseps : (system i t u).Separates S := by
    intro e
    fin_cases e
    · dsimp [system,S]
      simp only [centralMargin,centerX,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
        abs_neg] at hCD
      dsimp [dot,sub,orientedSquare,axisSquare]
      simp only [Real.cos_pi_add,Real.sin_pi_add]
      dsimp [angularWidth]
      nlinarith
    · dsimp [system,S]
      have hproj := primary_difference (Real.pi+t) a b c.1 c.2
      have he : dot (-Real.cos t,-Real.sin t)
          (sub (orientedSquare (Real.pi+t) a b).center c) = a-centralNormal (Real.pi+t) c.1 c.2 := by
        simpa [frameX,orientedSquare,dot,Real.cos_pi_add,Real.sin_pi_add] using hproj
      rw [he]
      simp only [centralMargin,angularWidth,Real.cos_pi_add,Real.sin_pi_add,abs_neg] at hCW
      dsimp [angularWidth]
      linarith
    · exact hi
  have hsupport (j : Fin 3) : dot ((system i t u).force j) (S j).center ≤ U j := by
    rw [system_force]
    fin_cases j
    · exact Stress.center_le_boxSupport hc (forceC i t)
    · rw [vertexValue_eq_support]
      exact Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hW) _
    · rw [vertexValue_eq_support]
      exact Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hD) _
  have hnonpos := (system i t u).defect_nonpos S U (system_nonnegative i t u) hseps hsupport
  rw [system_threshold] at hnonpos
  have hsum : (∑ j, U j) = Stress.boxSupport c0 (forceC i t)+
      vertexValue t (forceW i t u)+vertexValue u (forceD i t u) := by
    simp [U,Fin.sum_univ_succ]
    ring
  rw [hsum] at hnonpos
  have hpos := gap_positive i ht hu0 hu1 htu
  dsimp [gap] at hpos
  linarith

end
end SquaresInCircles.Six.Normalization.WestCardinal
