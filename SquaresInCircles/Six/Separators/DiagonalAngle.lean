import SquaresInCircles.Six.Separators.DiagonalAngleOwn

/-!
# Six squares: the angle of D exceeds 1/2

In a normalized packing the angle `d` of D is more than `1/2`. For W on its own
axis this is `own_west_diagonal_gt_half`. For W on the west side of C, at the
angle `w ∈ [-2/5, 2/5]`, suppose `d ≤ 1/2`; then `w ≤ d`, and W–D is separated
along the secondary axis of W or of D. The stress with weights
`(35, 40, 25)/100` or `(43, 30, 27)/100` on C–D, C–W and W–D has a nonpositive
slack, while the far-vertex supports bound it below by `gap`: a constant plus
functions of `w`, of `d` and of `d - w`, in which the length
`√(p² + q² + 2pq sin x)` of a rotating force is replaced by its tangent at a
rational `c²`. Each of these functions is a first harmonic, concave where its
harmonic part is nonnegative, so the gap is concave in `w`, in `d` and along the
edge `d = w`, and it is positive at the six vertices of the domain, by Taylor
brackets.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-- The tangent majorant `(p² + q² + 2pq sin x + c²)/(2c)` of the length
`√(p² + q² + 2pq sin x)` of a rotating force. -/
def rotTangent (p q c x : ℝ) : ℝ := (p^2+q^2+2*p*q*Real.sin x+c^2)/(2*c)

lemma rotTangent_eq (p q c x : ℝ) :
    rotTangent p q c x=(p^2+q^2+c^2)/(2*c)+(p*q/c)*Real.sin x := by
  unfold rotTangent
  ring

/-- A force `(U, V)` with `U² + V² = p² + q² + 2pq sin x` has length at most its
tangent majorant. -/
lemma rotTangent_bound {p q c x U V : ℝ} (hc : 0<c)
    (hUV : U^2+V^2=p^2+q^2+2*p*q*Real.sin x) :
    0≤rotTangent p q c x ∧ U^2+V^2≤(rotTangent p q c x)^2 := by
  have hy : 0≤p^2+q^2+2*p*q*Real.sin x := by rw [← hUV]; positivity
  exact ⟨div_nonneg (by positivity) (by linarith),hUV ▸ sq_le_tangent_sq hc⟩

namespace DiagonalAngle.Side

/-! W lies on the west side of C at the angle `w`, D at the angle `d`, and W–D
is separated along the secondary axis of D (`ds`) or of W. The weights are
`alpha`, `beta` and `mu` on C–D, C–W and W–D; after the far-vertex supports the
gap `gap ds w d` is the constant `constant` plus the terms `westTerm` in `w`,
`diagonalTerm` in `d` and `relativeTerm` in `d - w`, with the tangent majorants
of the lengths of the forces. On either side of `w = 0` it is `signedGap`. -/

def alpha (ds : Bool) : ℝ := if ds then 43/100 else 35/100
def beta (ds : Bool) : ℝ := if ds then 30/100 else 40/100
def mu (ds : Bool) : ℝ := if ds then 27/100 else 25/100

def constant (ds : Bool) : ℝ :=
  1-0.613*beta ds-(if ds then 1.689*(51/100) else 0)
/-- The terms of the gap in `w`, with `|sin w| = sin w` if `positive`. -/
def westTerm (ds positive : Bool) (w : ℝ) : ℝ :=
  beta ds*Real.cos w+(if positive then beta ds*Real.sin w else 0)-
    (if ds then 0 else 1.689*rotTangent (40/100) (25/100) (12/25) w)
/-- The terms of the gap in `d`. -/
def diagonalTerm (ds : Bool) (d : ℝ) : ℝ :=
  alpha ds*0.387*(Real.cos d+Real.sin d)-
    (if ds then 1.689*rotTangent (30/100) (27/100) (9/20) d else 0)
/-- The terms of the gap in `q = d - w`. -/
def relativeTerm (ds : Bool) (q : ℝ) : ℝ :=
  mu ds*(Real.cos q+Real.sin q)-
    (if ds then 0 else 1.689*rotTangent (35/100) (25/100) (1/2) q)

/-- The gap after the supports, for a sign of `w`. -/
def signedGap (ds positive : Bool) (w d : ℝ) : ℝ :=
  constant ds+westTerm ds positive w+diagonalTerm ds d+relativeTerm ds (d-w)

/-- The gap after the supports, for W on the west side of C at the angle `w`. -/
def gap (ds : Bool) (w d : ℝ) : ℝ :=
  if 0≤w then signedGap ds true w d else signedGap ds false w d

lemma signedGap_zero (ds : Bool) (d : ℝ) :
    signedGap ds true 0 d=signedGap ds false 0 d := by
  simp [signedGap,westTerm]

/-! Each of `westTerm`, `diagonalTerm` and `relativeTerm` is a constant plus a
first harmonic whose harmonic part is nonnegative on its interval, hence
concave. -/

lemma westTerm_concave (ds positive : Bool) :
    ConcaveOn ℝ (Set.Icc (-2/5) (2/5)) (westTerm ds positive) := by
  refine ((harmonic_concave (A := beta ds)
    (B := (if positive then beta ds else 0)-
      (if ds then 0 else 1.689*((40/100)*(25/100)/(12/25)))) fun x hx => ?_).add_const
    (-(if ds then 0 else 1.689*(((40/100)^2+(25/100)^2+(12/25)^2)/(2*(12/25)))))).congr
    fun x _ => by cases ds <;> cases positive <;> simp [westTerm,rotTangent_eq,harmonic] <;> ring
  have hc := (small_angle (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)).1
  have hs := abs_le.mp ((Real.abs_sin_le_abs (x := x)).trans
    (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩))
  cases ds <;> cases positive <;> norm_num [beta] <;> linarith [hs.1,hs.2]

lemma diagonalTerm_concave (ds : Bool) : ConcaveOn ℝ (Set.Icc 0 (1/2)) (diagonalTerm ds) := by
  refine ((harmonic_concave (A := alpha ds*0.387)
    (B := alpha ds*0.387-
      (if ds then 1.689*((30/100)*(27/100)/(9/20)) else 0)) fun x hx => ?_).add_const
    (-(if ds then 1.689*(((30/100)^2+(27/100)^2+(9/20)^2)/(2*(9/20))) else 0))).congr
    fun x _ => by cases ds <;> simp [diagonalTerm,rotTangent_eq,harmonic] <;> ring
  have ht := small_angle_nonneg (r := 9/10) ⟨hx.1,by linarith [hx.2]⟩ (by norm_num)
  have hs : Real.sin x≤1/2 := (Real.sin_le hx.1).trans hx.2
  cases ds <;> norm_num [alpha] <;> nlinarith [ht.1,ht.2.1]

lemma relativeTerm_concave (ds : Bool) : ConcaveOn ℝ (Set.Icc 0 (9/10)) (relativeTerm ds) := by
  refine ((harmonic_concave (A := mu ds)
    (B := mu ds-(if ds then 0 else 1.689*((35/100)*(25/100)/(1/2))))
    fun x hx => ?_).add_const
    (-(if ds then 0 else 1.689*(((35/100)^2+(25/100)^2+(1/2)^2)/(2*(1/2)))))).congr
    fun x _ => by cases ds <;> simp [relativeTerm,rotTangent_eq,harmonic] <;> ring
  have ht := small_angle_nonneg hx (by norm_num)
  cases ds <;> norm_num [mu] <;> nlinarith [ht.1,ht.2.1,ht.2.2]

lemma signedGap_concave_west (ds positive : Bool) {d l u : ℝ}
    (hl : -2/5≤l) (hu : u≤2/5) (hmap : ∀ x∈Set.Icc l u,0≤d-x ∧ d-x≤9/10) :
    ConcaveOn ℝ (Set.Icc l u) (fun w => signedGap ds positive w d) := by
  have hF := (westTerm_concave ds positive).subset (Set.Icc_subset_Icc hl hu) (convex_Icc l u)
  have hH := concave_affine_argument (relativeTerm_concave ds)
    (a := -1) (b := d) (by
      intro x hx; simpa only [neg_one_mul,neg_add_eq_sub,Set.mem_Icc] using hmap x hx)
  refine ((concaveOn_const (constant ds+diagonalTerm ds d) (convex_Icc l u)).add hF).add hH
    |>.congr ?_
  intro x _
  simp only [signedGap,Pi.add_apply,neg_one_mul,neg_add_eq_sub]
  ring

lemma signedGap_concave_diagonal (ds positive : Bool) {w l u : ℝ}
    (hl : 0≤l) (hu : u≤1/2) (hmap : ∀ x∈Set.Icc l u,0≤x-w ∧ x-w≤9/10) :
    ConcaveOn ℝ (Set.Icc l u) (signedGap ds positive w) := by
  have hG := (diagonalTerm_concave ds).subset (Set.Icc_subset_Icc hl hu) (convex_Icc l u)
  have hH := concave_affine_argument (relativeTerm_concave ds)
    (a := 1) (b := -w) (by
      intro x hx; simpa only [one_mul,sub_eq_add_neg,Set.mem_Icc] using hmap x hx)
  refine ((concaveOn_const (constant ds+westTerm ds positive w) (convex_Icc l u)).add hG).add hH
    |>.congr ?_
  intro x _
  simp only [signedGap,Pi.add_apply,one_mul,sub_eq_add_neg]

lemma signedGap_concave_edge (ds : Bool) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (fun x => signedGap ds true x x) := by
  have hF := (westTerm_concave ds true).subset
    (Set.Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc 0 (2/5))
  have hG := (diagonalTerm_concave ds).subset
    (Set.Icc_subset_Icc le_rfl (by norm_num)) (convex_Icc 0 (2/5))
  refine ((concaveOn_const (constant ds+relativeTerm ds 0) (convex_Icc 0 (2/5))).add
    (hF.add hG)).congr ?_
  intro x _
  simp only [signedGap,sub_self,Pi.add_apply]
  ring

/-- Positivity at the six vertices of the domain gives positivity of
`gap` on the whole domain, for either source. -/
theorem positive_of_vertices (ds : Bool) {w d : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hL0 : 0<signedGap ds false (-2/5) 0)
    (hLD : 0<signedGap ds false (-2/5) (1/2))
    (h00 : 0<signedGap ds false 0 0)
    (h0D : 0<signedGap ds false 0 (1/2))
    (hUU : 0<signedGap ds true (2/5) (2/5))
    (hUD : 0<signedGap ds true (2/5) (1/2)) : 0<gap ds w d := by
  unfold gap
  split_ifs with hpos
  · have hdiag := concave_gt_of_endpoints (signedGap_concave_edge ds)
      ⟨hpos,hw.2⟩
      (by simpa only [signedGap_zero] using h00) hUU
    have htop := concave_gt_of_endpoints
      (signedGap_concave_west ds true (d := (1:ℝ)/2) (l := 0) (u := (2:ℝ)/5)
        (by norm_num) le_rfl (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      ⟨hpos,hw.2⟩ (by simpa only [signedGap_zero] using h0D) hUD
    exact concave_gt_of_endpoints
      (signedGap_concave_diagonal ds true (w := w) (l := w) (u := (1:ℝ)/2) hpos le_rfl
        (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      ⟨hwd,hd.2⟩ hdiag htop
  · have hwn : w≤0 := (lt_of_not_ge hpos).le
    exact positive_on_separately_concave_rectangle ⟨hw.1,hwn⟩ hd
      (fun y hy => signedGap_concave_west ds false (d := y) (l := -(2:ℝ)/5) (u := 0)
        le_rfl (by norm_num)
        (by intro x hx; constructor <;> linarith [hy.1,hy.2,hx.1,hx.2]))
      (signedGap_concave_diagonal ds false (w := -(2:ℝ)/5) (l := 0) (u := (1:ℝ)/2)
        (by norm_num) le_rfl (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      (signedGap_concave_diagonal ds false (w := 0) (l := 0) (u := (1:ℝ)/2)
        (by norm_num) le_rfl (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      hL0 hLD h00 h0D

/-- `signedGap` is positive at the six vertices of the domain, for either
source: the angles there are `0`, `1/10`, `2/5`, `1/2`, `9/10` and `-2/5`, and
Taylor polynomials bracket their sines and cosines. -/
theorem vertices (ds : Bool) :
    0<signedGap ds false (-2/5) 0 ∧
    0<signedGap ds false (-2/5) (1/2) ∧
    0<signedGap ds false 0 0 ∧
    0<signedGap ds false 0 (1/2) ∧
    0<signedGap ds true (2/5) (2/5) ∧
    0<signedGap ds true (2/5) (1/2) := by
  have bracket (x : ℝ) (hx : 0≤x ∧ x≤9/10) := trig_bracket (l := x) (u := x) (x := x)
    hx.1 (by linarith [hx.2,Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  obtain ⟨hs4,hs4u,hc4,-⟩ := bracket (2/5) (by norm_num)
  obtain ⟨hs9,hs9u,hc9,-⟩ := bracket (9/10) (by norm_num)
  obtain ⟨hs1,hs1u,hc1,-⟩ := bracket (1/10) (by norm_num)
  obtain ⟨hs5,hs5u,hc5,-⟩ := bracket (1/2) (by norm_num)
  norm_num at hs4 hs4u hc4 hs9 hs9u hc9 hs1 hs1u hc1 hs5 hs5u hc5
  cases ds
  all_goals refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals norm_num [signedGap,westTerm,diagonalTerm,relativeTerm,constant,rotTangent,
    alpha,beta,mu,Real.cos_neg,Real.sin_neg]
  all_goals linarith

/-- `gap` is positive on the domain `-2/5 ≤ w ≤ 2/5`, `0 ≤ d ≤ 1/2`,
`w ≤ d`. -/
theorem gap_positive (ds : Bool) {w d : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d) :
    0<gap ds w d := by
  obtain ⟨hL0,hLD,h00,h0D,hUU,hUD⟩ := vertices ds
  exact positive_of_vertices ds hw hd hwd hL0 hLD h00 h0D hUU hUD

def westForce (ds : Bool) (w d : ℝ) : Point :=
  if ds then (beta ds*Real.cos w+mu ds*Real.sin (d-w),
    -beta ds*Real.sin w-mu ds*Real.cos (d-w))
  else (beta ds*Real.cos w,-beta ds*Real.sin w-mu ds)

def diagonalForce (ds : Bool) (w d : ℝ) : Point :=
  if ds then (alpha ds,mu ds)
  else (alpha ds+mu ds*Real.sin (d-w),mu ds*Real.cos (d-w))

/-- The threshold sum minus the works of the forces on W, D and C, for W on the
west side of C. -/
def slack (ds : Bool) (w d aw bw ad bd cx cy : ℝ) : ℝ :=
  1/2+(beta ds/2)*(Real.cos w+|Real.sin w|)+
    (alpha ds/2)*(Real.cos d+Real.sin d)+
    (mu ds/2)*(Real.cos (d-w)+Real.sin (d-w))-
    dot (westForce ds w d) (aw,bw)-dot (diagonalForce ds w d) (ad,bd)-
    ((beta ds+alpha ds*Real.cos d)*cx+alpha ds*Real.sin d*cy)

lemma side_force_norm (beta mu w : ℝ) :
    (beta*Real.cos w)^2+(beta*Real.sin w+mu)^2=beta^2+mu^2+2*beta*mu*Real.sin w := by
  linear_combination beta^2*(Real.sin_sq_add_cos_sq w)

lemma rotating_force_norm (beta mu w d : ℝ) :
    (beta*Real.cos w+mu*Real.sin (d-w))^2+
      (beta*Real.sin w+mu*Real.cos (d-w))^2=
      beta^2+mu^2+2*beta*mu*Real.sin d := by
  have hs : Real.sin w*Real.cos (d-w)+Real.cos w*Real.sin (d-w)=Real.sin d := by
    rw [← Real.sin_add]
    congr 1
    ring
  linear_combination beta^2*(Real.sin_sq_add_cos_sq w)+
    mu^2*(Real.sin_sq_add_cos_sq (d-w))+2*beta*mu*hs

lemma trig_bounds {w d : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d) :
    0≤Real.cos w ∧ -(2/5)≤Real.sin w ∧
    (0≤Real.cos d ∧ 0≤Real.sin d) ∧
    (1/2≤Real.cos (d-w) ∧ 0≤Real.sin (d-w)) := by
  have hsw := (abs_le.mp ((Real.abs_sin_le_abs (x := w)).trans
    (abs_le.mpr ⟨by linarith [hw.1],hw.2⟩))).1
  have hdt := small_angle_nonneg (r := 9/10) ⟨hd.1,by linarith [hd.2]⟩ (by norm_num)
  have hqt := small_angle_nonneg (r := 9/10)
    (show 0≤d-w ∧ d-w≤9/10 by constructor <;> linarith [hw.1,hd.2]) (by norm_num)
  have hcw := (small_angle (abs_le.mpr ⟨by linarith [hw.1],hw.2⟩)).1
  exact ⟨by linarith,hsw,⟨by linarith [hdt.1],hdt.2.1⟩,⟨by linarith [hqt.1],hqt.2.1⟩⟩

/-- On the domain, `slack` is at least `gap`: the forces on W and D
take the far-vertex support, with the tangent majorants of their lengths. -/
theorem gap_le_slack (ds : Bool) {w d aw bw ad bd cx cy : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    gap ds w d≤slack ds w d aw bw ad bd cx cy := by
  obtain ⟨hcw,hsw,hdt,hqt⟩ := trig_bounds hw hd hwd
  have hD' : ContainedChart ad |-bd| := by simpa only [abs_neg] using hD
  have hcentral := coarse_central_work hc
    (X := beta ds+alpha ds*Real.cos d)
    (Y := alpha ds*Real.sin d)
    (by cases ds <;> dsimp [alpha,beta] <;> linarith [hdt.1])
    (by cases ds <;> dsimp [alpha] <;> linarith [hdt.2]) le_rfl le_rfl
  have hpos (h : 0≤w) : 0≤Real.sin w :=
    Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hw.2,Real.pi_gt_d2])
  have hneg (h : ¬0≤w) : Real.sin w≤0 := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-w by linarith)
      (by linarith [hw.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at hs
    linarith
  cases ds
  · have hWt := rotTangent_bound (c := 12/25) (by norm_num)
      (side_force_norm (40/100) (25/100) w)
    have hWb := vertex_linear_upper hW (by linarith) hWt.1 hWt.2
    have hDt := rotTangent_bound (c := 1/2) (by norm_num)
      (rotating_norm_sq (35/100) (25/100) (d-w))
    have hDb := vertex_linear_upper hD' (by linarith [hqt.1]) hDt.1 hDt.2
    dsimp [alpha,beta] at hcentral
    unfold gap
    split_ifs with h
    · dsimp [signedGap,constant,westTerm,diagonalTerm,relativeTerm,slack,
        westForce,diagonalForce,alpha,beta,mu,dot]
      rw [abs_of_nonneg (hpos h)]
      nlinarith only [hWb,hDb,hcentral]
    · dsimp [signedGap,constant,westTerm,diagonalTerm,relativeTerm,slack,
        westForce,diagonalForce,alpha,beta,mu,dot]
      rw [abs_of_nonpos (hneg h)]
      nlinarith only [hWb,hDb,hcentral]
  · have hWt := rotTangent_bound (c := 9/20) (by norm_num)
      (rotating_force_norm (30/100) (27/100) w d)
    have hWb := vertex_linear_upper hW (by nlinarith [hqt.1]) hWt.1 hWt.2
    have hDb := vertex_linear_upper hD' (U := (43:ℝ)/100) (V := (27:ℝ)/100)
      (L := (51:ℝ)/100) (by norm_num) (by norm_num) (by norm_num)
    dsimp [alpha,beta] at hcentral
    unfold gap
    split_ifs with h
    · dsimp [signedGap,constant,westTerm,diagonalTerm,relativeTerm,slack,
        westForce,diagonalForce,alpha,beta,mu,dot]
      rw [abs_of_nonneg (hpos h)]
      nlinarith only [hWb,hDb,hcentral]
    · dsimp [signedGap,constant,westTerm,diagonalTerm,relativeTerm,slack,
        westForce,diagonalForce,alpha,beta,mu,dot]
      rw [abs_of_nonpos (hneg h)]
      nlinarith only [hWb,hDb,hcentral]

lemma slack_nonpositive (ds : Bool) {w d aw bw ad bd cx cy : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hCW : 0≤centralMargin .west (Real.pi+w) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi+w) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center)) :
    slack ds w d aw bw ad bd cx cy≤0 := by
  obtain ⟨hcw,_,hdt,hqt⟩ := trig_bounds hw hd hwd
  have hcq : 0≤Real.cos (d-w) := by linarith [hqt.1]
  have hW : 1/2-cx-aw*Real.cos w+bw*Real.sin w+(Real.cos w+|Real.sin w|)/2≤0 := by
    have e1 : Real.cos (Real.pi+w)=-Real.cos w := by rw [add_comm]; exact Real.cos_add_pi w
    have e2 : Real.sin (Real.pi+w)=-Real.sin w := by rw [add_comm]; exact Real.sin_add_pi w
    simp only [centralMargin,centerX,angularWidth,e1,e2,
      abs_neg,abs_of_nonneg hcw] at hCW
    nlinarith only [hCW]
  have hD : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    have e1 : Real.cos (Real.pi+d)=-Real.cos d := by rw [add_comm]; exact Real.cos_add_pi d
    have e2 : Real.sin (Real.pi+d)=-Real.sin d := by rw [add_comm]; exact Real.sin_add_pi d
    simp only [centralMargin,centralNormal,angularWidth,e1,e2,
      abs_neg,abs_of_nonneg hdt.1,abs_of_nonneg hdt.2] at hCD
    nlinarith only [hCD]
  have hq : (Real.pi+d)-(Real.pi+w)=d-w := by ring
  cases ds
  · change SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi+w) aw bw)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_left,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hqt.2] at hWD
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,dot]
    nlinarith only [hW,hD,hWD]
  · change SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi+d) ad bd)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_right,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hqt.2] at hWD
    dsimp [slack,westForce,diagonalForce,alpha,beta,mu,dot]
    nlinarith only [hW,hD,hWD]

/-- If W is separated along the west side of C, `w ≤ d ≤ 1/2`, and W and D are
separated along a secondary axis of W or of D, these separations contradict
the containment in the disk. -/
theorem impossible (ds : Bool) {w d aw bw ad bd cx cy : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hCW : 0≤centralMargin .west (Real.pi+w) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi+w) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center)) : False := by
  have hp := gap_positive ds hw hd hwd
  have hs := gap_le_slack ds hw hd hwd hW hD hc
  have hn := slack_nonpositive ds hw hd hwd hCW hCD hWD
  linarith

end DiagonalAngle.Side

/-- If W is separated along the west side of C, the angle of D exceeds `1/2`. -/
theorem cardinal_west_diagonal_gt_half {R : ℝ} (P : NormalizedPacking R)
    (hcard : P.ownAxis 2=false) : 1/2<P.diagonalAngle := by
  by_contra! hd
  have hwabs := abs_lt.mp (P.cardinal_angle 2 hcard)
  have hw : -2/5≤P.deviation 2 ∧ P.deviation 2≤2/5 :=
    ⟨by linarith [hwabs.1],hwabs.2.le⟩
  have hdiag : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 :=
    ⟨P.diagonal_angle_range.1.le,hd⟩
  have hWphase : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  have hmc : matchingCardinal 2=.west := rfl
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hwd : P.deviation 2≤P.diagonalAngle := by
    have hh := P.primary_order.2.2.1
    rw [hWphase,hDphase] at hh
    linarith
  obtain ⟨k,hsep,hcases⟩ := westDiagonal_secondary P
  rcases hcases with rfl | rfl
  · change SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) at hsep
    apply DiagonalAngle.Side.impossible false hw hdiag hwd (P.contained 2) (P.contained 3) P.box
      (by simpa only [hWphase,hmc] using P.cardinal_separator 2 hcard)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    simpa only [P.square_def,hWphase,hDphase,Bool.false_eq_true,ite_false] using hsep
  · change SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center) at hsep
    apply DiagonalAngle.Side.impossible true hw hdiag hwd (P.contained 2) (P.contained 3) P.box
      (by simpa only [hWphase,hmc] using P.cardinal_separator 2 hcard)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    simpa only [P.square_def,hWphase,hDphase,ite_true] using hsep

/-- In a normalized packing the angle of D exceeds `1/2`. -/
theorem normalized_diagonal_gt_half {R : ℝ} (P : NormalizedPacking R) :
    1/2<P.diagonalAngle := by
  cases hbit : P.ownAxis 2
  · exact cardinal_west_diagonal_gt_half P hbit
  · exact own_west_diagonal_gt_half P hbit

end SquaresInCircles.Six
