module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsCoefficientCertificates

/-!
# The original nonnegative-total weight domains

Uncompiled transcription of equations (23)--(24) and (29)--(30).
The upper k bound is the stated completed square at 3/10. The upper
l and c derivatives are bounded by their convex quadratic endpoint
chords. No coefficient range is added as a caller premise.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Explicit
open TensorWholeIntervalPolynomial TwoVariablePolynomial

structure BaseBounds (k l c : ℝ) : Prop where
  k_lower : 2/3≤k
  k_upper : k≤17/20
  l_positive : 0<l
  c_positive : 0<c
  k_le_l : k≤l
  l_le_three_halves_k : l≤(3/2)*k
  k_le_c : k≤c
  c_le_two : c≤2
  c_lower_ratio : (9/10)*l≤c
  c_upper_ratio : c≤(11/10)*l

theorem triangle_x {x y : ℝ} (hd : Domain .triangle x y) :
    x∈Icc 0 (8/15:ℝ) := ⟨hd.1,by linarith [hd.2.1,hd.2.2]⟩

theorem triangle_k_lower {x y : ℝ} (hd : Domain .triangle x y) :
    (1673/2500:ℝ)≤k .triangle x y := by
  have hx := triangle_x hd
  have h2 := mul_le_mul_of_nonneg_right hx.2 hx.1
  have h3 := pow_nonneg hx.1 3
  dsimp [k]
  nlinarith only [h2,h3,hx.1,hd.2.1]

theorem triangle_k_upper {x y : ℝ} (hd : Domain .triangle x y) :
    k .triangle x y<(849/1000:ℝ) := by
  have hx := triangle_x hd
  let u : ℝ := x-3/10
  have hu : u≤3/10 := by dsimp [u]; linarith [hx.2]
  have htail := mul_le_mul_of_nonneg_right hu (sq_nonneg u)
  have hsq := sq_nonneg (u+54/5605)
  have hedge : k .triangle x y≤k .triangle x (8/15-x) := by
    dsimp [k]
    linarith [hd.2.2]
  have hid : k .triangle x (8/15-x)=
      3183197/3750000-(27/15625)*u-(1351/6250)*u^2+(527/1250)*u^3 := by
    dsimp [k,u]
    ring
  have hcomplete : (3183197/3750000:ℝ)-(27/15625)*u-(1121/12500)*u^2=
      3568398829/4203750000-(1121/12500)*(u+54/5605)^2 := by ring
  rw [hid] at hedge
  nlinarith only [hedge,htail,hsq,hcomplete]

def lEdge (x : ℝ) : ℝ := l .triangle x (8/15-x)
def cEdge (x : ℝ) : ℝ := c .triangle x (8/15-x)

theorem lEdge_hasDerivAt (x : ℝ) :
    HasDerivAt lEdge ((1917/500)*x^2-(2733/1250)*x-93/400) x := by
  have hd : Differentiable ℝ lEdge := by dsimp [lEdge,l]; fun_prop
  convert (hd x).hasDerivAt using 1
  simp (disch := fun_prop) [lEdge,l]
  ring

theorem cEdge_hasDerivAt (x : ℝ) :
    HasDerivAt cEdge ((42207/10000)*x^2-(5743/2500)*x-2709/10000) x := by
  have hd : Differentiable ℝ cEdge := by dsimp [cEdge,c]; fun_prop
  convert (hd x).hasDerivAt using 1
  simp (disch := fun_prop) [cEdge,c]
  ring

theorem lEdge_antitone : AntitoneOn lEdge (Icc (0:ℝ) (8/15)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (lEdge_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => lEdge_hasDerivAt x)
  intro x hx
  have hchord := mul_nonneg hx.1.le (show 0≤8/15-x by linarith [hx.2])
  nlinarith only [hchord,hx.1]

theorem cEdge_antitone : AntitoneOn cEdge (Icc (0:ℝ) (8/15)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (cEdge_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => cEdge_hasDerivAt x)
  intro x hx
  have hchord := mul_nonneg hx.1.le (show 0≤8/15-x by linarith [hx.2])
  nlinarith only [hchord,hx.1]

theorem triangle_l_bounds {x y : ℝ} (hd : Domain .triangle x y) :
    (22/25:ℝ)<l .triangle x y ∧ l .triangle x y<567/500 := by
  have hx := triangle_x hd
  have hlow := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<Coefficients.d)
    Coefficients.l_lower_certificate.1 Coefficients.l_lower_certificate.2 hx
  have hlow' : (22/25:ℝ)<l .triangle x 0 := by
    simpa [Coefficients.edge,evaluate_restrict] using hlow
  have hupper := lEdge_antitone (show (0:ℝ)∈Icc 0 (8/15) by norm_num) hx hx.1
  have hedge : l .triangle x y≤lEdge x := by
    dsimp [lEdge,l]
    linarith [hd.2.2]
  have hzero : lEdge 0=(17/15:ℝ) := by norm_num [lEdge,l]
  rw [hzero] at hupper
  constructor
  · dsimp [l] at hlow' ⊢
    linarith [hd.2.1]
  · linarith

theorem triangle_c_bounds {x y : ℝ} (hd : Domain .triangle x y) :
    (439/500:ℝ)<c .triangle x y ∧ c .triangle x y<23/20 := by
  have hx := triangle_x hd
  have hlow := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<Coefficients.d)
    Coefficients.c_lower_certificate.1 Coefficients.c_lower_certificate.2 hx
  have hlow' : (439/500:ℝ)<c .triangle x 0 := by
    simpa [Coefficients.edge,evaluate_restrict] using hlow
  have hupper := cEdge_antitone (show (0:ℝ)∈Icc 0 (8/15) by norm_num) hx hx.1
  have hedge : c .triangle x y≤cEdge x := by
    dsimp [cEdge,c]
    linarith [hd.2.2]
  have hzero : cEdge 0=(34489/30000:ℝ) := by norm_num [cEdge,c]
  rw [hzero] at hupper
  constructor
  · dsimp [c] at hlow' ⊢
    linarith [hd.2.1]
  · linarith

theorem triangle_differences {x y : ℝ} (hd : Domain .triangle x y) :
    k .triangle x y<l .triangle x y ∧ k .triangle x y<c .triangle x y ∧
      (9/10)*l .triangle x y<c .triangle x y ∧ c .triangle x y<(11/10)*l .triangle x y := by
  have h0 := Coefficients.difference_lower 0 hd
  have h1 := Coefficients.difference_lower 1 hd
  have h2 := Coefficients.difference_lower 2 hd
  have h3 := Coefficients.difference_lower 3 hd
  norm_num [Coefficients.difference,Coefficients.differenceReserve] at h0 h1 h2 h3
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem triangle_l_ratio {x y : ℝ} (hd : Domain .triangle x y) :
    l .triangle x y<(3/2)*k .triangle x y := by
  have hx := triangle_x hd
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h3 := mul_le_mul_of_nonneg_right h2 hx.1
  have hid : (3/2)*k .triangle x y-l .triangle x y=
      19/5000+(1913/2500)*x+(999/5000)*x^2-(807/1250)*x^3+(17/100)*y := by
    dsimp [k,l]
    ring
  nlinarith only [hid,h3,hx.1,hd.2.1,sq_nonneg x]

theorem triangle_base_bounds {x y : ℝ} (hd : Domain .triangle x y) :
    BaseBounds (k .triangle x y) (l .triangle x y) (c .triangle x y) := by
  have hk0 := triangle_k_lower hd
  have hk1 := triangle_k_upper hd
  have hl := triangle_l_bounds hd
  have hc := triangle_c_bounds hd
  have hdif := triangle_differences hd
  exact ⟨by linarith,by linarith,by linarith [hl.1],by linarith [hc.1],
    hdif.1.le,(triangle_l_ratio hd).le,hdif.2.1.le,by linarith [hc.2],
    hdif.2.2.1.le,hdif.2.2.2.le⟩

theorem rectangle_ranges {x y : ℝ} (hd : Domain .rectangle x y) :
    (2/3:ℝ)<k .rectangle x y ∧ k .rectangle x y<17/20 ∧
      1≤l .rectangle x y ∧ l .rectangle x y<6/5 ∧
      l .rectangle x y<c .rectangle x y ∧ c .rectangle x y<6/5 ∧
      k .rectangle x y<l .rectangle x y ∧ l .rectangle x y<(3/2)*k .rectangle x y ∧
      c .rectangle x y≤(10163/10000)*l .rectangle x y := by
  rcases hd with ⟨⟨hx0,hx1⟩,⟨hy0,hy1⟩⟩
  dsimp [k,l,c]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith⟩

theorem rectangle_base_bounds {x y : ℝ} (hd : Domain .rectangle x y) :
    BaseBounds (k .rectangle x y) (l .rectangle x y) (c .rectangle x y) := by
  obtain ⟨hk0,hk1,hl0,hl1,hlc,hc1,hkl,hlk,hcl⟩ := rectangle_ranges hd
  exact ⟨hk0.le,hk1.le,by linarith,by linarith,hkl.le,hlk.le,
    hkl.le.trans hlc.le,by linarith,by linarith,by linarith⟩

theorem base_bounds (r : Region) {x y : ℝ} (hd : Domain r x y) :
    BaseBounds (k r x y) (l r x y) (c r x y) := by
  cases r
  · exact triangle_base_bounds hd
  · exact rectangle_base_bounds hd

theorem l_lower (r : Region) {x y : ℝ} (hd : Domain r x y) : (22/25:ℝ)<l r x y := by
  cases r
  · exact (triangle_l_bounds hd).1
  · linarith [(rectangle_ranges hd).2.2.1]

theorem c_upper (r : Region) {x y : ℝ} (hd : Domain r x y) : c r x y<6/5 := by
  cases r
  · linarith [(triangle_c_bounds hd).2]
  · exact (rectangle_ranges hd).2.2.2.2.2.1

theorem l_upper (r : Region) {x y : ℝ} (hd : Domain r x y) : l r x y<6/5 := by
  cases r
  · linarith [(triangle_l_bounds hd).2]
  · exact (rectangle_ranges hd).2.2.2.1

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Explicit
