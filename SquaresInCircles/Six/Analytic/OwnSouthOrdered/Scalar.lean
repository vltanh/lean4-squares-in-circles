import SquaresInCircles.Six.Analytic.OwnSouthOrdered.Diagonal

/-!
# Ordered own wings: the profile is positive

The profile is positive on `0 ≤ v ≤ s ≤ 2/3`, `v + s ≤ 24/25`,
`1/2 ≤ d ≤ 11/14`. By the monotonicity in `d` it suffices to take `d = 11/14`.
For fixed `v` the profile is a constant plus `A cos s + B sin s` with
`A, B ≥ 0`, concave in `s`, so its least value is at `s = v` or at
`s = min (2/3) (24/25 - v)`. On each of the edges `s = v`, `s = 2/3` and
`s = 24/25 - v` it is a constant plus a nonnegative first harmonic in `v` plus
`chord`, again concave, which leaves the vertices `(0, 0)`, `(0, 2/3)`,
`(22/75, 2/3)` and `(12/25, 12/25)`. There Taylor polynomials bound it below by
positive rationals.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthOrdered

private lemma harmonic_concave {A B l u : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) :
    ConcaveOn ℝ (Set.Icc l u) (fun x => A*Real.cos x+B*Real.sin x) := by
  have h := radicalTrig_concave (A := A) (B := B) (p := 1) (q := 0) (R := 0)
    (l := l) (u := u) (by norm_num) (by norm_num)
    (by intro x hx; norm_num)
    (by
      intro x hx
      have hc := Real.cos_nonneg_of_mem_Icc
        (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [hl,hx.1,hx.2,hu,Real.pi_pos])
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi (hl.trans hx.1)
        (by linarith [hx.2,hu,Real.pi_pos])
      simp only [zero_mul]
      positivity)
  convert h using 1
  funext x
  simp only [radicalTrig,zero_mul,sub_zero]

private lemma harmonic_chord_concave {A B K l u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 ≤ l) (hu : u ≤ 12/25) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun v => K+(A*Real.cos v+B*Real.sin v)+chord (11/14+v)) := by
  have ht := harmonic_concave (u := u) hA hB hl (by linarith [hu,Real.pi_gt_d2])
  have hq := concave_affine_argument (a := 1) (b := 11/14) chord_concave
    (l := l) (u := u) (by
      intro v hv
      constructor <;> linarith [hl,hu,hv.1,hv.2])
  have hq' : ConcaveOn ℝ (Set.Icc l u) (fun v => chord (11/14+v)) := by
    simpa only [one_mul,add_comm] using hq
  exact ((concave_constant K l u).add ht).add hq'

private lemma upper_trig :
    0 ≤ Real.sin ((11:ℝ)/14) ∧ Real.sin ((11:ℝ)/14) ≤ 4/5 ∧
    Real.cos ((11:ℝ)/14) ≤ 3/4 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := (11:ℝ)/14)
    (by norm_num) (by linarith [Real.pi_gt_d2])
  have hu := Real.sin_le (x := (11:ℝ)/14) (by norm_num)
  have hc := Seven.cos_upper_four (x := (11:ℝ)/14) (by norm_num)
  exact ⟨hs,by linarith,by nlinarith only [hc]⟩

private def sA : ℝ := southWeight*wingCos-wingSin*Real.cos (11/14)+(1/2)*Real.sin (11/14)
private def sB : ℝ := southWeight*wingSin-wingSin*Real.sin (11/14)-(1/2)*Real.cos (11/14)
private def sK (v : ℝ) : ℝ :=
  -83178077/125000000+westWeight*wing v+chord (11/14+v)

private lemma s_identity (v s : ℝ) :
    profile v s (11/14)=sK v+sA*Real.cos s+sB*Real.sin s := by
  dsimp [profile,wing,southTerm,sK,sA,sB]
  rw [Real.cos_sub,Real.sin_sub]
  ring

private lemma s_coefficients : 0 ≤ sA ∧ 0 ≤ sB := by
  have h := upper_trig
  dsimp [sA,sB,southWeight,wingCos,wingSin]
  constructor <;> linarith [Real.cos_le_one ((11:ℝ)/14)]

private lemma vertical_concave :
    ConcaveOn ℝ (Set.Icc 0 (22/75)) (fun v => profile v (2/3) (11/14)) := by
  have h := harmonic_chord_concave
    (A := westWeight*wingCos) (B := westWeight*wingSin)
    (K := -83178077/125000000+southWeight*wing (2/3)+southTerm (11/14-2/3))
    (l := 0) (u := 22/75)
    (by norm_num [westWeight,wingCos]) (by norm_num [westWeight,wingSin])
    (by norm_num) (by norm_num)
  convert h using 1
  funext v
  dsimp [profile,wing]
  ring

private lemma equal_wall_concave :
    ConcaveOn ℝ (Set.Icc 0 (12/25)) (fun v => profile v v (11/14)) := by
  let A := (westWeight+southWeight)*wingCos-wingSin*Real.cos (11/14)+(1/2)*Real.sin (11/14)
  let B := (westWeight+southWeight)*wingSin-wingSin*Real.sin (11/14)-(1/2)*Real.cos (11/14)
  have hA : 0 ≤ A := by
    dsimp [A,westWeight,southWeight,wingCos,wingSin]
    linarith [upper_trig.1,Real.cos_le_one ((11:ℝ)/14)]
  have hB : 0 ≤ B := by
    dsimp [B,westWeight,southWeight,wingSin]
    linarith [Real.sin_le_one ((11:ℝ)/14),Real.cos_le_one ((11:ℝ)/14)]
  have h := harmonic_chord_concave (K := -83178077/125000000)
    (l := 0) (u := 12/25) hA hB (by norm_num) le_rfl
  convert h using 1
  funext v
  dsimp [profile,wing,southTerm,A,B]
  rw [Real.cos_sub,Real.sin_sub]
  ring

private lemma sum_wall_concave :
    ConcaveOn ℝ (Set.Icc (22/75) (12/25))
      (fun v => profile v (24/25-v) (11/14)) := by
  let k : ℝ := 24/25
  let t : ℝ := 11/14-k
  let A := westWeight*wingCos+
    southWeight*(wingCos*Real.cos k+wingSin*Real.sin k)-wingSin*Real.cos t+(1/2)*Real.sin t
  let B := westWeight*wingSin+
    southWeight*(wingCos*Real.sin k-wingSin*Real.cos k)+wingSin*Real.sin t+(1/2)*Real.cos t
  have hck : 1/2 ≤ Real.cos k := by
    have h := Real.one_sub_sq_div_two_le_cos (x := k)
    norm_num [k] at h
    linarith
  have hsk := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ k by norm_num [k]) (show k ≤ Real.pi by dsimp [k]; linarith [Real.pi_gt_d2])
  have hct := Real.cos_nonneg_of_mem_Icc
    (show t ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      dsimp [t,k]
      constructor <;> linarith [Real.pi_gt_d2])
  have hst : -(1/5) ≤ Real.sin t := by
    have h := Real.sin_le (x := -t) (by norm_num [t,k])
    rw [Real.sin_neg] at h
    have ht : t=-61/350 := by norm_num [t,k]
    clear_value A B t k
    linarith
  have hA : 0 ≤ A := by
    dsimp [A,westWeight,southWeight,wingCos,wingSin]
    clear_value A B t k
    linarith [Real.cos_le_one t]
  have hB : 0 ≤ B := by
    dsimp [B,westWeight,southWeight,wingCos,wingSin]
    clear_value A B t k
    linarith [Real.cos_le_one k]
  have h := harmonic_chord_concave (K := -83178077/125000000)
    (l := 22/75) (u := 12/25) hA hB (by norm_num) le_rfl
  convert h using 1
  funext v
  dsimp [profile,wing,southTerm,A,B]
  rw [show (11:ℝ)/14-(24/25-v)=t+v by dsimp [t,k]; ring]
  simp only [Real.cos_sub,Real.sin_sub,Real.cos_add,Real.sin_add]
  dsimp [t,k]
  ring

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private def lowerPolynomial (v s : ℝ) : ℝ :=
  -83178077/125000000+
    westWeight*(wingCos*cosLower v+wingSin*sinLower v)+
    southWeight*(wingCos*cosLower s+wingSin*sinLower s)+
    (109/100)*sinLower (11/14+v)-chordCoefficient*sinUpper ((11/14+v)/2)-
    wingSin*cosUpper (11/14-s)+(1/2)*sinLower (11/14-s)

private lemma polynomial_le {v s : ℝ} (hv : 0 ≤ v) (hs : 0 ≤ s ∧ s ≤ 2/3) :
    lowerPolynomial v s ≤ profile v s (11/14) := by
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cs := Seven.cos_lower_six hs.1
  have ss := Seven.sin_lower_seven hs.1
  have sq := Seven.sin_lower_seven (x := 11/14+v) (by linarith)
  have sh := Seven.sin_upper_five (x := (11/14+v)/2) (by linarith)
  have cr := Seven.cos_upper_four (x := 11/14-s) (by linarith [hs.2])
  have sr := Seven.sin_lower_seven (x := 11/14-s) (by linarith [hs.2])
  dsimp [lowerPolynomial,profile,wing,chord,southTerm,westWeight,southWeight,
    wingCos,wingSin,chordCoefficient,cosLower,cosUpper,sinLower,sinUpper]
  nlinarith only [cv,sv,cs,ss,sq,sh,cr,sr]

lemma four_vertices :
    0 < profile 0 0 (11/14) ∧ 0 < profile 0 (2/3) (11/14) ∧
    0 < profile (22/75) (2/3) (11/14) ∧ 0 < profile (12/25) (12/25) (11/14) := by
  have h0 := polynomial_le (v := 0) (s := 0) (by norm_num) (by norm_num)
  have h1 := polynomial_le (v := 0) (s := 2/3) (by norm_num) (by norm_num)
  have h2 := polynomial_le (v := 22/75) (s := 2/3) (by norm_num) (by norm_num)
  have h3 := polynomial_le (v := 12/25) (s := 12/25) (by norm_num) (by norm_num)
  norm_num [lowerPolynomial,westWeight,southWeight,wingCos,wingSin,chordCoefficient,
    cosLower,cosUpper,sinLower,sinUpper] at h0 h1 h2 h3
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- The profile is positive on the ordered domain. -/
theorem positive {v s d : ℝ} (hv : 0 ≤ v) (hvs : v ≤ s)
    (hs : s ≤ 2/3) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : 0 < profile v s d := by
  have hvmax : v ≤ 12/25 := by linarith
  have hs0 : 0 ≤ s := hv.trans hvs
  have hequal : 0 < profile v v (11/14) :=
    positive_on_concave_interval (f := fun v => profile v v (11/14))
      equal_wall_concave ⟨hv,hvmax⟩ four_vertices.1 four_vertices.2.2.2
  have hupper : 0 < profile v s (11/14) := by
    by_cases hcut : v ≤ 22/75
    · have htop : 0 < profile v (2/3) (11/14) :=
        positive_on_concave_interval (f := fun v => profile v (2/3) (11/14))
          vertical_concave ⟨hv,hcut⟩ four_vertices.2.1 four_vertices.2.2.1
      rw [s_identity] at hequal htop ⊢
      have h := trig_lower_of_endpoints s_coefficients.1 s_coefficients.2 hv
        (show (2:ℝ)/3 ≤ Real.pi/2 by linarith [Real.pi_gt_d2])
        ⟨hvs,hs⟩ (C := -sK v) (by linarith) (by linarith)
      linarith
    · have hleft : 0 < profile (22/75) (24/25-22/75) (11/14) := by
        rw [show (24:ℝ)/25-22/75=2/3 by norm_num]
        exact four_vertices.2.2.1
      have hright : 0 < profile (12/25) (24/25-12/25) (11/14) := by
        rw [show (24:ℝ)/25-12/25=12/25 by norm_num]
        exact four_vertices.2.2.2
      have htop : 0 < profile v (24/25-v) (11/14) :=
        positive_on_concave_interval (f := fun v => profile v (24/25-v) (11/14))
          sum_wall_concave ⟨(le_of_not_ge hcut),hvmax⟩ hleft hright
      rw [s_identity] at hequal htop ⊢
      have hu : 24/25-v ≤ Real.pi/2 := by linarith [hv,Real.pi_gt_d2]
      have h := trig_lower_of_endpoints s_coefficients.1 s_coefficients.2 hv hu
        (show v ≤ s ∧ s ≤ 24/25-v by constructor <;> linarith)
        (C := -sK v) (by linarith) (by linarith)
      linarith
  exact hupper.trans_le (profile_at_upper_diagonal ⟨hv,hvmax⟩ ⟨hs0,hs⟩ hd)

end SquaresInCircles.Six.Analytic.OwnSouthOrdered
