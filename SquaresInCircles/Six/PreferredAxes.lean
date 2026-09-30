module
public import SquaresInCircles.Six.DirectedAxes

@[expose] public section

/-!
# Four source axes after pin orientation

An orientation table is used only after every one of its normals has positive
projection on the interior-pin chord. The theorem then derives a selected
separator from the original geometric SAT disjunction. No axis is discarded
on the strength of a numerical source preference.
-/

noncomputable section
namespace SquaresInCircles.Six

def unsignedPairAxis (S T : UnitSquare) (i : Fin 4) : Point :=
  ![normalX S,normalY S,normalX T,normalY T] i

def preferredPairAxis (sign : Fin 4 → Bool) (S T : UnitSquare) (i : Fin 4) : Point :=
  if sign i then unsignedPairAxis S T i else scale (-1) (unsignedPairAxis S T i)

lemma preferred_is_pairNormal (sign : Fin 4 → Bool) (S T : UnitSquare) (i : Fin 4) :
    ∃ j : Fin 8, preferredPairAxis sign S T i=Stress.pairNormal j S T := by
  fin_cases i
  · by_cases h : sign 0=true
    · exact ⟨0,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩
    · exact ⟨1,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩
  · by_cases h : sign 1=true
    · exact ⟨2,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩
    · exact ⟨3,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩
  · by_cases h : sign 2=true
    · exact ⟨4,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩
    · exact ⟨5,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩
  · by_cases h : sign 3=true
    · exact ⟨6,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩
    · exact ⟨7,by simp [preferredPairAxis,unsignedPairAxis,Stress.pairNormal,h]⟩

lemma preferred_abs_dot (sign : Fin 4 → Bool) (S T : UnitSquare) (i : Fin 4) (v : Point) :
    |dot (preferredPairAxis sign S T i) v|=|dot (unsignedPairAxis S T i) v| := by
  unfold preferredPairAxis
  split_ifs <;> simp only [dot_scale_neg,abs_neg]

lemma unsigned_separators_complete (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    ∃ i : Fin 4, Seven.SAT.threshold S T ≤
      |dot (unsignedPairAxis S T i) (sub T.center S.center)| := by
  have h := Seven.SAT.separating_axes S T hd
  rcases h with h | h | h | h
  · exact ⟨0,by simpa [unsignedPairAxis,normalX,frameX,dot] using h⟩
  · exact ⟨1,by simpa [unsignedPairAxis,normalY,frameY,dot] using h⟩
  · exact ⟨2,by simpa [unsignedPairAxis,normalX,frameX,dot] using h⟩
  · exact ⟨3,by simpa [unsignedPairAxis,normalY,frameY,dot] using h⟩

/-- Pin orientation preserves completeness of the four-axis source list. -/
theorem preferred_separators_complete (sign : Fin 4 → Bool) (S T : UnitSquare)
    {p q : Point} (hp : openSquare S p) (hq : openSquare T q)
    (hpos : ∀ i, 0 < dot (preferredPairAxis sign S T i) (sub q p))
    (hd : ∀ z, ¬ (openSquare S z ∧ openSquare T z)) :
    ∃ i : Fin 4, Seven.SAT.threshold S T ≤
      dot (preferredPairAxis sign S T i) (sub T.center S.center) := by
  obtain ⟨i,hi⟩ := unsigned_separators_complete S T hd
  obtain ⟨j,hj⟩ := preferred_is_pairNormal sign S T i
  have hn : preferredPairAxis sign S T i≠(0,0) := by rw [hj]; exact pairNormal_ne S T j
  have hw : width S (preferredPairAxis sign S T i)+width T (preferredPairAxis sign S T i)=
      Seven.SAT.threshold S T := by rw [hj]; exact pairNormal_widths S T j
  have h := orient_axis_from_pins hn hp hq (hpos i)
    (by rw [hw,preferred_abs_dot]; exact hi)
  exact ⟨i,by simpa only [hw] using h⟩

end SquaresInCircles.Six
