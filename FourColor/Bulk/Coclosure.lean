import FourColor.Chromogram
import FourColor.Color

/-!
# The Kempe co-closure is transitive

A trace in the co-closure of a set of traces that themselves lie in the
co-closure of `P` lies in the co-closure of `P`.  This is what lets a
certificate be checked in two stages: the bulk stage establishes the
co-closure of a large set of traces, and the residual stage may use any of
them as witnesses.
-/

namespace FourColor

theorem kempeCoclosure_trans {P Q : List Color → Prop} (hQ : ∀ et, Q et → KempeCoclosure P et)
    {et : List Color} (h : KempeCoclosure Q et) : KempeCoclosure P et := by
  intro P' hP' hP'et
  obtain ⟨et', hQet', hP'et'⟩ := h P' hP' hP'et
  exact hQ et' hQet' P' hP' hP'et'

/-- A trace satisfying `P` is in the co-closure of `P`. -/
theorem kempeCoclosure_of_mem {P : List Color → Prop} {et : List Color} (h : P et) :
    KempeCoclosure P et :=
  fun _ _ hP'et => ⟨et, h, hP'et⟩


/-- A trace is the image of its even form under the permutation that evened it. -/
theorem map_evenize_evenPerm' (es : List Color) : (evenize es).map (evenPerm es) = es := by
  unfold evenize
  cases h : evenTrace es with
  | false =>
    have hp : evenPerm es = EdgePerm.e132 := by unfold evenPerm; rw [h]; rfl
    rw [hp, List.map_map]
    refine (List.map_congr_left ?_).trans (List.map_id _)
    intro c _
    cases c <;> rfl
  | true =>
    have hp : evenPerm es = 1 := by unfold evenPerm; rw [h]; rfl
    rw [hp, List.map_map]
    refine (List.map_congr_left ?_).trans (List.map_id _)
    intro c _
    cases c <;> rfl

end FourColor
