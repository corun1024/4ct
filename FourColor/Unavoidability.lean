import FourColor.RedpartSound

/-!
# Unavoidability

Collating the seven presentations.  A minimal counter-example carries a face of
positive charge; discharging bounds its arity between five and eleven, and each
of the seven presentation scripts rules out one of those arities.  So there is
no minimal counter-example.

The scripts themselves are hypotheses here, so that the collation is checked
independently of the computations that discharge them.
-/

namespace FourColor

namespace Hypermap

variable {D : Type} [Finite D] {G : Hypermap D}

/-- At most five discharge rules apply at any dart of a minimal
counter-example: the source rules of a hub of arity outside `[5, 8]` are empty,
and for the four arities in range the bound is a computation. -/
theorem dscore1_le_five (hred : RedpartSound theRedpart)
    (hmin : G.MinimalCounterExample) (y : D) : G.dscore1 y ≤ 5 := by
  have hpenta : G.Pentagonal := hmin.pentagonal
  have hredp : ∀ (z : D) (q : Part), theRedpart q = true → ¬ G.ExactFitp z q :=
    fun z q hq => hred G hmin z q hq
  set x := G.invFace2 y with hx
  have hy : y = G.face (G.face x) := (G.face_face_invFace2 y).symm
  have harity : G.arity x = G.arity x := rfl
  rw [hy, G.dbound1_eq harity]
  by_cases hrange : 5 ≤ G.arity x ∧ G.arity x ≤ 8
  · -- a hub arity the rules can apply to: bound it by the check
    have hfit : G.ExactFitp x (Part.free (G.arity x)) := G.exact_fitp_free hpenta x
    have hsrc : pickSourceDrules (G.arity x) theDrules
        = (druleFork Part.conversePart (G.arity x)).source :=
      ((druleFork Part.conversePart (G.arity x)).source_eq).symm
    rw [hsrc]
    refine checkDbound1_le hredp hfit ?_
    -- the check itself, for each of the four arities in range
    obtain ⟨h5, h8⟩ := hrange
    interval_cases h : G.arity x <;> decide +kernel
  · -- no rule takes charge from a hub of this arity
    rw [pickSourceDrules_eq_nil hrange, dbound1]
    simp

/-- **Unavoidability**: no hypermap is a minimal counter-example. -/
theorem not_minimalCounterExample (hred : RedpartSound theRedpart)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    (e10 : ExcludedArity (RedpartSound theRedpart) 10)
    (e11 : ExcludedArity (RedpartSound theRedpart) 11) :
    ¬ G.MinimalCounterExample := by
  intro hmin
  have hgeo : G.PlanarPlainCubicConnected :=
    ⟨⟨⟨hmin.plain, hmin.cubic⟩, hmin.connected⟩, hmin.planar⟩
  obtain ⟨x, hx⟩ := G.posz_dscore hgeo
  have hvalid : ValidHub G x := ⟨hmin, hmin.pentagonal, hx⟩
  -- the arity of a positively charged face is between five and eleven
  have hlo : 5 ≤ G.arity x := hmin.pentagonal x
  have hhi : G.arity x < 12 :=
    G.dscore_cap1 (dscore1_le_five hred hmin) hx (by norm_num)
  -- and each of the seven presentations rules out one value
  interval_cases h : G.arity x
  · exact e5 hred G x hvalid h
  · exact e6 hred G x hvalid h
  · exact e7 hred G x hvalid h
  · exact e8 hred G x hvalid h
  · exact e9 hred G x hvalid h
  · exact e10 hred G x hvalid h
  · exact e11 hred G x hvalid h

end Hypermap

end FourColor
