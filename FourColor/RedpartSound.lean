import FourColor.Present
import FourColor.TheQuizTree
import FourColor.CfReducible
import FourColor.Embed

/-!
# The reducibility test is sound

Tying the two halves of the development together.  `redpart` decides that every
2-neighbourhood matching a part contains an embedded configuration kernel; the
embedding theorem says a minimal counter-example contains no embedded kernel of
a reducible configuration.  So, granted that every configuration in the
database is reducible, a part `redpart` accepts fits no dart of a minimal
counter-example — which is exactly what the presentation scripts assume.
-/

namespace FourColor

/-- Every configuration of the database is C-reducible.  This is discharged by
the 633 reducibility computations. -/
def Reducibility : Prop := ReducibleInRange 0 theConfigs.length theConfigs

namespace Hypermap

variable {D : Type} [Finite D] {G : Hypermap D}

/-- A configuration of the database is C-reducible. -/
theorem cfReducible_of_mem (hred : Reducibility) {cf : Config} (hcf : cf ∈ theConfigs) :
    CfReducible cf := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcf
  have : theConfigs[i]! = theConfigs[i] := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact this ▸ hred i (Nat.zero_le i) hi

/-- The quiz tree fits nowhere in a minimal counter-example: a dart it fitted
would carry an embedded kernel of one of the configurations, and every one of
them is reducible. -/
theorem not_fit_theQuizTree (hred : Reducibility) (hmin : G.MinimalCounterExample)
    (x : D) : ¬ G.Fit x theQuizTree := by
  intro hfit
  obtain ⟨cf, hcf, hR, hex⟩ := fit_theQuizTree hmin.plain hmin.cubic x hfit
  obtain ⟨x₀, hvq⟩ := valid_cfquiz hR
  have hemb := embeddable_cfquiz hR
  have hpc : (cfmap cf).map.Plain := hemb.base.base.base.base.plain
  have hqc : (cfmap cf).map.Quasicubic (cfring cf) := hemb.base.base.base.base.quasicubic
  have hcr : (cfmap cf).map.CReducible (cfring cf) (cfcontract cf) :=
    cfReducible_of_mem hred hcf
  rcases hex with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact not_embed_reducible hemb hmin
      (quiz_preembedding hmin.plain hmin.cubic hpc hqc hvq hy) hcr
  · exact not_embed_reducible hemb hmin.mirror
      (quiz_preembedding ((plain_mirror G).mpr hmin.plain) ((cubic_mirror G).mpr hmin.cubic)
        hpc hqc hvq hy) hcr

end Hypermap

/-- **The reducibility test is sound**: a part `redpart` accepts fits no dart of
a minimal counter-example.  This is the hypothesis the presentation scripts
carry, so with it every `excludeN` becomes unconditional. -/
theorem redpartSound_theRedpart (hred : Reducibility) : RedpartSound theRedpart := by
  intro D _ G hmin y q hq
  exact Hypermap.no_fit_redpart hmin.plainCubicPentagonal
    (Hypermap.not_fit_theQuizTree hred hmin) hq y

end FourColor
