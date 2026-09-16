import FourColor.Present
import FourColor.TheQuizTree

/-!
Translated from `present5.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # The parts of the arity 5 presentation

The parts the case analysis of `present5.v` reaches, as literals so that the
kernel computations in the script do not have to reduce a chain of splits. -/

namespace FourColor

def p5_0 : Part := (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_1l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_1r : Part := (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def q5_1 : Part := (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_2r : Part := (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_3r : Part := (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_4r : Part := (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_5r : Part := (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_8l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_8r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def q5_8 : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_9r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_10l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_10r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def q5_10 : Part := (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_11r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_12l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_12r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def q5_12 : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_13r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr66 .pr59 Part.nil)))))
def p5_15l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr79 .pr59 Part.nil)))))
def p5_15r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr66 .pr59 Part.nil)))))
def p5_20r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_21r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_22l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_22r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr69 .pr59 Part.nil)))))
def p5_23r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr79 .pr59 Part.nil)))))
def p5_25r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr79 .pr59 Part.nil)))))
def p5_29l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr56 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_29r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def q5_29 : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr56 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_30r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr79 .pr59 Part.nil)))))
def p5_31l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr79 .pr59 Part.nil)))))
def p5_31r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 Part.nil)))))
def p5_35r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_36r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))
def p5_37l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr79 .pr59 Part.nil)))))
def p5_37r : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr56 .pr59 Part.nil)))))
def p5_38l : Part := (Part.cons .pr55 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr66 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr66 .pr59 Part.nil)))))
def src5 : List Part := [(Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil))))), (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil))))), (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr59 .pr59 Part.nil))))), (Part.cons .pr59 .pr59 (Part.cons .pr55 .pr59 (Part.cons .pr79 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil))))), (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr56 .pr59 (Part.cons .pr55 .pr59 Part.nil))))), (Part.cons .pr55 .pr59 (Part.cons .pr56 .pr59 (Part.cons .pr69 .pr59 (Part.cons .pr59 .pr59 (Part.cons .pr59 .pr59 Part.nil)))))]
def tgt5 : List Part := []

/-- Any `DruleFork` for this arity is the canonical one: the structure's proof
fields pin its data down. -/
theorem druleFork_uniq5 {conv : Part → PRange × Part} (rf : DruleFork conv 5) :
    rf = druleFork conv 5 := by
  cases rf with
  | mk _ _ hs ht => cases hs; cases ht; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- selecting the rules of an arity from `theDrules` is a second of kernel time;
-- done here once instead of inside every one of the checks below
/-- The discharge rules of arity 5, as a literal. -/
def rf5 : DruleFork Part.conversePart 5 :=
  ⟨src5, tgt5, by decide +kernel, by decide +kernel⟩

/-- `succeed_by_hubcap` against the precomputed rule fork. -/
theorem succeed_by_hubcap5 (hredp : RedpartSound theRedpart) (hc : Hubcap)
    {p₀ p : Part} (hsz : p.size = 5) (h2 : 2 ≤ p.size)
    (hcover : hubcapCover p.size hc = true)
    (hfitc : hubcapFit theRedpart rf5 p hc = true) :
    SucceedsIn p₀ p := by
  refine succeed_by_hubcap hredp hc h2 hcover ?_
  rw [hsz, ← druleFork_uniq5 rf5]
  exact hfitc

end FourColor
