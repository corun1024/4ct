import Lean

/-!
# Large numerals from chunks

A bulk mask is a number of a few million bits.  Lean's parser turns a numeral
into a `Nat` by a digit-at-a-time fold, which is quadratic in its length, so a
mask is written as a list of hexadecimal chunks of `2 ^ 14` bits instead.
`bignat% [c₀, c₁, …]` assembles them, least significant chunk first, *at
elaboration time*: the term it produces is a single `Nat` literal, which the
kernel reads directly.  Nothing is trusted here — the literal is checked like
any other by the declarations that use it.
-/

namespace FourColor.Bulk

open Lean Elab Term Meta in
/-- `bignat% [c₀, c₁, …]` is `c₀ + c₁ * 2 ^ 16384 + c₂ * 2 ^ 32768 + …`, as one literal. -/
elab "bignat%" "[" cs:num,* "]" : term => do
  let mut acc : Nat := 0
  for c in cs.getElems.reverse do
    acc := (acc <<< 16384) ||| c.getNat
  return mkNatLit acc

end FourColor.Bulk
