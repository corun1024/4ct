import FourColor.RealPlane
import Mathlib.Topology.Connected.Basic

/-!
# The statement's elementary topology, against Mathlib's

`FourColor.RealPlane` states the Four Colour Theorem with elementary notions of
open, closed and connected regions, so that the statement can be read without
any topology library.  `isOpenRegion_iff` and `regionClosure_eq` there identify
the first two with Mathlib's.  This file identifies the third: for open regions
— the only ones the statement asks to be connected — the elementary
`IsConnectedRegion` is Mathlib's `IsPreconnected`.  Nothing in the proof depends
on this file; it exists so that the statement can be read either way.

## Main results

* `isConnectedRegion_iff_isPreconnected` — for an open region, elementary
  connectedness is Mathlib's preconnectedness.
* `simpleMap_iff` — a simple map is a plain map with open, preconnected regions.
-/

namespace FourColor

/-- Mathlib's preconnectedness implies the elementary connectedness, for every
region: the elementary notion only asks the two open sets to meet somewhere. -/
theorem isConnectedRegion_of_isPreconnected {r : Region} (h : IsPreconnected r) :
    IsConnectedRegion r := by
  intro u v hu hv hsub hur hvr
  obtain ⟨z, -, hzu, hzv⟩ := h u v ((isOpenRegion_iff u).mp hu) ((isOpenRegion_iff v).mp hv)
    hsub (by obtain ⟨z, hz⟩ := hur; exact ⟨z, hz.2, hz.1⟩)
    (by obtain ⟨z, hz⟩ := hvr; exact ⟨z, hz.2, hz.1⟩)
  exact ⟨z, hzu, hzv⟩

/-- **For an open region, elementary connectedness is Mathlib's
preconnectedness.**  Openness is what lets a separation of the region by two
open sets be shrunk to a pair of disjoint open sets. -/
theorem isConnectedRegion_iff_isPreconnected {r : Region} (hr : IsOpenRegion r) :
    IsConnectedRegion r ↔ IsPreconnected r := by
  refine ⟨fun h => ?_, isConnectedRegion_of_isPreconnected⟩
  intro u v hu hv hsub hru hrv
  have hr' := (isOpenRegion_iff r).mp hr
  have hm := h (u ∩ r) (v ∩ r) ((isOpenRegion_iff _).mpr (hu.inter hr'))
    ((isOpenRegion_iff _).mpr (hv.inter hr'))
    (fun z hz => by rcases hsub hz with h | h; exact Or.inl ⟨h, hz⟩; exact Or.inr ⟨h, hz⟩)
    (by obtain ⟨z, hzr, hzu⟩ := hru; exact ⟨z, ⟨hzu, hzr⟩, hzr⟩)
    (by obtain ⟨z, hzr, hzv⟩ := hrv; exact ⟨z, ⟨hzv, hzr⟩, hzr⟩)
  obtain ⟨z, ⟨hzu, hzr⟩, hzv, -⟩ := hm
  exact ⟨z, hzr, hzu, hzv⟩

/-- A simple map, read with Mathlib's notions. -/
theorem simpleMap_iff (m : PlaneMap) :
    SimpleMap m ↔ PlainMap m ∧ (∀ z, IsOpen (m z)) ∧ ∀ z, IsPreconnected (m z) := by
  constructor
  · intro h
    refine ⟨h.plain, fun z => (isOpenRegion_iff _).mp (h.isOpen z), fun z => ?_⟩
    exact (isConnectedRegion_iff_isPreconnected (h.isOpen z)).mp (h.isConnected z)
  · rintro ⟨hp, ho, hc⟩
    refine ⟨hp, fun z => (isOpenRegion_iff _).mpr (ho z), fun z => ?_⟩
    exact isConnectedRegion_of_isPreconnected (hc z)

end FourColor
