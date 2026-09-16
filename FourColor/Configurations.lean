import FourColor.CfMap

/-!
Translated from `configurations.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.

# The reducible configurations

The construction programs of the 633 reducible configurations, translated
mechanically from the reference's `configurations.v`.  Configuration number
`n` has index `n - 1` in `theConfigs`.
-/

namespace FourColor

/-- Configuration 1. -/
def cf001 : Config :=
  ⟨true, [13], [.H, .R 3, .H, .R 5, .H, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 2. -/
def cf002 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 6, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 3. -/
def cf003 : Config :=
  ⟨true, [17], [.H, .R 1, .H, .R 6, .H, .R 1, .Y, .R 4, .H, .R 6, .H, .R 6, .H, .R 6, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 4. -/
def cf004 : Config :=
  ⟨true, [1, 2, 12, 13], [.H, .R 2, .H, .R 7, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 5. -/
def cf005 : Config :=
  ⟨true, [10], [.H, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 6. -/
def cf006 : Config :=
  ⟨false, [19], [.H, .R 2, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 2, .H, .R 7, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 7. -/
def cf007 : Config :=
  ⟨true, [17], [.H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 8. -/
def cf008 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 9. -/
def cf009 : Config :=
  ⟨true, [26], [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y, .R 3, .H, .R 6, .H, .R 6, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 10. -/
def cf010 : Config :=
  ⟨false, [20], [.H, .R 2, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 3, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 11. -/
def cf011 : Config :=
  ⟨true, [1, 2, 8, 9], [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .Y, .R 2, .H, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 12. -/
def cf012 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .R 2, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 13. -/
def cf013 : Config :=
  ⟨false, [23], [.H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y, .R 6, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 14. -/
def cf014 : Config :=
  ⟨true, [14], [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 15. -/
def cf015 : Config :=
  ⟨false, [8, 9, 15, 16], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 16. -/
def cf016 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 17. -/
def cf017 : Config :=
  ⟨true, [26], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 18. -/
def cf018 : Config :=
  ⟨false, [26], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 19. -/
def cf019 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 20. -/
def cf020 : Config :=
  ⟨false, [1, 2, 8, 9], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 7, .H, .R 2, .H, .R 9, .Y, .R 5, .Y, .R 3, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 21. -/
def cf021 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 22. -/
def cf022 : Config :=
  ⟨false, [29], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 23. -/
def cf023 : Config :=
  ⟨false, [1, 2, 8, 9], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 24. -/
def cf024 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 7, .Y, .R 5, .H, .R 1, .Y, .R 5, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 25. -/
def cf025 : Config :=
  ⟨true, [25], [.H, .R 3, .H, .R 7, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 26. -/
def cf026 : Config :=
  ⟨false, [19], [.H, .R 7, .H, .R 1, .Y, .R 3, .H, .R 7, .Y, .R 4, .H, .R 5, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 27. -/
def cf027 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 6, .Y, .R 3, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 28. -/
def cf028 : Config :=
  ⟨false, [26], [.H, .R 2, .H, .R 9, .Y, .R 4, .H, .R 3, .H, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 29. -/
def cf029 : Config :=
  ⟨true, [4, 5, 21, 25], [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 30. -/
def cf030 : Config :=
  ⟨false, [19], [.H, .R 2, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 31. -/
def cf031 : Config :=
  ⟨false, [18], [.H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 32. -/
def cf032 : Config :=
  ⟨false, [23], [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 4, .H, .R 3, .H, .R 7, .H, .R 7, .Y, .R 6, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 33. -/
def cf033 : Config :=
  ⟨false, [24], [.H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 6, .Y, .R 4, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 34. -/
def cf034 : Config :=
  ⟨false, [15], [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y, .R 5, .H, .R 1, .Y, .R 4, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 35. -/
def cf035 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 6, .Y, .R 4, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 36. -/
def cf036 : Config :=
  ⟨true, [23], [.H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 37. -/
def cf037 : Config :=
  ⟨true, [23], [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y, .R 6, .H, .R 6, .Y, .R 4, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 38. -/
def cf038 : Config :=
  ⟨false, [10], [.H, .R 2, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 39. -/
def cf039 : Config :=
  ⟨true, [1, 2, 8, 9], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 3, .H, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 40. -/
def cf040 : Config :=
  ⟨false, [11, 12, 21, 26], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 41. -/
def cf041 : Config :=
  ⟨false, [20], [.H, .R 2, .H, .R 10, .Y, .R 5, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 42. -/
def cf042 : Config :=
  ⟨false, [23], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 43. -/
def cf043 : Config :=
  ⟨false, [30], [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 1, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 44. -/
def cf044 : Config :=
  ⟨false, [25], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 45. -/
def cf045 : Config :=
  ⟨true, [24], [.H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 1, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 46. -/
def cf046 : Config :=
  ⟨false, [18], [.H, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 1, .Y, .R 2, .H, .R 7, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 47. -/
def cf047 : Config :=
  ⟨true, [25], [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .Y, .R 4, .Y, .R 2, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 48. -/
def cf048 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 4, .H, .R 5, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 49. -/
def cf049 : Config :=
  ⟨false, [28], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 5, .Y, .R 4, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 50. -/
def cf050 : Config :=
  ⟨false, [27], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 51. -/
def cf051 : Config :=
  ⟨false, [14], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .H, .R 6, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 52. -/
def cf052 : Config :=
  ⟨false, [24], [.H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 53. -/
def cf053 : Config :=
  ⟨false, [23], [.H, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 54. -/
def cf054 : Config :=
  ⟨false, [28], [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 55. -/
def cf055 : Config :=
  ⟨false, [28], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 4, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 56. -/
def cf056 : Config :=
  ⟨false, [28], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 57. -/
def cf057 : Config :=
  ⟨false, [7], [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 7, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 58. -/
def cf058 : Config :=
  ⟨false, [26], [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 59. -/
def cf059 : Config :=
  ⟨false, [28], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 60. -/
def cf060 : Config :=
  ⟨false, [21], [.H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 7, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 61. -/
def cf061 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 62. -/
def cf062 : Config :=
  ⟨false, [8, 9, 15, 16], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .Y, .R 4, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 63. -/
def cf063 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 64. -/
def cf064 : Config :=
  ⟨false, [4, 5, 22, 27], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 6, .H, .R 7, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 65. -/
def cf065 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 66. -/
def cf066 : Config :=
  ⟨false, [1, 2, 8, 9], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 3, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 67. -/
def cf067 : Config :=
  ⟨false, [34], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 68. -/
def cf068 : Config :=
  ⟨false, [32], [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 69. -/
def cf069 : Config :=
  ⟨true, [25], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 70. -/
def cf070 : Config :=
  ⟨false, [33], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 5, .H, .R 8, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 71. -/
def cf071 : Config :=
  ⟨false, [21], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 72. -/
def cf072 : Config :=
  ⟨false, [25], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 73. -/
def cf073 : Config :=
  ⟨false, [25], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 74. -/
def cf074 : Config :=
  ⟨false, [15], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 3, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 75. -/
def cf075 : Config :=
  ⟨false, [15, 29], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .Y, .R 5, .Y, .R 3, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 76. -/
def cf076 : Config :=
  ⟨true, [27], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 77. -/
def cf077 : Config :=
  ⟨true, [14], [.H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 78. -/
def cf078 : Config :=
  ⟨false, [14], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 79. -/
def cf079 : Config :=
  ⟨false, [18], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .H, .R 5, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 80. -/
def cf080 : Config :=
  ⟨false, [27], [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 81. -/
def cf081 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 82. -/
def cf082 : Config :=
  ⟨false, [14], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 83. -/
def cf083 : Config :=
  ⟨false, [4, 5, 25, 30], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 84. -/
def cf084 : Config :=
  ⟨false, [20], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 85. -/
def cf085 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 86. -/
def cf086 : Config :=
  ⟨false, [26], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 87. -/
def cf087 : Config :=
  ⟨false, [25], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 88. -/
def cf088 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 9, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 89. -/
def cf089 : Config :=
  ⟨false, [8, 9, 15, 16], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 90. -/
def cf090 : Config :=
  ⟨true, [14, 15, 21, 22], [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 91. -/
def cf091 : Config :=
  ⟨false, [34], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .Y, .Y, .Y, .Y]⟩

/-- Configuration 92. -/
def cf092 : Config :=
  ⟨false, [28], [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 93. -/
def cf093 : Config :=
  ⟨false, [22], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 94. -/
def cf094 : Config :=
  ⟨false, [25], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 95. -/
def cf095 : Config :=
  ⟨false, [28], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 96. -/
def cf096 : Config :=
  ⟨false, [27], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 97. -/
def cf097 : Config :=
  ⟨false, [26], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 7, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 98. -/
def cf098 : Config :=
  ⟨false, [26], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 99. -/
def cf099 : Config :=
  ⟨false, [18], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 100. -/
def cf100 : Config :=
  ⟨true, [27], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 6, .Y, .Y, .Y, .Y, .Y]⟩

/-- Configuration 101. -/
def cf101 : Config :=
  ⟨false, [31], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 5, .H, .R 6, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 102. -/
def cf102 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 3, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 103. -/
def cf103 : Config :=
  ⟨false, [33], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 104. -/
def cf104 : Config :=
  ⟨true, [31, 33], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 5, .Y, .R 4, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 105. -/
def cf105 : Config :=
  ⟨false, [6], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 106. -/
def cf106 : Config :=
  ⟨false, [33], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 107. -/
def cf107 : Config :=
  ⟨false, [29], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 108. -/
def cf108 : Config :=
  ⟨false, [23], [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 109. -/
def cf109 : Config :=
  ⟨false, [6], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 110. -/
def cf110 : Config :=
  ⟨false, [32], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 111. -/
def cf111 : Config :=
  ⟨false, [23], [.H, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 112. -/
def cf112 : Config :=
  ⟨true, [23], [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 6, .H, .R 1, .Y, .R 6, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 113. -/
def cf113 : Config :=
  ⟨true, [6], [.H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 6, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 114. -/
def cf114 : Config :=
  ⟨false, [25], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 3, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 115. -/
def cf115 : Config :=
  ⟨false, [25], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 116. -/
def cf116 : Config :=
  ⟨true, [1, 2, 19, 24], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .H, .R 7, .Y, .R 2, .Y, .R 3, .Y, .R 4, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 117. -/
def cf117 : Config :=
  ⟨false, [14], [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .H, .R 6, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 118. -/
def cf118 : Config :=
  ⟨false, [23], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 4, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 119. -/
def cf119 : Config :=
  ⟨false, [6], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 4, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 120. -/
def cf120 : Config :=
  ⟨true, [6], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 121. -/
def cf121 : Config :=
  ⟨false, [28], [.H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 122. -/
def cf122 : Config :=
  ⟨false, [27], [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 123. -/
def cf123 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 124. -/
def cf124 : Config :=
  ⟨false, [12, 13, 28], [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y, .R 4, .Y, .R 5, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 125. -/
def cf125 : Config :=
  ⟨false, [26], [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 126. -/
def cf126 : Config :=
  ⟨false, [13], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 127. -/
def cf127 : Config :=
  ⟨false, [31], [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 128. -/
def cf128 : Config :=
  ⟨false, [4, 5, 18, 23], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 129. -/
def cf129 : Config :=
  ⟨false, [26], [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 8, .Y, .R 3, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 130. -/
def cf130 : Config :=
  ⟨false, [6], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 5, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 131. -/
def cf131 : Config :=
  ⟨false, [29], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 132. -/
def cf132 : Config :=
  ⟨false, [32], [.H, .R 4, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 133. -/
def cf133 : Config :=
  ⟨false, [34], [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 134. -/
def cf134 : Config :=
  ⟨false, [19], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 135. -/
def cf135 : Config :=
  ⟨true, [13], [.H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 136. -/
def cf136 : Config :=
  ⟨false, [14], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 137. -/
def cf137 : Config :=
  ⟨false, [29], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 138. -/
def cf138 : Config :=
  ⟨false, [18, 19, 29], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 139. -/
def cf139 : Config :=
  ⟨false, [7], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 140. -/
def cf140 : Config :=
  ⟨false, [12, 13, 29], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 4, .Y, .R 5, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 141. -/
def cf141 : Config :=
  ⟨true, [29], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 4, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 142. -/
def cf142 : Config :=
  ⟨false, [29], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 5, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 143. -/
def cf143 : Config :=
  ⟨false, [17, 22, 23, 28], [.H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 5, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 144. -/
def cf144 : Config :=
  ⟨false, [14], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 145. -/
def cf145 : Config :=
  ⟨false, [5, 19, 27, 29], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 146. -/
def cf146 : Config :=
  ⟨false, [26], [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 147. -/
def cf147 : Config :=
  ⟨false, [30], [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 148. -/
def cf148 : Config :=
  ⟨false, [13], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 149. -/
def cf149 : Config :=
  ⟨false, [29], [.H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 150. -/
def cf150 : Config :=
  ⟨false, [32], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 5, .H, .R 6, .Y, .R 3, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 151. -/
def cf151 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 152. -/
def cf152 : Config :=
  ⟨false, [4, 5, 22, 27], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 153. -/
def cf153 : Config :=
  ⟨false, [32], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 154. -/
def cf154 : Config :=
  ⟨false, [29], [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 155. -/
def cf155 : Config :=
  ⟨false, [26], [.H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 4, .H, .R 5, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 156. -/
def cf156 : Config :=
  ⟨false, [29], [.H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 157. -/
def cf157 : Config :=
  ⟨false, [6], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 158. -/
def cf158 : Config :=
  ⟨false, [6], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 5, .H, .R 7, .Y, .R 3, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 159. -/
def cf159 : Config :=
  ⟨false, [1, 2, 32], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 160. -/
def cf160 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 161. -/
def cf161 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 162. -/
def cf162 : Config :=
  ⟨false, [33], [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 163. -/
def cf163 : Config :=
  ⟨false, [33], [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 164. -/
def cf164 : Config :=
  ⟨false, [35], [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 165. -/
def cf165 : Config :=
  ⟨false, [36], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 166. -/
def cf166 : Config :=
  ⟨false, [11, 12, 18, 19], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 6, .H, .R 6, .Y, .R 5, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 167. -/
def cf167 : Config :=
  ⟨false, [33], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 168. -/
def cf168 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 169. -/
def cf169 : Config :=
  ⟨true, [11, 12, 18, 19], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 170. -/
def cf170 : Config :=
  ⟨false, [38], [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 10, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .Y, .R 7, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 171. -/
def cf171 : Config :=
  ⟨false, [26], [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 10, .H, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 6, .H, .R 6, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 172. -/
def cf172 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 10, .H, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 7, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 173. -/
def cf173 : Config :=
  ⟨false, [36], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 3, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .Y, .R 1, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 174. -/
def cf174 : Config :=
  ⟨false, [36], [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 175. -/
def cf175 : Config :=
  ⟨false, [20], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 176. -/
def cf176 : Config :=
  ⟨false, [20], [.H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 177. -/
def cf177 : Config :=
  ⟨false, [26], [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 178. -/
def cf178 : Config :=
  ⟨false, [29], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 6, .Y, .R 4, .Y, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 179. -/
def cf179 : Config :=
  ⟨false, [32], [.H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 6, .H, .R 6, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 180. -/
def cf180 : Config :=
  ⟨false, [7], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 4, .Y, .R 2, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 181. -/
def cf181 : Config :=
  ⟨false, [7, 29, 32], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 182. -/
def cf182 : Config :=
  ⟨false, [27], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 183. -/
def cf183 : Config :=
  ⟨false, [16, 32], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 4, .Y, .R 3, .H, .R 6, .Y, .R 2, .Y, .R 3, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 184. -/
def cf184 : Config :=
  ⟨false, [33], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 6, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 185. -/
def cf185 : Config :=
  ⟨false, [8, 31, 33], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 186. -/
def cf186 : Config :=
  ⟨false, [14], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 187. -/
def cf187 : Config :=
  ⟨false, [25, 30, 33], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 188. -/
def cf188 : Config :=
  ⟨false, [32], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 189. -/
def cf189 : Config :=
  ⟨false, [33], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .R 2, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 190. -/
def cf190 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 6, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 191. -/
def cf191 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 192. -/
def cf192 : Config :=
  ⟨false, [27], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 193. -/
def cf193 : Config :=
  ⟨false, [18, 21, 30, 33], [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 194. -/
def cf194 : Config :=
  ⟨false, [6, 10, 19, 33], [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 195. -/
def cf195 : Config :=
  ⟨false, [18], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 196. -/
def cf196 : Config :=
  ⟨false, [32], [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 197. -/
def cf197 : Config :=
  ⟨false, [24], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 6, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 198. -/
def cf198 : Config :=
  ⟨false, [33], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 5, .H, .R 7, .Y, .R 4, .Y, .R 3, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 199. -/
def cf199 : Config :=
  ⟨false, [21, 24, 30, 33], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 200. -/
def cf200 : Config :=
  ⟨false, [23], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 201. -/
def cf201 : Config :=
  ⟨false, [1, 2, 32], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 202. -/
def cf202 : Config :=
  ⟨false, [10], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 2, .H, .R 6, .Y, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 203. -/
def cf203 : Config :=
  ⟨false, [12, 13, 19, 20], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 204. -/
def cf204 : Config :=
  ⟨false, [36], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 6, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 205. -/
def cf205 : Config :=
  ⟨false, [35], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 9, .Y, .R 7, .Y, .R 7, .Y, .R 6, .H, .R 6, .Y, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 206. -/
def cf206 : Config :=
  ⟨false, [36], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 207. -/
def cf207 : Config :=
  ⟨false, [18, 19, 25, 26], [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 208. -/
def cf208 : Config :=
  ⟨false, [35], [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .R 6, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 209. -/
def cf209 : Config :=
  ⟨false, [26], [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 6, .H, .R 6, .H, .R 6, .Y, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 210. -/
def cf210 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 211. -/
def cf211 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 212. -/
def cf212 : Config :=
  ⟨false, [35], [.H, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 213. -/
def cf213 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 214. -/
def cf214 : Config :=
  ⟨false, [37], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 215. -/
def cf215 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 216. -/
def cf216 : Config :=
  ⟨false, [8, 9, 15, 16], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .Y, .R 4, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .Y, .Y, .R 5, .H, .R 6, .H, .R 6, .Y, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 217. -/
def cf217 : Config :=
  ⟨false, [8, 9, 15, 16], [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 7, .Y, .R 4, .H, .R 1, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 218. -/
def cf218 : Config :=
  ⟨false, [33], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 219. -/
def cf219 : Config :=
  ⟨false, [28], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 220. -/
def cf220 : Config :=
  ⟨false, [36], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 221. -/
def cf221 : Config :=
  ⟨false, [31], [.H, .R 3, .H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 222. -/
def cf222 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .Y, .R 3, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 223. -/
def cf223 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 2, .Y, .R 5, .H, .R 6, .Y, .R 2, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 224. -/
def cf224 : Config :=
  ⟨false, [36], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 8, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 225. -/
def cf225 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 6, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 226. -/
def cf226 : Config :=
  ⟨false, [35, 37], [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 6, .Y, .R 5, .Y, .R 4, .Y, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 227. -/
def cf227 : Config :=
  ⟨false, [30], [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .R 4, .Y, .R 2, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 228. -/
def cf228 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 7, .Y, .R 4, .Y, .R 4, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 229. -/
def cf229 : Config :=
  ⟨false, [36], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .R 3, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 230. -/
def cf230 : Config :=
  ⟨false, [7], [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 231. -/
def cf231 : Config :=
  ⟨false, [19], [.H, .R 10, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 232. -/
def cf232 : Config :=
  ⟨false, [11, 33, 37], [.H, .R 2, .H, .R 13, .Y, .R 5, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 233. -/
def cf233 : Config :=
  ⟨false, [35], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .H, .R 9, .Y, .R 6, .Y, .R 5, .Y, .Y, .R 4, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 234. -/
def cf234 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .Y, .R 5, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 235. -/
def cf235 : Config :=
  ⟨false, [32], [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 236. -/
def cf236 : Config :=
  ⟨false, [10], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 237. -/
def cf237 : Config :=
  ⟨false, [36], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 8, .Y, .R 8, .H, .R 8, .Y, .Y, .R 5, .Y, .R 4, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 238. -/
def cf238 : Config :=
  ⟨false, [43], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .Y, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 239. -/
def cf239 : Config :=
  ⟨false, [36], [.H, .R 4, .H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 240. -/
def cf240 : Config :=
  ⟨false, [38], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 241. -/
def cf241 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 242. -/
def cf242 : Config :=
  ⟨false, [14], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 243. -/
def cf243 : Config :=
  ⟨false, [32], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 244. -/
def cf244 : Config :=
  ⟨false, [32], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 245. -/
def cf245 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 246. -/
def cf246 : Config :=
  ⟨false, [1, 2, 30], [.H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 4, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 247. -/
def cf247 : Config :=
  ⟨false, [6], [.H, .R 10, .H, .R 1, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .Y, .R 3, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 248. -/
def cf248 : Config :=
  ⟨true, [31], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 249. -/
def cf249 : Config :=
  ⟨false, [26], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 250. -/
def cf250 : Config :=
  ⟨false, [20], [.H, .R 8, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .Y, .R 4, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 251. -/
def cf251 : Config :=
  ⟨false, [18], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 252. -/
def cf252 : Config :=
  ⟨false, [18], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 253. -/
def cf253 : Config :=
  ⟨false, [33], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 5, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 254. -/
def cf254 : Config :=
  ⟨false, [11, 12, 33], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 255. -/
def cf255 : Config :=
  ⟨false, [33], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .R 2, .Y, .R 3, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 256. -/
def cf256 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 257. -/
def cf257 : Config :=
  ⟨false, [33], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 258. -/
def cf258 : Config :=
  ⟨false, [24], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 259. -/
def cf259 : Config :=
  ⟨false, [4, 5, 22, 29], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 260. -/
def cf260 : Config :=
  ⟨false, [31], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 261. -/
def cf261 : Config :=
  ⟨false, [15, 16, 33], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 262. -/
def cf262 : Config :=
  ⟨false, [33], [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 4, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 263. -/
def cf263 : Config :=
  ⟨false, [21, 26, 33], [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 264. -/
def cf264 : Config :=
  ⟨true, [5, 30], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 4, .Y, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 265. -/
def cf265 : Config :=
  ⟨false, [14, 29, 31], [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 266. -/
def cf266 : Config :=
  ⟨false, [1, 2, 32], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 3, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 267. -/
def cf267 : Config :=
  ⟨false, [35], [.H, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 268. -/
def cf268 : Config :=
  ⟨false, [32], [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 269. -/
def cf269 : Config :=
  ⟨false, [33], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 5, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 270. -/
def cf270 : Config :=
  ⟨false, [33], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 271. -/
def cf271 : Config :=
  ⟨false, [18, 19, 33], [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 272. -/
def cf272 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 273. -/
def cf273 : Config :=
  ⟨false, [8], [.H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 274. -/
def cf274 : Config :=
  ⟨false, [36], [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 275. -/
def cf275 : Config :=
  ⟨false, [26], [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 276. -/
def cf276 : Config :=
  ⟨false, [6], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 277. -/
def cf277 : Config :=
  ⟨false, [36], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .H, .R 9, .H, .R 1, .Y, .R 8, .Y, .R 1, .Y, .R 1, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 278. -/
def cf278 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .H, .R 2, .H, .R 10, .Y, .R 3, .Y, .Y, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 279. -/
def cf279 : Config :=
  ⟨false, [40], [.H, .R 4, .H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 280. -/
def cf280 : Config :=
  ⟨false, [39], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 281. -/
def cf281 : Config :=
  ⟨false, [27, 30, 33], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 6, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 282. -/
def cf282 : Config :=
  ⟨false, [21], [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .R 5, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 283. -/
def cf283 : Config :=
  ⟨false, [7], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .R 3, .Y, .R 2, .Y, .R 2, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 284. -/
def cf284 : Config :=
  ⟨false, [36], [.H, .R 10, .H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 285. -/
def cf285 : Config :=
  ⟨false, [21], [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 286. -/
def cf286 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 287. -/
def cf287 : Config :=
  ⟨false, [28, 33, 37], [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 288. -/
def cf288 : Config :=
  ⟨false, [6, 12, 32, 34], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 289. -/
def cf289 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 290. -/
def cf290 : Config :=
  ⟨false, [27], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 291. -/
def cf291 : Config :=
  ⟨false, [36], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 292. -/
def cf292 : Config :=
  ⟨false, [18, 19, 37], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 293. -/
def cf293 : Config :=
  ⟨false, [34], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 4, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 294. -/
def cf294 : Config :=
  ⟨false, [28, 34, 36], [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 3, .Y, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 295. -/
def cf295 : Config :=
  ⟨false, [33], [.H, .R 10, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 296. -/
def cf296 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 297. -/
def cf297 : Config :=
  ⟨false, [8, 9, 30, 37], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 298. -/
def cf298 : Config :=
  ⟨false, [26, 33, 35], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 299. -/
def cf299 : Config :=
  ⟨false, [13, 31, 37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 300. -/
def cf300 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 2, .H, .R 1, .Y, .R 7, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 301. -/
def cf301 : Config :=
  ⟨false, [17], [.H, .R 12, .H, .R 1, .Y, .R 8, .H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 4, .Y, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 302. -/
def cf302 : Config :=
  ⟨false, [18, 19, 37], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 303. -/
def cf303 : Config :=
  ⟨true, [24, 29, 37], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 7, .H, .R 6, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .R 1, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 304. -/
def cf304 : Config :=
  ⟨true, [32], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .Y, .R 4, .Y, .R 1, .H, .R 5, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 305. -/
def cf305 : Config :=
  ⟨false, [37], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 10, .H, .R 10, .Y, .R 3, .Y, .R 5, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 306. -/
def cf306 : Config :=
  ⟨false, [35], [.H, .R 12, .H, .R 1, .Y, .R 8, .H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .Y, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 307. -/
def cf307 : Config :=
  ⟨false, [36], [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 10, .H, .R 10, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .Y, .Y, .R 1, .Y, .R 2, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 308. -/
def cf308 : Config :=
  ⟨false, [7], [.H, .R 5, .H, .R 13, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .H, .R 8, .Y, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 309. -/
def cf309 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 310. -/
def cf310 : Config :=
  ⟨false, [7], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .H, .R 8, .Y, .R 2, .Y, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 311. -/
def cf311 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 312. -/
def cf312 : Config :=
  ⟨false, [31], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 2, .Y, .R 5, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 313. -/
def cf313 : Config :=
  ⟨false, [42], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 314. -/
def cf314 : Config :=
  ⟨false, [33], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 315. -/
def cf315 : Config :=
  ⟨false, [42], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .Y, .R 6, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 316. -/
def cf316 : Config :=
  ⟨false, [6], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 9, .Y, .R 5, .H, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 317. -/
def cf317 : Config :=
  ⟨false, [46], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 9, .H, .R 9, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 318. -/
def cf318 : Config :=
  ⟨false, [37], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .R 6, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 319. -/
def cf319 : Config :=
  ⟨false, [35], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 320. -/
def cf320 : Config :=
  ⟨false, [14, 32, 34], [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 321. -/
def cf321 : Config :=
  ⟨false, [1, 2, 35], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 322. -/
def cf322 : Config :=
  ⟨false, [32], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 323. -/
def cf323 : Config :=
  ⟨false, [30], [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 324. -/
def cf324 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .H, .R 6, .H, .R 6, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 325. -/
def cf325 : Config :=
  ⟨true, [21], [.H, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .Y, .Y]⟩

/-- Configuration 326. -/
def cf326 : Config :=
  ⟨true, [29], [.H, .R 4, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 327. -/
def cf327 : Config :=
  ⟨false, [23], [.H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 5, .H, .R 5, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 328. -/
def cf328 : Config :=
  ⟨true, [0, 23], [.H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 329. -/
def cf329 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 4, .H, .R 7, .Y, .R 4, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 330. -/
def cf330 : Config :=
  ⟨true, [14, 15, 21, 26], [.H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 331. -/
def cf331 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 4, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 332. -/
def cf332 : Config :=
  ⟨false, [30], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 333. -/
def cf333 : Config :=
  ⟨false, [25], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 334. -/
def cf334 : Config :=
  ⟨true, [24], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 335. -/
def cf335 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 4, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 336. -/
def cf336 : Config :=
  ⟨false, [18], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 337. -/
def cf337 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 7, .Y, .R 5, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 338. -/
def cf338 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .R 5, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 339. -/
def cf339 : Config :=
  ⟨false, [12], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 5, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 340. -/
def cf340 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y, .R 5, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 341. -/
def cf341 : Config :=
  ⟨true, [26], [.H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 6, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 342. -/
def cf342 : Config :=
  ⟨false, [12, 13, 28], [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 343. -/
def cf343 : Config :=
  ⟨true, [1, 2, 8, 9], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 4, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 344. -/
def cf344 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 4, .H, .R 7, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 345. -/
def cf345 : Config :=
  ⟨false, [25], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 4, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 346. -/
def cf346 : Config :=
  ⟨false, [28], [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 347. -/
def cf347 : Config :=
  ⟨false, [4, 5, 24, 29], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 3, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 348. -/
def cf348 : Config :=
  ⟨false, [25], [.H, .R 4, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 7, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 349. -/
def cf349 : Config :=
  ⟨true, [24], [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 350. -/
def cf350 : Config :=
  ⟨false, [18], [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 351. -/
def cf351 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 1, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .R 2, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 352. -/
def cf352 : Config :=
  ⟨false, [21], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 8, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 353. -/
def cf353 : Config :=
  ⟨false, [29], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 354. -/
def cf354 : Config :=
  ⟨false, [11], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 5, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 355. -/
def cf355 : Config :=
  ⟨false, [25], [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 356. -/
def cf356 : Config :=
  ⟨false, [27], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 357. -/
def cf357 : Config :=
  ⟨false, [12, 13, 29], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 358. -/
def cf358 : Config :=
  ⟨false, [16, 17, 28], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 7, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 359. -/
def cf359 : Config :=
  ⟨false, [19], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .R 5, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 360. -/
def cf360 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 361. -/
def cf361 : Config :=
  ⟨false, [26], [.H, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 362. -/
def cf362 : Config :=
  ⟨false, [28], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 5, .H, .R 5, .Y, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 363. -/
def cf363 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 4, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 364. -/
def cf364 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 365. -/
def cf365 : Config :=
  ⟨false, [21], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 366. -/
def cf366 : Config :=
  ⟨false, [29], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 367. -/
def cf367 : Config :=
  ⟨false, [32], [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 368. -/
def cf368 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y, .R 5, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 369. -/
def cf369 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .R 6, .Y, .R 5, .H, .R 1, .H, .R 5, .H, .R 1, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 370. -/
def cf370 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 371. -/
def cf371 : Config :=
  ⟨true, [4, 5, 24, 29], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 372. -/
def cf372 : Config :=
  ⟨false, [4, 5, 18, 23], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 373. -/
def cf373 : Config :=
  ⟨false, [33], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 374. -/
def cf374 : Config :=
  ⟨false, [30], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y, .R 8, .H, .R 8, .Y, .R 2, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 375. -/
def cf375 : Config :=
  ⟨false, [37], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 6, .H, .R 1, .H, .R 2, .H, .R 9, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 376. -/
def cf376 : Config :=
  ⟨false, [21], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 3, .H, .R 8, .H, .R 1, .Y, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 377. -/
def cf377 : Config :=
  ⟨false, [29], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 378. -/
def cf378 : Config :=
  ⟨false, [18], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 3, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 379. -/
def cf379 : Config :=
  ⟨false, [30], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 380. -/
def cf380 : Config :=
  ⟨false, [30, 33], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 381. -/
def cf381 : Config :=
  ⟨false, [31], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 382. -/
def cf382 : Config :=
  ⟨false, [25], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .R 6, .Y, .R 4, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 383. -/
def cf383 : Config :=
  ⟨false, [14], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 384. -/
def cf384 : Config :=
  ⟨false, [33], [.H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 385. -/
def cf385 : Config :=
  ⟨false, [32], [.H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 386. -/
def cf386 : Config :=
  ⟨false, [29], [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 387. -/
def cf387 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 388. -/
def cf388 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 4, .H, .R 5, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 5, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 389. -/
def cf389 : Config :=
  ⟨false, [18], [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 390. -/
def cf390 : Config :=
  ⟨true, [25], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 391. -/
def cf391 : Config :=
  ⟨true, [36], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 9, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 392. -/
def cf392 : Config :=
  ⟨false, [27], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 1, .H, .R 1, .H, .R 9, .H, .R 9, .Y, .Y, .R 1, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 393. -/
def cf393 : Config :=
  ⟨false, [21], [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .H, .R 9, .H, .R 9, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 394. -/
def cf394 : Config :=
  ⟨false, [16, 17, 32], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 5, .H, .R 6, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 395. -/
def cf395 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 396. -/
def cf396 : Config :=
  ⟨false, [18], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 397. -/
def cf397 : Config :=
  ⟨false, [34], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 398. -/
def cf398 : Config :=
  ⟨false, [33], [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .Y, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 399. -/
def cf399 : Config :=
  ⟨false, [18], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 3, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 400. -/
def cf400 : Config :=
  ⟨false, [26], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 401. -/
def cf401 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 13, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .H, .R 8, .Y, .R 4, .Y, .R 4, .Y, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 402. -/
def cf402 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 403. -/
def cf403 : Config :=
  ⟨false, [26], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 4, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 404. -/
def cf404 : Config :=
  ⟨false, [0, 23], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .H, .R 7, .Y, .R 5, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 405. -/
def cf405 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 406. -/
def cf406 : Config :=
  ⟨false, [21], [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 7, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 407. -/
def cf407 : Config :=
  ⟨false, [18], [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 408. -/
def cf408 : Config :=
  ⟨false, [34], [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .R 6, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 409. -/
def cf409 : Config :=
  ⟨false, [25], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 410. -/
def cf410 : Config :=
  ⟨false, [1, 2, 28], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 411. -/
def cf411 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 412. -/
def cf412 : Config :=
  ⟨false, [28], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 413. -/
def cf413 : Config :=
  ⟨false, [25], [.H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 414. -/
def cf414 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 415. -/
def cf415 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 416. -/
def cf416 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 4, .H, .R 5, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 417. -/
def cf417 : Config :=
  ⟨false, [31], [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 418. -/
def cf418 : Config :=
  ⟨false, [32], [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 419. -/
def cf419 : Config :=
  ⟨false, [29], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 4, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 3, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 420. -/
def cf420 : Config :=
  ⟨false, [32], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 421. -/
def cf421 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 5, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 422. -/
def cf422 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 423. -/
def cf423 : Config :=
  ⟨false, [26], [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 2, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 424. -/
def cf424 : Config :=
  ⟨false, [26], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 425. -/
def cf425 : Config :=
  ⟨false, [26], [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 426. -/
def cf426 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 427. -/
def cf427 : Config :=
  ⟨false, [28], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 5, .H, .R 6, .H, .R 6, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 428. -/
def cf428 : Config :=
  ⟨false, [19], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 429. -/
def cf429 : Config :=
  ⟨false, [27], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 4, .H, .R 7, .Y, .R 2, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 430. -/
def cf430 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .R 6, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 431. -/
def cf431 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 432. -/
def cf432 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 1, .Y, .R 6, .Y, .R 4, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 433. -/
def cf433 : Config :=
  ⟨false, [6], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 4, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 434. -/
def cf434 : Config :=
  ⟨false, [1, 2, 9, 22], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 3, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 435. -/
def cf435 : Config :=
  ⟨false, [11, 12, 30], [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 436. -/
def cf436 : Config :=
  ⟨false, [22], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 437. -/
def cf437 : Config :=
  ⟨false, [28], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 438. -/
def cf438 : Config :=
  ⟨false, [25], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 9, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 439. -/
def cf439 : Config :=
  ⟨false, [35], [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .R 6, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 440. -/
def cf440 : Config :=
  ⟨false, [12, 28, 32, 35], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 441. -/
def cf441 : Config :=
  ⟨false, [29], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 442. -/
def cf442 : Config :=
  ⟨false, [32], [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 443. -/
def cf443 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 444. -/
def cf444 : Config :=
  ⟨false, [6], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 445. -/
def cf445 : Config :=
  ⟨false, [23], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 446. -/
def cf446 : Config :=
  ⟨false, [8], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 447. -/
def cf447 : Config :=
  ⟨false, [8, 9, 30, 32], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .R 4, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 448. -/
def cf448 : Config :=
  ⟨false, [32], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 449. -/
def cf449 : Config :=
  ⟨false, [33], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 2, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 450. -/
def cf450 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 451. -/
def cf451 : Config :=
  ⟨false, [27], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 452. -/
def cf452 : Config :=
  ⟨false, [0, 27], [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 453. -/
def cf453 : Config :=
  ⟨false, [27], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 454. -/
def cf454 : Config :=
  ⟨false, [15, 30, 33], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 455. -/
def cf455 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 456. -/
def cf456 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 457. -/
def cf457 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 458. -/
def cf458 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 459. -/
def cf459 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 460. -/
def cf460 : Config :=
  ⟨false, [16, 17, 32], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 461. -/
def cf461 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 462. -/
def cf462 : Config :=
  ⟨false, [16, 17, 32], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 463. -/
def cf463 : Config :=
  ⟨false, [12, 13, 32], [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y, .R 5, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 464. -/
def cf464 : Config :=
  ⟨false, [1, 2, 32], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 465. -/
def cf465 : Config :=
  ⟨false, [26], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 466. -/
def cf466 : Config :=
  ⟨false, [23], [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 467. -/
def cf467 : Config :=
  ⟨false, [32], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 468. -/
def cf468 : Config :=
  ⟨false, [33], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 4, .H, .R 6, .H, .R 6, .Y, .R 3, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 469. -/
def cf469 : Config :=
  ⟨false, [1, 2, 13, 23], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 470. -/
def cf470 : Config :=
  ⟨false, [11, 12, 33], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 471. -/
def cf471 : Config :=
  ⟨false, [19, 20, 33], [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 472. -/
def cf472 : Config :=
  ⟨false, [33], [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 473. -/
def cf473 : Config :=
  ⟨false, [18], [.H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .H, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y, .Y]⟩

/-- Configuration 474. -/
def cf474 : Config :=
  ⟨false, [21], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 6, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 475. -/
def cf475 : Config :=
  ⟨false, [8, 33, 36], [.H, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 476. -/
def cf476 : Config :=
  ⟨false, [33], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 5, .H, .R 5, .H, .R 10, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 477. -/
def cf477 : Config :=
  ⟨false, [33, 36], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 478. -/
def cf478 : Config :=
  ⟨false, [30, 32, 36], [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 5, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 479. -/
def cf479 : Config :=
  ⟨false, [15, 16, 33], [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 480. -/
def cf480 : Config :=
  ⟨false, [20, 24, 36], [.H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 481. -/
def cf481 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 482. -/
def cf482 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 483. -/
def cf483 : Config :=
  ⟨false, [32], [.H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y, .Y]⟩

/-- Configuration 484. -/
def cf484 : Config :=
  ⟨false, [23], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 3, .Y, .Y, .R 3, .H, .R 5, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 485. -/
def cf485 : Config :=
  ⟨false, [30], [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 486. -/
def cf486 : Config :=
  ⟨false, [36], [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 8, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 10, .H, .R 10, .Y, .Y, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 487. -/
def cf487 : Config :=
  ⟨false, [36], [.H, .R 9, .H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 488. -/
def cf488 : Config :=
  ⟨false, [10, 11, 40], [.H, .R 10, .H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 489. -/
def cf489 : Config :=
  ⟨false, [8, 31, 35, 37], [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 6, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 490. -/
def cf490 : Config :=
  ⟨false, [19], [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 491. -/
def cf491 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .R 4, .H, .R 2, .H, .R 7, .Y, .H, .R 1, .Y, .R 4, .H, .R 5, .Y, .R 3, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 492. -/
def cf492 : Config :=
  ⟨false, [34], [.H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 493. -/
def cf493 : Config :=
  ⟨false, [26, 27, 37], [.H, .R 10, .H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .R 4, .Y, .R 2, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 494. -/
def cf494 : Config :=
  ⟨false, [37], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 495. -/
def cf495 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 496. -/
def cf496 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 497. -/
def cf497 : Config :=
  ⟨false, [8], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 4, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 498. -/
def cf498 : Config :=
  ⟨false, [29, 34, 36], [.H, .R 3, .H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 6, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 499. -/
def cf499 : Config :=
  ⟨false, [36], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 6, .Y, .R 3, .Y, .R 3, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 500. -/
def cf500 : Config :=
  ⟨false, [34, 37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 501. -/
def cf501 : Config :=
  ⟨false, [33], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 502. -/
def cf502 : Config :=
  ⟨false, [34], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 6, .H, .R 8, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 503. -/
def cf503 : Config :=
  ⟨false, [34], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 504. -/
def cf504 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 505. -/
def cf505 : Config :=
  ⟨false, [8], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y, .R 2, .Y]⟩

/-- Configuration 506. -/
def cf506 : Config :=
  ⟨false, [36], [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 507. -/
def cf507 : Config :=
  ⟨false, [37], [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 7, .Y, .R 4, .Y, .R 1, .Y, .Y, .Y, .Y]⟩

/-- Configuration 508. -/
def cf508 : Config :=
  ⟨false, [6], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 2, .H, .R 5, .Y, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 509. -/
def cf509 : Config :=
  ⟨false, [35], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 510. -/
def cf510 : Config :=
  ⟨false, [8, 9, 30, 37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 4, .Y, .Y, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .Y, .Y]⟩

/-- Configuration 511. -/
def cf511 : Config :=
  ⟨false, [21, 25, 37], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 512. -/
def cf512 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 513. -/
def cf513 : Config :=
  ⟨false, [37, 39], [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 4, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 514. -/
def cf514 : Config :=
  ⟨false, [36], [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 515. -/
def cf515 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 516. -/
def cf516 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 517. -/
def cf517 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 2, .H, .R 1, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 518. -/
def cf518 : Config :=
  ⟨false, [25], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 2, .H, .R 9, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 519. -/
def cf519 : Config :=
  ⟨false, [6], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 7, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 4, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 3, .Y, .R 4, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 520. -/
def cf520 : Config :=
  ⟨false, [1, 2, 31], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 521. -/
def cf521 : Config :=
  ⟨false, [2, 31], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 522. -/
def cf522 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 3, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 523. -/
def cf523 : Config :=
  ⟨false, [34], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .H, .R 6, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 524. -/
def cf524 : Config :=
  ⟨false, [3, 36], [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .R 2, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 525. -/
def cf525 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 526. -/
def cf526 : Config :=
  ⟨false, [34], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .H, .R 2, .H, .R 9, .Y, .R 6, .Y, .R 1, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 527. -/
def cf527 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 5, .Y, .R 2, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 528. -/
def cf528 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 5, .H, .R 7, .H, .R 7, .Y, .R 1, .H, .R 1, .Y, .R 2, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 529. -/
def cf529 : Config :=
  ⟨true, [35], [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 530. -/
def cf530 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .H, .R 6, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 531. -/
def cf531 : Config :=
  ⟨false, [34], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 532. -/
def cf532 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 533. -/
def cf533 : Config :=
  ⟨false, [12, 33, 37], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 534. -/
def cf534 : Config :=
  ⟨false, [13, 20, 30], [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 535. -/
def cf535 : Config :=
  ⟨false, [7], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 536. -/
def cf536 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 537. -/
def cf537 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 538. -/
def cf538 : Config :=
  ⟨false, [33], [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 3, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 539. -/
def cf539 : Config :=
  ⟨false, [6], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 540. -/
def cf540 : Config :=
  ⟨false, [35], [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 541. -/
def cf541 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .Y, .R 4, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 542. -/
def cf542 : Config :=
  ⟨false, [34], [.H, .R 3, .H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .Y, .R 3, .Y, .R 2, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 543. -/
def cf543 : Config :=
  ⟨false, [34], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 544. -/
def cf544 : Config :=
  ⟨false, [34], [.H, .R 10, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 545. -/
def cf545 : Config :=
  ⟨false, [4, 5, 36], [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .Y, .R 6, .Y, .R 1, .Y, .R 4, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 546. -/
def cf546 : Config :=
  ⟨false, [36], [.H, .R 5, .H, .R 13, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 10, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 547. -/
def cf547 : Config :=
  ⟨false, [34], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 548. -/
def cf548 : Config :=
  ⟨false, [38], [.H, .R 2, .H, .R 13, .Y, .R 6, .H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 549. -/
def cf549 : Config :=
  ⟨false, [33], [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 550. -/
def cf550 : Config :=
  ⟨false, [38], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .R 7, .H, .R 7, .H, .R 7, .H, .R 2, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 551. -/
def cf551 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 552. -/
def cf552 : Config :=
  ⟨false, [19, 20, 40], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 8, .H, .R 8, .Y, .R 7, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 553. -/
def cf553 : Config :=
  ⟨false, [36], [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 6, .H, .R 5, .H, .R 11, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 10, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 5, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 554. -/
def cf554 : Config :=
  ⟨false, [40], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 555. -/
def cf555 : Config :=
  ⟨false, [37], [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 7, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 556. -/
def cf556 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 557. -/
def cf557 : Config :=
  ⟨false, [10, 31], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 558. -/
def cf558 : Config :=
  ⟨false, [27], [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 4, .Y, .Y, .Y]⟩

/-- Configuration 559. -/
def cf559 : Config :=
  ⟨false, [32], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 560. -/
def cf560 : Config :=
  ⟨false, [23], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 3, .Y, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 561. -/
def cf561 : Config :=
  ⟨false, [29], [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 2, .H, .R 1, .Y, .R 2, .Y, .Y, .Y]⟩

/-- Configuration 562. -/
def cf562 : Config :=
  ⟨true, [33], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 4, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 563. -/
def cf563 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 564. -/
def cf564 : Config :=
  ⟨false, [8, 9, 34], [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 6, .H, .R 7, .Y, .R 3, .Y, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 565. -/
def cf565 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .H, .R 7, .Y, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 566. -/
def cf566 : Config :=
  ⟨false, [17], [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .H, .R 6, .Y, .R 5, .Y, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 567. -/
def cf567 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .R 5, .Y, .Y, .Y, .Y, .Y]⟩

/-- Configuration 568. -/
def cf568 : Config :=
  ⟨true, [24], [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .Y, .Y, .Y]⟩

/-- Configuration 569. -/
def cf569 : Config :=
  ⟨true, [23], [.H, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 570. -/
def cf570 : Config :=
  ⟨false, [27], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 571. -/
def cf571 : Config :=
  ⟨false, [27], [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 6, .H, .R 1, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 572. -/
def cf572 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 573. -/
def cf573 : Config :=
  ⟨false, [24], [.H, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 574. -/
def cf574 : Config :=
  ⟨false, [33], [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 10, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 575. -/
def cf575 : Config :=
  ⟨false, [12, 13, 28], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 576. -/
def cf576 : Config :=
  ⟨true, [27], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 6, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 577. -/
def cf577 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 4, .H, .R 5, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 578. -/
def cf578 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 579. -/
def cf579 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 580. -/
def cf580 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 8, .Y, .R 6, .Y, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 581. -/
def cf581 : Config :=
  ⟨true, [31], [.H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 582. -/
def cf582 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .R 6, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 583. -/
def cf583 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 584. -/
def cf584 : Config :=
  ⟨false, [8, 9, 33], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 6, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 2, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 585. -/
def cf585 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 586. -/
def cf586 : Config :=
  ⟨false, [30], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 587. -/
def cf587 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 588. -/
def cf588 : Config :=
  ⟨false, [24], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 589. -/
def cf589 : Config :=
  ⟨false, [16, 17, 31], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 590. -/
def cf590 : Config :=
  ⟨false, [7], [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 591. -/
def cf591 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 592. -/
def cf592 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .R 6, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 593. -/
def cf593 : Config :=
  ⟨false, [15], [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 8, .H, .R 1, .Y, .R 7, .Y, .R 5, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 594. -/
def cf594 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 9, .Y, .R 3, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 595. -/
def cf595 : Config :=
  ⟨false, [41], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 1, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .H, .R 9, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 596. -/
def cf596 : Config :=
  ⟨false, [16, 17, 24], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 597. -/
def cf597 : Config :=
  ⟨true, [19, 20, 36], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 4, .H, .R 5, .Y, .R 3, .Y, .Y, .Y]⟩

/-- Configuration 598. -/
def cf598 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 599. -/
def cf599 : Config :=
  ⟨false, [30], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 4, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 600. -/
def cf600 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 4, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 601. -/
def cf601 : Config :=
  ⟨false, [1, 2, 26, 32], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 602. -/
def cf602 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 603. -/
def cf603 : Config :=
  ⟨false, [31], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 604. -/
def cf604 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 605. -/
def cf605 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 9, .Y, .R 7, .Y, .Y, .Y, .R 4, .H, .R 5, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 606. -/
def cf606 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 607. -/
def cf607 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .R 2, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 608. -/
def cf608 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .Y, .R 1, .Y, .R 3, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 609. -/
def cf609 : Config :=
  ⟨false, [27], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 610. -/
def cf610 : Config :=
  ⟨false, [29], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 5, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .Y]⟩

/-- Configuration 611. -/
def cf611 : Config :=
  ⟨false, [23], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 6, .Y, .R 1, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 612. -/
def cf612 : Config :=
  ⟨false, [23], [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 1, .Y, .R 4, .Y, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .Y, .Y]⟩

/-- Configuration 613. -/
def cf613 : Config :=
  ⟨false, [16, 17, 32], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 614. -/
def cf614 : Config :=
  ⟨false, [11, 12, 33], [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 615. -/
def cf615 : Config :=
  ⟨false, [12, 13, 30, 36], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .H, .R 6, .Y, .R 3, .Y, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 616. -/
def cf616 : Config :=
  ⟨false, [30], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 5, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 617. -/
def cf617 : Config :=
  ⟨false, [30], [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y]⟩

/-- Configuration 618. -/
def cf618 : Config :=
  ⟨false, [35], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y]⟩

/-- Configuration 619. -/
def cf619 : Config :=
  ⟨false, [35], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 7, .Y, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 620. -/
def cf620 : Config :=
  ⟨true, [31], [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 6, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y]⟩

/-- Configuration 621. -/
def cf621 : Config :=
  ⟨false, [34], [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y]⟩

/-- Configuration 622. -/
def cf622 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .Y, .Y]⟩

/-- Configuration 623. -/
def cf623 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 7, .H, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 624. -/
def cf624 : Config :=
  ⟨false, [31], [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 625. -/
def cf625 : Config :=
  ⟨false, [12, 13, 32], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 626. -/
def cf626 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 627. -/
def cf627 : Config :=
  ⟨true, [30], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y]⟩

/-- Configuration 628. -/
def cf628 : Config :=
  ⟨false, [6], [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩

/-- Configuration 629. -/
def cf629 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 630. -/
def cf630 : Config :=
  ⟨false, [27], [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .Y, .R 2, .Y, .R 2, .Y]⟩

/-- Configuration 631. -/
def cf631 : Config :=
  ⟨false, [31], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 5, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y]⟩

/-- Configuration 632. -/
def cf632 : Config :=
  ⟨false, [35], [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y]⟩

/-- Configuration 633. -/
def cf633 : Config :=
  ⟨true, [6], [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .Y, .Y, .Y]⟩

/-- The construction programs of the reducible configurations;
configuration number `n` has index `n - 1`. -/
def theConfigs : List Config :=
  [cf001,
   cf002,
   cf003,
   cf004,
   cf005,
   cf006,
   cf007,
   cf008,
   cf009,
   cf010,
   cf011,
   cf012,
   cf013,
   cf014,
   cf015,
   cf016,
   cf017,
   cf018,
   cf019,
   cf020,
   cf021,
   cf022,
   cf023,
   cf024,
   cf025,
   cf026,
   cf027,
   cf028,
   cf029,
   cf030,
   cf031,
   cf032,
   cf033,
   cf034,
   cf035,
   cf036,
   cf037,
   cf038,
   cf039,
   cf040,
   cf041,
   cf042,
   cf043,
   cf044,
   cf045,
   cf046,
   cf047,
   cf048,
   cf049,
   cf050,
   cf051,
   cf052,
   cf053,
   cf054,
   cf055,
   cf056,
   cf057,
   cf058,
   cf059,
   cf060,
   cf061,
   cf062,
   cf063,
   cf064,
   cf065,
   cf066,
   cf067,
   cf068,
   cf069,
   cf070,
   cf071,
   cf072,
   cf073,
   cf074,
   cf075,
   cf076,
   cf077,
   cf078,
   cf079,
   cf080,
   cf081,
   cf082,
   cf083,
   cf084,
   cf085,
   cf086,
   cf087,
   cf088,
   cf089,
   cf090,
   cf091,
   cf092,
   cf093,
   cf094,
   cf095,
   cf096,
   cf097,
   cf098,
   cf099,
   cf100,
   cf101,
   cf102,
   cf103,
   cf104,
   cf105,
   cf106,
   cf107,
   cf108,
   cf109,
   cf110,
   cf111,
   cf112,
   cf113,
   cf114,
   cf115,
   cf116,
   cf117,
   cf118,
   cf119,
   cf120,
   cf121,
   cf122,
   cf123,
   cf124,
   cf125,
   cf126,
   cf127,
   cf128,
   cf129,
   cf130,
   cf131,
   cf132,
   cf133,
   cf134,
   cf135,
   cf136,
   cf137,
   cf138,
   cf139,
   cf140,
   cf141,
   cf142,
   cf143,
   cf144,
   cf145,
   cf146,
   cf147,
   cf148,
   cf149,
   cf150,
   cf151,
   cf152,
   cf153,
   cf154,
   cf155,
   cf156,
   cf157,
   cf158,
   cf159,
   cf160,
   cf161,
   cf162,
   cf163,
   cf164,
   cf165,
   cf166,
   cf167,
   cf168,
   cf169,
   cf170,
   cf171,
   cf172,
   cf173,
   cf174,
   cf175,
   cf176,
   cf177,
   cf178,
   cf179,
   cf180,
   cf181,
   cf182,
   cf183,
   cf184,
   cf185,
   cf186,
   cf187,
   cf188,
   cf189,
   cf190,
   cf191,
   cf192,
   cf193,
   cf194,
   cf195,
   cf196,
   cf197,
   cf198,
   cf199,
   cf200,
   cf201,
   cf202,
   cf203,
   cf204,
   cf205,
   cf206,
   cf207,
   cf208,
   cf209,
   cf210,
   cf211,
   cf212,
   cf213,
   cf214,
   cf215,
   cf216,
   cf217,
   cf218,
   cf219,
   cf220,
   cf221,
   cf222,
   cf223,
   cf224,
   cf225,
   cf226,
   cf227,
   cf228,
   cf229,
   cf230,
   cf231,
   cf232,
   cf233,
   cf234,
   cf235,
   cf236,
   cf237,
   cf238,
   cf239,
   cf240,
   cf241,
   cf242,
   cf243,
   cf244,
   cf245,
   cf246,
   cf247,
   cf248,
   cf249,
   cf250,
   cf251,
   cf252,
   cf253,
   cf254,
   cf255,
   cf256,
   cf257,
   cf258,
   cf259,
   cf260,
   cf261,
   cf262,
   cf263,
   cf264,
   cf265,
   cf266,
   cf267,
   cf268,
   cf269,
   cf270,
   cf271,
   cf272,
   cf273,
   cf274,
   cf275,
   cf276,
   cf277,
   cf278,
   cf279,
   cf280,
   cf281,
   cf282,
   cf283,
   cf284,
   cf285,
   cf286,
   cf287,
   cf288,
   cf289,
   cf290,
   cf291,
   cf292,
   cf293,
   cf294,
   cf295,
   cf296,
   cf297,
   cf298,
   cf299,
   cf300,
   cf301,
   cf302,
   cf303,
   cf304,
   cf305,
   cf306,
   cf307,
   cf308,
   cf309,
   cf310,
   cf311,
   cf312,
   cf313,
   cf314,
   cf315,
   cf316,
   cf317,
   cf318,
   cf319,
   cf320,
   cf321,
   cf322,
   cf323,
   cf324,
   cf325,
   cf326,
   cf327,
   cf328,
   cf329,
   cf330,
   cf331,
   cf332,
   cf333,
   cf334,
   cf335,
   cf336,
   cf337,
   cf338,
   cf339,
   cf340,
   cf341,
   cf342,
   cf343,
   cf344,
   cf345,
   cf346,
   cf347,
   cf348,
   cf349,
   cf350,
   cf351,
   cf352,
   cf353,
   cf354,
   cf355,
   cf356,
   cf357,
   cf358,
   cf359,
   cf360,
   cf361,
   cf362,
   cf363,
   cf364,
   cf365,
   cf366,
   cf367,
   cf368,
   cf369,
   cf370,
   cf371,
   cf372,
   cf373,
   cf374,
   cf375,
   cf376,
   cf377,
   cf378,
   cf379,
   cf380,
   cf381,
   cf382,
   cf383,
   cf384,
   cf385,
   cf386,
   cf387,
   cf388,
   cf389,
   cf390,
   cf391,
   cf392,
   cf393,
   cf394,
   cf395,
   cf396,
   cf397,
   cf398,
   cf399,
   cf400,
   cf401,
   cf402,
   cf403,
   cf404,
   cf405,
   cf406,
   cf407,
   cf408,
   cf409,
   cf410,
   cf411,
   cf412,
   cf413,
   cf414,
   cf415,
   cf416,
   cf417,
   cf418,
   cf419,
   cf420,
   cf421,
   cf422,
   cf423,
   cf424,
   cf425,
   cf426,
   cf427,
   cf428,
   cf429,
   cf430,
   cf431,
   cf432,
   cf433,
   cf434,
   cf435,
   cf436,
   cf437,
   cf438,
   cf439,
   cf440,
   cf441,
   cf442,
   cf443,
   cf444,
   cf445,
   cf446,
   cf447,
   cf448,
   cf449,
   cf450,
   cf451,
   cf452,
   cf453,
   cf454,
   cf455,
   cf456,
   cf457,
   cf458,
   cf459,
   cf460,
   cf461,
   cf462,
   cf463,
   cf464,
   cf465,
   cf466,
   cf467,
   cf468,
   cf469,
   cf470,
   cf471,
   cf472,
   cf473,
   cf474,
   cf475,
   cf476,
   cf477,
   cf478,
   cf479,
   cf480,
   cf481,
   cf482,
   cf483,
   cf484,
   cf485,
   cf486,
   cf487,
   cf488,
   cf489,
   cf490,
   cf491,
   cf492,
   cf493,
   cf494,
   cf495,
   cf496,
   cf497,
   cf498,
   cf499,
   cf500,
   cf501,
   cf502,
   cf503,
   cf504,
   cf505,
   cf506,
   cf507,
   cf508,
   cf509,
   cf510,
   cf511,
   cf512,
   cf513,
   cf514,
   cf515,
   cf516,
   cf517,
   cf518,
   cf519,
   cf520,
   cf521,
   cf522,
   cf523,
   cf524,
   cf525,
   cf526,
   cf527,
   cf528,
   cf529,
   cf530,
   cf531,
   cf532,
   cf533,
   cf534,
   cf535,
   cf536,
   cf537,
   cf538,
   cf539,
   cf540,
   cf541,
   cf542,
   cf543,
   cf544,
   cf545,
   cf546,
   cf547,
   cf548,
   cf549,
   cf550,
   cf551,
   cf552,
   cf553,
   cf554,
   cf555,
   cf556,
   cf557,
   cf558,
   cf559,
   cf560,
   cf561,
   cf562,
   cf563,
   cf564,
   cf565,
   cf566,
   cf567,
   cf568,
   cf569,
   cf570,
   cf571,
   cf572,
   cf573,
   cf574,
   cf575,
   cf576,
   cf577,
   cf578,
   cf579,
   cf580,
   cf581,
   cf582,
   cf583,
   cf584,
   cf585,
   cf586,
   cf587,
   cf588,
   cf589,
   cf590,
   cf591,
   cf592,
   cf593,
   cf594,
   cf595,
   cf596,
   cf597,
   cf598,
   cf599,
   cf600,
   cf601,
   cf602,
   cf603,
   cf604,
   cf605,
   cf606,
   cf607,
   cf608,
   cf609,
   cf610,
   cf611,
   cf612,
   cf613,
   cf614,
   cf615,
   cf616,
   cf617,
   cf618,
   cf619,
   cf620,
   cf621,
   cf622,
   cf623,
   cf624,
   cf625,
   cf626,
   cf627,
   cf628,
   cf629,
   cf630,
   cf631,
   cf632,
   cf633]

set_option maxRecDepth 8000 in
/-- There are 633 reducible configurations. -/
theorem length_theConfigs : theConfigs.length = 633 := rfl

end FourColor
