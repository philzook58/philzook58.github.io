import Std.Data.List.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

theorem foo : 1 = 1 := by
  -- library_search
  exact _root_.trans rfl rfl
#check _root_.trans

theorem bar : x <= 7 + 3*x := by
  linarith

#print bar
def hello := "world"