/-
  (ℝ-) 벡터공간을 래핑한 간단 구조체
  carrier : Type
  inst    : Module ℝ carrier
-/
import Mathlib.Algebra.Module.Basic

universe u

structure VSpace where
  carrier : Type u
  _inst   : Module ℝ carrier

notation "⟦" V "⟧" => V.carrier
