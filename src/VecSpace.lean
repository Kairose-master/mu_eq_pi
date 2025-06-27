/-
  매우 얇은 ℝ‑벡터공간 래퍼
  carrier : underlying type
  _inst   : Module ℝ carrier
-/
import Mathlib.Algebra.Module.Basic

universe u

structure VSpace where
  carrier : Type u
  _inst   : Module ℝ carrier

notation "⟦" V "⟧" => V.carrier
