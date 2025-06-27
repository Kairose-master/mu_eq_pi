/-
  State monad (state set S is fixed once and for all)
  T_S X  =  S → (X × S)
  pure   =  λ x s, (x, s)
  bind   =  standard state‑monad bind
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

universe u v

namespace Jinu

variable (S : Type u)

structure StateMonadInst where
  T    : Type v → Type v := fun X => S → (X × S)
  pure : {X : Type v} → X → T X :=
    fun x s => (x, s)
  bind : {X Y : Type v} → T X → (X → T Y) → T Y :=
    fun f g s =>
      let (x, s') := f s
      g x s'

--  ▸  Monad laws (standard; proofs included for completeness)
lemma bind_pure {X : Type v} (M : StateMonadInst S)
    (f : M.T X) : M.bind f M.pure = f := by
  funext s
  dsimp [StateMonadInst.bind, StateMonadInst.pure]
  cases f s
  simp

lemma pure_bind {X Y : Type v} (M : StateMonadInst S)
    (x : X) (g : X → M.T Y) :
    M.bind (M.pure x) g = g x := rfl

lemma bind_assoc {X Y Z : Type v} (M : StateMonadInst S)
    (f : M.T X) (g : X → M.T Y) (h : Y → M.T Z) :
    M.bind (M.bind f g) h = M.bind f (fun x ↦ M.bind (g x) h) := by
  funext s
  dsimp [StateMonadInst.bind]
  cases f s with
  | _ x s₁ =>
    cases g x s₁
    rfl

end Jinu

