/-
Copyright (c) 2025 Jinu Jang. All rights reserved.
Released under the MIT license.
-/
import MuEqPi.StateMonad

/-!
# Where Part I meets the frontier: `μ` is not weakly cartesian

`MuEqPi.StateMonad` shows that the multiplication `μ` of the state monad is a
split epimorphism. A stronger property studied in current categorical
probability is that `μ` be **weakly cartesian**: every naturality square of `μ`

```
  T²X ──T²f──▶ T²Y
   │            │
  μ_X          μ_Y
   ▼            ▼
   TX ───Tf───▶ TY
```

is a *weak pullback* — whenever `Tf u = μ_Y v` there is some `w` with
`μ_X w = u` and `T²f w = v`. Bohinen and Perrone (*Categorical algebra of
conditional probability*, Appl. Cat. Struct. 34 (2026), arXiv:2502.14941)
prove this for the monads of Markov categories with conditionals satisfying the
equalizer principle — in particular for the Giry monad on standard Borel spaces
— and note it was previously known for the distribution monad on sets.

This file shows the **state monad fails it** as soon as the state type has two
elements. The obstruction is exactly the free inner state slot of Part I: the
compatibility condition `Tf u = μ_Y v` only constrains the inner computation at
the state the outer stage actually produces, while `T²f w = v` constrains it at
*every* state — so a non-surjective `f` cannot be lifted.

Being a split epimorphism, then, is where the state monad's `μ` stops; weak
cartesianness is a genuinely probabilistic phenomenon.

## Main results

* `MuEqPi.MuWeaklyCartesian` : the property, for the state monad on `S`.
* `MuEqPi.not_muWeaklyCartesian_bool` : it fails for `S = Bool`.
-/

universe u

namespace MuEqPi

/-- `μ` of the state monad on `S` is **weakly cartesian** if every naturality
square of `μ` is a weak pullback. -/
def MuWeaklyCartesian (S : Type u) : Prop :=
  ∀ {X Y : Type u} (f : X → Y) (u : St S X) (v : St S (St S Y)),
    St.map f u = St.mu v →
      ∃ w : St S (St S X), St.mu w = u ∧ St.map (St.map f) w = v

/-- **The state monad's `μ` is not weakly cartesian.** Witness: `S = Bool`,
`f : Unit → Bool` constantly `true`, and a nested computation `v` whose inner
stage returns `false` at the state the outer stage does *not* produce. The
compatibility `Tf u = μ v` holds because `μ` only ever looks at the produced
state, but no lift `w` exists because `T²f w = v` would force `f` to hit
`false`. -/
theorem not_muWeaklyCartesian_bool : ¬ MuWeaklyCartesian Bool := by
  intro h
  let f : Unit → Bool := fun _ => true
  let u : St Bool Unit := fun s => ((), s)
  let v : St Bool (St Bool Bool) := fun s => (fun t => (decide (t = s), t), s)
  have hc : St.map f u = St.mu v := by
    funext s
    simp [u, v, f, St.map, St.mu]
  obtain ⟨w, -, hw⟩ := h f u v hc
  have := congrArg (fun z : St Bool (St Bool Bool) => ((z true).1 false).1) hw
  simp [v, f, St.map] at this

end MuEqPi
