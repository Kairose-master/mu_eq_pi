/-
Copyright (c) 2025 Jinu Jang. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

/-!
# The state monad `T_S X = S → X × S`

This file develops the state monad from first principles: the endofunctor `St S`,
its unit `η`, its multiplication `μ`, and complete proofs of the functor laws,
the naturality squares, and the three monad laws.

The point of the file is the last section. The slogan *"monadic flattening is an
idempotent projection"* cannot be read literally: `μ : T² ⇒ T` is a map between
two *different* functors, so the equation `μ ∘ μ = μ` does not even typecheck.
What is true — and is proved here — is the following.

* `St.mu_rightInverse` : `μ ∘ Tη = id`, i.e. `μ` is a **split epimorphism** with
  canonical section `Tη = St.map η`.
* `St.collapse_idem` : consequently `e := Tη ∘ μ : T² → T²` is an **idempotent**,
  and `(μ, Tη)` is a splitting of `e` through `T`.
* `St.collapse_ne_id` : `e` is a *proper* idempotent — it is not the identity —
  so the statement has genuine content.

This is the correct, type-checking form of the informal claim, and it is the
statement that the rest of the development transports into linear algebra.

## Main definitions

* `MuEqPi.St S X` : the carrier `S → X × S`.
* `MuEqPi.St.map`, `MuEqPi.St.eta`, `MuEqPi.St.mu`, `MuEqPi.St.bind`.
* `MuEqPi.St.collapse` : the idempotent `Tη ∘ μ` on `T²`.
-/

universe u

namespace MuEqPi

/-- The carrier of the state monad, `T_S X = S → X × S`. -/
def St (S X : Type u) : Type u := S → X × S

namespace St

variable {S X Y Z : Type u}

/-- The value returned by a stateful computation started in state `s`. -/
def val (t : St S X) (s : S) : X := (t s).1

/-- The state left behind by a stateful computation started in state `s`.
This function is the *state-transition function* of `t`; it is the data that
reappears in `MuEqPi.Projection` as the graph along which the linear projection
projects. -/
def next (t : St S X) (s : S) : S := (t s).2

@[simp] theorem val_def (t : St S X) (s : S) : val t s = (t s).1 := rfl
@[simp] theorem next_def (t : St S X) (s : S) : next t s = (t s).2 := rfl

/-- Functorial action of `T_S` on morphisms. -/
def map (f : X → Y) (t : St S X) : St S Y := fun s => (f (t s).1, (t s).2)

/-- The unit `η : X → T_S X`, "return without touching the state". -/
def eta (x : X) : St S X := fun s => (x, s)

/-- The multiplication `μ : T_S (T_S X) → T_S X`: run the outer computation,
then feed the state it produced to the inner computation. -/
def mu (t : St S (St S X)) : St S X := fun s => (t s).1 (t s).2

/-- Kleisli extension (`bind`). -/
def bind (t : St S X) (k : X → St S Y) : St S Y := fun s => k (t s).1 (t s).2

@[simp] theorem map_apply (f : X → Y) (t : St S X) (s : S) :
    map f t s = (f (t s).1, (t s).2) := rfl

@[simp] theorem eta_apply (x : X) (s : S) : eta x s = (x, s) := rfl

@[simp] theorem mu_apply (t : St S (St S X)) (s : S) :
    mu t s = (t s).1 (t s).2 := rfl

@[simp] theorem bind_apply (t : St S X) (k : X → St S Y) (s : S) :
    bind t k s = k (t s).1 (t s).2 := rfl

/-! ### Functor laws -/

theorem map_id : map (id : X → X) = (id : St S X → St S X) := by
  funext t s; simp

theorem map_comp (f : X → Y) (g : Y → Z) :
    map (g ∘ f) = (map g ∘ map f : St S X → St S Z) := rfl

/-! ### Naturality of the structure maps -/

theorem eta_naturality (f : X → Y) :
    map f ∘ (eta : X → St S X) = eta ∘ f := rfl

theorem mu_naturality (f : X → Y) :
    (mu : St S (St S Y) → St S Y) ∘ map (map f)
      = map f ∘ (mu : St S (St S X) → St S X) := rfl

/-! ### The three monad laws -/

/-- Left unit: `μ ∘ η_T = id`. -/
theorem mu_eta : (mu : St S (St S X) → St S X) ∘ eta = id := rfl

/-- Right unit: `μ ∘ Tη = id`. -/
theorem mu_map_eta : (mu : St S (St S X) → St S X) ∘ map eta = id := by
  funext t s; simp

/-- Associativity: `μ ∘ Tμ = μ ∘ μ_T`. -/
theorem mu_assoc :
    (mu : St S (St S X) → St S X) ∘ map mu
      = mu ∘ (mu : St S (St S (St S X)) → St S (St S X)) := rfl

/-- `bind` is `μ` applied to a functorial image: this is precisely the sense in
which `μ` *is* Kleisli composition. -/
theorem bind_eq_mu_map (t : St S X) (k : X → St S Y) :
    bind t k = mu (map k t) := rfl

/-! ### Agreement with Lean's monad hierarchy -/

instance instMonad : Monad (St S) where
  pure := eta
  bind := bind

@[simp] theorem pure_eq_eta (x : X) : (pure x : St S X) = eta x := rfl

@[simp] theorem bind_eq_bind (t : St S X) (k : X → St S Y) :
    (t >>= k) = bind t k := rfl

theorem functor_map_eq_map (f : X → Y) (t : St S X) : f <$> t = map f t := rfl

instance instLawfulMonad : LawfulMonad (St S) :=
  LawfulMonad.mk' _
    (fun t => by funext s; simp [functor_map_eq_map])
    (fun _ _ => rfl)
    (fun _ _ _ => rfl)

/-!
### `μ` as a split epimorphism and the idempotent it induces

`μ ∘ Tη = id` says that `μ` is a retraction. The composite in the other order is
therefore an idempotent endomorphism of `T²`, and `T` is the retract it splits
off. This is the type-correct replacement for the ill-typed `μ ∘ μ = μ`.
-/

/-- `Tη` is a section of `μ`. -/
theorem mu_rightInverse :
    Function.RightInverse (map eta : St S X → St S (St S X)) mu :=
  fun t => congrFun mu_map_eta t

/-- `μ` is a split epimorphism, in particular surjective. -/
theorem mu_surjective : Function.Surjective (mu : St S (St S X) → St S X) :=
  mu_rightInverse.surjective

/-- `Tη` is injective. -/
theorem map_eta_injective :
    Function.Injective (map eta : St S X → St S (St S X)) :=
  mu_rightInverse.injective

/-- The **collapse operator** `e = Tη ∘ μ : T² → T²`. Concretely it replaces a
nested computation by the flat computation with the same overall behaviour,
re-nested trivially. -/
def collapse : St S (St S X) → St S (St S X) := map eta ∘ mu

@[simp] theorem collapse_apply (t : St S (St S X)) :
    collapse t = map eta (mu t) := rfl

/-- **The collapse operator is idempotent.** -/
theorem collapse_idem :
    (collapse : St S (St S X) → St S (St S X)) ∘ collapse = collapse := by
  show map eta ∘ ((mu : St S (St S X) → St S X) ∘ map eta) ∘ mu = map eta ∘ mu
  rw [mu_map_eta]
  rfl

/-- The splitting of `collapse` through `T`, half one. -/
theorem mu_collapse : (mu : St S (St S X) → St S X) ∘ collapse = mu := by
  show ((mu : St S (St S X) → St S X) ∘ map eta) ∘ mu = mu
  rw [mu_map_eta]
  rfl

/-- The splitting of `collapse` through `T`, half two. -/
theorem collapse_map_eta :
    (collapse : St S (St S X) → St S (St S X)) ∘ map eta = map eta := by
  show map eta ∘ ((mu : St S (St S X) → St S X) ∘ map eta) = map eta
  rw [mu_map_eta]
  rfl

/-- The image of `collapse` is exactly the image of `Tη`, i.e. the "already
flat" nested computations. -/
theorem range_collapse :
    Set.range (collapse : St S (St S X) → St S (St S X))
      = Set.range (map eta : St S X → St S (St S X)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨mu t, rfl⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨map eta t, congrFun collapse_map_eta t⟩

/-- **The idempotent is proper.** `collapse` is not the identity: a nested
computation whose inner stage actually consults the state is not recoverable
from its flattening. Witness: `S = X = Bool` and
`t = fun s => (fun s' => (s', s'), s)`. -/
theorem collapse_ne_id :
    (collapse : St Bool (St Bool Bool) → St Bool (St Bool Bool)) ≠ id := by
  intro h
  have h' := congrFun h (fun s => (fun s' => (s', s'), s))
  have := congrArg (fun u : St Bool (St Bool Bool) => ((u true).1 false).1) h'
  simp [collapse, mu, map, eta] at this

end St

end MuEqPi
