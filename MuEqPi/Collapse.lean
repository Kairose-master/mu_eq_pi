/-
Copyright (c) 2025 Jinu Jang. All rights reserved.
Released under the MIT license.
-/
import MuEqPi.Projection

/-!
# `μ = π`: monadic flattening is projection onto a graph

This file joins the two halves of the development.

A *nested* computation `t : X ⟶ T_S T_S Y` in the Kleisli category has two
pieces of data that can be read off without any higher-order structure:

* its **transition function** `outerNext t : X × S → S`, the state that the
  first stage leaves behind; and
* its **two-stage operator** `expand t : (X × S) × S → Y × S`, which runs the
  first stage from the outer state and then runs the second stage from the
  inner state slot — *treating that slot as a free parameter*.

`expand t` is an honest function between plain sets, so it linearises. The whole
point is the following identity, which holds by definition:

  `μ ∘ t = expand t ∘ graph (outerNext t)`.

Flattening is exactly *substituting the transition function into the free inner
slot*. Linearly, `graph (outerNext t)` becomes the section `Sect (outerNext t)`,
whose composite with `Flat` is the idempotent `π_{outerNext t}` of
`MuEqPi.Projection`. The main theorem is the resulting commuting square

  `lin (expand t) ∘ π_σ = lin (μ ∘ t) ∘ Flat`,

i.e. **projecting the doubled state space onto the graph and then running is the
same as flattening and then running.** That is the precise, provable content of
the slogan `μ ≡ π`.

## What is *not* claimed

The informal statement "`P : (ℝ^S ⊗ ℝ^S) ⊗ F(X) → ℝ^S ⊗ F(X)` with `P ∘ P = P`"
is not a theorem, because it is not a well-formed statement: a linear map whose
source and target differ cannot be idempotent. Nor is `μ ∘ μ = μ`, for the same
reason one type level up. The corrected statements are:

* set level — `μ ∘ Tη = id`, hence `Tη ∘ μ` is idempotent (`St.collapse_idem`);
* linear level — `Flat ∘ Sect σ = id`, hence `π_σ = Sect σ ∘ Flat` is an
  idempotent *endomorphism* of `ℝ[X × S] ⊗ ℝ[S]` (`proj_comp_proj`);
* and they are related by the square proved here.

Both idempotents are proper (`St.collapse_ne_id`, `proj_ne_id`), so neither
statement is vacuous.
-/

universe u

namespace MuEqPi

variable {S X Y : Type u}

/-- The **transition function** of the first stage of a nested computation:
the state the outer stage leaves behind. -/
def outerNext (t : X → St S (St S Y)) : Conf S X → S := fun p => (t p.1 p.2).2

/-- The **two-stage operator** of a nested computation: run the outer stage from
the outer state, then run the inner stage from the inner state slot, which is
here an independent parameter rather than the state the outer stage produced.

Unlike `t` itself, this is a function between plain sets, so it linearises. -/
def expand (t : X → St S (St S Y)) : DConf S X → Conf S Y :=
  fun q => (t q.1.1 q.1.2).1 q.2

@[simp] theorem outerNext_apply (t : X → St S (St S Y)) (x : X) (s : S) :
    outerNext t (x, s) = (t x s).2 := rfl

@[simp] theorem expand_apply (t : X → St S (St S Y)) (x : X) (s₁ s₂ : S) :
    expand t ((x, s₁), s₂) = (t x s₁).1 s₂ := rfl

/-- **Flattening is substitution into the free inner slot.** This identity holds
by definition, and it is the whole bridge between the monadic and the linear
picture. -/
theorem threadEquiv_mu (t : X → St S (St S Y)) :
    threadEquiv S X Y (fun x => St.mu (t x)) = expand t ∘ graph (outerNext t) :=
  rfl

/-- The linearised form: flattening a nested computation is the two-stage
operator restricted along the graph section. -/
theorem lin_mu (t : X → St S (St S Y)) :
    lin (threadEquiv S X Y fun x => St.mu (t x))
      = lin (expand t) ∘ₗ Sect (outerNext t) := by
  rw [threadEquiv_mu, lin_comp]
  rfl

/-- The same statement at the level of the linearisation functor. -/
theorem Lin_map_mu {X Y : Kl S} (t : X → St S (St S Y)) :
    ((Lin S).map (show X ⟶ Y from fun x => St.mu (t x))).hom
      = lin (expand t) ∘ₗ Sect (outerNext t) :=
  lin_mu t

/-- **`μ = π`.** For every nested computation `t`, projecting the doubled state
space onto the graph of `t`'s transition function and then running the two-stage
operator is the same as flattening `t` and then running the result.

`π_{outerNext t}` is an idempotent endomorphism (`proj_comp_proj`), proper as
soon as the state type is nontrivial (`proj_ne_id`). So monadic flattening is
faithfully modelled by an honest linear projection. -/
theorem mu_eq_pi (t : X → St S (St S Y)) :
    lin (expand t) ∘ₗ proj (outerNext t)
      = lin (threadEquiv S X Y fun x => St.mu (t x)) ∘ₗ Flat S X := by
  rw [lin_mu, proj]
  rfl

/-- The basis-vector form of `mu_eq_pi`, which is what the square says
concretely: the projection replaces the free inner state by the one the outer
stage produces, and then the two-stage operator computes the flattened result. -/
theorem mu_eq_pi_single (t : X → St S (St S Y)) (x : X) (s₁ s₂ : S) (r : ℝ) :
    lin (expand t) (proj (outerNext t) (Finsupp.single ((x, s₁), s₂) r))
      = Finsupp.single (St.mu (t x) s₁) r := by
  simp [St.mu]

/-- The projection is the identity precisely on configurations whose inner state
slot already agrees with the transition function — the "already flattened" ones. -/
theorem proj_eq_self_iff (t : X → St S (St S Y)) (x : X) (s₁ s₂ : S) :
    proj (outerNext t) (Finsupp.single ((x, s₁), s₂) (1 : ℝ))
        = Finsupp.single ((x, s₁), s₂) (1 : ℝ) ↔ (t x s₁).2 = s₂ := by
  constructor
  · intro h
    simpa using congrArg Prod.snd
      (Finsupp.single_left_injective (one_ne_zero (α := ℝ)) (by simpa using h))
  · rintro rfl
    simp

/-!
### The unit law, linearised

The monad law `μ ∘ Tη = id` says that a trivially nested computation flattens
back to itself. Under linearisation it becomes the statement that the graph
section is a genuine section, `Flat ∘ Sect σ = id` (`Flat_comp_Sect`). Here is
the direct form.
-/

/-- Flattening a trivially nested computation changes nothing, before or after
linearisation. -/
theorem lin_mu_map_eta (k : X → St S Y) :
    lin (threadEquiv S X Y fun x => St.mu (St.map St.eta (k x)))
      = lin (threadEquiv S X Y k) := by
  have h : (fun x => St.mu (St.map St.eta (k x))) = k :=
    funext fun x => congrFun St.mu_map_eta (k x)
  rw [h]

/-- ... and the corresponding transition function is just the transition
function of `k`, so the projection involved is `π` for `k`'s own graph. -/
theorem outerNext_map_eta (k : X → St S Y) :
    outerNext (fun x => St.map St.eta (k x)) = fun p => (k p.1 p.2).2 :=
  rfl

/-!
### A concrete proper projection

To see that none of this is vacuous, take `S = X = Y = Bool` and the nested
computation that flips the state and then returns whatever state it is handed.
Its transition function is `not`, so the projection collapses the plane spanned
by the two inner-state basis vectors onto a line — it is not the identity.
-/

section Example

/-- A nested computation over `S = Bool`: the outer stage flips the state, and
the inner stage reports the state it is started in. -/
def flipThenRead : Bool → St Bool (St Bool Bool) :=
  fun _ s => (fun s' => (s', s'), !s)

@[simp] theorem outerNext_flipThenRead :
    outerNext flipThenRead = fun p => !p.2 := rfl

/-- Flattening `flipThenRead` gives "flip the state, then report it". -/
theorem mu_flipThenRead (b : Bool) (s : Bool) :
    St.mu (flipThenRead b) s = (!s, !s) := rfl

/-- The associated linear projection is proper: it is not the identity. -/
theorem proj_flipThenRead_ne_id :
    proj (outerNext flipThenRead) ≠ LinearMap.id :=
  proj_ne_id_of_exists _ ⟨((true, true), true), by simp [flipThenRead]⟩

/-- Concretely, the projection sends the basis vector with inner state `true` and
outer state `true` to the one with inner state `false`. -/
example :
    proj (outerNext flipThenRead) (Finsupp.single ((true, true), true) (1 : ℝ))
      = Finsupp.single ((true, true), false) (1 : ℝ) := by
  simp

end Example

end MuEqPi
