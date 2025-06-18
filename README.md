# 📘 Flattening the State Monad: A Vector-Space Interpretation

This repository contains the full Lean 4 formalization and accompanying documentation for the paper:

> **"Flattening the State Monad via Idempotent Projection in Vector Spaces"**  
> ▪️ All proofs verified in **Lean 4** using `mathlib4`  
> ▪️ Includes formal integration with **ETC** and **Kairosé DSL**  
> ▪️ Research focus: **Monadic collapse ≈ geometric projection**

---

## 📚 Abstract

We present a vector-space semantics for the state monad  
\( T_S(X) = S $\to$ (X $\times$ S) \),  
interpreting nested monadic structure as an idempotent projection  
$\mu : T_S T_S(X) $\to$ T_S(X), $\quad$ $\mu$^2 = $\mu$$  
via a functor  
$F : $\mathsf${Kl}(T_S) $\to$ $\mathbf${Vect}_$\mathbb${R}$  
that maps computations into real vector spaces.

This yields a linear operator  
$P : ($\mathbb${R}^S $\otimes$ $\mathbb${R}^S) $\otimes$ $\mathbb${F}(X) $\to$ $\mathbb${R}^S $\otimes$ $\mathbb${F}(X)$  
with the identity \( P $\circ$ P = P \), thus proving  
$\mu $\equiv$ $\pi$$

---

## 🧮 Key Contributions

1. Constructs a functor \( F \) from the Kleisli category to \($\mathbf${Vect}_$\mathbb${R}\)
2. Defines an explicit linear projection \( P \) modeling monadic flattening
3. Formally proves \( P^2 = P \) (idempotence) in Lean 4
4. Connects the result to **Kairosé DSL** and **GPT tensor collapse**

---

## 🛠 Build Instructions

### Requirements
- Lean 4 (v4.2 or later)
- `lake` build system

### Setup
```bash
lake update
lake build
```

### Run executable (if available)
```bash
lake exe flatten_state_tensor
```

---

## 📁 Project Structure

```
.
├── README.md
├── lakefile.lean         # Project definition
├── lean-toolchain        # Lean version pinning
├── Main.lean             # Entry point
├── StateMonad.lean       # Monad and Kleisli category
├── Projection.lean       # Idempotent operator P
├── Collapse.lean         # Collapse identity: μ = π
└── DSL.lean              # Kairosé DSL connection
```

---

## 🧪 Verified in Lean 4

All proofs are fully formalized and type-checked in Lean 4.  
We follow idiomatic usage of `mathlib4` where applicable, with custom definitions implemented in `StateMonad.lean`.

---

## 🌐 Citation

If this work is useful in your research:

```bibtex
@misc{flatten-state-monad,
  author    = {Jinu Jang},
  title     = {Flattening the State Monad via Idempotent Projection in Vector Spaces},
  year      = {2025},
  note      = {Lean 4 formalisation, GitHub repository}
}
```

---

## 🧭 Future Directions

- Generalizing the result to other monads (e.g. probability, continuation)
- Embedding monadic collapse into tensor categories and DSLs
- Applying collapse projection to GPT/LLM token routing and model compression

---

## ❤️ Credits

Developed by [진우 (Jinu Jang)] — zzonstonebread@gmail.com  
Part of the ongoing **ETC (Existential Topological Collapse)** project  
and the **Kairosé DSL** formal symbolic structure family.