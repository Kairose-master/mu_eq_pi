# Flattening the State Monad: A Vector-Space Interpretation

This repository contains the full formalisation and supporting materials for the paper:

> **"Flattening the State Monad via Idempotent Projection in Vector Spaces"**  
> ∎ All proofs are verified in **Lean 4** using `mathlib4`  
> ∎ Formal DSL application structure for **ETC** and **Kairosé DSL**  
> ∎ Research focus: **Monadic collapse ≈ geometric projection**

---

## 📚 Abstract

We present a vector-space semantics for the state monad \( T_S(X) = S \to (X \times S) \) that flattens nested layers of state into a linear form. The central construction interprets the monadic multiplication  
\[ \mu : T_S T_S(X) \to T_S(X) \]  
as an **idempotent projection** \( P : V \to V \) such that \( P^2 = P \), via a functor  
\[ F : \Kleis(T_S) \to \Vect_{\mathbb{R}} \]  
that maps computations to real vector spaces.

---

## 🧮 Core Contributions

1. Defines a functor \( F \) from the Kleisli category to \(\Vect_\RR\)
2. Constructs a concrete linear map \(P\) realizing monadic flattening
3. Machine-checks the identity \(P^2 = P\) in Lean 4
4. Connects the result to Kairosé DSL and GPT tensor collapse

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

### Run tests (if available)
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
├── StateMonad.lean       # Monad + Kleisli structures
├── Projection.lean       # Idempotent linear operator P
├── Collapse.lean         # Collapse identity μ = π
└── DSL.lean              # Kairosé DSL applications
```

---

## 🧪 Verified in Lean 4

All proofs are formalised and type-checked in Lean 4.  
We follow idiomatic use of `mathlib4` where applicable, and define all custom constructions in `StateMonad.lean`.

---

## 🌐 Citation

If you use this work in research:

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

- Generalisation to other monads (e.g., probability, continuation)
- Categorical embedding of DSL-based tensor flattening
- Application to GPT/LLM internal token routing analysis

---

## ❤️ Credits

Developed by [진우 (Jinu Jang)] — zzonstonebread@gmail.com 
Part of the ongoing **ETC (Existential Topologic Collapse)** research line and the Kairosé DSL family.
