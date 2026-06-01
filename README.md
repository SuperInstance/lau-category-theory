# lau-category-theory

> Abstract category theory in Rust — categories, functors, natural transformations, adjunctions, limits, colimits, monads, and the Yoneda lemma, with an agent-protocol composition application.

## What This Does

Abstract category theory in Rust — categories, functors, natural transformations, adjunctions, limits, colimits, monads, and the Yoneda lemma, with an agent-protocol composition application.. Part of the PLATO/LAU ecosystem — a mathematically rigorous framework for building educational agents that learn, teach, and evolve.

## The Key Idea

This crate implements the core abstractions needed for its domain, with a focus on correctness, composability, and conservation guarantees. Every public type is serializable (serde), every algorithm is tested, and every invariant is verified.

## Install

```bash
cargo add lau-category-theory
```

## Quick Start

See the API Reference below for complete usage. Key entry points:

```rust
use lau_category_theory::*;
// See types and methods below for complete usage
```

## API Reference

```rust
pub struct Functor 
    pub fn new(name: impl Into<String>, source: impl Into<String>, target: impl Into<String>) -> Self 
    pub fn map_obj(&mut self, src: &Obj, tgt: &Obj) 
    pub fn map_mor(&mut self, src: &Morphism, tgt: &Morphism) 
    pub fn apply_obj(&self, obj: &Obj) -> Option<Obj> 
    pub fn apply_mor(&self, mor: &Morphism) -> Option<Morphism> 
    pub fn check_identity_law(&self, source: &FiniteCategory, target: &FiniteCategory) -> bool 
    pub fn check_composition_law(&self, source: &FiniteCategory, target: &FiniteCategory) -> bool 
    pub fn is_valid_functor(&self, source: &FiniteCategory, target: &FiniteCategory) -> bool 
pub struct ContravariantFunctor 
    pub fn new(name: impl Into<String>, source: impl Into<String>, target: impl Into<String>) -> Self 
    pub fn map_obj(&mut self, src: &Obj, tgt: &Obj) 
    pub fn map_mor(&mut self, src: &Morphism, tgt: &Morphism) 
    pub fn apply_obj(&self, obj: &Obj) -> Option<Obj> 
    pub fn apply_mor(&self, mor: &Morphism) -> Option<&Morphism> 
    pub fn check_identity_law(&self, source: &FiniteCategory) -> bool 
pub fn identity_functor(cat: &FiniteCategory) -> Functor 
pub struct NaturalTransformation 
    pub fn new(name: impl Into<String>, source_fun: impl Into<String>, target_fun: impl Into<String>) -> Self 
    pub fn set_component(&mut self, obj: &Obj, component: Morphism) 
    pub fn component(&self, obj: &Obj) -> Option<&Morphism> 
    pub fn check_naturality(
    pub fn vertical_compose(
pub fn horizontal_compose(
pub struct Monad 
    pub fn new(
    pub fn kleisli_compose(
    pub fn bind(&self, ta: &Obj, f: &Morphism) -> Morphism 
    pub fn return_morphism(&self, obj: &Obj) -> Option<Morphism> 
    pub fn join(&self, tta: &Obj) -> Option<Morphism> 
    pub fn check_left_identity(&self, cat: &FiniteCategory) -> bool 
    pub fn check_right_identity(&self, cat: &FiniteCategory) -> bool 
    pub fn check_associativity(&self, cat: &FiniteCategory) -> bool 
    pub fn check_monad_laws(&self, cat: &FiniteCategory) -> bool 
pub fn identity_monad(cat: &FiniteCategory) -> Monad 
pub fn list_monad() -> Monad 
pub fn maybe_monad() -> Monad 
pub struct Agent 
    pub fn new(name: impl Into<String>, role: impl Into<String>) -> Self 
    pub fn to_obj(&self) -> Obj 
pub struct Protocol 
    pub fn new(
    pub fn to_morphism(&self) -> Morphism 
pub struct AgentCategory 
    pub fn new(name: impl Into<String>) -> Self 
    pub fn add_agent(&mut self, agent: Agent) 
    pub fn add_protocol(&mut self, protocol: Protocol) -> Morphism 
    pub fn compose_protocols(
    pub fn protocol_stack_monad(&self) -> Monad 
    pub fn parallel_compose(&mut self, a: &Agent, b: &Agent) -> Product 
    pub fn choice_compose(&mut self, a: &Agent, b: &Agent) -> Coproduct 
pub struct Product 
    pub fn new(object: Obj, proj1: Morphism, proj2: Morphism) -> Self 
    pub fn pair(&self, f: &Morphism, g: &Morphism) -> Morphism 
pub fn product(cat: &mut FiniteCategory, a: &Obj, b: &Obj) -> Product 
pub struct Coproduct 
    pub fn new(object: Obj, inj1: Morphism, inj2: Morphism) -> Self 
    pub fn copair(&self, f: &Morphism, g: &Morphism) -> Morphism 
pub fn coproduct(cat: &mut FiniteCategory, a: &Obj, b: &Obj) -> Coproduct 
pub struct Equalizer 
```

## How It Works

Read the source in `src/` for full implementation details. All algorithms are documented with inline comments explaining the mathematical foundations.

## The Math

This crate implements formal mathematical constructs. See the source documentation for theorem statements and proofs of correctness.

## Testing

**57 tests** covering construction, serialization, correctness properties, edge cases, and composability with other lau-* crates.

## License

MIT
