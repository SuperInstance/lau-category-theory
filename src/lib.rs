//! # lau-category-theory
//!
//! Abstract category theory in Rust — categories, functors, natural transformations,
//! adjunctions, limits/colimits, monads, the Yoneda lemma, and an application to
//! agent protocol composition.

pub mod category;
pub mod functor;
pub mod natural_transformation;
pub mod adjunction;
pub mod limits;
pub mod monad;
pub mod yoneda;
pub mod agent_protocol;

pub mod prelude {
    pub use crate::category::*;
    pub use crate::functor::*;
    pub use crate::natural_transformation::*;
    pub use crate::adjunction::*;
    pub use crate::limits::*;
    pub use crate::monad::*;
    pub use crate::yoneda::*;
    pub use crate::agent_protocol::*;
}
