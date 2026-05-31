//! Monads — a monad on a category C is a triple (T, η, μ) where:
//! - T : C → C is an endofunctor
//! - η : Id_C ⇒ T (unit/return)
//! - μ : T∘T ⇒ T (join/multiplication)
//!
//! Satisfying:
//! - μ ∘ Tη = id     (left identity)
//! - μ ∘ ηT = id     (right identity)
//! - μ ∘ Tμ = μ ∘ μT (associativity)
//!
//! Also provides Kleisli composition and bind.

use serde::{Serialize, Deserialize};
use crate::category::{FiniteCategory, Obj, Morphism};
use crate::functor::Functor;
use crate::natural_transformation::NaturalTransformation;

/// A monad on a category.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Monad {
    pub name: String,
    pub endofunctor: Functor,
    pub unit: NaturalTransformation,
    pub multiplication: NaturalTransformation,
}

impl Monad {
    pub fn new(
        name: impl Into<String>,
        t: Functor,
        eta: NaturalTransformation,
        mu: NaturalTransformation,
    ) -> Self {
        Monad {
            name: name.into(),
            endofunctor: t,
            unit: eta,
            multiplication: mu,
        }
    }

    /// Kleisli composition: given f : A → T(B) and g : B → T(C),
    /// produce g >=> f : A → T(C) = μ_C ∘ T(g) ∘ f.
    pub fn kleisli_compose(
        &self,
        f: &Morphism,
        g: &Morphism,
    ) -> Morphism {
        Morphism::new(
            format!("({}>=>{})", g.name, f.name),
            f.dom.clone(),
            g.cod.clone(), // simplified; real Kleisli targets T(C)
        )
    }

    /// Bind operation: given a value in T(A) and a function A → T(B),
    /// produce T(B). This is μ_B ∘ T(f).
    pub fn bind(&self, ta: &Obj, f: &Morphism) -> Morphism {
        Morphism::new(
            format!("bind_{}_{}", ta.0, f.name),
            ta.clone(),
            f.cod.clone(),
        )
    }

    /// Return/unit: η_A : A → T(A).
    pub fn return_morphism(&self, obj: &Obj) -> Option<Morphism> {
        self.unit.component(obj).cloned()
    }

    /// Join: μ_A : T(T(A)) → T(A).
    pub fn join(&self, tta: &Obj) -> Option<Morphism> {
        self.multiplication.component(tta).cloned()
    }

    /// Check left identity monad law: μ_A ∘ T(η_A) = id_{T(A)}.
    pub fn check_left_identity(&self, cat: &FiniteCategory) -> bool {
        for obj in &cat.objects {
            let t_obj = match self.endofunctor.apply_obj(obj) {
                Some(o) => o,
                None => continue,
            };

            let eta_a = match self.unit.component(obj) {
                Some(m) => m,
                None => continue,
            };
            let t_eta = match self.endofunctor.apply_mor(eta_a) {
                Some(m) => m,
                None => continue,
            };

            let mu_a = match self.multiplication.component(&t_obj) {
                Some(m) => m,
                None => continue,
            };

            let composed = cat.compose(mu_a, &t_eta);
            let expected = Morphism::id(&t_obj);
            match composed {
                Some(c) if c == expected => {}
                Some(_) => return false,
                None => continue,
            }
        }
        true
    }

    /// Check right identity monad law: μ_A ∘ η_{T(A)} = id_{T(A)}.
    pub fn check_right_identity(&self, cat: &FiniteCategory) -> bool {
        for obj in &cat.objects {
            let t_obj = match self.endofunctor.apply_obj(obj) {
                Some(o) => o,
                None => continue,
            };

            let eta_ta = match self.unit.component(&t_obj) {
                Some(m) => m,
                None => continue,
            };

            let mu_a = match self.multiplication.component(&t_obj) {
                Some(m) => m,
                None => continue,
            };

            let composed = cat.compose(mu_a, &eta_ta);
            let expected = Morphism::id(&t_obj);
            match composed {
                Some(c) if c == expected => {}
                Some(_) => return false,
                None => continue,
            }
        }
        true
    }

    /// Check associativity monad law: μ_A ∘ T(μ_A) = μ_A ∘ μ_{T(A)}.
    pub fn check_associativity(&self, cat: &FiniteCategory) -> bool {
        for obj in &cat.objects {
            let t_obj = match self.endofunctor.apply_obj(obj) {
                Some(o) => o,
                None => continue,
            };
            let tt_obj = match self.endofunctor.apply_obj(&t_obj) {
                Some(o) => o,
                None => continue,
            };

            let mu_a = match self.multiplication.component(&t_obj) {
                Some(m) => m,
                None => continue,
            };
            let mu_ta = match self.multiplication.component(&tt_obj) {
                Some(m) => m,
                None => continue,
            };

            let t_mu = match self.endofunctor.apply_mor(mu_a) {
                Some(m) => m,
                None => continue,
            };

            // μ_A ∘ T(μ_A)
            let left = cat.compose(mu_a, &t_mu);
            // μ_A ∘ μ_{T(A)}
            let right = cat.compose(mu_a, &mu_ta);

            match (left, right) {
                (Some(l), Some(r)) if l.name == r.name => {}
                (None, None) => {}
                _ => return false,
            }
        }
        true
    }

    /// Check all three monad laws.
    pub fn check_monad_laws(&self, cat: &FiniteCategory) -> bool {
        self.check_left_identity(cat) && self.check_right_identity(cat) && self.check_associativity(cat)
    }
}

/// The identity monad: T = Id, η = id, μ = id.
pub fn identity_monad(cat: &FiniteCategory) -> Monad {
    let t = crate::functor::identity_functor(cat);
    let mut eta = NaturalTransformation::new("η_id", "Id", "Id");
    let mut mu = NaturalTransformation::new("μ_id", "Id∘Id", "Id");
    for obj in &cat.objects {
        let id = Morphism::id(obj);
        eta.set_component(obj, id.clone());
        mu.set_component(obj, id);
    }
    Monad::new("Identity", t, eta, mu)
}

/// The list/sequence monad (simplified representation).
pub fn list_monad() -> Monad {
    let t = Functor::new("List", "Set", "Set");
    let eta = NaturalTransformation::new("η_list", "Id", "List");
    let mu = NaturalTransformation::new("μ_list", "List∘List", "List");
    Monad::new("List", t, eta, mu)
}

/// The maybe/option monad.
pub fn maybe_monad() -> Monad {
    let t = Functor::new("Maybe", "Set", "Set");
    let eta = NaturalTransformation::new("η_maybe", "Id", "Maybe");
    let mu = NaturalTransformation::new("μ_maybe", "Maybe∘Maybe", "Maybe");
    Monad::new("Maybe", t, eta, mu)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::*;

    #[test]
    fn test_identity_monad() {
        let cat = trivial_category();
        let monad = identity_monad(&cat);
        assert!(monad.check_monad_laws(&cat));
    }

    #[test]
    fn test_monad_unit() {
        let cat = trivial_category();
        let monad = identity_monad(&cat);
        let obj = cat.objects.first().unwrap();
        let ret = monad.return_morphism(obj);
        assert!(ret.is_some());
        assert_eq!(ret.unwrap(), Morphism::id(obj));
    }

    #[test]
    fn test_monad_join() {
        let cat = trivial_category();
        let monad = identity_monad(&cat);
        let obj = cat.objects.first().unwrap();
        let join = monad.join(obj);
        assert!(join.is_some());
    }

    #[test]
    fn test_kleisli_compose() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let cat = FiniteCategory::new("K", vec![a.clone(), b.clone(), c.clone()]);
        let monad = identity_monad(&cat);

        let f = Morphism::new("f", a.clone(), b.clone());
        let g = Morphism::new("g", b.clone(), c.clone());
        let composed = monad.kleisli_compose(&f, &g);
        assert_eq!(composed.dom, a);
        assert_eq!(composed.cod, c);
    }

    #[test]
    fn test_bind() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let cat = FiniteCategory::new("Bind", vec![a.clone(), b.clone()]);
        let monad = identity_monad(&cat);
        let f = Morphism::new("f", a.clone(), b.clone());
        let result = monad.bind(&a, &f);
        assert_eq!(result.dom, a);
    }

    #[test]
    fn test_list_monad() {
        let m = list_monad();
        assert_eq!(m.name, "List");
    }

    #[test]
    fn test_maybe_monad() {
        let m = maybe_monad();
        assert_eq!(m.name, "Maybe");
    }

    #[test]
    fn test_identity_monad_left_identity() {
        let cat = trivial_category();
        let monad = identity_monad(&cat);
        assert!(monad.check_left_identity(&cat));
    }

    #[test]
    fn test_identity_monad_right_identity() {
        let cat = trivial_category();
        let monad = identity_monad(&cat);
        assert!(monad.check_right_identity(&cat));
    }

    #[test]
    fn test_identity_monad_associativity() {
        let cat = trivial_category();
        let monad = identity_monad(&cat);
        assert!(monad.check_associativity(&cat));
    }
}
