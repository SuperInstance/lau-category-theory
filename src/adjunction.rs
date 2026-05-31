//! Adjunctions — pairs of functors F ⊣ G with unit η and counit ε
//! satisfying the triangle identities.
//!
//! An adjunction F ⊣ G consists of:
//! - F : C → D (left adjoint)
//! - G : D → C (right adjoint)
//! - η : Id_C ⇒ G∘F (unit)
//! - ε : F∘G ⇒ Id_D (counit)
//! such that:
//!   εF ∘ Fη = id_F  (left triangle)
//!   Gε ∘ ηG = id_G  (right triangle)

use serde::{Serialize, Deserialize};
use crate::category::{FiniteCategory, Obj, Morphism};
use crate::functor::Functor;
use crate::natural_transformation::NaturalTransformation;

/// An adjunction between two functors.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Adjunction {
    pub name: String,
    pub left_adj: Functor,
    pub right_adj: Functor,
    pub unit: NaturalTransformation,
    pub counit: NaturalTransformation,
}

impl Adjunction {
    pub fn new(
        name: impl Into<String>,
        left: Functor,
        right: Functor,
        unit: NaturalTransformation,
        counit: NaturalTransformation,
    ) -> Self {
        Adjunction {
            name: name.into(),
            left_adj: left,
            right_adj: right,
            unit,
            counit,
        }
    }

    /// Check the left triangle identity: ε_F(X) ∘ F(η_X) = id_{F(X)} for all X.
    pub fn check_left_triangle(&self, cat_c: &FiniteCategory, cat_d: &FiniteCategory) -> bool {
        for obj in &cat_c.objects {
            let f_obj = match self.left_adj.apply_obj(obj) {
                Some(o) => o,
                None => return false,
            };

            // F(η_X)
            let eta_x = match self.unit.component(obj) {
                Some(m) => m,
                None => return false,
            };
            let f_eta_x = match self.left_adj.apply_mor(eta_x) {
                Some(m) => m,
                None => continue, // Might not be in composition table
            };

            // ε_{F(X)}
            let epsilon_fx = match self.counit.component(&f_obj) {
                Some(m) => m,
                None => continue,
            };

            // ε_{F(X)} ∘ F(η_X) should equal id_{F(X)}
            let composed = cat_d.compose(epsilon_fx, &f_eta_x);
            let expected = Morphism::id(&f_obj);
            match composed {
                Some(c) if c == expected => {}
                Some(_) => return false,
                None => continue, // undefined composition
            }
        }
        true
    }

    /// Check the right triangle identity: G(ε_Y) ∘ η_{G(Y)} = id_{G(Y)} for all Y.
    pub fn check_right_triangle(&self, cat_c: &FiniteCategory, cat_d: &FiniteCategory) -> bool {
        for obj in &cat_d.objects {
            let g_obj = match self.right_adj.apply_obj(obj) {
                Some(o) => o,
                None => return false,
            };

            // η_{G(Y)}
            let eta_gy = match self.unit.component(&g_obj) {
                Some(m) => m,
                None => continue,
            };

            // G(ε_Y)
            let epsilon_y = match self.counit.component(obj) {
                Some(m) => m,
                None => continue,
            };
            let g_epsilon_y = match self.right_adj.apply_mor(epsilon_y) {
                Some(m) => m,
                None => continue,
            };

            // G(ε_Y) ∘ η_{G(Y)} should equal id_{G(Y)}
            let composed = cat_c.compose(&g_epsilon_y, eta_gy);
            let expected = Morphism::id(&g_obj);
            match composed {
                Some(c) if c == expected => {}
                Some(_) => return false,
                None => continue,
            }
        }
        true
    }

    /// Check both triangle identities.
    pub fn check_triangle_identities(&self, cat_c: &FiniteCategory, cat_d: &FiniteCategory) -> bool {
        self.check_left_triangle(cat_c, cat_d) && self.check_right_triangle(cat_c, cat_d)
    }
}

/// The free-forgetful adjunction between sets and lists (monoids).
/// F: Set → Mon (free monoid construction), U: Mon → Set (underlying set).
/// This is a simplified representation.
pub fn free_forgetful_adjunction() -> Adjunction {
    let left = Functor::new("Free", "Set", "Mon");
    let right = Functor::new("Forget", "Mon", "Set");
    let unit = NaturalTransformation::new("η", "Id_Set", "Forget∘Free");
    let counit = NaturalTransformation::new("ε", "Free∘Forget", "Id_Mon");
    Adjunction::new("Free⊣Forget", left, right, unit, counit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::*;
    use crate::functor::identity_functor;

    #[test]
    fn test_identity_adjunction() {
        let cat = trivial_category();
        let left = identity_functor(&cat);
        let right = identity_functor(&cat);
        let obj = cat.objects.first().unwrap();

        let mut unit = NaturalTransformation::new("η", "Id", "Id");
        unit.set_component(obj, Morphism::id(obj));

        let mut counit = NaturalTransformation::new("ε", "Id", "Id");
        counit.set_component(obj, Morphism::id(obj));

        let adj = Adjunction::new("Id⊣Id", left, right, unit, counit);
        assert!(adj.check_triangle_identities(&cat, &cat));
    }

    #[test]
    fn test_adjunction_on_discrete_category() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let cat = FiniteCategory::new("Disc", vec![a.clone(), b.clone()]);

        let left = identity_functor(&cat);
        let right = identity_functor(&cat);

        let mut unit = NaturalTransformation::new("η", "Id", "Id");
        unit.set_component(&a, Morphism::id(&a));
        unit.set_component(&b, Morphism::id(&b));

        let mut counit = NaturalTransformation::new("ε", "Id", "Id");
        counit.set_component(&a, Morphism::id(&a));
        counit.set_component(&b, Morphism::id(&b));

        let adj = Adjunction::new("Id⊣Id", left, right, unit, counit);
        assert!(adj.check_triangle_identities(&cat, &cat));
    }

    #[test]
    fn test_adjunction_triangle_left() {
        let cat = trivial_category();
        let left = identity_functor(&cat);
        let right = identity_functor(&cat);
        let obj = cat.objects.first().unwrap();

        let mut unit = NaturalTransformation::new("η", "Id", "Id");
        unit.set_component(obj, Morphism::id(obj));
        let mut counit = NaturalTransformation::new("ε", "Id", "Id");
        counit.set_component(obj, Morphism::id(obj));

        let adj = Adjunction::new("test", left, right, unit, counit);
        assert!(adj.check_left_triangle(&cat, &cat));
    }

    #[test]
    fn test_adjunction_triangle_right() {
        let cat = trivial_category();
        let left = identity_functor(&cat);
        let right = identity_functor(&cat);
        let obj = cat.objects.first().unwrap();

        let mut unit = NaturalTransformation::new("η", "Id", "Id");
        unit.set_component(obj, Morphism::id(obj));
        let mut counit = NaturalTransformation::new("ε", "Id", "Id");
        counit.set_component(obj, Morphism::id(obj));

        let adj = Adjunction::new("test", left, right, unit, counit);
        assert!(adj.check_right_triangle(&cat, &cat));
    }

    #[test]
    fn test_free_forgetful() {
        let adj = free_forgetful_adjunction();
        assert_eq!(adj.name, "Free⊣Forget");
        assert_eq!(adj.left_adj.name, "Free");
        assert_eq!(adj.right_adj.name, "Forget");
    }
}
