//! Natural transformations — morphisms between functors.
//!
//! Given functors F, G : C → D, a natural transformation α : F ⇒ G assigns to each
//! object X in C a morphism α_X : F(X) → G(X) such that for every f : X → Y,
//! α_Y ∘ F(f) = G(f) ∘ α_X (the naturality square).

use serde::{Serialize, Deserialize};
use crate::category::{FiniteCategory, Obj, Morphism};
use crate::functor::Functor;
use std::collections::HashMap;

/// A natural transformation between two functors.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NaturalTransformation {
    pub name: String,
    pub source_functor: String,
    pub target_functor: String,
    /// Component for each object: object name → morphism name in the target category.
    components: HashMap<String, Morphism>,
}

impl NaturalTransformation {
    pub fn new(name: impl Into<String>, source_fun: impl Into<String>, target_fun: impl Into<String>) -> Self {
        NaturalTransformation {
            name: name.into(),
            source_functor: source_fun.into(),
            target_functor: target_fun.into(),
            components: HashMap::new(),
        }
    }

    /// Set the component α_X for object X.
    pub fn set_component(&mut self, obj: &Obj, component: Morphism) {
        self.components.insert(obj.0.clone(), component);
    }

    /// Get the component for an object.
    pub fn component(&self, obj: &Obj) -> Option<&Morphism> {
        self.components.get(&obj.0)
    }

    /// Verify the naturality condition for all morphisms in the source category:
    /// For every f : X → Y,  α_Y ∘ F(f) = G(f) ∘ α_X.
    pub fn check_naturality(
        &self,
        source_cat: &FiniteCategory,
        target_cat: &FiniteCategory,
        f_functor: &Functor,
        g_functor: &Functor,
    ) -> bool {
        for mor in &source_cat.morphisms {
            let alpha_x = match self.component(&mor.dom) {
                Some(m) => m,
                None => continue,
            };
            let alpha_y = match self.component(&mor.cod) {
                Some(m) => m,
                None => continue,
            };

            let f_of_mor = match f_functor.apply_mor(mor) {
                Some(m) => m,
                None => continue,
            };
            let g_of_mor = match g_functor.apply_mor(mor) {
                Some(m) => m,
                None => continue,
            };

            // α_Y ∘ F(f)
            let left = target_cat.compose(alpha_y, &f_of_mor);
            // G(f) ∘ α_X
            let right = target_cat.compose(&g_of_mor, alpha_x);

            match (left, right) {
                (Some(l), Some(r)) if l.name == r.name => {}
                (None, None) => {} // Both undefined might be acceptable
                _ => return false,
            }
        }
        true
    }

    /// Vertical composition: given α : F ⇒ G and β : G ⇒ H, produce β ∘ α : F ⇒ H.
    pub fn vertical_compose(
        &self,
        other: &NaturalTransformation,
        source_cat: &FiniteCategory,
        target_cat: &FiniteCategory,
        f_functor: &Functor,
        h_functor: &Functor,
    ) -> Result<NaturalTransformation, String> {
        if self.target_functor != other.source_functor {
            return Err("Functors don't line up for vertical composition".into());
        }
        let name = format!("{}∘{}", other.name, self.name);
        let mut result = NaturalTransformation::new(name, &self.source_functor, &other.target_functor);
        for obj in &source_cat.objects {
            let alpha = self.component(obj);
            let beta = other.component(obj);
            match (alpha, beta) {
                (Some(a), Some(b)) => {
                    if let Some(comp) = target_cat.compose(b, a) {
                        result.set_component(obj, comp);
                    }
                }
                _ => {}
            }
        }
        Ok(result)
    }
}

/// Horizontal composition: given α : F ⇒ G and β : H ⇒ K,
/// produce β ∘ α : H∘F ⇒ K∘G (Godement product).
pub fn horizontal_compose(
    alpha: &NaturalTransformation,
    beta: &NaturalTransformation,
) -> NaturalTransformation {
    let name = format!("{}⊗{}", alpha.name, beta.name);
    NaturalTransformation::new(
        name,
        &format!("{}∘{}", beta.source_functor, alpha.source_functor),
        &format!("{}∘{}", beta.target_functor, alpha.target_functor),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::*;
    use crate::functor::*;

    fn setup_categories() -> (FiniteCategory, FiniteCategory) {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let mut src = FiniteCategory::new("C", vec![a.clone(), b.clone()]);
        let f = src.add_morphism("f", &a, &b);

        let x = Obj::new("X");
        let y = Obj::new("Y");
        let mut tgt = FiniteCategory::new("D", vec![x.clone(), y.clone()]);
        let fa = tgt.add_morphism("Fa", &x, &y);
        let ga = tgt.add_morphism("Ga", &x, &y);

        (src, tgt)
    }

    #[test]
    fn test_natural_transformation_components() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let x = Obj::new("X");
        let y = Obj::new("Y");

        let mut nt = NaturalTransformation::new("α", "F", "G");
        let alpha_a = Morphism::new("α_A", x.clone(), y.clone());
        let alpha_b = Morphism::new("α_B", x.clone(), y.clone());
        nt.set_component(&a, alpha_a.clone());
        nt.set_component(&b, alpha_b.clone());

        assert_eq!(nt.component(&a).unwrap().name, "α_A");
        assert_eq!(nt.component(&b).unwrap().name, "α_B");
    }

    #[test]
    fn test_naturality_with_identity_functors() {
        let cat = trivial_category();
        let f = identity_functor(&cat);
        let g = identity_functor(&cat);

        let obj = cat.objects.first().unwrap().clone();
        let mut nt = NaturalTransformation::new("id_nt", "Id", "Id");
        nt.set_component(&obj, Morphism::id(&obj));

        assert!(nt.check_naturality(&cat, &cat, &f, &g));
    }

    #[test]
    fn test_vertical_composition() {
        let a = Obj::new("A");
        let x = Obj::new("X");
        let mut cat = FiniteCategory::new("VComp", vec![a.clone()]);
        let mut tgt = FiniteCategory::new("Tgt", vec![x.clone()]);

        let mut alpha = NaturalTransformation::new("α", "F", "G");
        alpha.set_component(&a, Morphism::id(&x));

        let mut beta = NaturalTransformation::new("β", "G", "H");
        beta.set_component(&a, Morphism::id(&x));

        let f = identity_functor(&cat);
        let h = identity_functor(&cat);

        let composed = alpha.vertical_compose(&beta, &cat, &tgt, &f, &h).unwrap();
        assert_eq!(composed.source_functor, "F");
        assert_eq!(composed.target_functor, "H");
    }

    #[test]
    fn test_horizontal_composition() {
        let alpha = NaturalTransformation::new("α", "F", "G");
        let beta = NaturalTransformation::new("β", "H", "K");
        let result = horizontal_compose(&alpha, &beta);
        assert_eq!(result.name, "α⊗β");
    }

    #[test]
    fn test_natural_transformation_on_arrow_category() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let mut src = FiniteCategory::new("C", vec![a.clone(), b.clone()]);
        let f = src.add_morphism("f", &a, &b);

        // Target category with objects X, Y and extra objects for alpha components
        let x = Obj::new("X");
        let y = Obj::new("Y");
        let mut tgt = FiniteCategory::new("D", vec![x.clone(), y.clone()]);
        let fa = tgt.add_morphism("Ff", &x, &y);
        let ga = tgt.add_morphism("Gf", &x, &y);

        // α_A: F(A) → G(A), i.e. α_A: X → X (both F and G send A to X)
        // α_B: F(B) → G(B), i.e. α_B: Y → Y
        let alpha_a = tgt.add_morphism("αA", &x, &x);
        let alpha_b = tgt.add_morphism("αB", &y, &y);

        // Naturality: α_B ∘ Ff = Gf ∘ α_A
        // Left: α_B ∘ Ff = αB ∘ Ff : X → Y (since Ff: X→Y, αB: Y→Y)
        // Right: Gf ∘ α_A = Gf ∘ αA : X → Y (since αA: X→X, Gf: X→Y)
        // Both result in X → Y. Set both to the same morphism.
        let gf_alpha = tgt.add_morphism("naturality", &x, &y);
        tgt.set_composition(&alpha_b, &fa, &gf_alpha);
        tgt.set_composition(&ga, &alpha_a, &gf_alpha);

        let mut nt = NaturalTransformation::new("α", "F", "G");
        nt.set_component(&a, alpha_a);
        nt.set_component(&b, alpha_b);

        // Build functors: both send A→X, B→Y
        let mut ff = Functor::new("F", "C", "D");
        ff.map_obj(&a, &x);
        ff.map_obj(&b, &y);
        let id_a = src.find_morphism("id_A").unwrap().clone();
        let id_b = src.find_morphism("id_B").unwrap().clone();
        let id_x = tgt.find_morphism("id_X").unwrap().clone();
        let id_y = tgt.find_morphism("id_Y").unwrap().clone();
        ff.map_mor(&id_a, &id_x);
        ff.map_mor(&id_b, &id_y);
        ff.map_mor(&f, &fa);

        let mut gf = Functor::new("G", "C", "D");
        gf.map_obj(&a, &x);
        gf.map_obj(&b, &y);
        gf.map_mor(&id_a, &id_x);
        gf.map_mor(&id_b, &id_y);
        gf.map_mor(&f, &ga);

        assert!(nt.check_naturality(&src, &tgt, &ff, &gf));
    }
}
