//! Functors — structure-preserving maps between categories.
//!
//! A functor F : C → D maps objects to objects and morphisms to morphisms,
//! preserving identity and composition (the functor laws).

use serde::{Serialize, Deserialize};
use crate::category::{FiniteCategory, Obj, Morphism};
use std::collections::HashMap;

/// A functor between finite categories, defined by its action on objects and morphisms.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Functor {
    pub name: String,
    pub source_cat: String,
    pub target_cat: String,
    /// Object mapping: source object name → target object name.
    obj_map: HashMap<String, String>,
    /// Morphism mapping: source morphism name → target morphism name.
    mor_map: HashMap<String, String>,
}

impl Functor {
    pub fn new(name: impl Into<String>, source: impl Into<String>, target: impl Into<String>) -> Self {
        Functor {
            name: name.into(),
            source_cat: source.into(),
            target_cat: target.into(),
            obj_map: HashMap::new(),
            mor_map: HashMap::new(),
        }
    }

    /// Map an object.
    pub fn map_obj(&mut self, src: &Obj, tgt: &Obj) {
        self.obj_map.insert(src.0.clone(), tgt.0.clone());
    }

    /// Map a morphism.
    pub fn map_mor(&mut self, src: &Morphism, tgt: &Morphism) {
        self.mor_map.insert(src.name.clone(), tgt.name.clone());
    }

    /// Apply the functor to an object.
    pub fn apply_obj(&self, obj: &Obj) -> Option<Obj> {
        self.obj_map.get(&obj.0).map(|s| Obj::new(s))
    }

    /// Apply the functor to a morphism.
    pub fn apply_mor(&self, mor: &Morphism) -> Option<Morphism> {
        self.mor_map.get(&mor.name).map(|name| {
            let dom = self.obj_map.get(&mor.dom.0).unwrap().clone();
            let cod = self.obj_map.get(&mor.cod.0).unwrap().clone();
            Morphism::new(name, Obj::new(dom), Obj::new(cod))
        })
    }

    /// Verify the first functor law: F(id_A) = id_{F(A)} for all objects A.
    pub fn check_identity_law(&self, source: &FiniteCategory, target: &FiniteCategory) -> bool {
        for obj in &source.objects {
            let id_src = Morphism::id(obj);
            if let Some(f_id) = self.apply_mor(&id_src) {
                let expected_id = Morphism::id(&self.apply_obj(obj).unwrap());
                if f_id != expected_id { return false; }
            } else {
                return false;
            }
        }
        true
    }

    /// Verify the second functor law: F(g ∘ f) = F(g) ∘ F(f).
    pub fn check_composition_law(&self, source: &FiniteCategory, target: &FiniteCategory) -> bool {
        for f in &source.morphisms {
            for g in &source.morphisms {
                if !g.composable_with(f) { continue; }
                let gf = match source.compose(g, f) {
                    Some(c) => c,
                    None => continue,
                };
                let f_gf = match self.apply_mor(&gf) {
                    Some(c) => c,
                    None => continue,
                };
                let ff = match self.apply_mor(f) {
                    Some(c) => c,
                    None => continue,
                };
                let fg = match self.apply_mor(g) {
                    Some(c) => c,
                    None => continue,
                };
                let composed = match target.compose(&fg, &ff) {
                    Some(c) => c,
                    None => continue,
                };
                if composed.name != f_gf.name { return false; }
            }
        }
        true
    }

    /// Check both functor laws.
    pub fn is_valid_functor(&self, source: &FiniteCategory, target: &FiniteCategory) -> bool {
        self.check_identity_law(source, target) && self.check_composition_law(source, target)
    }
}

/// A contravariant functor reverses the direction of morphisms.
/// F : C^op → D, so F(f : A → B) = F(f) : F(B) → F(A).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContravariantFunctor {
    pub name: String,
    pub source_cat: String,
    pub target_cat: String,
    obj_map: HashMap<String, String>,
    mor_map: HashMap<String, Morphism>,
}

impl ContravariantFunctor {
    pub fn new(name: impl Into<String>, source: impl Into<String>, target: impl Into<String>) -> Self {
        ContravariantFunctor {
            name: name.into(),
            source_cat: source.into(),
            target_cat: target.into(),
            obj_map: HashMap::new(),
            mor_map: HashMap::new(),
        }
    }

    pub fn map_obj(&mut self, src: &Obj, tgt: &Obj) {
        self.obj_map.insert(src.0.clone(), tgt.0.clone());
    }

    /// Map a morphism. The resulting morphism goes in the opposite direction.
    pub fn map_mor(&mut self, src: &Morphism, tgt: &Morphism) {
        // Reversed: F(f: A→B) = F(f): F(B)→F(A)
        let reversed = Morphism::new(
            &tgt.name,
            self.apply_obj(&src.cod).unwrap(),
            self.apply_obj(&src.dom).unwrap(),
        );
        self.mor_map.insert(src.name.clone(), reversed);
    }

    pub fn apply_obj(&self, obj: &Obj) -> Option<Obj> {
        self.obj_map.get(&obj.0).map(|s| Obj::new(s))
    }

    pub fn apply_mor(&self, mor: &Morphism) -> Option<&Morphism> {
        self.mor_map.get(&mor.name)
    }

    /// Verify: F(id) = id, and F(g ∘ f) = F(f) ∘ F(g) (reversed order).
    pub fn check_identity_law(&self, source: &FiniteCategory) -> bool {
        for obj in &source.objects {
            let id_src = Morphism::id(obj);
            if let Some(f_id) = self.apply_mor(&id_src) {
                let expected = Morphism::id(&self.apply_obj(obj).unwrap());
                if *f_id != expected { return false; }
            } else {
                return false;
            }
        }
        true
    }
}

/// The identity functor on a category.
pub fn identity_functor(cat: &FiniteCategory) -> Functor {
    let mut f = Functor::new("Id", &cat.name, &cat.name);
    for obj in &cat.objects {
        f.map_obj(obj, obj);
    }
    for mor in &cat.morphisms {
        f.map_mor(mor, mor);
    }
    f
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::*;

    fn make_arrow_category() -> (FiniteCategory, Morphism, Morphism, Obj) {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let mut cat = FiniteCategory::new("Arrow", vec![a.clone(), b.clone(), c.clone()]);
        let f = cat.add_morphism("f", &a, &b);
        let g = cat.add_morphism("g", &b, &c);
        let gf = cat.add_morphism("g∘f", &a, &c);
        cat.set_composition(&g, &f, &gf);
        (cat, f, g, a)
    }

    #[test]
    fn test_identity_functor() {
        let (cat, _, _, _) = make_arrow_category();
        let id_f = identity_functor(&cat);
        assert!(id_f.is_valid_functor(&cat, &cat));
        // Check it actually maps to same objects
        for obj in &cat.objects {
            assert_eq!(id_f.apply_obj(obj).unwrap(), *obj);
        }
    }

    #[test]
    fn test_functor_between_categories() {
        let (cat, _, _, _) = make_arrow_category();

        let x = Obj::new("X");
        let y = Obj::new("Y");
        let z = Obj::new("Z");
        let mut cat2 = FiniteCategory::new("Target", vec![x.clone(), y.clone(), z.clone()]);
        let f2 = cat2.add_morphism("Ff", &x, &y);
        let g2 = cat2.add_morphism("Fg", &y, &z);
        let gf2 = cat2.add_morphism("FgFf", &x, &z);
        cat2.set_composition(&g2, &f2, &gf2);

        let mut fun = Functor::new("F", "Arrow", "Target");
        fun.map_obj(&Obj::new("A"), &x);
        fun.map_obj(&Obj::new("B"), &y);
        fun.map_obj(&Obj::new("C"), &z);

        // Map identity morphisms
        let id_a = cat.find_morphism("id_A").unwrap();
        let id_b = cat.find_morphism("id_B").unwrap();
        let id_c = cat.find_morphism("id_C").unwrap();
        let id_x = cat2.find_morphism("id_X").unwrap();
        let id_y = cat2.find_morphism("id_Y").unwrap();
        let id_z = cat2.find_morphism("id_Z").unwrap();
        fun.map_mor(id_a, id_x);
        fun.map_mor(id_b, id_y);
        fun.map_mor(id_c, id_z);

        fun.map_mor(&cat.find_morphism("f").unwrap().clone(), &f2);
        fun.map_mor(&cat.find_morphism("g").unwrap().clone(), &g2);
        fun.map_mor(&cat.find_morphism("g∘f").unwrap().clone(), &gf2);

        assert!(fun.is_valid_functor(&cat, &cat2));
    }

    #[test]
    fn test_contravariant_functor() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let mut cat = FiniteCategory::new("Simple", vec![a.clone(), b.clone()]);
        let f = cat.add_morphism("f", &a, &b);

        let x = Obj::new("X");
        let y = Obj::new("Y");
        let mut cat2 = FiniteCategory::new("Target", vec![x.clone(), y.clone()]);

        let mut contra = ContravariantFunctor::new("H", "Simple", "Target");
        contra.map_obj(&a, &x);
        contra.map_obj(&b, &y);

        // Map identity morphisms
        let id_a = cat.find_morphism("id_A").unwrap().clone();
        let id_b = cat.find_morphism("id_B").unwrap().clone();
        contra.map_mor(&id_a, &Morphism::id(&x));
        contra.map_mor(&id_b, &Morphism::id(&y));

        // f: A→B should map to H(f): H(B)→H(A) = Y→X
        let reversed = Morphism::new("Hf", y.clone(), x.clone());
        contra.map_mor(&f, &reversed);

        let applied = contra.apply_mor(&f).unwrap();
        assert_eq!(applied.dom, y);
        assert_eq!(applied.cod, x);
        assert!(contra.check_identity_law(&cat));
    }

    #[test]
    fn test_functor_preserves_identity() {
        let cat = trivial_category();
        let id = identity_functor(&cat);
        let obj = cat.objects.first().unwrap();
        let f_id = id.apply_mor(&Morphism::id(obj)).unwrap();
        assert_eq!(f_id, Morphism::id(obj));
    }
}
