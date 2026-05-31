//! Core category trait and implementations.
//!
//! A category consists of objects, morphisms between objects, an identity morphism
//! for each object, and associative composition of compatible morphisms.

use serde::{Serialize, Deserialize};
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::HashMap;

/// A label for an object in a category. We use string identifiers for simplicity
/// while remaining fully general.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct Obj(pub String);

impl Obj {
    pub fn new(s: impl Into<String>) -> Self { Obj(s.into()) }
}

impl std::fmt::Display for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Obj({})", self.0)
    }
}

/// A morphism from one object to another, identified by name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct Morphism {
    pub name: String,
    pub dom: Obj,
    pub cod: Obj,
}

impl Morphism {
    pub fn new(name: impl Into<String>, dom: Obj, cod: Obj) -> Self {
        Morphism { name: name.into(), dom, cod }
    }

    /// Identity morphism for an object.
    pub fn id(obj: &Obj) -> Self {
        Morphism::new(format!("id_{}", obj.0), obj.clone(), obj.clone())
    }

    /// Check if this morphism can be composed with another on the right:
    /// `self ∘ other` is valid iff `self.dom == other.cod`.
    pub fn composable_with(&self, other: &Morphism) -> bool {
        self.dom == other.cod
    }
}

impl std::fmt::Display for Morphism {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {} → {}", self.name, self.dom, self.cod)
    }
}

/// A concrete finite category defined by its objects, morphisms, and composition table.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FiniteCategory {
    pub name: String,
    pub objects: Vec<Obj>,
    pub morphisms: Vec<Morphism>,
    /// Composition table: (f.name, g.name) → h means f ∘ g = h.
    /// The composite h must have dom = g.dom and cod = f.cod.
    composition: HashMap<(String, String), String>,
}

impl FiniteCategory {
    pub fn new(name: impl Into<String>, objects: Vec<Obj>) -> Self {
        let mut morphisms: Vec<Morphism> = objects.iter().map(|o| Morphism::id(o)).collect();
        FiniteCategory {
            name: name.into(),
            objects,
            morphisms,
            composition: HashMap::new(),
        }
    }

    /// Add a morphism. Returns the added morphism handle.
    pub fn add_morphism(&mut self, name: impl Into<String>, dom: &Obj, cod: &Obj) -> Morphism {
        let m = Morphism::new(name, dom.clone(), cod.clone());
        self.morphisms.push(m.clone());
        m
    }

    /// Define composition: `first ∘ second = result`.
    pub fn set_composition(&mut self, first: &Morphism, second: &Morphism, result: &Morphism) {
        assert!(first.dom == second.cod, "Composition domain mismatch");
        assert!(result.dom == second.dom && result.cod == first.cod, "Result morphism shape mismatch");
        self.composition.insert((first.name.clone(), second.name.clone()), result.name.clone());
    }

    /// Compose two morphisms: `first ∘ second`.
    pub fn compose(&self, first: &Morphism, second: &Morphism) -> Option<Morphism> {
        if first.dom != second.cod {
            return None;
        }
        // Identity cases
        if first.dom == first.cod && first.name == format!("id_{}", first.dom.0) {
            return Some(second.clone());
        }
        if second.dom == second.cod && second.name == format!("id_{}", second.dom.0) {
            return Some(first.clone());
        }
        self.composition
            .get(&(first.name.clone(), second.name.clone()))
            .map(|name| Morphism::new(name, second.dom.clone(), first.cod.clone()))
    }

    /// Look up a morphism by name.
    pub fn find_morphism(&self, name: &str) -> Option<&Morphism> {
        self.morphisms.iter().find(|m| m.name == name)
    }

    /// Verify identity laws: `id ∘ f = f` and `f ∘ id = f` for all morphisms f.
    pub fn check_identity_laws(&self) -> bool {
        for m in &self.morphisms {
            let id_dom = Morphism::id(&m.dom);
            let id_cod = Morphism::id(&m.cod);
            // id_cod ∘ m = m
            if let Some(comp) = self.compose(&id_cod, m) {
                if comp != *m { return false; }
            }
            // m ∘ id_dom = m
            if let Some(comp) = self.compose(m, &id_dom) {
                if comp != *m { return false; }
            }
        }
        true
    }

    /// Check associativity for all triples of composable morphisms.
    pub fn check_associativity(&self) -> bool {
        for f in &self.morphisms {
            for g in &self.morphisms {
                if f.dom != g.cod { continue; }
                for h in &self.morphisms {
                    if g.dom != h.cod { continue; }
                    // (f ∘ g) ∘ h = f ∘ (g ∘ h)
                    let fg = match self.compose(f, g) {
                        Some(c) => c,
                        None => continue,
                    };
                    let gh = match self.compose(g, h) {
                        Some(c) => c,
                        None => continue,
                    };
                    let left = self.compose(&fg, h);
                    let right = self.compose(f, &gh);
                    match (left, right) {
                        (Some(l), Some(r)) if l.name == r.name => {}
                        _ => return false,
                    }
                }
            }
        }
        true
    }

    /// Full category axiom check.
    pub fn is_valid_category(&self) -> bool {
        self.check_identity_laws() && self.check_associativity()
    }
}

/// The trivial category with one object and only the identity morphism.
pub fn trivial_category() -> FiniteCategory {
    let obj = Obj::new("*");
    FiniteCategory::new("Trivial", vec![obj])
}

/// Build the category of sets with at most 3 elements (finite approximation).
/// This is useful for testing.
pub fn finite_set_category(name: &str, n: usize) -> FiniteCategory {
    let objects: Vec<Obj> = (0..=n).map(|i| Obj::new(format!("Set{}", i))).collect();
    let mut cat = FiniteCategory::new(name, objects.clone());
    // Add some morphisms for testing
    for (i, dom) in objects.iter().enumerate() {
        for (j, cod) in objects.iter().enumerate() {
            if i != j {
                cat.add_morphism(format!("f_{}_{}", i, j), dom, cod);
            }
        }
    }
    cat
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identity_morphism() {
        let obj = Obj::new("X");
        let id = Morphism::id(&obj);
        assert_eq!(id.dom, obj);
        assert_eq!(id.cod, obj);
        assert_eq!(id.name, "id_X");
    }

    #[test]
    fn test_composability() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let f = Morphism::new("f", a.clone(), b.clone());
        let g = Morphism::new("g", b.clone(), c.clone());
        assert!(g.composable_with(&f));
        assert!(!f.composable_with(&g));
    }

    #[test]
    fn test_trivial_category() {
        let cat = trivial_category();
        assert_eq!(cat.objects.len(), 1);
        assert_eq!(cat.morphisms.len(), 1); // just identity
        assert!(cat.is_valid_category());
    }

    #[test]
    fn test_category_with_composition() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let mut cat = FiniteCategory::new("ABC", vec![a.clone(), b.clone(), c.clone()]);

        let f = cat.add_morphism("f", &a, &b);
        let g = cat.add_morphism("g", &b, &c);
        let gf = cat.add_morphism("g∘f", &a, &c);

        cat.set_composition(&g, &f, &gf);

        let composed = cat.compose(&g, &f).unwrap();
        assert_eq!(composed.name, "g∘f");
        assert_eq!(composed.dom, a);
        assert_eq!(composed.cod, c);
    }

    #[test]
    fn test_identity_laws() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let mut cat = FiniteCategory::new("IdTest", vec![a.clone(), b.clone()]);
        let f = cat.add_morphism("f", &a, &b);

        let id_a = cat.find_morphism("id_A").unwrap().clone();
        let id_b = cat.find_morphism("id_B").unwrap().clone();

        // id_B ∘ f = f
        let comp1 = cat.compose(&id_b, &f).unwrap();
        assert_eq!(comp1, f);
        // f ∘ id_A = f
        let comp2 = cat.compose(&f, &id_a).unwrap();
        assert_eq!(comp2, f);

        assert!(cat.check_identity_laws());
    }

    #[test]
    fn test_associativity() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let d = Obj::new("D");
        let mut cat = FiniteCategory::new("AssocTest", vec![a.clone(), b.clone(), c.clone(), d.clone()]);

        let f = cat.add_morphism("f", &a, &b);
        let g = cat.add_morphism("g", &b, &c);
        let h = cat.add_morphism("h", &c, &d);

        let gf = cat.add_morphism("g∘f", &a, &c);
        let hg = cat.add_morphism("h∘g", &b, &d);
        let hgf = cat.add_morphism("h∘g∘f", &a, &d);

        cat.set_composition(&g, &f, &gf);
        cat.set_composition(&h, &g, &hg);
        cat.set_composition(&h, &gf, &hgf);
        cat.set_composition(&hg, &f, &hgf);

        assert!(cat.check_associativity());
        assert!(cat.is_valid_category());
    }

    #[test]
    fn test_display() {
        let obj = Obj::new("X");
        let m = Morphism::new("f", Obj::new("A"), obj);
        assert_eq!(format!("{}", m), "f: Obj(A) → Obj(X)");
    }
}
