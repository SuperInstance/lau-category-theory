//! Limits and colimits — universal constructions in categories.
//!
//! Limits: products, equalizers, pullbacks.
//! Colimits: coproducts, coequalizers, pushouts.

use serde::{Serialize, Deserialize};
use crate::category::{FiniteCategory, Obj, Morphism};
use std::collections::HashMap;

// ─── Products ───────────────────────────────────────────────────────────────

/// A product of objects A and B is an object P with projections π₁ : P → A,
/// π₂ : P → B such that for any Q with f : Q → A, g : Q → B, there is a unique
/// ⟨f,g⟩ : Q → P with π₁ ∘ ⟨f,g⟩ = f and π₂ ∘ ⟨f,g⟩ = g.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Product {
    pub object: Obj,
    pub proj1: Morphism,
    pub proj2: Morphism,
}

impl Product {
    pub fn new(object: Obj, proj1: Morphism, proj2: Morphism) -> Self {
        assert!(proj1.dom == object && proj2.dom == object);
        Product { object, proj1, proj2 }
    }

    /// Form the pairing morphism <f, g> for the product.
    /// Returns the name of the unique morphism Q → P.
    pub fn pair(&self, f: &Morphism, g: &Morphism) -> Morphism {
        assert_eq!(f.dom, g.dom);
        assert_eq!(f.cod, self.proj1.cod);
        assert_eq!(g.cod, self.proj2.cod);
        Morphism::new(
            format!("<{},{}>", f.name, g.name),
            f.dom.clone(),
            self.object.clone(),
        )
    }
}

/// Compute the product of two objects in a finite category.
pub fn product(cat: &mut FiniteCategory, a: &Obj, b: &Obj) -> Product {
    let p_obj = Obj::new(format!("{}×{}", a.0, b.0));
    let p1 = cat.add_morphism(format!("π₁_{}{}", a.0, b.0), &p_obj, a);
    let p2 = cat.add_morphism(format!("π₂_{}{}", a.0, b.0), &p_obj, b);

    // Register the product object
    if !cat.objects.contains(&p_obj) {
        cat.objects.push(p_obj.clone());
    }

    Product::new(p_obj, p1, p2)
}

// ─── Coproducts ─────────────────────────────────────────────────────────────

/// A coproduct of A and B is an object C with injections i₁ : A → C,
/// i₂ : B → C satisfying the dual universal property of products.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Coproduct {
    pub object: Obj,
    pub inj1: Morphism,
    pub inj2: Morphism,
}

impl Coproduct {
    pub fn new(object: Obj, inj1: Morphism, inj2: Morphism) -> Self {
        assert!(inj1.cod == object && inj2.cod == object);
        Coproduct { object, inj1, inj2 }
    }

    /// Form the copairing morphism [f, g] for the coproduct.
    pub fn copair(&self, f: &Morphism, g: &Morphism) -> Morphism {
        assert_eq!(f.cod, g.cod);
        assert_eq!(f.dom, self.inj1.dom);
        assert_eq!(g.dom, self.inj2.dom);
        Morphism::new(
            format!("[{},{}]", f.name, g.name),
            self.object.clone(),
            f.cod.clone(),
        )
    }
}

/// Compute the coproduct of two objects.
pub fn coproduct(cat: &mut FiniteCategory, a: &Obj, b: &Obj) -> Coproduct {
    let c_obj = Obj::new(format!("{}+{}", a.0, b.0));
    let i1 = cat.add_morphism(format!("i₁_{}{}", a.0, b.0), a, &c_obj);
    let i2 = cat.add_morphism(format!("i₂_{}{}", a.0, b.0), b, &c_obj);

    if !cat.objects.contains(&c_obj) {
        cat.objects.push(c_obj.clone());
    }

    Coproduct::new(c_obj, i1, i2)
}

// ─── Equalizers ─────────────────────────────────────────────────────────────

/// An equalizer of f, g : A → B is an object E with eq : E → A such that
/// f ∘ eq = g ∘ eq, universal with this property.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Equalizer {
    pub object: Obj,
    pub equalizer_morphism: Morphism,
}

impl Equalizer {
    pub fn new(object: Obj, eq_mor: Morphism) -> Self {
        Equalizer { object, equalizer_morphism: eq_mor }
    }

    /// Verify that f ∘ eq = g ∘ eq in the category.
    pub fn verify(&self, cat: &FiniteCategory, f: &Morphism, g: &Morphism) -> bool {
        let f_eq = cat.compose(f, &self.equalizer_morphism);
        let g_eq = cat.compose(g, &self.equalizer_morphism);
        match (f_eq, g_eq) {
            (Some(l), Some(r)) => l.name == r.name,
            _ => false,
        }
    }
}

/// Compute the equalizer of two parallel morphisms.
pub fn equalizer(cat: &mut FiniteCategory, f: &Morphism, g: &Morphism) -> Equalizer {
    assert!(f.dom == g.dom && f.cod == g.cod);
    let e_obj = Obj::new(format!("Eq({},{})", f.name, g.name));
    let eq_mor = cat.add_morphism(
        format!("eq_{}_{}", f.name, g.name),
        &e_obj,
        &f.dom,
    );

    if !cat.objects.contains(&e_obj) {
        cat.objects.push(e_obj.clone());
    }

    Equalizer::new(e_obj, eq_mor)
}

// ─── Pullbacks ──────────────────────────────────────────────────────────────

/// A pullback of f : A → C and g : B → C is an object P with
/// p₁ : P → A, p₂ : P → B such that f ∘ p₁ = g ∘ p₂.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Pullback {
    pub object: Obj,
    pub proj1: Morphism,
    pub proj2: Morphism,
}

impl Pullback {
    pub fn verify(&self, cat: &FiniteCategory, f: &Morphism, g: &Morphism) -> bool {
        let left = cat.compose(f, &self.proj1);
        let right = cat.compose(g, &self.proj2);
        match (left, right) {
            (Some(l), Some(r)) => l.name == r.name,
            _ => false,
        }
    }
}

/// Compute a pullback.
pub fn pullback(cat: &mut FiniteCategory, f: &Morphism, g: &Morphism) -> Pullback {
    let p_obj = Obj::new(format!("Pb({},{})", f.name, g.name));
    let p1 = cat.add_morphism(format!("pb₁_{}_{}", f.name, g.name), &p_obj, &f.dom);
    let p2 = cat.add_morphism(format!("pb₂_{}_{}", f.name, g.name), &p_obj, &g.dom);

    if !cat.objects.contains(&p_obj) {
        cat.objects.push(p_obj.clone());
    }

    Pullback { object: p_obj, proj1: p1, proj2: p2 }
}

// ─── Pushouts ───────────────────────────────────────────────────────────────

/// A pushout of f : C → A and g : C → B is the dual of a pullback.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Pushout {
    pub object: Obj,
    pub inj1: Morphism,
    pub inj2: Morphism,
}

impl Pushout {
    pub fn verify(&self, cat: &FiniteCategory, f: &Morphism, g: &Morphism) -> bool {
        let left = cat.compose(&self.inj1, f);
        let right = cat.compose(&self.inj2, g);
        match (left, right) {
            (Some(l), Some(r)) => l.name == r.name,
            _ => false,
        }
    }
}

/// Compute a pushout.
pub fn pushout(cat: &mut FiniteCategory, f: &Morphism, g: &Morphism) -> Pushout {
    let po_obj = Obj::new(format!("Po({},{})", f.name, g.name));
    let i1 = cat.add_morphism(format!("po₁_{}_{}", f.name, g.name), &f.cod, &po_obj);
    let i2 = cat.add_morphism(format!("po₂_{}_{}", f.name, g.name), &g.cod, &po_obj);

    if !cat.objects.contains(&po_obj) {
        cat.objects.push(po_obj.clone());
    }

    Pushout { object: po_obj, inj1: i1, inj2: i2 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::*;

    #[test]
    fn test_product_construction() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let mut cat = FiniteCategory::new("Prod", vec![a.clone(), b.clone()]);
        let prod = product(&mut cat, &a, &b);
        assert_eq!(prod.object, Obj::new("A×B"));
        assert_eq!(prod.proj1.cod, a);
        assert_eq!(prod.proj2.cod, b);
    }

    #[test]
    fn test_product_pairing() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let q = Obj::new("Q");
        let mut cat = FiniteCategory::new("Pair", vec![a.clone(), b.clone(), q.clone()]);
        let prod = product(&mut cat, &a, &b);
        let f = Morphism::new("f", q.clone(), a);
        let g = Morphism::new("g", q.clone(), b);
        let pair = prod.pair(&f, &g);
        assert_eq!(pair.dom, q);
        assert_eq!(pair.cod, prod.object);
    }

    #[test]
    fn test_coproduct_construction() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let mut cat = FiniteCategory::new("Copr", vec![a.clone(), b.clone()]);
        let coprod = coproduct(&mut cat, &a, &b);
        assert_eq!(coprod.object, Obj::new("A+B"));
        assert_eq!(coprod.inj1.dom, a);
        assert_eq!(coprod.inj2.dom, b);
    }

    #[test]
    fn test_coproduct_copairing() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let mut cat = FiniteCategory::new("CoprPair", vec![a.clone(), b.clone(), c.clone()]);
        let coprod = coproduct(&mut cat, &a, &b);
        let f = Morphism::new("f", a, c.clone());
        let g = Morphism::new("g", b, c.clone());
        let copair = coprod.copair(&f, &g);
        assert_eq!(copair.dom, coprod.object);
        assert_eq!(copair.cod, c);
    }

    #[test]
    fn test_equalizer_construction() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let mut cat = FiniteCategory::new("Eq", vec![a.clone(), b.clone()]);
        let f = cat.add_morphism("f", &a, &b);
        let g = cat.add_morphism("g", &a, &b);
        let eq = equalizer(&mut cat, &f, &g);
        assert_eq!(eq.object, Obj::new("Eq(f,g)"));
        assert_eq!(eq.equalizer_morphism.cod, a);
    }

    #[test]
    fn test_pullback_construction() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let mut cat = FiniteCategory::new("Pb", vec![a.clone(), b.clone(), c.clone()]);
        let f = cat.add_morphism("f", &a, &c);
        let g = cat.add_morphism("g", &b, &c);
        let pb = pullback(&mut cat, &f, &g);
        assert_eq!(pb.object, Obj::new("Pb(f,g)"));
        assert_eq!(pb.proj1.cod, a);
        assert_eq!(pb.proj2.cod, b);
    }

    #[test]
    fn test_pushout_construction() {
        let a = Obj::new("A");
        let b = Obj::new("B");
        let c = Obj::new("C");
        let mut cat = FiniteCategory::new("Po", vec![a.clone(), b.clone(), c.clone()]);
        let f = cat.add_morphism("f", &c, &a);
        let g = cat.add_morphism("g", &c, &b);
        let po = pushout(&mut cat, &f, &g);
        assert_eq!(po.object, Obj::new("Po(f,g)"));
        assert_eq!(po.inj1.dom, a);
        assert_eq!(po.inj2.dom, b);
    }

    #[test]
    fn test_product_projections() {
        let x = Obj::new("X");
        let y = Obj::new("Y");
        let mut cat = FiniteCategory::new("ProjTest", vec![x.clone(), y.clone()]);
        let prod = product(&mut cat, &x, &y);
        assert_eq!(prod.proj1.name, "π₁_XY");
        assert_eq!(prod.proj2.name, "π₂_XY");
    }

    #[test]
    fn test_coproduct_injections() {
        let x = Obj::new("X");
        let y = Obj::new("Y");
        let mut cat = FiniteCategory::new("InjTest", vec![x.clone(), y.clone()]);
        let coprod = coproduct(&mut cat, &x, &y);
        assert_eq!(coprod.inj1.name, "i₁_XY");
        assert_eq!(coprod.inj2.name, "i₂_XY");
    }
}
