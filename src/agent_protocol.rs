//! Agent protocol composition — agents as objects, protocols as morphisms.
//!
//! This module applies category theory to model software agents and their
//! communication protocols. Each agent is an object, each protocol (message
//! format + behavior contract) is a morphism, and protocol composition is
//! morphism composition.

use serde::{Serialize, Deserialize};
use crate::category::{FiniteCategory, Obj, Morphism};
use crate::functor::Functor;
use crate::monad::Monad;
use crate::limits::{Product, Coproduct, product, coproduct};

/// An agent in the system, identified by name and role.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Agent {
    pub name: String,
    pub role: String,
}

impl Agent {
    pub fn new(name: impl Into<String>, role: impl Into<String>) -> Self {
        Agent { name: name.into(), role: role.into() }
    }

    pub fn to_obj(&self) -> Obj {
        Obj::new(&self.name)
    }
}

/// A protocol between agents: defines the message format and behavioral contract.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Protocol {
    pub name: String,
    pub from_agent: String,
    pub to_agent: String,
    pub message_format: String,
    pub contract: String,
}

impl Protocol {
    pub fn new(
        name: impl Into<String>,
        from: &Agent,
        to: &Agent,
        format: impl Into<String>,
        contract: impl Into<String>,
    ) -> Self {
        Protocol {
            name: name.into(),
            from_agent: from.name.clone(),
            to_agent: to.name.clone(),
            message_format: format.into(),
            contract: contract.into(),
        }
    }

    pub fn to_morphism(&self) -> Morphism {
        Morphism::new(&self.name, Obj::new(&self.from_agent), Obj::new(&self.to_agent))
    }
}

/// The category of agents and protocols.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentCategory {
    pub category: FiniteCategory,
    pub agents: Vec<Agent>,
    pub protocols: Vec<Protocol>,
}

impl AgentCategory {
    pub fn new(name: impl Into<String>) -> Self {
        AgentCategory {
            category: FiniteCategory::new(name, vec![]),
            agents: vec![],
            protocols: vec![],
        }
    }

    /// Register an agent in the category.
    pub fn add_agent(&mut self, agent: Agent) {
        let obj = agent.to_obj();
        if !self.category.objects.contains(&obj) {
            self.category.objects.push(obj);
        }
        self.agents.push(agent);
    }

    /// Register a protocol between two agents.
    pub fn add_protocol(&mut self, protocol: Protocol) -> Morphism {
        let mor = protocol.to_morphism();
        self.category.morphisms.push(mor.clone());
        self.protocols.push(protocol);
        mor
    }

    /// Compose two protocols: if protocol A goes from agent X to Y,
    /// and protocol B goes from Y to Z, then the composite B∘A goes from X to Z.
    pub fn compose_protocols(
        &mut self,
        first: &Protocol,
        second: &Protocol,
        name: impl Into<String>,
    ) -> Protocol {
        assert_eq!(first.to_agent, second.from_agent,
            "Protocols don't chain: {} ends at {}, but {} starts at {}",
            first.name, first.to_agent, second.name, second.from_agent);

        let composite = Protocol::new(
            name,
            &Agent::new(&first.from_agent, "sender"),
            &Agent::new(&second.to_agent, "receiver"),
            format!("{};{}", first.message_format, second.message_format),
            format!("{} ∘ {}", second.contract, first.contract),
        );

        let mor = composite.to_morphism();
        // Set composition in the category
        let f_mor = first.to_morphism();
        let s_mor = second.to_morphism();
        self.category.morphisms.push(mor.clone());
        self.category.set_composition(&s_mor, &f_mor, &mor);

        self.protocols.push(composite.clone());
        composite
    }

    /// A pipeline of agents and protocols forms a monad-like structure:
    /// agents can be wrapped in "protocol stacks" that compose.
    pub fn protocol_stack_monad(&self) -> Monad {
        let t = Functor::new("ProtocolStack", &self.category.name, &self.category.name);
        let eta = crate::natural_transformation::NaturalTransformation::new("η", "Id", "T");
        let mu = crate::natural_transformation::NaturalTransformation::new("μ", "TT", "T");
        Monad::new("ProtocolStack", t, eta, mu)
    }

    /// Product of agents = parallel composition (fan-out).
    pub fn parallel_compose(&mut self, a: &Agent, b: &Agent) -> Product {
        product(&mut self.category, &a.to_obj(), &b.to_obj())
    }

    /// Coproduct of agents = choice composition (fan-in).
    pub fn choice_compose(&mut self, a: &Agent, b: &Agent) -> Coproduct {
        coproduct(&mut self.category, &a.to_obj(), &b.to_obj())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_agent_creation() {
        let agent = Agent::new("Alice", "client");
        assert_eq!(agent.name, "Alice");
        assert_eq!(agent.role, "client");
        assert_eq!(agent.to_obj(), Obj::new("Alice"));
    }

    #[test]
    fn test_protocol_creation() {
        let alice = Agent::new("Alice", "client");
        let bob = Agent::new("Bob", "server");
        let proto = Protocol::new("greet", &alice, &bob, "JSON", "request-response");
        assert_eq!(proto.from_agent, "Alice");
        assert_eq!(proto.to_agent, "Bob");
        let mor = proto.to_morphism();
        assert_eq!(mor.dom, Obj::new("Alice"));
        assert_eq!(mor.cod, Obj::new("Bob"));
    }

    #[test]
    fn test_agent_category() {
        let mut cat = AgentCategory::new("Agents");
        let alice = Agent::new("Alice", "client");
        let bob = Agent::new("Bob", "server");
        let carol = Agent::new("Carol", "proxy");

        cat.add_agent(alice.clone());
        cat.add_agent(bob.clone());
        cat.add_agent(carol.clone());

        assert_eq!(cat.agents.len(), 3);
        assert_eq!(cat.category.objects.len(), 3);
    }

    #[test]
    fn test_protocol_composition() {
        let mut cat = AgentCategory::new("Chain");
        let alice = Agent::new("Alice", "client");
        let bob = Agent::new("Bob", "proxy");
        let carol = Agent::new("Carol", "server");

        cat.add_agent(alice.clone());
        cat.add_agent(bob.clone());
        cat.add_agent(carol.clone());

        let p1 = Protocol::new("request", &alice, &bob, "JSON", "send");
        let p2 = Protocol::new("forward", &bob, &carol, "JSON", "relay");

        let m1 = cat.add_protocol(p1);
        let m2 = cat.add_protocol(p2);

        let composite = cat.compose_protocols(
            &cat.protocols[0].clone(),
            &cat.protocols[1].clone(),
            "pipe",
        );

        assert_eq!(composite.from_agent, "Alice");
        assert_eq!(composite.to_agent, "Carol");
    }

    #[test]
    fn test_parallel_composition() {
        let mut cat = AgentCategory::new("Parallel");
        let alice = Agent::new("Alice", "client");
        let bob = Agent::new("Bob", "client");
        cat.add_agent(alice.clone());
        cat.add_agent(bob.clone());

        let prod = cat.parallel_compose(&alice, &bob);
        assert_eq!(prod.object, Obj::new("Alice×Bob"));
    }

    #[test]
    fn test_choice_composition() {
        let mut cat = AgentCategory::new("Choice");
        let alice = Agent::new("Alice", "primary");
        let bob = Agent::new("Bob", "fallback");
        cat.add_agent(alice.clone());
        cat.add_agent(bob.clone());

        let coprod = cat.choice_compose(&alice, &bob);
        assert_eq!(coprod.object, Obj::new("Alice+Bob"));
    }

    #[test]
    fn test_protocol_stack_monad() {
        let mut cat = AgentCategory::new("Stack");
        let alice = Agent::new("Alice", "client");
        cat.add_agent(alice);
        let monad = cat.protocol_stack_monad();
        assert_eq!(monad.name, "ProtocolStack");
    }

    #[test]
    fn test_multi_hop_pipeline() {
        let mut cat = AgentCategory::new("MultiHop");
        let a = Agent::new("A", "src");
        let b = Agent::new("B", "hop");
        let c = Agent::new("C", "hop");
        let d = Agent::new("D", "dst");

        cat.add_agent(a.clone());
        cat.add_agent(b.clone());
        cat.add_agent(c.clone());
        cat.add_agent(d.clone());

        let p1 = Protocol::new("p1", &a, &b, "JSON", "send");
        let p2 = Protocol::new("p2", &b, &c, "JSON", "relay");
        let p3 = Protocol::new("p3", &c, &d, "JSON", "deliver");

        cat.add_protocol(p1);
        cat.add_protocol(p2);
        cat.add_protocol(p3);

        let comp1 = cat.compose_protocols(&cat.protocols[0].clone(), &cat.protocols[1].clone(), "p2p1");
        assert_eq!(comp1.from_agent, "A");
        assert_eq!(comp1.to_agent, "C");

        let comp2 = cat.compose_protocols(&comp1, &cat.protocols[2].clone(), "full_pipe");
        assert_eq!(comp2.from_agent, "A");
        assert_eq!(comp2.to_agent, "D");
    }
}
