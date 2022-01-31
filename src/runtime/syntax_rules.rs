use comet::api::{Collectable, Finalize, Trace};
use comet_extra::alloc::{hash::HashSet, vector::Vector};

use crate::{Heap, Managed};

use super::{
    value::{Symbol, Value},
    SchemeThread,
};

pub struct SyntaxRules {
    ellipsis: Managed<Symbol>,
    name: Option<Managed<Symbol>>,
    reserved: HashSet<Managed<Symbol>, Heap>,
    literals: HashSet<Managed<Symbol>, Heap>,
    patterns: Vector<Value, Heap>,
    templates: Vector<Value, Heap>,
}

struct MatchTree {
    root: Managed<Node>,
    depth: usize,
    complete: bool,
}

impl MatchTree {
    pub fn new(thread: &mut SchemeThread) -> Self {
        let parent = Vector::new(&mut thread.mutator);
        Self {
            root: thread
                .mutator
                .allocate(Node::Parent(parent), comet::gc_base::AllocationSpace::New),
            depth: 0,
            complete: false,
        }
    }

    pub fn tail_node(&self, depth: usize) -> Managed<Node> {
        let mut res = self.root;
        for _ in 0..depth {
            res = res.last_child();
        }
        res
    }

    pub fn enter(&mut self, thread: &mut SchemeThread, expr: Value) {
        let node = thread
            .mutator
            .allocate(Node::Leaf(expr), comet::gc_base::AllocationSpace::New);
        self.tail_node(self.depth).append_child(thread, node);
    }
}

enum Node {
    Leaf(Value),
    Parent(Vector<Managed<Self>, Heap>),
}

impl Node {
    pub fn append_child(&mut self, thread: &mut SchemeThread, node: Managed<Self>) {
        match self {
            Self::Parent(x) => {
                x.push(&mut thread.mutator, node);
                x.write_barrier(&mut thread.mutator);
            }
            _ => unreachable!(),
        }
    }
    pub fn last_child(&self) -> Managed<Self> {
        match self {
            Self::Parent(x) => *x.last().unwrap(),
            _ => unreachable!(),
        }
    }

    pub fn num_children(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Parent(x) => x.len(),
        }
    }
}

unsafe impl Trace for Node {
    fn trace(&mut self, _vis: &mut dyn comet::api::Visitor) {
        match self {
            Self::Leaf(x) => x.trace(_vis),
            Self::Parent(x) => x.trace(_vis),
        }
    }
}

unsafe impl Finalize for Node {}
impl Collectable for Node {}
