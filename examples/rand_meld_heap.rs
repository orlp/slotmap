// Randomized meldable heap.
// https://en.wikipedia.org/wiki/Randomized_meldable_heap

extern crate slotmap;

use slotmap::{SlotMap, SecondaryMap, Key, Slottable};

// Intentionally not copy or clone.
struct NodeHandle(Key);

#[derive(Copy, Clone)]
struct Node<T: Slottable> {
    value: T,
    children: [Key; 2],
    parent: Key,
}

struct RandMeldHeap<T: Ord + Slottable> {
    sm: SlotMap<Node<T>>,
    rng: std::num::Wrapping<u32>,
    root: Key,
}

impl<T: Ord + std::fmt::Debug + Slottable> RandMeldHeap<T> {
    pub fn new() -> Self {
        Self {
            sm: SlotMap::new(),
            rng: std::num::Wrapping(0xdeadbeef),
            root: Key::null(),
        }
    }

    pub fn coinflip(&mut self) -> bool {
        // Simple LCG for top speed - random quality barely matters.
        self.rng += (self.rng << 8) + std::num::Wrapping(1);
        self.rng >> 31 > std::num::Wrapping(0)
    }

    pub fn insert(&mut self, value: T) -> NodeHandle {
        let k = self.sm.insert(Node {
            value,
            children: [Key::null(), Key::null()],
            parent: Key::null(),
        });

        let root = self.root;
        self.root = self.meld(k, root);

        NodeHandle(k)
    }

    pub fn pop(&mut self) -> Option<T> {
        if let Some(root) = self.sm.remove(self.root) {
            self.root = self.meld(root.children[0], root.children[1]);
            if let Some(new_root) = self.sm.get_mut(self.root) {
                new_root.parent = Key::null();
            }

            Some(root.value)
        } else {
            None
        }
    }

    pub fn remove_key(&mut self, node: NodeHandle) -> T {
        let node = node.0;
        self.unlink_node(node);
        self.sm.remove(node).unwrap().value
    }

    pub fn update_key(&mut self, node: &NodeHandle, value: T) {
        let node = node.0;

        // Unlink and re-insert.
        self.unlink_node(node);
        self.sm[node] = Node {
            value,
            children: [Key::null(), Key::null()],
            parent: Key::null(),
        };
        let root = self.root;
        self.root = self.meld(node, root);
    }

    fn unlink_node(&mut self, node: Key) {
        // Remove node from heap by merging children and placing them where
        // node used to be.
        let children = self.sm[node].children;
        let parent_key = self.sm[node].parent;

        let melded_children = self.meld(children[0], children[1]);
        if let Some(mc) = self.sm.get_mut(melded_children) {
            mc.parent = parent_key;
        }

        if let Some(parent) = self.sm.get_mut(parent_key) {
            if parent.children[0] == node {
                parent.children[0] = melded_children;
            } else {
                parent.children[1] = melded_children;
            }
        } else {
            self.root = melded_children;
        }
    }

    fn meld(&mut self, mut a: Key, mut b: Key) -> Key {
        if a.is_null() { return b; }
        if b.is_null() { return a; }

        if self.sm[a].value > self.sm[b].value {
            std::mem::swap(&mut a, &mut b);
        }

        let ret = a;

        // From this point parent and trickle are assumed to be valid keys.
        let mut parent = a;
        let mut trickle = b;

        loop {
            // If a child spot is free, put our trickle there.
            let children = self.sm[parent].children;
            if children[0].is_null() {
                self.sm[parent].children[0] = trickle;
                self.sm[trickle].parent = parent;
                break;
            } else if children[1].is_null() {
                self.sm[parent].children[1] = trickle;
                self.sm[trickle].parent = parent;
                break;
            }

            // No spot free, choose a random child.
            let c = self.coinflip() as usize;
            let child = children[c];
            if self.sm[child].value > self.sm[trickle].value {
                self.sm[parent].children[c] = trickle;
                self.sm[trickle].parent = parent;
                parent = trickle;
                trickle = child;
            } else {
                parent = child;
            }
        }
        
        ret
    }

    pub fn len(&self) -> usize {
        self.sm.len()
    }
}


fn main() {
    let mut rhm = RandMeldHeap::new();
    let the_answer = rhm.insert(-2);
    let big = rhm.insert(999);

    for k in (0..10).rev() {
        rhm.insert(k * k);
    }

    rhm.update_key(&the_answer, 42);
    rhm.remove_key(big);

    while rhm.len() > 0 {
        println!("{}", rhm.pop().unwrap());
    }

    let mut sm = SlotMap::new();
    let foo = sm.insert("foo");  // Key generated on insert.
    let bar = sm.insert("bar");
    assert_eq!(sm[foo], "foo");
    assert_eq!(sm[bar], "bar");

    sm.remove(bar);
    let reuse = sm.insert("reuse");  // Space from bar reused.
    assert_eq!(sm.contains_key(bar), false);  // After deletion a key stays invalid.

    let mut sec = SecondaryMap::new();
    sec.insert(foo, "noun");  // We provide the key for secondary maps.
    sec.insert(reuse, "verb");

    for (key, val) in sm {
        println!("{} is a {}", val, sec[key]);
    }
}
