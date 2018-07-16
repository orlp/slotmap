// A simple doubly linked list example using slotmap.

extern crate slotmap;

use slotmap::{SlotMap, Key};

struct Node<T> {
    value: T,
    prev: Key,
    next: Key,
}

struct List<T> {
    sm: SlotMap<Node<T>>,
    head: Key,
    tail: Key,
}

impl<T> List<T> {
    fn new() -> Self {
        Self {
            sm: SlotMap::new(),
            head: Key::null(),
            tail: Key::null(),
        }
    }

    fn len(&self) -> usize {
        self.sm.len()
    }

    fn push_head(&mut self, value: T) {
        let k = self.sm.insert(Node {
            value,
            prev: Key::null(),
            next: self.head,
        });

        if let Some(old_head) = self.sm.get_mut(self.head) {
            old_head.prev = k;
        } else {
            self.tail = k;
        }
        self.head = k;
    }
    
    fn push_tail(&mut self, value: T) {
        let k = self.sm.insert(Node {
            value,
            prev: self.tail,
            next: Key::null(),
        });

        if let Some(old_tail) = self.sm.get_mut(self.tail) {
            old_tail.next = k;
        } else {
            self.head = k;
        }
        self.tail = k;
    }

    fn pop_head(&mut self) -> Option<T> {
        if let Some(old_head) = self.sm.remove(self.head) {
            self.head = old_head.next;
            Some(old_head.value)
        } else {
            None
        }
    }

    fn pop_tail(&mut self) -> Option<T> {
        if let Some(old_tail) = self.sm.remove(self.tail) {
            self.tail = old_tail.prev;
            Some(old_tail.value)
        } else {
            None
        }
    }
}

extern crate serde_json;

fn main() {
    let mut dll = List::new();
    dll.push_head(5);
    dll.push_tail(6);
    dll.push_tail(7);
    dll.push_head(4);

    assert_eq!(dll.len(), 4);
    assert_eq!(dll.pop_head(), Some(4));
    assert_eq!(dll.pop_head(), Some(5));
    assert_eq!(dll.pop_tail(), Some(7));
    assert_eq!(dll.pop_tail(), Some(6));
    assert_eq!(dll.pop_head(), None);
    assert_eq!(dll.pop_tail(), None);
}
