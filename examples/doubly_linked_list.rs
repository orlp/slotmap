// A simple doubly linked list example using slotmap.

extern crate slotmap;

use slotmap::{SlotMap, Key};

struct Node<T> {
    value: T,
    prev: Option<Key>,
    next: Option<Key>,
}

struct List<T> {
    sm: SlotMap<Node<T>>,
    head: Option<Key>,
    tail: Option<Key>,
    len: usize,
}

impl<T> List<T> {
    fn new() -> Self {
        Self {
            sm: SlotMap::new(),
            head: None,
            tail: None,
            len: 0,
        }
    }

    fn len(&self) -> usize {
        self.len
    }

    fn push_head(&mut self, value: T) {
        let k = self.sm.insert(Node {
            value,
            prev: None,
            next: self.head,
        });

        if let Some(head) = self.head {
            self.sm[head].prev = Some(k);
        } else {
            self.tail = Some(k);
        }
        self.head = Some(k);
        self.len += 1;
    }
    
    fn push_tail(&mut self, value: T) {
        let k = self.sm.insert(Node {
            value,
            prev: self.tail,
            next: None,
        });

        if let Some(tail) = self.tail {
            self.sm[tail].next = Some(k);
        } else {
            self.head = Some(k);
        }
        self.tail = Some(k);
        self.len += 1;
    }

    fn pop_head(&mut self) -> Option<T> {
        if let Some(head) = self.head {
            self.head = self.sm[head].next;
            self.len -= 1;
            if self.len == 0 {
                self.tail = None;
            }

            Some(self.sm.remove(head).unwrap().value)
        } else {
            None
        }
    }

    fn pop_tail(&mut self) -> Option<T> {
        if let Some(tail) = self.tail {
            self.tail = self.sm[tail].prev;
            self.len -= 1;
            if self.len == 0 {
                self.head = None;
            }

            Some(self.sm.remove(tail).unwrap().value)
        } else {
            None
        }
    }
}

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
}
