// compile with `rustc --edition=2018 --test hashtable.rs`

use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

pub enum HashMapItem<V> {
    Empty,
    Tombstone { key: u64 },
    Entry { key: u64, value: V },
}

impl<V: Clone> Clone for HashMapItem<V> {
    fn clone(&self) -> Self {
        match self {
            HashMapItem::Empty => HashMapItem::Empty,
            HashMapItem::Tombstone { key } => HashMapItem::Tombstone { key: *key },
            HashMapItem::Entry { key, ref value } => HashMapItem::Entry { key: *key, value: value.clone() },
        }
    }
}

pub struct FixedSizeHashMap<V> {
    storage: Vec<HashMapItem<V>>,
    count: usize,
}

impl<V> FixedSizeHashMap<V> {
    pub fn new(size: usize) -> Self {
        Self {
            storage: (0..size).map(|_| HashMapItem::Empty).collect(),
            count: 0,
        }
    }

    pub fn from_storage(storage: Vec<HashMapItem<V>>, count: usize) {
        if cfg!(debug_assertions) {
            assert_eq!(
                storage.iter().filter(|s| match s {
                    HashMapItem::Entry { .. } | HashMapItem::Tombstone { .. } => true,
                    HashMapItem::Empty => false
                }).count(),
                count);
        }
    }

    fn slot_for_key(&self, key: u64) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let h = hasher.finish();
        (h as usize) % self.storage.len()
    }

    fn slot_successor(&self, slot: usize) -> usize {
        // written to match the dafny implementation (to avoid potential overflow)
        if slot == (self.storage.len() - 1) {
            0
        } else {
            slot + 1
        }
    }

    fn probe(&self, key: u64) -> usize {
        let mut slot_idx = self.slot_for_key(key);
        loop {
            match &self.storage[slot_idx] {
                HashMapItem::Empty => return slot_idx,
                HashMapItem::Tombstone { key: t_key } if key == *t_key => return slot_idx,
                HashMapItem::Entry { key: t_key, value: _ } if key == *t_key => return slot_idx,
                _ => (),
            }
            slot_idx = self.slot_successor(slot_idx);
        }
    }

    pub fn insert(&mut self, key: u64, value: V) -> Option<V> {
        if self.count == self.storage.len() {
            panic!("hashtable is full");
        }
        let slot_idx = self.probe(key);
        if let HashMapItem::Entry { key: _, value: ref mut old_value } = &mut self.storage[slot_idx] {
            /* return */ Some(std::mem::replace(old_value, value))
        } else {
            if let HashMapItem::Empty = &self.storage[slot_idx] {
                self.count += 1;
            }
            self.storage[slot_idx] = HashMapItem::Entry { key, value };
            None
        }
    }

    pub fn get<'a>(&'a self, key: u64) -> Option<&'a V> { // note return type
        let slot_idx = self.probe(key);
        match &self.storage[slot_idx] {
            HashMapItem::Entry { key: _, ref value } => Some(value),
            _ => None,
        }
    }

    pub fn remove(&mut self, key: u64) -> Option<V> {
        let slot_idx = self.probe(key);
        match &self.storage[slot_idx] {
            HashMapItem::Entry { .. } => {
                // non-lexical-lifetime required
                let entry = std::mem::replace(&mut self.storage[slot_idx], HashMapItem::Tombstone { key: key });
                if let HashMapItem::Entry { key: _, /* move */ value } = entry {
                    Some(value)
                } else {
                    unreachable!()
                }
            },
            _ => None,
        }
    }

    pub fn update_by_slot(&mut self, slot_idx: usize, value: V) {
        match &mut self.storage[slot_idx] {
            HashMapItem::Entry { key: _, value: ref mut slot_value } => {
                *slot_value = value;
            }
            _ => {
                panic!("slot is not an Entry");
            }
        }
    }
}

impl<V: Clone> Clone for FixedSizeHashMap<V> {
    fn clone(&self) -> Self {
        Self {
            storage: self.storage.clone(),
            count: self.count,
        }
    }
}

#[cfg(test)]
mod fixed_size_hash_map_test {
    use super::*;

    #[test]
    fn test1() {
        let mut hm = FixedSizeHashMap::new(1024);
        for i in (0..128).filter(|x| x % 3 == 0) {
            hm.insert(i, i);
        }
        for i in 0..128 {
            let v = hm.get(i);
            if i % 3 == 0 {
                assert_eq!(v, Some(&i));
            } else {
                assert_eq!(v, None);
            }
        }
        for i in (0..128).filter(|x| x % 3 == 0 && x % 2 == 0) {
            assert_eq!(hm.remove(i), Some(i));
        }
        for i in 0..128 {
            let v = hm.get(i);
            if i % 3 == 0 && i % 2 != 0 {
                assert_eq!(v, Some(&i));
            } else {
                assert_eq!(v, None);
            }
        }
        for i in 129..512 {
            hm.insert(i, i);
        }
    }
}

pub struct ResizingHashMap<V> {
    underlying: FixedSizeHashMap<V>,
    count: usize,
}

impl<V> ResizingHashMap<V> {
    pub fn new(size: usize) -> Self {
        Self {
            underlying: FixedSizeHashMap::new(size),
            count: 0,
        }
    }

    pub fn from_underlying(underlying: FixedSizeHashMap<V>, count: usize) -> Self {
        if cfg!(debug_assertions) {
            assert_eq!(
                underlying.storage.iter().filter(|s| if let HashMapItem::Entry { .. } = s { true } else { false }).count(),
                count);
        }
        Self {
            underlying,
            count,
        }
    }

    fn realloc(&mut self) {
        let new_size = (128 + self.count) * 4;
        // take apart the old underlying
        let FixedSizeHashMap { storage: old_storage, count: _ } =
            std::mem::replace(&mut self.underlying, FixedSizeHashMap::new(new_size));
        for e in old_storage.into_iter() {
            if let HashMapItem::Entry { key, value } = e {
                self.underlying.insert(key, value);
            }
        }
    }

    pub fn insert_and_get_old(&mut self, key: u64, value: V) -> Option<V> {
        if self.underlying.storage.len() / 2 <= self.underlying.count {
            self.realloc();
        }

        let replaced = self.underlying.insert(key, value);
        if replaced.is_none() {
            self.count += 1;
        }
        replaced
    }

    pub fn insert(&mut self, key: u64, value: V) {
        let _ = self.insert_and_get_old(key, value);
        // drop the replaced value, if any
    }

    pub fn remove_and_get(&mut self, key: u64) -> Option<V> {
        let removed = self.underlying.remove(key);
        if removed.is_some() {
            self.count -= 1;
        }
        removed
    }

    pub fn remove(&mut self, key: u64) {
        let _ = self.remove_and_get(key);
        // drop removed value, if any
    }

    pub fn get<'a>(&'a self, key: u64) -> Option<&'a V> {
        self.underlying.get(key)
    }

    // idiomatic rust iterator
    pub fn iter<'a>(&'a self) -> HashMapIter<'a, V> {
        HashMapIter {
            map: self,
            slot_idx: 0,
        }
    }

    // idiomatic rust iterator with mutable references
    pub fn iter_mut<'a>(&'a mut self) -> HashMapIterMut<'a, V> {
        HashMapIterMut {
            map: self,
            slot_idx: 0,
        }
    }

    pub fn max_key(&self) -> u64 {
        let mut m = 0;
        for (k, _) in self.iter() {
            if k > m {
                m = k;
            }
        }
        m
    }

    // veribetrfs-style iterator (no reference to the map in the iterator object)
    pub fn veribetrfs_iter_start<'a>(&'a self) -> VeribetrfsHashMapIter<'a, V> {
        let mut slot_idx = 0;
        while slot_idx < self.underlying.storage.len() {
            if let HashMapItem::Entry { key, ref value } = &self.underlying.storage[slot_idx] {
                return VeribetrfsHashMapIter {
                    slot_idx,
                    next: Some((*key, value)),
                };
            }
            slot_idx += 1;
        }
        VeribetrfsHashMapIter {
            slot_idx,
            next: None,
        }
    }

    // veribetrfs-style iterator (no reference to the map in the iterator object)
    pub fn veribetrfs_iter_inc<'a, 'b>(&'a self, it: VeribetrfsHashMapIter<'b, V>) -> VeribetrfsHashMapIter<'a, V> {
        let VeribetrfsHashMapIter { slot_idx, next: _ } = it;
        let mut slot_idx = slot_idx + 1;
        while slot_idx < self.underlying.storage.len() {
            if let HashMapItem::Entry { key, ref value } = &self.underlying.storage[slot_idx] {
                return VeribetrfsHashMapIter {
                    slot_idx,
                    next: Some((*key, value)),
                };
            }
            slot_idx += 1;
        }
        VeribetrfsHashMapIter {
            slot_idx,
            next: None,
        }
    }
}

impl<V: Clone> Clone for ResizingHashMap<V> {
    fn clone(&self) -> Self {
        Self {
            underlying: self.underlying.clone(),
            count: self.count,
        }
    }
}

pub struct HashMapIter<'a, V: 'a> {
    map: &'a ResizingHashMap<V>,
    slot_idx: usize,
}

impl<'a, V: 'a> Iterator for HashMapIter<'a, V> {
    type Item = (u64, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.slot_idx < self.map.underlying.storage.len() {
            let cur_slot = self.slot_idx;
            self.slot_idx += 1;
            if let HashMapItem::Entry { key, value } = &self.map.underlying.storage[cur_slot] {
                return Some((*key, value));
            }
        }
        return None;
    }
}

pub struct HashMapIterMut<'a, V: 'a> {
    map: &'a mut ResizingHashMap<V>,
    slot_idx: usize,
}

impl<'a, V: 'a> Iterator for HashMapIterMut<'a, V> {
    type Item = (u64, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.slot_idx < self.map.underlying.storage.len() {
            let cur_slot = self.slot_idx;
            self.slot_idx += 1;
            if let HashMapItem::Entry { key, ref mut value } = &mut self.map.underlying.storage[cur_slot] {
                unsafe {
                    // this is safe because we never return the same reference from this iterator
                    let elided: *mut V = value as *mut _;
                    return Some((*key, &mut *elided));
                }
            }
        }
        return None;
    }
}

pub struct VeribetrfsHashMapIter<'a, V> {
    slot_idx: usize,
    next: Option<(u64, &'a V)>,
}

impl<'a, V> std::ops::Deref for VeribetrfsHashMapIter<'a, V> {
    type Target = Option<(u64, &'a V)>;
    
    fn deref(&self) -> &Self::Target {
        &self.next
    }
}

#[cfg(test)]
mod resizing_hash_map_test {
    use super::*;

    #[test]
    fn test1() {
        let mut rhm = ResizingHashMap::new(1024);
        for i in (0..128).filter(|x| x % 3 == 0) {
            rhm.insert(i, i);
        }
        for i in 0..128 {
            let v = rhm.get(i);
            if i % 3 == 0 {
                assert_eq!(v, Some(&i));
            } else {
                assert_eq!(v, None);
            }
        }

        let iterator = rhm.iter();
        for (k, v) in iterator {
            assert_eq!(k, *v);
            assert!(k % 3 == 0);
        }
        assert!(rhm.iter().count() == (0..128).filter(|x| x % 3 == 0).count());
    }

    // no clone
    struct LinearV { value: u64 }

    #[test]
    fn test2() {
        let mut rhm = ResizingHashMap::new(1024);
        for i in (0..128).filter(|x| x % 3 == 0) {
            rhm.insert(i, LinearV { value: i });
        }
        for i in 0..128 {
            let v = rhm.get(i);
            if i % 3 == 0 {
                match v {
                    Some(LinearV { value }) => assert_eq!(*value, i),
                    None => assert!(false),
                }
            } else {
                assert!(v.is_none());
            }
        }

        let mut iterator = rhm.iter();
        while let Some((k, v)) = iterator.next() {
            assert_eq!(k, v.value);
            assert!(k % 3 == 0);
        }
        assert!(rhm.iter().count() == (0..128).filter(|x| x % 3 == 0).count());

        let mut mut_iterator = rhm.iter_mut();
        while let Some ((_k, ref mut v)) = mut_iterator.next() {
            (*v).value *= 2;
        }

        let mut iterator = rhm.iter();
        while let Some((k, v)) = iterator.next() {
            assert_eq!(k * 2, v.value);
            assert!(k % 3 == 0);
        }

        let mut v_iterator = rhm.veribetrfs_iter_start();
        use std::ops::Deref;
        let mut count = 0;
        while let Some((k, ref v)) = v_iterator.deref() {
            count += 1;
            assert_eq!(k * 2, v.value);
            assert!(k % 3 == 0);
            v_iterator = rhm.veribetrfs_iter_inc(v_iterator);
        }

        assert_eq!(count, (0..128).filter(|x| x % 3 == 0).count());
    }
}
