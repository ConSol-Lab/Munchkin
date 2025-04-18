use std::marker::PhantomData;
use std::num::NonZero;
use std::ops::Index;
use std::ops::IndexMut;

/// Structure for storing elements of type `Value`, the structure can only be indexed by structures
/// of type `Key`.
///
/// Almost all features of this structure require that `Key` implements the [StorageKey] trait.
#[derive(Debug, Hash, PartialEq, Eq)]
pub(crate) struct KeyedVec<Key, Value> {
    /// [PhantomData] to ensure that the [KeyedVec] is bound to the structure
    key: PhantomData<Key>,
    /// Storage of the elements of type `Value`
    elements: Vec<Value>,
}

impl<Key, Value: Clone> Clone for KeyedVec<Key, Value> {
    fn clone(&self) -> Self {
        Self {
            key: PhantomData,
            elements: self.elements.clone(),
        }
    }
}

impl<Key, Value> Default for KeyedVec<Key, Value> {
    fn default() -> Self {
        Self {
            key: PhantomData,
            elements: Vec::default(),
        }
    }
}

impl<Key: StorageKey, Value> KeyedVec<Key, Value> {
    pub(crate) fn new(elements: Vec<Value>) -> Self {
        KeyedVec {
            key: PhantomData,
            elements,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.elements.len()
    }

    pub(crate) fn push(&mut self, value: Value) {
        self.elements.push(value)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &'_ Value> {
        self.elements.iter()
    }

    pub(crate) fn into_entries(self) -> impl Iterator<Item = (Key, Value)> {
        self.elements
            .into_iter()
            .enumerate()
            .map(|(idx, value)| (Key::create_from_index(idx), value))
    }
}

#[allow(unused, reason = "-")]
impl<Key: StorageKey, Value: Clone> KeyedVec<Key, Value> {
    /// Insert a specific key-value pair. If an item already exists with the given key, it is
    /// overwritten.
    pub(crate) fn insert_with_default(&mut self, key: Key, mut value: Value, default_value: Value) {
        self.accomodate(key.clone(), default_value);

        std::mem::swap(&mut value, &mut self.elements[key.index()]);
    }

    pub(crate) fn resize(&mut self, new_len: usize, value: Value) {
        self.elements.resize(new_len, value)
    }

    /// Ensure the storage can accomodate the given key. Values for keys that are between the
    /// current last key and the given key will be `default_value`.
    pub(crate) fn accomodate(&mut self, key: Key, default_value: Value) {
        let idx = key.index();

        if idx >= self.elements.len() {
            self.elements.resize(idx + 1, default_value);
        }
    }
}

impl<Key: StorageKey, Value> Index<Key> for KeyedVec<Key, Value> {
    type Output = Value;

    fn index(&self, index: Key) -> &Self::Output {
        &self.elements[index.index()]
    }
}

impl<Key: StorageKey, Value> Index<&Key> for KeyedVec<Key, Value> {
    type Output = Value;

    fn index(&self, index: &Key) -> &Self::Output {
        &self.elements[index.index()]
    }
}

impl<Key: StorageKey, Value> IndexMut<Key> for KeyedVec<Key, Value> {
    fn index_mut(&mut self, index: Key) -> &mut Self::Output {
        &mut self.elements[index.index()]
    }
}

impl StorageKey for usize {
    fn index(&self) -> usize {
        *self
    }

    fn create_from_index(index: usize) -> Self {
        index
    }
}

impl StorageKey for NonZero<u32> {
    fn index(&self) -> usize {
        self.get() as usize - 1
    }

    fn create_from_index(index: usize) -> Self {
        Self::new(index as u32 + 1).unwrap()
    }
}

/// A simple trait which requires that the structures implementing this trait can generate an index.
pub(crate) trait StorageKey: Clone {
    fn index(&self) -> usize;
    #[allow(unused, reason = "-")]
    fn create_from_index(index: usize) -> Self;
}
