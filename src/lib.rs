//! Defines the [NumMap] struct which acts as if all unmapped keys have a value of 0.
//! 
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-03-31

#![deny(missing_docs,)]
#![cfg_attr(feature = "map_get_key_value", feature(map_get_key_value,),)]

use std::{
  hash::*, iter::*, fmt,
  ops::{Deref, DerefMut,},
  borrow::{Borrow, BorrowMut,},
  convert::{AsRef, AsMut,},
  collections::{hash_map::RandomState, HashMap,},
  cmp::Ordering,
};

mod number;
mod iter;

pub use self::{number::*, iter::*,};

/// A map of numbers where all keys are considered mapped but 0 values are not stored.
pub struct NumMap<K, V, S = RandomState,>(HashMap<K, V::NonZero, S>,)
  where V: Number;

impl<K, V,> NumMap<K, V, RandomState,>
  where K: Hash + Eq, V: Number, {
  /// Creates an empty `NumMap`.
  /// 
  /// The hash map is initially created with a capacity of 0, so it will not allocate until it is first inserted into.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map: NumMap<&str, i32> = NumMap::new();
  #[inline]
  pub fn new() -> Self { HashMap::new().into() }
  /// Creates an empty `NumMap` with the specified capacity.
  /// 
  /// The `NumMap` will be able to hold at least capacity elements without reallocating.
  /// If capacity is 0, the hash map will not allocate.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let map: NumMap<&str, i32> = NumMap::with_capacity(10);
  /// ```
  #[inline]
  pub fn with_capacity(capactiy: usize,) -> Self { HashMap::with_capacity(capactiy,).into() }
}

impl<K, V, S,> NumMap<K, V, S,>
  where V: Number, {
  /// An iterator over all the key/value pairs present in this `NumMap`.
  #[inline]
  pub fn iter(&self,) -> Iter<K, V,> {
    Iter(self.0.iter().map(|(k, v,): (&K, &V::NonZero,),| (k, v.get(),),))
  }
}

impl<K, V, S,> NumMap<K, V, S,>
  where K: Eq + Hash, V: Number, S: BuildHasher, {
  /// Creates an empty `NumMap` which will use the given hash builder to hash keys.
  /// 
  /// The created map has the default initial capacity.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// use std::collections::hash_map::RandomState;
  /// 
  /// let s = RandomState::new();
  /// let mut map = NumMap::<i32, i32,>::with_hasher(s);
  /// 
  /// map.set(1, 2);
  /// ```
  /// 
  /// # Warnings
  /// 
  /// `hash_builder` is normally randomly generated, and is designed to allow `NumMap`s
  /// to be resistant to attacks that cause many collisions and very poor performance.
  /// Setting it manually using this function can expose a DoS attack vector.
  #[inline]
  pub fn with_hasher(hash_builder: S,) -> Self { HashMap::with_hasher(hash_builder,).into() }
  /// Creates an empty `NumMap` with the specified capacity, using hash_builder to hash the keys.
  /// 
  /// The hash map will be able to hold at least capacity elements without reallocating.
  /// If capacity is 0, the hash map will not allocate.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// use std::collections::hash_map::RandomState;
  /// 
  /// let s = RandomState::new();
  /// let mut map = NumMap::<i32, i32,>::with_capacity_and_hasher(10, s);
  /// 
  /// map.set(1, 2);
  /// ```
  /// 
  /// # Warning
  /// 
  /// `hash_builder` is normally randomly generated, and is designed to allow `NumMap`s
  /// to be resistant to attacks that cause many collisions and very poor performance.
  /// Setting it manually using this function can expose a DoS attack vector.
  #[inline]
  pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S,) -> Self {
    HashMap::with_capacity_and_hasher(capacity, hash_builder,).into()
  }
  /// Returns the value mapped to the corresponding key.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::<i32, i32,>::new();
  /// 
  /// map.set(1, 2);
  /// assert_eq!(map.get(&1), 2);
  /// assert_eq!(map.get(&2), 0);
  /// ```
  #[inline]
  pub fn get<Q,>(&self, k: &Q,) -> V
    where K: Borrow<Q>, Q: Hash + Eq, {
    self.0.get(k,).map(|v,| v.get(),).unwrap_or(V::ZERO,)
  }
  /// Returns the key-value pair corresponding to the supplied key.
  /// 
  /// The supplied key may be any borrowed form of the map's key type, but `Hash` and
  /// `Eq` on the borrowed form must match those for the key type.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// #![feature(map_get_key_value)]
  /// 
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::new();
  /// 
  /// map.set(1, 2);
  /// assert_eq!(map.get_key_value(&1), (&1, 2));
  /// assert_eq!(map.get_key_value(&2), (&2, 0));
  /// ```
  #[cfg(feature = "map_get_key_value",)]
  #[inline]
  pub fn get_key_value<'a,>(&'a self, k: &'a K,) -> (&'a K, V) {
    self.0.get_key_value(k,).map(|(k, v,),| (k, v.get(),),).unwrap_or((k, V::ZERO,),)
  }
  /// Updates the value mapped to the corresponding key and returns the old value.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::<i32, i32,>::new();
  /// 
  /// assert_eq!(map.set(1, 2), 0);
  /// assert_eq!(map.set(1, 0), 2);
  /// ```
  pub fn set(&mut self, k: K, v: V,) -> V {
    match V::NonZero::new(v,) {
      Some(v) => self.0.insert(k, v,),
      None => self.0.remove(&k,)
    }.map(V::NonZero::get,).unwrap_or(V::ZERO,)
  }
  /// Updates the value mapped to the corresponding key and returns the old value.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// use std::num::NonZeroU32;
  /// 
  /// let mut map = NumMap::<u32, u32,>::new();
  /// let two = NonZeroU32::new(2,).unwrap();
  /// 
  /// assert_eq!(map.insert(1, two), 0);
  /// ```
  #[inline]
  pub fn insert(&mut self, k: K, v: V::NonZero,) -> V {
    self.0.insert(k, v,).map(V::NonZero::get,).unwrap_or(V::ZERO,)
  }
  /// Removes and returns the value mapped to the corresponding key.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::<i32, i32,>::new();
  /// 
  /// assert_eq!(map.remove(&1), 0);
  /// assert_eq!(map.set(1, 2), 0);
  /// assert_eq!(map.remove(&1), 2);
  /// ```
  #[inline]
  pub fn remove<Q,>(&mut self, k: &Q,) -> V
    where K: Borrow<Q>, Q: Eq + Hash, {
    self.0.remove(k,).map(V::NonZero::get,).unwrap_or(V::ZERO,)
  }
  /// Removes and returns both the key and the value mapped to the key.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::<i32, i32,>::new();
  /// 
  /// assert_eq!(map.remove_entry(1), (1, 0,));
  /// assert_eq!(map.set(1, 2), 0);
  /// assert_eq!(map.remove_entry(1), (1, 2,));
  /// ```
  #[inline]
  pub fn remove_entry(&mut self, k: K,) -> (K, V) {
    self.0.remove_entry(&k,).map(|(k, v,),| (k, v.get(),),).unwrap_or((k, V::ZERO,),)
  }
  /// Retains only the elements specified by the predicate.
  /// 
  /// In other words, remove all pairs (k, v) such that f(&k,&mut v) returns false.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map: NumMap<i32, i32> = (0..8).map(|x|(x, x*10)).collect();
  /// 
  /// map.retain(|&k, _| k % 2 == 1);
  /// assert_eq!(map.len(), 4);
  /// ```
  #[inline]
  pub fn retain<F,>(&mut self, mut f: F,)
    where F: FnMut(&K, V,) -> bool, {
    self.0.retain(move |k, v,| f(k, v.get(),),)
  }
}

impl<K, V, S,> Clone for NumMap<K, V, S,>
  where V: Number, HashMap<K, V::NonZero, S>: Clone, {
  #[inline]
  fn clone(&self,) -> Self { self.0.clone().into() }
}

impl<K, V, S,> From<HashMap<K, V::NonZero, S>> for NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn from(from: HashMap<K, V::NonZero, S>,) -> Self { NumMap(from,) }
}

impl<K, V, S,> Default for NumMap<K, V, S,>
  where V: Number, HashMap<K, V::NonZero, S>: Default, {
  #[inline]
  fn default() -> Self { HashMap::default().into() }
}

impl<K, V, S,> PartialEq<HashMap<K, V::NonZero, S>> for NumMap<K, V, S,>
  where V: Number, HashMap<K, V::NonZero, S>: PartialEq, {
  #[inline]
  fn eq(&self, rhs: &HashMap<K, V::NonZero, S>,) -> bool { self.0 == *rhs }
}

impl<K, V, S,> PartialEq for NumMap<K, V, S,>
  where V: Number, Self: PartialEq<HashMap<K, V::NonZero, S>>, {
  #[inline]
  fn eq(&self, rhs: &Self,) -> bool { *self == rhs.0 }
}

impl<K, V, S,> Eq for NumMap<K, V, S,>
  where V: Number, HashMap<K, V::NonZero, S>: Eq, {}

/// Compares the two sets; sets are only considered `Greater` or `Less` if **ALL** of the
/// mapping are `Greater` or `Less` (`Equal` is ignored).
impl<K, V, S,> PartialOrd<HashMap<K, V::NonZero, S>> for NumMap<K, V, S,>
  where K: Eq + Hash, V: Number, S: BuildHasher,
    Self: PartialEq<HashMap<K, V::NonZero, S>>, {
  fn partial_cmp(&self, rhs: &HashMap<K, V::NonZero, S>,) -> Option<Ordering> {
    let mut lhs_iter;
    let mut rhs_iter;
    //Iterate over all values from the largest set.
    let iter: &mut dyn Iterator<Item = Ordering> = if self.len() >= rhs.len() {
      lhs_iter = self.0.iter().map(|(k, v,),| rhs.get(k,)
        .map(move |rhs,| v.get().cmp(&rhs.get(),),)
        .unwrap_or(Ordering::Greater,),
      );

      &mut lhs_iter
    } else {
      rhs_iter = rhs.iter().map(|(k, rhs,),| self.0.get(k,)
        .map(move |v,| v.get().cmp(&rhs.get(),),)
        .unwrap_or(Ordering::Less,),
      );

      &mut rhs_iter
    };
    //Filter out all equal values.
    let mut iter = iter.filter(move |o,| o != &Ordering::Equal,);
    let ord = match iter.next() {
      Some(ord) => ord,
      //If there is no unequal values the sets are equal.
      None => return Some(Ordering::Equal),
    };

    //If all orderings are aligned the sets are ordered.
    if iter.all(move |o,| ord == o,) { return Some(ord) }
    else { None }
  }
}

impl<K, V, S,> PartialOrd for NumMap<K, V, S,>
  where K: Eq + Hash, V: Number, S: BuildHasher,
    Self: PartialOrd<HashMap<K, V::NonZero, S>>, {
  #[inline]
  fn partial_cmp(&self, rhs: &Self,) -> Option<Ordering> { self.partial_cmp(&rhs.0,) }
}

impl<K, V, S, A,> FromIterator<A> for NumMap<K, V, S,>
  where K: Hash + Eq, V: Number, S: Default + BuildHasher, A: Into<(K, V,)>, {
  fn from_iter<Iter,>(iter: Iter,) -> Self
    where Iter: IntoIterator<Item = A>, {
    iter.into_iter()
    .map(A::into,)
    .filter_map(|(k, v,),| V::NonZero::new(v,).map(move |v,| (k, v,),),)
    .collect::<HashMap<_, _, S,>>().into()
  }
}

impl<'a, K, V, S,> Extend<(&'a K, &'a V,)> for NumMap<K, V, S,>
  where K: 'a + Hash + Eq + Copy, V: 'a + Number, S: Default + BuildHasher, {
  #[inline]
  fn extend<Iter,>(&mut self, iter: Iter,)
    where Iter: IntoIterator<Item = (&'a K, &'a V,)>, {
    self.extend(iter.into_iter()
      .map(|(&k, &v,),| (k, v,),),
    )
  }
}

impl<K, V, S,> Extend<(K, V,)> for NumMap<K, V, S,>
  where K: Hash + Eq, V: Number, S: Default + BuildHasher, {
  fn extend<Iter,>(&mut self, iter: Iter,)
    where Iter: IntoIterator<Item = (K, V,)>, {
    self.0.extend(
      iter.into_iter()
      .filter_map(|(k, v,),| V::NonZero::new(v,).map(move |v,| (k, v,),),),
    )
  }
}

impl<K, V, S,> IntoIterator for NumMap<K, V, S,>
  where V: Number, {
  type Item = (K, V,);
  type IntoIter = IntoIter<K, V,>;

  #[inline]
  fn into_iter(self,) -> Self::IntoIter {
    IntoIter(self.0.into_iter().map(|(k, v,): (K, V::NonZero,),| (k, v.get(),),),)
  }
}

impl<K, V, S,> Deref for NumMap<K, V, S,>
  where V: Number, {
  type Target = HashMap<K, V::NonZero, S>;

  #[inline]
  fn deref(&self,) -> &Self::Target { &self.0 }
}

impl<K, V, S,> DerefMut for NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn deref_mut(&mut self,) -> &mut Self::Target { &mut self.0 }
}

impl<K, V, S,> Borrow<HashMap<K, V::NonZero, S>> for NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn borrow(&self,) -> &HashMap<K, V::NonZero, S> { &self.0 }
}

impl<K, V, S,> BorrowMut<HashMap<K, V::NonZero, S>> for NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn borrow_mut(&mut self,) -> &mut HashMap<K, V::NonZero, S> { &mut self.0 }
}

impl<K, V, S,> AsRef<HashMap<K, V::NonZero, S>> for NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn as_ref(&self,) -> &HashMap<K, V::NonZero, S> { &self.0 }
}

impl<K, V, S,> AsMut<HashMap<K, V::NonZero, S>> for NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn as_mut(&mut self,) -> &mut HashMap<K, V::NonZero, S> { &mut self.0 }
}

impl<K, V, S,> fmt::Debug for NumMap<K, V, S,>
  where V: Number, HashMap<K, V::NonZero, S>: fmt::Debug, {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { self.0.fmt(fmt,) }
}

#[cfg(test,)]
mod tests {
  use super::*;

  #[test]
  fn test_cmp() {
    let one = (1..=10).map(|x,| (x, x,),).collect::<NumMap<_, _,>>();
    let two = (1..=10).map(|x,| (x, 2 * x,),).collect::<NumMap<_, _,>>();
    let neg_two = (1..=10).map(|x,| (x, -2 * x,),).collect::<NumMap<_, _,>>();

    assert!(one < two);
    assert!(one > neg_two);
    assert!(two > neg_two);
    assert!(one == one);
    assert!(one >= one);
    assert!(one <= one);
    assert!(neg_two == neg_two);
    assert!(neg_two >= neg_two);
    assert!(neg_two <= neg_two);
  }
}
