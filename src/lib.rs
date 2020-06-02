//! Defines the [NumMap] struct which acts as if all unmapped keys have a value of 0.
//! 
//! ```rust
//! # #[macro_use] extern crate nummap; fn main() {
//! let mut map = map![(1, 2), (3, 4)];
//! 
//! //We have set no mapping but we still get 0.
//! assert_eq!(map.get(&0,), 0,);
//! 
//! //We didn't set a mapping here either but we still get 0.
//! assert_eq!(map.set(0, 10,), 0,);
//! assert_eq!(map.get(&0,), 10,);
//! # }
//! ```
//! 
//! Since all keys are considered mapped arithmetic is implemented on values.
//! 
//! ```rust
//! # #[macro_use] extern crate nummap; fn main() {
//! let map = map![(1, 2), (3, 4)] + map![(1, 4), (3, 2)];
//! 
//! assert_eq!(map, map![(1, 3), (3, 3)] * 2,);
//! # }
//! ```
//! 
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2020-01-06

#![deny(missing_docs,)]
#![cfg_attr(feature = "hashbrown", no_std,)]
#![cfg_attr(feature = "map_get_key_value", feature(map_get_key_value,),)]
#![feature(associated_type_defaults,)]

#[cfg(test,)]
extern crate std;
extern crate alloc;

use core::{
  hash::*, iter::*, fmt,
  ops::{
    Deref, DerefMut,
    Add, AddAssign,
    Neg, Sub, SubAssign,
    Mul, MulAssign,
    Div, DivAssign,
  },
  borrow::{Borrow, BorrowMut,},
  convert::{AsRef, AsMut,},
  cmp::Ordering,
};

/// Creates a `NumMap` in a simiar manner to `vec![]`.
/// 
/// The specific `BuildHasher` to use can be specified after the mappings.
/// 
/// ```rust
/// # use nummap::*; fn main() {
/// map![(0, 1), (2, 3); nummap::DefaultHashBuilder];
/// map![(0, 1), (2, 3)];
/// let _: NumMap<i32, i32> = map![];
/// # }
/// ```
#[cfg(feature = "hashbrown",)]
#[macro_export]
macro_rules! map {
  () => (::nummap::NumMap::<_, _, ::nummap::DefaultHashBuilder>::default());
  ($(($k:expr, $v:expr $(,)? ),)* ; $tp:ty) => {{
    let mut map = ::nummap::NumMap::<_, _, $tp>::default();

    $(map.set($k, $v,);)*

    map
  }};
  (($k1:expr, $v1:expr $(,)? ) $(, ($k2:expr, $v2:expr $(,)? ))* $(,)* ; $tp:ty) => (map!(($k1, $v1), $(($k2, $v2,),)* ; $tp));
  (($k1:expr, $v1:expr $(,)? ) $(, ($k2:expr, $v2:expr $(,)? ))* $(,)*) => (map!(($k1, $v1), $(($k2, $v2,),)* ; ::nummap::DefaultHashBuilder));
}

/// Creates a `NumMap` in a simiar manner to `vec![]`.
/// 
/// The specific `BuildHasher` to use can be specified after the mappings.
/// 
/// ```rust
/// # use nummap::*; fn main() {
/// map![(0, 1), (2, 3),; std::collections::hash_map::RandomState];
/// map![(0, 1), (2, 3)];
/// let _: NumMap<i32, i32> = map![];
/// # }
/// ```
#[cfg(not(feature = "hashbrown",),)]
#[macro_export]
macro_rules! map {
  () => (::nummap::NumMap::<_, _, ::nummap::RandomState>::default());
  ($(($k:expr, $v:expr $(,)? ),)* ; $tp:ty) => {{
    let mut map = ::nummap::NumMap::<_, _, $tp>::default();

    $(map.set($k, $v,);)*

    map
  }};
  (($k1:expr, $v1:expr $(,)? ) $(, ($k2:expr, $v2:expr $(,)? ))* $(,)* ; $tp:ty) => (map!(($k1, $v1), $(($k2, $v2,),)* ; $tp));
  (($k1:expr, $v1:expr $(,)? ) $(, ($k2:expr, $v2:expr $(,)? ))* $(,)*) => (map!(($k1, $v1), $(($k2, $v2,),)* ; ::nummap::RandomState));
}

mod number;
mod iter;
#[cfg(not(feature = "hashbrown",),)]
mod with_std;
#[cfg(feature = "hashbrown",)]
mod no_std;
mod serde;

pub use self::{number::*, iter::*,};
#[cfg(not(feature = "hashbrown",),)]
pub use self::with_std::*;
#[cfg(feature = "hashbrown",)]
pub use self::no_std::*;

impl<K, V, S,> NumMap<K, V, S,>
  where V: Number, {
  /// An iterator over all the key/value pairs present in this `NumMap`.
  #[inline]
  pub fn iter(&self,) -> Iter<K, V,> {
    Iter(self.0.iter().map(|(k, v,): (&K, &V::NonZero,),| (k, v.as_num(),),),)
  }
  /// An iterator over all the values present in this `NumMap`.
  #[inline]
  pub fn values(&self,) -> Values<K, V,> {
    Values(self.0.values().map(|v: &V::NonZero,| v.as_num(),),)
  }
  /// An iterator over all the key/value pairs present in this `NumMap`.
  /// 
  /// All the values will be removed from the map.
  #[inline]
  pub fn drain(&mut self,) -> Drain<K, V,> {
    Drain(self.0.drain().map(|(k, v,): (K, V::NonZero,),| (k, v.as_num(),),),)
  }
}

impl<K, V, S,> NumMap<K, V, S,>
  where K: Eq + Hash,
    V: Number,
    S: BuildHasher,
    Option<V::NonZero>: ToNumber<V,>, {
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
    where K: Borrow<Q>,
      Q: Hash + Eq + ?Sized, {
    self.0.get(k,).copied().as_num()
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
      Some(v) => self.insert(k, v,),
      None => self.remove(&k,),
    }
  }
  /// Updates the value mapped to the corresponding key and returns the old value.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// # #[macro_use] extern crate nummap; fn main() {
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::<i32, i32,>::new();
  /// 
  /// assert_eq!(map.update(1, |v,| *v = 2), 0);
  /// assert_eq!(map, map![(1, 2)]);
  /// assert_eq!(map.update(1, |v,| *v = 0), 2);
  /// assert_eq!(map, map![(1, 0)]);
  /// # }
  /// ```
  pub fn update(&mut self, k: K, f: impl FnOnce(&mut V,),) -> V {
    let entry = self.entry(k,);
    let old_num = match &entry {
      Entry::Occupied(entry) => entry.get().as_num(),
      _ => V::ZERO,
    };
    let new_num = {
      let mut num = old_num;

      f(&mut num,); num
    };

    //If the new number is non zero, insert it into the map.
    if let Some(num) = V::NonZero::new(new_num,) {
      entry.insert(num,);
    //If the new number is zero, clear the entry.
    } else if let Entry::Occupied(entry) = entry {
      entry.remove();
    }

    old_num
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
    self.0.insert(k, v,).as_num()
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
    where K: Borrow<Q>,
      Q: Eq + Hash + ?Sized, {
    self.0.remove(k,).as_num()
  }
  /// Iterates the mappings for all the keys returned by `keys`.
  /// 
  /// # Params
  /// 
  /// keys --- The iterator of keys to visit.  
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::<i32, i32,>::new();
  /// 
  /// map.set(1, 2);
  /// map.set(3, 4);
  /// 
  /// let mut iter = map.iter_keys(vec![1, 2, 3],);
  /// 
  /// assert_eq!(iter.next(), Some((1, 2)));
  /// assert_eq!(iter.next(), Some((2, 0)));
  /// assert_eq!(iter.next(), Some((3, 4)));
  /// assert_eq!(iter.next(), None);
  /// ```
  pub fn iter_keys<'a, Q, Iter,>(&'a self, keys: Iter,) -> impl 'a + Iterator<Item = (Q, V,)>
    where K: Borrow<Q>,
      Q: Eq + Hash,
      Iter: 'a + IntoIterator<Item = Q>, {
    keys.into_iter().map(move |k,| {
      let value = self.get(&k,);

      (k, value,)
    },)
  }
  /// Applies a mapping function to the value of all the keys returned by `keys`.
  /// 
  /// # Params
  /// 
  /// keys --- The iterator of keys to visit.  
  /// map --- The mapping function to apply to the entries.  
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map = NumMap::<i32, i32,>::new();
  /// 
  /// map.set(1, 2);
  /// map.set(3, 4);
  /// 
  /// map.map_keys(vec![1, 2, 3], |_, v,| *v -= 2);
  /// 
  /// let mut iter = map.iter();
  /// 
  /// assert_eq!(iter.count(), 2,);
  /// ```
  pub fn map_keys<Iter, F,>(&mut self, keys: Iter, mut map: F,)
    where Iter: IntoIterator<Item = K>,
      F: FnMut(&K, &mut V,), {
    for k in keys {
      let mut v = self.get(&k,);

      map(&k, &mut v,);
      self.set(k, v,);
    }
  }
}

impl<K, V, S,> NumMap<K, V, S,>
  where K: Eq + Hash,
    V: Number,
    S: BuildHasher, {
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
  /// let mut map = NumMap::<i32, i32, RandomState,>::with_hasher(s);
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
  /// let mut map = NumMap::<i32, i32, RandomState,>::with_capacity_and_hasher(10, s);
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
  /// Returns the key-value pair corresponding to the supplied key.
  /// 
  /// The supplied key may be any borrowed form of the map's key type, but `Hash` and
  /// `Eq` on the borrowed form must match those for the key type.
  /// 
  /// Enabled with feature "map_get_key_value".
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
    self.0.get_key_value(k,)
    .map(move |(k, v,),| (k, v.as_num(),),)
    .unwrap_or((k, V::ZERO,),)
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
    self.0.remove_entry(&k,)
    .map(move |(k, v,),| (k, v.as_num(),),)
    .unwrap_or((k, V::ZERO,),)
  }
  /// Retains only the elements specified by the predicate.
  /// 
  /// In other words, remove all pairs (k, v) such that f(&k,&mut v) returns `false`.
  /// 
  /// Be aware that setting a value to its zero value will have it removed implicitly.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use nummap::NumMap;
  /// 
  /// let mut map: NumMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
  /// 
  /// map.retain(|&k, v| {
  ///   *v %= 3;
  ///   k % 2 == 1
  /// },);
  /// assert_eq!(map.len(), 3);
  /// ```
  pub fn retain<F,>(&mut self, mut f: F,)
    where F: FnMut(&K, &mut V,) -> bool, {
    self.0.retain(move |k, v,| {
      let mut num = v.as_num();
      let keep = f(k, &mut num,);

      match NonZero::new(num,) {
        Some(num) => { *v = num; keep },
        None => false,
      }
    },)
  }
}

impl<K, V, S,> Clone for NumMap<K, V, S,>
  where V: Number,
    HashMap<K, V::NonZero, S>: Clone, {
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

impl<K, V, S, A,> PartialEq<A> for NumMap<K, V, S,>
  where V: Number,
    A: Borrow<HashMap<K, V::NonZero, S>>,
    Self: PartialOrd<A>, {
  fn eq(&self, rhs: &A,) -> bool {
    //If the two sets are not equal size then they cannot be equal.
    self.len() == rhs.borrow().len()
    && self.partial_cmp(rhs,) == Some(Ordering::Equal)
  }
}

impl<K, V, S,> Eq for NumMap<K, V, S,>
  where V: Number,
    Self: PartialEq<Self>, {}

/// Compares the two sets; sets are only considered `Greater` or `Less` if **ALL** of the
/// mapping are `Greater` or `Less` (`Equal` is ignored).
impl<K, V, S, A,> PartialOrd<A> for NumMap<K, V, S,>
  where K: Eq + Hash,
    V: Number + PartialOrd,
    S: BuildHasher,
    A: Borrow<HashMap<K, V::NonZero, S>>,
    Option<V::NonZero>: ToNumber<V,>, {
  fn partial_cmp(&self, rhs: &A,) -> Option<Ordering> {
    let rhs = rhs.borrow();
    //The collection of keys.
    let keys = self.keys()
      .chain(rhs.keys(),)
      .collect::<HashSet<_>>()
      .into_iter();
    //The comparisons between all of the value pairs.
    let mut comparisons = keys.map(|k,| {
        let lhs = self.get(k,);
        
        match rhs.get(k,) {
          Some(rhs) => lhs.partial_cmp(&rhs.as_num(),),
          None => lhs.partial_cmp(&V::ZERO,),
        }
      },)
      //Filter out equal comparisons.
      .filter(|&cmp,| cmp != Some(Ordering::Equal),);
    //The first comparison found.
    let cmp = match comparisons.next() {
      //If a pair cannot be compared then the sets cannot be compared.
      Some(cmp) => cmp?,
      //If we found no nonequal comparisons the sets are equal.
      None => return Some(Ordering::Equal),
    };

    for compare in comparisons {
      //If a pair cannot be compared or two different comparisons exist in the set they
      //cannot be compared.
      if compare? != cmp { return None }
    }

    Some(cmp)
  }
}

impl<K, V, S, A,> FromIterator<A> for NumMap<K, V, S,>
  where K: Hash + Eq,
    V: Number,
    S: Default + BuildHasher,
    A: Into<(K, V,)>, {
  fn from_iter<Iter,>(iter: Iter,) -> Self
    where Iter: IntoIterator<Item = A>, {
    iter.into_iter()
    .map(A::into,)
    .filter_map(|(k, v,),| V::NonZero::new(v,).map(move |v,| (k, v,),),)
    .collect::<HashMap<_, _, S,>>().into()
  }
}

impl<'a, K, V, S,> Extend<(&'a K, &'a V,)> for NumMap<K, V, S,>
  where K: 'a + Hash + Eq + Copy,
    V: 'a + Number,
    S: BuildHasher, {
  fn extend<Iter,>(&mut self, iter: Iter,)
    where Iter: IntoIterator<Item = (&'a K, &'a V,)>, {
    self.extend(iter.into_iter()
      .map(|(&k, &v,),| (k, v,),),
    )
  }
}

impl<K, V, S,> Extend<(K, V,)> for NumMap<K, V, S,>
  where K: Hash + Eq,
    V: Number,
    S: BuildHasher, {
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

  fn into_iter(self,) -> Self::IntoIter {
    IntoIter(self.0.into_iter().map(|(k, v,): (K, V::NonZero,),| (k, v.as_num(),),),)
  }
}

impl<'a, K, V, S,> IntoIterator for &'a NumMap<K, V, S,>
  where V: Number, {
  type Item = (&'a K, V,);
  type IntoIter = Iter<'a, K, V,>;

  #[inline]
  fn into_iter(self,) -> Self::IntoIter { self.iter() }
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

impl<K, V, S,> Borrow<HashMap<K, V::NonZero, S>> for &'_ NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn borrow(&self,) -> &HashMap<K, V::NonZero, S> { &self.0 }
}

impl<K, V, S,> Borrow<HashMap<K, V::NonZero, S>> for &'_ mut NumMap<K, V, S,>
  where V: Number, {
  #[inline]
  fn borrow(&self,) -> &HashMap<K, V::NonZero, S> { &self.0 }
}

impl<K, V, S,> BorrowMut<HashMap<K, V::NonZero, S>> for &'_ mut NumMap<K, V, S,>
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
  where K: fmt::Debug,
    V: Number + fmt::Debug, {
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
    fmt.debug_map().entries(self.iter(),).finish()
  }
}

impl<K, V, S,> Neg for NumMap<K, V, S,>
  where K: Eq + Hash,
    V: Number + Neg<Output = V>,
    S: BuildHasher, {
  type Output = Self;

  fn neg(mut self,) -> Self::Output {
    use alloc::vec::Vec;

    let pairs = self.drain()
      .map(|(k, v,),| (k, -v,),)
      .collect::<Vec<_>>();
    self.extend(pairs,);
    
    self
  }
}

impl<K, V, S, A,> Add<A> for NumMap<K, V, S,>
  where V: Number,
    Self: AddAssign<A>, {
  type Output = Self;

  #[inline]
  fn add(mut self, rhs: A,) -> Self::Output { self += rhs; self }
}

impl<K, V, S, A,> AddAssign<A> for NumMap<K, V, S,>
  where K: Eq + Clone + Hash,
    V: Number + AddAssign,
    S: BuildHasher,
    A: Borrow<HashMap<K, V::NonZero, S>>,
    Option<V::NonZero>: ToNumber<V,>, {
  fn add_assign(&mut self, rhs: A,) {
    for (k, v,) in rhs.borrow() {
      self.update(k.clone(), move |n,| *n += v.as_num(),);
    }
  }
}

impl<K, V, S, A,> Sub<A> for NumMap<K, V, S,>
  where V: Number,
    Self: SubAssign<A>, {
  type Output = Self;

  #[inline]
  fn sub(mut self, rhs: A,) -> Self::Output { self -= rhs; self }
}

impl<K, V, S, A,> SubAssign<A> for NumMap<K, V, S,>
  where K: Eq + Clone + Hash,
    V: Number + SubAssign,
    S: BuildHasher,
    A: Borrow<HashMap<K, V::NonZero, S>>,
    Option<V::NonZero>: ToNumber<V,>, {
  fn sub_assign(&mut self, rhs: A,) {
    for (k, v,) in rhs.borrow() {
      self.update(k.clone(), move |n,| *n -= v.as_num(),);
    }
  }
}

impl<K, V1, V2, S,> Mul<V2> for NumMap<K, V1, S,>
  where V1: Number,
    Self: MulAssign<V2>, {
  type Output = Self;

  #[inline]
  fn mul(mut self, rhs: V2,) -> Self::Output { self *= rhs; self }
}

impl<K, V1, V2, S,> MulAssign<V2> for NumMap<K, V1, S,>
  where K: Eq + Hash,
    V1: Number + MulAssign<V2>,
    V2: Clone,
    S: BuildHasher, {
  fn mul_assign(&mut self, rhs: V2,) {
    self.retain(move |_, v,| { *v *= rhs.clone(); true },)
  }
}

impl<K, V1, V2, S,> Div<V2> for NumMap<K, V1, S,>
  where V1: Number,
    Self: DivAssign<V2>, {
  type Output = Self;

  #[inline]
  fn div(mut self, rhs: V2,) -> Self::Output { self /= rhs; self }
}

impl<K, V1, V2, S,> DivAssign<V2> for NumMap<K, V1, S,>
  where K: Eq + Clone + Hash,
    V1: Number + DivAssign<V2>,
    V2: Clone,
    S: BuildHasher, {
  fn div_assign(&mut self, rhs: V2,) {
    self.retain(move |_, v,| { *v /= rhs.clone(); true },)
  }
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
  #[test]
  fn test_math() {
    let one = (1..=10).map(|x,| (x, x,),).collect::<NumMap<_, _,>>();
    let two = (1..=10).map(|x,| (x, 2 * x,),).collect::<NumMap<_, _,>>();

    assert!(one.clone() + &one == two);
    assert!(two.clone() - &one == one);
    assert!(one.clone() - &two == -one.clone());
    assert!(one.clone() * 2 == two);
    assert!(two.clone() / 2 == one);
  }
}
