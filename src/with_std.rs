//! Implementations for [NumMap] which require the `std` crate to be available.
//! 
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-05-06

use super::*;
pub use std::collections::{hash_map::RandomState, HashMap, HashSet,};

/// A map of numbers where all keys are considered mapped but 0 values are not stored.
pub struct NumMap<K, V, S = RandomState,>(pub(super) HashMap<K, V::NonZero, S>,)
  where V: Number;

impl<K, V,> NumMap<K, V, RandomState,>
  where K: Hash + Eq,
    V: Number, {
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
  /// ```
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
