//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-05-17

use super::*;
use std::collections::hash_map;

/// The Iterator which visits all non zero values in a [NumMap].
pub struct Iter<'a, K, V,>(pub(crate) Map<hash_map::Iter<'a, K, V::NonZero>, fn((&'a K, &'a V::NonZero,)) -> (&'a K, V,)>,)
  where V: Number;

impl<'a, K, V,> Iterator for Iter<'a, K, V,>
  where V: Number, {
  type Item = (&'a K, V,);

  #[inline]
  fn size_hint(&self,) -> (usize, Option<usize>,) { self.0.size_hint() }
  #[inline]
  fn next(&mut self,) -> Option<Self::Item> { self.0.next() }
}

/// The Iterator which visits all non zero values in a [NumMap].
pub struct Drain<'a, K, V,>(pub(crate) Map<hash_map::Drain<'a, K, V::NonZero>, fn((K, V::NonZero,)) -> (K, V,)>,)
  where V: Number;

impl<'a, K, V,> Iterator for Drain<'a, K, V,>
  where V: Number, {
  type Item = (K, V,);

  #[inline]
  fn size_hint(&self,) -> (usize, Option<usize>,) { self.0.size_hint() }
  #[inline]
  fn next(&mut self,) -> Option<Self::Item> { self.0.next() }
}

/// The IntoIterator type which visits all non zero values from a [NumMap].
pub struct IntoIter<K, V,>(pub(crate) Map<hash_map::IntoIter<K, V::NonZero>, fn((K, V::NonZero,)) -> (K, V,)>,)
  where V: Number;

impl<K, V,> Iterator for IntoIter<K, V,>
  where V: Number, {
  type Item = (K, V,);

  #[inline]
  fn size_hint(&self,) -> (usize, Option<usize>,) { self.0.size_hint() }
  #[inline]
  fn next(&mut self,) -> Option<Self::Item> { self.0.next() }
}
