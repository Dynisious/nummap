//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-03-30

use std::{num::*, ops::*, mem,};

/// A marker trait for types which have a [NonZero] equivilant.
pub trait Number: Add + AddAssign
  + Sub + SubAssign
  + Mul + MulAssign
  + Div + DivAssign
  + Eq + Ord
  + Copy + Sized {
  /// The [NonZero] equivilant.
  type NonZero: NonZero<Self>;

  /// The zero value of this type.
  const ZERO: Self;
}

impl Number for usize {
  type NonZero = NonZeroUsize;

  const ZERO: Self = 0;
}

impl Number for u8 {
  type NonZero = NonZeroU8;

  const ZERO: Self = 0;
}

impl Number for u16 {
  type NonZero = NonZeroU16;

  const ZERO: Self = 0;
}

impl Number for u32 {
  type NonZero = NonZeroU32;

  const ZERO: Self = 0;
}

impl Number for u64 {
  type NonZero = NonZeroU64;

  const ZERO: Self = 0;
}

impl Number for u128 {
  type NonZero = NonZeroU128;

  const ZERO: Self = 0;
}

impl Number for isize {
  type NonZero = NonZeroUsize;

  const ZERO: Self = 0;
}

impl Number for i8 {
  type NonZero = NonZeroU8;

  const ZERO: Self = 0;
}

impl Number for i16 {
  type NonZero = NonZeroU16;

  const ZERO: Self = 0;
}

impl Number for i32 {
  type NonZero = NonZeroU32;

  const ZERO: Self = 0;
}

impl Number for i64 {
  type NonZero = NonZeroU64;

  const ZERO: Self = 0;
}

impl Number for i128 {
  type NonZero = NonZeroU128;

  const ZERO: Self = 0;
}

/// A marker trait for types which have are `NonZero` numbers.
pub trait NonZero<Num,>: Eq + Ord + Copy + Sized
  where Num: Number, {
  /// Constructs a new value returning `None` for `0`.
  fn new(num: Num,) -> Option<Self>;
  /// Gets the inner value.
  fn get(self,) -> Num;
}

impl NonZero<usize> for NonZeroUsize {
  #[inline]
  fn new(num: usize,) -> Option<Self> { Self::new(num,) }
  #[inline]
  fn get(self,) -> usize { Self::get(self,) }
}

impl NonZero<u8> for NonZeroU8 {
  #[inline]
  fn new(num: u8,) -> Option<Self> { Self::new(num,) }
  #[inline]
  fn get(self,) -> u8 { Self::get(self,) }
}

impl NonZero<u16> for NonZeroU16 {
  #[inline]
  fn new(num: u16,) -> Option<Self> { Self::new(num,) }
  #[inline]
  fn get(self,) -> u16 { Self::get(self,) }
}

impl NonZero<u32> for NonZeroU32 {
  #[inline]
  fn new(num: u32,) -> Option<Self> { Self::new(num,) }
  #[inline]
  fn get(self,) -> u32 { Self::get(self,) }
}

impl NonZero<u64> for NonZeroU64 {
  #[inline]
  fn new(num: u64,) -> Option<Self> { Self::new(num,) }
  #[inline]
  fn get(self,) -> u64 { Self::get(self,) }
}

impl NonZero<u128> for NonZeroU128 {
  #[inline]
  fn new(num: u128,) -> Option<Self> { Self::new(num,) }
  #[inline]
  fn get(self,) -> u128 { Self::get(self,) }
}

impl NonZero<isize> for NonZeroUsize {
  #[inline]
  fn new(num: isize,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  fn get(self,) -> isize { unsafe { mem::transmute(Self::get(self,),) } }
}

impl NonZero<i8> for NonZeroU8 {
  #[inline]
  fn new(num: i8,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  fn get(self,) -> i8 { unsafe { mem::transmute(Self::get(self,),) } }
}

impl NonZero<i16> for NonZeroU16 {
  #[inline]
  fn new(num: i16,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  fn get(self,) -> i16 { unsafe { mem::transmute(Self::get(self,),) } }
}

impl NonZero<i32> for NonZeroU32 {
  #[inline]
  fn new(num: i32,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  fn get(self,) -> i32 { unsafe { mem::transmute(Self::get(self,),) } }
}

impl NonZero<i64> for NonZeroU64 {
  #[inline]
  fn new(num: i64,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  fn get(self,) -> i64 { unsafe { mem::transmute(Self::get(self,),) } }
}

impl NonZero<i128> for NonZeroU128 {
  #[inline]
  fn new(num: i128,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  fn get(self,) -> i128 { unsafe { mem::transmute(Self::get(self,),) } }
}

#[cfg(test,)]
mod tests {
  use super::*;

  #[test]
  fn test_i32_number() {
    /*Just a test that the `NonZero` implementations for i32
    (and assumingly other i-types) work as expected.
    */

    let two = <NonZeroU32 as NonZero<i32>>::new(2,);
    let neg_two = <NonZeroU32 as NonZero<i32>>::new(-2,);

    assert_eq!(two, NonZero::new(2u32,),);
    assert_eq!(neg_two, NonZero::new(std::u32::MAX - 1,),);
    
    let two = two.unwrap();
    let neg_two = neg_two.unwrap();

    assert_eq!(<NonZeroU32 as NonZero<i32>>::get(two,), 2i32,);
    assert_eq!(<NonZeroU32 as NonZero<i32>>::get(neg_two,), -2,);
  }
}