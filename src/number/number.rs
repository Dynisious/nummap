//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-05-06

use super::*;

/// A marker trait for types which have a [NonZero] equivilant.
pub trait Number: Copy + Sized {
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
  type NonZero = NonZeroIsize;

  const ZERO: Self = 0;
}

impl Number for i8 {
  type NonZero = NonZeroI8;

  const ZERO: Self = 0;
}

impl Number for i16 {
  type NonZero = NonZeroI16;

  const ZERO: Self = 0;
}

impl Number for i32 {
  type NonZero = NonZeroI32;

  const ZERO: Self = 0;
}

impl Number for i64 {
  type NonZero = NonZeroI64;

  const ZERO: Self = 0;
}

impl Number for i128 {
  type NonZero = NonZeroI128;

  const ZERO: Self = 0;
}

impl Number for f32 {
  type NonZero = NonZeroU32;

  const ZERO: Self = 0.0;
}

impl Number for f64 {
  type NonZero = NonZeroU64;

  const ZERO: Self = 0.0;
}
