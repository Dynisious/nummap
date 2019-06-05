//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-05-06

use super::*;

/// A marker trait for types which are `NonZero` numbers.
pub trait NonZero<Num,>: ToNumber<Num,> + Copy + Sized
  where Num: Number, {
  /// The optional equivelant of this
  type Optional: ToNumber<Num,> = Option<Self>;

  /// Constructs a new value returning `None` for `0`.
  fn new(num: Num,) -> Option<Self>;
  /// Constructs a new value assuming it is not `0`.
  unsafe fn new_unchecked(num: Num,) -> Self;
}

impl NonZero<usize> for NonZeroUsize {
  #[inline]
  fn new(num: usize,) -> Option<Self> { Self::new(num,) }
  #[inline]
  unsafe fn new_unchecked(num: usize,) -> Self { Self::new_unchecked(num,) }
}

impl NonZero<u8> for NonZeroU8 {
  #[inline]
  fn new(num: u8,) -> Option<Self> { Self::new(num,) }
  #[inline]
  unsafe fn new_unchecked(num: u8,) -> Self { Self::new_unchecked(num,) }
}

impl NonZero<u16> for NonZeroU16 {
  #[inline]
  fn new(num: u16,) -> Option<Self> { Self::new(num,) }
  #[inline]
  unsafe fn new_unchecked(num: u16,) -> Self { Self::new_unchecked(num,) }
}

impl NonZero<u32> for NonZeroU32 {
  #[inline]
  fn new(num: u32,) -> Option<Self> { Self::new(num,) }
  #[inline]
  unsafe fn new_unchecked(num: u32,) -> Self { Self::new_unchecked(num,) }
}

impl NonZero<u64> for NonZeroU64 {
  #[inline]
  fn new(num: u64,) -> Option<Self> { Self::new(num,) }
  #[inline]
  unsafe fn new_unchecked(num: u64,) -> Self { Self::new_unchecked(num,) }
}

impl NonZero<u128> for NonZeroU128 {
  #[inline]
  fn new(num: u128,) -> Option<Self> { Self::new(num,) }
  #[inline]
  unsafe fn new_unchecked(num: u128,) -> Self { Self::new_unchecked(num,) }
}

impl NonZero<isize> for NonZeroIsize {
  #[inline]
  fn new(num: isize,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: isize,) -> Self { mem::transmute(num,) }
}

impl NonZero<i8> for NonZeroI8 {
  #[inline]
  fn new(num: i8,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: i8,) -> Self { mem::transmute(num,) }
}

impl NonZero<i16> for NonZeroI16 {
  #[inline]
  fn new(num: i16,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: i16,) -> Self { mem::transmute(num,) }
}

impl NonZero<i32> for NonZeroI32 {
  #[inline]
  fn new(num: i32,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: i32,) -> Self { mem::transmute(num,) }
}

impl NonZero<i64> for NonZeroI64 {
  #[inline]
  fn new(num: i64,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: i64,) -> Self { mem::transmute(num,) }
}

impl NonZero<i128> for NonZeroI128 {
  #[inline]
  fn new(num: i128,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: i128,) -> Self { mem::transmute(num,) }
}

impl NonZero<f32> for NonZeroU32 {
  #[inline]
  fn new(num: f32,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: f32,) -> Self { mem::transmute(num,) }
}

impl NonZero<f64> for NonZeroU64 {
  #[inline]
  fn new(num: f64,) -> Option<Self> { Self::new(unsafe { mem::transmute(num,) },) }
  #[inline]
  unsafe fn new_unchecked(num: f64,) -> Self { mem::transmute(num,) }
}
