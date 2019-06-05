//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-05-06

use super::*;

/// A type which can be converted to a [Number].
pub trait ToNumber<Num,>: Copy + Sized
  where Num: Number, {
  /// Converts a value to a [Number].
  fn as_num(self,) -> Num;
}

impl ToNumber<usize,> for usize {
  #[inline]
  fn as_num(self,) -> usize { self }
}

impl ToNumber<u8,> for u8 {
  #[inline]
  fn as_num(self,) -> u8 { self }
}

impl ToNumber<u16,> for u16 {
  #[inline]
  fn as_num(self,) -> u16 { self }
}

impl ToNumber<u32,> for u32 {
  #[inline]
  fn as_num(self,) -> u32 { self }
}

impl ToNumber<u64,> for u64 {
  #[inline]
  fn as_num(self,) -> u64 { self }
}

impl ToNumber<u128,> for u128 {
  #[inline]
  fn as_num(self,) -> u128 { self }
}

impl ToNumber<isize,> for isize {
  #[inline]
  fn as_num(self,) -> isize { self }
}

impl ToNumber<i8,> for i8 {
  #[inline]
  fn as_num(self,) -> i8 { self }
}

impl ToNumber<i16,> for i16 {
  #[inline]
  fn as_num(self,) -> i16 { self }
}

impl ToNumber<i32,> for i32 {
  #[inline]
  fn as_num(self,) -> i32 { self }
}

impl ToNumber<i64,> for i64 {
  #[inline]
  fn as_num(self,) -> i64 { self }
}

impl ToNumber<i128,> for i128 {
  #[inline]
  fn as_num(self,) -> i128 { self }
}

impl ToNumber<f32,> for f32 {
  #[inline]
  fn as_num(self,) -> f32 { self }
}

impl ToNumber<f64,> for f64 {
  #[inline]
  fn as_num(self,) -> f64 { self }
}

impl ToNumber<usize,> for NonZeroUsize {
  #[inline]
  fn as_num(self,) -> usize { self.get() }
}

impl ToNumber<u8,> for NonZeroU8 {
  #[inline]
  fn as_num(self,) -> u8 { self.get() }
}

impl ToNumber<u16,> for NonZeroU16 {
  #[inline]
  fn as_num(self,) -> u16 { self.get() }
}

impl ToNumber<u32,> for NonZeroU32 {
  #[inline]
  fn as_num(self,) -> u32 { self.get() }
}

impl ToNumber<u64,> for NonZeroU64 {
  #[inline]
  fn as_num(self,) -> u64 { self.get() }
}

impl ToNumber<u128,> for NonZeroU128 {
  #[inline]
  fn as_num(self,) -> u128 { self.get() }
}

impl ToNumber<isize,> for NonZeroIsize {
  #[inline]
  fn as_num(self,) -> isize { self.get() }
}

impl ToNumber<i8,> for NonZeroI8 {
  #[inline]
  fn as_num(self,) -> i8 { self.get() }
}

impl ToNumber<i16,> for NonZeroI16 {
  #[inline]
  fn as_num(self,) -> i16 { self.get() }
}

impl ToNumber<i32,> for NonZeroI32 {
  #[inline]
  fn as_num(self,) -> i32 { self.get() }
}

impl ToNumber<i64,> for NonZeroI64 {
  #[inline]
  fn as_num(self,) -> i64 { self.get() }
}

impl ToNumber<i128,> for NonZeroI128 {
  #[inline]
  fn as_num(self,) -> i128 { self.get() }
}

impl ToNumber<f32,> for NonZeroU32 {
  #[inline]
  fn as_num(self,) -> f32 { f32::from_bits(self.get(),) }
}

impl ToNumber<f64,> for NonZeroU64 {
  #[inline]
  fn as_num(self,) -> f64 { f64::from_bits(self.get(),) }
}

impl<N,> ToNumber<N,> for Option<NonZeroU8>
  where NonZeroU8: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroU8::as_num,).unwrap_or(N::ZERO,) }
}

impl<N,> ToNumber<N,> for Option<NonZeroU16>
  where NonZeroU16: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroU16::as_num,).unwrap_or(N::ZERO,) }
}

impl<N,> ToNumber<N,> for Option<NonZeroU32>
  where NonZeroU32: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroU32::as_num,).unwrap_or(N::ZERO,) }
}

impl<N,> ToNumber<N,> for Option<NonZeroU64>
  where NonZeroU64: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroU64::as_num,).unwrap_or(N::ZERO,) }
}

impl<N,> ToNumber<N,> for Option<NonZeroI8>
  where NonZeroI8: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroI8::as_num,).unwrap_or(N::ZERO,) }
}

impl<N,> ToNumber<N,> for Option<NonZeroI16>
  where NonZeroI16: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroI16::as_num,).unwrap_or(N::ZERO,) }
}

impl<N,> ToNumber<N,> for Option<NonZeroI32>
  where NonZeroI32: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroI32::as_num,).unwrap_or(N::ZERO,) }
}

impl<N,> ToNumber<N,> for Option<NonZeroI64>
  where NonZeroI64: ToNumber<N,>,
    N: Number, {
  #[inline]
  fn as_num(self,) -> N { self.map(NonZeroI64::as_num,).unwrap_or(N::ZERO,) }
}
