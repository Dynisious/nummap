//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-05-07

#![cfg(feature = "serde",)]

use super::*;
use ::serde::{
  ser::{Serialize, Serializer, SerializeMap,},
  de::{self, Deserialize, Deserializer, MapAccess,},
};

impl<K, V, H,> Serialize for NumMap<K, V, H,>
  where K: Serialize,
    V: Number + Serialize, {
  fn serialize<S,>(&self, serializer: S,) -> Result<S::Ok, S::Error>
    where S: Serializer, {
    let mut serializer = serializer.serialize_map(Some(self.len()),)?;

    for (k, v,) in self {
      serializer.serialize_key(k,)?;
      serializer.serialize_value(&v,)?;
    }

    serializer.end()
  }
}

impl<'de, K, V, S,> Deserialize<'de,> for NumMap<K, V, S,>
  where K: Eq + Hash + Deserialize<'de>,
    V: Number + Deserialize<'de>,
    S: Default + BuildHasher,
    Option<V::NonZero>: ToNumber<V,>, {
  fn deserialize<D,>(deserializer: D,) -> Result<Self, D::Error>
    where D: Deserializer<'de>, {
    use core::marker::PhantomData;
    
    struct Visitor<K, V, S,>(PhantomData<(K, V, S,)>,);

    impl<'de, K, V, S,> de::Visitor<'de> for Visitor<K, V, S,>
      where K: Eq + Hash + Deserialize<'de>,
        V: Number + Deserialize<'de>,
        S: Default + BuildHasher,
        Option<V::NonZero>: ToNumber<V,>, {
      type Value = NumMap<K, V, S,>;

      #[inline]
      fn expecting(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
        fmt.write_str("a `NumMap`",)
      }
      fn visit_map<A,>(self, mut map: A,) -> Result<Self::Value, A::Error>
        where A: MapAccess<'de>, {
        let capactiy = map.size_hint().unwrap_or(0,);
        let mut num_map = NumMap::with_capacity_and_hasher(capactiy, S::default(),);

        loop {
          match map.next_entry()? {
            Some((k, v,)) => { num_map.set(k, v,); },
            None => break,
          }
        }

        Ok(num_map)
      }
    }

    deserializer.deserialize_map(Visitor(PhantomData,),)
  }
}

#[cfg(test,)]
mod tests {
  use super::*;

  #[test]
  fn test_nummap_serde() {
    let map = {
      let mut map = NumMap::new();

      map.set(0, 1,);
      map.set(2, 3,);
      map.set(4, 5,);

      map
    };
    let other = serde_cbor::to_vec(&map,)
      .expect("Error serialising the `NumMap`");
    let other = serde_cbor::from_slice::<NumMap<u32, u32,>>(&other,)
      .expect("Error deserialising the `NumMap`");
    
    assert_eq!(map, other, "`NumMap` corrupted during serde",);
  }
}
