// SPDX-License-Identifier: CC0-1.0

//! SHA256t implementation (tagged SHA256).
//!

use core::marker::PhantomData;
use core::ops::Index;
use core::slice::SliceIndex;
use core::cmp;

use crate::{sha256, FromSliceError};

type HashEngine = sha256::HashEngine;

/// Trait representing a tag that can be used as a context for SHA256t hashes.
pub trait Tag {
    /// Returns a hash engine that is pre-tagged and is ready to be used for the data.
    fn engine() -> sha256::HashEngine;
}

/// Output of the SHA256t hash function.
#[repr(transparent)]
pub struct Hash<T: Tag>([u8; 32], PhantomData<T>);

#[cfg(feature = "schemars")]
impl<T: Tag> schemars::JsonSchema for Hash<T> {
    fn schema_name() -> String { "Hash".to_owned() }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        let mut schema: schemars::schema::SchemaObject = <String>::json_schema(gen).into();
        schema.string = Some(Box::new(schemars::schema::StringValidation {
            max_length: Some(32 * 2),
            min_length: Some(32 * 2),
            pattern: Some("[0-9a-fA-F]+".to_owned()),
        }));
        schema.into()
    }
}

impl<T: Tag> Hash<T> {
    fn internal_new(arr: [u8; 32]) -> Self { Hash(arr, Default::default()) }

    fn internal_engine() -> HashEngine { T::engine() }
}

impl<T: Tag> Copy for Hash<T> {}
impl<T: Tag> Clone for Hash<T> {
    fn clone(&self) -> Self { *self }
}
impl<T: Tag> PartialEq for Hash<T> {
    fn eq(&self, other: &Hash<T>) -> bool { self.0 == other.0 }
}
impl<T: Tag> Eq for Hash<T> {}
impl<T: Tag> Default for Hash<T> {
    fn default() -> Self { Hash([0; 32], PhantomData) }
}
impl<T: Tag> PartialOrd for Hash<T> {
    fn partial_cmp(&self, other: &Hash<T>) -> Option<cmp::Ordering> {
        Some(cmp::Ord::cmp(self, other))
    }
}
impl<T: Tag> Ord for Hash<T> {
    fn cmp(&self, other: &Hash<T>) -> cmp::Ordering { cmp::Ord::cmp(&self.0, &other.0) }
}
impl<T: Tag> core::hash::Hash for Hash<T> {
    fn hash<H: core::hash::Hasher>(&self, h: &mut H) { self.0.hash(h) }
}

crate::internal_macros::hash_trait_impls!(256, true, T: Tag);

fn from_engine<T: Tag>(e: sha256::HashEngine) -> Hash<T> {
    use crate::Hash as _;

    Hash::from_byte_array(sha256::Hash::from_engine(e).to_byte_array())
}

/// Macro used to define a newtype tagged hash.
///
/// This macro creates two types:
///
/// * a tag struct
/// * a hash wrapper
///
/// The syntax is:
///
/// ```
/// # use bitcoin_hashes::sha256t_hash_newtype;
/// sha256t_hash_newtype! {
///     /// Optional documentation details here.
///     /// Summary is always generated.
///     pub struct FooTag = hash_str("foo");
///
///     /// A foo hash.
///     // Direction works just like in case of hash_newtype! macro.
///     #[hash_newtype(forward)]
///     pub struct FooHash(_);
/// }
/// ```
///
/// The structs must be defined in this order - tag first, then hash type. `hash_str` marker
/// says the midstate should be generated by hashing the supplied string in a way described in
/// BIP-341. Alternatively, you can supply `hash_bytes` to hash raw bytes. If you have the midstate
/// already pre-computed and prefer **compiler** performance to readability you may use
/// `raw(MIDSTATE_BYTES, HASHED_BYTES_LENGTH)` instead.
///
/// Both visibility modifiers and attributes are optional and passed to inner structs (excluding
/// `#[hash_newtype(...)]`). The attributes suffer same compiler performance limitations as in
/// [`hash_newtype`] macro.
///
/// The macro accepts multiple inputs so you can define multiple hash newtypes in one macro call.
/// Just make sure to enter the structs in order `Tag0`, `Hash0`, `Tag1`, `Hash1`...
///
/// [`hash_newtype`]: crate::hash_newtype
#[macro_export]
macro_rules! sha256t_hash_newtype {
    ($($(#[$($tag_attr:tt)*])* $tag_vis:vis struct $tag:ident = $constructor:tt($($tag_value:tt)+); $(#[$($hash_attr:tt)*])* $hash_vis:vis struct $hash_name:ident($(#[$($field_attr:tt)*])* _);)+) => {
        $(
        $crate::sha256t_hash_newtype_tag!($tag_vis, $tag, stringify!($hash_name), $(#[$($tag_attr)*])*);

        impl $crate::sha256t::Tag for $tag {
            #[inline]
            fn engine() -> $crate::sha256::HashEngine {
                const MIDSTATE: ($crate::sha256::Midstate, usize) = $crate::sha256t_hash_newtype_tag_constructor!($constructor, $($tag_value)+);
                #[allow(unused)]
                const _LENGTH_CHECK: () = [(); 1][MIDSTATE.1 % 64];
                $crate::sha256::HashEngine::from_midstate(MIDSTATE.0, MIDSTATE.1)
            }
        }

        $crate::hash_newtype! {
            $(#[$($hash_attr)*])*
            $hash_vis struct $hash_name($(#[$($field_attr)*])* $crate::sha256t::Hash<$tag>);
        }
        )+
    }
}

// Workaround macros being unavailable in attributes.
#[doc(hidden)]
#[macro_export]
macro_rules! sha256t_hash_newtype_tag {
    ($vis:vis, $tag:ident, $name:expr, $(#[$($attr:meta)*])*) => {
        #[doc = "The tag used for [`"]
        #[doc = $name]
        #[doc = "`]\n\n"]
        $(#[$($attr)*])*
        #[derive(Copy, Clone, PartialEq, Eq, Default, PartialOrd, Ord, Hash)]
        $vis struct $tag;
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! sha256t_hash_newtype_tag_constructor {
    (hash_str, $value:expr) => {
        ($crate::sha256::Midstate::hash_tag($value.as_bytes()), 64)
    };
    (hash_bytes, $value:expr) => {
        ($crate::sha256::Midstate::hash_tag($value), 64)
    };
    (raw, $bytes:expr, $len:expr) => {
        ($crate::sha256::Midstate::from_byte_array($bytes), $len)
    };
}

#[cfg(test)]
mod tests {
    use crate::{sha256, sha256t};

    const TEST_MIDSTATE: [u8; 32] = [
        156, 224, 228, 230, 124, 17, 108, 57, 56, 179, 202, 242, 195, 15, 80, 137, 211, 243, 147,
        108, 71, 99, 110, 96, 125, 179, 62, 234, 221, 198, 240, 201,
    ];

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
    pub struct TestHashTag;

    impl sha256t::Tag for TestHashTag {
        fn engine() -> sha256::HashEngine {
            // The TapRoot TapLeaf midstate.
            let midstate = sha256::Midstate::from_byte_array(TEST_MIDSTATE);
            sha256::HashEngine::from_midstate(midstate, 64)
        }
    }

    #[cfg(feature = "schemars")]
    impl schemars::JsonSchema for TestHashTag {
        fn schema_name() -> String { "Hash".to_owned() }

        fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
            let mut schema: schemars::schema::SchemaObject = <String>::json_schema(gen).into();
            schema.string = Some(Box::new(schemars::schema::StringValidation {
                max_length: Some(64 * 2),
                min_length: Some(64 * 2),
                pattern: Some("[0-9a-fA-F]+".to_owned()),
            }));
            schema.into()
        }
    }

    /// A hash tagged with `$name`.
    #[cfg(all(feature = "alloc", feature = "hex"))]
    pub type TestHash = sha256t::Hash<TestHashTag>;

    sha256t_hash_newtype! {
        /// Test detailed explanation.
        struct NewTypeTag = raw(TEST_MIDSTATE, 64);

        /// A test hash.
        #[hash_newtype(backward)]
        struct NewTypeHash(_);
    }

    #[test]
    #[cfg(all(feature = "alloc", feature = "hex"))]
    fn test_sha256t() {
        use crate::Hash;

        assert_eq!(
            TestHash::hash(&[0]).to_string(),
            "29589d5122ec666ab5b4695070b6debc63881a4f85d88d93ddc90078038213ed"
        );
        assert_eq!(
            NewTypeHash::hash(&[0]).to_string(),
            "29589d5122ec666ab5b4695070b6debc63881a4f85d88d93ddc90078038213ed"
        );
    }

    // This test verifies that the `sha256t_hash_newtype` macro implements `FromStr`.
    #[test]
    #[cfg(feature = "hex-std")]
    fn parse_hex() {
        use crate::Hash;

        let hex = "29589d5122ec666ab5b4695070b6debc63881a4f85d88d93ddc90078038213ed";
        let want = TestHash::hash(&[0]);
        let got = hex.parse::<TestHash>().expect("failed to parse hex");
        assert_eq!(got, want)
    }
}
