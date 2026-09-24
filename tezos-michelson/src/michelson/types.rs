mod comparables;
mod macros;

use macros::{make_type, make_types};
use tezos_core::internal::normalizer::Normalizer;

use super::Michelson;
use crate::{internal::normalizer::MichelsonNormalizer, Error, Result};
pub use comparables::{
    option as comparable_option, or as comparable_or, pair as comparable_pair,
    Option as ComparableOption, Or as ComparableOr, Pair as ComparablePair,
    Primitive as ComparableTypePrimitive, Type as ComparableType, *,
};

make_types!(
    type_enum: Comparable(crate::michelson::types::ComparableType),
    [
        pub fn is_valid_prim_name(name: &str) -> bool {
            let primitive = name.parse::<Primitive>();
            if primitive.is_err() {
                return name.parse::<comparables::Primitive>().is_ok();
            }
            primitive.is_ok()
        }

        fn fallback(value: PrimitiveApplication) -> Result<Self> {
            Ok(Self::Comparable(value.try_into()?))
        }
    ],
    conversion_fallback: fallback,
    (Parameter, parameter, boxed: (r#type: Type)),
    (Storage, storage, boxed: (r#type: Type)),
    (
        Code,
        code,
        boxed: (code: crate::michelson::data::instructions::Instruction)
    ),
    (Option, option, boxed: (r#type: Type)),
    (List, list, boxed: (r#type: Type)),
    (Set, set, boxed: (r#type: Type)),
    (Operation, operation),
    (Contract, contract, boxed: (r#type: Type)),
    (Ticket, ticket, boxed: (r#type: Type)),
    (Pair, pair, vec: (types: Type)),
    (Or, or, boxed: (lhs: Type), boxed: (rhs: Type)),
    (
        Lambda,
        lambda,
        boxed: (parameter_type: Type),
        boxed: (return_type: Type)
    ),
    (
        Map,
        map,
        boxed: (key_type: Type),
        boxed: (value_type: Type)
    ),
    (
        BigMap,
        big_map,
        boxed: (key_type: Type),
        boxed: (value_type: Type)
    ),
    (Bls12_381G1, bls12_381_g1),
    (Bls12_381G2, bls12_381_g2),
    (Bls12_381Fr, bls12_381_fr),
    (
        SaplingTransaction,
        sapling_transaction,
        (memo_size: crate::michelson::data::Nat)
    ),
    (
        SaplingState,
        sapling_state,
        (memo_size: crate::michelson::data::Nat)
    ),
    (Chest, chest),
    (ChestKey, chest_key),
);

impl Type {
    pub fn normalized(self) -> Self {
        MichelsonNormalizer::normalize(self)
    }
}

impl From<Type> for Michelson {
    fn from(value: Type) -> Self {
        Self::Type(value)
    }
}

impl TryFrom<Michelson> for Type {
    type Error = Error;

    fn try_from(value: Michelson) -> Result<Self> {
        if let Michelson::Type(value) = value {
            return Ok(value);
        }
        Err(Error::InvalidMichelson)
    }
}

impl From<Primitive> for crate::michelson::Primitive {
    fn from(value: Primitive) -> Self {
        Self::Type(value)
    }
}
