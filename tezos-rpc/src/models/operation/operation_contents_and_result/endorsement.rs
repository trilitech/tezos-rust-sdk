use tezos_core::types::encoded::{BlockPayloadHash, ImplicitAddress};

use crate::{Error, Result};

use {
    crate::models::balance_update::BalanceUpdate,
    crate::models::operation::kind::OperationKind,
    serde::{Deserialize, Serialize},
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Endorsement {
    /// [OperationKind::Endorsement] or [OperationKind::AttestationWithDal]
    pub kind: OperationKind,
    /// integer ∈ [-2^31-1, 2^31]
    pub level: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<EndorsementMetadata>,
    /// integer ∈ [0, 2^16-1]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slot: Option<u16>,
    /// integer ∈ [-2^31-1, 2^31]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub round: Option<i32>,
    /// Hash of a consensus value (Base58Check-encoded)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub block_payload_hash: Option<BlockPayloadHash>,
    /// Present only when kind is `attestation_with_dal`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dal_attestation: Option<String>,
}

impl From<tezos_operation::operations::Endorsement> for Endorsement {
    fn from(value: tezos_operation::operations::Endorsement) -> Self {
        Self {
            kind: OperationKind::Endorsement,
            level: Some(value.level),
            metadata: None,
            slot: Some(value.slot),
            round: Some(value.round),
            block_payload_hash: Some(value.block_payload_hash),
            dal_attestation: None,
        }
    }
}

impl TryFrom<Endorsement> for tezos_operation::operations::Endorsement {
    type Error = Error;

    fn try_from(value: Endorsement) -> Result<Self> {
        Ok(Self {
            slot: value.slot.ok_or(Error::InvalidConversion)?,
            level: value.level.ok_or(Error::InvalidConversion)?,
            round: value.round.ok_or(Error::InvalidConversion)?,
            block_payload_hash: value.block_payload_hash.ok_or(Error::InvalidConversion)?,
        })
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct EndorsementMetadata {
    /// Public key hash (Base58Check-encoded)
    pub delegate: ImplicitAddress,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub balance_updates: Option<Vec<BalanceUpdate>>,
    /// Pre-Tallinn protocols expose attesting weight as a single integer.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub endorsement_power: Option<i32>,
    /// From Tallinn onward, attesting weight is `{slots, baking_power}`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub consensus_power: Option<ConsensusPower>,
    /// Consensus key of the delegate (added in Tallinn protocol).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub consensus_key: Option<ImplicitAddress>,
    /// Legacy field (used in old protocols)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slots: Option<Vec<u16>>,
}

/// The result-side counterpart of [Attesting_power.t]: `slots` plus an
/// optional `baking_power` (only populated once "all bakers attest" is active).
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct ConsensusPower {
    pub slots: i32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub baking_power: Option<String>,
}
