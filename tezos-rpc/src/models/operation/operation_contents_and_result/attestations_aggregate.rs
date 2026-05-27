use {
    crate::models::balance_update::BalanceUpdate,
    crate::models::operation::kind::OperationKind,
    crate::models::operation::operation_contents_and_result::endorsement::ConsensusPower,
    serde::{Deserialize, Serialize},
    tezos_core::types::encoded::{BlockPayloadHash, ImplicitAddress, PublicKey},
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct AttestationsAggregate {
    /// [OperationKind::AttestationsAggregate]
    pub kind: OperationKind,
    pub consensus_content: AggregateConsensusContent,
    pub committee: Vec<CommitteeSlot>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<AttestationsAggregateMetadata>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct AggregateConsensusContent {
    pub level: i32,
    pub round: i32,
    pub block_payload_hash: BlockPayloadHash,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct CommitteeSlot {
    pub slot: u16,
    /// Present iff the committee member also attested on the DAL for this slot.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dal_attestation: Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct AttestationsAggregateMetadata {
    #[serde(default)]
    pub balance_updates: Vec<BalanceUpdate>,
    pub committee: Vec<CommitteeMember>,
    pub total_consensus_power: ConsensusPower,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct CommitteeMember {
    pub delegate: ImplicitAddress,
    /// Either a public key hash (e.g. `tz4...`) or a full public key. Modeled
    /// loosely because Tallinn-era RPCs vary across this field.
    pub consensus_pkh: ConsensusPkh,
    pub consensus_power: ConsensusPower,
}

/// `consensus_pkh` in Tallinn metadata can be either a public key hash or a
/// full public key depending on the consensus algorithm; accept both.
#[derive(Debug, Serialize, Deserialize, Clone)]
#[serde(untagged)]
pub enum ConsensusPkh {
    Hash(ImplicitAddress),
    Key(PublicKey),
    Raw(String),
}
