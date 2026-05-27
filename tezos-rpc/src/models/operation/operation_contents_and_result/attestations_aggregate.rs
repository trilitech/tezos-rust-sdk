use {
    crate::models::balance_update::BalanceUpdate,
    crate::models::operation::kind::OperationKind,
    crate::models::operation::operation_contents_and_result::endorsement::ConsensusPower,
    serde::{Deserialize, Serialize},
    tezos_core::types::encoded::{BlockPayloadHash, ImplicitAddress},
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub balance_updates: Option<Vec<BalanceUpdate>>,
    pub committee: Vec<CommitteeMember>,
    pub total_consensus_power: ConsensusPower,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct CommitteeMember {
    pub delegate: ImplicitAddress,
    pub consensus_pkh: ImplicitAddress,
    pub consensus_power: ConsensusPower,
}
