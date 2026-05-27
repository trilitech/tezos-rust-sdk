use {
    crate::models::balance_update::BalanceUpdate,
    crate::models::operation::kind::OperationKind,
    crate::models::operation::operation_result::OperationResultStatus,
    serde::{Deserialize, Serialize},
    tezos_core::types::{encoded::ImplicitAddress, mutez::Mutez},
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DalPublishCommitment {
    /// [OperationKind::DalPublishCommitment]
    pub kind: OperationKind,
    pub source: ImplicitAddress,
    pub fee: Mutez,
    pub counter: String,
    pub gas_limit: String,
    pub storage_limit: String,
    pub slot_header: SlotHeader,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<DalPublishCommitmentMetadata>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SlotHeader {
    pub slot_index: u8,
    /// Base58Check-encoded DAL commitment (`sh...`).
    pub commitment: String,
    /// Hex-encoded commitment proof.
    pub commitment_proof: String,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DalPublishCommitmentMetadata {
    #[serde(default)]
    pub balance_updates: Vec<BalanceUpdate>,
    pub operation_result: DalPublishCommitmentResult,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DalPublishCommitmentResult {
    pub status: OperationResultStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slot_header: Option<PublishedSlotHeader>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub consumed_milligas: Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct PublishedSlotHeader {
    pub version: String,
    pub level: i32,
    pub index: u8,
    pub commitment: String,
}
