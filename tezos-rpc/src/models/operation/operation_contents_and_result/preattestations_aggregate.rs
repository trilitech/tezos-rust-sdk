use {
    super::attestations_aggregate::{AggregateConsensusContent, AttestationsAggregateMetadata},
    crate::models::operation::kind::OperationKind,
    serde::{Deserialize, Serialize},
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct PreattestationsAggregate {
    /// [OperationKind::PreattestationsAggregate]
    pub kind: OperationKind,
    pub consensus_content: AggregateConsensusContent,
    /// Preattestations don't carry DAL state, so the committee is just slots.
    pub committee: Vec<u16>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<AttestationsAggregateMetadata>,
}
