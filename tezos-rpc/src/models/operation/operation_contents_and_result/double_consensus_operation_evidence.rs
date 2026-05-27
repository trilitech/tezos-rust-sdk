use {
    super::double_endorsement_evidence::InlinedEndorsement,
    crate::models::operation::kind::OperationKind,
    crate::models::operation::metadata::Metadata,
    serde::{Deserialize, Serialize},
};

/// Tallinn (proto 024) unifies `double_endorsement_evidence` and
/// `double_preendorsement_evidence` into a single operation. The inlined ops
/// reuse [InlinedEndorsement] because both attestation and preattestation
/// payloads have the same JSON shape inside the evidence.
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DoubleConsensusOperationEvidence {
    /// [OperationKind::DoubleConsensusOperationEvidence]
    pub kind: OperationKind,
    pub slot: u16,
    pub op1: InlinedEndorsement,
    pub op2: InlinedEndorsement,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<Metadata>,
}
