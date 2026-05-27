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

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> serde_json::Value {
        serde_json::json!({
            "kind": "double_consensus_operation_evidence",
            "slot": 17,
            "op1": {
                "branch": "BMLJapq1nxNo67Cak9nyU9p6EZ8DGK5NFjc4nVQYXwhHdmapAz7",
                "operations": {
                    "kind": "attestation",
                    "slot": 17,
                    "level": 1839178,
                    "round": 0,
                    "block_payload_hash": "vh1he5NXZcwZmGe3cGdepQU83C6Qky7m1tWJsShNnjT7amg8X7Jy"
                },
                "signature": "sigrP9miXpMmFZpn8TbAy1j8RPFTvrzLHDE6ZtrFCQ4q7E1dzRomHXxca8SAtXtdj95s5CcZhMvm1nYQBQgcAxu7JGgiof5N"
            },
            "op2": {
                "branch": "BMLJapq1nxNo67Cak9nyU9p6EZ8DGK5NFjc4nVQYXwhHdmapAz7",
                "operations": {
                    "kind": "attestation",
                    "slot": 17,
                    "level": 1839178,
                    "round": 0,
                    "block_payload_hash": "vh2MGrBpkc1cEPmuJxFLDpkkvmgaJk2WonZ55EhJgmRBxApxJtPS"
                },
                "signature": "sigrP9miXpMmFZpn8TbAy1j8RPFTvrzLHDE6ZtrFCQ4q7E1dzRomHXxca8SAtXtdj95s5CcZhMvm1nYQBQgcAxu7JGgiof5N"
            }
        })
    }

    #[test]
    fn test_deserialize() {
        let parsed: DoubleConsensusOperationEvidence =
            serde_json::from_value(sample()).expect("sample must deserialize");
        assert_eq!(parsed.kind, OperationKind::DoubleConsensusOperationEvidence);
        assert_eq!(parsed.slot, 17);
        assert_eq!(parsed.op1.operations.kind, OperationKind::Attestation);
        assert_eq!(parsed.op2.operations.kind, OperationKind::Attestation);
    }

    #[test]
    fn test_roundtrip_structural() {
        let original = sample();
        let parsed: DoubleConsensusOperationEvidence =
            serde_json::from_value(original.clone()).expect("sample must deserialize");
        let reserialized =
            serde_json::to_value(&parsed).expect("must serialize back to JSON value");
        assert_eq!(reserialized, original);
    }
}
