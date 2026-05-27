use {
    super::double_endorsement_evidence::InlinedEndorsement,
    crate::models::operation::kind::OperationKind,
    crate::models::operation::metadata::Metadata,
    serde::{Deserialize, Serialize},
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DalEntrapmentEvidence {
    /// [OperationKind::DalEntrapmentEvidence]
    pub kind: OperationKind,
    pub attestation: InlinedEndorsement,
    pub consensus_slot: u16,
    pub slot_index: u8,
    pub shard_with_proof: ShardWithProof,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<Metadata>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ShardWithProof {
    pub shard: Shard,
    /// Base58Check-encoded BLS proof (`sh1...`).
    pub proof: String,
}

/// Wire form is a two-element JSON tuple `[index, [hex_byte_array, ...]]`.
pub type Shard = (i32, Vec<String>);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::operation::kind::OperationKind;

    const SAMPLE: &str =
        include_str!("../../../protocol_rpc/block/__TEST_DATA__/dal_entrapment_evidence.sample.json");

    #[test]
    fn test_deserialize() {
        let parsed: DalEntrapmentEvidence =
            serde_json::from_str(SAMPLE).expect("sample must deserialize");
        assert_eq!(parsed.kind, OperationKind::DalEntrapmentEvidence);
        assert_eq!(parsed.consensus_slot, 5);
        assert_eq!(parsed.slot_index, 15);
        assert_eq!(parsed.shard_with_proof.shard.0, 403);
        assert_eq!(parsed.shard_with_proof.shard.1.len(), 3);
        assert_eq!(
            parsed.attestation.operations.kind,
            OperationKind::AttestationWithDal,
        );
    }

    #[test]
    fn test_roundtrip_structural() {
        let original: serde_json::Value =
            serde_json::from_str(SAMPLE).expect("sample is valid JSON");
        let parsed: DalEntrapmentEvidence =
            serde_json::from_str(SAMPLE).expect("sample must deserialize");
        let reserialized =
            serde_json::to_value(&parsed).expect("must serialize back to JSON value");
        assert_eq!(reserialized, original);
    }
}
