use crate::alloc::string::ToString;
use alloc::string::String;
use scale_info::TypeInfo;
use serde::{Deserialize, Serialize};
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{BlakeTwo256, Hash};
use scale_codec::{Decode, DecodeWithMemTracking, Encode};
use sp_std::prelude::*;

#[derive(
	Default, Deserialize, Serialize, Encode, Decode, Clone, Debug, PartialEq, Eq, TypeInfo,
)]

pub struct CustomEvent {
	pub id: u64,
	pub data: CustomData,
	pub timestamp: u64,
	pub block_height: u64,
	pub last_epoch: Option<u64>,
	pub last_blockhash: Option<String>,
	pub last_slot: Option<u64>,
	pub new_epoch: Option<u64>,
	pub new_slot: Option<u64>,
	pub new_blockhash: Option<String>,
	pub epoch_nonce: Option<String>,
	pub extra_entropy: Option<String>,
}

impl CustomEvent {
	pub fn is_valid(&self) -> bool {
		self.timestamp != 0 && self.block_height != 0
	}

	pub fn hash_without_timestamp(&self) -> [u8; 32] {
		let mut encoded_data = self.id.encode();
		encoded_data.extend(self.data.encode());
		encoded_data.extend(self.block_height.encode());
		BlakeTwo256::hash_of(&encoded_data).into()
	}

	pub fn hash(&self) -> [u8; 32] {
		let mut encoded_data = self.data.event_type.encode();
		encoded_data.extend(self.data.encode());
		blake2_256(&encoded_data)
	}
}
impl TryFrom<CustomEvent> for EpochChangeData {
	type Error = &'static str;

	fn try_from(custom_event: CustomEvent) -> Result<Self, Self::Error> {
		Ok(custom_event.data.data)
	}
}

#[derive(
	Default, Deserialize, Serialize, Encode, Decode, Clone, Debug, PartialEq, Eq, TypeInfo,
)]
pub struct CustomData {
	#[serde(rename = "type")]
	pub event_type: String,
	pub data: EpochChangeData,
}

impl CustomData {
	pub fn hash(&self) -> [u8; 32] {
		let mut encoded_data = self.event_type.encode();
		encoded_data.extend(self.data.encode());
		blake2_256(&encoded_data)
	}
}

#[derive(
	Default, Deserialize, Serialize, Encode, Decode, DecodeWithMemTracking, Clone, Debug, PartialEq, Eq, TypeInfo,
)]
pub struct EpochChangeData {
	pub last_epoch: u64,
	pub last_blockhash: String,
	pub last_slot: u64,
	pub new_epoch: u64,
	pub new_slot: u64,
	pub new_blockhash: String,
	pub epoch_nonce: String,
	pub extra_entropy: Option<String>,
}

impl EpochChangeData {
	pub fn hash(&self) -> [u8; 32] {
		let mut encoded_data = self.last_epoch.encode();
		encoded_data.extend(self.last_blockhash.encode());
		encoded_data.extend(self.last_slot.encode());
		encoded_data.extend(self.new_epoch.encode());
		encoded_data.extend(self.new_slot.encode());
		encoded_data.extend(self.new_blockhash.encode());
		encoded_data.extend(self.epoch_nonce.encode());

		if let Some(extra_entropy) = &self.extra_entropy {
			encoded_data.extend(extra_entropy.encode());
		}
		blake2_256(&encoded_data)
	}
	fn epoch_change_data_to_custom_event(
		epoch_change_data: &EpochChangeData,
		event_id: u64,
		timestamp: u64,
		block_height: u64,
	) -> CustomEvent {
		CustomEvent {
			id: event_id,
			data: CustomData {
				event_type: "EpochChange".to_string(),
				data: epoch_change_data.clone(),
			},
			timestamp,
			block_height,
			last_epoch: Some(epoch_change_data.last_epoch),
			last_blockhash: Some(epoch_change_data.last_blockhash.clone()),
			last_slot: Some(epoch_change_data.last_slot),
			new_epoch: Some(epoch_change_data.new_epoch),
			new_slot: Some(epoch_change_data.new_slot),
			new_blockhash: Some(epoch_change_data.new_blockhash.clone()),
			epoch_nonce: Some(epoch_change_data.epoch_nonce.clone()),
			extra_entropy: epoch_change_data.extra_entropy.clone(),
		}
	}
}
