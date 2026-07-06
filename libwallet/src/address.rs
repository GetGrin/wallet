// Copyright 2021 The Grin Develope;
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Functions defining wallet 'addresses', i.e. ed2559 keys based on
//! a derivation path

use crate::grin_util::secp::key::SecretKey;
use crate::Error;
use ed25519_dalek::PublicKey as DalekPublicKey;
use ed25519_dalek::SecretKey as DalekSecretKey;
use grin_keychain::{ChildNumber, Identifier, Keychain, SwitchCommitmentType};

use crate::blake2::blake2b::blake2b;

/// Highest proof-address derivation index the RECEIVE path scans when
/// detecting which of this wallet's addresses a payment-proof slate is
/// addressed to. Per-offer address minting (the app-side allocator) must stay
/// at or below this bound, or the receive side could not find the matching
/// signing key and the proof would fail the sender's finalize-time check.
pub const MAX_PROOF_ADDRESS_INDEX: u32 = 1023;

/// Derive a secret key given a derivation path and index
pub fn address_from_derivation_path<K>(
	keychain: &K,
	parent_key_id: &Identifier,
	index: u32,
) -> Result<SecretKey, Error>
where
	K: Keychain,
{
	let mut key_path = parent_key_id.to_path();
	// An output derivation for acct m/0
	// is m/0/0/0, m/0/0/1 (for instance), m/1 is m/1/0/0, m/1/0/1
	// Address generation path should be
	// for m/0: m/0/1/0, m/0/1/1
	// for m/1: m/1/1/0, m/1/1/1
	key_path.path[1] = ChildNumber::from(1);
	key_path.depth += 1;
	key_path.path[key_path.depth as usize - 1] = ChildNumber::from(index);
	let key_id = Identifier::from_path(&key_path);
	let sec_key = keychain.derive_key(0, &key_id, SwitchCommitmentType::None)?;
	let hashed = blake2b(32, &[], &sec_key.0[..]);
	Ok(SecretKey::from_slice(
		&keychain.secp(),
		&hashed.as_bytes()[..],
	)?)
}

/// The derivation index of `address` among this wallet's proof/slatepack
/// addresses (indices `0..=max` under `parent_key_id`), or `None` when the
/// address is not this wallet's within that bound. Index 0 — the default app
/// address — is checked first, so the common case costs a single derivation,
/// exactly like the old pinned-index behavior. Used by the receive path to
/// sign a payment proof with the key MATCHING the address the sender paid to
/// (a proof signed by any other key fails the sender's finalize-time check),
/// and by proof verification's is-this-mine test.
pub fn proof_address_derivation_index<K>(
	keychain: &K,
	parent_key_id: &Identifier,
	address: &DalekPublicKey,
	max: u32,
) -> Result<Option<u32>, Error>
where
	K: Keychain,
{
	for index in 0..=max {
		let sec_key = address_from_derivation_path(keychain, parent_key_id, index)?;
		let d_skey = match DalekSecretKey::from_bytes(&sec_key.0) {
			Ok(k) => k,
			Err(e) => {
				return Err(Error::ED25519Key(format!("{}", e)));
			}
		};
		let pub_key: DalekPublicKey = (&d_skey).into();
		if &pub_key == address {
			return Ok(Some(index));
		}
	}
	Ok(None)
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::grin_keychain::{ExtKeychain, ExtKeychainPath, Keychain};
	use crate::grin_util::secp::key::SecretKey as SecpSecretKey;
	use crate::grin_util::static_secp_instance;
	use crate::internal::tx::{create_payment_proof_signature, payment_proof_message};
	use ed25519_dalek::Verifier;
	use rand::rngs::mock::StepRng;

	fn test_parent() -> Identifier {
		ExtKeychainPath::new(2, 0, 0, 0, 0).to_identifier()
	}

	fn dalek_pub(sec: &SecretKey) -> DalekPublicKey {
		let d = DalekSecretKey::from_bytes(&sec.0).unwrap();
		(&d).into()
	}

	#[test]
	// A per-offer proof address minted at index N is a DIFFERENT address from
	// index 0 (and from every other index), and the receive-side detection
	// finds exactly the index it was minted at.
	fn minted_indices_are_distinct_and_detectable() {
		let keychain = ExtKeychain::from_random_seed(false).unwrap();
		let parent = test_parent();
		let addrs: Vec<DalekPublicKey> = (0..=8u32)
			.map(|i| {
				dalek_pub(&address_from_derivation_path(&keychain, &parent, i).unwrap())
			})
			.collect();
		// Pairwise distinct — index N never collides with index 0 or any other.
		for i in 0..addrs.len() {
			for j in (i + 1)..addrs.len() {
				assert_ne!(
					addrs[i].to_bytes(),
					addrs[j].to_bytes(),
					"indices {} and {} must derive distinct addresses",
					i,
					j
				);
			}
		}
		// Detection maps each address back to exactly its index.
		for (i, addr) in addrs.iter().enumerate() {
			assert_eq!(
				proof_address_derivation_index(&keychain, &parent, addr, 16).unwrap(),
				Some(i as u32)
			);
		}
		// A foreign address is not detected as ours.
		let other = ExtKeychain::from_random_seed(false).unwrap();
		let foreign =
			dalek_pub(&address_from_derivation_path(&other, &parent, 0).unwrap());
		assert_eq!(
			proof_address_derivation_index(&keychain, &parent, &foreign, 16).unwrap(),
			None
		);
	}

	#[test]
	// The money-path round trip the receive fix must uphold: a payment-proof
	// slate addressed to the wallet's index-N address is signed with index N's
	// key (detect -> derive -> sign, exactly the patched foreign::receive_tx
	// sequence), and that signature VERIFIES against the addressed key under
	// the sender's finalize-time check (tx.rs verify_slate_payment_proof's
	// receiver_address.verify). The old pinned index-0 signature must FAIL
	// that same check, demonstrating the bug this fixes.
	fn receive_signs_with_matching_indexed_key() {
		let keychain = ExtKeychain::from_random_seed(false).unwrap();
		let parent = test_parent();
		let amount: u64 = 2_000_000_000;

		// The sender pays to the wallet's per-offer address minted at index 7.
		let minted_index = 7u32;
		let receiver_address = dalek_pub(
			&address_from_derivation_path(&keychain, &parent, minted_index).unwrap(),
		);

		// A sender address (any foreign ed25519 key).
		let sender_address = {
			let secp_inst = static_secp_instance();
			let secp = secp_inst.lock();
			let mut rng = StepRng::new(9_876_543_210_u64, 1);
			dalek_pub(&SecpSecretKey::new(&secp, &mut rng))
		};

		// A kernel excess commitment for the proof message.
		let excess = {
			let secp_inst = static_secp_instance();
			let secp = secp_inst.lock();
			let mut rng = StepRng::new(1_234_567_890_u64, 1);
			let blind = SecpSecretKey::new(&secp, &mut rng);
			secp.commit(0, blind).unwrap()
		};

		// RECEIVE SIDE (patched foreign::receive_tx): detect the addressed
		// index, derive the MATCHING key, sign.
		let detected = proof_address_derivation_index(
			&keychain,
			&parent,
			&receiver_address,
			MAX_PROOF_ADDRESS_INDEX,
		)
		.unwrap()
		.expect("minted address must be detected");
		assert_eq!(detected, minted_index);
		let signing_key =
			address_from_derivation_path(&keychain, &parent, detected).unwrap();
		let sig =
			create_payment_proof_signature(amount, &excess, sender_address, signing_key)
				.unwrap();

		// SENDER SIDE (tx.rs finalize check): the signature must verify
		// against the address the sender paid to.
		let msg = payment_proof_message(amount, &excess, sender_address).unwrap();
		assert!(
			receiver_address.verify(&msg, &sig).is_ok(),
			"proof signed by the matching indexed key must verify"
		);

		// The OLD behavior — always signing with index 0 — fails the sender's
		// check for a payment addressed to index 7 (the pinned-index bug).
		let old_sig = create_payment_proof_signature(
			amount,
			&excess,
			sender_address,
			address_from_derivation_path(&keychain, &parent, 0).unwrap(),
		)
		.unwrap();
		assert!(
			receiver_address.verify(&msg, &old_sig).is_err(),
			"an index-0 signature must NOT verify against an index-7 address"
		);
	}
}
