// SPDX-License-Identifier: CC0-1.0

//! Bitcoin script extension traits.

use core::fmt;

use hex::DisplayHex;

use super::witness_version::WitnessVersion;
use super::{bytes_to_asm_fmt, Instruction, InstructionIndices, Instructions, PushBytes, Script};
use crate::consensus::Encodable;
use crate::internal_macros::define_extension_trait;
use crate::opcodes::all::*;
use crate::opcodes::{self, Opcode};
use crate::policy::DUST_RELAY_TX_FEE;
use crate::prelude::{sink, String};
use crate::taproot::{LeafVersion, TapLeafHash};
use crate::FeeRate;

define_extension_trait! {
    /// Extension functionality for the [`Script`] type.
    pub trait ScriptExt impl for Script {
        /// Computes leaf hash of tapscript.
        fn tapscript_leaf_hash(&self) -> TapLeafHash {
            TapLeafHash::from_script(self, LeafVersion::TapScript)
        }

        /// Returns the minimum value an output with this script should have in order to be
        /// broadcastable on today's Bitcoin network.
        ///
        /// Dust depends on the -dustrelayfee value of the Bitcoin Core node you are broadcasting to.
        /// This function uses the default value of 0.00003 BTC/kB (3 sat/vByte).
        ///
        /// To use a custom value, use [`minimal_non_dust_custom`].
        ///
        /// [`minimal_non_dust_custom`]: Script::minimal_non_dust_custom
        fn minimal_non_dust(&self) -> crate::Amount {
            minimal_non_dust_internal(self, DUST_RELAY_TX_FEE.into())
        }

        /// Returns the minimum value an output with this script should have in order to be
        /// broadcastable on today's Bitcoin network.
        ///
        /// Dust depends on the -dustrelayfee value of the Bitcoin Core node you are broadcasting to.
        /// This function lets you set the fee rate used in dust calculation.
        ///
        /// The current default value in Bitcoin Core (as of v26) is 3 sat/vByte.
        ///
        /// To use the default Bitcoin Core value, use [`minimal_non_dust`].
        ///
        /// [`minimal_non_dust`]: Script::minimal_non_dust
        fn minimal_non_dust_custom(&self, dust_relay_fee: FeeRate) -> crate::Amount {
            minimal_non_dust_internal(self, dust_relay_fee.to_sat_per_kwu() * 4)
        }

        /// Returns witness version of the script, if any, assuming the script is a `scriptPubkey`.
        ///
        /// # Returns
        ///
        /// The witness version if this script is found to conform to the SegWit rules:
        ///
        /// > A scriptPubKey (or redeemScript as defined in BIP16/P2SH) that consists of a 1-byte
        /// > push opcode (for 0 to 16) followed by a data push between 2 and 40 bytes gets a new
        /// > special meaning. The value of the first push is called the "version byte". The following
        /// > byte vector pushed is called the "witness program".
        fn witness_version(&self) -> Option<WitnessVersion> {
            let script_len = self.0.len();
            if !(4..=42).contains(&script_len) {
                return None;
            }

            let ver_opcode = Opcode::from(self.0[0]); // Version 0 or PUSHNUM_1-PUSHNUM_16
            let push_opbyte = self.0[1]; // Second byte push opcode 2-40 bytes

            if push_opbyte < OP_PUSHBYTES_2.to_u8() || push_opbyte > OP_PUSHBYTES_40.to_u8() {
                return None;
            }
            // Check that the rest of the script has the correct size
            if script_len - 2 != push_opbyte as usize {
                return None;
            }

            WitnessVersion::try_from(ver_opcode).ok()
        }

        /// Checks whether a script pubkey is a P2SH output.
        fn is_p2sh(&self) -> bool {
            self.0.len() == 23
                && self.0[0] == OP_HASH160.to_u8()
                && self.0[1] == OP_PUSHBYTES_20.to_u8()
                && self.0[22] == OP_EQUAL.to_u8()
        }

        /// Checks whether a script pubkey is a P2PKH output.
        fn is_p2pkh(&self) -> bool {
            self.0.len() == 25
                && self.0[0] == OP_DUP.to_u8()
                && self.0[1] == OP_HASH160.to_u8()
                && self.0[2] == OP_PUSHBYTES_20.to_u8()
                && self.0[23] == OP_EQUALVERIFY.to_u8()
                && self.0[24] == OP_CHECKSIG.to_u8()
        }

        /// Checks whether a script is push only.
        ///
        /// Note: `OP_RESERVED` (`0x50`) and all the OP_PUSHNUM operations
        /// are considered push operations.
        fn is_push_only(&self) -> bool {
            for inst in self.instructions() {
                match inst {
                    Err(_) => return false,
                    Ok(Instruction::PushBytes(_)) => {}
                    Ok(Instruction::Op(op)) if op.to_u8() <= 0x60 => {}
                    // From Bitcoin Core
                    // if (opcode > OP_PUSHNUM_16 (0x60)) return false
                    Ok(Instruction::Op(_)) => return false,
                }
            }
            true
        }

        /// Checks whether a script pubkey is a bare multisig output.
        ///
        /// In a bare multisig pubkey script the keys are not hashed, the script
        /// is of the form:
        ///
        ///    `2 <pubkey1> <pubkey2> <pubkey3> 3 OP_CHECKMULTISIG`
        fn is_multisig(&self) -> bool {
            let required_sigs;

            let mut instructions = self.instructions();
            if let Some(Ok(Instruction::Op(op))) = instructions.next() {
                if let Some(pushnum) = op.decode_pushnum() {
                    required_sigs = pushnum;
                } else {
                    return false;
                }
            } else {
                return false;
            }

            let mut num_pubkeys: u8 = 0;
            while let Some(Ok(instruction)) = instructions.next() {
                match instruction {
                    Instruction::PushBytes(_) => {
                        num_pubkeys += 1;
                    }
                    Instruction::Op(op) => {
                        if let Some(pushnum) = op.decode_pushnum() {
                            if pushnum != num_pubkeys {
                                return false;
                            }
                        }
                        break;
                    }
                }
            }

            if required_sigs > num_pubkeys {
                return false;
            }

            if let Some(Ok(Instruction::Op(op))) = instructions.next() {
                if op != OP_CHECKMULTISIG {
                    return false;
                }
            } else {
                return false;
            }

            instructions.next().is_none()
        }

        /// Checks whether a script pubkey is a Segregated Witness (segwit) program.
        fn is_witness_program(&self) -> bool { self.witness_version().is_some() }

        /// Checks whether a script pubkey is a P2WSH output.
        fn is_p2wsh(&self) -> bool {
            self.0.len() == 34
                && self.witness_version() == Some(WitnessVersion::V0)
                && self.0[1] == OP_PUSHBYTES_32.to_u8()
        }

        /// Checks whether a script pubkey is a P2WPKH output.
        fn is_p2wpkh(&self) -> bool {
            self.0.len() == 22
                && self.witness_version() == Some(WitnessVersion::V0)
                && self.0[1] == OP_PUSHBYTES_20.to_u8()
        }

        /// Checks whether a script pubkey is a P2TR output.
        fn is_p2tr(&self) -> bool {
            self.0.len() == 34
                && self.witness_version() == Some(WitnessVersion::V1)
                && self.0[1] == OP_PUSHBYTES_32.to_u8()
        }

        /// Check if this is a consensus-valid OP_RETURN output.
        ///
        /// To validate if the OP_RETURN obeys Bitcoin Core's current standardness policy, use
        /// [`is_standard_op_return()`](Self::is_standard_op_return) instead.
        fn is_op_return(&self) -> bool {
            match self.0.first() {
                Some(b) => *b == OP_RETURN.to_u8(),
                None => false,
            }
        }

        /// Check if this is an OP_RETURN that obeys Bitcoin Core standardness policy.
        ///
        /// What this function considers to be standard may change without warning pending Bitcoin Core
        /// changes.
        fn is_standard_op_return(&self) -> bool { self.is_op_return() && self.0.len() <= 80 }

        /// Checks whether a script is trivially known to have no satisfying input.
        ///
        /// This method has potentially confusing semantics and an unclear purpose, so it's going to be
        /// removed. Use `is_op_return` if you want `OP_RETURN` semantics.
        #[deprecated(
            since = "0.32.0",
            note = "The method has potentially confusing semantics and is going to be removed, you might want `is_op_return`"
        )]
        fn is_provably_unspendable(&self) -> bool {
            use crate::opcodes::Class::{IllegalOp, ReturnOp};

            match self.0.first() {
                Some(b) => {
                    let first = Opcode::from(*b);
                    let class = first.classify(opcodes::ClassifyContext::Legacy);

                    class == ReturnOp || class == IllegalOp
                }
                None => false,
            }
        }

        /// Get redeemScript following BIP16 rules regarding P2SH spending.
        ///
        /// This does not guarantee that this represents a P2SH input [`Script`].
        /// It merely gets the last push of the script.
        ///
        /// Use [`Script::is_p2sh`] on the scriptPubKey to check whether it is actually a P2SH script.
        fn redeem_script(&self) -> Option<&Script> {
            // Script must consist entirely of pushes.
            if self.instructions().any(|i| i.is_err() || i.unwrap().push_bytes().is_none()) {
                return None;
            }

            if let Some(Ok(Instruction::PushBytes(b))) = self.instructions().last() {
                Some(Script::from_bytes(b.as_bytes()))
            } else {
                None
            }
        }

        /// Returns the minimum value an output with this script should have in order to be
        /// broadcastable on today’s Bitcoin network.
        #[deprecated(since = "0.32.0", note = "use minimal_non_dust and friends")]
        fn dust_value(&self) -> crate::Amount { self.minimal_non_dust() }

        /// Counts the sigops for this Script using accurate counting.
        ///
        /// In Bitcoin Core, there are two ways to count sigops, "accurate" and "legacy".
        /// This method uses "accurate" counting. This means that OP_CHECKMULTISIG and its
        /// verify variant count for N sigops where N is the number of pubkeys used in the
        /// multisig. However, it will count for 20 sigops if CHECKMULTISIG is not preceded by an
        /// OP_PUSHNUM from 1 - 16 (this would be an invalid script)
        ///
        /// Bitcoin Core uses accurate counting for sigops contained within redeemScripts (P2SH)
        /// and witnessScripts (P2WSH) only. It uses legacy for sigops in scriptSigs and scriptPubkeys.
        ///
        /// (Note: Taproot scripts don't count toward the sigop count of the block,
        /// nor do they have CHECKMULTISIG operations. This function does not count OP_CHECKSIGADD,
        /// so do not use this to try and estimate if a Taproot script goes over the sigop budget.)
        fn count_sigops(&self) -> usize { count_sigops_internal(self, true) }

        /// Counts the sigops for this Script using legacy counting.
        ///
        /// In Bitcoin Core, there are two ways to count sigops, "accurate" and "legacy".
        /// This method uses "legacy" counting. This means that OP_CHECKMULTISIG and its
        /// verify variant count for 20 sigops.
        ///
        /// Bitcoin Core uses legacy counting for sigops contained within scriptSigs and
        /// scriptPubkeys. It uses accurate for redeemScripts (P2SH) and witnessScripts (P2WSH).
        ///
        /// (Note: Taproot scripts don't count toward the sigop count of the block,
        /// nor do they have CHECKMULTISIG operations. This function does not count OP_CHECKSIGADD,
        /// so do not use this to try and estimate if a Taproot script goes over the sigop budget.)
        fn count_sigops_legacy(&self) -> usize { count_sigops_internal(self, false) }

        /// Iterates over the script instructions.
        ///
        /// Each returned item is a nested enum covering opcodes, datapushes and errors.
        /// At most one error will be returned and then the iterator will end. To instead iterate over
        /// the script as sequence of bytes call the [`bytes`](Script::bytes) method.
        ///
        /// To force minimal pushes, use [`instructions_minimal`](Self::instructions_minimal).
        fn instructions(&self) -> Instructions {
            Instructions { data: self.0.iter(), enforce_minimal: false }
        }

        /// Iterates over the script instructions while enforcing minimal pushes.
        ///
        /// This is similar to [`instructions`](Self::instructions) but an error is returned if a push
        /// is not minimal.
        fn instructions_minimal(&self) -> Instructions {
            Instructions { data: self.0.iter(), enforce_minimal: true }
        }

        /// Iterates over the script instructions and their indices.
        ///
        /// Unless the script contains an error, the returned item consists of an index pointing to the
        /// position in the script where the instruction begins and the decoded instruction - either an
        /// opcode or data push.
        ///
        /// To force minimal pushes, use [`Self::instruction_indices_minimal`].
        fn instruction_indices(&self) -> InstructionIndices {
            InstructionIndices::from_instructions(self.instructions())
        }

        /// Iterates over the script instructions and their indices while enforcing minimal pushes.
        ///
        /// This is similar to [`instruction_indices`](Self::instruction_indices) but an error is
        /// returned if a push is not minimal.
        fn instruction_indices_minimal(&self) -> InstructionIndices {
            InstructionIndices::from_instructions(self.instructions_minimal())
        }

        /// Writes the human-readable assembly representation of the script to the formatter.
        fn fmt_asm(&self, f: &mut dyn fmt::Write) -> fmt::Result {
            bytes_to_asm_fmt(self.as_ref(), f)
        }

        /// Returns the human-readable assembly representation of the script.
        fn to_asm_string(&self) -> String {
            let mut buf = String::new();
            self.fmt_asm(&mut buf).unwrap();
            buf
        }

        /// Formats the script as lower-case hex.
        ///
        /// This is a more convenient and performant way to write `format!("{:x}", script)`.
        /// For better performance you should generally prefer displaying the script but if `String` is
        /// required (this is common in tests) this method can be used.
        fn to_hex_string(&self) -> String { self.as_bytes().to_lower_hex_string() }

        /// Returns the first opcode of the script (if there is any).
        fn first_opcode(&self) -> Option<Opcode> {
            self.as_bytes().first().copied().map(From::from)
        }
    }
}

pub(crate) fn minimal_non_dust_internal(script: &Script, dust_relay_fee: u64) -> crate::Amount {
    // This must never be lower than Bitcoin Core's GetDustThreshold() (as of v0.21) as it may
    // otherwise allow users to create transactions which likely can never be broadcast/confirmed.
    let sats = dust_relay_fee
        .checked_mul(if script.is_op_return() {
            0
        } else if script.is_witness_program() {
            32 + 4 + 1 + (107 / 4) + 4 + // The spend cost copied from Core
                8 + // The serialized size of the TxOut's amount field
                script.consensus_encode(&mut sink()).expect("sinks don't error") as u64 // The serialized size of this script_pubkey
        } else {
            32 + 4 + 1 + 107 + 4 + // The spend cost copied from Core
                8 + // The serialized size of the TxOut's amount field
                script.consensus_encode(&mut sink()).expect("sinks don't error") as u64 // The serialized size of this script_pubkey
        })
        .expect("dust_relay_fee or script length should not be absurdly large")
        / 1000; // divide by 1000 like in Core to get value as it cancels out DEFAULT_MIN_RELAY_TX_FEE
                // Note: We ensure the division happens at the end, since Core performs the division at the end.
                //       This will make sure none of the implicit floor operations mess with the value.

    crate::Amount::from_sat(sats)
}

fn count_sigops_internal(script: &Script, accurate: bool) -> usize {
    let mut n = 0;
    let mut pushnum_cache = None;
    for inst in script.instructions() {
        match inst {
            Ok(Instruction::Op(opcode)) => {
                match opcode {
                    // p2pk, p2pkh
                    OP_CHECKSIG | OP_CHECKSIGVERIFY => {
                        n += 1;
                    }
                    OP_CHECKMULTISIG | OP_CHECKMULTISIGVERIFY => {
                        match (accurate, pushnum_cache) {
                            (true, Some(pushnum)) => {
                                // Add the number of pubkeys in the multisig as sigop count
                                n += usize::from(pushnum);
                            }
                            _ => {
                                // MAX_PUBKEYS_PER_MULTISIG from Bitcoin Core
                                // https://github.com/bitcoin/bitcoin/blob/v25.0/src/script/script.h#L29-L30
                                n += 20;
                            }
                        }
                    }
                    _ => {
                        pushnum_cache = opcode.decode_pushnum();
                    }
                }
            }
            Ok(Instruction::PushBytes(_)) => {
                pushnum_cache = None;
            }
            // In Bitcoin Core it does `if (!GetOp(pc, opcode)) break;`
            Err(_) => break,
        }
    }

    n
}

/// Iterates the script to find the last opcode.
///
/// Returns `None` is the instruction is data push or if the script is empty.
pub(in crate::blockdata::script) fn last_opcode(script: &Script) -> Option<Opcode> {
    match script.instructions().last() {
        Some(Ok(Instruction::Op(op))) => Some(op),
        _ => None,
    }
}

/// Iterates the script to find the last pushdata.
///
/// Returns `None` if the instruction is an opcode or if the script is empty.
pub(crate) fn last_pushdata(script: &Script) -> Option<&PushBytes> {
    match script.instructions().last() {
        // Handles op codes up to (but excluding) OP_PUSHNUM_NEG.
        Some(Ok(Instruction::PushBytes(bytes))) => Some(bytes),
        // OP_16 (0x60) and lower are considered "pushes" by Bitcoin Core (excl. OP_RESERVED).
        // However we are only interested in the pushdata so we can ignore them.
        _ => None,
    }
}