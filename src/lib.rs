#![cfg_attr(not(test), no_std)]

mod hash;

use crate::hash::{hash, H256};
use arrayref::{array_mut_ref, array_ref};
use core::cmp::PartialEq;
use core::convert::From;
use core::marker::PhantomData;
use core::ops::{Add, BitAnd, Shr, Sub};

pub struct Imp<'a, T>
where
    T: Clone + Shr<usize, Output = T> + BitAnd<Output = T> + Add + Sub + PartialEq + From<usize>,
{
    pub offsets: &'a [u8],
    pub db: &'a mut [u8],
    pub height: usize,
    _phantom: PhantomData<T>,
}

impl<'a, T> Imp<'a, T>
where
    T: Clone + Shr<usize, Output = T> + BitAnd<Output = T> + Add + Sub + PartialEq + From<usize>,
{
    pub fn new(data: &'a mut [u8], height: usize) -> Self {
        // Read the number of offsets
        let length = u64::from_le_bytes(*array_ref![data, 0, 8]) as usize;

        // Grab the offsets slice
        let begin = 8;
        let end = length * 8;
        let offsets = &data[begin..end];

        // Grab the proof slice as mutable
        let begin = end;
        let end = begin + length * 32;
        let db = unsafe { &mut *(&data[begin..end] as *const [u8] as *mut [u8]) };

        Self {
            offsets,
            db,
            height,
            _phantom: PhantomData::<T>,
        }
    }

    // TODO: add debug check that operations are occuring only on
    // leaf nodes
    pub fn get(&self, index: T) -> H256 {
        let offset = self.lookup(index) * 32;
        *array_ref![self.db, offset, 32]
    }

    pub fn update(&mut self, index: T, value: H256) {
        let offset = self.lookup(index) * 32;
        self.db[offset..offset + 32].copy_from_slice(&value);
    }

    fn lookup(&self, index: T) -> usize {
        let mut position = 0u64;
        let mut offset = 0u64;

        for i in 1..(self.height + 4) {
            let bit = (index.clone() >> (self.height + 3 - i)) & 1.into();

            if bit == 0.into() {
                position += 1;
            } else {
                let skip =
                    u64::from_le_bytes(*array_ref![self.offsets, (position * 8) as usize, 8]);
                position += skip;
                offset += skip;
            }
        }

        offset as usize
    }

    pub fn root(&mut self) -> H256 {
        let offsets = unsafe {
            core::slice::from_raw_parts(self.offsets.as_ptr() as *const u64, self.offsets.len() / 8)
        };

        fn helper(proof: &[u8], offsets: &[u64], offset: u64) -> H256 {
            if offsets.len() == 0 {
                return *array_ref![proof, (offset * 32) as usize, 32];
            }

            let mut left = *array_ref![proof, (offset * 32) as usize, 32];
            let mut right = *array_ref![proof, ((offset + 1) * 32) as usize, 32];

            if offsets[0] != 1 {
                left = helper(proof, &offsets[1..offsets[0] as usize], offset);
            }

            if offsets.len() != 1 {
                right = helper(
                    proof,
                    &offsets[offsets[0] as usize..],
                    offsets[0] as u64 + offset,
                );
            }

            // Copy chunks into hashing buffer
            let mut buf = [0u8; 64];
            buf[0..32].copy_from_slice(&left);
            buf[32..64].copy_from_slice(&right);

            // Hash chunks
            hash(array_mut_ref![buf, 0, 64]);

            *array_ref![buf, 0, 32]
        }

        helper(self.db, offsets, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bigint::U256;

    fn zh(mut depth: usize) -> H256 {
        let mut buf = [0u8; 64];

        // Hash of an account with a balance of zero.
        let mut tmp = [
            218, 109, 128, 123, 247, 149, 16, 97, 70, 229, 130, 39, 117, 217, 20, 176, 39, 122,
            101, 36, 15, 101, 14, 212, 200, 167, 202, 119, 130, 78, 90, 223,
        ];

        buf[0..32].copy_from_slice(&tmp);
        buf[32..64].copy_from_slice(&tmp);

        while depth > 0 {
            tmp.copy_from_slice(&buf[0..32]);
            buf[32..64].copy_from_slice(&tmp);
            hash(&mut buf);
            depth -= 1;
        }

        *array_ref![buf, 0, 32]
    }

    fn h256(n: u8) -> H256 {
        let mut ret = [0u8; 32];
        ret[0] = n;
        ret
    }

    fn get_proof() -> Vec<u8> {
        // indexes = [16, 17, 9, 10, 11, 3]
        let offsets: Vec<u8> = vec![6, 5, 3, 2, 1, 1].iter().fold(vec![], |mut acc, x| {
            let x = *x as u64;
            acc.extend(&x.to_le_bytes());
            acc
        });

        let proof: Vec<u8> = vec![h256(0), h256(0), h256(1), h256(1), zh(0), zh(0)]
            .iter()
            .fold(vec![], |mut acc, x| {
                acc.extend(x);
                acc
            });

        let mut ret = offsets;
        ret.extend(proof);

        ret
    }

    fn build_data(offsets: Vec<u64>, proof: Vec<H256>) -> Vec<u8> {
        let offsets: Vec<u8> = offsets.iter().fold(vec![], |mut acc, x| {
            let x = *x as u64;
            acc.extend(&x.to_le_bytes());
            acc
        });

        let proof: Vec<u8> = proof.iter().fold(vec![], |mut acc, x| {
            acc.extend(x);
            acc
        });

        let mut ret = offsets;
        ret.extend(proof);

        ret
    }

    #[test]
    fn lookup_small_branch() {
        // indexes = [4, 10, 11, 3]
        let mut offsets: Vec<u8> = vec![4, 3, 1, 1].iter().fold(vec![], |mut acc, x| {
            let x = *x as u64;
            acc.extend(&x.to_le_bytes());
            acc
        });

        offsets.extend(vec![0u8; 32 * 4]);

        let mem = Imp::<U256>::new(&mut offsets, 1);

        assert_eq!(mem.lookup((10 << 1).into()), 1);
        assert_eq!(mem.lookup((11 << 1).into()), 2);
        assert_eq!(mem.lookup((4 << 2).into()), 0);
        assert_eq!(mem.lookup((3 << 3).into()), 3);
    }

    #[test]
    fn lookup_single_account() {
        let mut proof = get_proof();
        let mem = Imp::<U256>::new(&mut proof, 1);

        assert_eq!(mem.lookup((9 << 1).into()), 2);
        assert_eq!(mem.lookup((10 << 1).into()), 3);
        assert_eq!(mem.lookup((11 << 1).into()), 4);
        assert_eq!(mem.lookup(16.into()), 0);
        assert_eq!(mem.lookup(17.into()), 1);
    }

    #[test]
    fn lookup_full_tree() {
        // indexes = [8, 9, 10, 11, 12, 13, 14, 15]
        let mut offsets: Vec<u8> =
            vec![7, 4, 2, 1, 1, 2, 1, 1]
                .iter()
                .fold(vec![], |mut acc, x| {
                    let x = *x as u64;
                    acc.extend(&x.to_le_bytes());
                    acc
                });

        offsets.extend(vec![0u8; 32 * 7]);

        let mem = Imp::<U256>::new(&mut offsets, 1);

        for i in 0..7 {
            assert_eq!(mem.lookup(((i + 8) << 1).into()), i as usize);
        }
    }

    #[test]
    fn root_simple_branch() {
        // indexes = [4, 10, 11, 3]
        let offsets: Vec<u64> = vec![4, 3, 1, 1];
        let proof = vec![zh(1), zh(0), zh(0), zh(2)];
        let mut data = build_data(offsets, proof);
        let mut mem = Imp::<U256>::new(&mut data, 1);
        assert_eq!(mem.root(), zh(3))
    }

    #[test]
    fn root_full_tree() {
        // indexes = [8, 9, 10, 11, 12, 13, 14, 15]
        let offsets: Vec<u64> = vec![8, 4, 2, 1, 1, 2, 1, 1];
        let proof = vec![zh(0), zh(0), zh(0), zh(0), zh(0), zh(0), zh(0), zh(0)];
        let mut data = build_data(offsets, proof);
        let mut mem = Imp::<U256>::new(&mut data, 1);
        assert_eq!(mem.root(), zh(3))
    }

    #[test]
    fn root_large_branch() {
        // indexes = [2, 6, 7168, 7169, 3585, 1793, 897, 449, 225, 113, 57, 29, 15]
        let offsets: Vec<u64> = vec![13, 1, 1, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
        let proof = vec![
            zh(11),
            zh(10),
            zh(0),
            zh(0),
            zh(1),
            zh(2),
            zh(3),
            zh(4),
            zh(5),
            zh(6),
            zh(7),
            zh(8),
            zh(9),
        ];

        let mut data = build_data(offsets, proof);
        let mut mem = Imp::<U256>::new(&mut data, 1);
        assert_eq!(mem.root(), zh(12))
    }
}
