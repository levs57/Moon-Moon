pub(crate) const NUM_CHALLENGE_BITS: usize = 128;
pub(crate) const NUM_HASH_BITS: usize = 250;
pub(crate) const BN_LIMB_WIDTH: usize = 64;
pub(crate) const BN_N_LIMBS: usize = 4;
pub(crate) const NUM_FE_WITHOUT_IO_FOR_CRHF: usize = 21; // new - it is 17+4, (quick maths: 4 per Xi because BN_N_LIMBS=4, +7 to absorb W, E, u, + 2 for vk and i)
pub(crate) const NUM_FE_FOR_RO: usize = 24;
