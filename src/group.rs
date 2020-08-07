use super::ctrl::{self, Ctrl};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;
use std::is_x86_feature_detected;

pub const SIZE: usize = 16;

/// A `Group` performs SIMD powered lookups
/// on an array of `Ctrl`s.
pub struct Group(pub *const Ctrl);

impl Group {
    pub fn matches(&self, ctrl: Ctrl) -> MaskIter {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("sse2") {
                return unsafe { self.matches_sse2(ctrl) };
            }
        }
        todo!("Implement non-x86/non-SSE fallback");
    }

    pub fn filled(&self) -> MaskIter {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("sse2") {
                return unsafe { self.filled_sse2() };
            }
        }
        todo!("Implement non-x86/non-SSE fallback");
    }

    pub fn empty(&self) -> MaskIter {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("sse2") {
                return unsafe { self.empty_sse2() };
            }
        }
        todo!("Implement non-x86/non-SSE fallback");
    }

    pub fn matches_mask(&self, ctrl: Ctrl) -> u32 {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("sse2") {
                return unsafe { self.matches_mask_sse2(ctrl) };
            }
        }
        todo!("Implement non-x86/non-SSE fallback");
    }

    pub fn filled_mask(&self) -> u32 {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("sse2") {
                return unsafe { self.filled_mask_sse2() };
            }
        }
        todo!("Implement non-x86/non-SSE fallback");
    }

    #[target_feature(enable = "sse2")]
    unsafe fn matches_sse2(&self, ctrl: Ctrl) -> MaskIter {
        let mask = self.matches_mask_sse2(ctrl);
        MaskIter::new(mask)
    }

    #[target_feature(enable = "sse2")]
    unsafe fn filled_sse2(&self) -> MaskIter {
        let mask = self.filled_mask_sse2();
        MaskIter::new(mask)
    }

    #[target_feature(enable = "sse2")]
    unsafe fn empty_sse2(&self) -> MaskIter {
        let mask = self.empty_mask_sse2();
        MaskIter::new(mask)
    }

    #[target_feature(enable = "sse2")]
    unsafe fn matches_mask_sse2(&self, ctrl: Ctrl) -> u32 {
        let mask = u8::from(ctrl);
        self.mask(mask as i8, _mm_cmpeq_epi8)
    }

    #[target_feature(enable = "sse2")]
    unsafe fn filled_mask_sse2(&self) -> u32 {
        self.mask(-1, _mm_cmpgt_epi8)
    }

    #[target_feature(enable = "sse2")]
    unsafe fn empty_mask_sse2(&self) -> u32 {
        self.mask(ctrl::Flag::Empty as i8, _mm_cmpeq_epi8)
    }

    #[target_feature(enable = "sse2")]
    unsafe fn mask(&self, mask: i8, f: unsafe fn(__m128i, __m128i) -> __m128i) -> u32 {
        let mask = _mm_set1_epi8(mask);
        let group = _mm_load_si128(self.0 as *const _);
        _mm_movemask_epi8(f(group, mask)) as u32
    }
}

/// `MaskIter` iterates over a bitmask from right
/// to left, returning the index of each 1.
pub struct MaskIter(u32);

impl MaskIter {
    fn new(mask: u32) -> Self {
        Self(mask)
    }
}

impl Iterator for MaskIter {
    type Item = isize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0 == 0 {
            return None;
        }
        let tzs = self.0.trailing_zeros() as isize;
        self.0 &= !0 - 1 << tzs;
        Some(tzs)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let ones = self.0.count_ones() as usize;
        (ones, Some(ones))
    }
}
