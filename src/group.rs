use super::Ctrl;
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
    pub fn matches(&self, ctrl: Ctrl) -> impl Iterator<Item = isize> {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("sse2") {
                return unsafe { self.matches_sse2(ctrl) };
            }
        }
        todo!("Implement non-x86/non-SSE fallback");
    }

    pub fn filled(&self) -> impl Iterator<Item = isize> {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("sse2") {
                return unsafe { self.filled_sse2() };
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
    unsafe fn matches_sse2(&self, ctrl: Ctrl) -> impl Iterator<Item = isize> {
        let result = self.matches_mask_sse2(ctrl);
        (0..SIZE)
            .map(move |s| (s, result >> s))
            .filter(|(_, m)| m & 1 == 1)
            .map(|(s, _)| s as isize)
    }

    #[target_feature(enable = "sse2")]
    unsafe fn filled_sse2(&self) -> impl Iterator<Item = isize> {
        let result = self.filled_mask_sse2();
        (0..SIZE)
            .map(move |s| (s, result >> s))
            .filter(|(_, m)| m & 1 == 1)
            .map(|(s, _)| s as isize)
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
    unsafe fn mask(&self, mask: i8, f: unsafe fn(__m128i, __m128i) -> __m128i) -> u32 {
        let mask = _mm_set1_epi8(mask);
        let group = _mm_load_si128(self.0 as *const _);
        _mm_movemask_epi8(f(group, mask)) as u32
    }
}
