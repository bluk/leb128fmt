//! Leb128fmt is a library to decode and encode `LEB128` formatted numbers.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    rust_2018_idioms,
    unused_lifetimes,
    unused_qualifications
)]

use core::convert::TryFrom;

/// Returns the maximum byte length that is used to encode a value for a given
/// number of `BITS`.
///
/// A value can possibly be encoded with a fewer number of bytes.
///
/// # Example
///
/// ```rust
/// assert_eq!(5, leb128fmt::max_len::<32>());
/// assert_eq!(10, leb128fmt::max_len::<64>());
///
/// assert_eq!(5, leb128fmt::max_len::<33>());
/// ```
#[inline]
#[must_use]
pub const fn max_len<const BITS: u32>() -> usize {
    let rem = if BITS % 7 == 0 { 0 } else { 1 };
    ((BITS / 7) + rem) as usize
}

/// Returns true if this is the last byte in an encoded LEB128 value.
///
/// # Example
///
/// ```rust
/// let bytes = &[0x42, 0x8F, 0xFF, 0x7F, 0xFF];
/// let pos = 1;
/// let end = bytes.iter().skip(pos).copied().position(leb128fmt::is_last);
/// let end = end.unwrap();
/// assert_eq!(pos + end, 3);
/// let value = &bytes[pos..=pos + end];
/// ```
#[inline]
#[must_use]
pub const fn is_last(byte: u8) -> bool {
    byte & 0x80 == 0
}

/// Builds custom unsigned integer encode functions.
///
/// The macro's 3 parameters are:
///
/// 1. The name of the function.
/// 2. The type to return.
/// 3. The number of encoded BITS to decode.
///
/// ```rust
/// leb128fmt::encode_uint_arr!(encode_u33, u64, 33);
///
/// let result = encode_u33(0);
/// assert_eq!(Some(([0x00, 0x00, 0x00, 0x00, 0x00], 1)), result);
///
/// let result = encode_u33(8589934591);
/// assert_eq!(Some(([0xFF, 0xFF, 0xFF, 0xFF, 0x1F], 5)), result);
/// ```
#[macro_export]
macro_rules! encode_uint_arr {
    ($func:ident, $num_ty:ty, $bits:literal) => {
        /// Encodes an unsigned LEB128 number.
        ///
        /// If the value can be encoded in the given number of bits, then return
        /// the encoded output and the index after the last byte written.
        ///
        /// If the value cannot be encoded with the given number of bits, then return None.
        #[must_use]
        pub const fn $func(
            mut value: $num_ty,
        ) -> Option<(
            [u8; (($bits / 7) + if $bits % 7 == 0 { 0 } else { 1 }) as usize],
            usize,
        )> {
            const BITS: u32 = $bits;
            if <$num_ty>::BITS > BITS && value >> BITS - 1 > 1 {
                return None;
            }

            let mut output = [0; (($bits / 7) + if $bits % 7 == 0 { 0 } else { 1 }) as usize];
            let mut index = 0;
            loop {
                let mut b = (value & 0x7f) as u8;

                value >>= 7;
                let done = value == 0;

                if !done {
                    b |= 0x80;
                }

                output[index] = b;
                index += 1;

                if done {
                    return Some((output, index));
                }
            }
        }
    };
}

encode_uint_arr!(encode_u16, u16, 16);
encode_uint_arr!(encode_u32, u32, 32);
encode_uint_arr!(encode_u64, u64, 64);

/// Builds custom unsigned integer encode functions with the max byte length of
/// byte arrays used.
///
/// The macro's 3 parameters are:
///
/// 1. The name of the function.
/// 2. The type to return.
/// 3. The number of encoded BITS to decode.
///
/// ```rust
/// leb128fmt::encode_fixed_uint_arr!(encode_fixed_u33, u64, 33);
///
/// let output = encode_fixed_u33(0);
/// assert_eq!(Some([0x80, 0x80, 0x80, 0x80, 0x00]), output);
///
/// let output = encode_fixed_u33(8589934591);
/// assert_eq!(Some([0xFF, 0xFF, 0xFF, 0xFF, 0x1F]), output);
/// ```
#[macro_export]
macro_rules! encode_fixed_uint_arr {
    ($func:ident, $num_ty:ty, $bits:literal) => {
        /// Encodes an unsigned LEB128 number with using the maximum number of
        /// bytes for the given bits length.
        ///
        /// If the value can be encoded in the given number of bits, then return
        /// the encoded value.
        ///
        /// If the value cannot be encoded with the given number of bits, then return None.
        #[must_use]
        pub const fn $func(
            value: $num_ty,
        ) -> Option<[u8; (($bits / 7) + if $bits % 7 == 0 { 0 } else { 1 }) as usize]> {
            const BITS: u32 = $bits;
            if <$num_ty>::BITS > BITS && value >> BITS - 1 > 1 {
                return None;
            }

            let mut output = [0; (($bits / 7) + if $bits % 7 == 0 { 0 } else { 1 }) as usize];

            let mut index = 0;
            let mut shift: u32 = 0;
            loop {
                let v = value >> shift;

                let mut b = (v & 0x7f) as u8;

                let done = shift == BITS - (BITS % 7);

                if !done {
                    b |= 0x80;
                }

                output[index] = b;
                index += 1;
                shift += 7;

                if done {
                    return Some(output);
                }
            }
        }
    };
}

encode_fixed_uint_arr!(encode_fixed_u16, u16, 16);
encode_fixed_uint_arr!(encode_fixed_u32, u32, 32);
encode_fixed_uint_arr!(encode_fixed_u64, u64, 64);

/// Builds custom unsigned integer decode functions.
///
/// The macro's 3 parameters are:
///
/// 1. The name of the function.
/// 2. The type to return.
/// 3. The number of encoded BITS to decode.
///
/// ```rust
/// leb128fmt::decode_uint_arr!(decode_u33, u64, 33);
///
/// let input = [0xFF, 0xFF, 0xFF, 0xFF, 0x1F];
/// let result = decode_u33(input);
/// assert_eq!(Some((8589934591, 5)), result);
/// ```
#[macro_export]
macro_rules! decode_uint_arr {
    ($func:ident, $num_ty:ty, $bits:literal) => {
        /// Decodes an unsigned LEB128 number.
        ///
        /// If there is a valid encoded value, returns the decoded value and the
        /// index after the last byte read.
        ///
        /// If the encoding is incorrect, returns `None`.
        ///
        /// If the size in bits of the returned type is less than the size of the value in bits, returns `None`.
        /// For instance, if 33 bits are being decoded, then the returned type must be at least a `u64`.
        #[must_use]
        pub const fn $func(
            input: [u8; (($bits / 7) + if $bits % 7 == 0 { 0 } else { 1 }) as usize],
        ) -> Option<($num_ty, usize)> {
            const BITS: u32 = $bits;
            if BITS > <$num_ty>::BITS {
                return None;
            }

            let n = input[0];
            if n & 0x80 == 0 {
                return Some((n as $num_ty, 1));
            }

            let mut result = (n & 0x7f) as $num_ty;
            let mut shift = 7;
            let mut pos = 1;
            loop {
                let n = input[pos];

                // If unnecessary bits are set (the bits would be dropped when
                // the value is shifted), then return an error.
                //
                // This error may be too strict.
                //
                // There should be at least a simple check to quickly
                // determine that the decoding has failed instead of
                // misinterpreting further data.
                //
                // For a less strict check, the && condition could be:
                //
                // (n & 0x80) != 0
                //
                // Another stricter condition is if the last byte has a 0 value.
                // The encoding is correct but not the minimal number of bytes
                // was used to express the final value.
                if shift == BITS - (BITS % 7) && n >= 1 << (BITS % 7) {
                    return None;
                }

                if n & 0x80 == 0 {
                    result |= (n as $num_ty) << shift;
                    return Some((result, pos + 1));
                }

                result |= ((n & 0x7f) as $num_ty) << shift;
                shift += 7;
                pos += 1;
            }
        }
    };
}

decode_uint_arr!(decode_u16, u16, 16);
decode_uint_arr!(decode_u32, u32, 32);
decode_uint_arr!(decode_u64, u64, 64);

mod private {
    pub trait Sealed {}

    impl Sealed for u8 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
    impl Sealed for u128 {}
}

/// Sealed trait for supported unsigned integer types.
pub trait UInt: private::Sealed {
    /// Size of the type in bits.
    const BITS: u32;
}

impl UInt for u8 {
    const BITS: u32 = u8::BITS;
}

impl UInt for u16 {
    const BITS: u32 = u16::BITS;
}

impl UInt for u32 {
    const BITS: u32 = u32::BITS;
}

impl UInt for u64 {
    const BITS: u32 = u64::BITS;
}

impl UInt for u128 {
    const BITS: u32 = u128::BITS;
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum InnerError {
    NeedMoreBytes,
    InvalidEncoding,
}

/// Error when decoding a LEB128 value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(InnerError);

impl Error {
    /// If more bytes are needed in the slice to decode the value
    #[inline]
    #[must_use]
    pub const fn is_more_bytes_needed(&self) -> bool {
        matches!(self.0, InnerError::NeedMoreBytes)
    }

    /// If the value has an invalid encoding
    #[inline]
    #[must_use]
    pub const fn is_invalid_encoding(&self) -> bool {
        matches!(self.0, InnerError::InvalidEncoding)
    }
}

/// Encodes a given value into an output slice using the fixed set of bytes.
///
/// # Examples
///
/// ```rust
/// let mut buffer = vec![254; 10];
/// let mut pos = 0;
/// let result = leb128fmt::encode_uint_slice::<_, 32>(0u32, &mut buffer, &mut pos);
/// assert_eq!(Some(1), result);
/// assert_eq!(1, pos);
/// assert_eq!(&[0x00], &buffer[..pos]);
///
/// assert_eq!(&[0x00, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE], buffer.as_slice());
///
/// let result = leb128fmt::encode_uint_slice::<_, 32>(u32::MAX, &mut buffer, &mut pos);
/// assert_eq!(Some(5), result);
/// assert_eq!(6, pos);
/// assert_eq!(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F], &buffer[1..pos]);
///
/// assert_eq!(&[0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0xFE, 0xFE, 0xFE, 0xFE], buffer.as_slice());
///
/// // Will try to encode even if the output slice is not as big as the maximum
/// // number of bytes required to output every value for the given BITS
/// let mut buffer = vec![254; 4];
/// let mut pos = 0;
/// let result = leb128fmt::encode_uint_slice::<_, 32>(1028u32, &mut buffer, &mut pos);
/// assert_eq!(Some(2), result);
/// assert_eq!(&[0x84, 0x08, 0xFE, 0xFE], buffer.as_slice());
///
/// // Will return `None` if the output buffer is not long enough but will have partially written
/// // the value
/// let mut buffer = vec![254; 4];
/// let mut pos = 0;
/// let result = leb128fmt::encode_uint_slice::<_, 32>(u32::MAX, &mut buffer, &mut pos);
/// assert_eq!(None, result);
/// assert_eq!(&[0xFF, 0xFF, 0xFF, 0xFF], buffer.as_slice());
///
/// // Will return `None` if the given value cannot be encoded with the given number of bits.
/// let mut buffer = vec![254; 10];
/// let mut pos = 0;
/// let result = leb128fmt::encode_uint_slice::<_, 32>(u64::MAX, &mut buffer, &mut pos);
/// assert_eq!(None, result);
/// assert_eq!(&[0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE], buffer.as_slice());
/// ```
#[allow(clippy::manual_let_else)]
pub fn encode_uint_slice<T, const BITS: u32>(
    mut value: T,
    output: &mut [u8],
    pos: &mut usize,
) -> Option<usize>
where
    T: Copy
        + PartialEq
        + core::ops::BitAnd
        + core::ops::Shr<u32>
        + core::ops::ShrAssign<u32>
        + From<u8>
        + UInt,
    <T as core::ops::Shr<u32>>::Output: PartialEq<T>,
    u8: TryFrom<<T as core::ops::BitAnd<T>>::Output>,
{
    if T::BITS > BITS && value >> BITS != T::from(0) {
        return None;
    }

    let mut index = *pos;
    loop {
        if index >= output.len() {
            return None;
        }

        let mut b = match u8::try_from(value & T::from(0x7f)) {
            Ok(b) => b,
            Err(_) => unreachable!(),
        };

        value >>= 7;

        let done = value == T::from(0);

        if !done {
            b |= 0x80;
        }

        output[index] = b;
        index += 1;

        if done {
            let len = index - *pos;
            *pos = index;
            return Some(len);
        }
    }
}

/// Encodes a given value into an output slice using a fixed set of bytes.
///
/// # Examples
///
/// ```rust
/// let mut buffer = vec![254; 10];
/// let mut pos = 0;
/// let result = leb128fmt::encode_fixed_uint_slice::<_, 32>(0u32, &mut buffer, &mut pos);
/// assert_eq!(Some(5), result);
/// assert_eq!(5, pos);
/// assert_eq!(&[0x80, 0x80, 0x80, 0x80, 0x00], &buffer[..pos]);
///
/// assert_eq!(&[0x80, 0x80, 0x80, 0x80, 0x00, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE], buffer.as_slice());
///
/// let result = leb128fmt::encode_fixed_uint_slice::<_, 32>(u32::MAX, &mut buffer, &mut pos);
/// assert_eq!(Some(5), result);
/// assert_eq!(10, pos);
/// assert_eq!(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F], &buffer[5..pos]);
///
/// assert_eq!(&[0x80, 0x80, 0x80, 0x80, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F], buffer.as_slice());
///
/// // Will return `None` if the output buffer is not long enough.
/// let mut buffer = vec![254; 4];
/// let mut pos = 0;
/// let result = leb128fmt::encode_fixed_uint_slice::<_, 32>(u32::MAX, &mut buffer, &mut pos);
/// assert_eq!(None, result);
/// assert_eq!(&[0xFE, 0xFE, 0xFE, 0xFE], buffer.as_slice());
///
/// // Will return `None` if the given value cannot be encoded with the given number of bits.
/// let mut buffer = vec![254; 10];
/// let mut pos = 0;
/// let result = leb128fmt::encode_fixed_uint_slice::<_, 32>(u64::MAX, &mut buffer, &mut pos);
/// assert_eq!(None, result);
/// assert_eq!(&[0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE], buffer.as_slice());
/// ```
#[allow(clippy::manual_let_else)]
pub fn encode_fixed_uint_slice<T, const BITS: u32>(
    mut value: T,
    output: &mut [u8],
    pos: &mut usize,
) -> Option<usize>
where
    T: Copy + core::ops::BitAnd + core::ops::Shr<u32> + core::ops::ShrAssign<u32> + From<u8> + UInt,
    <T as core::ops::Shr<u32>>::Output: core::ops::BitAnd<T>,
    <T as core::ops::Shr<u32>>::Output: PartialEq<T>,
    u8: TryFrom<<<T as core::ops::Shr<u32>>::Output as core::ops::BitAnd<T>>::Output>,
    u8: TryFrom<<T as std::ops::BitAnd>::Output>,
{
    if T::BITS > BITS && value >> BITS != T::from(0) {
        return None;
    }

    if output[*pos..].len() < max_len::<BITS>() {
        return None;
    }

    let mut index = *pos;
    for _ in 0..(max_len::<BITS>() - 1) {
        let mut b = match u8::try_from(value & T::from(0x7f)) {
            Ok(b) => b,
            Err(_) => unreachable!(),
        };

        b |= 0x80;

        value >>= 7;

        output[index] = b;
        index += 1;
    }

    let b = match u8::try_from(value & T::from(0x7f)) {
        Ok(b) => b,
        Err(_) => unreachable!(),
    };
    output[index] = b;
    index += 1;

    let len = index - *pos;
    *pos = index;
    Some(len)
}

/// Decodes an unsigned integer from a slice of bytes and starting at a given position.
///
/// # Errors
///
/// Returns an error if the value is not properly encoded or if more bytes are
/// needed to decode the value.
///
/// # Panics
///
/// Panics if the size in bits of the returned type is less than the size of the value in bits.
/// For instance, if 33 bits are being decoded, then the returned type must be at least a `u64`.
///
/// ```rust
/// let input = &[0x42, 0x8F, 0xFF, 0x7F, 0xFF];
/// let mut pos = 1;
/// let result = leb128fmt::decode_uint_slice::<u32, 32>(input.as_slice(), &mut pos);
/// assert_eq!(result, Ok(2097039));
/// assert_eq!(pos, 4);
/// ```
pub fn decode_uint_slice<T, const BITS: u32>(input: &[u8], pos: &mut usize) -> Result<T, Error>
where
    T: core::ops::Shl<u32, Output = T> + core::ops::BitOrAssign + From<u8> + UInt,
{
    assert!(BITS <= T::BITS);
    if input.is_empty() {
        return Err(Error(InnerError::NeedMoreBytes));
    }

    let n = input[*pos];
    if is_last(n) {
        *pos += 1;
        return Ok(T::from(n));
    }

    let mut result = T::from(n & 0x7f);
    let mut shift: u32 = 7;

    let mut idx = *pos + 1;
    loop {
        if idx >= input.len() {
            return Err(Error(InnerError::NeedMoreBytes));
        }

        let n = input[idx];

        // If unnecessary bits are set (the bits would be dropped when
        // the value is shifted), then return an error.
        //
        // This error may be too strict.
        //
        // There should be at least a simple check to quickly
        // determine that the decoding has failed instead of
        // misinterpreting further data.
        //
        // For a less strict check, the && condition could be:
        //
        // (n & 0x80) != 0
        //
        // Another stricter condition is if the last byte has a 0 value.
        // The encoding is correct but not the minimal number of bytes
        // was used to express the final value.
        if shift == BITS - (BITS % 7) && n >= 1 << (BITS % 7) {
            return Err(Error(InnerError::InvalidEncoding));
        }

        if is_last(n) {
            result |= T::from(n) << shift;
            *pos = idx + 1;
            return Ok(result);
        }

        result |= T::from(n & 0x7f) << shift;
        shift += 7;
        idx += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_u8() {
        let mut buffer = [0; 4];
        let mut pos = 1;
        let written = encode_fixed_uint_slice::<_, 8>(u8::MAX, &mut buffer, &mut pos);
        assert_eq!(3, pos);
        assert_eq!([0x00, 0xFF, 0x01, 0x00], buffer);
        assert_eq!(Some(2), written);
    }

    #[test]
    fn test_encode_u16() {
        let mut buffer = [0; 5];
        let mut pos = 1;
        let written = encode_fixed_uint_slice::<_, 16>(u16::MAX, &mut buffer, &mut pos);
        assert_eq!(4, pos);
        assert_eq!([0x00, 0xFF, 0xFF, 0x03, 0x00], buffer);
        assert_eq!(Some(3), written);
    }

    #[test]
    fn test_encode_u32() {
        let mut buffer = [0; 6];
        let mut pos = 1;
        let written = encode_fixed_uint_slice::<_, 32>(u32::MAX, &mut buffer, &mut pos);
        assert_eq!(6, pos);
        assert_eq!([0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F], buffer);
        assert_eq!(Some(5), written);
    }

    #[test]
    fn test_encode_u64_as_33_bits_2() {
        let mut buffer = [0; 6];
        let mut pos = 1;
        let written = encode_fixed_uint_slice::<_, 33>(2u64.pow(33) - 1, &mut buffer, &mut pos);
        let mut pos = 1;
        let value = decode_uint_slice::<33, u64>(&buffer, &mut pos).unwrap();
        assert_eq!(8_589_934_592 - 1, value);
        assert_eq!(6, pos);
        assert_eq!([0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F], buffer);
        assert_eq!(Some(5), written);
    }

    #[test]
    fn test_encode_u64_as_33_bits_with_too_large_value() {
        let mut buffer = [0; 6];
        let mut pos = 1;
        let written = encode_fixed_uint_slice::<_, 33>(2u64.pow(34) - 1, &mut buffer, &mut pos);
        assert_eq!(1, pos);
        assert_eq!([0x00, 0x00, 0x00, 0x00, 0x00, 0x00], buffer);
        assert_eq!(None, written);
    }

    #[test]
    fn test_encode_u64() {
        let mut buffer = [0; 20];
        let mut pos = 1;
        let written = encode_fixed_uint_slice::<_, 64>(u64::MAX, &mut buffer, &mut pos);
        assert_eq!(11, pos);
        assert_eq!(Some(10), written);
    }

    #[test]
    fn test_decode_u32() {
        let input = [0xff, 0xff, 0xff, 0xff, 0x0f];
        let result = decode_u32(input);
        assert_eq!(result, Some((u32::MAX, 5)));

        let input = [0x00, 0x00, 0x00, 0x00, 0x00];
        let result = decode_u32(input);
        assert_eq!(result, Some((u32::MIN, 1)));

        // Valid but in-efficient way to encode 0.
        let input = [0x80, 0x80, 0x80, 0x80, 0x00];
        let result = decode_u32(input);
        assert_eq!(result, Some((u32::MIN, 5)));
    }

    #[test]
    fn test_decode_u32_errors() {
        // Maximum of 5 bytes encoding, the 0x80 bit must not be set.
        let input = [0xff, 0xff, 0xff, 0xff, 0x8f];
        let result = decode_u32(input);
        assert_eq!(result, None);

        // Parts of 0x1f (0x10) will be shifted out of the final value and lost.
        // This may too strict of a check since it could be ok.
        let input = [0xff, 0xff, 0xff, 0xff, 0x1f];
        let result = decode_u32(input);
        assert_eq!(result, None);
    }

    #[test]
    fn test_decode_u64() {
        let input = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01];
        let result = decode_u64(input);
        assert_eq!(result, Some((u64::MAX, 10)));

        let input = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let result = decode_u64(input);
        assert_eq!(result, Some((u64::MIN, 1)));

        // Valid but in-efficient way to encode 0.
        let input = [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00];
        let result = decode_u64(input);
        assert_eq!(result, Some((u64::MIN, 10)));
    }

    #[test]
    fn test_decode_u64_errors() {
        // Maximum of 10 bytes encoding, the 0x80 bit must not be set in the final byte.
        let input = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81];
        let result = decode_u64(input);
        assert_eq!(result, None);

        // 0x02 will be shifted out of the final value and lost.
        // This may too strict of a check since it could be ok.
        let input = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02];
        let result = decode_u64(input);
        assert_eq!(result, None);
    }
}
